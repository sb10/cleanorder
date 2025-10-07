package main

import (
	"go/ast"
	"go/parser"
	"go/token"
	"sort"
	"strings"
)

// callFirstPosMap shortens the map type used to record first call positions.
type callFirstPosMap map[string]map[string]int

// analysisResult aggregates all information derived from parsing needed for
// subsequent ordering & emission phases.
type analysisResult struct {
	fset           *token.FileSet
	src            []byte
	file           *ast.File
	constVar       []block
	typeBlocks     []block
	typeNames      []string
	typeDeclFor    map[string]block
	funcBlocks     []funcBlock
	funcByKey      map[string]funcBlock
	firstDeclStart int
	lastImportEnd  int
	lastDeclEnd    int
	// call graph + sequencing
	adj       map[string]map[string]struct{}
	callersOf map[string]map[string]struct{}
	callSeq   map[string][]string
	// classifications
	constructors map[string][]string
	methods      map[string][]string
	helpers      map[string]map[string]struct{}
	users        map[string]map[string]struct{}
	independent  []string
}

func newAnalysisResult(fset *token.FileSet, src []byte, file *ast.File) *analysisResult {
	return &analysisResult{
		fset:           fset,
		src:            src,
		file:           file,
		constVar:       []block{},
		typeBlocks:     []block{},
		typeNames:      []string{},
		typeDeclFor:    map[string]block{},
		funcBlocks:     []funcBlock{},
		funcByKey:      map[string]funcBlock{},
		firstDeclStart: -1,
		lastImportEnd:  -1,
		lastDeclEnd:    -1,
		adj:            map[string]map[string]struct{}{},
		callersOf:      map[string]map[string]struct{}{},
		callSeq:        map[string][]string{},
		constructors:   map[string][]string{},
		methods:        map[string][]string{},
		helpers:        map[string]map[string]struct{}{},
		users:          map[string]map[string]struct{}{},
	}
}

// analyzeFile parses filename and computes metadata required for reordering.
func analyzeFile(filename string, src []byte) (*analysisResult, error) {
	fset := token.NewFileSet()

	file, err := parser.ParseFile(fset, filename, src, parser.ParseComments)
	if err != nil {
		return nil, err
	}

	res := newAnalysisResult(fset, src, file)

	res.collectDecls(fset, file)
	res.buildCallGraph()
	res.classify()

	return res, nil
}

// collectDecls scans file.Decls and populates basic declaration information.
//
//nolint:gocognit
func (res *analysisResult) collectDecls(fset *token.FileSet, file *ast.File) {
	for _, decl := range file.Decls {
		s := fset.Position(decl.Pos()).Offset
		e := fset.Position(decl.End()).Offset

		if gd, ok := decl.(*ast.GenDecl); ok {
			res.handleGenDecl(fset, gd, s, e)
		}

		if fd, ok := decl.(*ast.FuncDecl); ok {
			res.handleFuncDecl(fset, fd)
		}

		if res.firstDeclStart == -1 || s < res.firstDeclStart {
			res.firstDeclStart = s
		}

		if e > res.lastDeclEnd {
			res.lastDeclEnd = e
		}
	}
}

func (res *analysisResult) handleGenDecl(fset *token.FileSet, gd *ast.GenDecl, s, e int) {
	s = res.adjustDeclStartForDoc(fset, gd, s)
	e = res.extendEndForInlineComments(fset, gd, e)
	res.recordGenDecl(gd, s, e)
}

func (res *analysisResult) adjustDeclStartForDoc(fset *token.FileSet, gd *ast.GenDecl, s int) int {
	if gd.Doc != nil {
		return fset.Position(gd.Doc.Pos()).Offset
	}

	return s
}

func (res *analysisResult) extendEndForInlineComments(fset *token.FileSet, gd *ast.GenDecl, e int) int {
	startLine := fset.Position(gd.Pos()).Line
	endLine := fset.Position(gd.End()).Line

	for _, cg := range res.file.Comments {
		for _, c := range cg.List {
			if res.commentLineWithin(fset, c, startLine, endLine) {
				e = res.extendEndForComment(fset, c, e)
			}
			// Additionally, if the comment appears on the same line as the end
			// of the declaration (inline trailing comment), include it. This is
			// required so that re-emitting the declaration preserves inline
			// comments like "//nolint" that would otherwise be separated onto
			// a new line when go/format runs after we splice declarations.
			if fset.Position(c.Pos()).Line == endLine {
				e = res.extendEndForComment(fset, c, e)
			}
		}
	}

	return e
}

func (res *analysisResult) commentLineWithin(fset *token.FileSet, c *ast.Comment, start, end int) bool {
	line := fset.Position(c.Pos()).Line

	return line >= start && line <= end
}

func (res *analysisResult) extendEndForComment(fset *token.FileSet, c *ast.Comment, cur int) int {
	ce := fset.Position(c.End()).Offset
	if ce > cur {
		return ce
	}

	return cur
}

func (res *analysisResult) recordGenDecl(gd *ast.GenDecl, s, e int) {
	switch gd.Tok {
	case token.IMPORT:
		if e > res.lastImportEnd {
			res.lastImportEnd = e
		}
	case token.CONST, token.VAR:
		res.constVar = append(res.constVar, block{s, e})
	case token.TYPE:
		res.typeBlocks = append(res.typeBlocks, block{s, e})

		for _, sp := range gd.Specs {
			if ts, ok := sp.(*ast.TypeSpec); ok {
				name := ts.Name.Name
				res.typeDeclFor[name] = block{s, e}
				res.typeNames = append(res.typeNames, name)
			}
		}
	default:
	}
}

func (res *analysisResult) handleFuncDecl(fset *token.FileSet, fd *ast.FuncDecl) {
	fs := fset.Position(fd.Pos()).Offset
	fe := fset.Position(fd.End()).Offset
	if fd.Doc != nil {
		fs = fset.Position(fd.Doc.Pos()).Offset
	}

	// Extend end to capture any trailing inline comment on the same line as
	// the function's closing brace. Without this, an inline comment that
	// belongs logically to the function (e.g. a //nolint at end of single-line
	// func) could appear detached after reordering.
	funcEndLine := fset.Position(fd.End()).Line
	for _, cg := range res.file.Comments {
		for _, c := range cg.List {
			if fset.Position(c.Pos()).Line == funcEndLine {
				fe = res.extendEndForComment(fset, c, fe)
			}
		}
	}

	recv := getRecvType(fd)
	key := fd.Name.Name
	if recv != "" { // qualify method key to avoid collisions between different receiver types with same method name
		key = recv + "." + key
	}

	fb := funcBlock{key: key, start: fs, end: fe, recvType: recv, isMethod: recv != ""}
	res.funcBlocks = append(res.funcBlocks, fb)
	res.funcByKey[fb.key] = fb
}

// buildCallGraph inspects function bodies to build adjacency and call sequence
// info.
func (res *analysisResult) buildCallGraph() {
	nameToKey := res.buildSimpleNameIndex()
	callFirstPos := callFirstPosMap{}

	res.initAdjacency()

	res.walkFuncsCollectCalls(callFirstPos, nameToKey)
}

func (res *analysisResult) buildSimpleNameIndex() map[string]string {
	temp := map[string][]string{}

	for _, fb := range res.funcBlocks {
		simple := fb.key
		if fb.isMethod {
			if idx := strings.LastIndex(simple, "."); idx != -1 {
				simple = simple[idx+1:]
			}
		}

		temp[simple] = append(temp[simple], fb.key)
	}

	nameToKey := map[string]string{}

	for n, list := range temp {
		if len(list) == 1 {
			nameToKey[n] = list[0]
		}
	}

	return nameToKey
}

func (res *analysisResult) initAdjacency() {
	for _, fb := range res.funcBlocks {
		res.adj[fb.key] = map[string]struct{}{}
	}
}

func (res *analysisResult) walkFuncsCollectCalls(callFirstPos callFirstPosMap, nameToKey map[string]string) {
	for _, decl := range res.file.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Body == nil {
			continue
		}

		res.processFuncCalls(fd, callFirstPos, nameToKey)
	}
}

func (res *analysisResult) processFuncCalls(
	fd *ast.FuncDecl,
	callFirstPos callFirstPosMap,
	nameToKey map[string]string,
) {
	// Use the same key scheme as funcBlocks (receiver-qualified for methods)
	callerKey := fd.Name.Name
	if fd.Recv != nil {
		if rt := getRecvType(fd); rt != "" {
			callerKey = rt + "." + callerKey
		}
	}

	if _, ok := callFirstPos[callerKey]; !ok {
		callFirstPos[callerKey] = map[string]int{}
	}

	res.collectCallPositions(fd, callerKey, callFirstPos, nameToKey)

	if seq := res.buildSeqForCaller(callerKey, callFirstPos); len(seq) > 0 {
		res.callSeq[callerKey] = seq
	}
}

func (res *analysisResult) collectCallPositions(
	fd *ast.FuncDecl,
	callerKey string,
	callFirstPos callFirstPosMap,
	nameToKey map[string]string,
) {
	ast.Inspect(fd.Body, func(n ast.Node) bool { return res.inspectCallExpr(n, callerKey, callFirstPos, nameToKey) })
}

func (res *analysisResult) inspectCallExpr(
	n ast.Node,
	callerKey string,
	callFirstPos callFirstPosMap,
	nameToKey map[string]string,
) bool {
	ce, ok := n.(*ast.CallExpr)
	if !ok {
		return true
	}

	res.recordCall(ce, callerKey, callFirstPos, nameToKey)

	return true
}

// recordCall updates adjacency & caller metadata for a call expression.
func (res *analysisResult) recordCall(
	ce *ast.CallExpr,
	callerKey string,
	callFirstPos callFirstPosMap,
	nameToKey map[string]string,
) {
	name := callNameFromExpr(ce.Fun)
	if name == "" {
		return
	}

	callee, ok := nameToKey[name]
	if !ok || callee == callerKey {
		return
	}

	res.adj[callerKey][callee] = struct{}{}
	if _, ok := res.callersOf[callee]; !ok {
		res.callersOf[callee] = map[string]struct{}{}
	}

	res.callersOf[callee][callerKey] = struct{}{}
	if _, seen := callFirstPos[callerKey][callee]; !seen {
		callFirstPos[callerKey][callee] = res.fset.Position(ce.Pos()).Offset
	}
}

func callNameFromExpr(e ast.Expr) string {
	switch fun := e.(type) {
	case *ast.Ident:
		return fun.Name
	case *ast.SelectorExpr:
		return fun.Sel.Name
	default:
		return ""
	}
}

func (res *analysisResult) buildSeqForCaller(caller string, callFirstPos callFirstPosMap) []string {
	if len(callFirstPos[caller]) == 0 {
		return nil
	}

	type pair struct {
		name string
		pos  int
	}

	arr := make([]pair, 0, len(callFirstPos[caller]))
	for k, p := range callFirstPos[caller] {
		arr = append(arr, pair{k, p})
	}

	sort.Slice(arr, func(i, j int) bool { return arr[i].pos < arr[j].pos })

	seq := make([]string, len(arr))
	for i := range arr {
		seq[i] = arr[i].name
	}

	return seq
}

// classify computes type sets, constructors, methods, helpers, users and
// independents.
func (res *analysisResult) classify() {
	typeSet := res.computeTypeSet()
	res.initTypeMaps(typeSet)
	res.findConstructors(typeSet)
	res.findMethods(typeSet)
	res.computeHelpers()
	res.computeUsers(typeSet)
	res.computeIndependent()
}

func (res *analysisResult) computeTypeSet() map[string]struct{} {
	typeSet := map[string]struct{}{}
	for _, tn := range res.typeNames {
		typeSet[tn] = struct{}{}
	}

	return typeSet
}

func (res *analysisResult) initTypeMaps(typeSet map[string]struct{}) {
	for tn := range typeSet {
		res.helpers[tn] = map[string]struct{}{}
		res.users[tn] = map[string]struct{}{}
	}
}

//nolint:gocognit,gocyclo
func (res *analysisResult) findConstructors(typeSet map[string]struct{}) {
	for _, decl := range res.file.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv != nil {
			continue
		}

		name := fd.Name.Name

		if fd.Type.Results == nil {
			continue
		}

		for _, f := range fd.Type.Results.List {
			tn := resolveResultTypeToIdent(f.Type)
			if tn == "" {
				continue
			}

			if _, ok := typeSet[tn]; ok {
				// treat any such function as constructor-like; we still keep
				// original ordering among constructors.
				res.constructors[tn] = append(res.constructors[tn], name)
			}
		}
	}
}

func resolveResultTypeToIdent(t ast.Expr) string {
	for {
		switch tt := t.(type) {
		case *ast.StarExpr:
			t = tt.X

			continue
		case *ast.Ident:
			return tt.Name
		default:
			return ""
		}
	}
}

func (res *analysisResult) findMethods(typeSet map[string]struct{}) {
	for _, decl := range res.file.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv == nil {
			continue
		}

		rt := getRecvType(fd)
		if _, ok := typeSet[rt]; ok {
			// build qualified key same way as handleFuncDecl
			name := fd.Name.Name
			q := rt + "." + name
			res.methods[rt] = append(res.methods[rt], q)
		}
	}
}

//nolint:gocognit
func (res *analysisResult) computeHelpers() {
	for tn, mlist := range res.methods {
		for _, m := range mlist {
			for callee := range res.adj[m] {
				if fb, ok := res.funcByKey[callee]; ok && !fb.isMethod {
					res.helpers[tn][callee] = struct{}{}
				}
			}
		}
	}
}

//nolint:gocognit,gocyclo
func (res *analysisResult) computeUsers(typeSet map[string]struct{}) {
	ctorSet := map[string]string{}

	for tn, list := range res.constructors {
		for _, c := range list {
			ctorSet[c] = tn
		}
	}

	methodSet := map[string]string{}

	for tn, list := range res.methods {
		for _, m := range list {
			name := m
			if idx := strings.LastIndex(name, "."); idx != -1 {
				name = name[idx+1:]
			}

			methodSet[name] = tn
		}
	}

	for _, decl := range res.file.Decls {
		fd, ok := decl.(*ast.FuncDecl)
		if !ok || fd.Recv != nil {
			continue
		}

		res.inspectFuncForUsers(fd, typeSet, ctorSet, methodSet)
	}
}

func (res *analysisResult) inspectFuncForUsers(
	fd *ast.FuncDecl,
	typeSet map[string]struct{},
	ctorSet, methodSet map[string]string,
) {
	name := fd.Name.Name

	// If this function is a constructor for some type, we do NOT want to
	// consider it a 'user' of any other types it happens to reference in its
	// parameters or body. Otherwise a constructor that accepts existing types
	// (eg. takes *DirectoryPath but returns FileInfo) would be emitted in the
	// users section of the parameter type's cluster, preceding its own type
	// declaration, which is undesirable. We also don't need constructors to be
	// classified as users of their constructed type (they are emitted in the
	// constructors phase). So we simply skip user classification entirely for
	// constructor functions.
	if _, isCtor := ctorSet[name]; isCtor {
		return
	}

	for tn := range typeSet {
		if usesType(fd, tn) {
			res.users[tn][name] = struct{}{}
		}
	}

	if fd.Body == nil {
		return
	}

	ast.Inspect(fd.Body, func(n ast.Node) bool { return res.handleCallExprForUsers(n, name, ctorSet, methodSet) })
}

func (res *analysisResult) handleCallExprForUsers(n ast.Node, name string, ctorSet, methodSet map[string]string) bool {
	ce, ok := n.(*ast.CallExpr)
	if !ok {
		return true
	}

	switch fun := ce.Fun.(type) {
	case *ast.Ident:
		if tn, ok := ctorSet[fun.Name]; ok {
			res.users[tn][name] = struct{}{}
		}

		if tn, ok := methodSet[fun.Name]; ok {
			res.users[tn][name] = struct{}{}
		}
	case *ast.SelectorExpr:
		if tn, ok := methodSet[fun.Sel.Name]; ok {
			res.users[tn][name] = struct{}{}
		}
	}

	return true
}

func (res *analysisResult) computeIndependent() {
	ctorSet := res.buildConstructorSet()
	userSet := res.buildUserSet()

	for _, fb := range res.funcBlocks {
		if res.isIndependentCandidate(fb, ctorSet, userSet) {
			res.independent = append(res.independent, fb.key)
		}
	}
}

// buildConstructorSet returns a set of constructor function names for
// exclusion.
func (res *analysisResult) buildConstructorSet() map[string]struct{} {
	ctorSet := map[string]struct{}{}

	for _, list := range res.constructors {
		for _, c := range list {
			ctorSet[c] = struct{}{}
		}
	}

	return ctorSet
}

// buildUserSet returns a set of user function names (those that reference a
// type).
func (res *analysisResult) buildUserSet() map[string]struct{} {
	userSet := map[string]struct{}{}

	for _, umap := range res.users {
		for u := range umap {
			userSet[u] = struct{}{}
		}
	}

	return userSet
}

// isIndependentCandidate applies the independent classification rules for a
// single funcBlock.
func (res *analysisResult) isIndependentCandidate(fb funcBlock, ctorSet, userSet map[string]struct{}) bool {
	if fb.isMethod {
		return false
	}

	name := fb.key
	if _, isCtor := ctorSet[name]; isCtor {
		return false
	}

	if _, isUser := userSet[name]; isUser {
		return false
	}

	if len(res.adj[name]) > 0 {
		return false
	}

	if len(res.callersOf[name]) > 0 {
		return false
	}

	return true
}
