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

//nolint:gocyclo
func (res *analysisResult) handleGenDecl(fset *token.FileSet, gd *ast.GenDecl, s, e int) {
	if gd.Doc != nil {
		s = fset.Position(gd.Doc.Pos()).Offset
	}

	// Extend end to include trailing inline comments that fall within the
	// lines spanned by the declaration to preserve trailing //nolint comments.
	declStartLine := fset.Position(gd.Pos()).Line
	declEndLine := fset.Position(gd.End()).Line
	for _, cgroup := range res.file.Comments {
		for _, c := range cgroup.List {
			cline := fset.Position(c.Pos()).Line
			if cline < declStartLine || cline > declEndLine {
				continue
			}
			ce := fset.Position(c.End()).Offset
			if ce > e {
				e = ce
			}
		}
	}

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
		// ignore other token kinds
	}
}

func (res *analysisResult) handleFuncDecl(fset *token.FileSet, fd *ast.FuncDecl) {
	fs := fset.Position(fd.Pos()).Offset

	fe := fset.Position(fd.End()).Offset
	if fd.Doc != nil {
		fs = fset.Position(fd.Doc.Pos()).Offset
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
	// map simple names to unique keys only when not ambiguous to avoid
	// accidental collisions across different receiver types.
	temp := map[string][]string{}
	for _, fb := range res.funcBlocks {
		simple := fb.key
		if fb.isMethod { // strip receiver qualifier
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

	callFirstPos := callFirstPosMap{}

	for _, fb := range res.funcBlocks {
		res.adj[fb.key] = map[string]struct{}{}
	}

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

//nolint:funlen,gocognit

func (res *analysisResult) collectCallPositions(
	fd *ast.FuncDecl,
	callerKey string,
	callFirstPos callFirstPosMap,
	nameToKey map[string]string,
) {
	ast.Inspect(fd.Body, func(n ast.Node) bool {
		ce, ok := n.(*ast.CallExpr)
		if !ok {
			return true
		}

		name := callNameFromExpr(ce.Fun)
		if name == "" {
			return true
		}

		callee, ok := nameToKey[name]
		if !ok || callee == callerKey {
			return true
		}

		res.adj[callerKey][callee] = struct{}{}
		if _, ok := res.callersOf[callee]; !ok {
			res.callersOf[callee] = map[string]struct{}{}
		}

		res.callersOf[callee][callerKey] = struct{}{}
		if _, seen := callFirstPos[callerKey][callee]; !seen {
			callFirstPos[callerKey][callee] = res.fset.Position(ce.Pos()).Offset
		}

		return true
	})
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

// isConstructorLikeName reports whether a free function name should be
// considered a constructor for ordering purposes. Historically only names with
// prefix "New" were treated as constructors. The project source uses a
// lowercase form (e.g. newEmitter) that returns the type; we extend detection
// to accept that pattern so that such helper constructors are clustered
// immediately after their type.
// isConstructorLikeName retained for potential future use; now any free
// function returning the type is considered a constructor. Kept to avoid
// removing previously used symbol.
func isConstructorLikeName(name string) bool { return strings.HasPrefix(name, "New") }

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
