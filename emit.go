package main

import (
	"bytes"
	"sort"
)

type emitter struct {
	a            *analysisResult
	src          []byte
	out          *bytes.Buffer
	funcByKey    map[string]funcBlock
	adj          map[string]map[string]struct{}
	callSeq      map[string][]string
	constructors map[string][]string
	methods      map[string][]string
	helpers      map[string]map[string]struct{}
	users        map[string]map[string]struct{}
	independent  []string
	// earlyIndependent is the subset of independent free functions that
	// originally appear before the first type declaration in the file. We
	// only emit these at the top. Independent functions that appear after
	// the first type are left in place (emitted later in source order) to
	// avoid moving private helpers above a file's primary public type.
	earlyIndependent []string

	writtenDecl map[int]struct{}
	writtenFunc map[string]struct{}
}

func newEmitter(a *analysisResult) *emitter {
	e := &emitter{
		a:                a,
		src:              a.src,
		out:              &bytes.Buffer{},
		funcByKey:        a.funcByKey,
		adj:              a.adj,
		callSeq:          a.callSeq,
		constructors:     a.constructors,
		methods:          a.methods,
		helpers:          a.helpers,
		users:            a.users,
		independent:      a.independent,
		writtenDecl:      map[int]struct{}{},
		writtenFunc:      map[string]struct{}{},
		earlyIndependent: []string{},
	}

	// Determine first exported, documented type start offset.
	firstExportedDocTypeStart := -1
	for _, tn := range a.typeNames {
		if len(tn) == 0 || tn[0] < 'A' || tn[0] > 'Z' { // unexported
			continue
		}
		if !a.typeHasDoc[tn] { // require doc comment to infer 'primary' type
			continue
		}
		if b, ok := a.typeDeclFor[tn]; ok {
			if firstExportedDocTypeStart == -1 || b.start < firstExportedDocTypeStart {
				firstExportedDocTypeStart = b.start
			}
		}
	}

	// If no exported documented type, keep legacy behaviour (all independents elevated)
	if firstExportedDocTypeStart == -1 {
		e.earlyIndependent = append(e.earlyIndependent, e.independent...)
		return e
	}

	// Decide whether to suppress moving independents that appear after this primary type.
	// If every independent function starts after the type, we treat them as
	// trailing helpers and keep them in place. If at least one appears before,
	// we elevate only those before.
	allAfter := true
	for _, k := range e.independent {
		if fb, ok := e.funcByKey[k]; ok && fb.start < firstExportedDocTypeStart {
			allAfter = false
			break
		}
	}

	for _, k := range e.independent {
		fb, ok := e.funcByKey[k]
		if !ok {
			continue
		}
		if allAfter {
			// keep all in place (earlyIndependent remains empty)
			continue
		}
		if fb.start < firstExportedDocTypeStart {
			e.earlyIndependent = append(e.earlyIndependent, k)
		}
	}

	return e
}

func (e *emitter) build() {
	// header
	e.writeHeader()

	// const/var blocks
	e.writeConstVar()

	// independent functions (only those that originally appeared before the
	// first type). Others are left in place to minimise movement when no
	// ordering constraints require change.
	if len(e.earlyIndependent) > 0 {
		base := sortExportedFirstByOriginal(e.earlyIndependent, e.funcByKey)
		ord := minimalReorderSubset(base, 0, e.adj, e.callSeq)
		for _, k := range ord {
			e.writeFuncIfNotWritten(k)
		}

		e.writeNL()
	}

	// types and associated functions
	e.writeTypes()

	// other type blocks
	e.writeTypeBlocks()

	// remaining connected components
	e.writeRemainingComponents()

	// remaining top-level funcs
	e.writeRemainingFuncs()

	e.writeTrailer()
}

func (e *emitter) writeHeader() {
	headerEnd := 0
	if e.a.lastImportEnd != -1 {
		headerEnd = e.a.lastImportEnd
	} else if e.a.firstDeclStart > 0 {
		headerEnd = e.a.firstDeclStart
	}

	if headerEnd > 0 {
		e.out.Write(e.src[:headerEnd])
	}
}

func (e *emitter) writeConstVar() {
	if len(e.a.constVar) == 0 {
		return
	}

	e.writeNL()

	for i, b := range e.a.constVar {
		if i > 0 {
			e.writeNL()
		}

		e.out.Write(e.src[b.start:b.end])
	}

	e.writeNL()
}

func (e *emitter) writeTypes() {
	for _, tn := range e.a.typeNames {
		b, ok := e.a.typeDeclFor[tn]
		if !ok {
			continue
		}

		e.processType(tn, b)
	}
}

func (e *emitter) processType(tn string, b block) {
	hasCtors := len(e.constructors[tn]) > 0
	hasMethods := len(e.methods[tn]) > 0

	// Always emit the type declaration itself.
	if !e.isWritten(b) {
		e.writeNL()
		e.out.Write(e.src[b.start:b.end])
		e.markWritten(b)
	}

	// If there are constructors or methods, emit them clustered; otherwise
	// we still may have users of this type that must appear after the type.
	if hasCtors || hasMethods {
		e.writeConstructorsAndCluster(tn)
	}
	e.writeUsersForType(tn)
	e.writeNL()
}

func (e *emitter) writeTypeBlocks() {
	for _, b := range e.a.typeBlocks {
		if !e.isWritten(b) {
			e.writeNL()
			e.out.Write(e.src[b.start:b.end])
			e.markWritten(b)
		}
	}
}

//nolint:gocognit // graph traversal; refactor would be risky for behaviour
func (e *emitter) writeRemainingComponents() {
	remainingSet := map[string]struct{}{}

	for _, fb := range e.a.funcBlocks {
		if fb.isMethod {
			continue
		}

		if _, ok := e.writtenFunc[fb.key]; !ok {
			remainingSet[fb.key] = struct{}{}
		}
	}

	for key := range remainingSet {
		if _, ok := remainingSet[key]; !ok {
			continue
		}

		comp := e.collectComponent(key, remainingSet)

		ord := sortExportedFirstByOriginal(comp, e.funcByKey)
		ord = minimalReorderSubset(ord, 0, e.adj, e.callSeq)

		ord = packWithinSubset(ord, 0, e.adj, e.callSeq)
		for _, k := range ord {
			e.writeFuncIfNotWritten(k)
		}

		e.writeNL()
	}
}

//nolint:gocognit // BFS traversal of component
func (e *emitter) collectComponent(key string, remainingSet map[string]struct{}) []string {
	comp := []string{}
	queue := []string{key}
	delete(remainingSet, key)

	for len(queue) > 0 {
		u := queue[0]
		queue = queue[1:]

		comp = append(comp, u)
		for v := range e.adj[u] {
			if _, ok := remainingSet[v]; ok {
				delete(remainingSet, v)
				queue = append(queue, v)
			}
		}

		for v := range e.a.callersOf[u] {
			if _, ok := remainingSet[v]; ok {
				delete(remainingSet, v)
				queue = append(queue, v)
			}
		}
	}

	return comp
}

func (e *emitter) writeDeclIfNeeded(b block) {
	if !e.isWritten(b) {
		e.writeNL()
		e.out.Write(e.src[b.start:b.end])
		e.markWritten(b)
	}
}

func (e *emitter) isWritten(b block) bool {
	_, ok := e.writtenDecl[b.start]

	return ok
}

func (e *emitter) markWritten(b block) { e.writtenDecl[b.start] = struct{}{} }

func (e *emitter) writeConstructorsAndCluster(tn string) {
	for _, name := range e.constructors[tn] {
		e.writeFuncIfNotWritten(name)
	}

	methodList := e.methods[tn]
	helperList := e.gatherHelperList(tn)

	cluster := append(append([]string{}, methodList...), helperList...)
	ord := sortByOriginal(cluster, e.funcByKey)

	firstCallerIdx, firstCaller := e.findFirstCallerInOrd(ord)
	pinned := e.computePinnedFromFirstCaller(ord, firstCallerIdx, firstCaller)

	ord = minimalReorderSubset(ord, pinned, e.adj, e.callSeq)

	ord = packWithinSubset(ord, pinned, e.adj, e.callSeq)
	for _, k := range ord {
		e.writeFuncIfNotWritten(k)
	}
}

func (e *emitter) writeUsersForType(tn string) {
	userList := []string{}

	for _, fb := range e.a.funcBlocks {
		if _, ok := e.users[tn][fb.key]; ok {
			userList = append(userList, fb.key)
		}
	}

	if len(userList) == 0 {
		return
	}

	uord := sortExportedFirstByOriginal(userList, e.funcByKey)
	uord = minimalReorderSubset(uord, 0, e.adj, e.callSeq)

	uord = packWithinSubset(uord, 0, e.adj, e.callSeq)
	for _, k := range uord {
		e.writeFuncIfNotWritten(k)
	}
}

func (e *emitter) writeRemainingFuncs() {
	writtenKeys := e.buildWrittenKeys()

	for _, fb := range e.a.funcBlocks {
		if _, ok := writtenKeys[fb.key]; ok {
			continue
		}

		e.writeFuncIfNotWritten(fb.key)
	}
}

//nolint:gocognit // small helper collecting names; cognitive metric noisy
func (e *emitter) buildWrittenKeys() map[string]struct{} {
	writtenKeys := map[string]struct{}{}

	for _, tn := range e.a.typeNames {
		for _, k := range e.constructors[tn] {
			writtenKeys[k] = struct{}{}
		}

		for _, k := range e.methods[tn] {
			writtenKeys[k] = struct{}{}
		}

		for k := range e.helpers[tn] {
			writtenKeys[k] = struct{}{}
		}

		for k := range e.users[tn] {
			writtenKeys[k] = struct{}{}
		}
	}

	for _, k := range e.independent {
		writtenKeys[k] = struct{}{}
	}

	return writtenKeys
}

func (e *emitter) writeFuncIfNotWritten(name string) {
	if _, ok := e.writtenFunc[name]; ok {
		return
	}

	if fb, ok := e.funcByKey[name]; ok {
		e.writeNL()
		e.out.Write(e.src[fb.start:fb.end])
		e.writtenFunc[name] = struct{}{}
	}
}

func (e *emitter) writeNL() {
	if e.out.Len() > 0 && !bytes.HasSuffix(e.out.Bytes(), []byte("\n\n")) {
		if !bytes.HasSuffix(e.out.Bytes(), []byte("\n")) {
			e.out.WriteByte('\n')
		}

		e.out.WriteByte('\n')
	}
}

func (e *emitter) gatherHelperList(tn string) []string {
	helperList := []string{}

	for _, fb := range e.a.funcBlocks {
		if _, ok := e.helpers[tn][fb.key]; ok {
			helperList = append(helperList, fb.key)
		}
	}

	return helperList
}

//nolint:gocognit // small search across order list
func (e *emitter) findFirstCallerInOrd(ord []string) (int, string) {
	ordSet := map[string]struct{}{}
	for _, k := range ord {
		ordSet[k] = struct{}{}
	}

	for i, name := range ord {
		if seq, ok := e.callSeq[name]; ok && len(seq) > 0 {
			for _, cal := range seq {
				if _, ok := ordSet[cal]; ok {
					return i, name
				}
			}
		}
	}

	return -1, ""
}

func (e *emitter) computePinnedFromFirstCaller(ord []string, firstCallerIdx int, firstCaller string) int {
	if firstCallerIdx == -1 {
		return 0
	}

	ordSet := map[string]struct{}{}
	for _, k := range ord {
		ordSet[k] = struct{}{}
	}

	calSet := map[string]struct{}{}

	for _, c := range e.callSeq[firstCaller] {
		if _, ok := ordSet[c]; ok {
			calSet[c] = struct{}{}
		}
	}

	pinned := 0

	for i := 0; i < firstCallerIdx; i++ {
		if _, isCal := calSet[ord[i]]; !isCal {
			pinned++
		}
	}

	return pinned
}

func (e *emitter) writeTrailer() {
	if e.a.lastDeclEnd < 0 || e.a.lastDeclEnd > len(e.src) {
		return
	}

	tail := e.src[e.a.lastDeclEnd:]
	if len(tail) == 0 { // file ended at last decl
		e.normaliseTerminalNewline()

		return
	}

	if tail[0] == '\n' { // trim any extra blank lines before attaching tail
		e.trimTrailingNewlines()
	} else if e.needSingleSeparator() { // ensure exactly one separator newline
		e.out.WriteByte('\n')
	}

	e.out.Write(tail)
}

// normaliseTerminalNewline ensures output ends with exactly one newline when
// there is no original tail content.
func (e *emitter) normaliseTerminalNewline() {
	b := e.out.Bytes()

	i := len(b)
	for i > 0 && b[i-1] == '\n' {
		i--
	}

	if i != len(b) { // rebuild without surplus newlines
		var nb bytes.Buffer
		nb.Write(b[:i])
		e.out = &nb
	}

	if e.out.Len() == 0 || !bytes.HasSuffix(e.out.Bytes(), []byte("\n")) {
		e.out.WriteByte('\n')
	}
}

// trimTrailingNewlines removes all trailing newlines so that if the original
// tail begins with a newline we do not create extra blank lines.
func (e *emitter) trimTrailingNewlines() {
	b := e.out.Bytes()

	i := len(b)
	for i > 0 && b[i-1] == '\n' {
		i--
	}

	if i == len(b) { // nothing trimmed
		return
	}

	var nb bytes.Buffer
	nb.Write(b[:i])
	e.out = &nb
}

// needSingleSeparator reports whether we need to insert a single newline
// between previously written declarations and a tail that does not start with
// a newline.
func (e *emitter) needSingleSeparator() bool {
	return e.out.Len() > 0 && !bytes.HasSuffix(e.out.Bytes(), []byte("\n"))
}

// buildOutput assembles the reordered source bytes according to the rules.
func buildOutput(a *analysisResult) []byte {
	e := newEmitter(a)
	e.build()

	return e.out.Bytes()
}

// sortExportedFirstByOriginal returns keys ordered so exported (public) names
// come before private ones, and within each partition items are ordered by
// original byte offset. Exportedness is determined by the first rune of the
// function name (for methods, the name after the dot).
func sortExportedFirstByOriginal(keys []string, funcByKey map[string]funcBlock) []string {
	out := append([]string(nil), keys...)

	isExported := func(k string) bool {
		name := k
		// For methods, key format is "Recv.Name"; extract method name
		if dot := indexByte(name, '.'); dot >= 0 {
			name = name[dot+1:]
		}
		if name == "" {
			return false
		}
		r := name[0]
		return r >= 'A' && r <= 'Z'
	}

	sort.SliceStable(out, func(i, j int) bool {
		ei, ej := isExported(out[i]), isExported(out[j])
		if ei != ej {
			return ei && !ej // exported first
		}
		return funcByKey[out[i]].start < funcByKey[out[j]].start
	})

	return out
}

// indexByte is a tiny helper to avoid importing strings for a single use.
func indexByte(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}
