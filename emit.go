package main

import (
	"bytes"
	"go/token"
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
	// Reverse index of constructor function name -> types it constructs.
	ctorToTypes map[string][]string
	// For const/var blocks: map block start offset -> types referenced by that block
	constBlockDeps map[int][]string
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
		ctorToTypes:      map[string][]string{},
		earlyIndependent: []string{},
	}

	// Build reverse constructor map: ctor name -> all types it constructs
	for tn, list := range a.constructors {
		for _, c := range list {
			e.ctorToTypes[c] = append(e.ctorToTypes[c], tn)
		}
	}

	// Build const/var block dependencies from analysis constVarUsers
	e.constBlockDeps = map[int][]string{}
	for tn, blks := range a.constVarUsers {
		for _, b := range blks {
			e.constBlockDeps[b.start] = append(e.constBlockDeps[b.start], tn)
		}
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

	// Helper to order a subset of const/var blocks by const-usage dependencies
	orderSubset := func(infos []constVarInfo, idxs []int) []int {
		if len(idxs) <= 1 {
			return append([]int(nil), idxs...)
		}
		n := len(idxs)
		pos := make(map[int]int, n)
		for i, id := range idxs {
			pos[id] = i
		}
		indeg := make([]int, n)
		adj := make([][]int, n)
		for i := range adj {
			adj[i] = []int{}
		}
		// map original index within subset to its defines if it's a const block
		defines := make([]map[string]struct{}, n)
		for i, id := range idxs {
			if infos[id].tok == token.CONST {
				defines[i] = infos[id].defines
			} else {
				defines[i] = map[string]struct{}{}
			}
		}
		// Build edges: for each var in subset, add edges from consts in subset that it uses
		for i, id := range idxs {
			if infos[id].tok != token.VAR {
				continue
			}
			for ci, cdefs := range defines {
				if len(cdefs) == 0 {
					continue
				}
				// quick intersection
				used := infos[id].usesIdents
				dep := false
				for name := range used {
					if _, ok := cdefs[name]; ok {
						dep = true
						break
					}
				}
				if dep {
					adj[ci] = append(adj[ci], i)
					indeg[i]++
				}
			}
		}
		// Kahn's algorithm with stability based on original position within subset
		ready := make([]int, 0, n)
		for i := 0; i < n; i++ {
			if indeg[i] == 0 {
				ready = append(ready, i)
			}
		}
		sort.Ints(ready)
		orderedLocal := make([]int, 0, n)
		for len(ready) > 0 {
			i := ready[0]
			ready = ready[1:]
			orderedLocal = append(orderedLocal, idxs[i])
			for _, nb := range adj[i] {
				indeg[nb]--
				if indeg[nb] == 0 {
					// insert nb keeping ready sorted
					insertPos := sort.SearchInts(ready, nb)
					if insertPos == len(ready) || ready[insertPos] != nb {
						ready = append(ready, 0)
						copy(ready[insertPos+1:], ready[insertPos:])
						ready[insertPos] = nb
					}
				}
			}
		}
		if len(orderedLocal) != n {
			return append([]int(nil), idxs...)
		}
		return orderedLocal
	}

	infos := e.a.constVarInfos
	// Partition into untyped and typed groups (typed have recorded type deps)
	untypedIdx := []int{}
	typedIdx := []int{}
	if len(infos) == len(e.a.constVar) && len(infos) > 0 {
		for i, inf := range infos {
			if _, ok := e.constBlockDeps[inf.blk.start]; ok {
				typedIdx = append(typedIdx, i)
			} else {
				untypedIdx = append(untypedIdx, i)
			}
		}
	} else {
		// Fallback: no detailed infos
		for i := range e.a.constVar {
			if _, ok := e.constBlockDeps[e.a.constVar[i].start]; ok {
				typedIdx = append(typedIdx, i)
			} else {
				untypedIdx = append(untypedIdx, i)
			}
		}
	}

	// Order each group independently with const-usage constraints
	if len(infos) == len(e.a.constVar) && len(infos) > 0 {
		untypedIdx = orderSubset(infos, untypedIdx)
		typedIdx = orderSubset(infos, typedIdx)
	}

	outCount := 0
	// Emit all untyped blocks first to keep unrelated consts/vars at the very top
	for _, id := range untypedIdx {
		var b block
		if len(infos) == len(e.a.constVar) && len(infos) > 0 {
			b = infos[id].blk
		} else {
			b = e.a.constVar[id]
		}
		if outCount > 0 {
			e.writeNL()
		}
		e.out.Write(e.src[b.start:b.end])
		e.markWritten(b)
		outCount++
	}

	// Then emit typed blocks; inject required type declarations immediately before each
	for _, id := range typedIdx {
		var b block
		if len(infos) == len(e.a.constVar) && len(infos) > 0 {
			b = infos[id].blk
		} else {
			b = e.a.constVar[id]
		}
		emittedType := false
		if deps, ok := e.constBlockDeps[b.start]; ok {
			// emit dependency types in deterministic order by original position
			if len(deps) > 1 {
				sort.SliceStable(deps, func(i, j int) bool {
					bi, bok := e.a.typeDeclFor[deps[i]]
					bj, bjok := e.a.typeDeclFor[deps[j]]
					if !bok || !bjok {
						return deps[i] < deps[j]
					}
					if bi.start != bj.start {
						return bi.start < bj.start
					}
					return deps[i] < deps[j]
				})
			}
			for _, tn := range deps {
				if tb, ok := e.a.typeDeclFor[tn]; ok && !e.isWritten(tb) {
					e.writeDeclIfNeeded(tb)
					emittedType = true
				}
			}
		}
		if outCount > 0 || emittedType {
			e.writeNL()
		}
		e.out.Write(e.src[b.start:b.end])
		e.markWritten(b)
		outCount++
	}

	e.writeNL()
}

func (e *emitter) writeTypes() {
	visited := map[string]bool{}
	for _, tn := range e.a.typeNames {
		e.emitTypeWithDeps(tn, visited)
	}
}

// emitTypeWithDeps ensures that any not-yet-emitted types used by the methods of tn
// are emitted before tn to satisfy the precedence "types before users" across receiver types.
func (e *emitter) emitTypeWithDeps(tn string, visited map[string]bool) {
	if visited[tn] {
		return
	}
	visited[tn] = true

	// Skip incidental types here; they will be emitted inline before the first user.
	if _, inc := e.a.incidentalTypes[tn]; inc {
		return
	}

	// Emit dependency types first
	for dep := range e.typeDeps(tn) {
		e.emitTypeWithDeps(dep, visited)
	}

	b, ok := e.a.typeDeclFor[tn]
	if !ok {
		return
	}

	// Always process the type to ensure its constructors/methods/users are
	// emitted, even if the type declaration itself has already been written
	// earlier (e.g., to satisfy a typed const block dependency). processType
	// internally checks and avoids re-emitting the type declaration when it
	// has been written, but still emits the associated functions.
	e.processType(tn, b)
}

// typeDeps returns the set of types referenced by methods of tn (as recorded in users)
// that should be emitted before tn to ensure the referenced types precede their users.
func (e *emitter) typeDeps(tn string) map[string]struct{} {
	deps := map[string]struct{}{}

	mset := map[string]struct{}{}
	for _, m := range e.methods[tn] {
		mset[m] = struct{}{}
	}
	// Method-based dependencies: if any method of tn is a recorded user of 'other',
	// then 'other' must be emitted before tn.
	if len(mset) > 0 {
		for other := range e.a.typeDeclFor {
			if other == tn {
				continue
			}
			// Skip incidental types; they will be inlined near first user.
			if _, inc := e.a.incidentalTypes[other]; inc {
				continue
			}
			for m := range mset {
				if _, ok := e.users[other][m]; ok {
					deps[other] = struct{}{}
					break
				}
			}
		}
	}

	// Declaration-based dependencies: if tn's declaration mentions another
	// declared type, that type must precede tn.
	if dset, ok := e.a.typeDeclDeps[tn]; ok {
		for other := range dset {
			// Skip incidental types; they will be inlined near first user.
			if _, inc := e.a.incidentalTypes[other]; inc {
				continue
			}
			deps[other] = struct{}{}
		}
	}

	return deps
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
	// Emit any const/var blocks that reference this type before function users
	e.writeConstVarUsersForType(tn)
	e.writeUsersForType(tn)
	e.writeNL()
}

// writeConstVarUsersForType emits deferred const/var blocks that reference tn.
func (e *emitter) writeConstVarUsersForType(tn string) {
	blks := e.a.constVarUsers[tn]
	if len(blks) == 0 {
		return
	}
	// Preserve original order
	for _, b := range blks {
		if !e.isWritten(b) {
			e.writeDeclIfNeeded(b)
		}
	}
}

func (e *emitter) writeTypeBlocks() {
	for _, b := range e.a.typeBlocks {
		// Determine the type name for this block to check incidental status
		tn := ""
		for name, blk := range e.a.typeDeclFor {
			if blk == b {
				tn = name
				break
			}
		}

		// Skip incidental types; they will be emitted inline before first user
		if tn != "" {
			if _, inc := e.a.incidentalTypes[tn]; inc {
				continue
			}
		}

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

	// Process components in a deterministic order by picking start keys
	// sorted by exported-first and original position.
	startKeys := make([]string, 0, len(remainingSet))
	for k := range remainingSet {
		startKeys = append(startKeys, k)
	}
	startKeys = sortExportedFirstByOriginal(startKeys, e.funcByKey)

	for _, key := range startKeys {
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
		if e.isCtorReady(name) {
			e.writeFuncIfNotWritten(name)
		}
	}

	methodList := e.methods[tn]
	helperList := e.gatherHelperList(tn)

	cluster := append(append([]string{}, methodList...), helperList...)
	ord := sortByOriginal(cluster, e.funcByKey)

	firstCallerIdx, firstCaller := e.findFirstCallerInOrd(ord)
	pinned := e.computePinnedFromFirstCaller(ord, firstCallerIdx, firstCaller)

	// Apply "callee-after-first-caller" within this cluster by constructing
	// a filtered adjacency and callSeq that only enforce edges from a single
	// designated first caller per helper (shared callees are anchored under
	// that caller; later callers do not constrain placement).
	fAdj, fSeq := e.buildFirstCallerAdjacency(ord, methodList, helperList)

	ord = minimalReorderSubset(ord, pinned, fAdj, fSeq)

	ord = packWithinSubset(ord, pinned, fAdj, fSeq)
	for _, k := range ord {
		e.writeFuncIfNotWritten(k)
	}
}

// isCtorReady reports whether all types constructed by the constructor have
// already had their type declarations emitted. This ensures that a constructor
// returning multiple declared types appears after all of those types.
func (e *emitter) isCtorReady(ctor string) bool {
	types := e.ctorToTypes[ctor]
	if len(types) == 0 {
		return true
	}
	for _, tn := range types {
		b, ok := e.a.typeDeclFor[tn]
		if !ok {
			continue
		}
		if !e.isWritten(b) {
			return false
		}
	}
	return true
}

// buildFirstCallerAdjacency creates adjacency and call sequence maps for a
// type's method/helper cluster that implement the "callee-after-first-caller"
// rule: for each helper, only a single predecessor edge from its designated
// first caller is retained. The designated caller is chosen as follows:
//   - Prefer a method that calls the largest number of helpers (anchor).
//   - If the anchor calls H, use the anchor; otherwise, use the earliest method
//     in the cluster order that calls H.
//
// Call sequences are restricted to helper calls only.
func (e *emitter) buildFirstCallerAdjacency(ord, methodList, helperList []string) (map[string]map[string]struct{}, map[string][]string) {
	ordIdx := map[string]int{}
	for i, k := range ord {
		ordIdx[k] = i
	}

	// Build callers-in-cluster for each helper
	callersOf := map[string][]string{}
	helperSet := map[string]struct{}{}
	methodSet := map[string]struct{}{}
	for _, h := range helperList {
		helperSet[h] = struct{}{}
	}
	for _, m := range methodList {
		methodSet[m] = struct{}{}
	}

	for _, m := range methodList {
		for cal := range e.adj[m] {
			if _, isHelper := helperSet[cal]; isHelper {
				callersOf[cal] = append(callersOf[cal], m)
			}
		}
	}

	// Choose anchor: method that calls the most helpers (tie -> earliest in ord)
	anchor := ""
	maxCount := -1
	for _, m := range methodList {
		cnt := 0
		for cal := range e.adj[m] {
			if _, isHelper := helperSet[cal]; isHelper {
				cnt++
			}
		}
		if cnt > maxCount || (cnt == maxCount && cnt > 0 && (anchor == "" || ordIdx[m] < ordIdx[anchor])) {
			if cnt > 0 {
				anchor = m
				maxCount = cnt
			}
		}
	}

	// Initialise filtered structures
	fAdj := map[string]map[string]struct{}{}
	fSeq := map[string][]string{}
	for _, k := range ord {
		fAdj[k] = map[string]struct{}{}
	}

	// Record designated caller for each helper
	designated := map[string]string{}

	// For each helper, select designated first caller and add single edge
	for _, h := range helperList {
		cs := callersOf[h]
		if len(cs) == 0 {
			continue
		}

		// Prefer anchor if it calls h
		chosen := ""
		if anchor != "" {
			for _, m := range cs {
				if m == anchor {
					chosen = m
					break
				}
			}
		}
		if chosen == "" {
			// fallback: earliest caller in ord
			chosen = cs[0]
			for _, m := range cs[1:] {
				if ordIdx[m] < ordIdx[chosen] {
					chosen = m
				}
			}
		}

		designated[h] = chosen

		if _, ok := fAdj[chosen]; !ok {
			fAdj[chosen] = map[string]struct{}{}
		}
		fAdj[chosen][h] = struct{}{}
	}

	// Restrict call sequences: only include helpers for which the method is
	// the designated first caller, preserving the caller's original first-use order.
	for _, m := range methodList {
		if seq, ok := e.callSeq[m]; ok && len(seq) > 0 {
			filtered := make([]string, 0, len(seq))
			seen := map[string]struct{}{}
			for _, c := range seq {
				if _, isHelper := helperSet[c]; isHelper && designated[c] == m {
					if _, s := seen[c]; !s {
						filtered = append(filtered, c)
						seen[c] = struct{}{}
					}
				}
			}
			if len(filtered) > 0 {
				fSeq[m] = filtered
			}
		}
	}

	// Methods do not depend on other methods in this filtered model; we avoid
	// introducing method->method edges so methods keep original relative order.

	return fAdj, fSeq
}

func (e *emitter) writeUsersForType(tn string) {
	userList := []string{}

	for _, fb := range e.a.funcBlocks {
		if _, ok := e.users[tn][fb.key]; !ok {
			continue
		}

		// Ensure we never emit a method before its receiver type has been
		// written. This can occur when a method is considered a "user" of a
		// different type that is processed earlier in source order.
		if fb.isMethod {
			if b, ok := e.a.typeDeclFor[fb.recvType]; ok {
				if !e.isWritten(b) {
					// receiver type not yet emitted; skip here (it will be
					// emitted with its own type cluster later)
					continue
				}
			}
		}

		userList = append(userList, fb.key)
	}

	if len(userList) == 0 {
		return
	}

	uord := sortExportedFirstByOriginal(userList, e.funcByKey)
	uord = minimalReorderSubset(uord, 0, e.adj, e.callSeq)

	uord = packWithinSubset(uord, 0, e.adj, e.callSeq)

	// Build a quick set of users to avoid packing helpers that are themselves
	// classified as users of this type (those will be emitted according to the
	// user ordering we computed above).
	userSet := map[string]struct{}{}
	for _, u := range uord {
		userSet[u] = struct{}{}
	}

	for _, k := range uord {
		// If this user is a method and references an incidental type, ensure
		// that type is emitted immediately before the method (kept adjacent).
		if fb, ok := e.funcByKey[k]; ok && fb.isMethod {
			// Collect incidental types referenced by this user and emit them
			// in deterministic order by their original declaration position.
			incList := make([]string, 0, len(e.a.incidentalTypes))
			for inc := range e.a.incidentalTypes {
				if _, ok := e.users[inc][k]; ok {
					incList = append(incList, inc)
				}
			}
			if len(incList) > 1 {
				sort.SliceStable(incList, func(i, j int) bool {
					bi := e.a.typeDeclFor[incList[i]]
					bj := e.a.typeDeclFor[incList[j]]
					if bi.start != bj.start {
						return bi.start < bj.start
					}
					return incList[i] < incList[j]
				})
			}
			for _, inc := range incList {
				if b, ok := e.a.typeDeclFor[inc]; ok && !e.isWritten(b) {
					e.writeDeclIfNeeded(b)
				}
			}
		}

		// Write the user itself
		e.writeFuncIfNotWritten(k)

		// After writing a free-function user, pack its private helpers
		// immediately beneath it in first-use order, provided doing so does
		// not violate caller-before-callee (i.e., do not move a shared helper
		// before another not-yet-written caller).
		e.writeHelpersUnderCaller(k, userSet)
	}
}

// writeHelpersUnderCaller packs and writes helper free functions called by
// the given caller directly under it in first-use order, subject to the
// constraint that a helper is only packed if all of its other callers (if any)
// have already been written. This mirrors the callee-after-first-caller rule
// used for method clusters, applied within a type's users section for free
// functions like Generate().
func (e *emitter) writeHelpersUnderCaller(caller string, userSet map[string]struct{}) {
	// Depth-first packing of helper subtrees under the given caller in
	// first-use order. We intentionally prefer callee-after-first-caller:
	// once a helper is placed under this caller, later callers do not force
	// the helper to move further down. This mirrors method cluster behaviour.
	visited := map[string]struct{}{}
	var pack func(string)
	pack = func(curCaller string) {
		seq, ok := e.callSeq[curCaller]
		if !ok || len(seq) == 0 {
			return
		}
		seenThis := map[string]struct{}{}
		for _, cal := range seq {
			if _, s := seenThis[cal]; s {
				continue
			}
			seenThis[cal] = struct{}{}

			fb, ok := e.funcByKey[cal]
			if !ok || fb.isMethod {
				continue
			}
			if _, isUser := userSet[cal]; isUser {
				// another user of the same type; leave it to user ordering
				continue
			}
			if _, already := e.writtenFunc[cal]; already {
				continue
			}
			if _, seen := visited[cal]; seen {
				continue
			}

			// Emit helper directly under curCaller
			e.writeFuncIfNotWritten(cal)
			visited[cal] = struct{}{}

			// Recursively pack helpers of this helper
			pack(cal)
		}
	}

	pack(caller)
}

func (e *emitter) writeRemainingFuncs() {
	writtenKeys := e.buildWrittenKeys()

	for _, fb := range e.a.funcBlocks {
		if _, ok := writtenKeys[fb.key]; ok {
			continue
		}

		// Inline incidental type declaration immediately before first user
		for inc := range e.a.incidentalTypes {
			if _, ok := e.users[inc][fb.key]; ok {
				if b, ok := e.a.typeDeclFor[inc]; ok && !e.isWritten(b) {
					e.writeDeclIfNeeded(b)
				}
			}
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
			if _, inc := e.a.incidentalTypes[tn]; inc {
				// Defer these users to allow emitting the incidental type inline.
				continue
			}

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

// indexByte is a tiny helper to avoid importing strings for a single use.
func indexByte(s string, c byte) int {
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			return i
		}
	}
	return -1
}
