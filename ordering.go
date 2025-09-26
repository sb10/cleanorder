package main

import "sort"

// sortByOriginal returns a copy of keys ordered by original byte offset.
func sortByOriginal(keys []string, funcByKey map[string]funcBlock) []string {
	out := append([]string(nil), keys...)
	sort.SliceStable(out, func(i, j int) bool { return funcByKey[out[i]].start < funcByKey[out[j]].start })

	return out
}

// minimalReorderSubset performs minimal movement respecting predecessor edges.
//
//nolint:gocognit,gocyclo,cyclop,funlen // algorithmic complexity; refactor would be risky
func minimalReorderSubset(
	keys []string,
	pinned int,
	adj map[string]map[string]struct{},
	callSeq map[string][]string,
) []string {
	order := append([]string(nil), keys...)
	pos := map[string]int{}
	keysSet := map[string]struct{}{}

	for i, k := range order {
		pos[k] = i
		keysSet[k] = struct{}{}
	}

	pred := map[string]map[string]struct{}{}
	getPred := func(k string) map[string]struct{} {
		if m, ok := pred[k]; ok {
			return m
		}

		m := map[string]struct{}{}
		pred[k] = m

		return m
	}

	for caller, neigh := range adj {
		if _, ok := keysSet[caller]; !ok {
			continue
		}

		for callee := range neigh {
			if _, ok := keysSet[callee]; ok {
				getPred(callee)[caller] = struct{}{}
			}
		}
	}

	for _, seq := range callSeq {
		filt := make([]string, 0, len(seq))
		for _, c := range seq {
			if _, ok := keysSet[c]; ok {
				filt = append(filt, c)
			}
		}

		for i := 0; i < len(filt); i++ {
			for j := i + 1; j < len(filt); j++ {
				a, b := filt[i], filt[j]
				getPred(b)[a] = struct{}{}
			}
		}
	}

	changed := true

	const extraGuard = 5

	guard := len(order)*len(order) + extraGuard
	for changed && guard > 0 {
		changed = false
		guard--

		for i := 0; i < len(order); i++ {
			if i < pinned {
				continue
			}

			g := order[i]

			maxIdx := -1
			for p := range getPred(g) {
				if idx, ok := pos[p]; ok && idx > maxIdx {
					maxIdx = idx
				}
			}

			if maxIdx < 0 || maxIdx < pos[g] {
				continue
			}

			from := pos[g]

			to := maxIdx + 1
			if to > len(order) {
				to = len(order)
			}

			if to-1 == from {
				continue
			}

			order = append(order[:from], order[from+1:]...)
			if to > from {
				to--
			}

			order = append(order[:to], append([]string{g}, order[to:]...)...)
			for j, k := range order {
				pos[k] = j
			}

			changed = true
		}
	}

	return order
}

// packWithinSubset packs callees below their callers while respecting
// predecessor constraints.
//
//nolint:gocognit,gocyclo,cyclop,funlen // algorithmic complexity; refactor would be risky
func packWithinSubset(
	order []string,
	pinned int,
	adj map[string]map[string]struct{},
	callSeq map[string][]string,
) []string {
	out := append([]string(nil), order...)
	if len(out) == 0 {
		return out
	}

	keysSet := map[string]struct{}{}
	for _, k := range out {
		keysSet[k] = struct{}{}
	}

	pred := map[string]map[string]struct{}{}
	getPred := func(k string) map[string]struct{} {
		if m, ok := pred[k]; ok {
			return m
		}

		m := map[string]struct{}{}
		pred[k] = m

		return m
	}

	for caller, neigh := range adj {
		if _, ok := keysSet[caller]; !ok {
			continue
		}

		for callee := range neigh {
			if _, ok := keysSet[callee]; ok {
				getPred(callee)[caller] = struct{}{}
			}
		}
	}

	for _, seq := range callSeq {
		filt := make([]string, 0, len(seq))
		for _, c := range seq {
			if _, ok := keysSet[c]; ok {
				filt = append(filt, c)
			}
		}

		for i := 0; i < len(filt); i++ {
			for j := i + 1; j < len(filt); j++ {
				a, b := filt[i], filt[j]
				getPred(b)[a] = struct{}{}
			}
		}
	}

	pos := map[string]int{}
	for i, k := range out {
		pos[k] = i
	}

	for ci := 0; ci < len(out); ci++ {
		caller := out[ci]

		seq := callSeq[caller]
		if len(seq) == 0 {
			continue
		}

		filtered := make([]string, 0, len(seq))
		seen := map[string]struct{}{}

		for _, v := range seq {
			if _, ok := keysSet[v]; ok {
				if _, s := seen[v]; !s {
					filtered = append(filtered, v)
					seen[v] = struct{}{}
				}
			}
		}

		insertPos := max(ci+1, pinned)

		for _, v := range filtered {
			maxPred := -1
			for p := range getPred(v) {
				if idx, ok := pos[p]; ok && idx > maxPred {
					maxPred = idx
				}
			}

			desired := max(max(maxPred+1, insertPos), pinned)

			cur := pos[v]
			if cur == desired {
				insertPos = desired + 1

				continue
			}

			out = append(out[:cur], out[cur+1:]...)
			if desired > cur {
				desired--
			}

			if desired < 0 {
				desired = 0
			}

			if desired > len(out) {
				desired = len(out)
			}

			out = append(out[:desired], append([]string{v}, out[desired:]...)...)

			pos = map[string]int{}
			for i, k := range out {
				pos[k] = i
			}

			insertPos = max(pos[v]+1, pinned)
		}
	}

	return out
}
