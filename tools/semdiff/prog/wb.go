package main

// Functions of the write-barrier difftest (#36): pointer stores into heap objects and through
// pointers, so the `writebarrier` pass expands them (StoreWB, MoveWB, ZeroWB: a load of
// runtime.writeBarrier, a branch to the buffered or helper path, the plain store, WBend).

func init() {
	for k, v := range map[string]any{
		"wbList": wbList, "wbPrepend": wbPrepend, "wbSetNext": wbSetNext, "wbStr": wbStr,
		"wbCopy": wbCopy, "wbClear": wbClear, "wbSlicePtrs": wbSlicePtrs,
		"wbAppendStr": wbAppendStr, "wbSwapPtr": wbSwapPtr, "wbNode": wbNode,
		"wbArrPtrs": wbArrPtrs, "wbRec": wbRec,
	} {
		funcs[k] = v
	}
}

//go:noinline
func wbList(n int) int {
	var l *node
	for i := range n & 15 {
		x := new(node)
		x.V = i
		x.Next = l
		l = x
	}
	return listSum(l)
}

//go:noinline
func wbPrepend(l *node, v int) *node { return &node{V: v, Next: l} }

//go:noinline
func wbSetNext(a, b *node) int {
	if a == nil {
		return -1
	}
	a.Next = b
	return listSum(a)
}

//go:noinline
func wbStr(r *rec, s string) string {
	if r == nil {
		return ""
	}
	old := r.S
	r.S = s
	return old
}

//go:noinline
func wbCopy(dst, src *big) int {
	if dst == nil || src == nil {
		return -1
	}
	*dst = *src
	return dst.N + len(dst.Tag)
}

//go:noinline
func wbClear(p *big) int {
	if p == nil {
		return -1
	}
	n := len(p.Tag)
	*p = big{}
	return n
}

//go:noinline
func wbSlicePtrs(n int) int {
	s := make([]*int, n&7)
	for i := range s {
		x := i * 3
		s[i] = &x
	}
	t := 0
	for _, p := range s {
		t += *p
	}
	return t
}

//go:noinline
func wbAppendStr(s []string, t string) []string { return append(s, t, t+"!") }

//go:noinline
func wbSwapPtr(pp, qq **int) {
	if pp == nil || qq == nil {
		return
	}
	*pp, *qq = *qq, *pp
}

//go:noinline
func wbNode(p, q *node) node {
	if p == nil {
		return node{}
	}
	*p = node{V: 1, Next: q}
	return *p
}

//go:noinline
func wbArrPtrs(a *[4]*int, p *int, i int) int {
	if a == nil {
		return -1
	}
	a[i&3] = p
	t := 0
	for _, q := range a {
		if q != nil {
			t += *q
		}
	}
	return t
}

//go:noinline
func wbRec(rs []rec, s string, i int) []rec {
	if len(rs) == 0 {
		return rs
	}
	rs[uint(i)%uint(len(rs))].S = s
	return rs
}
