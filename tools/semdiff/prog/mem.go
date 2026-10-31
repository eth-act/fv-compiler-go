package main

import "unsafe"

// Functions of the P2 difftest: memory, pointers and composites (slices, strings, structs,
// arrays, pointers), still without calls other than the runtime's panicking entry points:
// no append/make/new/string concatenation/map/interface method calls.

type pair struct {
	X, Y int
}

type rec struct {
	A int32
	B bool
	C uint8
	S string
	P pair
}

type big struct {
	N   int
	Arr [6]int
	Tag string
}

type node struct {
	V    int
	Next *node
}

func init() {
	for k, v := range map[string]any{
		"sliceSum": sliceSum, "sliceIdx": sliceIdx, "sliceSet": sliceSet, "sliceSub": sliceSub,
		"sliceRev": sliceRev, "sliceCap": sliceCap, "bytesXor": bytesXor, "sliceCopy3": sliceCopy3,
		"strLen": strLen, "strIdx": strIdx, "strSub": strSub, "strCount": strCount,
		"strConst": strConst, "strIsAbc": strIsAbc, "split2": split2,
		"pairSwap": pairSwap, "pairPtr": pairPtr, "recGet": recGet, "recMod": recMod,
		"ptrInc": ptrInc, "ptrDeref": ptrDeref, "ptrSwap": ptrSwap, "listSum": listSum,
		"arrParam": arrParam, "arrLocal": arrLocal, "arrRet": arrRet, "arr1": arr1,
		"bigCopy": bigCopy, "bigZero": bigZero, "bigSum": bigSum,
		"table": table, "table8": table8, "setPtr": setPtr, "nilSlice": nilSlice,
		"ptrEq": ptrEq, "sliceAlias": sliceAlias, "sliceData": sliceData, "strData": strData,
	} {
		funcs[k] = v
	}
}

//go:noinline
func sliceSum(s []int) int {
	t := 0
	for _, x := range s {
		t += x
	}
	return t
}

//go:noinline
func sliceIdx(s []int, i int) int { return s[i] }

//go:noinline
func sliceSet(s []int, i, v int) int {
	s[i] = v
	return len(s)
}

//go:noinline
func sliceSub(s []int, i, j int) []int { return s[i:j] }

//go:noinline
func sliceRev(s []int) {
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
}

//go:noinline
func sliceCap(s []int, i int) (int, int) {
	t := s[:i]
	return len(t), cap(t)
}

//go:noinline
func bytesXor(b []byte, k byte) uint64 {
	var h uint64
	for i := range b {
		b[i] ^= k
		h = h*31 + uint64(b[i])
	}
	return h
}

//go:noinline
func sliceCopy3(dst, src []int) int {
	n := 0
	for i := 0; i < 3 && i < len(dst) && i < len(src); i++ {
		dst[i] = src[i]
		n++
	}
	return n
}

//go:noinline
func strLen(s string) int { return len(s) }

//go:noinline
func strIdx(s string, i int) byte { return s[i] }

//go:noinline
func strSub(s string, i, j int) string { return s[i:j] }

//go:noinline
func strCount(s string, c byte) int {
	n := 0
	for i := 0; i < len(s); i++ {
		if s[i] == c {
			n++
		}
	}
	return n
}

//go:noinline
func strConst(i int) (byte, string) {
	const s = "hello, gofv"
	return s[i%len(s)], s[i%4:]
}

//go:noinline
func strIsAbc(s string) bool { return s == "abc" }

//go:noinline
func split2(s string, i int) (string, string) {
	if i < 0 || i > len(s) {
		return "", s
	}
	return s[:i], s[i:]
}

//go:noinline
func pairSwap(p pair) pair { return pair{p.Y, p.X} }

//go:noinline
func pairPtr(p *pair, d int) int {
	p.X += d
	p.Y -= d
	return p.X * p.Y
}

//go:noinline
func recGet(r rec) (int32, bool, uint8, string, int) { return r.A, r.B, r.C, r.S, r.P.X + r.P.Y }

//go:noinline
func recMod(r *rec, s string) rec {
	r.A++
	r.B = !r.B
	r.S = s
	r.P.Y = int(r.C)
	return *r
}

//go:noinline
func ptrInc(p *int) int {
	*p++
	return *p
}

//go:noinline
func ptrDeref(p *int, q *int) int { return *p - *q }

//go:noinline
func ptrSwap(p, q *int) {
	*p, *q = *q, *p
}

//go:noinline
func listSum(n *node) int {
	t := 0
	for k := 0; n != nil && k < 100; k++ {
		t += n.V
		n = n.Next
	}
	return t
}

//go:noinline
func arrParam(a [4]int, i int) int { return a[i&3] + a[0] }

//go:noinline
func arrLocal(i int) int {
	var a [8]int
	for k := range a {
		a[k] = k * k
	}
	return a[i&7]
}

//go:noinline
func arrRet(x int) [3]int { return [3]int{x, x + 1, x * 2} }

//go:noinline
func arr1(a [1]int, i int) int { return a[i] }

//go:noinline
func bigCopy(p *big) big {
	b := *p
	b.N++
	b.Arr[2] = b.N
	return b
}

//go:noinline
func bigZero(p *big) int {
	n := p.N
	*p = big{}
	return n
}

//go:noinline
func bigSum(b big) int {
	t := b.N
	for _, x := range b.Arr {
		t += x
	}
	return t + len(b.Tag)
}

//go:noinline
func table(i int) int {
	switch i {
	case 0:
		return 7
	case 1:
		return 11
	case 2:
		return 13
	case 3:
		return 17
	case 4:
		return 19
	case 5:
		return 23
	case 6:
		return 29
	case 7:
		return 31
	}
	return -1
}

//go:noinline
func table8(i uint8) string {
	switch i {
	case 0:
		return "zero"
	case 1:
		return "one"
	case 2:
		return "two"
	case 3:
		return "three"
	case 4:
		return "four"
	}
	return "many"
}

//go:noinline
func setPtr(pp **int, p *int) int {
	*pp = p
	return **pp
}

//go:noinline
func nilSlice(s []int) (bool, int, bool) { return s == nil, len(s), len(s) == 0 }

//go:noinline
func ptrEq(p, q *int) (bool, bool) { return p == q, p != nil }

//go:noinline
func sliceAlias(s []int, i int) int {
	t := s[1:]
	t[0] = i
	return s[1] + t[0]
}

// sliceData dereferences the data pointer of a possibly-nil slice: the open question
// "SlicePtr non-nil" of docs/plans/semantics.md §10 (nilcheckelim treats SlicePtr as non-nil).
//
//go:noinline
func sliceData(s []int) int {
	if s != nil && len(s) == 0 {
		return -1 // the data pointer of an empty non-nil slice points past its allocation
	}
	return *unsafe.SliceData(s)
}

//go:noinline
func strData(s string) byte {
	if len(s) == 0 {
		return 0
	}
	return *unsafe.StringData(s)
}
