package main

// Copies of the regMask helpers of _gen/main.go (Copyright 2015 The Go Authors, BSD licence),
// which the arch op files (ARM64Ops.go) call. checkFuncs verifies that each declaration below
// is textually identical to the one in main.go.

import "math/bits"

func regMaskAt(i uint) regMask {
	if i < 64 {
		return regMask{v1: 1 << i}
	}
	return regMask{v2: 1 << (i - 64)}
}

func (r regMask) empty() bool {
	return r.v1 == 0 && r.v2 == 0
}

func (r regMask) hasReg(i uint) bool {
	if i < 64 {
		return (r.v1>>i)&1 != 0
	}
	return (r.v2>>(i-64))&1 != 0
}

func (r regMask) addReg(i uint) regMask {
	if i < 64 {
		return regMask{r.v1 | 1<<i, r.v2}
	}
	return regMask{r.v1, r.v2 | 1<<(i-64)}
}

func (r regMask) union(s regMask) regMask {
	return regMask{r.v1 | s.v1, r.v2 | s.v2}
}

func (r regMask) minus(s regMask) regMask {
	return regMask{r.v1 &^ s.v1, r.v2 &^ s.v2}
}

func countRegs(r regMask) int {
	return bits.OnesCount64(r.v1) + bits.OnesCount64(r.v2)
}

// for sorting a pair of integers by key
type intPair struct {
	key, val int
}
type byKey []intPair

func (a byKey) Len() int           { return len(a) }
func (a byKey) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a byKey) Less(i, j int) bool { return a[i].key < a[j].key }

// regMaskFuncs are the declarations above that checkFuncs compares with main.go ("T.m" for
// methods).
var regMaskFuncs = []string{"regMaskAt", "regMask.empty", "regMask.hasReg", "regMask.addReg",
	"regMask.union", "regMask.minus", "countRegs", "byKey.Len", "byKey.Swap", "byKey.Less"}
