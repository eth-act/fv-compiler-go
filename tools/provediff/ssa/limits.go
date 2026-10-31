package ssa

import (
	"fmt"
	"math"
	"math/rand/v2"
)

// The limit arithmetic of prove.go (type limit up to constValue) is copied into
// prove_limit.go by scripts/prove-difftest.sh.

var limitOps = []string{"add", "sub", "mul", "exp2", "com", "neg", "ctz", "bitlen", "popcount",
	"const", "fixed", "intersect", "safe"}

var interesting = []int64{0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128, 255, 256, 1000,
	math.MaxInt8, math.MinInt8, math.MaxInt16, math.MinInt16, math.MaxInt32, math.MinInt32,
	math.MaxUint32, math.MaxInt64, math.MinInt64, -1, -2, -8, -128, -129}

func randInt(r *rand.Rand) int64 {
	switch r.IntN(4) {
	case 0:
		return interesting[r.IntN(len(interesting))]
	case 1:
		return interesting[r.IntN(len(interesting))] + int64(r.IntN(5)) - 2
	case 2:
		return int64(r.IntN(300)) - 150
	default:
		return int64(r.Uint64())
	}
}

func randLimit(r *rand.Rand) limit {
	a, b := randInt(r), randInt(r)
	if a > b && r.IntN(4) != 0 {
		a, b = b, a
	}
	c, d := uint64(randInt(r)), uint64(randInt(r))
	if c > d && r.IntN(4) != 0 {
		c, d = d, c
	}
	switch r.IntN(6) {
	case 0: // constant
		return limit{min: a, max: a, umin: uint64(a), umax: uint64(a)}
	case 1:
		return noLimit()
	case 2: // only signed
		l := noLimit()
		l.min, l.max = a, b
		return l
	case 3: // only unsigned
		l := noLimit()
		l.umin, l.umax = c, d
		return l
	}
	return limit{min: a, max: b, umin: c, umax: d}
}

func lstr(l limit) string { return fmt.Sprintf("%d:%d:%d:%d", l.min, l.max, l.umin, l.umax) }

// LimitCase returns "L <op> <b> <l1> <l2> <result>"; limits are min:max:umin:umax.
func LimitCase(r *rand.Rand) string {
	op := limitOps[r.IntN(len(limitOps))]
	b := []uint{8, 16, 32, 64}[r.IntN(4)]
	l1, l2 := randLimit(r), randLimit(r)
	var res string
	switch op {
	case "add":
		res = lstr(l1.add(l2, b))
	case "sub":
		res = lstr(l1.sub(l2, b))
	case "mul":
		res = lstr(l1.mul(l2, b))
	case "exp2":
		res = lstr(l1.exp2(b))
	case "com":
		res = lstr(l1.com(b))
	case "neg":
		res = lstr(l1.neg(b))
	case "ctz":
		res = lstr(l1.ctz(b))
	case "bitlen":
		res = lstr(l1.bitlen(b))
	case "popcount":
		res = lstr(l1.popcount(b))
	case "const":
		v, ok := l1.constValue()
		res = fmt.Sprintf("%d:%v", v, ok)
	case "fixed":
		f, c := l1.unsignedFixedLeadingBits()
		res = fmt.Sprintf("%d:%d", f, c)
	case "intersect":
		res = lstr(l1.intersect(l2))
	case "safe":
		s1, o1 := safeAdd(l1.min, l2.max, b)
		s2, o2 := safeSub(l1.min, l2.max, b)
		s3, o3 := safeAddU(l1.umin, l2.umax, b)
		s4, o4 := safeSubU(l1.umin, l2.umax, b)
		res = fmt.Sprintf("%d:%v:%d:%v:%d:%v:%d:%v", s1, o1, s2, o2, s3, o3, s4, o4)
	}
	return fmt.Sprintf("L %s %d %s %s %s", op, b, lstr(l1), lstr(l2), res)
}
