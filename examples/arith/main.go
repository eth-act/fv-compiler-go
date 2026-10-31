// Integer arithmetic: constant folding, strength reduction, division by constants,
// overflow-sensitive shifts and comparisons (opt, divisible, divmod, prove, known bits).
package main

import "os"

//go:noinline
func mix(a, b int64, c uint32, d int8) int64 {
	x := a*7 + b/3 - int64(c%5)
	x ^= int64(d) << (c & 7)
	if x < 0 {
		x = -x
	}
	return x>>2 | int64(uint64(a)>>61)
}

//go:noinline
func divisible(n uint64) bool { return n%6 == 0 && n%10 != 0 }

//go:noinline
func clamp(x, lo, hi int) int {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

func main() {
	s := mix(int64(len(os.Args)), 1000, 77, -3)
	if divisible(uint64(s)) {
		s++
	}
	os.Exit(clamp(int(s), 0, 1) - 1)
}
