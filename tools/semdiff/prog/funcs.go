package main

import "math/bits"

// Functions of the P1 difftest: integer and boolean parameters and results only, no memory,
// no calls (the math/bits functions used are intrinsics on arm64; bits.Div64 is not, so it is
// left out). Division and shifts by variables reach the runtime's panicking entry points
// (panicdivide, panicshift).
var funcs = map[string]any{
	"add8": add8, "sub16": sub16, "mul32": mul32, "arith64": arith64, "mixw": mixw,
	"divs8": divs8, "divs16": divs16, "divs32": divs32, "divs64": divs64,
	"divu8": divu8, "divu32": divu32, "divu64": divu64, "modsu": modsu,
	"divconst": divconst, "divconstu": divconstu, "divisible": divisible,
	"shl": shl, "shr": shr, "shru": shru, "shifts8": shifts8, "shiftsu": shiftsu, "shiftc": shiftc,
	"cmp": cmp, "cmpu": cmpu, "boolops": boolops, "shortc": shortc,
	"clamp": clamp, "abs": abs, "sel": sel, "minmax": minmax, "minmaxu": minmaxu,
	"conv": conv, "conv2": conv2,
	"sum": sum, "gcd": gcd, "collatz": collatz, "nested": nested, "popl": popl,
	"sw": sw, "swsparse": swsparse,
	"bitsf": bitsf, "bitsrot": bitsrot, "mulhi": mulhi, "addc": addc, "subb": subb,
	"multi": multi, "overflow": overflow, "isPow2": isPow2, "hash": hash,
}

//go:noinline
func add8(a, b int8) int8 { return a + b*3 - (a ^ b) }

//go:noinline
func sub16(a, b uint16) (uint16, int16) { return a - b, int16(a) - int16(b)<<2 }

//go:noinline
func mul32(a, b int32, c uint32) (int32, uint32) { return a * b, c * uint32(a) * 0x9e3779b9 }

//go:noinline
func arith64(a, b int64) int64 {
	x := a*7 + b - (a &^ b)
	x |= a >> 3
	return x*x - -a + ^b
}

//go:noinline
func mixw(a int8, b int16, c int32, d int64, e uint8, f uint16, g uint32, h uint64) int64 {
	return int64(a)*int64(e) + int64(b)*int64(f) - int64(c)*int64(g) + d ^ int64(h)
}

//go:noinline
func divs8(a, b int8) (int8, int8) { return a / b, a % b }

//go:noinline
func divs16(a, b int16) (int16, int16) { return a / b, a % b }

//go:noinline
func divs32(a, b int32) (int32, int32) { return a / b, a % b }

//go:noinline
func divs64(a, b int64) (int64, int64) { return a / b, a % b }

//go:noinline
func divu8(a, b uint8) (uint8, uint8) { return a / b, a % b }

//go:noinline
func divu32(a, b uint32) (uint32, uint32) { return a / b, a % b }

//go:noinline
func divu64(a, b uint64) (uint64, uint64) { return a / b, a % b }

//go:noinline
func modsu(a int64, b uint64) int64 {
	if b == 0 {
		return -1
	}
	return int64(uint64(a)%b) + a%int64(b|1)
}

//go:noinline
func divconst(a int64, b int32, c int16, d int8) (int64, int64, int32, int16, int8) {
	return a / 7, a % 10, b / -3, c % 1000, d / 4
}

//go:noinline
func divconstu(a uint64, b uint32, c uint16, d uint8) (uint64, uint64, uint32, uint16, uint8) {
	return a / 7, a % 10, b / 3, c % 1000, d / 6
}

//go:noinline
func divisible(n uint64, m int32) (bool, bool, bool) {
	return n%6 == 0, m%10 != 0, n%(1<<20) == 0
}

//go:noinline
func shl(a int64, s int) int64 { return a << s }

//go:noinline
func shr(a int64, s int) int64 { return a >> s }

//go:noinline
func shru(a uint64, s int) uint64 { return a >> s }

//go:noinline
func shifts8(a int8, b uint8, s uint8) (int8, uint8, int8) { return a << s, b >> s, a >> s }

//go:noinline
func shiftsu(a uint32, s uint16, t uint64) (uint32, uint32, int32) {
	return a << s, a >> t, int32(a) >> (s & 31)
}

//go:noinline
func shiftc(a uint64, b int32) (uint64, int32, uint64) {
	return a<<63 | a>>1, b >> 31, (a >> 70) + (a << 3)
}

//go:noinline
func cmp(a, b int64, c, d int8) (bool, bool, bool, bool) {
	return a < b, a <= b, c == d, c > d
}

//go:noinline
func cmpu(a, b uint64, c, d uint16) (bool, bool, bool) {
	return a < b, c >= d, a != uint64(c)
}

//go:noinline
func boolops(a, b, c bool) (bool, bool, bool, uint8) {
	x := a && !b || c
	y := a == b
	z := a != c
	var n uint8
	if x {
		n = 1
	}
	return x, y, z, n
}

//go:noinline
func shortc(a, b int) int {
	if a > 0 && b > 0 || a < -10 {
		return a + b
	}
	if a == b || (a < b && b < 100) {
		return 1
	}
	return 0
}

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

//go:noinline
func abs(x int64) int64 {
	if x < 0 {
		x = -x
	}
	return x
}

//go:noinline
func sel(c bool, a, b int32) int32 {
	r := b
	if c {
		r = a
	}
	return r
}

//go:noinline
func minmax(a, b, c int64) (int64, int64) { return min(a, b, c), max(a, b) }

//go:noinline
func minmaxu(a, b uint32, c, d uint64) (uint32, uint64) { return max(a, b), min(c, d) }

//go:noinline
func conv(a int64) (int8, uint8, int16, uint16, int32, uint32, uint64) {
	return int8(a), uint8(a), int16(a), uint16(a), int32(a), uint32(a), uint64(a)
}

//go:noinline
func conv2(a int8, b uint8, c int32, d uint32) (int64, uint64, int64, uint64, int16) {
	return int64(a), uint64(b), int64(c), uint64(d), int16(b) + int16(a)
}

//go:noinline
func sum(n int) int {
	s := 0
	for i := 0; i < n && i < 1000; i++ {
		s += i * i
	}
	return s
}

//go:noinline
func gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

//go:noinline
func collatz(n uint64) int {
	steps := 0
	for n > 1 && steps < 500 {
		if n%2 == 0 {
			n /= 2
		} else {
			n = 3*n + 1
		}
		steps++
	}
	return steps
}

//go:noinline
func nested(n, m int) int {
	t := 0
	for i := range n % 20 {
		for j := i; j < m%20; j++ {
			if (i+j)%3 == 0 {
				continue
			}
			t += i ^ j
		}
	}
	return t
}

//go:noinline
func popl(x uint64) int {
	c := 0
	for x != 0 {
		x &= x - 1
		c++
	}
	return c
}

//go:noinline
func sw(x, y int) int {
	// Case bodies depend on y, so the switch is a jump table, not a lookup in a static array.
	switch x {
	case 0:
		return y + 10
	case 1:
		return y * 11
	case 2:
		return y - 22
	case 3:
		return y ^ 33
	case 4:
		return y & 44
	case 5:
		return y | 55
	case 6:
		return y << 6
	case 7:
		return y >> 7
	case 8:
		return -y
	case 9:
		return y * y
	}
	return -1
}

//go:noinline
func swsparse(x uint32) int {
	switch x {
	case 1, 100, 1000:
		return 1
	case 7:
		return 7
	case 1 << 20:
		return 20
	case 0xffffffff:
		return -1
	}
	return 0
}

//go:noinline
func bitsf(x uint64, y uint32, z uint16, w uint8) (int, int, int, int, uint64, uint32, uint16, int, uint8) {
	return bits.TrailingZeros64(x), bits.Len32(y), bits.OnesCount16(z), bits.LeadingZeros8(w),
		bits.ReverseBytes64(x), bits.Reverse32(y), bits.ReverseBytes16(z), bits.TrailingZeros8(w),
		bits.Reverse8(w)
}

//go:noinline
func bitsrot(x uint64, y uint32, k int) (uint64, uint32, uint16, uint8) {
	return bits.RotateLeft64(x, k), bits.RotateLeft32(y, -k), bits.RotateLeft16(uint16(x), k), bits.RotateLeft8(uint8(y), 3)
}

//go:noinline
func mulhi(x, y uint64, a, b int64) (uint64, uint64, int64, uint64) {
	hi, lo := bits.Mul64(x, y)
	return hi, lo, a / 1000003, x / 1000003
}

//go:noinline
func addc(x, y, c uint64) (uint64, uint64) { return bits.Add64(x, y, c&1) }

//go:noinline
func subb(x, y, c uint64) (uint64, uint64) { return bits.Sub64(x, y, c&1) }

//go:noinline
func multi(a int, b bool) (int, bool, int, uint8) {
	if b {
		return a, !b, a * 2, uint8(a)
	}
	return -a, b, a / 2, uint8(a >> 8)
}

//go:noinline
func overflow(a, b int64) (int64, bool) {
	c := a * b
	if a != 0 && c/a != b {
		return 0, true
	}
	return c, false
}

//go:noinline
func isPow2(x uint64) bool { return x != 0 && x&(x-1) == 0 }

//go:noinline
func hash(x uint64, n int) uint64 {
	h := uint64(14695981039346656037)
	for i := range n % 64 {
		h ^= (x >> (uint(i) % 64)) & 0xff
		h *= 1099511628211
	}
	return h
}
