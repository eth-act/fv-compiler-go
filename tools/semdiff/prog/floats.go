package main

// Functions of the P4 difftest: float32/float64 arithmetic, comparisons, conversions (including
// out-of-range and NaN float → integer conversions, arm64's FCVTZS/FCVTZU), math intrinsics
// (Sqrt, Floor, Ceil, Trunc, Round, RoundToEven, Abs, FMA), Go's min/max, bit casts, float
// constants, loops, memory, and complex values.
//
// arm64 lowering fuses a + x*y into FMADD (ARM64.rules, "useFMA"; the Go spec allows it), which
// the generic ops' semantics does not: a product feeding an addition is written float64(x*y),
// an explicit conversion that rounds (Round64F) and blocks the fusion. Complex multiplication
// and division are left out for the same reason (the frontend's x*y-u*v, runtime.complex128div).

import "math"

func init() {
	for k, v := range map[string]any{
		"fadd64": fadd64, "fsub64": fsub64, "fmul64": fmul64, "fdiv64": fdiv64, "fneg64": fneg64,
		"fadd32": fadd32, "fsub32": fsub32, "fmul32": fmul32, "fdiv32": fdiv32, "fneg32": fneg32,
		"fcmp64": fcmp64, "fcmp32": fcmp32, "fsign": fsign,
		"fsqrt": fsqrt, "fsqrt32": fsqrt32, "ffloor": ffloor, "fceil": fceil, "ftrunc": ftrunc,
		"fround": fround, "froundeven": froundeven, "fabs": fabs, "fcopysign": fcopysign,
		"ffma": ffma, "fmin64": fmin64, "fmax64": fmax64, "fmin32": fmin32, "fmax32": fmax32,
		"fmin3": fmin3,
		"f64toi64": f64toi64, "f64toi32": f64toi32, "f64toi16": f64toi16, "f64toi8": f64toi8,
		"f64tou64": f64tou64, "f64tou32": f64tou32, "f64tou16": f64tou16, "f64tou8": f64tou8,
		"f32toi64": f32toi64, "f32toi32": f32toi32, "f32tou64": f32tou64, "f32tou32": f32tou32,
		"i64tof64": i64tof64, "i32tof64": i32tof64, "i16tof64": i16tof64, "i8tof32": i8tof32,
		"u64tof64": u64tof64, "u32tof64": u32tof64, "u8tof64": u8tof64, "i64tof32": i64tof32,
		"u64tof32": u64tof32, "i32tof32": i32tof32, "u32tof32": u32tof32,
		"f64tof32": f64tof32, "f32tof64": f32tof64, "fexplicit": fexplicit,
		"fbits": fbits, "ffrombits": ffrombits, "fbits32": fbits32, "ffrombits32": ffrombits32,
		"fisnan": fisnan, "fisinf": fisinf, "fconsts": fconsts, "fconstfold": fconstfold,
		"fsum": fsum, "fdot": fdot, "fnewton": fnewton, "fpoint": fpoint, "fscale": fscale,
		"fmaxslice": fmaxslice, "fselect": fselect, "fclamp": fclamp, "fhalves": fhalves,
		"fcount": fcount,
		"cadd": cadd, "csub64": csub64, "cparts": cparts, "cmake": cmake, "cneg": cneg,
		"ceq": ceq, "cwiden": cwiden, "cconj": cconj,
	} {
		funcs[k] = v
	}
}

func fadd64(x, y float64) float64 { return x + y }
func fsub64(x, y float64) float64 { return x - y }
func fmul64(x, y float64) float64 { return x * y }
func fdiv64(x, y float64) float64 { return x / y }
func fneg64(x float64) float64    { return -x }
func fadd32(x, y float32) float32 { return x + y }
func fsub32(x, y float32) float32 { return x - y }
func fmul32(x, y float32) float32 { return x * y }
func fdiv32(x, y float32) float32 { return x / y }
func fneg32(x float32) float32    { return -x }

func fcmp64(x, y float64) (bool, bool, bool, bool, bool, bool) {
	return x == y, x != y, x < y, x <= y, x > y, x >= y
}

func fcmp32(x, y float32) (bool, bool, bool, bool, bool, bool) {
	return x == y, x != y, x < y, x <= y, x > y, x >= y
}

func fsign(x float64) int {
	if x < 0 {
		return -1
	}
	if x > 0 {
		return 1
	}
	if x == 0 {
		return 0
	}
	return 2
}

func fsqrt(x float64) float64     { return math.Sqrt(x) }
func fsqrt32(x float32) float32   { return float32(math.Sqrt(float64(x))) }
func ffloor(x float64) float64    { return math.Floor(x) }
func fceil(x float64) float64     { return math.Ceil(x) }
func ftrunc(x float64) float64    { return math.Trunc(x) }
func fround(x float64) float64    { return math.Round(x) }
func froundeven(x float64) float64 { return math.RoundToEven(x) }
func fabs(x float64) float64      { return math.Abs(x) }
func fcopysign(x, y float64) float64 { return math.Copysign(x, y) }
func ffma(x, y, z float64) float64 { return math.FMA(x, y, z) }
func fmin64(x, y float64) float64 { return min(x, y) }
func fmax64(x, y float64) float64 { return max(x, y) }
func fmin32(x, y float32) float32 { return min(x, y) }
func fmax32(x, y float32) float32 { return max(x, y) }
func fmin3(x, y, z float64) float64 { return min(x, y, z) }

func f64toi64(x float64) int64   { return int64(x) }
func f64toi32(x float64) int32   { return int32(x) }
func f64toi16(x float64) int16   { return int16(x) }
func f64toi8(x float64) int8     { return int8(x) }
func f64tou64(x float64) uint64  { return uint64(x) }
func f64tou32(x float64) uint32  { return uint32(x) }
func f64tou16(x float64) uint16  { return uint16(x) }
func f64tou8(x float64) uint8    { return uint8(x) }
func f32toi64(x float32) int64   { return int64(x) }
func f32toi32(x float32) int32   { return int32(x) }
func f32tou64(x float32) uint64  { return uint64(x) }
func f32tou32(x float32) uint32  { return uint32(x) }
func i64tof64(x int64) float64   { return float64(x) }
func i32tof64(x int32) float64   { return float64(x) }
func i16tof64(x int16) float64   { return float64(x) }
func i8tof32(x int8) float32     { return float32(x) }
func u64tof64(x uint64) float64  { return float64(x) }
func u32tof64(x uint32) float64  { return float64(x) }
func u8tof64(x uint8) float64    { return float64(x) }
func i64tof32(x int64) float32   { return float32(x) }
func u64tof32(x uint64) float32  { return float32(x) }
func i32tof32(x int32) float32   { return float32(x) }
func u32tof32(x uint32) float32  { return float32(x) }
func f64tof32(x float64) float32 { return float32(x) }
func f32tof64(x float32) float64 { return float64(x) }

// fexplicit: explicit conversions round (Round64F/Round32F) and keep the products unfused.
func fexplicit(x, y float64, a, b float32) (float64, float32) {
	return float64(x*y) + 1, float32(a*b) - b
}

func fbits(x float64) uint64      { return math.Float64bits(x) }
func ffrombits(b uint64) float64  { return math.Float64frombits(b) }
func fbits32(x float32) uint32    { return math.Float32bits(x) }
func ffrombits32(b uint32) float32 { return math.Float32frombits(b) }
func fisnan(x float64) (bool, bool) { return x != x, math.IsNaN(x) }
func fisinf(x float64) (bool, bool, bool) {
	return math.IsInf(x, 0), math.IsInf(x, 1), math.IsInf(x, -1)
}

func fconsts() (float64, float32, float64, float32, float64) {
	return math.Pi, float32(math.E), -0.0 * 1, math.MaxFloat32, math.SmallestNonzeroFloat64
}

func fconstfold(x float64) (float64, float64, float64) {
	// not x * -1: generic.rules:1325 rewrites it to -x, which differs on NaNs (docs/plans/semantics.md §10)
	return float64(x*2) + 0.5, x / 4, x * -2
}

func fsum(xs []float64) float64 {
	s := 0.0
	for _, x := range xs {
		s += x
	}
	return s
}

func fdot(xs []float64, ys []float32) float64 {
	s := 0.0
	for i := range min(len(xs), len(ys)) {
		s += float64(xs[i] * float64(ys[i]))
	}
	return s
}

func fnewton(x float64) float64 {
	if !(x > 0) || x > 1e300 {
		return -1
	}
	z := 1.0
	for range 30 {
		z -= float64(float64(z*z)-x) / float64(2*z)
	}
	return z
}

type point struct {
	X, Y float64
	W    float32
}

func fpoint(p point, k float64) point {
	return point{float64(p.X * k), float64(p.Y * k), p.W + float32(k)}
}

func fscale(p *float64, xs []float32, k float32) {
	if p != nil {
		*p = *p / float64(k)
	}
	for i := range xs {
		xs[i] *= k
	}
}

func fmaxslice(xs []float64) (float64, int) {
	best, at := math.Inf(-1), -1
	for i, x := range xs {
		if x > best {
			best, at = x, i
		}
	}
	return best, at
}

func fselect(x, y float64, c bool) float64 {
	r := y
	if c {
		r = x
	}
	return r
}

func fclamp(x, lo, hi float32) float32 {
	if x < lo {
		return lo
	}
	if x > hi {
		return hi
	}
	return x
}

func fhalves(x float64) [4]float64 {
	var a [4]float64
	for i := range a {
		a[i] = x
		x /= 2
	}
	return a
}

func fcount(xs []float32) (int, int, int) {
	neg, nan, big := 0, 0, 0
	for _, x := range xs {
		switch {
		case x != x:
			nan++
		case x < 0:
			neg++
		case x >= 1<<20:
			big++
		}
	}
	return neg, nan, big
}

func cadd(a, b complex128) complex128 { return a + b }
func csub64(a, b complex64) complex64  { return a - b }
func cparts(a complex64) (float32, float32) { return real(a), imag(a) }
func cmake(x, y float64) complex128   { return complex(x, y) }
func cneg(a complex128) complex128    { return -a }
func ceq(a, b complex128) bool        { return a == b }
func cwiden(a complex64) complex128   { return complex128(a) }
func cconj(a complex128) complex128   { return complex(real(a), -imag(a)) }
