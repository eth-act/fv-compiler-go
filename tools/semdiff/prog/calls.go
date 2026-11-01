package main

// Functions of the P3 difftest: calls between program functions (static, closures, method
// values, interface methods, recursion) and the runtime calls the compiler emits for new,
// make, append, copy, string conversion and concatenation, and boxing.

type shape interface {
	area() int
	scale(k int) shape
}

type rect struct{ w, h int }

type square struct{ s int }

//go:noinline
func (r rect) area() int { return r.w * r.h }

//go:noinline
func (r rect) scale(k int) shape { return rect{r.w * k, r.h * k} }

//go:noinline
func (q *square) area() int { return q.s * q.s }

//go:noinline
func (q *square) scale(k int) shape { return &square{q.s * k} }

type counter struct{ n int }

//go:noinline
func (c *counter) add(d int) int {
	c.n += d
	return c.n
}

func init() {
	for k, v := range map[string]any{
		"callAdd": callAdd, "callDiv": callDiv, "fib": fib, "callMulti": callMulti,
		"callStruct": callStruct, "callArr": callArr, "callBig": callBig,
		"closureAdd": closureAdd, "closureCount": closureCount, "applyTwice": applyTwice,
		"methodValue": methodValue, "methodPtr": methodPtr, "ifaceArea": ifaceArea,
		"ifaceScale": ifaceScale, "newInt": newInt, "newStruct": newStruct,
		"makeSum": makeSum, "makeBad": makeBad, "appendN": appendN, "appendCap": appendCap,
		"appendStr": appendStr, "copyN": copyN, "concat2": concat2, "concat4": concat4,
		"bytesToStr": bytesToStr, "strToBytes": strToBytes, "strCmp": strCmp,
		"boxInt": boxInt, "boxStr": boxStr, "manyArgs": manyArgs, "deepRec": deepRec,
		"strSlices": strSlices,
	} {
		funcs[k] = v
	}
}

//go:noinline
func add3(a, b, c int) int { return a + b*2 + c*3 }

//go:noinline
func callAdd(x, y int) int { return add3(x, y, x^y) + add3(y, x, 1) }

//go:noinline
func div(a, b int) int { return a / b }

//go:noinline
func callDiv(a, b int) int { return div(a, b) + 1 }

//go:noinline
func fib(n uint8) int {
	n %= 20
	if n < 2 {
		return int(n)
	}
	return fib(n-1) + fib(n-2)
}

//go:noinline
func divmod(a, b uint32) (uint32, uint32, bool) {
	if b == 0 {
		return 0, 0, false
	}
	return a / b, a % b, true
}

//go:noinline
func callMulti(a, b uint32) (uint32, bool) {
	q, r, ok := divmod(a, b)
	return q*b + r, ok
}

//go:noinline
func swapPair(p pair) pair { return pair{p.Y, p.X} }

//go:noinline
func callStruct(x, y int) int {
	p := swapPair(pair{x, y})
	return p.X - p.Y
}

//go:noinline
func sumArr(a [5]int) int { return a[0] + a[1] + a[2] + a[3] + a[4] }

//go:noinline
func callArr(x int) int { return sumArr([5]int{x, x + 1, x + 2, x * 3, -x}) }

//go:noinline
func bigRet(n int) big {
	var b big
	b.N = n
	for i := range b.Arr {
		b.Arr[i] = n * i
	}
	b.Tag = "big"
	return b
}

//go:noinline
func callBig(n int) int {
	b := bigRet(n)
	return bigSum(b)
}

//go:noinline
func adder(k int) func(int) int { return func(x int) int { return x + k } }

//go:noinline
func closureAdd(k, x int) int { return adder(k)(x) }

//go:noinline
func closureCount(n uint8) int {
	c := 0
	inc := func(d int) { c += d }
	for i := range int(n) {
		inc(i)
	}
	return c
}

//go:noinline
func twice(f func(int) int, x int) int { return f(f(x)) }

//go:noinline
func applyTwice(k, x int) int { return twice(adder(k), x) + twice(func(y int) int { return y * 2 }, x) }

//go:noinline
func methodValue(n, d int) int {
	c := &counter{n}
	f := c.add
	f(d)
	return f(d)
}

//go:noinline
func methodPtr(n, d int) int {
	c := counter{n}
	c.add(d)
	return c.n
}

//go:noinline
func ifaceArea(w, h int, sq bool) int {
	var s shape = rect{w, h}
	if sq {
		s = &square{w}
	}
	return s.area()
}

//go:noinline
func ifaceScale(w, h, k int) int {
	var s shape = rect{w, h}
	return s.scale(k).area() + (&square{w}).scale(k).area()
}

//go:noinline
func newInt(x int) int {
	p := new(int)
	*p = x
	q := p
	*q += 1
	return *p
}

//go:noinline
func newStruct(x int, s string) (int, string) {
	r := &rec{A: int32(x), S: s}
	r.P.X = x * 2
	return r.P.X + int(r.A), r.S
}

//go:noinline
func makeSum(n uint8) int {
	s := make([]int, n, n+3)
	for i := range s {
		s[i] = i * i
	}
	t := 0
	for _, x := range s {
		t += x
	}
	return t + cap(s)
}

//go:noinline
func makeBad(n, c int) int {
	s := make([]byte, n, c)
	return len(s) + cap(s)
}

//go:noinline
func appendN(n uint8) (int, int, int) {
	var s []int
	for i := range int(n) {
		s = append(s, i)
	}
	t := 0
	for _, x := range s {
		t += x
	}
	return len(s), cap(s), t
}

//go:noinline
func appendCap(s []int, x int) ([]int, int) {
	s = append(s, x, x+1)
	return s, cap(s)
}

//go:noinline
func appendStr(ss []string, s string) []string { return append(ss, s, s+s) }

//go:noinline
func copyN(dst, src []int) (int, []int) {
	n := copy(dst, src)
	return n, dst
}

//go:noinline
func concat2(a, b string) string { return a + b }

//go:noinline
func concat4(a, b, c, d string) (string, int) {
	s := a + "-" + b + c + d
	return s, len(s)
}

//go:noinline
func bytesToStr(b []byte) string { return string(b) }

//go:noinline
func strToBytes(s string) ([]byte, int) {
	b := []byte(s)
	if len(b) > 0 {
		b[0] = 'X'
	}
	return b, cap(b)
}

//go:noinline
func strCmp(a, b string) (bool, bool) { return a == b, a+"x" == b+"x" }

//go:noinline
func boxInt(x int) int {
	var e any = x
	if v, ok := e.(int); ok {
		return v + 1
	}
	return 0
}

//go:noinline
func boxStr(s string) int {
	var e any = s
	return len(e.(string))
}

//go:noinline
func many(a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r int) int {
	return a + b*2 + c*3 + d*4 + e*5 + f*6 + g*7 + h*8 + i*9 + j*10 + k*11 + l*12 + m*13 +
		n*14 + o*15 + p*16 + q*17 + r*18
}

//go:noinline
func manyArgs(x int) int { return many(x, x+1, x+2, x+3, x+4, x+5, x+6, x+7, x+8, x+9, x, x, x, x, x, x, x, -x) }

//go:noinline
func deepRec(n uint8, acc int) int {
	if n == 0 {
		return acc
	}
	return deepRec(n-1, acc*3+int(n)) + 1
}

//go:noinline
func strSlices(s string, i int) (string, string) {
	if i < 0 || i > len(s) {
		i = len(s)
	}
	return split2(s, i)
}
