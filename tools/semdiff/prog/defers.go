package main

// Functions of the P5 defer/recover difftest: open-coded defers (deferBits and slots), defers
// in loops (runtime.deferproc, deferreturn), more than 8 defers (runtime.deferprocStack),
// deferred calls with arguments (deferwrap wrappers), named results changed by deferred calls,
// recover of runtime errors and of panic values, re-panics in deferred calls, recover outside
// a deferred call (nil), nil deferred functions, and runtime errors that propagate after the
// deferred calls ran.

func init() {
	for k, v := range map[string]any{
		"deferOrder": deferOrder, "deferLoop": deferLoop, "deferMany": deferMany,
		"deferArgs": deferArgs, "recoverDiv": recoverDiv, "recoverValue": recoverValue,
		"recoverString": recoverString, "repanic": repanic, "recoverNoPanic": recoverNoPanic,
		"recoverHelper": recoverHelper, "deferNilFunc": deferNilFunc,
		"deferPropagate": deferPropagate, "recoverLoop": recoverLoop,
		"recoverCallee": recoverCallee, "deferResultOrder": deferResultOrder,
		"recoverIndex": recoverIndex, "recoverTwice": recoverTwice,
	} {
		funcs[k] = v
	}
}

func deferOrder(n int) (r int) {
	defer func() { r = r*10 + 1 }()
	if n > 0 {
		defer func() { r = r*10 + 2 }()
	}
	defer func() { r = r*10 + 3 }()
	return n % 7
}

func deferLoop(n uint8) (r int) {
	for i := range int(n % 6) {
		defer func(i int) { r = r*10 + i }(i)
	}
	return 1
}

func deferMany(x int) (r int) {
	defer func() { r += 1 }()
	defer func() { r += 2 }()
	defer func() { r += 4 }()
	defer func() { r += 8 }()
	defer func() { r += 16 }()
	defer func() { r += 32 }()
	defer func() { r += 64 }()
	defer func() { r += 128 }()
	defer func() { r *= 3 }()
	if x < 0 {
		return -x
	}
	return x % 1000
}

//go:noinline
func addTo(p *int, d int) { *p += d }

func deferArgs(x int) (r int) {
	defer addTo(&r, x)
	x *= 2
	defer addTo(&r, x)
	return 5
}

func recoverDiv(a, b int) (q int, ok bool) {
	defer func() {
		if recover() != nil {
			q, ok = -1, false
		}
	}()
	return a / b, true
}

func recoverValue(x int) (r int) {
	defer func() {
		if v := recover(); v != nil {
			r = v.(int) * 2
		}
	}()
	if x > 0 {
		panic(x)
	}
	return -x
}

func recoverString(s string) (r string) {
	defer func() {
		if v := recover(); v != nil {
			r = "recovered " + v.(string)
		}
	}()
	if len(s) > 2 {
		panic(s)
	}
	return s
}

func repanic(x int) (r int) {
	defer func() {
		if v := recover(); v != nil {
			r = v.(int)
		}
	}()
	defer func() {
		panic(x + 1)
	}()
	panic(x)
}

func recoverNoPanic(x int) bool {
	return recover() == nil && x == x
}

//go:noinline
func catch(r *int) {
	if recover() != nil {
		*r = 99
	}
}

func recoverHelper(a, b int) (r int) {
	defer catch(&r)
	return a % b
}

func deferNilFunc(x int) (r int) {
	defer func() {
		if recover() != nil {
			r = 5
		}
	}()
	var f func()
	if x > 0 {
		f = func() { r = 6 }
	}
	defer f()
	return 1
}

func deferPropagate(a, b int) (r int) {
	defer func() { r = 3 }()
	return a / b
}

func recoverLoop(n uint8, b int) (r int) {
	for i := range int(n % 4) {
		defer func(i int) {
			if recover() != nil {
				r += 100 * (i + 1)
			}
		}(i)
	}
	return 10 / b
}

//go:noinline
func mayPanic(x int) int {
	if x%3 == 0 {
		panic(x)
	}
	return x
}

func recoverCallee(x int) (r int) {
	defer func() {
		if v := recover(); v != nil {
			r = -v.(int)
		}
	}()
	return mayPanic(x) + 1
}

func deferResultOrder(x int) (a, b int) {
	defer func() { a, b = b, a }()
	defer func() { a += x }()
	return 1, 2
}

func recoverIndex(s []int, i int) (v int, ok bool) {
	defer func() {
		if recover() != nil {
			v, ok = -1, false
		}
	}()
	return s[i], true
}

func recoverTwice(x int) (r int) {
	defer func() {
		r = 0
		if recover() != nil {
			r++
		}
		if recover() != nil {
			r += 10
		}
	}()
	if x != 0 {
		panic(x)
	}
	return 7
}
