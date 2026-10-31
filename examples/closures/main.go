// Closures, captured variables, function values and method values (expand calls,
// writebarrier on captured pointers, nilcheckelim).
package main

import "os"

type counter struct{ n int }

func (c *counter) inc(d int) { c.n += d }

//go:noinline
func apply(f func(int) int, xs []int) []int {
	out := make([]int, 0, len(xs))
	for _, x := range xs {
		out = append(out, f(x))
	}
	return out
}

//go:noinline
func adder(k int) func(int) int {
	return func(x int) int { return x + k }
}

func main() {
	c := &counter{}
	inc := c.inc
	ys := apply(adder(3), []int{1, 2, 3})
	for _, y := range ys {
		inc(y)
	}
	if c.n != 15 {
		os.Exit(1)
	}
}
