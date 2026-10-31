// sccp map-order repro (tests/sccp-order/run.sh): in f, sccp proves `x > 1` and `y > 1`
// false; rewiring their two If blocks removes two edges into the `s += 7` block, which keeps two
// predecessors, so its Preds order after sccp depends on Go map iteration order.
package main

var sink, sink2 int

//go:noinline
func f(n int, a, b []int) int {
	x, y, s := 1, 1, 0
	for i := 0; i < n; i++ {
		if a[i] > 0 || b[i] > 0 || x > 1 || y > 1 {
			s += 7
		}
		if x > 1 {
			x = 2
			sink = i
		}
		if y > 1 {
			y = 3
			sink2 = i
		}
	}
	return s
}

//go:noinline
func g(n int) int {
	x, y, s := 1, 1, 0
	for i := 0; i < n; i++ {
		if i > 5 || i < 2 || x > 1 || y > 1 {
			s++
		}
		if x > 1 {
			x = 2
			sink = i
		}
		if y > 1 {
			y = 3
			sink2 = i
		}
	}
	return s
}

func main() {
	println(f(3, []int{1, 2, 3}, []int{1, 2, 3}), g(10))
}
