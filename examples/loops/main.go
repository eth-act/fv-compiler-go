// Loops with bounds checks, induction variables and nested control flow
// (prove, check bce, fuse, shortcircuit, branchelim, phiopt).
package main

import "os"

//go:noinline
func sum(xs []int) (s int) {
	for i := 0; i < len(xs); i++ {
		s += xs[i]
	}
	return
}

//go:noinline
func count(b []byte, c byte) int {
	n := 0
	for _, x := range b {
		if x == c || x == c+1 {
			n++
		}
	}
	return n
}

//go:noinline
func matmul(a, b, c *[4][4]float64) {
	for i := range 4 {
		for j := range 4 {
			var t float64
			for k := range 4 {
				t += a[i][k] * b[k][j]
			}
			c[i][j] = t
		}
	}
}

//go:noinline
func max3(a, b, c int) int {
	m := a
	if b > m {
		m = b
	}
	if c > m {
		m = c
	}
	return m
}

func main() {
	xs := []int{1, 2, 3, 4}
	var a, b, c [4][4]float64
	a[1][2], b[2][1] = 2, 3
	matmul(&a, &b, &c)
	r := sum(xs) + count([]byte(os.Args[0]), '/') + max3(1, 2, 3) + int(c[1][1])
	if r == 0 {
		os.Exit(1)
	}
}
