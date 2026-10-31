// Interfaces: dynamic calls, type switches, type assertions, devirtualisation,
// interface comparisons (opt rules on itabs, read-only data folding).
package main

import (
	"fmt"
	"os"
)

type shape interface{ area() float64 }
type sq struct{ s float64 }
type circ struct{ r float64 }

func (q sq) area() float64    { return q.s * q.s }
func (c *circ) area() float64 { return 3 * c.r * c.r }

//go:noinline
func total(xs []shape) (t float64) {
	for _, x := range xs {
		switch v := x.(type) {
		case sq:
			t += v.s * v.s
		default:
			t += x.area()
		}
	}
	return
}

//go:noinline
func same(a, b any) bool { return a == b }

func main() {
	var s shape = sq{2}
	t := total([]shape{s, &circ{1}})
	if !same(1, 1) || t != 7 {
		fmt.Println(t)
		os.Exit(1)
	}
}
