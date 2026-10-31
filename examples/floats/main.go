// Floating point: conversions, comparisons with NaN, constant folding of float ops,
// math intrinsics.
package main

import (
	"math"
	"os"
)

//go:noinline
func norm(x, y float64) float64 { return math.Sqrt(x*x + y*y) }

//go:noinline
func toInt(f float32) (int32, uint64) { return int32(f), uint64(float64(f) * 2) }

//go:noinline
func isNaN(f float64) bool { return f != f }

func main() {
	a, b := toInt(2.5)
	if norm(3, 4) != 5 || a != 2 || b != 5 || isNaN(1) || !isNaN(math.NaN()) {
		os.Exit(1)
	}
}
