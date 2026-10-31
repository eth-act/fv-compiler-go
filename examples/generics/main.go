// Generics: shape-instantiated functions with dictionaries (dictionary loads folded
// by isFixedLoad), constraints, generic types.
package main

import (
	"cmp"
	"os"
)

type num interface{ ~int | ~int64 | ~float64 }

//go:noinline
func sumOf[T num](xs []T) (s T) {
	for _, x := range xs {
		s += x
	}
	return
}

type pair[K comparable, V any] struct {
	k K
	v V
}

//go:noinline
func maxBy[T any, K cmp.Ordered](xs []T, key func(T) K) (best T) {
	for i, x := range xs {
		if i == 0 || key(x) > key(best) {
			best = x
		}
	}
	return
}

func main() {
	ps := []pair[string, int]{{"a", 1}, {"b", 3}, {"c", 2}}
	b := maxBy(ps, func(p pair[string, int]) int { return p.v })
	if sumOf([]int{1, 2}) != 3 || sumOf([]float64{0.5, 0.25}) != 0.75 || b.k != "b" {
		os.Exit(1)
	}
}
