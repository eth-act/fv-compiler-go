// Slices and strings: append, copy, conversions, string concatenation and comparison,
// bounds-check elimination, memmove/memclr inlining.
package main

import "os"

//go:noinline
func reverse(s string) string {
	b := []byte(s)
	for i, j := 0, len(b)-1; i < j; i, j = i+1, j-1 {
		b[i], b[j] = b[j], b[i]
	}
	return string(b)
}

//go:noinline
func clear16(b []byte) {
	if len(b) >= 16 {
		for i := range b[:16] {
			b[i] = 0
		}
	}
}

//go:noinline
func join(a, b string) string { return a + "/" + b }

func main() {
	b := make([]byte, 32)
	copy(b, "hello, world, hello, world")
	clear16(b)
	if reverse("abc") != "cba" || join("a", "b") != "a/b" || b[3] != 0 {
		os.Exit(1)
	}
}
