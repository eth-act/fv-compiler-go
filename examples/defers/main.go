// Defer, panic and recover; open-coded defers and named results.
package main

import "os"

//go:noinline
func safeDiv(a, b int) (q int, ok bool) {
	defer func() {
		if recover() != nil {
			q, ok = 0, false
		}
	}()
	return a / b, true
}

//go:noinline
func withCleanup(n int) (r int) {
	for i := range n {
		defer func(i int) { r += i }(i)
	}
	return n
}

func main() {
	if _, ok := safeDiv(1, 0); ok || withCleanup(3) != 6 {
		os.Exit(1)
	}
}
