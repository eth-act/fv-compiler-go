// Maps and channels: runtime calls with pointer arguments, write barriers, select.
package main

import "os"

//go:noinline
func histogram(s string) map[rune]int {
	m := map[rune]int{}
	for _, r := range s {
		m[r]++
	}
	return m
}

//go:noinline
func pipeline(n int) int {
	ch := make(chan int, n)
	for i := range n {
		ch <- i
	}
	close(ch)
	s := 0
	for v := range ch {
		s += v
	}
	return s
}

func main() {
	if histogram("abca")['a'] != 2 || pipeline(4) != 6 {
		os.Exit(1)
	}
}
