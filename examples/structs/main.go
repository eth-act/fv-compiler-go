// Structs and arrays passed by value, field updates, struct copies and comparisons
// (decompose user, expand calls, dse, dead auto elim, memcombine).
package main

import "os"

type point struct{ x, y int32 }
type rect struct {
	min, max point
	name     string
}

//go:noinline
func area(r rect) int64 {
	return int64(r.max.x-r.min.x) * int64(r.max.y-r.min.y)
}

//go:noinline
func grow(r *rect, d int32) rect {
	r.min.x -= d
	r.min.y -= d
	r.max = point{r.max.x + d, r.max.y + d}
	return *r
}

//go:noinline
func put(b []byte, v uint32) {
	b[0] = byte(v)
	b[1] = byte(v >> 8)
	b[2] = byte(v >> 16)
	b[3] = byte(v >> 24)
}

func main() {
	r := rect{point{0, 0}, point{2, 3}, "r"}
	g := grow(&r, 1)
	var buf [4]byte
	put(buf[:], uint32(area(g)))
	if g != r || buf[0] == 0 {
		os.Exit(1)
	}
}
