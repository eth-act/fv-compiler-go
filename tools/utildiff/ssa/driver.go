// Package ssa holds verbatim copies of cmd/compile/internal/ssa's sparseset.go, sparsemap.go
// and sparsemappos.go (copied in by scripts/util-difftest.sh) plus this driver, which runs
// random operation sequences on them and records the observable results as a trace. The
// Lean side (GoFVTest/UtilDiff.lean) replays the operations on GoFV.Util.SparseSet,
// SparseMap and SparseMapPos and must print the same trace.
//
// Trace syntax: one token per observable result, separated by spaces.
package ssa

import (
	"fmt"
	"math/rand/v2"
	"strings"

	"gofv/tools/utildiff/src"
)

// ID and Value stand in for the compiler's types (id.go, value.go) used by sparseset.go.
type ID int32

type Value struct{ ID ID }

// key draws a key in [0, n): mostly from a small pool so that keys repeat.
func key(r *rand.Rand, n int, pool []ID) ID {
	if len(pool) > 0 && r.IntN(3) > 0 {
		return pool[r.IntN(len(pool))]
	}
	return ID(r.IntN(n))
}

func keyPool(r *rand.Rand, n int) []ID {
	m := 1 + r.IntN(8)
	pool := make([]ID, m)
	for i := range pool {
		pool[i] = ID(r.IntN(n))
	}
	return pool
}

// GenSet returns a random op sequence for a sparseSet of capacity n and its trace.
// Ops: aK add, AK1,K2,.. addAll, rK remove, p pop, c clear, qK contains, s size, l contents.
func GenSet(r *rand.Rand, n, nops int) (ops []string, trace string) {
	s := newSparseSet(n)
	var out []string
	pool := keyPool(r, max(n, 1))
	for range nops {
		k := r.IntN(100)
		switch {
		case n == 0:
			// No key is valid: only key-free ops.
			switch k % 3 {
			case 0:
				ops = append(ops, "c")
				s.clear()
			case 1:
				ops = append(ops, "s")
				out = append(out, fmt.Sprint(s.size()))
			default:
				ops = append(ops, "l")
				out = append(out, setContents(s))
			}
		case k < 35:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("a%d", x))
			s.add(x)
		case k < 40:
			m := r.IntN(6)
			xs := make([]ID, m)
			strs := make([]string, m)
			for i := range xs {
				xs[i] = key(r, n, pool)
				strs[i] = fmt.Sprint(xs[i])
			}
			ops = append(ops, "A"+strings.Join(strs, ","))
			if r.IntN(2) == 0 {
				s.addAll(xs)
			} else {
				vs := make([]*Value, m)
				for i, x := range xs {
					vs[i] = &Value{ID: x}
				}
				s.addAllValues(vs)
			}
		case k < 60:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("r%d", x))
			s.remove(x)
		case k < 70:
			if s.size() == 0 {
				ops = append(ops, "s")
				out = append(out, fmt.Sprint(s.size()))
				continue
			}
			ops = append(ops, "p")
			out = append(out, fmt.Sprint(s.pop()))
		case k < 72:
			ops = append(ops, "c")
			s.clear()
		case k < 88:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("q%d", x))
			out = append(out, b01(s.contains(x)))
		case k < 92:
			ops = append(ops, "s")
			out = append(out, fmt.Sprint(s.size()))
		default:
			ops = append(ops, "l")
			out = append(out, setContents(s))
		}
	}
	ops = append(ops, "l")
	out = append(out, setContents(s))
	return ops, strings.Join(out, " ")
}

func b01(b bool) string {
	if b {
		return "1"
	}
	return "0"
}

func setContents(s *sparseSet) string {
	var b strings.Builder
	b.WriteByte('[')
	for i, x := range s.contents() {
		if i > 0 {
			b.WriteByte(',')
		}
		fmt.Fprint(&b, x)
	}
	b.WriteByte(']')
	return b.String()
}

func val(r *rand.Rand) int32 {
	switch r.IntN(4) {
	case 0:
		return int32(r.IntN(5)) - 2
	case 1:
		return int32(r.Uint32())
	default:
		return int32(r.IntN(1000))
	}
}

// GenMap returns a random op sequence for a sparseMap of capacity n and its trace.
// Ops: sK:V set, gK get (V, or - if absent), rK remove, c clear, qK contains, z size,
// l contents ([K:V,...]).
func GenMap(r *rand.Rand, n, nops int) (ops []string, trace string) {
	s := newSparseMap(n)
	var out []string
	pool := keyPool(r, max(n, 1))
	for range nops {
		k := r.IntN(100)
		if n == 0 {
			k = 90 + k%10
		}
		switch {
		case k < 35:
			x, v := key(r, n, pool), val(r)
			ops = append(ops, fmt.Sprintf("s%d:%d", x, v))
			s.set(x, v)
		case k < 55:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("g%d", x))
			if v, ok := s.get(x); ok {
				out = append(out, fmt.Sprint(v))
			} else {
				out = append(out, "-")
			}
		case k < 75:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("r%d", x))
			s.remove(x)
		case k < 77:
			ops = append(ops, "c")
			s.clear()
		case k < 90:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("q%d", x))
			out = append(out, b01(s.contains(x)))
		case k < 95:
			ops = append(ops, "z")
			out = append(out, fmt.Sprint(s.size()))
		default:
			ops = append(ops, "l")
			out = append(out, mapContents(s))
		}
	}
	ops = append(ops, "l")
	out = append(out, mapContents(s))
	return ops, strings.Join(out, " ")
}

func mapContents(s *sparseMap) string {
	var b strings.Builder
	b.WriteByte('[')
	for i, e := range s.contents() {
		if i > 0 {
			b.WriteByte(',')
		}
		fmt.Fprintf(&b, "%d:%d", e.key, e.val)
	}
	b.WriteByte(']')
	return b.String()
}

// GenMapPos returns a random op sequence for a sparseMapPos of capacity n and its trace.
// Ops: sK:V:I:L set (position index I, lico L), gK get (-1 if absent), rK remove, c clear,
// qK contains, z size, l contents ([K:V:I:L,...]).
func GenMapPos(r *rand.Rand, n, nops int) (ops []string, trace string) {
	s := newSparseMapPos(n)
	var out []string
	pool := keyPool(r, max(n, 1))
	for range nops {
		k := r.IntN(100)
		if n == 0 {
			k = 90 + k%10
		}
		switch {
		case k < 35:
			x, v := key(r, n, pool), val(r)
			p := src.XPos{Index: int32(r.IntN(4)), Lico: r.Uint32()}
			ops = append(ops, fmt.Sprintf("s%d:%d:%d:%d", x, v, p.Index, p.Lico))
			s.set(x, v, p)
		case k < 55:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("g%d", x))
			out = append(out, fmt.Sprint(s.get(x)))
		case k < 75:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("r%d", x))
			s.remove(x)
		case k < 77:
			ops = append(ops, "c")
			s.clear()
		case k < 90:
			x := key(r, n, pool)
			ops = append(ops, fmt.Sprintf("q%d", x))
			out = append(out, b01(s.contains(x)))
		case k < 95:
			ops = append(ops, "z")
			out = append(out, fmt.Sprint(s.size()))
		default:
			ops = append(ops, "l")
			out = append(out, mapPosContents(s))
		}
	}
	ops = append(ops, "l")
	out = append(out, mapPosContents(s))
	return ops, strings.Join(out, " ")
}

func mapPosContents(s *sparseMapPos) string {
	var b strings.Builder
	b.WriteByte('[')
	for i, e := range s.contents() {
		if i > 0 {
			b.WriteByte(',')
		}
		fmt.Fprintf(&b, "%d:%d:%d:%d", e.key, e.val, e.pos.Index, e.pos.Lico)
	}
	b.WriteByte(']')
	return b.String()
}
