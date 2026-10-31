// Command utildiff writes differential test cases for GoFV.Util (issue #41): inputs and Go's
// results for slices.SortFunc, sort.Sort and the compiler's sparseSet, sparseMap and
// sparseMapPos. GoFVTest/UtilDiff.lean (lake exe util-difftest) recomputes every result with
// the Lean ports and compares. Run through scripts/util-difftest.sh, which copies the
// compiler's sparse*.go into ssa/ and checks that the host Go's sort sources are the pinned
// go1.27.3 ones.
//
// Output, one case per line, space-separated:
//
//	F <cmp> <n> <key_1..key_n> <perm_1..perm_n>   slices.SortFunc
//	S <cmp> <n> <key_1..key_n> <perm_1..perm_n>   sort.Sort
//	T <cap> <nops> <op_1..op_nops> <trace...>      sparseSet
//	M <cap> <nops> <op_1..op_nops> <trace...>      sparseMap
//	P <cap> <nops> <op_1..op_nops> <trace...>      sparseMapPos
//
// Sorted elements are key<<12 | i for input position i (n <= 2000 < 4096), so ties on the
// key stay distinguishable; perm lists the input positions in output order. Comparators
// (cmpFn) include ties, few classes, raw differences and inconsistent (non-transitive,
// non-antisymmetric) ones, as the compiler's cse/storeOrder comparators can be.
// Sparse-structure ops and trace tokens: see ssa/driver.go.
//
// usage: utildiff [-n cases per kind] [-seed s] -o out.txt
package main

import (
	"bufio"
	"cmp"
	"flag"
	"fmt"
	"log"
	"math/rand/v2"
	"os"
	"slices"
	"sort"
	"strconv"

	"gofv/tools/utildiff/ssa"
)

// mix is a 64-bit hash of a pair; GoFVTest/UtilDiff.lean has the same function.
func mix(x, y int) uint64 {
	h := uint64(x)*0x9E3779B97F4A7C15 ^ uint64(y)*0xC2B2AE3D27D4EB4F
	h ^= h >> 29
	h *= 0xBF58476D1CE4E5B9
	h ^= h >> 32
	return h
}

const numCmp = 8

func cmpFn(id int) func(x, y int) int {
	switch id {
	case 0: // by key, ties between equal keys
		return func(x, y int) int { return cmp.Compare(x>>12, y>>12) }
	case 1: // total order
		return func(x, y int) int { return cmp.Compare(x, y) }
	case 2: // inconsistent, with zeros
		return func(x, y int) int { return int(mix(x, y)%3) - 1 }
	case 3: // three classes
		return func(x, y int) int { return cmp.Compare((x>>12)%3, (y>>12)%3) }
	case 4: // raw difference
		return func(x, y int) int { return x>>12 - y>>12 }
	case 5: // inconsistent, never zero
		return func(x, y int) int {
			if mix(x, y)&1 == 1 {
				return -1
			}
			return 1
		}
	case 6: // inconsistent, rarely less: unbalanced partitions, reaches heapSort
		return func(x, y int) int {
			if mix(x, y)%16 == 0 {
				return -1
			}
			return 1
		}
	default: // inconsistent, mostly less: unbalanced the other way
		return func(x, y int) int {
			if mix(x, y)%16 == 0 {
				return 1
			}
			return -1
		}
	}
}

type lessSorter struct {
	data []int
	cmp  func(x, y int) int
}

func (s lessSorter) Len() int           { return len(s.data) }
func (s lessSorter) Less(i, j int) bool { return s.cmp(s.data[i], s.data[j]) < 0 }
func (s lessSorter) Swap(i, j int)      { s.data[i], s.data[j] = s.data[j], s.data[i] }

var boundary = []int{0, 1, 2, 11, 12, 13, 14, 49, 50, 51, 52, 63, 64, 65, 100, 127, 128, 129, 2000}

func size(r *rand.Rand) int {
	switch k := r.IntN(20); {
	case k < 6:
		return r.IntN(21)
	case k < 12:
		return r.IntN(101)
	case k < 17:
		return r.IntN(601)
	case k < 18:
		return boundary[r.IntN(len(boundary))]
	default:
		return r.IntN(2001)
	}
}

func keys(r *rand.Rand, n int) []int {
	a := make([]int, n)
	swaps := func(k int) {
		for range k {
			if n > 0 {
				i, j := r.IntN(n), r.IntN(n)
				a[i], a[j] = a[j], a[i]
			}
		}
	}
	switch r.IntN(14) {
	case 0:
		for i := range a {
			a[i] = r.IntN(1 << 20)
		}
	case 1:
		for i := range a {
			a[i] = r.IntN(2)
		}
	case 2:
		for i := range a {
			a[i] = r.IntN(10)
		}
	case 3:
		for i := range a {
			a[i] = r.IntN(n + 1)
		}
	case 4:
		for i := range a {
			a[i] = i
		}
	case 5:
		for i := range a {
			a[i] = n - i
		}
	case 6:
		for i := range a {
			a[i] = 7
		}
	case 7:
		m := 1 + r.IntN(20)
		for i := range a {
			a[i] = i % m
		}
	case 8:
		for i := range a {
			a[i] = min(i, n-i)
		}
	case 9:
		for i := range a {
			a[i] = i
		}
		swaps(1 + r.IntN(5))
	case 10:
		for i := range a {
			a[i] = n - i
		}
		swaps(1 + r.IntN(5))
	case 11:
		for i := range a {
			a[i] = i / 3
		}
	case 12: // sorted, with the largest element pushed to the front
		for i := range a {
			a[i] = i - 1
		}
		if n > 0 {
			a[0] = n
		}
	default: // sorted prefix, random tail
		p := r.IntN(n + 1)
		for i := range a {
			if i < p {
				a[i] = i
			} else {
				a[i] = r.IntN(n + 1)
			}
		}
	}
	return a
}

func main() {
	out := flag.String("o", "", "output file")
	n := flag.Int("n", 12000, "cases per kind")
	seed := flag.Uint64("seed", 41, "random seed")
	flag.Parse()
	if *out == "" {
		log.Fatal("utildiff: -o is required")
	}
	f, err := os.Create(*out)
	if err != nil {
		log.Fatal(err)
	}
	w := bufio.NewWriterSize(f, 1<<20)
	r := rand.New(rand.NewPCG(*seed, 0x6f6676))

	writeSort := func(kind string, id int, ks, perm []int) {
		w.WriteString(kind)
		w.WriteString(" " + strconv.Itoa(id) + " " + strconv.Itoa(len(ks)))
		for _, k := range ks {
			w.WriteString(" " + strconv.Itoa(k))
		}
		for _, p := range perm {
			w.WriteString(" " + strconv.Itoa(p))
		}
		w.WriteByte('\n')
	}
	for _, kind := range []string{"F", "S"} {
		for c := range *n {
			id := c % numCmp
			ks := keys(r, size(r))
			data := make([]int, len(ks))
			for i, k := range ks {
				data[i] = k<<12 | i
			}
			if kind == "F" {
				slices.SortFunc(data, cmpFn(id))
			} else {
				sort.Sort(lessSorter{data, cmpFn(id)})
			}
			perm := make([]int, len(data))
			for i, x := range data {
				perm[i] = x & 0xfff
			}
			writeSort(kind, id, ks, perm)
		}
	}
	for _, g := range []struct {
		kind string
		gen  func(*rand.Rand, int, int) ([]string, string)
	}{{"T", ssa.GenSet}, {"M", ssa.GenMap}, {"P", ssa.GenMapPos}} {
		for range *n {
			capacity := r.IntN(300)
			if r.IntN(4) == 0 {
				capacity = r.IntN(5)
			}
			ops, trace := g.gen(r, capacity, r.IntN(400))
			fmt.Fprintf(w, "%s %d %d", g.kind, capacity, len(ops))
			for _, op := range ops {
				w.WriteString(" " + op)
			}
			w.WriteString(" " + trace + "\n")
		}
	}
	if err := w.Flush(); err != nil {
		log.Fatal(err)
	}
	if err := f.Close(); err != nil {
		log.Fatal(err)
	}
}
