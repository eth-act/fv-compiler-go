// Command provediff writes differential test cases for the prove pass's helpers (issue #24):
// random operation sequences on the compiler's poset (poset.go, copied into ssa/ by
// scripts/prove-difftest.sh) with Go's results and the poset's internal state after every
// operation, and random limit-arithmetic cases (prove.go's limit code, copied likewise).
// GoFVTest/ProveDiff.lean (lake exe prove-difftest) replays them on GoFV.Opt.Prove.{Poset,Limit}
// and compares. Line formats: ssa/driver.go, ssa/limits.go.
//
// usage: provediff [-n cases] [-seed s] -o out.txt
package main

import (
	"bufio"
	"flag"
	"fmt"
	"log"
	"math/rand/v2"
	"os"

	"gofv/tools/provediff/ssa"
)

func main() {
	out := flag.String("o", "", "output file")
	n := flag.Int("n", 20000, "poset cases (and 10x as many limit cases)")
	seed := flag.Uint64("seed", 24, "random seed")
	flag.Parse()
	if *out == "" {
		log.Fatal("provediff: -o required")
	}
	f, err := os.Create(*out)
	if err != nil {
		log.Fatal(err)
	}
	w := bufio.NewWriter(f)
	r := rand.New(rand.NewPCG(*seed, 0x5eed))
	for i := range *n {
		// Few values make many interactions (aliasing, collapsing paths, merges); more values
		// make wider DAGs with extra nodes.
		k := 2 + r.IntN(4)
		if i%3 == 0 {
			k = 2 + r.IntN(14)
		}
		nops := 1 + r.IntN(60)
		fmt.Fprintln(w, ssa.PosetCase(r, k, nops, i%2 == 1))
	}
	for range 10 * *n {
		fmt.Fprintln(w, ssa.LimitCase(r))
	}
	if err := w.Flush(); err != nil {
		log.Fatal(err)
	}
	if err := f.Close(); err != nil {
		log.Fatal(err)
	}
}
