// Command ssastats summarises gofv-ssa export files (docs/contracts/export.md): number of
// functions, values, and per pass how many functions the pass changed.
//
// usage: ssastats [-json] <dir>...
//
// Every *.ssa file under the given directories is read. A pass "changed" a function when the
// section after it differs from the section before it, ignoring the pass header, the
// definition lines (a new or redefined definition implies a changed body line anyway, except
// for redefinitions of mutated aux objects, which count as a change too) and warn lines.
package main

import (
	"bufio"
	"encoding/json"
	"flag"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"strings"
)

type passStat struct {
	Name    string `json:"name"`
	Ran     int    `json:"ran"`
	Changed int    `json:"changed"`
	Values  int    `json:"values"` // values after the pass, summed over functions
	Blocks  int    `json:"blocks"`
}

type stats struct {
	Files       int         `json:"files"`
	Sections    int         `json:"sections"`
	Bytes       int64       `json:"bytes"`
	ValuesStart int         `json:"values_start"`
	BlocksStart int         `json:"blocks_start"`
	Warns       int         `json:"warns"`
	UnknownAux  int         `json:"unknown_aux"`
	Passes      []*passStat `json:"passes"`
	byName      map[string]*passStat
}

func main() {
	asJSON := flag.Bool("json", false, "print JSON instead of a table")
	flag.Parse()
	if flag.NArg() == 0 {
		fmt.Fprintln(os.Stderr, "usage: ssastats [-json] <dir>...")
		os.Exit(2)
	}
	st := &stats{byName: map[string]*passStat{}}
	for _, dir := range flag.Args() {
		err := filepath.WalkDir(dir, func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() || !strings.HasSuffix(path, ".ssa") {
				return nil
			}
			return st.file(path)
		})
		if err != nil {
			fmt.Fprintln(os.Stderr, "ssastats:", err)
			os.Exit(1)
		}
	}
	if *asJSON {
		enc := json.NewEncoder(os.Stdout)
		enc.SetIndent("", "  ")
		enc.Encode(st)
		return
	}
	st.print()
}

// section is the comparable content of one section.
type section struct {
	name   string
	body   []string
	defs   int
	values int
	blocks int
}

func (st *stats) file(path string) error {
	f, err := os.Open(path)
	if err != nil {
		return err
	}
	defer f.Close()
	if fi, err := f.Stat(); err == nil {
		st.Bytes += fi.Size()
	}
	sc := bufio.NewScanner(f)
	sc.Buffer(make([]byte, 1<<20), 1<<30)
	var secs []*section
	var cur *section
	for sc.Scan() {
		line := sc.Text()
		tag, _, _ := strings.Cut(line, " ")
		switch tag {
		case "pass":
			_, rest, _ := strings.Cut(line, " ")
			_, name, _ := strings.Cut(rest, " ")
			cur = &section{name: strings.Trim(name, `"`)}
			secs = append(secs, cur)
		case "end":
			cur = nil
		case "warn":
			st.Warns++
		case "aux":
			if f := strings.SplitN(line, " ", 4); len(f) > 2 && f[2] == "unknown" {
				st.UnknownAux++
			}
			if cur != nil {
				cur.defs++
			}
		case "posbase", "type", "field", "abiparam", "reloc", "rtype", "slot":
			if cur != nil {
				cur.defs++
			}
		default:
			if cur != nil {
				cur.body = append(cur.body, line)
				switch tag {
				case "v":
					cur.values++
				case "b":
					cur.blocks++
				}
			}
		}
	}
	if err := sc.Err(); err != nil {
		return fmt.Errorf("%s: %v", path, err)
	}
	if len(secs) == 0 {
		return fmt.Errorf("%s: no sections", path)
	}
	st.Files++
	st.Sections += len(secs)
	st.ValuesStart += secs[0].values
	st.BlocksStart += secs[0].blocks
	for i := 1; i < len(secs); i++ {
		s := secs[i]
		ps := st.byName[s.name]
		if ps == nil {
			ps = &passStat{Name: s.name}
			st.byName[s.name] = ps
			st.Passes = append(st.Passes, ps)
		}
		ps.Ran++
		ps.Values += s.values
		ps.Blocks += s.blocks
		if s.defs > 0 || !equal(s.body, secs[i-1].body) {
			ps.Changed++
		}
	}
	return nil
}

func equal(a, b []string) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func (st *stats) print() {
	fmt.Printf("functions %d, sections %d, bytes %d\n", st.Files, st.Sections, st.Bytes)
	fmt.Printf("input (start): values %d, blocks %d\n", st.ValuesStart, st.BlocksStart)
	fmt.Printf("warn lines %d, unknown aux %d\n\n", st.Warns, st.UnknownAux)
	// Passes in order of first appearance, i.e. pipeline order.
	ps := st.Passes
	fmt.Printf("| %-28s | %9s | %9s | %7s | %10s |\n", "pass", "ran", "changed", "%", "values")
	fmt.Printf("|%s|%s|%s|%s|%s|\n", strings.Repeat("-", 30), strings.Repeat("-", 11), strings.Repeat("-", 11), strings.Repeat("-", 9), strings.Repeat("-", 12))
	for _, p := range ps {
		pct := 0.0
		if p.Ran > 0 {
			pct = 100 * float64(p.Changed) / float64(p.Ran)
		}
		fmt.Printf("| %-28s | %9d | %9d | %6.1f%% | %10d |\n", p.Name, p.Ran, p.Changed, pct, p.Values)
	}
}
