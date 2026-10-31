// Command opsgen generates GoFV/SSA/Op.lean from the generic op tables of the Go compiler
// (cmd/compile/internal/ssa/_gen/{genericOps,decOps,divisibleOps,divmodOps}.go; the SIMD
// generic ops of simdgenericOps.go are left out, see nosimd.go).
//
// Those files are package main of the _gen generator and refer to its types (opData,
// blockData, arch, ...). scripts/gen-ops.sh copies them next to this file in a scratch
// directory and runs the result, so the op tables are evaluated by Go itself (including the
// init functions that append the SIMD ops and register the archs). The types below are copies
// of _gen/main.go; checkTypes verifies against main.go that their fields still match.
//
// usage: opsgen -gen <_gen dir> -o <Op.lean> -source <description of the source tree>
package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/parser"
	"go/printer"
	"go/token"
	"log"
	"os"
	"path/filepath"
	"reflect"
	"slices"
	"sort"
	"strings"
)

// Copies of the _gen/main.go types (checked by checkTypes).

type arch struct {
	name               string
	pkg                string
	genfile            string
	genSIMDfile        string
	ops                []opData
	blocks             []blockData
	regnames           []string
	ParamIntRegNames   string
	ParamFloatRegNames string
	gpregmask          regMask
	fpregmask          regMask
	fp32regmask        regMask
	fp64regmask        regMask
	simdregmask        regMask
	specialregmask     regMask
	framepointerreg    int8
	linkreg            int8
	generic            bool
	imports            []string
}

type opData struct {
	name              string
	reg               regInfo
	asm               string
	typ               string
	aux               string
	rematerializeable bool
	argLength         int32
	commutative       bool
	resultInArg0      bool
	resultNotInArgs   bool
	clobberFlags      bool
	needIntTemp       bool
	call              bool
	tailCall          bool
	nilCheck          bool
	faultOnNilArg0    bool
	faultOnNilArg1    bool
	hasSideEffects    bool
	zeroWidth         bool
	unsafePoint       bool
	fixedReg          bool
	earlyOk           bool
	addrSinkArg0      bool
	addrSinkArg1      bool
	symEffect         string
	scale             uint8
}

type blockData struct {
	name     string
	controls int
	aux      string
}

type regInfo struct {
	inputs       []regMask
	clobbers     regMask
	clobbersArg0 bool
	clobbersArg1 bool
	outputs      []regMask
}

type regMask struct {
	v1, v2 uint64
}

var archs []arch

// checkTypes fails unless every struct above has exactly the fields (names and types) of the
// same-named struct in _gen/main.go.
func checkTypes(genDir string) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, filepath.Join(genDir, "main.go"), nil, 0)
	if err != nil {
		log.Fatal(err)
	}
	want := map[string]reflect.Type{
		"arch":      reflect.TypeOf(arch{}),
		"opData":    reflect.TypeOf(opData{}),
		"blockData": reflect.TypeOf(blockData{}),
		"regInfo":   reflect.TypeOf(regInfo{}),
		"regMask":   reflect.TypeOf(regMask{}),
	}
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.TYPE {
			continue
		}
		for _, s := range g.Specs {
			ts := s.(*ast.TypeSpec)
			rt, ok := want[ts.Name.Name]
			if !ok {
				continue
			}
			delete(want, ts.Name.Name)
			var got []string
			for _, fl := range ts.Type.(*ast.StructType).Fields.List {
				var b bytes.Buffer
				printer.Fprint(&b, fset, fl.Type)
				for _, n := range fl.Names {
					got = append(got, n.Name+" "+b.String())
				}
			}
			var have []string
			for i := range rt.NumField() {
				have = append(have, rt.Field(i).Name+" "+strings.ReplaceAll(rt.Field(i).Type.String(), "main.", ""))
			}
			if !slices.Equal(got, have) {
				log.Fatalf("type %s in _gen/main.go changed:\n  _gen: %v\n  here: %v", ts.Name.Name, got, have)
			}
		}
	}
	if len(want) != 0 {
		log.Fatalf("types not found in _gen/main.go: %v", want)
	}
}

// Lean names that are not usable as bare constructor identifiers.
var leanReserved = map[string]bool{"Type": true, "Prop": true, "Sort": true}

func ident(name string) string {
	if leanReserved[name] {
		return "«" + name + "»"
	}
	return name
}

func leanString(s string) string {
	if strings.ContainsAny(s, "\"\\\n") {
		log.Fatalf("unexpected character in string %q", s)
	}
	return `"` + s + `"`
}

// Aux type names of ssa/op.go (auxNone ... auxSizeAndAlign, without the aux prefix), the
// constructors of GoFV.SSA.AuxType.
var auxTypes = []string{"None", "Bool", "Int8", "Int16", "Int32", "Int64", "Int128", "UInt8",
	"Float32", "Float64", "FlagConstant", "CCop", "NameOffsetInt8", "String", "Sym", "SymOff",
	"SymValAndOff", "Typ", "TypSize", "Call", "CallOff", "PanicBoundsC", "PanicBoundsCC",
	"ARM64BitField", "ARM64ConditionalParams", "S390XRotateParams", "S390XCCMask",
	"S390XCCMaskInt8", "S390XCCMaskUint8", "SizeAndAlign"}

// fn emits `def <name> : Op → <ty>` as one match: arms grouped by value, the most frequent
// value as the wildcard default (ties: first in op order).
func fn(w *bytes.Buffer, doc, name, ty string, ops []opData, val func(opData) string) {
	count := map[string]int{}
	var order []string
	for _, o := range ops {
		v := val(o)
		if count[v] == 0 {
			order = append(order, v)
		}
		count[v]++
	}
	def := order[0]
	for _, v := range order {
		if count[v] > count[def] {
			def = v
		}
	}
	fmt.Fprintf(w, "/-- %s -/\n", doc)
	if len(order) == 1 {
		fmt.Fprintf(w, "def %s (_ : Op) : %s := %s\n\n", name, ty, def)
		return
	}
	fmt.Fprintf(w, "def %s : Op → %s\n", name, ty)
	for _, v := range order {
		if v == def {
			continue
		}
		for _, o := range ops {
			if val(o) == v {
				fmt.Fprintf(w, "  | .%s => %s\n", ident(o.name), v)
			}
		}
	}
	fmt.Fprintf(w, "  | _ => %s\n\n", def)
}

func main() {
	genDir := flag.String("gen", "", "_gen directory of the pinned Go tree")
	out := flag.String("o", "", "output Lean file")
	source := flag.String("source", "", "description of the Go source tree, for the header")
	flag.Parse()
	if *genDir == "" || *out == "" || *source == "" {
		flag.Usage()
		os.Exit(2)
	}
	checkTypes(*genDir)

	// As _gen/main.go: archs sorted by name, ops and blocks concatenated in that order.
	sort.SliceStable(archs, func(i, j int) bool { return archs[i].name < archs[j].name })
	ops := []opData{{name: "Invalid"}}
	blocks := []blockData{{name: "Invalid"}}
	var archNames []string
	for _, a := range archs {
		if !a.generic {
			log.Fatalf("arch %s is not generic", a.name)
		}
		archNames = append(archNames, a.name)
		for _, o := range a.ops {
			if o.name == "Invalid" {
				continue
			}
			if !reflect.DeepEqual(o.reg, regInfo{}) || o.asm != "" || o.scale != 0 {
				log.Fatalf("generic op %s has register/asm/scale data", o.name)
			}
			ops = append(ops, o)
		}
		blocks = append(blocks, a.blocks...)
	}
	seen := map[string]bool{}
	for _, o := range ops {
		if seen[o.name] {
			log.Fatalf("duplicate op %s", o.name)
		}
		seen[o.name] = true
		if o.aux != "" && !slices.Contains(auxTypes, o.aux) {
			log.Fatalf("op %s: unknown aux type %s", o.name, o.aux)
		}
		// _gen/main.go genOp: symEffect is required exactly for Sym* aux types.
		if (o.symEffect != "") != strings.HasPrefix(o.aux, "Sym") {
			log.Fatalf("op %s: symEffect %q with aux %q", o.name, o.symEffect, o.aux)
		}
	}

	w := new(bytes.Buffer)
	fmt.Fprintf(w, "-- Generated by tools/opsgen (scripts/gen-ops.sh) from %s\n", *source)
	fmt.Fprintf(w, "-- src/cmd/compile/internal/ssa/_gen, archs %s; without the SIMD generic ops\n", strings.Join(archNames, ", "))
	fmt.Fprintln(w, "-- (tools/opsgen/nosimd.go). DO NOT EDIT.")
	fmt.Fprintln(w, "import GoFV.SSA.OpInfo")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace GoFV.SSA")
	fmt.Fprintln(w)
	fmt.Fprintf(w, "/-- The %d generic SSA ops, in the order of Go's `opcodeTable` (`Op.Invalid` is `OpInvalid`). -/\n", len(ops))
	fmt.Fprintln(w, "inductive Op where")
	for _, o := range ops {
		fmt.Fprintf(w, "  | %s\n", ident(o.name))
	}
	fmt.Fprintln(w, "  deriving DecidableEq, Inhabited")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace Op")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "/-- Every op, in `opcodeTable` order. -/")
	fmt.Fprintln(w, "def all : Array Op := #[")
	for i, o := range ops {
		sep := ","
		if i == len(ops)-1 {
			sep = "]"
		}
		fmt.Fprintf(w, "  .%s%s\n", ident(o.name), sep)
	}
	fmt.Fprintln(w)
	fn(w, "`Op.String()`: the op's name (`opcodeTable[o].name`).", "name", "String", ops, func(o opData) string {
		if o.name == "Invalid" {
			return leanString("OpInvalid")
		}
		return leanString(o.name)
	})
	fn(w, "`opcodeTable[o].argLen`: number of arguments, -1 if variable.", "argLen", "Int", ops, func(o opData) string {
		if o.argLength < 0 {
			return fmt.Sprintf("(%d)", o.argLength)
		}
		return fmt.Sprint(o.argLength)
	})
	fn(w, "`opcodeTable[o].auxType`.", "auxType", "AuxType", ops, func(o opData) string {
		if o.aux == "" {
			return ".None"
		}
		return "." + o.aux
	})
	fn(w, "Default result type (`opData.typ`, as written in `_gen`; empty if none).", "typ", "String", ops, func(o opData) string {
		return leanString(o.typ)
	})
	fn(w, "`opcodeTable[o].symEffect`.", "symEffect", "SymEffect", ops, func(o opData) string {
		e := map[string]bool{}
		for _, s := range strings.Split(o.symEffect, ",") {
			switch s {
			case "", "None":
			case "Read", "Write", "Addr":
				e[s] = true
			default:
				log.Fatalf("op %s: unknown symEffect %s", o.name, s)
			}
		}
		return fmt.Sprintf("{ read := %v, write := %v, addr := %v }", e["Read"], e["Write"], e["Addr"])
	})
	rt := reflect.TypeOf(opData{})
	for i := range rt.NumField() {
		f := rt.Field(i)
		if f.Type.Kind() != reflect.Bool {
			continue
		}
		fn(w, fmt.Sprintf("`opcodeTable[o].%s`.", f.Name), f.Name, "Bool", ops, func(o opData) string {
			return fmt.Sprint(reflect.ValueOf(o).Field(i).Bool())
		})
	}
	fmt.Fprintln(w, "end Op")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "instance : Hashable Op := ⟨fun o => hash o.ctorIdx⟩")
	fmt.Fprintln(w, "instance : ToString Op := ⟨Op.name⟩")
	fmt.Fprintln(w, "instance : Repr Op := ⟨fun o _ => .text (\"GoFV.SSA.Op.\" ++ if o = .Invalid then \"Invalid\" else o.name)⟩")
	fmt.Fprintln(w)

	fmt.Fprintf(w, "/-- The %d generic block kinds, in Go's order (`BlockKind.Invalid` is `BlockInvalid`). -/\n", len(blocks))
	fmt.Fprintln(w, "inductive BlockKind where")
	for _, b := range blocks {
		fmt.Fprintf(w, "  | %s\n", ident(b.name))
	}
	fmt.Fprintln(w, "  deriving DecidableEq, Inhabited, Repr")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace BlockKind")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "/-- Every block kind, in Go's order. -/")
	fmt.Fprint(w, "def all : Array BlockKind := #[")
	for i, b := range blocks {
		if i > 0 {
			fmt.Fprint(w, ", ")
		}
		fmt.Fprintf(w, ".%s", ident(b.name))
	}
	fmt.Fprintln(w, "]")
	fmt.Fprintln(w)
	bfn := func(doc, name, ty string, val func(blockData) string) {
		fmt.Fprintf(w, "/-- %s -/\n", doc)
		fmt.Fprintf(w, "def %s : BlockKind → %s\n", name, ty)
		for _, b := range blocks {
			fmt.Fprintf(w, "  | .%s => %s\n", ident(b.name), val(b))
		}
		fmt.Fprintln(w)
	}
	bfn("`BlockKind.String()`.", "name", "String", func(b blockData) string {
		if b.name == "Invalid" {
			return leanString("BlockInvalid")
		}
		return leanString(b.name)
	})
	bfn("Number of control values (`blockData.controls`).", "controls", "Nat", func(b blockData) string {
		return fmt.Sprint(b.controls)
	})
	bfn("`BlockKind.AuxIntType()` (empty if the kind has no AuxInt).", "auxIntType", "String", func(b blockData) string {
		switch b.aux {
		case "":
			return leanString("")
		case "Int64":
			return leanString("int64")
		}
		log.Fatalf("block %s: unsupported aux %s", b.name, b.aux)
		return ""
	})
	fmt.Fprintln(w, "end BlockKind")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "instance : Hashable BlockKind := ⟨fun k => hash k.ctorIdx⟩")
	fmt.Fprintln(w, "instance : ToString BlockKind := ⟨BlockKind.name⟩")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "end GoFV.SSA")
	if err := os.WriteFile(*out, w.Bytes(), 0o644); err != nil {
		log.Fatal(err)
	}
	fmt.Printf("opsgen: %d ops, %d block kinds -> %s\n", len(ops), len(blocks), *out)
}
