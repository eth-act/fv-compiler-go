// Command opsgen generates GoFV/SSA/Op.lean and GoFV/SSA/OpARM64.lean from the op tables of
// the Go compiler: the generic archs (cmd/compile/internal/ssa/_gen/{genericOps,decOps,
// divisibleOps,divmodOps}.go) and ARM64 (ARM64Ops.go). The SIMD ops (simdgenericOps.go,
// simdARM64ops.go) are left out, see nosimd.go.
//
// Those files are package main of the _gen generator and refer to its types (opData,
// blockData, arch, ...). scripts/gen-ops.sh copies them next to this file in a scratch
// directory and runs the result, so the op tables are evaluated by Go itself (including the
// init functions that register the archs). The types below and the helpers in regmask.go are
// copies of _gen/main.go; checkTypes and checkFuncs verify that they still match. checkOpGen
// (opgen.go) compares every exported op, block kind and the ARM64 register tables with the
// pinned generated opGen.go, which the compiler is built from.
//
// usage: opsgen -gen <_gen dir> -o <Op.lean> -arm64 <OpARM64.lean> -regs <RegARM64.lean>
//
//	-source <description>
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
	"path"
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

// exportedArchs are the archs whose ops and blocks enter the Lean tables.
var exportedArchs = map[string]bool{"ARM64": true, "dec": true, "divisible": true, "divmod": true, "generic": true}

func parseGo(file string) (*token.FileSet, *ast.File) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, file, nil, 0)
	if err != nil {
		log.Fatal(err)
	}
	return fset, f
}

func nodeString(fset *token.FileSet, n any) string {
	var b bytes.Buffer
	if err := printer.Fprint(&b, fset, n); err != nil {
		log.Fatal(err)
	}
	return b.String()
}

// checkTypes fails unless every struct above has exactly the fields (names and types) of the
// same-named struct in _gen/main.go.
func checkTypes(genDir string) {
	fset, f := parseGo(filepath.Join(genDir, "main.go"))
	want := map[string]reflect.Type{
		"arch":      reflect.TypeOf(arch{}),
		"opData":    reflect.TypeOf(opData{}),
		"blockData": reflect.TypeOf(blockData{}),
		"regInfo":   reflect.TypeOf(regInfo{}),
		"regMask":   reflect.TypeOf(regMask{}),
		"intPair":   reflect.TypeOf(intPair{}),
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
				for _, n := range fl.Names {
					got = append(got, n.Name+" "+nodeString(fset, fl.Type))
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

// checkFuncs fails unless each declaration of regMaskFuncs (and the type byKey) in regmask.go
// is textually identical to the one in _gen/main.go.
func checkFuncs(genDir string) {
	decls := func(file string) map[string]string {
		fset, f := parseGo(file)
		m := map[string]string{}
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				name := d.Name.Name
				if d.Recv != nil {
					name = nodeString(fset, d.Recv.List[0].Type) + "." + name
				}
				d.Doc = nil
				m[name] = nodeString(fset, d)
			case *ast.GenDecl:
				if d.Tok != token.TYPE {
					continue
				}
				for _, s := range d.Specs {
					if ts := s.(*ast.TypeSpec); ts.Name.Name == "byKey" {
						m["type byKey"] = nodeString(fset, ts)
					}
				}
			}
		}
		return m
	}
	gen, here := decls(filepath.Join(genDir, "main.go")), decls("regmask.go")
	for _, n := range append(slices.Clone(regMaskFuncs), "type byKey") {
		if gen[n] == "" || gen[n] != here[n] {
			log.Fatalf("%s in _gen/main.go differs from tools/opsgen/regmask.go:\n  _gen: %s\n  here: %s", n, gen[n], here[n])
		}
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

// lop is an exported op with its arch.
type lop struct {
	opData
	archName string // arch.Name(): "" for the generic archs
	pkg      string // path.Base(arch.pkg), the package of the asm constants
	generic  bool
}

// ctor is the Lean constructor: the Go constant without "Op" (OpARM64ADD → ARM64ADD).
func (o lop) ctor() string { return ident(o.archName + o.name) }

func (o lop) goConst() string { return "Op" + o.archName + o.name }

type lblock struct {
	blockData
	archName string
}

func (b lblock) ctor() string    { return ident(b.archName + b.name) }
func (b lblock) goConst() string { return "Block" + b.archName + b.name }

// auxIntType is _gen/rulegen.go blockData.auxIntType, with "" for "invalid" (main.go genOp:
// AuxIntType() returns "" for those kinds).
func (b blockData) auxIntType() string {
	switch b.aux {
	case "S390XCCMaskInt8":
		return "int8"
	case "S390XCCMaskUint8":
		return "uint8"
	case "Int64":
		return "int64"
	}
	return ""
}

// ioInfo is an inputInfo/outputInfo of opGen.go.
type ioInfo struct {
	idx  int
	regs regMask
}

// genReg is the regInfo opGen.go stores for an op (main.go genOp): inputs without empty masks,
// inputs and outputs in allocation order (sort.Sort by register count).
type genReg struct {
	inputs                     []ioInfo
	clobbers                   regMask
	clobbersArg0, clobbersArg1 bool
	outputs                    []ioInfo
}

func genRegInfo(r regInfo) genReg {
	g := genReg{clobbers: r.clobbers, clobbersArg0: r.clobbersArg0, clobbersArg1: r.clobbersArg1}
	var s []intPair
	for i, m := range r.inputs {
		if !m.empty() {
			s = append(s, intPair{countRegs(m), i})
		}
	}
	sort.Sort(byKey(s))
	for _, p := range s {
		g.inputs = append(g.inputs, ioInfo{p.val, r.inputs[p.val]})
	}
	s = s[:0]
	for i, m := range r.outputs {
		s = append(s, intPair{countRegs(m), i})
	}
	sort.Sort(byKey(s))
	for _, p := range s {
		g.outputs = append(g.outputs, ioInfo{p.val, r.outputs[p.val]})
	}
	return g
}

func leanMask(m regMask) string { return fmt.Sprintf("⟨%d, %d⟩", m.v1, m.v2) }

func leanIOs(l []ioInfo) string {
	var s []string
	for _, x := range l {
		s = append(s, fmt.Sprintf("⟨%d, %s⟩", x.idx, leanMask(x.regs)))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

func (g genReg) lean() string {
	var f []string
	if len(g.inputs) > 0 {
		f = append(f, "inputs := "+leanIOs(g.inputs))
	}
	if !g.clobbers.empty() {
		f = append(f, "clobbers := "+leanMask(g.clobbers))
	}
	if g.clobbersArg0 {
		f = append(f, "clobbersArg0 := true")
	}
	if g.clobbersArg1 {
		f = append(f, "clobbersArg1 := true")
	}
	if len(g.outputs) > 0 {
		f = append(f, "outputs := "+leanIOs(g.outputs))
	}
	if len(f) == 0 {
		return "{}"
	}
	return "{ " + strings.Join(f, ", ") + " }"
}

// fn emits `def <name> : <dom> → <ty>` as one match: arms grouped by value, the most frequent
// value as the wildcard default (ties: first in order).
func fn[T any](w *bytes.Buffer, doc, name, dom, ty string, xs []T, ctor func(T) string, val func(T) string) {
	count := map[string]int{}
	var order []string
	for _, x := range xs {
		v := val(x)
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
		fmt.Fprintf(w, "def %s (_ : %s) : %s := %s\n\n", name, dom, ty, def)
		return
	}
	fmt.Fprintf(w, "def %s : %s → %s\n", name, dom, ty)
	for _, v := range order {
		if v == def {
			continue
		}
		for _, x := range xs {
			if val(x) == v {
				fmt.Fprintf(w, "  | .%s => %s\n", ctor(x), v)
			}
		}
	}
	fmt.Fprintf(w, "  | _ => %s\n\n", def)
}

func opCtor(o lop) string       { return o.ctor() }
func blockCtor(b lblock) string { return b.ctor() }

// numRuns emits `goNum`/`ofGoNum?`: Go's constant value as a function of `ctorIdx`. The
// exported constants occur in Go's order with gaps (other archs, SIMD ops), so the map is
// affine on runs of consecutive Go numbers.
func numRuns(w *bytes.Buffer, ty string, nums []int) {
	type run struct{ idx, num, n int }
	var runs []run
	for i, n := range nums {
		if i > 0 && n <= nums[i-1] {
			log.Fatalf("%s: Go numbers not increasing at %d", ty, i)
		}
		if len(runs) > 0 && runs[len(runs)-1].num+runs[len(runs)-1].n == n {
			runs[len(runs)-1].n++
			continue
		}
		runs = append(runs, run{i, n, 1})
	}
	fmt.Fprintf(w, "/-- The Go constant's value (`%s(o)` in the pinned opGen.go; other archs and the SIMD\nentries make it differ from `ctorIdx`). -/\n", ty)
	fmt.Fprintf(w, "def goNum (o : %s) : Nat :=\n  let i := o.ctorIdx\n", ty)
	for k, r := range runs {
		if k == len(runs)-1 {
			fmt.Fprintf(w, "  i + %d\n\n", r.num-r.idx)
		} else {
			fmt.Fprintf(w, "  if i < %d then i + %d else\n", r.idx+r.n, r.num-r.idx)
		}
	}
	fmt.Fprintf(w, "/-- Inverse of `goNum`: the exported %s with Go value `n`, if any. -/\n", ty)
	fmt.Fprintf(w, "def ofGoNum? (n : Nat) : Option %s :=\n", ty)
	for _, r := range runs {
		fmt.Fprintf(w, "  if %d ≤ n ∧ n < %d then all[n - %d]? else\n", r.num, r.num+r.n, r.num-r.idx)
	}
	fmt.Fprintln(w, "  none")
	fmt.Fprintln(w)
}

func main() {
	genDir := flag.String("gen", "", "_gen directory of the pinned Go tree")
	out := flag.String("o", "", "output Lean file (Op.lean)")
	outARM64 := flag.String("arm64", "", "output Lean file of the ARM64 op tables (OpARM64.lean)")
	outRegs := flag.String("regs", "", "output Lean file of the ARM64 registers (RegARM64.lean)")
	source := flag.String("source", "", "description of the Go source tree, for the header")
	flag.Parse()
	if *genDir == "" || *out == "" || *outARM64 == "" || *outRegs == "" || *source == "" {
		flag.Usage()
		os.Exit(2)
	}
	checkTypes(*genDir)
	checkFuncs(*genDir)

	// As _gen/main.go: archs sorted by name, ops and blocks concatenated in that order.
	sort.SliceStable(archs, func(i, j int) bool { return archs[i].name < archs[j].name })
	simd := simdARM64Names()
	ops := []lop{{opData: opData{name: "Invalid"}}}
	blocks := []lblock{{blockData: blockData{name: "Invalid"}}}
	var archNames []string
	var arm64 *arch
	for i := range archs {
		a := &archs[i]
		if !exportedArchs[a.name] {
			log.Fatalf("unexpected arch %s", a.name)
		}
		archNames = append(archNames, a.name)
		name := a.name // arch.Name()
		if a.name == "generic" {
			name = ""
		}
		if a.name == "ARM64" {
			arm64 = a
		}
		for _, o := range a.ops {
			if o.name == "Invalid" || (a.name == "ARM64" && simd[o.name]) {
				continue
			}
			if a.generic && (!reflect.DeepEqual(o.reg, regInfo{}) || o.asm != "" || o.scale != 0) {
				log.Fatalf("generic op %s has register/asm/scale data", o.name)
			}
			ops = append(ops, lop{o, name, path.Base(a.pkg), a.generic})
		}
		for _, b := range a.blocks {
			blocks = append(blocks, lblock{b, name})
		}
	}
	if arm64 == nil {
		log.Fatal("no ARM64 arch")
	}
	ctors, names := map[string]bool{}, map[string]bool{}
	for _, o := range ops {
		if ctors[o.ctor()] || names[o.name] {
			log.Fatalf("duplicate op %s", o.ctor())
		}
		ctors[o.ctor()], names[o.name] = true, true
		if o.aux != "" && !slices.Contains(auxTypes, o.aux) {
			log.Fatalf("op %s: unknown aux type %s", o.name, o.aux)
		}
		// _gen/main.go genOp: symEffect is required exactly for Sym* aux types.
		if (o.symEffect != "") != strings.HasPrefix(o.aux, "Sym") {
			log.Fatalf("op %s: symEffect %q with aux %q", o.name, o.symEffect, o.aux)
		}
	}
	bctors := map[string]bool{}
	for _, b := range blocks {
		if bctors[b.ctor()] {
			log.Fatalf("duplicate block kind %s", b.ctor())
		}
		bctors[b.ctor()] = true
	}
	g := checkOpGen(filepath.Join(*genDir, "..", "opGen.go"), ops, blocks, arm64, simd)

	writeOps(*out, *source, archNames, ops, blocks, g)
	writeARM64(*outARM64, *source, ops)
	writeRegs(*outRegs, *source, arm64)
	fmt.Printf("opsgen: %d ops (%d ARM64), %d block kinds, %d ARM64 registers -> %s, %s\n",
		len(ops), g.nARM64, len(blocks), len(arm64.regnames), *out, *outARM64)
}

func header(w *bytes.Buffer, source, what string) {
	fmt.Fprintf(w, "-- Generated by tools/opsgen (scripts/gen-ops.sh) from %s\n", source)
	fmt.Fprintf(w, "-- src/cmd/compile/internal/ssa/_gen, %s; without the SIMD ops\n", what)
	fmt.Fprintln(w, "-- (tools/opsgen/nosimd.go); checked against opGen.go. DO NOT EDIT.")
}

func writeOps(file, source string, archNames []string, ops []lop, blocks []lblock, g opGenNums) {
	w := new(bytes.Buffer)
	header(w, source, "archs "+strings.Join(archNames, ", "))
	fmt.Fprintln(w, "import GoFV.SSA.OpInfo")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace GoFV.SSA")
	fmt.Fprintln(w)
	fmt.Fprintf(w, "/-- The %d SSA ops (%d ARM64, %d generic), in the order of Go's `opcodeTable` (`Op.Invalid` is\n`OpInvalid`). Constructors are the Go constants without `Op` (`OpARM64ADD` is `Op.ARM64ADD`). -/\n",
		len(ops), g.nARM64, len(ops)-1-g.nARM64)
	fmt.Fprintln(w, "inductive Op where")
	for _, o := range ops {
		fmt.Fprintf(w, "  | %s\n", o.ctor())
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
		fmt.Fprintf(w, "  .%s%s\n", o.ctor(), sep)
	}
	fmt.Fprintln(w)
	opFn := func(doc, name, ty string, val func(lop) string) {
		fn(w, doc, name, "Op", ty, ops, opCtor, val)
	}
	opFn("`Op.String()`: the op's name (`opcodeTable[o].name`; `ADD` for `OpARM64ADD`).", "name", "String", func(o lop) string {
		if o.name == "Invalid" {
			return leanString("OpInvalid")
		}
		return leanString(o.name)
	})
	opFn("The op's arch prefix (`arch.Name()`: `\"ARM64\"`, `\"\"` for the generic ops and `Invalid`).", "archName", "String", func(o lop) string {
		return leanString(o.archName)
	})
	opFn("`opcodeTable[o].generic`.", "generic", "Bool", func(o lop) string {
		return fmt.Sprint(o.generic)
	})
	opFn("`opcodeTable[o].argLen`: number of arguments, -1 if variable.", "argLen", "Int", func(o lop) string {
		if o.argLength < 0 {
			return fmt.Sprintf("(%d)", o.argLength)
		}
		return fmt.Sprint(o.argLength)
	})
	opFn("`opcodeTable[o].auxType`.", "auxType", "AuxType", func(o lop) string {
		if o.aux == "" {
			return ".None"
		}
		return "." + o.aux
	})
	opFn("Default result type (`opData.typ`, as written in `_gen`; empty if none).", "typ", "String", func(o lop) string {
		return leanString(o.typ)
	})
	opFn("`opcodeTable[o].symEffect`.", "symEffect", "SymEffect", func(o lop) string {
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
		opFn(fmt.Sprintf("`opcodeTable[o].%s`.", f.Name), f.Name, "Bool", func(o lop) string {
			return fmt.Sprint(reflect.ValueOf(o.opData).Field(i).Bool())
		})
	}
	fmt.Fprintln(w, "/-- The op's name in the gofv export (`docs/contracts/export.md`): arch prefix and name\n(`ARM64ADD`; generic ops: `name`). -/")
	fmt.Fprintln(w, "def exportName (o : Op) : String := o.archName ++ o.name")
	fmt.Fprintln(w)
	numRuns(w, "Op", g.ops)
	fmt.Fprintln(w, "end Op")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "instance : Hashable Op := ⟨fun o => hash o.ctorIdx⟩")
	fmt.Fprintln(w, "instance : ToString Op := ⟨Op.name⟩")
	fmt.Fprintln(w, "instance : Repr Op := ⟨fun o _ => .text (\"GoFV.SSA.Op.\" ++ if o = .Invalid then \"Invalid\" else o.exportName)⟩")
	fmt.Fprintln(w)

	fmt.Fprintf(w, "/-- The %d block kinds (ARM64 and generic), in Go's order (`BlockKind.Invalid` is `BlockInvalid`;\n`BlockARM64EQ` is `BlockKind.ARM64EQ`). -/\n", len(blocks))
	fmt.Fprintln(w, "inductive BlockKind where")
	for _, b := range blocks {
		fmt.Fprintf(w, "  | %s\n", b.ctor())
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
		fmt.Fprintf(w, ".%s", b.ctor())
	}
	fmt.Fprintln(w, "]")
	fmt.Fprintln(w)
	bFn := func(doc, name, ty string, val func(lblock) string) {
		fn(w, doc, name, "BlockKind", ty, blocks, blockCtor, val)
	}
	bFn("`BlockKind.String()` (`EQ` for `BlockARM64EQ`).", "name", "String", func(b lblock) string {
		if b.name == "Invalid" {
			return leanString("BlockInvalid")
		}
		return leanString(b.name)
	})
	bFn("The kind's arch prefix (`\"ARM64\"`, `\"\"` for the generic kinds and `Invalid`).", "archName", "String", func(b lblock) string {
		return leanString(b.archName)
	})
	bFn("Number of control values (`blockData.controls`).", "controls", "Nat", func(b lblock) string {
		return fmt.Sprint(b.controls)
	})
	bFn("`BlockKind.AuxIntType()` (empty if the kind has no AuxInt).", "auxIntType", "String", func(b lblock) string {
		return leanString(b.auxIntType())
	})
	bFn("`blockData.aux`: the kind's aux type as written in `_gen` (empty if none).", "aux", "String", func(b lblock) string {
		return leanString(b.aux)
	})
	fmt.Fprintln(w, "/-- The kind's name in the gofv export: arch prefix and name (`ARM64EQ`; generic: `name`). -/")
	fmt.Fprintln(w, "def exportName (k : BlockKind) : String := k.archName ++ k.name")
	fmt.Fprintln(w)
	numRuns(w, "BlockKind", g.blocks)
	fmt.Fprintln(w, "end BlockKind")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "instance : Hashable BlockKind := ⟨fun k => hash k.ctorIdx⟩")
	fmt.Fprintln(w, "instance : ToString BlockKind := ⟨BlockKind.name⟩")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "end GoFV.SSA")
	if err := os.WriteFile(file, w.Bytes(), 0o644); err != nil {
		log.Fatal(err)
	}
}

// paramRegs is main.go's parameterRegisterList: register numbers of the named registers.
func paramRegs(a *arch, names string) []int {
	num := map[string]int{}
	for i, r := range a.regnames {
		num[r] = i
	}
	var regs []int
	for _, n := range strings.Split(strings.TrimSpace(names), " ") {
		if n == "" {
			continue
		}
		i, ok := num[n]
		if !ok {
			log.Fatalf("parameter register %s not found", n)
		}
		regs = append(regs, i)
	}
	return regs
}

func writeARM64(file, source string, ops []lop) {
	w := new(bytes.Buffer)
	header(w, source, "ARM64Ops.go")
	fmt.Fprintln(w, "import GoFV.SSA.Op")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace GoFV.SSA")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace Op")
	fmt.Fprintln(w)
	fn(w, "`opcodeTable[o].reg` (`regInfo`, inputs and outputs in allocation order: by number of\nallowed registers, as `_gen/main.go` genOp sorts them; inputs with an empty mask left out).\nEmpty for the generic ops.", "regInfo", "Op", "RegInfo", ops, opCtor, func(o lop) string {
		return genRegInfo(o.reg).lean()
	})
	fn(w, "`opData.asm`: the instruction (`arm64.A<asm>` in opGen.go; empty if none).", "asm", "Op", "String", ops, opCtor, func(o lop) string {
		return leanString(o.asm)
	})
	fn(w, "`opcodeTable[o].scale`.", "scale", "Op", "Nat", ops, opCtor, func(o lop) string {
		return fmt.Sprint(o.scale)
	})
	fmt.Fprintln(w, "end Op")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "end GoFV.SSA")
	if err := os.WriteFile(file, w.Bytes(), 0o644); err != nil {
		log.Fatal(err)
	}
}

func writeRegs(file, source string, a *arch) {
	w := new(bytes.Buffer)
	header(w, source, "ARM64Ops.go")
	fmt.Fprintln(w, "import GoFV.SSA.OpInfo")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace GoFV.SSA")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "namespace ARM64")
	fmt.Fprintln(w)
	fmt.Fprintf(w, "/-- `registersARM64`: the %d registers known to regalloc, `num` = index (R18 = platform register\nand R27 = REGTMP are absent; `g` is R28, `ZERO` and `SP` are both encoding 31). -/\n", len(a.regnames))
	fmt.Fprintln(w, "def registers : Array Register := #[")
	for i, r := range a.regnames {
		sep := ","
		if i == len(a.regnames)-1 {
			sep = "]"
		}
		fmt.Fprintf(w, "  ⟨%d, %s⟩%s\n", i, leanString(r), sep)
	}
	fmt.Fprintln(w)
	ints := func(l []int) string {
		var s []string
		for _, x := range l {
			s = append(s, fmt.Sprint(x))
		}
		return "[" + strings.Join(s, ", ") + "]"
	}
	fmt.Fprintf(w, "/-- `paramIntRegARM64`: register numbers of the integer argument registers (%s). -/\n", a.ParamIntRegNames)
	fmt.Fprintf(w, "def paramIntReg : List Nat := %s\n\n", ints(paramRegs(a, a.ParamIntRegNames)))
	fmt.Fprintf(w, "/-- `paramFloatRegARM64` (%s). -/\n", a.ParamFloatRegNames)
	fmt.Fprintf(w, "def paramFloatReg : List Nat := %s\n\n", ints(paramRegs(a, a.ParamFloatRegNames)))
	masks := []struct {
		name string
		m    regMask
	}{{"gpRegMask", a.gpregmask}, {"fpRegMask", a.fpregmask}, {"simdRegMask", a.simdregmask}, {"specialRegMask", a.specialregmask}}
	for _, m := range masks {
		fmt.Fprintf(w, "/-- `%sARM64`. -/\ndef %s : RegMask := %s\n\n", m.name, m.name, leanMask(m.m))
	}
	if !a.fp32regmask.empty() || !a.fp64regmask.empty() {
		log.Fatal("ARM64 has fp32/fp64 register masks")
	}
	fmt.Fprintf(w, "/-- `framepointerRegARM64` (-1: none). -/\ndef framepointerReg : Int := %d\n\n", a.framepointerreg)
	fmt.Fprintf(w, "/-- `linkRegARM64` (R30). -/\ndef linkReg : Int := %d\n\n", a.linkreg)
	fmt.Fprintln(w, "end ARM64")
	fmt.Fprintln(w)
	fmt.Fprintln(w, "end GoFV.SSA")
	if err := os.WriteFile(file, w.Bytes(), 0o644); err != nil {
		log.Fatal(err)
	}
}
