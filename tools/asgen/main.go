// Command asgen generates GoFV/Asm/As.lean, the assembler opcodes (obj.As) of the pinned Go
// tree that compiled arm64 code can carry: the portable opcodes of cmd/internal/obj (AXXX …
// AUNDEF) and the arm64 opcodes of cmd/internal/obj/arm64, with their names (what
// As.String() prints, the gofv-prog export's spelling) and Go values.
//
// Sources (parsed with go/parser, never hand-copied):
//   - src/cmd/internal/obj/link.go: the portable const block (AXXX … A_ARCHSPECIFIC) and the
//     architecture bases (ABase386 = (1 + iota) << 11, …, ABaseARM64, …);
//   - src/cmd/internal/obj/util.go: var Anames (portable names);
//   - src/cmd/internal/obj/arm64/anames.go: var Anames (stringer output, indexed from
//     obj.A_ARCHSPECIFIC).
//
// It also generates (each optional):
//   - -reg GoFV/Asm/Reg.lean (reg.go): the integer constants of cmd/internal/obj/arm64
//     a.out.go and sysRegEnc.go (registers, SPOP_*, C_*, …) except the opcode block;
//   - -opasm GoFV/Asm/OpAsm.lean (opasm.go): opcodeTable[op].asm of ssa/opGen.go for every
//     constructor of -oplean GoFV/SSA/Op.lean, and condBits, blockJump, leJumps, gtJumps of
//     cmd/compile/internal/arm64/ssa.go;
//   - -abi GoFV/Asm/Abi.lean (abi.go): the integer constants of internal/abi symtab.go,
//     bounds.go, stack.go, abi_arm64.go and type.go's TraceArgs*;
//   - -optab GoFV/Asm/Optab.lean (optab.go): the integer constants of arm64/asm7.go, optab in
//     buildop's sorted order, oprange, and the LSE atomic opcode maps;
//   - -obj GoFV/Asm/ObjConst.lean (optab.go): the integer constants of cmd/internal/obj
//     link.go (symbol attributes, ABIs, …) except the opcode block.
//
// Constant values come from go/types (load.go: declarations-only type check of the pinned
// packages for linux/arm64, errors ignored, every emitted value checked to be known).
//
// usage: asgen -go <pinned Go root> -o GoFV/Asm/As.lean [-reg …] [-opasm … -oplean …] [-abi …] [-optab …] [-obj …]
// -source "<version (rev)>"
package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"log"
	"os"
	"path/filepath"
	"strconv"
)

func parse(path string) *ast.File {
	f, err := parser.ParseFile(token.NewFileSet(), path, nil, 0)
	if err != nil {
		log.Fatal(err)
	}
	return f
}

// constBlock returns the names of the const block whose first spec declares first.
func constBlock(f *ast.File, first string) []string {
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.CONST || len(g.Specs) == 0 {
			continue
		}
		vs := g.Specs[0].(*ast.ValueSpec)
		if vs.Names[0].Name != first {
			continue
		}
		var names []string
		for _, s := range g.Specs {
			for _, n := range s.(*ast.ValueSpec).Names {
				names = append(names, n.Name)
			}
		}
		return names
	}
	log.Fatalf("no const block starting with %s", first)
	return nil
}

// anames returns the strings of `var Anames = []string{…}` and the key expression of its
// first element (nil if unkeyed).
func anames(f *ast.File) ([]string, ast.Expr) {
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.VAR {
			continue
		}
		for _, s := range g.Specs {
			vs := s.(*ast.ValueSpec)
			if vs.Names[0].Name != "Anames" {
				continue
			}
			lit := vs.Values[0].(*ast.CompositeLit)
			var out []string
			var key ast.Expr
			for i, e := range lit.Elts {
				if kv, ok := e.(*ast.KeyValueExpr); ok {
					if i != 0 {
						log.Fatal("Anames: key after the first element")
					}
					key = kv.Key
					e = kv.Value
				}
				str, err := strconv.Unquote(e.(*ast.BasicLit).Value)
				if err != nil {
					log.Fatal(err)
				}
				out = append(out, str)
			}
			return out, key
		}
	}
	log.Fatal("no var Anames")
	return nil, nil
}

func index(xs []string, x string) int {
	for i, y := range xs {
		if y == x {
			return i
		}
	}
	log.Fatalf("%s not found", x)
	return -1
}

func main() {
	goroot := flag.String("go", "", "pinned Go root")
	out := flag.String("o", "", "output Lean file (As.lean)")
	source := flag.String("source", "?", "Go version and revision for the header")
	regOut := flag.String("reg", "", "output Lean file for the arm64 a.out.go constants (Reg.lean)")
	opAsmOut := flag.String("opasm", "", "output Lean file for opcodeTable asm and arm64/ssa.go tables (OpAsm.lean)")
	abiOut := flag.String("abi", "", "output Lean file for the internal/abi constants (Abi.lean)")
	optabOut := flag.String("optab", "", "output Lean file for the asm7.go tables (Optab.lean; needs the a.out.go names)")
	objOut := flag.String("obj", "", "output Lean file for the cmd/internal/obj link.go constants (ObjConst.lean)")
	opLean := flag.String("oplean", "", "GoFV/SSA/Op.lean (constructor names checked by -opasm)")
	flag.Parse()
	if *goroot == "" || *out == "" {
		log.Fatal("usage: asgen -go <Go root> -o <As.lean> [-reg <Reg.lean>] [-opasm <OpAsm.lean> -oplean <Op.lean>] [-abi <Abi.lean>] -source <version>")
	}
	objDir := filepath.Join(*goroot, "src/cmd/internal/obj")
	link := parse(filepath.Join(objDir, "link.go"))
	portable := constBlock(link, "AXXX")
	archSpecific := index(portable, "A_ARCHSPECIFIC")
	bases := constBlock(link, "ABase386")
	baseARM64 := (index(bases, "ABaseARM64") + 1) << 11
	generic, key := anames(parse(filepath.Join(objDir, "util.go")))
	if key != nil || len(generic) != archSpecific {
		log.Fatalf("obj.Anames has %d names, A_ARCHSPECIFIC is %d", len(generic), archSpecific)
	}
	for i, n := range generic {
		if "A"+n != portable[i] {
			log.Fatalf("obj.Anames[%d] = %q, constant %s", i, n, portable[i])
		}
	}
	arm64, key := anames(parse(filepath.Join(objDir, "arm64/anames.go")))
	if sel, ok := key.(*ast.SelectorExpr); !ok || sel.Sel.Name != "A_ARCHSPECIFIC" {
		log.Fatal("arm64.Anames does not start at obj.A_ARCHSPECIFIC")
	}
	all := append(append([]string{}, generic...), arm64...)
	seen := map[string]bool{}
	for _, n := range all {
		if seen[n] {
			log.Fatalf("duplicate opcode name %s", n)
		}
		seen[n] = true
	}

	var b bytes.Buffer
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("-- Generated by tools/asgen (scripts/gen-asm.sh) from Go %s\n", *source)
	p("-- src/cmd/internal/obj/{link.go,util.go}, src/cmd/internal/obj/arm64/anames.go. DO NOT EDIT.\n")
	p("import Std.Data.HashMap.Basic\n\nnamespace GoFV.Asm\n\n")
	p("/-- The %d assembler opcodes (`obj.As`) of compiled arm64 code: the %d portable opcodes of\n", len(all), len(generic))
	p("`cmd/internal/obj` (`AXXX` … `AUNDEF`) and the %d arm64 opcodes (`AADC` …), in Go's order.\n", len(arm64))
	p("Constructors are the Go constants without `A` (`obj.ATEXT` is `As.TEXT`, `arm64.AMOVD` is\n")
	p("`As.MOVD`), i.e. what `As.String()` prints. -/\n")
	p("inductive As where\n")
	for _, n := range all {
		p("  | %s\n", n)
	}
	p("  deriving DecidableEq, Inhabited\n\nnamespace As\n\n")
	p("/-- Every opcode, in constructor order. -/\ndef all : Array As := #[\n")
	for i, n := range all {
		sep := ","
		if i == len(all)-1 {
			sep = "]"
		}
		p("  .%s%s\n", n, sep)
	}
	p("\n/-- `As.String()`. -/\ndef name : As → String\n")
	for _, n := range all {
		p("  | .%s => %q\n", n, n)
	}
	p("\n/-- The Go value: portable opcodes from 0, arm64 opcodes from `obj.ABaseARM64 +\n")
	p("obj.A_ARCHSPECIFIC` = %d + %d. -/\n", baseARM64, archSpecific)
	p("def goNum (a : As) : Nat :=\n  let i := a.ctorIdx\n  if i < %d then i else i + %d\n\n", archSpecific, baseARM64)
	p("/-- Opcodes by name. -/\ndef byName : Std.HashMap String As :=\n")
	p("  all.foldl (fun m a => m.insert a.name a) {}\n\n")
	p("/-- The opcode named `s` (`As.String()` spelling), if any. -/\n")
	p("def ofName? (s : String) : Option As := byName[s]?\n\n")
	p("end As\n\ninstance : ToString As := ⟨As.name⟩\n")
	p("instance : Repr As := ⟨fun a _ => .text (\"GoFV.Asm.As.\" ++ a.name)⟩\n\nend GoFV.Asm\n")
	writeFile(*out, b.Bytes())

	tab := &asTable{generic: generic, arm64: arm64, archSpecific: archSpecific, baseARM64: baseARM64}
	l := newLoader(*goroot, "cmd/internal/obj", "cmd/internal/obj/arm64", "internal/abi", "internal/goarch")
	if v, _ := constant.Int64Val(l.intConst("cmd/internal/obj", "ABaseARM64")); int(v) != baseARM64 {
		log.Fatalf("obj.ABaseARM64 = %d, asgen computed %d", v, baseARM64)
	}
	if v, _ := constant.Int64Val(l.intConst("cmd/internal/obj", "A_ARCHSPECIFIC")); int(v) != archSpecific {
		log.Fatalf("obj.A_ARCHSPECIFIC = %d, asgen computed %d", v, archSpecific)
	}
	var regNames map[string]bool
	if *regOut != "" || *opAsmOut != "" || *optabOut != "" {
		var reg []byte
		reg, regNames = genReg(l, *source)
		if *regOut != "" {
			writeFile(*regOut, reg)
		}
	}
	if *opAsmOut != "" {
		if *opLean == "" {
			log.Fatal("-opasm needs -oplean")
		}
		writeFile(*opAsmOut, genOpAsm(l, tab, regNames, *opLean, *source))
	}
	if *optabOut != "" {
		writeFile(*optabOut, genOptab(l, tab, regNames, *goroot, *source))
	}
	if *objOut != "" {
		writeFile(*objOut, genObj(l, *source))
	}
	if *abiOut != "" {
		writeFile(*abiOut, genAbi(l, *source))
	}
}

func writeFile(path string, data []byte) {
	if err := os.WriteFile(path, data, 0o666); err != nil {
		log.Fatal(err)
	}
}

// asTable maps Go `obj.As` values to the As.lean constructor names.
type asTable struct {
	generic, arm64          []string
	archSpecific, baseARM64 int
}

// name is the As constructor of the opcode with Go value v (fatal if v is no opcode).
func (t *asTable) name(v constant.Value) string {
	n, ok := constant.Int64Val(v)
	if !ok {
		log.Fatalf("opcode value %s is not an int64", v)
	}
	if n >= 0 && n < int64(t.archSpecific) {
		return t.generic[n]
	}
	i := n - int64(t.baseARM64+t.archSpecific)
	if i >= 0 && i < int64(len(t.arm64)) {
		return t.arm64[i]
	}
	log.Fatalf("%d is not an arm64 or portable opcode", n)
	return ""
}
