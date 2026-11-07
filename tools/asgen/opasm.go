package main

import (
	"bufio"
	"bytes"
	"fmt"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/token"
	"log"
	"os"
	"path/filepath"
	"strconv"
	"strings"
)

// leanCtors returns the constructor names of `inductive <typ> where` in the Lean file path
// (the generated GoFV/SSA/Op.lean: one `  | Name` line per constructor).
func leanCtors(path, typ string) []string {
	f, err := os.Open(path)
	if err != nil {
		log.Fatal(err)
	}
	defer f.Close()
	var out []string
	in := false
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := sc.Text()
		switch {
		case line == "inductive "+typ+" where":
			in = true
		case in && strings.HasPrefix(line, "  | "):
			out = append(out, strings.TrimPrefix(line, "  | "))
		case in:
			if len(out) == 0 {
				log.Fatalf("%s: inductive %s has no constructors", path, typ)
			}
			return out
		}
	}
	if err := sc.Err(); err != nil {
		log.Fatal(err)
	}
	log.Fatalf("%s: no inductive %s", path, typ)
	return nil
}

// goSource is a parsed Go file whose selector expressions are evaluated against the loader.
type goSource struct {
	l       *loader
	fset    *token.FileSet
	f       *ast.File
	name    string
	imports map[string]string // local package name → import path
}

func parseGo(l *loader, path string) *goSource {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, path, nil, 0)
	if err != nil {
		log.Fatal(err)
	}
	s := &goSource{l: l, fset: fset, f: f, name: filepath.Base(path), imports: map[string]string{}}
	for _, im := range f.Imports {
		p, _ := strconv.Unquote(im.Path.Value)
		n := p[strings.LastIndex(p, "/")+1:]
		if im.Name != nil {
			n = im.Name.Name
		}
		s.imports[n] = p
	}
	return s
}

func (s *goSource) fatalf(e ast.Node, format string, args ...any) {
	log.Fatalf("%s: %s", s.fset.Position(e.Pos()), fmt.Sprintf(format, args...))
}

func (s *goSource) line(e ast.Node) int { return s.fset.Position(e.Pos()).Line }

// sel splits a qualified identifier pkg.Name into the import path and Name.
func (s *goSource) sel(e ast.Expr) (string, string) {
	se, ok := e.(*ast.SelectorExpr)
	if !ok {
		s.fatalf(e, "not a qualified identifier: %T", e)
	}
	x, ok := se.X.(*ast.Ident)
	if !ok {
		s.fatalf(e, "not a qualified identifier")
	}
	path, ok := s.imports[x.Name]
	if !ok {
		s.fatalf(e, "%s is not an imported package", x.Name)
	}
	return path, se.Sel.Name
}

// eval is the integer value of e: an integer literal or a constant of a loaded package.
func (s *goSource) eval(e ast.Expr) constant.Value {
	if lit, ok := e.(*ast.BasicLit); ok && lit.Kind == token.INT {
		return constant.MakeFromLiteral(lit.Value, token.INT, 0)
	}
	path, name := s.sel(e)
	if !s.l.allow[path] {
		s.fatalf(e, "constant of unloaded package %s", path)
	}
	return s.l.intConst(path, name)
}

// varLit returns the composite literal initializing the package-level `var name = …`.
func (s *goSource) varLit(name string) *ast.CompositeLit {
	for _, d := range s.f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.VAR {
			continue
		}
		for _, sp := range g.Specs {
			vs := sp.(*ast.ValueSpec)
			if len(vs.Names) == 1 && vs.Names[0].Name == name {
				if len(vs.Values) != 1 {
					s.fatalf(vs, "var %s has no single initializer", name)
				}
				lit, ok := vs.Values[0].(*ast.CompositeLit)
				if !ok {
					s.fatalf(vs, "var %s is not a composite literal", name)
				}
				return lit
			}
		}
	}
	log.Fatalf("%s: no var %s", s.name, name)
	return nil
}

// ssaName strips prefix from the cmd/compile/internal/ssa constant e (ssa.OpX → X).
func (s *goSource) ssaName(e ast.Expr, prefix string, ctors map[string]bool) string {
	path, name := s.sel(e)
	if path != "cmd/compile/internal/ssa" || !strings.HasPrefix(name, prefix) {
		s.fatalf(e, "not an ssa.%s… constant", prefix)
	}
	n := strings.TrimPrefix(name, prefix)
	if !ctors[n] {
		s.fatalf(e, "ssa.%s has no GoFV.SSA constructor", name)
	}
	return n
}

// fields returns the values of the struct literal e by field name (keyed) or position.
func (s *goSource) fields(e ast.Expr, names ...string) []ast.Expr {
	lit, ok := e.(*ast.CompositeLit)
	if !ok || len(lit.Elts) != len(names) {
		s.fatalf(e, "expected a literal with %d fields %v", len(names), names)
	}
	out := make([]ast.Expr, len(names))
	for i, el := range lit.Elts {
		if kv, ok := el.(*ast.KeyValueExpr); ok {
			k, _ := kv.Key.(*ast.Ident)
			j := -1
			for jj, n := range names {
				if k != nil && k.Name == n {
					j = jj
				}
			}
			if j < 0 || out[j] != nil {
				s.fatalf(el, "unexpected field key")
			}
			out[j] = kv.Value
		} else {
			out[i] = el
		}
	}
	for i := range out {
		if out[i] == nil {
			s.fatalf(e, "missing field %s", names[i])
		}
	}
	return out
}

func set(xs []string) map[string]bool {
	m := map[string]bool{}
	for _, x := range xs {
		m[x] = true
	}
	return m
}

// opAsmWitnesses / arm64Witnesses are spot values Lean checks (expected from the Go source).
var opAsmWitnesses = []string{
	"opAsm .ARM64ADD = .ADD", "opAsm .ARM64MOVDconst = .MOVD", "opAsm .ARM64CALLstatic = .XXX",
	"opAsm .ARM64MOVDaddr = .MOVD", "opAsm .ARM64CSEL = .CSEL",
	"opAsm .Add64 = .XXX", "opAsm .Invalid = .XXX", "opAsm .ARM64FMOVDload = .FMOVD",
}
var arm64Witnesses = []string{
	"condBits .ARM64Equal = some SPOP_EQ", "condBits .ARM64LessThanF = some SPOP_MI",
	"condBits .ARM64ADD = none", "blockJump .ARM64ULT = some (.BLO, .BHS)",
	"blockJump .ARM64Z = some (.CBZ, .CBNZ)", "blockJump .Plain = none",
	"leJumps[0]![1]! = (.BPL, 1)", "gtJumps[1]![1]! = (.BPL, 0)",
}

// genOpAsm generates OpAsm.lean.
func genOpAsm(l *loader, tab *asTable, regNames map[string]bool, opLean, source string) []byte {
	ops := leanCtors(opLean, "Op")
	opSet := set(ops)
	kinds := set(leanCtors(opLean, "BlockKind"))
	internal := filepath.Join(l.goroot, "src/cmd/compile/internal")

	// opcodeTable[op].asm, by the Op constant block of opGen.go.
	og := parseGo(l, filepath.Join(internal, "ssa/opGen.go"))
	var opConsts []string
	for _, d := range og.f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok || g.Tok != token.CONST || g.Specs[0].(*ast.ValueSpec).Names[0].Name != "OpInvalid" {
			continue
		}
		for _, sp := range g.Specs {
			for _, n := range sp.(*ast.ValueSpec).Names {
				opConsts = append(opConsts, n.Name)
			}
		}
	}
	table := og.varLit("opcodeTable")
	if len(opConsts) == 0 || len(table.Elts) != len(opConsts) {
		log.Fatalf("opGen.go: %d Op constants, %d opcodeTable entries", len(opConsts), len(table.Elts))
	}
	asmOf := map[string]string{}
	tableLine := map[string]int{}
	for i, el := range table.Elts {
		name := strings.TrimPrefix(opConsts[i], "Op")
		if !opSet[name] {
			continue
		}
		entry, ok := el.(*ast.CompositeLit)
		if !ok {
			og.fatalf(el, "opcodeTable entry is not a literal")
		}
		asm := "XXX"
		for _, f := range entry.Elts {
			kv, ok := f.(*ast.KeyValueExpr)
			if !ok {
				og.fatalf(f, "unkeyed opInfo field")
			}
			if k, _ := kv.Key.(*ast.Ident); k != nil && k.Name == "name" {
				lit, ok := kv.Value.(*ast.BasicLit)
				if !ok || !strings.HasSuffix(opConsts[i], strings.Trim(lit.Value, "\"")) {
					og.fatalf(f, "opcodeTable[%s] has another name", opConsts[i])
				}
			}
			if k, _ := kv.Key.(*ast.Ident); k != nil && k.Name == "asm" {
				asm = tab.name(og.eval(kv.Value))
			}
		}
		asmOf[name] = asm
		tableLine[name] = og.line(el)
	}
	for _, op := range ops {
		if _, ok := asmOf[op]; !ok {
			log.Fatalf("Op.lean constructor %s is not in opGen.go", op)
		}
	}

	// arm64/ssa.go tables.
	as := parseGo(l, filepath.Join(internal, "arm64/ssa.go"))
	type condEntry struct{ op, spop string }
	var conds []condEntry
	seen := map[string]bool{}
	condLit := as.varLit("condBits")
	for _, el := range condLit.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			as.fatalf(el, "condBits: unkeyed element")
		}
		op := as.ssaName(kv.Key, "Op", opSet)
		path, spop := as.sel(kv.Value)
		if path != "cmd/internal/obj/arm64" || !regNames[spop] {
			as.fatalf(kv.Value, "condBits value is not a Reg.lean constant")
		}
		as.eval(kv.Value) // known integer value
		if seen[op] {
			as.fatalf(el, "duplicate condBits key %s", op)
		}
		seen[op] = true
		conds = append(conds, condEntry{op, spop})
	}
	type jumpEntry struct{ kind, asm, inv string }
	var jumps []jumpEntry
	jumpLit := as.varLit("blockJump")
	for _, el := range jumpLit.Elts {
		kv, ok := el.(*ast.KeyValueExpr)
		if !ok {
			as.fatalf(el, "blockJump: unkeyed element")
		}
		k := as.ssaName(kv.Key, "Block", kinds)
		if seen["Block"+k] {
			as.fatalf(el, "duplicate blockJump key %s", k)
		}
		seen["Block"+k] = true
		f := as.fields(kv.Value, "asm", "invasm")
		jumps = append(jumps, jumpEntry{k, tab.name(as.eval(f[0])), tab.name(as.eval(f[1]))})
	}
	indexJumps := func(name string) (string, int) {
		lit := as.varLit(name)
		if len(lit.Elts) != 2 {
			as.fatalf(lit, "%s: expected [2][2]IndexJump", name)
		}
		var rows []string
		for _, row := range lit.Elts {
			r, ok := row.(*ast.CompositeLit)
			if !ok || len(r.Elts) != 2 {
				as.fatalf(row, "%s: expected [2]IndexJump", name)
			}
			var cells []string
			for _, cell := range r.Elts {
				f := as.fields(cell, "Jump", "Index")
				idx, ok := constant.Int64Val(as.eval(f[1]))
				if !ok || idx < 0 {
					as.fatalf(cell, "%s: bad Index", name)
				}
				cells = append(cells, fmt.Sprintf("(.%s, %d)", tab.name(as.eval(f[0])), idx))
			}
			rows = append(rows, "#["+strings.Join(cells, ", ")+"]")
		}
		return "#[" + strings.Join(rows, ", ") + "]", as.line(lit)
	}
	leJumps, leLine := indexJumps("leJumps")
	gtJumps, gtLine := indexJumps("gtJumps")

	var b bytes.Buffer
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("-- Generated by tools/asgen (scripts/gen-asm.sh) from Go %s\n", source)
	p("-- src/cmd/compile/internal/ssa/opGen.go, src/cmd/compile/internal/arm64/ssa.go; ops checked\n")
	p("-- against GoFV/SSA/Op.lean. DO NOT EDIT.\n")
	p("import GoFV.SSA.Op\nimport GoFV.Asm.As\nimport GoFV.Asm.Reg\n\n")
	p("/-! # SSA op opcodes and the arm64 branch tables\n\n")
	p("* `opAsm`: `Op.Asm()` = `opcodeTable[op].asm` (ssa/opGen.go:%d, `asm:` fields; `obj.AXXX`\n", og.line(table))
	p("  when absent) for every `GoFV.SSA.Op`.\n")
	p("* `ARM64.condBits` (arm64/ssa.go:%d), `ARM64.blockJump` (arm64/ssa.go:%d),\n", as.line(condLit), as.line(jumpLit))
	p("  `ARM64.leJumps` (arm64/ssa.go:%d), `ARM64.gtJumps` (arm64/ssa.go:%d): `[2][2]ssagen.IndexJump`\n", leLine, gtLine)
	p("  as `(Jump, Index)` pairs. -/\n\n")
	p("namespace GoFV.Asm\n\nopen GoFV.SSA (Op BlockKind)\n\n")
	p("/-- `opcodeTable[op].asm` (ssa/opGen.go). -/\ndef opAsm : Op → As\n")
	for _, op := range ops {
		p("  | .%s => .%s\n", op, asmOf[op])
	}
	p("\nnamespace ARM64\n\n")
	p("/-- `condBits` (arm64/ssa.go:%d): the condition (`SpecialOperand`) of a flag predicate op. -/\n", as.line(condLit))
	p("def condBits : Op → Option Int\n")
	for _, c := range conds {
		p("  | .%s => some %s\n", c.op, c.spop)
	}
	p("  | _ => none\n\n")
	p("/-- `blockJump` (arm64/ssa.go:%d): `(asm, invasm)` of a conditional block kind. -/\n", as.line(jumpLit))
	p("def blockJump : BlockKind → Option (As × As)\n")
	for _, j := range jumps {
		p("  | .%s => some (.%s, .%s)\n", j.kind, j.asm, j.inv)
	}
	p("  | _ => none\n\n")
	p("/-- `leJumps` (arm64/ssa.go:%d): `LEnoov` branches, `[next == b.Succs[i]][j]` = `(Jump, Index)`. -/\n", leLine)
	p("def leJumps : Array (Array (As × Nat)) := %s\n\n", leJumps)
	p("/-- `gtJumps` (arm64/ssa.go:%d): `GTnoov` branches, `[next == b.Succs[i]][j]` = `(Jump, Index)`. -/\n", gtLine)
	p("def gtJumps : Array (Array (As × Nat)) := %s\n\n", gtJumps)
	p("/-! Spot values. -/\n\n")
	for _, w := range arm64Witnesses {
		p("example : %s := rfl\n", w)
	}
	p("\nend ARM64\n\n")
	for _, w := range opAsmWitnesses {
		p("example : %s := rfl\n", w)
	}
	p("\nend GoFV.Asm\n")
	return b.Bytes()
}
