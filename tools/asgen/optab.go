package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/constant"
	"go/token"
	"go/types"
	"log"
	"os"
	"path/filepath"
	"runtime"
	"slices"
	"sort"
	"strconv"
)

// optabEntry is arm64.Optab (asm7.go) with the Go field types.
type optabEntry struct {
	as             int64
	a1, a2, a3, a4 uint8
	a5             uint8
	type_          int8
	size_          int8
	param          int16
	flag           int8
	scond          uint8
	line           int
}

// ocmp is asm7.go's ocmp (the comparator buildop sorts optab with; a5, type_, size_, param
// and flag are not compared).
func ocmp(p1, p2 optabEntry) int {
	if p1.as != p2.as {
		return int(p1.as) - int(p2.as)
	}
	if p1.a1 != p2.a1 {
		return int(p1.a1) - int(p2.a1)
	}
	if p1.a2 != p2.a2 {
		return int(p1.a2) - int(p2.a2)
	}
	if p1.a3 != p2.a3 {
		return int(p1.a3) - int(p2.a3)
	}
	if p1.a4 != p2.a4 {
		return int(p1.a4) - int(p2.a4)
	}
	if p1.scond != p2.scond {
		return int(p1.scond) - int(p2.scond)
	}
	return 0
}

// optabWitnesses are spot facts Lean checks: entries of the sorted table and the ranges of
// some opcodes, as read off the asm section of the quick corpus (`Optab` index and opcode).
var optabWitnesses = []string{
	"(optab[0]!).as = .CALL", "(optab[301 - 1]!).as = .MOVD", "(optab[13 - 1]!).as = .PCDATA",
	"(optab[2 - 1]!).as = .CALL", "(optab[85 - 1]!).as = .CBZ",
	"(oprange .CBNZW).isSome = true", "oprange .SUBS = oprange .ADD",
	"oprange .EOR = oprange .AND", "atomicSWP .SWPALD = some 0xf8e08000",
	"atomicSWP .SWPD = some 0xf8208000", "prfopfield SPOP_PSTL3STRM = some 21",
	"rprfopfield SPOP_PSTSTRM = some 5", "(sysInstFields SPOP_VAE1IS).map (·.op2) = some 1",
}

// genOptab generates Optab.lean: the integer constants of asm7.go, optab in the order
// buildop leaves it (slices.SortFunc with ocmp), the oprange table buildop builds, the
// atomicLDADD / atomicSWP / atomicCASP opcode maps and the special-operand tables
// (rprfopfield, prfopfield, sysInstFields, pstatefield).
func genOptab(l *loader, tab *asTable, regNames map[string]bool, goroot, source string) []byte {
	const pkg = "cmd/internal/obj/arm64"
	// slices.SortFunc is pdqsort, which is not stable: the order of entries that ocmp calls
	// equal depends on the algorithm, so it must be the pinned tree's.
	host, err1 := os.ReadFile(filepath.Join(runtime.GOROOT(), "src/slices/zsortanyfunc.go"))
	pinned, err2 := os.ReadFile(filepath.Join(goroot, "src/slices/zsortanyfunc.go"))
	if err1 != nil || err2 != nil || !bytes.Equal(host, pinned) {
		log.Fatalf("optab: the generator's slices.SortFunc (%s) differs from the pinned tree's", runtime.Version())
	}
	l.load(pkg)
	info := l.info[pkg]
	f := l.file(pkg, "asm7.go")
	scope := l.pkgs[pkg].Scope()
	objScope := l.load("cmd/internal/obj").Scope()
	pos := func(n ast.Node) token.Position { return l.fset.Position(n.Pos()) }
	val := func(e ast.Expr) int64 {
		tv, ok := info.Types[e]
		if !ok || tv.Value == nil || tv.Value.Kind() != constant.Int {
			log.Fatalf("%s: no constant integer value", pos(e))
		}
		v, ok := constant.Int64Val(tv.Value)
		if !ok {
			log.Fatalf("%s: not an int64", pos(e))
		}
		return v
	}
	// constOf resolves a constant name in a function body (not type-checked): an identifier
	// of the arm64 package or obj.Name.
	constOf := func(e ast.Expr) int64 {
		var o types.Object
		switch x := e.(type) {
		case *ast.Ident:
			o = scope.Lookup(x.Name)
		case *ast.SelectorExpr:
			if id, ok := x.X.(*ast.Ident); ok && id.Name == "obj" {
				o = objScope.Lookup(x.Sel.Name)
			}
		}
		c, ok := o.(*types.Const)
		if !ok || c.Val().Kind() != constant.Int {
			log.Fatalf("%s: not an integer constant", pos(e))
		}
		v, _ := constant.Int64Val(c.Val())
		return v
	}
	varLit := func(name string) *ast.CompositeLit {
		for _, d := range f.Decls {
			g, ok := d.(*ast.GenDecl)
			if !ok || g.Tok != token.VAR {
				continue
			}
			for _, sp := range g.Specs {
				vs := sp.(*ast.ValueSpec)
				if len(vs.Names) == 1 && vs.Names[0].Name == name && len(vs.Values) == 1 {
					if lit, ok := vs.Values[0].(*ast.CompositeLit); ok {
						return lit
					}
				}
			}
		}
		log.Fatalf("asm7.go: no var %s", name)
		return nil
	}

	// optab, in source order, then sorted as buildop does.
	var opt []optabEntry
	for _, e := range varLit("optab").Elts {
		lit, ok := e.(*ast.CompositeLit)
		if !ok || len(lit.Elts) != 11 {
			log.Fatalf("%s: optab entry is not an 11-field literal", pos(e))
		}
		for _, x := range lit.Elts {
			if _, kv := x.(*ast.KeyValueExpr); kv {
				log.Fatalf("%s: keyed optab entry", pos(x))
			}
		}
		v := func(i int) int64 { return val(lit.Elts[i]) }
		opt = append(opt, optabEntry{as: v(0), a1: uint8(v(1)), a2: uint8(v(2)), a3: uint8(v(3)),
			a4: uint8(v(4)), a5: uint8(v(5)), type_: int8(v(6)), size_: int8(v(7)),
			param: int16(v(8)), flag: int8(v(9)), scond: uint8(v(10)), line: pos(e).Line})
	}
	slices.SortFunc(opt, ocmp)

	// oprange: buildop's loop over the sorted table and its switch, interpreted.
	var sw *ast.SwitchStmt
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Name.Name != "buildop" {
			continue
		}
		ast.Inspect(fd.Body, func(n ast.Node) bool {
			if s, ok := n.(*ast.SwitchStmt); ok {
				if id, ok := s.Tag.(*ast.Ident); ok && id.Name == "as" {
					sw = s
				}
			}
			return sw == nil
		})
	}
	if sw == nil {
		log.Fatal("asm7.go: no `switch as` in buildop")
	}
	mapKeys := func(name string) []int64 {
		var ks []int64
		for _, e := range varLit(name).Elts {
			ks = append(ks, val(e.(*ast.KeyValueExpr).Key))
		}
		return ks
	}
	type rng struct{ start, stop int }
	oprange := map[int64]rng{}
	clauses := sw.Body.List
	clauseOf := func(as int64) int {
		def := -1
		for i, s := range clauses {
			cc := s.(*ast.CaseClause)
			if cc.List == nil {
				def = i
			}
			for _, e := range cc.List {
				if constOf(e) == as {
					return i
				}
			}
		}
		return def
	}
	isOprangeset := func(s ast.Stmt) (ast.Expr, bool) {
		es, ok := s.(*ast.ExprStmt)
		if !ok {
			return nil, false
		}
		call, ok := es.X.(*ast.CallExpr)
		if !ok || len(call.Args) != 2 {
			return nil, false
		}
		if fn, ok := call.Fun.(*ast.Ident); !ok || fn.Name != "oprangeset" {
			return nil, false
		}
		if t, ok := call.Args[1].(*ast.Ident); !ok || t.Name != "t" {
			log.Fatalf("%s: oprangeset with a range other than t", pos(s))
		}
		return call.Args[0], true
	}
	for i := 0; i < len(opt); i++ {
		as, start := opt[i].as, i
		for ; i < len(opt)-1; i++ {
			if opt[i+1].as != as {
				break
			}
		}
		r := rng{start, i + 1}
		oprange[as] = r
		k := clauseOf(as)
		cc := clauses[k].(*ast.CaseClause)
		if cc.List == nil {
			log.Fatalf("buildop: opcode %s reaches the default case", tab.name(constant.MakeInt64(as)))
		}
	body:
		for {
			for _, s := range cc.Body {
				if x, ok := isOprangeset(s); ok {
					oprange[constOf(x)] = r
					continue
				}
				switch s := s.(type) {
				case *ast.BranchStmt:
					switch s.Tok {
					case token.BREAK:
						break body
					case token.FALLTHROUGH:
						k++
						cc = clauses[k].(*ast.CaseClause)
						continue body
					}
					log.Fatalf("%s: unexpected %s", pos(s), s.Tok)
				case *ast.RangeStmt:
					// for i := range m { [if i == K { continue }] oprangeset(i, t) }
					key, ok1 := s.Key.(*ast.Ident)
					m, ok2 := s.X.(*ast.Ident)
					if !ok1 || !ok2 || s.Value != nil {
						log.Fatalf("%s: unexpected range loop", pos(s))
					}
					skip := map[int64]bool{}
					var set bool
					for _, b := range s.Body.List {
						if x, ok := isOprangeset(b); ok {
							if id, ok := x.(*ast.Ident); !ok || id.Name != key.Name {
								log.Fatalf("%s: unexpected oprangeset in range loop", pos(b))
							}
							set = true
							continue
						}
						is, ok := b.(*ast.IfStmt)
						if !ok || is.Init != nil || is.Else != nil || len(is.Body.List) != 1 {
							log.Fatalf("%s: unexpected statement in range loop", pos(b))
						}
						if br, ok := is.Body.List[0].(*ast.BranchStmt); !ok || br.Tok != token.CONTINUE || set {
							log.Fatalf("%s: unexpected if in range loop", pos(b))
						}
						be, ok := is.Cond.(*ast.BinaryExpr)
						if !ok || be.Op != token.EQL {
							log.Fatalf("%s: unexpected condition", pos(b))
						}
						if id, ok := be.X.(*ast.Ident); !ok || id.Name != key.Name {
							log.Fatalf("%s: unexpected condition", pos(b))
						}
						skip[constOf(be.Y)] = true
					}
					if !set {
						log.Fatalf("%s: range loop without oprangeset", pos(s))
					}
					for _, k := range mapKeys(m.Name) {
						if !skip[k] {
							oprange[k] = r
						}
					}
				default:
					log.Fatalf("%s: unexpected statement %T in buildop's switch", pos(s), s)
				}
			}
			break
		}
	}

	var b bytes.Buffer
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("-- Generated by tools/asgen (scripts/gen-asm.sh) from Go %s\n", source)
	p("-- src/cmd/internal/obj/arm64/asm7.go, values by go/types. DO NOT EDIT.\n")
	p("import GoFV.Asm.As\nimport GoFV.Asm.Reg\n\n")
	p("/-! # arm64 assembler tables (`asm7.go`)\n\n")
	p("- every integer constant of `asm7.go` (`funcAlign`, `S64`, the `Optab.flag` bits `LFROM` …);\n")
	p("- `optab` in the order `buildop` leaves it: the source table sorted by `slices.SortFunc`\n")
	p("  with `ocmp` (pdqsort, not stable; the generator checks that its `slices` sort is the pinned\n")
	p("  tree's and sorts with it), so `Prog.Optab = k` is `optab[k - 1]`;\n")
	p("- `oprange`: the `[start, stop)` slice of `optab` that `buildop` assigns to an opcode\n")
	p("  (`oprange[as & obj.AMask]`), from its loop over the sorted table and its `switch`\n")
	p("  (`oprangeset` aliases, the range loops over `atomicLDADD`/`atomicSWP`);\n")
	p("- `atomicLDADD`, `atomicSWP`, `atomicCASP`: the opcode maps of the LSE atomics;\n")
	p("- `rprfopfield`, `prfopfield`, `sysInstFields`, `pstatefield`: the special-operand tables. -/\n\n")
	p("namespace GoFV.Asm.ARM64\n")
	blocks := l.constBlocks(pkg, "asm7.go", func([]string, string) bool { return true })
	for _, block := range blocks {
		p("\n-- asm7.go:%d\n", block[0].line)
		for _, c := range block {
			if regNames[c.name] {
				log.Fatalf("asm7.go: constant %s also in a.out.go", c.name)
			}
			p("def %s : Int := %s\n", leanName(c.name), c.val.ExactString())
		}
	}
	p("\n/-- `arm64.Optab`. Operand classes are `C_*` values; `type_` is the `asmout` case. -/\n")
	p("structure Optab where\n  as : As\n  a1 : Nat\n  a2 : Nat\n  a3 : Nat\n  a4 : Nat\n  a5 : Nat\n")
	p("  type_ : Int\n  size_ : Int\n  param : Int\n  flag : Int\n  scond : Nat\n")
	p("  deriving DecidableEq, Inhabited, Repr\n\n")
	p("/-- `optab` after `buildop`'s sort (%d entries; the comment is the source line). -/\n", len(opt))
	p("def optab : Array Optab := #[\n")
	for i, o := range opt {
		sep := ","
		if i == len(opt)-1 {
			sep = "]"
		}
		p("  ⟨.%s, %d, %d, %d, %d, %d, %d, %d, %d, %d, %d⟩%s -- %d: asm7.go:%d\n",
			tab.name(constant.MakeInt64(o.as)), o.a1, o.a2, o.a3, o.a4, o.a5, o.type_, o.size_,
			o.param, o.flag, o.scond, sep, i+1, o.line)
	}
	p("\n/-- `oprange[as]`: the `[start, stop)` indices of `optab` `oplook` searches (`none`: the\n")
	p("opcode has no entries, `oplook` reports an illegal combination). -/\n")
	p("def oprange : As → Option (Nat × Nat)\n")
	type kv struct {
		name string
		r    rng
	}
	var rs []kv
	for as, r := range oprange {
		rs = append(rs, kv{tab.name(constant.MakeInt64(as)), r})
	}
	sort.Slice(rs, func(i, j int) bool { return rs[i].name < rs[j].name })
	for _, x := range rs {
		p("  | .%s => some (%d, %d)\n", x.name, x.r.start, x.r.stop)
	}
	p("  | _ => none\n")
	for _, m := range []string{"atomicLDADD", "atomicSWP", "atomicCASP"} {
		p("\n/-- `%s`. -/\ndef %s : As → Option UInt32\n", m, m)
		type ent struct {
			name string
			v    int64
		}
		var es []ent
		for _, e := range varLit(m).Elts {
			kv := e.(*ast.KeyValueExpr)
			es = append(es, ent{tab.name(constant.MakeInt64(val(kv.Key))), val(kv.Value)})
		}
		sort.Slice(es, func(i, j int) bool { return es[i].name < es[j].name })
		for _, e := range es {
			p("  | .%s => some 0x%s\n", e.name, strconv.FormatInt(e.v, 16))
		}
		p("  | _ => none\n")
	}
	// Operand tables of asm7.go keyed by SpecialOperand (map literals; emitted sorted by key).
	keyName := func(e ast.Expr) string {
		id, ok := e.(*ast.Ident)
		if !ok || !regNames[id.Name] {
			log.Fatalf("%s: key is not an a.out.go constant", pos(e))
		}
		return id.Name
	}
	type kent struct {
		key  int64
		name string
		lit  ast.Expr
	}
	mapEnts := func(name string) []kent {
		var es []kent
		for _, e := range varLit(name).Elts {
			kv := e.(*ast.KeyValueExpr)
			es = append(es, kent{val(kv.Key), keyName(kv.Key), kv.Value})
		}
		sort.Slice(es, func(i, j int) bool { return es[i].key < es[j].key })
		return es
	}
	for _, m := range []string{"rprfopfield", "prfopfield"} {
		p("\n/-- `%s` (`SpecialOperand` → field). -/\ndef %s (s : Int) : Option UInt32 :=\n  [", m, m)
		for i, e := range mapEnts(m) {
			if i > 0 {
				p(",\n   ")
			}
			p("(%s, %d)", e.name, val(e.lit))
		}
		p("].lookup s\n")
	}
	p("\n/-- An entry of `sysInstFields`. -/\nstructure SysInstField where\n")
	p("  op1 : Nat\n  cn : Nat\n  cm : Nat\n  op2 : Nat\n  hasOperand2 : Bool\n")
	p("\n/-- `sysInstFields`: the `SYS` form of the `TLBI` and `DC` operands. -/\n")
	p("def sysInstFields (s : Int) : Option SysInstField :=\n  ([")
	boolOf := func(e ast.Expr) string {
		tv := info.Types[e]
		if tv.Value == nil || tv.Value.Kind() != constant.Bool {
			log.Fatalf("%s: not a constant bool", pos(e))
		}
		return strconv.FormatBool(constant.BoolVal(tv.Value))
	}
	for i, e := range mapEnts("sysInstFields") {
		lit, ok := e.lit.(*ast.CompositeLit)
		if !ok || len(lit.Elts) != 5 {
			log.Fatalf("%s: sysInstFields entry is not a 5-field literal", pos(e.lit))
		}
		if i > 0 {
			p(",\n    ")
		}
		p("(%s, ⟨%d, %d, %d, %d, %s⟩)", e.name, val(lit.Elts[0]), val(lit.Elts[1]), val(lit.Elts[2]),
			val(lit.Elts[3]), boolOf(lit.Elts[4]))
	}
	p("] : List (Int × SysInstField)).lookup s\n")
	p("\n/-- `pstatefield`: `(opd, enc)` in source order. -/\ndef pstatefield : Array (Int × UInt32) := #[")
	for i, e := range varLit("pstatefield").Elts {
		lit := e.(*ast.CompositeLit)
		if i > 0 {
			p(", ")
		}
		p("(%s, %d)", keyName(lit.Elts[0]), val(lit.Elts[1]))
	}
	p("]\n")
	p("\n/-! Spot values (checked by the interpreter: kernel reduction of the table is too deep). -/\n\n")
	for _, w := range optabWitnesses {
		p("#guard %s\n", w)
	}
	p("\nend GoFV.Asm.ARM64\n")
	return b.Bytes()
}

// objWitnesses are spot values Lean checks (expected values from the Go declarations).
var objWitnesses = []struct{ name, val string }{
	{"AttrDuplicateOK", "1"}, {"AttrNoSplit", "4"}, {"AttrLeaf", "8"}, {"AttrNoFrame", "64"},
	{"AttrNeedCtxt", "32"}, {"ABIInternal", "1"}, {"AMask", "2047"}, {"Destination", "1"},
	{"R_ADDR", "1"}, {"R_WEAK", "-32768"},
}

// genObj generates ObjConst.lean: the integer constants of cmd/internal/obj link.go except
// the portable opcode block (As.lean), and the relocation types of cmd/internal/objabi
// reloctype.go with relocTypeNum (RelocType.String() name → value).
func genObj(l *loader, source string) []byte {
	const pkg = "cmd/internal/obj"
	names := map[string]bool{}
	var b bytes.Buffer
	p := func(format string, args ...any) { fmt.Fprintf(&b, format, args...) }
	p("-- Generated by tools/asgen (scripts/gen-asm.sh) from Go %s\n", source)
	p("-- src/cmd/internal/obj/link.go, src/cmd/internal/objabi/reloctype.go, values by go/types. DO NOT EDIT.\n\n")
	p("/-! # `cmd/internal/obj` constants\n\n")
	p("The integer constants of the `const` declarations of `cmd/internal/obj/link.go` (symbol\n")
	p("attributes `Attr*`, ABIs, `TYPE_*`/`NAME_*`, operand positions, `AMask`, …; the source line is\n")
	p("noted above each declaration) except the portable opcode block (`GoFV.Asm.As`). Go names\n")
	p("verbatim, values computed by `go/types`; and the relocation types `R_*` of\n")
	p("`cmd/internal/objabi/reloctype.go` with `relocTypeNum`. -/\n\n")
	p("namespace GoFV.Asm.Obj\n")
	blocks := l.constBlocks(pkg, "link.go", func(block []string, n string) bool {
		return block[0] != "AXXX"
	})
	for _, block := range blocks {
		p("\n-- link.go:%d\n", block[0].line)
		for _, c := range block {
			if names[c.name] {
				log.Fatalf("obj: duplicate constant %s", c.name)
			}
			names[c.name] = true
			p("def %s : Int := %s\n", leanName(c.name), c.val.ExactString())
		}
	}
	relocs := l.constBlocks("cmd/internal/objabi", "reloctype.go", func([]string, string) bool { return true })
	var rnames []string
	for _, block := range relocs {
		p("\n-- objabi/reloctype.go:%d\n", block[0].line)
		for _, c := range block {
			if names[c.name] {
				log.Fatalf("obj: duplicate constant %s", c.name)
			}
			names[c.name] = true
			rnames = append(rnames, c.name)
			p("def %s : Int := %s\n", leanName(c.name), c.val.ExactString())
		}
	}
	p("\n/-- The `objabi.RelocType` named `s` (`RelocType.String()`: the constant's name). -/\n")
	p("def relocTypeNum : String → Option Int\n")
	for _, n := range rnames {
		p("  | %q => some %s\n", n, leanName(n))
	}
	p("  | _ => none\n")
	p("\n/-! Spot values. -/\n\n")
	for _, w := range objWitnesses {
		if !names[w.name] {
			log.Fatalf("obj: witness %s not emitted", w.name)
		}
		p("example : %s = %s := rfl\n", w.name, w.val)
	}
	p("\nend GoFV.Asm.Obj\n")
	return b.Bytes()
}
