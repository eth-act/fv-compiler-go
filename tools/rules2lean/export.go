//go:build rules2lean

// rules2lean exporter. This file is not built on its own: tools/rules2lean (main.go) adds it to
// the pinned rulegen package (third_party/go/src/cmd/compile/internal/ssa/_gen) with
// `go run -overlay`, so the export uses rulegen's own parser (Rule.parse, expandOr, parseValue,
// extract, split, splitNameExpr, varCount, typeName, ...), op tables (genericOps, blocks) and
// code generator (genMatch, genResult, genBlockRewrite, used as a cross-check) unchanged.
// The rule-file reading loop of genRulesSuffix is copied below (loadRules) because it is not
// a separate function in rulegen.go (Copyright 2015 The Go Authors, BSD licence).
//
// Every Go expression of a rule (conditions, auxint/aux/type expressions on both sides, code
// results) is type-checked with go/types inside a synthetic file added to the pinned
// cmd/compile/internal/ssa package, and exported with its Go type on every node.
//
// Output: Lean modules under $GOFV_OUT (GoFV/Rules/Generated) and a Markdown helper inventory
// at $GOFV_INVENTORY. See docs/contracts/rules.md.

package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/build"
	"go/constant"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"io/fs"
	"log"
	"math"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"time"
)

func init() {
	// Runs after every other init of the rulegen package (file name zz_*), i.e. after the
	// op tables are complete; never returns.
	rules2leanMain()
	os.Exit(0)
}

// ruleFile is a rule file `_gen/<arch><suffix>.rules`, rewritten by rewriteValue<arch><suffix>.
type ruleFile struct{ arch, suffix string }

func (f ruleFile) name() string { return f.arch + f.suffix }

// ruleFiles are the rule sets exported: the machine-independent ones (Phase 1) and the arm64
// lowering rules ("lower", "late lower").
var ruleFiles = []ruleFile{{"generic", ""}, {"dec", ""}, {"divisible", ""}, {"divmod", ""}, {"ARM64", ""}, {"ARM64", "latelower"}}

// simdOps are the SIMD ops (Go constant names without "Op"; GOEXPERIMENT=simd only, left out of
// GoFV.SSA.Op by tools/opsgen): the generic SIMD ops and those of simdARM64ops.go. The rules
// of simdARM64.rules, which rulegen appends to ARM64.rules, all start at one of them and are
// not exported (loadRules).
var simdOps = func() map[string]bool {
	m := map[string]bool{}
	for _, o := range simdGenericOps() {
		m[o.name] = true
	}
	var r regInfo
	for _, o := range simdARM64Ops(r, r, r, r, r, r) {
		m["ARM64"+o.name] = true
	}
	return m
}()

// ---------------------------------------------------------------------------------------
// Export model

type xVar struct {
	Name string
	Kind string // value | type | auxInt | aux
	Decl string // Go source of the synthetic declaration's right-hand side
	Ty   types.Type
}

// slot is a Go expression of a rule, type-checked in a synthetic statement.
type slot struct {
	Src  string // expression source as written in the rule
	Stmt string // synthetic statement, with %s for the (parenthesised) expression
	Ex   func(ast.Stmt) ast.Expr
	Expr ast.Expr // after type-checking
	Role string   // cond | matchAuxInt | matchAux | matchType | resType | resAuxInt | resAux | copy | block
}

type xField struct {
	Kind string // any | bind | eq
	Var  int
	E    *slot
}

type xPat struct {
	Kind    string // wild | bind | same | op
	Var     int
	Op      string
	Name    int // -1 if none
	Ty      xField
	AuxInt  xField
	Aux     xField
	Args    []*xPat
	Arity   string // fixed | exact | atLeast | ellipsis
	ArityN  int
	Commute bool
}

type xRArg struct {
	Kind string // var | node | expr
	N    int
	E    *slot // expr: a Go expression of type *Value (`flagArg(x)`), evaluated at AddArg time
}

type xNode struct {
	Op     string
	Ty     *slot // nil: keep v.Type (top node of an in-place rewrite without <type>)
	AuxInt *slot
	Aux    *slot
	Args   []xRArg
}

type xResult struct {
	Kind  string // copy | build | setOp
	Copy  *slot
	Nodes []*xNode
	SetOp string
}

type xRule struct {
	Arch    *arch
	File    string
	Line    int
	LeanId  string
	Text    string
	Block   bool
	Op      string // value op or block kind (Go name, no prefix)
	Vars    []*xVar
	varIdx  map[string]int
	Pat     *xPat   // value rules
	Ctrls   []*xPat // block rules: one pattern per control (op node or bind)
	BAuxInt xField  // block rules
	BAux    xField
	Cond    *slot
	Move    *slot
	Result  xResult
	Pos     []int // value rules: pattern path of the value whose Pos new values get
	// block rules
	NewKind    string
	NewCtrls   [][]*xNode // per new control: nodes (preorder), empty if a variable
	NewCtrlVar []int      // per new control: variable index if a plain variable, else -1
	NewCtrlPos []string   // per new control: "ctrl:i:<path>" / "block"
	NewAuxInt  *slot
	NewAux     *slot
	Swap       bool
	slots      []*slot
	fnName     string
	// cross-check data
	declNames []string
	allocOps  []string
	posVar    string   // value rules: Go variable whose Pos new values get ("" = v)
	allocPos  []string // Go position expression of each NewValue0, in order
	rawKind   string   // block rules: the kind as written in the rule file ("EQ")
}

func (r *xRule) newSlot(role, src, stmt string, ex func(ast.Stmt) ast.Expr) *slot {
	s := &slot{Src: src, Stmt: stmt, Ex: ex, Role: role}
	r.slots = append(r.slots, s)
	return s
}

func (r *xRule) addVar(name, kind, decl string) int {
	if _, ok := r.varIdx[name]; ok {
		log.Fatalf("%s: variable %s bound twice", r.loc(), name)
	}
	r.varIdx[name] = len(r.Vars)
	r.Vars = append(r.Vars, &xVar{Name: name, Kind: kind, Decl: decl})
	return len(r.Vars) - 1
}

func (r *xRule) loc() string { return fmt.Sprintf("%s.rules:%d", r.File, r.Line) }

// ---------------------------------------------------------------------------------------
// Reading rule files (copied from genRulesSuffix in rulegen.go).

type locRule struct {
	Rule
	file string
	line int
}

// loadRules reads _gen/<arch><suffix>.rules (and, as rulegen does for suffix "", the arch's
// simd<arch>.rules). The rules of the SIMD file are dropped after checking that each starts at
// a SIMD op (simdOps) and that no other rule does; simdSkipped returns the ops (Go constant
// names) whose rewrite functions rulegen generated for them only.
func loadRules(a arch, suffix string) (ops []string, oprules map[string][]locRule, blocks []string, blockrules map[string][]locRule, simdSkipped map[string]bool) {
	var readers []NamedReader
	name := a.name + suffix + ".rules"
	text, err := os.Open(name)
	if err != nil {
		log.Fatalf("can't read rule file: %v", err)
	}
	readers = append(readers, NamedReader{name, text})
	simdname := "simd" + a.name + ".rules"
	if suffix == "" {
		if simdtext, err := os.Open(simdname); err == nil {
			readers = append(readers, NamedReader{simdname, simdtext})
		}
	}
	simdSkipped = map[string]bool{}
	blockrules = map[string][]locRule{}
	oprules = map[string][]locRule{}
	scanner := MultiScannerFromReaders(readers)
	rule := ""
	var lineno int
	var ruleLineno int
	for scanner.Scan() {
		lineno = scanner.Line()
		line := scanner.Text()
		if i := strings.Index(line, "//"); i >= 0 {
			line = line[:i]
		}
		rule += " " + line
		rule = strings.TrimSpace(rule)
		if rule == "" {
			continue
		}
		if !strings.Contains(rule, "=>") {
			continue
		}
		if ruleLineno == 0 {
			ruleLineno = lineno
		}
		if strings.HasSuffix(rule, "=>") {
			continue
		}
		if n := balance(rule); n > 0 {
			continue
		} else if n < 0 {
			break
		}
		loc := fmt.Sprintf("%s:%d", scanner.Name(), ruleLineno)
		file := strings.TrimSuffix(scanner.Name(), ".rules")
		for _, rule2 := range expandOr(rule) {
			r := locRule{Rule{Rule: rule2, Loc: loc}, file, ruleLineno}
			rawop := strings.Split(rule2, " ")[0][1:]
			if isBlock(rawop, a) {
				if scanner.Name() == simdname {
					log.Fatalf("%s: block rule in %s", loc, simdname)
				}
				blockrules[rawop] = append(blockrules[rawop], r)
				continue
			}
			match, _, _ := r.parse()
			op, oparch, _, _, _, _ := parseValue(match, a, loc)
			opname := fmt.Sprintf("Op%s%s", oparch, op.name)
			if isSimd := simdOps[oparch+op.name]; isSimd != (scanner.Name() == simdname) {
				log.Fatalf("%s: rule for op %s (SIMD: %v) in %s", loc, opname, isSimd, scanner.Name())
			} else if isSimd {
				simdSkipped[opname] = true
				continue
			}
			oprules[opname] = append(oprules[opname], r)
		}
		rule = ""
		ruleLineno = 0
	}
	if err := scanner.Err(); err != nil {
		log.Fatalf("scanner failed: %v\n", err)
	}
	if balance(rule) != 0 {
		log.Fatalf("%s:%d: unbalanced rule: %v\n", scanner.Name(), lineno, rule)
	}
	for op := range oprules {
		ops = append(ops, op)
	}
	sort.Strings(ops)
	for op := range blockrules {
		blocks = append(blocks, op)
	}
	sort.Strings(blocks)
	return
}

// ---------------------------------------------------------------------------------------
// Match side: a mirror of genMatch0 that builds a pattern tree instead of Go statements. It
// keeps rulegen's declaration order exactly (that order decides bind vs. compare, and so each
// variable's Go type); crossCheck compares it with the real genMatch output.

type matcher struct {
	r        *xRule
	a        arch
	declared map[string]bool
	decls    []string // Declare names in rulegen order (incl. synthetic v_0 ...)
	cnt      map[string]int
	block    bool // block rule: value expressions are b.Controls[i]
}

func (m *matcher) isDeclared(name string) bool {
	if predeclared[name] {
		return true
	}
	return m.declared[name]
}

func (m *matcher) declare(name string) {
	m.declared[name] = true
	m.decls = append(m.decls, name)
}

// field handles a <type>, [auxint] or {aux} restriction of an op node whose Go value
// expression is gv.
func (m *matcher) field(name, field, dclType, gv string) xField {
	if name == "" {
		return xField{Kind: "any"}
	}
	if dclType == "" || dclType == "invalid" {
		log.Fatalf("%s: op has no declared type for %s", m.r.loc(), field)
	}
	var conv string
	switch field {
	case "Aux":
		conv = fmt.Sprintf("auxTo%s(%%s.Aux)", title(dclType))
	case "AuxInt":
		conv = fmt.Sprintf("auxIntTo%s(%%s.AuxInt)", title(dclType))
	case "Type":
		conv = "%s.Type"
	}
	if !token.IsIdentifier(name) || m.isDeclared(name) {
		ex := func(s ast.Stmt) ast.Expr { return s.(*ast.AssignStmt).Rhs[0].(*ast.BinaryExpr).Y }
		role := map[string]string{"Aux": "matchAux", "AuxInt": "matchAuxInt", "Type": "matchType"}[field]
		return xField{Kind: "eq", E: m.r.newSlot(role, name, "_ = "+fmt.Sprintf(conv, m.valueDecl())+" != (%s)", ex)}
	}
	m.declare(name)
	if name == "_" {
		// rulegen declares "_ := ..." and its unused-variable pass deletes it: no constraint.
		return xField{Kind: "any"}
	}
	kind := map[string]string{"Aux": "aux", "AuxInt": "auxInt", "Type": "type"}[field]
	return xField{Kind: "bind", Var: m.r.addVar(name, kind, fmt.Sprintf(conv, m.valueDecl()))}
}

// gen mirrors genMatch0(rr, arch, match, v, cnt, pregenTop). gv is the Go variable name of the
// value (v, v_0, x, ...), path its pattern path, valExpr a Go expression of type *Value usable
// in synthetic declarations. It returns the pattern node, the pos variable ("" if none) and
// the position path.
func (m *matcher) gen(match, gv string, path []int, pregenTop bool) (*xPat, string, []int) {
	if match[0] != '(' || match[len(match)-1] != ')' {
		log.Fatalf("%s: non-compound expr in genMatch0: %q", m.r.loc(), match)
	}
	op, oparch, typ, auxint, aux, args := parseValue(match, m.a, m.r.loc())
	p := &xPat{Kind: "op", Op: leanOp(m.r, oparch, op.name), Name: -1, Arity: "fixed"}
	var pos string
	var posPath []int
	if op.faultOnNilArg0 || op.faultOnNilArg1 {
		pos, posPath = gv, path
	}
	if len(args) == 1 && args[0] == "..." {
		p.Arity = "ellipsis"
		args = nil
	} else if op.argLength == -1 {
		l := len(args)
		if l == 0 || args[l-1] != "___" {
			p.Arity, p.ArityN = "exact", l
		} else if l > 1 && args[l-1] == "___" {
			p.Arity, p.ArityN = "atLeast", l-1
		} else {
			p.Arity, p.ArityN = "atLeast", 0
		}
	} else if len(args) > 0 && args[len(args)-1] == "___" {
		p.Arity, p.ArityN = "atLeast", len(args)-1
	}
	p.Ty = m.field(typ, "Type", "*types.Type", gv)
	p.AuxInt = m.field(auxint, "AuxInt", op.auxIntType(), gv)
	p.Aux = m.field(aux, "Aux", op.auxType(), gv)

	commutative := op.commutative
	if commutative {
		if args[0] == args[1] {
			commutative = false
		}
		if m.cnt[args[0]] == 1 && m.cnt[args[1]] == 1 {
			commutative = false
		}
	}
	p.Commute = commutative
	p.Args = make([]*xPat, len(args))
	// The last argument may be declared first (rulegen: "access last argument first").
	n0 := len(args)
	for i, a := range args {
		if a == "_" {
			p.Args[i] = &xPat{Kind: "wild", Name: -1}
		}
	}
	if !pregenTop {
		for n := len(args) - 1; n > 0; n-- {
			a := args[n]
			if a == "_" {
				continue
			}
			if !m.isDeclared(a) && token.IsIdentifier(a) && !(commutative && len(args) == 2) {
				m.declare(a)
				if a != "___" {
					p.Args[n] = m.leafBind(a)
				}
				n0 = n
			}
			break
		}
	}
	if commutative && !pregenTop {
		for i := 0; i <= 1; i++ {
			m.declare(fmt.Sprintf("%s_%d", gv, i))
		}
	}
	for i, arg := range args[:n0] {
		if arg == "_" {
			p.Args[i] = &xPat{Kind: "wild", Name: -1}
			continue
		}
		var rhs string
		if (commutative && i < 2) || pregenTop {
			rhs = fmt.Sprintf("%s_%d", gv, i)
		} else {
			rhs = fmt.Sprintf("%s.Args[%d]", gv, i)
		}
		if !strings.Contains(arg, "(") {
			if !token.IsIdentifier(arg) {
				log.Fatalf("%s: non-identifier leaf %q", m.r.loc(), arg)
			}
			if arg == "___" {
				// rulegen declares "___ := ..." and its unused-variable pass deletes it.
				if i != len(args)-1 {
					log.Fatalf("%s: ___ not last", m.r.loc())
				}
				if arg != rhs {
					m.declare(arg)
				}
				continue
			}
			if m.isDeclared(arg) {
				v, ok := m.r.varIdx[arg]
				if !ok {
					log.Fatalf("%s: comparison with non-rule name %s", m.r.loc(), arg)
				}
				p.Args[i] = &xPat{Kind: "same", Var: v, Name: -1}
			} else {
				if arg != rhs {
					m.declare(arg)
				}
				p.Args[i] = m.leafBind(arg)
			}
			continue
		}
		argname, expr := splitNameExpr(arg)
		named := argname != ""
		if argname == "" {
			argname = fmt.Sprintf("%s_%d", gv, i)
		}
		if argname != rhs {
			m.declare(argname)
		}
		sub, argPos, argPosPath := m.gen(expr, argname, append(append([]int{}, path...), i), false)
		if named {
			sub.Name = m.r.addVar(argname, "value", m.valueDecl())
		}
		p.Args[i] = sub
		if argPos != "" {
			pos, posPath = argPos, argPosPath
		}
	}
	if len(args) > 0 && args[len(args)-1] == "___" {
		p.Args = p.Args[:len(args)-1]
	}
	for _, a := range p.Args {
		if a == nil {
			log.Fatalf("%s: internal: missing pattern argument", m.r.loc())
		}
	}
	return p, pos, posPath
}

func (m *matcher) valueDecl() string {
	if m.block {
		return "b.Controls[0]"
	}
	return "v"
}

func (m *matcher) leafBind(name string) *xPat {
	return &xPat{Kind: "bind", Var: m.r.addVar(name, "value", m.valueDecl()), Name: -1}
}

// ---------------------------------------------------------------------------------------
// Result side: a mirror of genResult0 producing value nodes in allocation order.

type resulter struct {
	r        *xRule
	a        arch
	nodes    []*xNode
	allocs   []string
	allocPos []string       // Go position expression of each allocation (cross-check)
	pos      string         // position new values get (rulegen's pos/newpos)
	cse      map[string]int // nil: no sharing (block rules)
	block    bool
}

// leanOp is the GoFV.SSA.Op constructor of an op parseValue resolved: the Go constant without
// "Op" (arch prefix and name). SIMD ops have no constructor.
func leanOp(r *xRule, oparch, name string) string {
	if simdOps[oparch+name] {
		log.Fatalf("%s: SIMD op %s%s", r.loc(), oparch, name)
	}
	return oparch + name
}

func (g *resulter) ex(stmt string, f func(ast.Stmt) ast.Expr) (string, func(ast.Stmt) ast.Expr) {
	return stmt, f
}

func rhs0(s ast.Stmt) ast.Expr { return s.(*ast.AssignStmt).Rhs[0] }
func callArg(i int) func(ast.Stmt) ast.Expr {
	return func(s ast.Stmt) ast.Expr {
		var c *ast.CallExpr
		switch s := s.(type) {
		case *ast.AssignStmt:
			c = s.Rhs[0].(*ast.CallExpr)
		case *ast.ExprStmt:
			c = s.X.(*ast.CallExpr)
		}
		return c.Args[i]
	}
}

// gen mirrors genResult0(rr, arch, result, top, move, pos, cse) and returns the argument.
func (g *resulter) gen(result string, top, move bool) xRArg {
	resname, expr := splitNameExpr(result)
	result = expr
	if result[0] != '(' {
		if top {
			log.Fatalf("%s: internal: top variable handled by caller", g.r.loc())
		}
		if v, ok := g.r.varIdx[result]; ok {
			return xRArg{Kind: "var", N: v}
		}
		if token.IsIdentifier(result) {
			log.Fatalf("%s: result argument %q is not a rule variable", g.r.loc(), result)
		}
		// rulegen passes any other argument text through as a Go expression (AddArg(e)).
		return xRArg{Kind: "expr", E: g.r.newSlot("resArg", result, "v.AddArg((%s))", callArg(0))}
	}
	w := normalizeWhitespace(result)
	if g.cse != nil {
		if prev, ok := g.cse[w]; ok {
			return xRArg{Kind: "node", N: prev}
		}
	}
	if resname != "" {
		log.Fatalf("%s: named result node %s unsupported", g.r.loc(), resname)
	}
	op, oparch, typ, auxint, aux, args := parseValue(result, g.a, g.r.loc())
	lop := leanOp(g.r, oparch, op.name)
	typeOverride := typ != ""
	if typ == "" && op.typ != "" {
		typ = typeName(op.typ)
	}
	n := &xNode{Op: lop}
	idx := len(g.nodes)
	g.nodes = append(g.nodes, n)
	if top && !move {
		if typeOverride {
			n.Ty = g.r.newSlot("resType", typ, "v.Type = (%s)", rhs0)
		}
	} else {
		if typ == "" {
			log.Fatalf("%s: sub-expression %s must have a type", g.r.loc(), result)
		}
		pos := "v.Pos"
		if g.block {
			pos = "b.Pos"
		}
		n.Ty = g.r.newSlot("resType", typ, "_ = b.NewValue0("+pos+", OpInvalid, (%s))", callArg(2))
		g.allocs = append(g.allocs, lop)
		g.allocPos = append(g.allocPos, g.pos)
	}
	if auxint != "" {
		n.AuxInt = g.r.newSlot("resAuxInt", auxint, "_ = "+unTitle(op.auxIntType())+"ToAuxInt((%s))", callArg(0))
	}
	if aux != "" {
		n.Aux = g.r.newSlot("resAux", aux, "_ = "+unTitle(op.auxType())+"ToAux((%s))", callArg(0))
	}
	for _, arg := range args {
		n.Args = append(n.Args, g.gen(arg, false, move))
	}
	if g.cse != nil {
		g.cse[w] = idx
	}
	return xRArg{Kind: "node", N: idx}
}

// ---------------------------------------------------------------------------------------
// Building rules

var syntheticName = regexp.MustCompile(`^.+_[0-9]+$`)

func buildValueRule(a arch, lr locRule, op string) *xRule {
	r := &xRule{Arch: &a, File: lr.file, Line: lr.line, Text: normalizeSpaces(lr.Rule.Rule), Op: strings.TrimPrefix(op, "Op"), varIdx: map[string]int{}}
	match, cond, result := lr.parse()
	rr := &RuleRewrite{Loc: lr.Loc}
	rr.Match, rr.Cond, rr.Result = match, cond, result
	m := &matcher{r: r, a: a, declared: map[string]bool{}, cnt: varCount(rr)}
	argLen := opByName(a, op).argLength
	pat, pos, posPath := m.gen(match, "v", nil, argLen >= 0)
	r.posVar = pos
	r.Pat = pat
	r.Pos = posPath
	r.declNames = m.decls
	if cond != "" {
		r.Cond = r.newSlot("cond", cond, "_ = (%s)", rhs0)
	}
	res := result
	move := res[0] == '@'
	if move {
		s := strings.SplitN(res[1:], " ", 2)
		r.Move = r.newSlot("block", s[0], "b = (%s)", rhs0)
		res = s[1]
	}
	g := &resulter{r: r, a: a, cse: map[string]int{}, pos: "v.Pos"}
	if pos != "" {
		g.pos = pos + ".Pos"
	}
	switch {
	case res[0] == '{':
		r.Result = xResult{Kind: "copy", Copy: r.newSlot("copy", res[1:len(res)-1], "v.copyOf((%s))", callArg(0))}
	case res[0] != '(':
		_, expr := splitNameExpr(res)
		r.Result = xResult{Kind: "copy", Copy: r.newSlot("copy", expr, "v.copyOf((%s))", callArg(0))}
	default:
		g.gen(res, true, move)
		r.Result = xResult{Kind: "build", Nodes: g.nodes}
	}
	r.allocOps, r.allocPos = g.allocs, g.allocPos
	return r
}

func buildEllipsisRule(a arch, lr locRule, op, eop string) *xRule {
	r := &xRule{Arch: &a, File: lr.file, Line: lr.line, Text: normalizeSpaces(lr.Rule.Rule), Op: strings.TrimPrefix(op, "Op"), varIdx: map[string]int{}}
	r.Pat = &xPat{Kind: "op", Op: r.Op, Name: -1, Arity: "ellipsis", Ty: xField{Kind: "any"}, AuxInt: xField{Kind: "any"}, Aux: xField{Kind: "any"}}
	r.Result = xResult{Kind: "setOp", SetOp: strings.TrimPrefix(eop, "Op")}
	return r
}

// leanBlock is the GoFV.SSA.BlockKind constructor of a block kind of a rule (rulegen's
// getBlockInfo name without "Block": "If", "ARM64EQ").
func leanBlock(kind string, a arch) string {
	name, _ := getBlockInfo(kind, a)
	return strings.TrimPrefix(name, "Block")
}

func buildBlockRule(a arch, lr locRule, kind string) *xRule {
	r := &xRule{Arch: &a, File: lr.file, Line: lr.line, Text: normalizeSpaces(lr.Rule.Rule), Op: leanBlock(kind, a), rawKind: kind, Block: true, varIdx: map[string]int{}}
	_, data := getBlockInfo(kind, a)
	match, cond, result := lr.parse()
	_, _, auxint, aux, s := extract(match)
	if len(s) < data.controls {
		log.Fatalf("%s: too few controls", r.loc())
	}
	m := &matcher{r: r, a: a, declared: map[string]bool{}, cnt: nil, block: true}
	pos := make([]string, data.controls)
	goPos := make([]string, data.controls) // rulegen's pos[i]
	for i, arg := range s[:data.controls] {
		if strings.Contains(arg, "(") {
			vname, expr := splitNameExpr(arg)
			named := vname != ""
			if vname == "" {
				vname = fmt.Sprintf("v_%v", i)
			}
			m.declare(vname)
			p, pv, pp := m.gen(expr, vname, []int{i}, false)
			if named {
				p.Name = r.addVar(vname, "value", "b.Controls[0]")
			}
			r.Ctrls = append(r.Ctrls, p)
			if pp != nil {
				pos[i] = "ctrl:" + pathString(pp)
			} else {
				pos[i] = "ctrl:" + pathString([]int{i})
			}
			goPos[i] = vname + ".Pos"
			if pv != "" {
				goPos[i] = pv + ".Pos"
			}
		} else {
			m.declare(arg)
			r.Ctrls = append(r.Ctrls, m.leafBind(arg))
			pos[i] = "ctrl:" + pathString([]int{i})
			goPos[i] = arg + ".Pos"
		}
	}
	r.BAuxInt = blockField(m, auxint, "AuxInt", data.auxIntType())
	r.BAux = blockField(m, aux, "Aux", data.auxType())
	r.declNames = m.decls
	if cond != "" {
		r.Cond = r.newSlot("cond", cond, "_ = (%s)", rhs0)
	}
	outop, _, oauxint, oaux, t := extract(result)
	_, outdata := getBlockInfo(outop, a)
	r.NewKind = leanBlock(outop, a)
	if len(t) < outdata.controls {
		log.Fatalf("%s: too few result controls", r.loc())
	}
	succs := s[data.controls:]
	newsuccs := t[outdata.controls:]
	g := &resulter{r: r, a: a, cse: nil, block: true}
	for i, control := range t[:outdata.controls] {
		newpos := "block"
		g.pos = "b.Pos"
		if i < len(pos) && pos[i] != "" {
			newpos = pos[i]
			g.pos = goPos[i]
		}
		start := len(g.nodes)
		if control[0] != '(' {
			_, e := splitNameExpr(control)
			v, ok := r.varIdx[e]
			if !ok {
				log.Fatalf("%s: control %q is not a variable", r.loc(), control)
			}
			r.NewCtrlVar = append(r.NewCtrlVar, v)
			r.NewCtrls = append(r.NewCtrls, nil)
		} else {
			g.gen(control, false, false)
			r.NewCtrlVar = append(r.NewCtrlVar, -1)
			r.NewCtrls = append(r.NewCtrls, g.nodes[start:])
		}
		r.NewCtrlPos = append(r.NewCtrlPos, newpos)
	}
	if oauxint != "" {
		r.NewAuxInt = r.newSlot("resAuxInt", oauxint, "_ = "+unTitle(outdata.auxIntType())+"ToAuxInt((%s))", callArg(0))
	}
	if oaux != "" {
		r.NewAux = r.newSlot("resAux", oaux, "_ = "+unTitle(outdata.auxType())+"ToAux((%s))", callArg(0))
	}
	for i := range succs {
		if succs[i] != newsuccs[i] {
			r.Swap = true
		}
	}
	r.allocOps, r.allocPos = g.allocs, g.allocPos
	return r
}

func blockField(m *matcher, name, field, dclType string) xField {
	if name == "" {
		return xField{Kind: "any"}
	}
	conv := fmt.Sprintf("%sTo%s(b.%s)", unTitle(field), title(dclType), field)
	if !token.IsIdentifier(name) || m.isDeclared(name) {
		role := map[string]string{"Aux": "matchAux", "AuxInt": "matchAuxInt"}[field]
		return xField{Kind: "eq", E: m.r.newSlot(role, name, "_ = "+conv+" != (%s)", func(s ast.Stmt) ast.Expr { return s.(*ast.AssignStmt).Rhs[0].(*ast.BinaryExpr).Y })}
	}
	m.declare(name)
	if name == "_" {
		return xField{Kind: "any"}
	}
	kind := map[string]string{"Aux": "aux", "AuxInt": "auxInt"}[field]
	return xField{Kind: "bind", Var: m.r.addVar(name, kind, conv)}
}

func pathString(p []int) string {
	var s []string
	for _, i := range p {
		s = append(s, strconv.Itoa(i))
	}
	return strings.Join(s, ".")
}

// crossCheck runs rulegen's real code generator on the rule and compares the sequences of
// declared names, of allocated ops and of their positions, and the position genMatch chose,
// with the mirror's.
func crossCheck(a arch, lr locRule, r *xRule, op string) {
	rr := &RuleRewrite{Loc: lr.Loc}
	if r.Block {
		_, data := getBlockInfo(r.rawKind, a)
		rr = genBlockRewrite(lr.Rule, a, data)
	} else {
		rr.Match, rr.Cond, rr.Result = lr.parse()
		pos, _ := genMatch(rr, a, rr.Match, opByName(a, op).argLength >= 0)
		want := "v.Pos"
		if r.posVar != "" {
			want = r.posVar + ".Pos"
		}
		if pos == "" {
			pos = "v.Pos"
		}
		if pos != want {
			log.Fatalf("%s: position mismatch: rulegen %s, mirror %s", r.loc(), pos, want)
		}
		if rr.Cond != "" {
			rr.add(breakf("!(%s)", rr.Cond))
		}
		genResult(rr, a, rr.Result, pos)
	}
	var decls, allocs, allocPos []string
	for _, s := range rr.List {
		d, ok := s.(*Declare)
		if !ok {
			continue
		}
		if c, ok := d.Value.(*ast.CallExpr); ok {
			if sel, ok := c.Fun.(*ast.SelectorExpr); ok && sel.Sel.Name == "NewValue0" {
				allocs = append(allocs, strings.TrimPrefix(c.Args[1].(*ast.Ident).Name, "Op"))
				allocPos = append(allocPos, types.ExprString(c.Args[0]))
				continue
			}
		}
		decls = append(decls, d.Name)
	}
	if strings.Join(decls, ",") != strings.Join(r.declNames, ",") {
		log.Fatalf("%s: declaration order mismatch:\n rulegen %v\n mirror  %v", r.loc(), decls, r.declNames)
	}
	if strings.Join(allocs, ",") != strings.Join(r.allocOps, ",") {
		log.Fatalf("%s: allocation order mismatch:\n rulegen %v\n mirror  %v", r.loc(), allocs, r.allocOps)
	}
	if strings.Join(allocPos, ",") != strings.Join(r.allocPos, ",") {
		log.Fatalf("%s: allocation position mismatch:\n rulegen %v\n mirror  %v", r.loc(), allocPos, r.allocPos)
	}
}

// ---------------------------------------------------------------------------------------
// Type-checking all rule expressions inside the pinned ssa package.

// zbootstrap is internal/buildcfg/zbootstrap.go as cmd/dist writes it (mkbuildcfg); only
// needed if the pinned tree has not been built. Values do not matter for type-checking.
const zbootstrap = "package buildcfg\n\nimport \"runtime\"\n\n" +
	"const DefaultGO386 = `sse2`\nconst DefaultGOAMD64 = `v1`\nconst DefaultGOARM = `7`\n" +
	"const DefaultGOARM64 = `v8.0`\nconst DefaultGOMIPS = `hardfloat`\nconst DefaultGOMIPS64 = `hardfloat`\n" +
	"const DefaultGOPPC64 = `power8`\nconst DefaultGORISCV64 = `rva20u64`\nconst defaultGOEXPERIMENT = ``\n" +
	"const defaultGO_EXTLINK_ENABLED = ``\nconst defaultGO_LDSO = ``\nconst version = `go1.27.3`\n" +
	"const defaultGOOS = runtime.GOOS\nconst defaultGOARCH = runtime.GOARCH\nconst DefaultGOFIPS140 = `off`\n" +
	"const DefaultCGO_ENABLED = \"\"\n"

type fakeInfo struct{ name string }

func (f fakeInfo) Name() string       { return f.name }
func (f fakeInfo) Size() int64        { return int64(len(zbootstrap)) }
func (f fakeInfo) Mode() fs.FileMode  { return 0444 }
func (f fakeInfo) ModTime() time.Time { return time.Time{} }
func (f fakeInfo) IsDir() bool        { return false }
func (f fakeInfo) Sys() any           { return nil }

var ssaPkg *types.Package

func typecheck(goroot string, rules []*xRule) *types.Info {
	ctxt := &build.Default
	ctxt.GOROOT = goroot
	ctxt.GOOS, ctxt.GOARCH = "linux", "arm64"
	ctxt.CgoEnabled = false
	bdir := filepath.Join(goroot, "src", "internal", "buildcfg")
	zpath := filepath.Join(bdir, "zbootstrap.go")
	if _, err := os.Stat(zpath); err != nil {
		ctxt.ReadDir = func(dir string) ([]fs.FileInfo, error) {
			ents, err := os.ReadDir(dir)
			if err != nil {
				return nil, err
			}
			var out []fs.FileInfo
			for _, e := range ents {
				fi, err := e.Info()
				if err != nil {
					return nil, err
				}
				out = append(out, fi)
			}
			if filepath.Clean(dir) == bdir {
				out = append(out, fakeInfo{"zbootstrap.go"})
			}
			return out, nil
		}
		ctxt.OpenFile = func(p string) (io.ReadCloser, error) {
			if filepath.Clean(p) == zpath {
				return io.NopCloser(strings.NewReader(zbootstrap)), nil
			}
			return os.Open(p)
		}
	}
	fset := token.NewFileSet()
	dir := filepath.Join(goroot, "src", "cmd", "compile", "internal", "ssa")
	bp, err := ctxt.ImportDir(dir, 0)
	if err != nil {
		log.Fatal(err)
	}
	var files []*ast.File
	for _, f := range bp.GoFiles {
		af, err := parser.ParseFile(fset, filepath.Join(dir, f), nil, parser.SkipObjectResolution)
		if err != nil {
			log.Fatal(err)
		}
		// Bodies are irrelevant for the rule expressions; dropping them makes the check
		// faster and independent of the host go/types' support for newer statements.
		for _, d := range af.Decls {
			if fd, ok := d.(*ast.FuncDecl); ok {
				fd.Body = nil
			}
		}
		files = append(files, af)
	}
	src := syntheticFile(rules)
	synth, err := parser.ParseFile(fset, "gofv_rules_synthetic.go", src, parser.SkipObjectResolution)
	if err != nil {
		os.WriteFile(filepath.Join(os.Getenv("GOFV_TMP"), "gofv_rules_synthetic.go"), []byte(src), 0644)
		log.Fatalf("synthetic file: %v", err)
	}
	files = append(files, synth)
	info := &types.Info{
		Types:      map[ast.Expr]types.TypeAndValue{},
		Uses:       map[*ast.Ident]types.Object{},
		Defs:       map[*ast.Ident]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
	}
	var errs []string
	conf := types.Config{
		Importer: importer.ForCompiler(fset, "source", nil),
		Sizes:    types.SizesFor("gc", "arm64"),
		Error: func(err error) {
			te, ok := err.(types.Error)
			if ok && fset.Position(te.Pos).Filename == "gofv_rules_synthetic.go" && !te.Soft {
				errs = append(errs, err.Error())
			} else if ok && fset.Position(te.Pos).Filename == "gofv_rules_synthetic.go" && !strings.Contains(te.Msg, "declared and not used") && !strings.Contains(te.Msg, "imported and not used") {
				errs = append(errs, err.Error())
			}
		},
	}
	ssaPkg, _ = conf.Check("cmd/compile/internal/ssa", fset, files, info)
	if len(errs) > 0 {
		os.WriteFile(filepath.Join(os.Getenv("GOFV_TMP"), "gofv_rules_synthetic.go"), []byte(src), 0644)
		log.Fatalf("type errors in rule expressions:\n%s", strings.Join(errs, "\n"))
	}
	// Attach the expressions.
	fns := map[string]*ast.FuncDecl{}
	for _, d := range synth.Decls {
		if fd, ok := d.(*ast.FuncDecl); ok {
			fns[fd.Name.Name] = fd
		}
	}
	for _, r := range rules {
		fd := fns[r.fnName]
		body := fd.Body.List
		off := len(body) - len(r.slots)
		for i, s := range r.slots {
			s.Expr = unparen(s.Ex(body[off+i]))
		}
		for _, st := range body[:off] {
			as, ok := st.(*ast.AssignStmt)
			if !ok || as.Tok != token.DEFINE {
				continue
			}
			id := as.Lhs[0].(*ast.Ident)
			if vi, ok := r.varIdx[id.Name]; ok {
				r.Vars[vi].Ty = info.Defs[id].Type()
			}
		}
	}
	return info
}

func unparen(e ast.Expr) ast.Expr {
	for {
		p, ok := e.(*ast.ParenExpr)
		if !ok {
			return e
		}
		e = p.X
	}
}

func syntheticFile(rules []*xRule) string {
	var b bytes.Buffer
	// The imports of every generated rewrite file (rulegen's fprint).
	b.WriteString("package ssa\n\nimport (\n\t\"fmt\"\n\t\"internal/buildcfg\"\n\t\"math\"\n\t\"math/bits\"\n\t\"cmd/internal/obj\"\n\t\"cmd/compile/internal/base\"\n\t\"cmd/compile/internal/types\"\n\t\"cmd/compile/internal/ir\"\n)\n\n")
	for i, r := range rules {
		r.fnName = fmt.Sprintf("_gofv_rule_%d", i)
		if r.Block {
			fmt.Fprintf(&b, "func %s(b *Block) {\n\tconfig := b.Func.Config\n\ttyp := &b.Func.Config.Types\n\t_, _ = config, typ\n", r.fnName)
		} else {
			fmt.Fprintf(&b, "func %s(v *Value) {\n\tb := v.Block\n\tconfig := b.Func.Config\n\tfe := b.Func.fe\n\ttyp := &b.Func.Config.Types\n\t_, _, _ = config, fe, typ\n", r.fnName)
		}
		for _, v := range r.Vars {
			decl := v.Decl
			decl = strings.ReplaceAll(decl, "%s", r.declBase())
			fmt.Fprintf(&b, "\t%s := %s\n\t_ = %s\n", v.Name, decl, v.Name)
		}
		for _, s := range r.slots {
			fmt.Fprintf(&b, "\t"+s.Stmt+"\n", s.Src)
		}
		b.WriteString("}\n\n")
	}
	return b.String()
}

func (r *xRule) declBase() string {
	if r.Block {
		return "b.Controls[0]"
	}
	return "v"
}

// ---------------------------------------------------------------------------------------
// Lean rendering of typed Go expressions.

type inventory struct {
	cats map[string]map[string]*invEntry // category -> name -> entry
}

type invEntry struct {
	count int
	rules map[string]bool
	files map[string]int
	sig   string
}

func (inv *inventory) add(cat, name, sig string, r *xRule) {
	if inv.cats == nil {
		inv.cats = map[string]map[string]*invEntry{}
	}
	m := inv.cats[cat]
	if m == nil {
		m = map[string]*invEntry{}
		inv.cats[cat] = m
	}
	e := m[name]
	if e == nil {
		e = &invEntry{rules: map[string]bool{}, files: map[string]int{}, sig: sig}
		m[name] = e
	}
	e.count++
	e.rules[r.LeanId] = true
	e.files[r.File]++
}

type renderer struct {
	info *types.Info
	inv  *inventory
	r    *xRule
	role string
}

func qual(p *types.Package) string {
	if p == ssaPkg {
		return ""
	}
	return p.Name()
}

func leanStr(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, c := range s {
		switch {
		case c == '"':
			b.WriteString("\\\"")
		case c == '\\':
			b.WriteString("\\\\")
		case c == '\n':
			b.WriteString("\\n")
		case c == '\t':
			b.WriteString("\\t")
		case c < 0x20 || c == 0x7f:
			fmt.Fprintf(&b, "\\x%02x", c)
		default:
			b.WriteRune(c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func (rd *renderer) goTy(t types.Type) string {
	if b, ok := t.(*types.Basic); ok {
		switch b.Kind() {
		case types.Bool:
			return ".bool"
		case types.Int:
			return ".int"
		case types.Int8:
			return ".int8"
		case types.Int16:
			return ".int16"
		case types.Int32:
			return ".int32"
		case types.Int64:
			return ".int64"
		case types.Uint:
			return ".uint"
		case types.Uint8:
			return ".uint8"
		case types.Uint16:
			return ".uint16"
		case types.Uint32:
			return ".uint32"
		case types.Uint64:
			return ".uint64"
		case types.Uintptr:
			return ".uintptr"
		case types.Float32:
			return ".float32"
		case types.Float64:
			return ".float64"
		case types.String:
			return ".string"
		case types.UntypedInt, types.UntypedRune:
			// e.g. constant shift counts, which go/types leaves untyped.
			return ".untypedInt"
		case types.UntypedBool:
			return ".untypedBool"
		case types.UntypedFloat:
			return ".untypedFloat"
		case types.UntypedString:
			return ".untypedString"
		case types.UntypedNil:
			return ".untypedNil"
		default:
			log.Fatalf("%s: expression of type %s", rd.r.loc(), b)
		}
	}
	return fmt.Sprintf("(.named %s)", leanStr(types.TypeString(t, qual)))
}

func (rd *renderer) lit(t types.Type, v constant.Value) string {
	switch v.Kind() {
	case constant.Bool:
		return fmt.Sprintf("(.bool %v)", constant.BoolVal(v))
	case constant.String:
		return fmt.Sprintf("(.str %s)", leanStr(constant.StringVal(v)))
	case constant.Int:
		if b, ok := t.Underlying().(*types.Basic); ok && b.Info()&types.IsFloat != 0 {
			return rd.floatLit(b, v)
		}
		s := v.ExactString()
		if strings.HasPrefix(s, "-") {
			return fmt.Sprintf("(.int (%s))", s)
		}
		return fmt.Sprintf("(.int %s)", s)
	case constant.Float:
		b, ok := t.Underlying().(*types.Basic)
		if !ok || b.Info()&types.IsFloat == 0 {
			log.Fatalf("%s: float constant of type %s", rd.r.loc(), t)
		}
		return rd.floatLit(b, v)
	}
	log.Fatalf("%s: constant %v", rd.r.loc(), v)
	return ""
}

func (rd *renderer) floatLit(b *types.Basic, v constant.Value) string {
	f, _ := constant.Float64Val(constant.ToFloat(v))
	if b.Kind() == types.Float32 {
		return fmt.Sprintf("(.float32 0x%08x)", math.Float32bits(float32(f)))
	}
	return fmt.Sprintf("(.float64 0x%016x)", math.Float64bits(f))
}

var binOps = map[token.Token]string{
	token.ADD: "add", token.SUB: "sub", token.MUL: "mul", token.QUO: "quo", token.REM: "rem",
	token.AND: "and", token.OR: "or", token.XOR: "xor", token.SHL: "shl", token.SHR: "shr",
	token.AND_NOT: "andNot", token.LAND: "land", token.LOR: "lor", token.EQL: "eq",
	token.NEQ: "ne", token.LSS: "lt", token.LEQ: "le", token.GTR: "gt", token.GEQ: "ge",
}

var unOps = map[token.Token]string{token.SUB: "neg", token.NOT: "not", token.XOR: "com", token.ADD: "plus"}

func (rd *renderer) expr(e ast.Expr) string {
	e = unparen(e)
	tv, ok := rd.info.Types[e]
	if !ok {
		log.Fatalf("%s: untyped expression %T", rd.r.loc(), e)
	}
	if tv.Value != nil {
		if obj := rd.constObj(e); obj != nil {
			if named, ok := obj.Type().(*types.Named); ok {
				if named.Obj().Name() == "Op" && named.Obj().Pkg() == ssaPkg {
					rd.inv.add("op constants", obj.Name(), "", rd.r)
					return fmt.Sprintf("(.op .%s)", strings.TrimPrefix(obj.Name(), "Op"))
				}
				q := qualName(obj)
				rd.inv.add("named constants", q, types.TypeString(obj.Type(), qual), rd.r)
				return fmt.Sprintf("(.cnst %s %s %s)", leanStr(q), rd.goTy(tv.Type), rd.lit(tv.Type, tv.Value))
			}
		}
		return fmt.Sprintf("(.lit %s %s)", rd.goTy(tv.Type), rd.lit(tv.Type, tv.Value))
	}
	switch e := e.(type) {
	case *ast.Ident:
		if e.Name == "nil" {
			return fmt.Sprintf("(.lit %s .nil)", rd.goTy(tv.Type))
		}
		obj := rd.info.Uses[e]
		switch obj := obj.(type) {
		case *types.Var:
			if obj.Parent() != nil && obj.Parent() != obj.Pkg().Scope() {
				if i, ok := rd.r.varIdx[e.Name]; ok {
					return fmt.Sprintf("(.var %d)", i)
				}
				switch e.Name {
				case "v", "b", "config", "fe", "typ":
					rd.inv.add("reserved names", e.Name, types.TypeString(obj.Type(), qual), rd.r)
					return fmt.Sprintf("(.rsv .%s)", e.Name)
				}
				log.Fatalf("%s: unknown local %s", rd.r.loc(), e.Name)
			}
			q := qualName(obj)
			rd.inv.add("package variables", q, types.TypeString(obj.Type(), qual), rd.r)
			return fmt.Sprintf("(.glob %s %s)", leanStr(q), rd.goTy(tv.Type))
		}
		log.Fatalf("%s: identifier %s (%T)", rd.r.loc(), e.Name, obj)
	case *ast.SelectorExpr:
		if sel, ok := rd.info.Selections[e]; ok {
			switch sel.Kind() {
			case types.FieldVal:
				rt := types.TypeString(sel.Recv(), qual)
				rd.inv.add("fields", rt+"."+e.Sel.Name, types.TypeString(sel.Type(), qual), rd.r)
				return fmt.Sprintf("(.field %s %s %s)", rd.expr(e.X), leanStr(e.Sel.Name), rd.goTy(tv.Type))
			default:
				log.Fatalf("%s: method value %s", rd.r.loc(), e.Sel.Name)
			}
		}
		obj := rd.info.Uses[e.Sel]
		if v, ok := obj.(*types.Var); ok {
			q := qualName(v)
			rd.inv.add("package variables", q, types.TypeString(v.Type(), qual), rd.r)
			return fmt.Sprintf("(.glob %s %s)", leanStr(q), rd.goTy(tv.Type))
		}
		log.Fatalf("%s: selector %s (%T)", rd.r.loc(), e.Sel.Name, obj)
	case *ast.CallExpr:
		return rd.call(e, tv)
	case *ast.BinaryExpr:
		op, ok := binOps[e.Op]
		if !ok {
			log.Fatalf("%s: binary %s", rd.r.loc(), e.Op)
		}
		xt := rd.info.Types[unparen(e.X)].Type
		rd.inv.add("operators", e.Op.String()+" "+types.TypeString(xt, qual), "", rd.r)
		return fmt.Sprintf("(.binop .%s %s %s %s)", op, rd.expr(e.X), rd.expr(e.Y), rd.goTy(tv.Type))
	case *ast.UnaryExpr:
		op, ok := unOps[e.Op]
		if !ok {
			log.Fatalf("%s: unary %s", rd.r.loc(), e.Op)
		}
		rd.inv.add("operators", "unary "+e.Op.String()+" "+types.TypeString(tv.Type, qual), "", rd.r)
		return fmt.Sprintf("(.unop .%s %s %s)", op, rd.expr(e.X), rd.goTy(tv.Type))
	case *ast.IndexExpr:
		rd.inv.add("operators", "index "+types.TypeString(rd.info.Types[unparen(e.X)].Type, qual), "", rd.r)
		return fmt.Sprintf("(.index %s %s %s)", rd.expr(e.X), rd.expr(e.Index), rd.goTy(tv.Type))
	case *ast.TypeAssertExpr:
		rd.inv.add("type assertions", types.TypeString(rd.info.Types[unparen(e.X)].Type, qual)+".("+types.TypeString(tv.Type, qual)+")", "", rd.r)
		return fmt.Sprintf("(.assert %s %s)", rd.goTy(tv.Type), rd.expr(e.X))
	case *ast.StarExpr:
		rd.inv.add("operators", "deref "+types.TypeString(rd.info.Types[unparen(e.X)].Type, qual), "", rd.r)
		return fmt.Sprintf("(.deref %s %s)", rd.expr(e.X), rd.goTy(tv.Type))
	case *ast.CompositeLit:
		// A keyed struct literal T{f1: e1, f2: e2} is exported as the pseudo-call
		// `.call "T{f1,f2}" [e1, e2] T` (fields in source order, unnamed fields zero): a pure
		// function of its field values (docs/contracts/rules.md).
		var keys []string
		var vals []ast.Expr
		for _, el := range e.Elts {
			kv, ok := el.(*ast.KeyValueExpr)
			if !ok {
				log.Fatalf("%s: unkeyed composite literal", rd.r.loc())
			}
			keys = append(keys, kv.Key.(*ast.Ident).Name)
			vals = append(vals, kv.Value)
		}
		if _, ok := tv.Type.Underlying().(*types.Struct); !ok {
			log.Fatalf("%s: composite literal of non-struct type %s", rd.r.loc(), tv.Type)
		}
		name := types.TypeString(tv.Type, qual) + "{" + strings.Join(keys, ",") + "}"
		rd.inv.add("composite literals", name, "", rd.r)
		return fmt.Sprintf("(.call %s %s %s)", leanStr(name), rd.args(vals), rd.goTy(tv.Type))
	}
	log.Fatalf("%s: unsupported expression %T", rd.r.loc(), e)
	return ""
}

func qualName(obj types.Object) string {
	if obj.Pkg() == nil || obj.Pkg() == ssaPkg {
		return obj.Name()
	}
	return obj.Pkg().Name() + "." + obj.Name()
}

func (rd *renderer) constObj(e ast.Expr) types.Object {
	switch e := e.(type) {
	case *ast.Ident:
		if c, ok := rd.info.Uses[e].(*types.Const); ok {
			return c
		}
	case *ast.SelectorExpr:
		if c, ok := rd.info.Uses[e.Sel].(*types.Const); ok {
			return c
		}
	}
	return nil
}

func (rd *renderer) args(es []ast.Expr) string {
	var s []string
	for _, a := range es {
		s = append(s, rd.expr(a))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

func (rd *renderer) call(e *ast.CallExpr, tv types.TypeAndValue) string {
	fun := unparen(e.Fun)
	if ftv, ok := rd.info.Types[fun]; ok && ftv.IsType() {
		if len(e.Args) != 1 {
			log.Fatalf("%s: conversion arity", rd.r.loc())
		}
		rd.inv.add("conversions", types.TypeString(rd.info.Types[unparen(e.Args[0])].Type, qual)+" -> "+types.TypeString(tv.Type, qual), "", rd.r)
		return fmt.Sprintf("(.conv %s %s)", rd.goTy(tv.Type), rd.expr(e.Args[0]))
	}
	if e.Ellipsis.IsValid() {
		log.Fatalf("%s: variadic call with ...", rd.r.loc())
	}
	// Generic instantiation f[T](...)
	if ix, ok := fun.(*ast.IndexExpr); ok {
		fun = ix.X
	}
	switch f := fun.(type) {
	case *ast.Ident:
		switch obj := rd.info.Uses[f].(type) {
		case *types.Builtin:
			rd.inv.add("builtins", f.Name, "", rd.r)
			return fmt.Sprintf("(.builtin %s %s %s)", leanStr(f.Name), rd.args(e.Args), rd.goTy(tv.Type))
		case *types.Func:
			rd.inv.add("functions", qualName(obj), sigString(obj), rd.r)
			return fmt.Sprintf("(.call %s %s %s)", leanStr(qualName(obj)), rd.args(e.Args), rd.goTy(tv.Type))
		}
	case *ast.SelectorExpr:
		if sel, ok := rd.info.Selections[f]; ok {
			if sel.Kind() != types.MethodVal {
				log.Fatalf("%s: call of field %s", rd.r.loc(), f.Sel.Name)
			}
			recv := types.TypeString(sel.Recv(), qual)
			rd.inv.add("methods", recv+"."+f.Sel.Name, sigString(sel.Obj().(*types.Func)), rd.r)
			return fmt.Sprintf("(.method %s %s %s %s)", rd.expr(f.X), leanStr(f.Sel.Name), rd.args(e.Args), rd.goTy(tv.Type))
		}
		if obj, ok := rd.info.Uses[f.Sel].(*types.Func); ok {
			rd.inv.add("functions", qualName(obj), sigString(obj), rd.r)
			return fmt.Sprintf("(.call %s %s %s)", leanStr(qualName(obj)), rd.args(e.Args), rd.goTy(tv.Type))
		}
	}
	log.Fatalf("%s: unsupported call %T", rd.r.loc(), fun)
	return ""
}

func sigString(f *types.Func) string {
	return types.TypeString(f.Type(), qual)
}

// ---------------------------------------------------------------------------------------
// Lean output

func (rd *renderer) slotExpr(s *slot) string {
	rd.role = s.Role
	rd.inv.add("expression roles", s.Role, "", rd.r)
	return rd.expr(s.Expr)
}

func (rd *renderer) optSlot(s *slot) string {
	if s == nil {
		return "none"
	}
	return "(some " + rd.slotExpr(s) + ")"
}

func (rd *renderer) field(f xField) string {
	switch f.Kind {
	case "any":
		return ".any"
	case "bind":
		return fmt.Sprintf("(.bind %d)", f.Var)
	default:
		return fmt.Sprintf("(.eq %s)", rd.slotExpr(f.E))
	}
}

func (rd *renderer) pat(p *xPat) string {
	switch p.Kind {
	case "wild":
		return ".wild"
	case "bind":
		return fmt.Sprintf("(.bind %d)", p.Var)
	case "same":
		return fmt.Sprintf("(.same %d)", p.Var)
	}
	name := "none"
	if p.Name >= 0 {
		name = fmt.Sprintf("(some %d)", p.Name)
	}
	var arity string
	switch p.Arity {
	case "fixed":
		arity = ".fixed"
	case "ellipsis":
		arity = ".ellipsis"
	default:
		arity = fmt.Sprintf("(.%s %d)", p.Arity, p.ArityN)
	}
	var as []string
	for _, a := range p.Args {
		as = append(as, rd.pat(a))
	}
	return fmt.Sprintf("(.op .%s %s %s %s %s %s [%s] %v)", p.Op, name, rd.field(p.Ty), rd.field(p.AuxInt), rd.field(p.Aux), arity, strings.Join(as, ", "), p.Commute)
}

func (rd *renderer) nodes(ns []*xNode, base int) string {
	var out []string
	for _, n := range ns {
		var as []string
		for _, a := range n.Args {
			switch a.Kind {
			case "var":
				as = append(as, fmt.Sprintf(".var %d", a.N))
			case "expr":
				as = append(as, fmt.Sprintf(".expr %s", rd.slotExpr(a.E)))
			default:
				as = append(as, fmt.Sprintf(".node %d", a.N-base))
			}
		}
		out = append(out, fmt.Sprintf("{ op := .%s, ty := %s, auxInt := %s, aux := %s, args := [%s] }", n.Op, rd.optSlot(n.Ty), rd.optSlot(n.AuxInt), rd.optSlot(n.Aux), strings.Join(as, ", ")))
	}
	return "[" + strings.Join(out, ",\n      ") + "]"
}

func (rd *renderer) vars() string {
	var vs []string
	for _, v := range rd.r.Vars {
		vs = append(vs, fmt.Sprintf("⟨%s, .%s, %s⟩", leanStr(v.Name), v.Kind, rd.goTy(v.Ty)))
	}
	return "[" + strings.Join(vs, ", ") + "]"
}

func natList(p []int) string {
	var s []string
	for _, i := range p {
		s = append(s, strconv.Itoa(i))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

var convRe = regexp.MustCompile(`\b(auxIntTo\w+|auxTo\w+|\w+ToAuxInt|\w+ToAux)\(`)

// convs records the AuxInt/Aux conversion functions the generated code of the rule calls.
func (rd *renderer) convs() {
	var srcs []string
	for _, v := range rd.r.Vars {
		srcs = append(srcs, v.Decl)
	}
	for _, s := range rd.r.slots {
		srcs = append(srcs, s.Stmt)
	}
	for _, s := range srcs {
		for _, m := range convRe.FindAllStringSubmatch(s, -1) {
			rd.inv.add("aux conversions", m[1], "", rd.r)
		}
	}
}

func (rd *renderer) valueRule(w *bytes.Buffer) {
	r := rd.r
	rd.convs()
	fmt.Fprintf(w, "/-- `%s`: `%s` -/\n", r.loc(), docText(r.Text))
	fmt.Fprintf(w, "def %s : Rule where\n", r.LeanId)
	fmt.Fprintf(w, "  loc := ⟨%s, %d⟩\n", leanStr(r.File), r.Line)
	fmt.Fprintf(w, "  op := .%s\n", r.Op)
	fmt.Fprintf(w, "  vars := %s\n", rd.vars())
	fmt.Fprintf(w, "  pat := %s\n", rd.pat(r.Pat))
	fmt.Fprintf(w, "  cond := %s\n", rd.optSlot(r.Cond))
	fmt.Fprintf(w, "  block := %s\n", rd.optSlot(r.Move))
	switch r.Result.Kind {
	case "copy":
		fmt.Fprintf(w, "  result := .copy %s\n", rd.slotExpr(r.Result.Copy))
	case "setOp":
		fmt.Fprintf(w, "  result := .setOp .%s\n", r.Result.SetOp)
	default:
		fmt.Fprintf(w, "  result := .build\n      %s\n", rd.nodes(r.Result.Nodes, 0))
	}
	fmt.Fprintf(w, "  pos := %s\n\n", natList(r.Pos))
}

func (rd *renderer) blockRule(w *bytes.Buffer) {
	r := rd.r
	rd.convs()
	fmt.Fprintf(w, "/-- `%s`: `%s` -/\n", r.loc(), docText(r.Text))
	fmt.Fprintf(w, "def %s : BlockRule where\n", r.LeanId)
	fmt.Fprintf(w, "  loc := ⟨%s, %d⟩\n", leanStr(r.File), r.Line)
	fmt.Fprintf(w, "  kind := .%s\n", r.Op)
	fmt.Fprintf(w, "  vars := %s\n", rd.vars())
	var cs []string
	for _, c := range r.Ctrls {
		cs = append(cs, rd.pat(c))
	}
	fmt.Fprintf(w, "  controls := [%s]\n", strings.Join(cs, ", "))
	fmt.Fprintf(w, "  auxInt := %s\n", rd.field(r.BAuxInt))
	fmt.Fprintf(w, "  aux := %s\n", rd.field(r.BAux))
	fmt.Fprintf(w, "  cond := %s\n", rd.optSlot(r.Cond))
	fmt.Fprintf(w, "  newKind := .%s\n", r.NewKind)
	var ncs []string
	base := 0
	for i := range r.NewCtrlVar {
		var pos string
		if r.NewCtrlPos[i] == "block" {
			pos = ".block"
		} else {
			parts := strings.Split(strings.TrimPrefix(r.NewCtrlPos[i], "ctrl:"), ".")
			var p []int
			for _, s := range parts {
				n, _ := strconv.Atoi(s)
				p = append(p, n)
			}
			pos = fmt.Sprintf("(.control %d %s)", p[0], natList(p[1:]))
		}
		if r.NewCtrlVar[i] >= 0 {
			ncs = append(ncs, fmt.Sprintf("⟨.var %d, %s⟩", r.NewCtrlVar[i], pos))
		} else {
			ncs = append(ncs, fmt.Sprintf("⟨.build %s, %s⟩", rd.nodes(r.NewCtrls[i], base), pos))
			base += len(r.NewCtrls[i])
		}
	}
	fmt.Fprintf(w, "  newControls := [%s]\n", strings.Join(ncs, ",\n    "))
	fmt.Fprintf(w, "  newAuxInt := %s\n", rd.optSlot(r.NewAuxInt))
	fmt.Fprintf(w, "  newAux := %s\n", rd.optSlot(r.NewAux))
	fmt.Fprintf(w, "  swapSuccs := %v\n\n", r.Swap)
}

// docText makes rule text safe inside a Lean doc comment and a Markdown code span.
func docText(s string) string {
	return strings.NewReplacer("`", "'", "/-", "/ -", "-/", "- /").Replace(s)
}

const header = "-- Generated by tools/rules2lean from the pinned Go %s (_gen/%s.rules). Do not edit.\n-- Regenerate: scripts/memcap.sh go run -C tools/rules2lean . (docs/contracts/rules.md).\n"

// rulesPerModule bounds module size.
const rulesPerModule = 120

type opGroup struct {
	op    string // Lean constructor (Op / BlockKind)
	raw   string // block groups: the kind as written in the rule file
	rules []*xRule
}

func rules2leanMain() {
	log.SetFlags(0)
	out := os.Getenv("GOFV_OUT")
	invPath := os.Getenv("GOFV_INVENTORY")
	goroot := os.Getenv("GOFV_GOROOT")
	goVersion := os.Getenv("GOFV_GOVERSION")
	if out == "" || goroot == "" {
		log.Fatal("GOFV_OUT and GOFV_GOROOT must be set (run via tools/rules2lean)")
	}
	type fileData struct {
		name   string
		values []opGroup
		blocks []opGroup
	}
	var all []*xRule
	var datas []*fileData
	for _, rf := range ruleFiles {
		var a arch
		found := false
		for _, x := range archs {
			if x.name == rf.arch {
				a, found = x, true
			}
		}
		if !found {
			log.Fatalf("no arch %s", rf.arch)
		}
		fd := &fileData{name: rf.name()}
		ops, oprules, blocks, blockrules, simdSkipped := loadRules(a, rf.suffix)
		ids := map[string]int{}
		leanId := func(lr locRule) string {
			base := fmt.Sprintf("r_%s_%d", lr.file, lr.line)
			ids[base]++
			if ids[base] > 1 {
				return fmt.Sprintf("%s_%d", base, ids[base])
			}
			return base
		}
		for _, op := range ops {
			g := opGroup{op: strings.TrimPrefix(op, "Op")}
			lrs := oprules[op]
			if eop, ok := parseEllipsisRules(toRules(lrs), a); ok {
				r := buildEllipsisRule(a, lrs[0], op, eop)
				r.LeanId = leanId(lrs[0])
				g.rules = append(g.rules, r)
			} else {
				for _, lr := range lrs {
					r := buildValueRule(a, lr, op)
					crossCheck(a, lr, r, op)
					r.LeanId = leanId(lr)
					g.rules = append(g.rules, r)
				}
			}
			all = append(all, g.rules...)
			fd.values = append(fd.values, g)
		}
		for _, kind := range blocks {
			g := opGroup{op: leanBlock(kind, a), raw: kind}
			for _, lr := range blockrules[kind] {
				r := buildBlockRule(a, lr, kind)
				crossCheck(a, lr, r, "")
				r.LeanId = leanId(lr)
				g.rules = append(g.rules, r)
			}
			all = append(all, g.rules...)
			fd.blocks = append(fd.blocks, g)
		}
		checkGenerated(fd.name, fd.values, fd.blocks, oprules, blockrules, simdSkipped)
		datas = append(datas, fd)
	}
	info := typecheck(goroot, all)
	inv := &inventory{}

	if err := os.RemoveAll(out); err != nil {
		log.Fatal(err)
	}
	var written []string
	write := func(rel string, content []byte) {
		p := filepath.Join(out, rel)
		if err := os.MkdirAll(filepath.Dir(p), 0755); err != nil {
			log.Fatal(err)
		}
		if err := os.WriteFile(p, content, 0644); err != nil {
			log.Fatal(err)
		}
		written = append(written, rel)
	}
	var umbrella []string
	for _, fd := range datas {
		mod := strings.ToUpper(fd.name[:1]) + fd.name[1:]
		ns := "GoFV.Rules.Generated." + mod
		// Chunk ops into modules of about rulesPerModule rules, never splitting an op.
		var chunks [][]opGroup
		var cur []opGroup
		n := 0
		for _, g := range fd.values {
			if n > 0 && n+len(g.rules) > rulesPerModule {
				chunks = append(chunks, cur)
				cur, n = nil, 0
			}
			cur = append(cur, g)
			n += len(g.rules)
		}
		if len(cur) > 0 {
			chunks = append(chunks, cur)
		}
		var parts []string
		for ci, ch := range chunks {
			part := fmt.Sprintf("Values%02d", ci)
			parts = append(parts, part)
			var w bytes.Buffer
			fmt.Fprintf(&w, header, goVersion, fd.name)
			fmt.Fprintf(&w, "-- Value rules for ops %s .. %s.\nimport GoFV.Rules.Syntax\n\nnamespace %s\nopen GoFV.Rules\n\n", ch[0].op, ch[len(ch)-1].op, ns)
			for _, g := range ch {
				var ids []string
				for _, r := range g.rules {
					rd := &renderer{info: info, inv: inv, r: r}
					rd.valueRule(&w)
					ids = append(ids, r.LeanId)
				}
				fmt.Fprintf(&w, "/-- Rules of `Op%s`, in matching order. -/\ndef ops_%s : List Rule := [%s]\n\n", g.op, g.op, strings.Join(ids, ", "))
			}
			fmt.Fprintf(&w, "end %s\n", ns)
			write(filepath.Join(mod, part+".lean"), w.Bytes())
		}
		if len(fd.blocks) > 0 {
			parts = append(parts, "Blocks")
			var w bytes.Buffer
			fmt.Fprintf(&w, header, goVersion, fd.name)
			fmt.Fprintf(&w, "-- Block rules.\nimport GoFV.Rules.Syntax\n\nnamespace %s\nopen GoFV.Rules\n\n", ns)
			for _, g := range fd.blocks {
				var ids []string
				for _, r := range g.rules {
					rd := &renderer{info: info, inv: inv, r: r}
					rd.blockRule(&w)
					ids = append(ids, r.LeanId)
				}
				fmt.Fprintf(&w, "/-- Rules of `Block%s`, in matching order. -/\ndef blocks_%s : List BlockRule := [%s]\n\n", g.op, g.op, strings.Join(ids, ", "))
			}
			fmt.Fprintf(&w, "end %s\n", ns)
			write(filepath.Join(mod, "Blocks.lean"), w.Bytes())
		}
		// Table module.
		var w bytes.Buffer
		fmt.Fprintf(&w, header, goVersion, fd.name)
		for _, p := range parts {
			fmt.Fprintf(&w, "import %s.%s\n", ns, p)
		}
		fmt.Fprintf(&w, "\nnamespace %s\nopen GoFV.Rules\n\n", ns)
		nv, nb := 0, 0
		var vs, bs []string
		for _, g := range fd.values {
			vs = append(vs, fmt.Sprintf("(.%s, ops_%s)", g.op, g.op))
			nv += len(g.rules)
		}
		for _, g := range fd.blocks {
			bs = append(bs, fmt.Sprintf("(.%s, blocks_%s)", g.op, g.op))
			nb += len(g.rules)
		}
		fmt.Fprintf(&w, "/-- `_gen/%s.rules`: value rules per op (ops sorted by Go name, as rulegen's switch),\nblock rules per block kind. -/\ndef ruleSet : RuleSet where\n  name := %s\n", fd.name, leanStr(fd.name))
		fmt.Fprintf(&w, "  values := [%s]\n", strings.Join(vs, ",\n    "))
		fmt.Fprintf(&w, "  blocks := [%s]\n\n", strings.Join(bs, ", "))
		fmt.Fprintf(&w, "/-- Number of value rules and block rules (after `|` expansion). -/\ndef counts : Nat × Nat := (%d, %d)\n\nend %s\n", nv, nb, ns)
		write(mod+".lean", w.Bytes())
		umbrella = append(umbrella, ns)
		log.Printf("%s: %d ops, %d value rules, %d block kinds, %d block rules, %d modules", fd.name, len(fd.values), nv, len(fd.blocks), nb, len(parts)+1)
	}
	// Umbrella.
	var w bytes.Buffer
	fmt.Fprintf(&w, "-- Generated by tools/rules2lean from the pinned Go %s. Do not edit.\n", goVersion)
	for _, u := range umbrella {
		fmt.Fprintf(&w, "import %s\n", u)
	}
	write("../Generated.lean", w.Bytes())
	if invPath != "" {
		writeInventory(invPath, inv, all)
	}
	sort.Strings(written)
	log.Printf("wrote %d files under %s", len(written), out)
}

func toRules(lrs []locRule) []Rule {
	var rs []Rule
	for _, lr := range lrs {
		rs = append(rs, lr.Rule)
	}
	return rs
}

func writeInventory(path string, inv *inventory, all []*xRule) {
	var w bytes.Buffer
	w.WriteString(invBegin + "\n<!-- Generated by tools/rules2lean; do not edit by hand. -->\n")
	cats := []string{"functions", "methods", "fields", "package variables", "builtins", "conversions", "type assertions", "operators", "named constants", "reserved names", "aux conversions", "expression roles"}
	for c := range inv.cats {
		found := false
		for _, x := range cats {
			found = found || x == c
		}
		if !found && c != "op constants" {
			cats = append(cats, c)
		}
	}
	for _, c := range cats {
		m := inv.cats[c]
		if len(m) == 0 {
			continue
		}
		fmt.Fprintf(&w, "\n#### %s\n\n", strings.ToUpper(c[:1])+c[1:])
		withSig := c == "functions" || c == "methods" || c == "fields" || c == "package variables" || c == "named constants" || c == "reserved names"
		var fileNames []string
		for _, rf := range ruleFiles {
			fileNames = append(fileNames, rf.name())
		}
		cols := strings.Join(fileNames, " / ")
		if withSig {
			w.WriteString("| Name | Go type | Uses | Rules | " + cols + " |\n| --- | --- | --: | --: | --- |\n")
		} else {
			w.WriteString("| Form | Uses | Rules | " + cols + " |\n| --- | --: | --: | --- |\n")
		}
		var names []string
		for n := range m {
			names = append(names, n)
		}
		sort.Slice(names, func(i, j int) bool {
			if m[names[i]].count != m[names[j]].count {
				return m[names[i]].count > m[names[j]].count
			}
			return names[i] < names[j]
		})
		for _, n := range names {
			e := m[n]
			var counts []string
			for _, f := range fileNames {
				counts = append(counts, strconv.Itoa(e.files[f]))
			}
			per := strings.Join(counts, " / ")
			if withSig {
				fmt.Fprintf(&w, "| `%s` | `%s` | %d | %d | %s |\n", n, strings.ReplaceAll(e.sig, "|", "\\|"), e.count, len(e.rules), per)
			} else {
				fmt.Fprintf(&w, "| `%s` | %d | %d | %s |\n", strings.ReplaceAll(n, "|", "\\|"), e.count, len(e.rules), per)
			}
		}
	}
	if m := inv.cats["op constants"]; len(m) > 0 {
		var names []string
		for n := range m {
			names = append(names, n)
		}
		sort.Strings(names)
		fmt.Fprintf(&w, "\n#### Op constants in expressions\n\n%s\n", "`"+strings.Join(names, "`, `")+"`")
	}
	// Forms the machine-independent rule files (Phase 1, already interpreted) never use: what
	// the interpreter needs in addition for the arm64 lowering rules.
	var newForms []string
	for _, c := range cats {
		if c == "expression roles" || c == "reserved names" {
			continue
		}
		var names []string
		for n, e := range inv.cats[c] {
			old := 0
			for _, f := range []string{"generic", "dec", "divisible", "divmod"} {
				old += e.files[f]
			}
			if old == 0 {
				names = append(names, n)
			}
		}
		if len(names) == 0 {
			continue
		}
		sort.Strings(names)
		newForms = append(newForms, fmt.Sprintf("- %s%s (%d): `%s`", strings.ToUpper(c[:1]), c[1:], len(names), strings.ReplaceAll(strings.Join(names, "`, `"), "|", "\\|")))
	}
	if len(newForms) > 0 {
		fmt.Fprintf(&w, "\n#### Used only by the arm64 rule files\n\nForms of the tables above with no use in `generic` / `dec` / `divisible` / `divmod`, i.e. what the\ninterpreter needs beyond Phase 1 for `ARM64` and `ARM64latelower`:\n\n%s\n", strings.Join(newForms, "\n"))
	}
	w.WriteString("\n" + invEnd)
	doc, err := os.ReadFile(path)
	if err != nil {
		log.Fatal(err)
	}
	i, j := bytes.Index(doc, []byte(invBegin)), bytes.Index(doc, []byte(invEnd))
	if i < 0 || j < i {
		log.Fatalf("%s: inventory markers missing", path)
	}
	out := append(append(append([]byte{}, doc[:i]...), w.Bytes()...), doc[j+len(invEnd):]...)
	if err := os.WriteFile(path, out, 0644); err != nil {
		log.Fatal(err)
	}
}

const (
	invBegin = "<!-- BEGIN rules2lean inventory -->"
	invEnd   = "<!-- END rules2lean inventory -->"
)

// checkGenerated compares the exported rule order with the pinned compiler's generated
// rewrite<file>.go: per function (op) and per block kind, the sequence of
// "// match:", "// cond:", "// result:" comments must equal the exported rules' text; the
// dispatch switch of rewriteValue<file> must have a case for exactly the exported ops, calling
// the op's function or, for an ellipsis rule, setting the exported op. Functions and cases of
// the dropped SIMD ops (simdSkipped) are ignored.
func checkGenerated(name string, values, blocks []opGroup, oprules, blockrules map[string][]locRule, simdSkipped map[string]bool) {
	src, err := os.ReadFile(filepath.Join("..", "rewrite"+name+".go"))
	if err != nil {
		log.Fatal(err)
	}
	fnRe := regexp.MustCompile(`^func rewriteValue` + name + `_Op(\w+)\(`)
	blockFnRe := regexp.MustCompile(`^func rewriteBlock` + name + `\(`)
	dispatchRe := regexp.MustCompile(`^func rewriteValue` + name + `\(v \*Value\) bool \{$`)
	caseRe := regexp.MustCompile(`^\tcase Block(\w+):`)
	opCaseRe := regexp.MustCompile(`^\tcase Op(\w+):$`)
	callRe := regexp.MustCompile(`^\t\treturn rewriteValue` + name + `_Op(\w+)\(v\)$`)
	setRe := regexp.MustCompile(`^\t\tv\.Op = Op(\w+)$`)
	got := map[string][]string{}    // "v:Op" / "b:Kind" -> rule texts
	dispatch := map[string]string{} // Op -> "fn" | "set:<Op>"
	key := ""
	inBlock, inDispatch := false, false
	dcase := ""
	cur := ""
	flush := func() {
		if cur != "" {
			got[key] = append(got[key], cur)
			cur = ""
		}
	}
	for _, line := range strings.Split(string(src), "\n") {
		if m := fnRe.FindStringSubmatch(line); m != nil {
			flush()
			key, inBlock, inDispatch = "v:"+m[1], false, false
			continue
		}
		if blockFnRe.MatchString(line) {
			flush()
			key, inBlock, inDispatch = "", true, false
			continue
		}
		if dispatchRe.MatchString(line) {
			flush()
			key, inBlock, inDispatch = "", false, true
			continue
		}
		if inDispatch {
			if m := opCaseRe.FindStringSubmatch(line); m != nil {
				dcase = m[1]
			} else if m := callRe.FindStringSubmatch(line); m != nil && dcase == m[1] {
				dispatch[dcase] = "fn"
			} else if m := setRe.FindStringSubmatch(line); m != nil && dcase != "" {
				dispatch[dcase] = "set:" + m[1]
			}
			continue
		}
		if inBlock {
			if m := caseRe.FindStringSubmatch(line); m != nil {
				flush()
				key = "b:" + m[1]
				continue
			}
		}
		t := strings.TrimSpace(line)
		switch {
		case strings.HasPrefix(t, "// match: "):
			flush()
			cur = "match: " + strings.TrimPrefix(t, "// match: ")
		case strings.HasPrefix(t, "// cond: "), strings.HasPrefix(t, "// result: "):
			cur += " | " + strings.TrimPrefix(t, "// ")
		}
	}
	flush()
	text := func(lr locRule) string {
		m, c, r := lr.parse()
		s := "match: " + m
		if c != "" {
			s += " | cond: " + c
		}
		return s + " | result: " + r
	}
	for op := range simdSkipped {
		delete(got, "v:"+strings.TrimPrefix(op, "Op"))
		delete(dispatch, strings.TrimPrefix(op, "Op"))
	}
	want := map[string][]string{}
	for _, g := range values {
		d := "fn"
		if g.rules[0].Result.Kind == "setOp" {
			d = "set:" + g.rules[0].Result.SetOp
		}
		if dispatch[g.op] != d {
			log.Fatalf("%s: dispatch of Op%s in rewrite%s.go is %q, exported %q", name, g.op, name, dispatch[g.op], d)
		}
		delete(dispatch, g.op)
		if d != "fn" {
			continue // ellipsis rules have no function
		}
		for _, lr := range oprules["Op"+g.op] {
			want["v:"+g.op] = append(want["v:"+g.op], text(lr))
		}
	}
	if len(dispatch) != 0 {
		log.Fatalf("%s: ops dispatched in rewrite%s.go but not exported: %v", name, name, dispatch)
	}
	for _, g := range blocks {
		for _, lr := range blockrules[g.raw] {
			want["b:"+g.op] = append(want["b:"+g.op], text(lr))
		}
	}
	if len(got) != len(want) {
		log.Fatalf("%s: %d rule functions/cases in rewrite%s.go, %d exported", name, len(got), name, len(want))
	}
	n := 0
	for k, w := range want {
		g := got[k]
		if strings.Join(g, "\n") != strings.Join(w, "\n") {
			log.Fatalf("%s: rules of %s differ from rewrite%s.go:\n got  %q\n want %q", name, k, name, g, w)
		}
		n += len(w)
	}
	log.Printf("%s: %d rules match rewrite%s.go in order (%d SIMD ops skipped)", name, n, name, len(simdSkipped))
}
