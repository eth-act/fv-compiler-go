package main

// checkOpGen: the exported tables against the pinned generated opGen.go (the file the
// compiler is built from). Every exported op must have the opcodeTable entry genOp would write
// for it (name, aux type, argLen, every flag, symEffect, generic, asm, scale, regInfo with its
// allocation order), the ARM64 ops left out must be exactly the SIMD ones, and block kinds,
// AuxIntType, the ARM64 register list, parameter registers and register masks must agree.

import (
	"fmt"
	"go/ast"
	"go/token"
	"log"
	"reflect"
	"slices"
	"strconv"
	"strings"
)

type opGenNums struct {
	ops, blocks []int // Go constant value of each exported op / block kind
	nARM64      int
}

func intOf(e ast.Expr) int64 {
	switch e := e.(type) {
	case *ast.BasicLit:
		n, err := strconv.ParseInt(e.Value, 0, 64)
		if err != nil {
			u, err2 := strconv.ParseUint(e.Value, 0, 64)
			if err2 != nil {
				log.Fatalf("opGen.go: bad integer %s", e.Value)
			}
			return int64(u)
		}
		return n
	case *ast.UnaryExpr:
		if e.Op == token.SUB {
			return -intOf(e.X)
		}
	case *ast.ParenExpr:
		return intOf(e.X)
	case *ast.CallExpr: // int8(-1)
		if len(e.Args) == 1 {
			return intOf(e.Args[0])
		}
	}
	log.Fatalf("opGen.go: not an integer: %T", e)
	return 0
}

func uintOf(e ast.Expr) uint64 {
	if l, ok := e.(*ast.BasicLit); ok {
		u, err := strconv.ParseUint(l.Value, 0, 64)
		if err == nil {
			return u
		}
	}
	log.Fatalf("opGen.go: not an unsigned integer: %T", e)
	return 0
}

func maskOf(e ast.Expr) regMask {
	var m regMask
	for _, el := range e.(*ast.CompositeLit).Elts {
		kv := el.(*ast.KeyValueExpr)
		switch kv.Key.(*ast.Ident).Name {
		case "v1":
			m.v1 = uintOf(kv.Value)
		case "v2":
			m.v2 = uintOf(kv.Value)
		}
	}
	return m
}

func (g genReg) canon() string {
	ios := func(l []ioInfo) string {
		var s []string
		for _, x := range l {
			s = append(s, fmt.Sprintf("%d:%d:%d", x.idx, x.regs.v1, x.regs.v2))
		}
		return strings.Join(s, ",")
	}
	return fmt.Sprintf("in=%s;clob=%d:%d;a0=%v;a1=%v;out=%s", ios(g.inputs), g.clobbers.v1, g.clobbers.v2, g.clobbersArg0, g.clobbersArg1, ios(g.outputs))
}

func regOf(e ast.Expr) genReg {
	var g genReg
	ios := func(e ast.Expr) []ioInfo {
		var l []ioInfo
		for _, el := range e.(*ast.CompositeLit).Elts {
			c := el.(*ast.CompositeLit)
			l = append(l, ioInfo{int(intOf(c.Elts[0])), maskOf(c.Elts[1])})
		}
		return l
	}
	for _, el := range e.(*ast.CompositeLit).Elts {
		kv := el.(*ast.KeyValueExpr)
		switch k := kv.Key.(*ast.Ident).Name; k {
		case "inputs":
			g.inputs = ios(kv.Value)
		case "outputs":
			g.outputs = ios(kv.Value)
		case "clobbers":
			g.clobbers = maskOf(kv.Value)
		case "clobbersArg0":
			g.clobbersArg0 = kv.Value.(*ast.Ident).Name == "true"
		case "clobbersArg1":
			g.clobbersArg1 = kv.Value.(*ast.Ident).Name == "true"
		default:
			log.Fatalf("opGen.go: unknown regInfo field %s", k)
		}
	}
	return g
}

// canonEntry renders an opcodeTable element as sorted key=value pairs.
func canonEntry(fset *token.FileSet, e *ast.CompositeLit) string {
	var kvs []string
	for _, el := range e.Elts {
		kv := el.(*ast.KeyValueExpr)
		k := kv.Key.(*ast.Ident).Name
		var v string
		switch k {
		case "name":
			v, _ = strconv.Unquote(kv.Value.(*ast.BasicLit).Value)
		case "argLen", "scale":
			v = fmt.Sprint(intOf(kv.Value))
		case "reg":
			v = regOf(kv.Value).canon()
		default:
			v = strings.ReplaceAll(nodeString(fset, kv.Value), " ", "")
		}
		kvs = append(kvs, k+"="+v)
	}
	sort := slices.Clone(kvs)
	slices.Sort(sort)
	return strings.Join(sort, ";")
}

// canonOp is what genOp writes for o, in canonEntry's form.
func canonOp(o lop) string {
	kvs := []string{"name=" + o.name, fmt.Sprintf("argLen=%d", o.argLength)}
	if o.aux != "" {
		kvs = append(kvs, "auxType=aux"+o.aux)
	}
	rv := reflect.ValueOf(o.opData)
	for i := range rv.NumField() {
		if f := rv.Type().Field(i); f.Type.Kind() == reflect.Bool && rv.Field(i).Bool() {
			kvs = append(kvs, f.Name+"=true")
		}
	}
	if o.symEffect != "" {
		kvs = append(kvs, "symEffect=Sym"+strings.ReplaceAll(o.symEffect, ",", "|Sym"))
	}
	if o.generic {
		kvs = append(kvs, "generic=true")
	} else {
		if o.asm != "" {
			kvs = append(kvs, "asm="+o.pkg+".A"+o.asm)
		}
		if o.scale != 0 {
			kvs = append(kvs, fmt.Sprintf("scale=%d", o.scale))
		}
		kvs = append(kvs, "reg="+genRegInfo(o.reg).canon())
	}
	slices.Sort(kvs)
	return strings.Join(kvs, ";")
}

func checkOpGen(file string, ops []lop, blocks []lblock, arm64 *arch, simd map[string]bool) opGenNums {
	fset, f := parseGo(file)
	var opConsts, blockConsts []string
	vars := map[string]ast.Expr{}
	var firstType string
	for _, d := range f.Decls {
		g, ok := d.(*ast.GenDecl)
		if !ok {
			continue
		}
		switch g.Tok {
		case token.CONST:
			var names []string
			for _, s := range g.Specs {
				vs := s.(*ast.ValueSpec)
				if len(names) == 0 {
					firstType = ""
					if vs.Type != nil {
						firstType = nodeString(fset, vs.Type)
					}
				}
				names = append(names, vs.Names[0].Name)
			}
			switch firstType {
			case "Op":
				opConsts = names
			case "BlockKind":
				blockConsts = names
			}
		case token.VAR:
			for _, s := range g.Specs {
				vs := s.(*ast.ValueSpec)
				if len(vs.Values) == 1 {
					vars[vs.Names[0].Name] = vs.Values[0]
				}
			}
		}
	}
	if len(opConsts) == 0 || len(blockConsts) == 0 {
		log.Fatal("opGen.go: Op or BlockKind constants not found")
	}
	table := vars["opcodeTable"].(*ast.CompositeLit).Elts
	if len(table) != len(opConsts) {
		log.Fatalf("opGen.go: %d opcodeTable entries for %d Op constants", len(table), len(opConsts))
	}
	opNum := map[string]int{}
	for i, c := range opConsts {
		opNum[c] = i
	}
	var res opGenNums
	exported := map[string]bool{}
	for _, o := range ops {
		c := o.goConst()
		if o.name == "Invalid" {
			c = "OpInvalid"
		}
		i, ok := opNum[c]
		if !ok {
			log.Fatalf("opGen.go: no constant %s", c)
		}
		exported[c] = true
		res.ops = append(res.ops, i)
		if o.name == "Invalid" {
			continue
		}
		if o.archName == "ARM64" {
			res.nARM64++
		}
		got, want := canonEntry(fset, table[i].(*ast.CompositeLit)), canonOp(o)
		if got != want {
			log.Fatalf("opGen.go: entry of %s differs:\n  opGen.go: %s\n  opsgen:   %s", c, got, want)
		}
	}
	var skipped []string
	for _, c := range opConsts {
		if strings.HasPrefix(c, "OpARM64") && !exported[c] {
			if !simd[strings.TrimPrefix(c, "OpARM64")] {
				log.Fatalf("opGen.go: ARM64 op %s neither exported nor SIMD", c)
			}
			skipped = append(skipped, c)
		}
	}
	if len(skipped) != len(simd) {
		log.Fatalf("opGen.go: %d ARM64 SIMD ops, %d in simdARM64ops.go", len(skipped), len(simd))
	}

	// Block kinds: constants, blockString, AuxIntType.
	blockNum := map[string]int{}
	for i, c := range blockConsts {
		blockNum[c] = i
	}
	str := map[string]string{}
	for _, el := range vars["blockString"].(*ast.CompositeLit).Elts {
		kv := el.(*ast.KeyValueExpr)
		str[kv.Key.(*ast.Ident).Name], _ = strconv.Unquote(kv.Value.(*ast.BasicLit).Value)
	}
	auxInt := map[string]string{}
	for _, d := range f.Decls {
		fd, ok := d.(*ast.FuncDecl)
		if !ok || fd.Name.Name != "AuxIntType" {
			continue
		}
		for _, st := range fd.Body.List {
			sw, ok := st.(*ast.SwitchStmt)
			if !ok {
				continue
			}
			for _, cc := range sw.Body.List {
				cl := cc.(*ast.CaseClause)
				v, _ := strconv.Unquote(cl.Body[0].(*ast.ReturnStmt).Results[0].(*ast.BasicLit).Value)
				for _, e := range cl.List {
					auxInt[e.(*ast.Ident).Name] = v
				}
			}
		}
	}
	for _, b := range blocks {
		c := b.goConst()
		i, ok := blockNum[c]
		if !ok {
			log.Fatalf("opGen.go: no constant %s", c)
		}
		res.blocks = append(res.blocks, i)
		name := b.name
		if b.name == "Invalid" {
			name = "BlockInvalid"
		}
		if str[c] != name || auxInt[c] != b.auxIntType() {
			log.Fatalf("opGen.go: block %s: name %q / %q, AuxIntType %q / %q", c, str[c], name, auxInt[c], b.auxIntType())
		}
	}
	nb := 0
	for _, c := range blockConsts {
		if strings.HasPrefix(c, "BlockARM64") {
			nb++
		}
	}
	if nb != len(arm64.blocks) {
		log.Fatalf("opGen.go: %d ARM64 block kinds, %d exported", nb, len(arm64.blocks))
	}

	// ARM64 registers, parameter registers and masks.
	regs := vars["registersARM64"].(*ast.CompositeLit).Elts
	if len(regs) != len(arm64.regnames) {
		log.Fatalf("opGen.go: %d ARM64 registers, %d in ARM64Ops.go", len(regs), len(arm64.regnames))
	}
	for i, r := range regs {
		el := r.(*ast.CompositeLit).Elts
		name, _ := strconv.Unquote(el[2].(*ast.BasicLit).Value)
		if intOf(el[0]) != int64(i) || name != arm64.regnames[i] {
			log.Fatalf("opGen.go: register %d is %s, ARM64Ops.go has %s", i, name, arm64.regnames[i])
		}
		want := "0"
		if n := objName(name); n != "" {
			want = "arm64." + n
		}
		if got := nodeString(fset, el[1]); got != want {
			log.Fatalf("opGen.go: register %s has objNum %s, expected %s", name, got, want)
		}
	}
	ints := func(v string) []int {
		var l []int
		for _, e := range vars[v].(*ast.CompositeLit).Elts {
			l = append(l, int(intOf(e)))
		}
		return l
	}
	if !slices.Equal(ints("paramIntRegARM64"), paramRegs(arm64, arm64.ParamIntRegNames)) ||
		!slices.Equal(ints("paramFloatRegARM64"), paramRegs(arm64, arm64.ParamFloatRegNames)) {
		log.Fatal("opGen.go: ARM64 parameter registers differ")
	}
	for v, m := range map[string]regMask{"gpRegMaskARM64": arm64.gpregmask, "fpRegMaskARM64": arm64.fpregmask,
		"simdRegMaskARM64": arm64.simdregmask, "specialRegMaskARM64": arm64.specialregmask} {
		if maskOf(vars[v]) != m {
			log.Fatalf("opGen.go: %s differs", v)
		}
	}
	if intOf(vars["framepointerRegARM64"]) != int64(arm64.framepointerreg) || intOf(vars["linkRegARM64"]) != int64(arm64.linkreg) {
		log.Fatal("opGen.go: ARM64 framepointer/link register differ")
	}
	if _, ok := vars["fp32RegMaskARM64"]; ok {
		log.Fatal("opGen.go: unexpected fp32RegMaskARM64")
	}
	return res
}
