package main

// arm64ObjNums evaluates the cmd/internal/obj register numbers of the ARM64 registers
// (Register.objNum, written by _gen/main.go genOp as arm64.REG_<name>, arm64.REGSP, arm64.REGG,
// arm64.REGZERO, and 0 for SB). The constants are computed by go/types from the pinned
// sources: the const declarations of cmd/internal/obj/arm64/a.out.go that define them, with
// `obj.X` replaced by the declaration of X from cmd/internal/obj/util.go, checked as one
// synthetic package (the tree need not be built).

import (
	"bytes"
	"go/ast"
	"go/constant"
	"go/parser"
	"go/printer"
	"go/token"
	"go/types"
	"log"
	"path/filepath"
)

// objName is genOp's expression for register r ("" for SB, whose objNum is 0).
func objName(r string) string {
	switch r {
	case "SB":
		return ""
	case "SP":
		return "REGSP"
	case "g":
		return "REGG"
	case "ZERO":
		return "REGZERO"
	}
	return "REG_" + r
}

func arm64ObjNums(goroot string, regnames []string) []int64 {
	obj := filepath.Join(goroot, "src", "cmd", "internal", "obj")
	need := map[string]bool{}
	for _, r := range regnames {
		if n := objName(r); n != "" {
			need[n] = true
		}
	}
	var src bytes.Buffer
	src.WriteString("package objnum\n\n")
	emit := func(file string, want func(names []string) bool) {
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, file, nil, 0)
		if err != nil {
			log.Fatal(err)
		}
		for _, d := range f.Decls {
			g, ok := d.(*ast.GenDecl)
			if !ok || g.Tok != token.CONST {
				continue
			}
			var names []string
			for _, s := range g.Specs {
				for _, n := range s.(*ast.ValueSpec).Names {
					names = append(names, n.Name)
				}
			}
			if !want(names) {
				continue
			}
			// obj.X -> X (the obj declarations are emitted into the same package).
			ast.Inspect(g, func(n ast.Node) bool {
				if vs, ok := n.(*ast.ValueSpec); ok {
					for i, v := range vs.Values {
						if sel, ok := v.(*ast.SelectorExpr); ok {
							if id, ok := sel.X.(*ast.Ident); ok && id.Name == "obj" {
								vs.Values[i] = sel.Sel
							}
						}
					}
				}
				if b, ok := n.(*ast.BinaryExpr); ok {
					for _, p := range []*ast.Expr{&b.X, &b.Y} {
						if sel, ok := (*p).(*ast.SelectorExpr); ok {
							if id, ok := sel.X.(*ast.Ident); ok && id.Name == "obj" {
								*p = sel.Sel
							}
						}
					}
				}
				return true
			})
			g.Doc = nil
			if err := printer.Fprint(&src, fset, g); err != nil {
				log.Fatal(err)
			}
			src.WriteString("\n\n")
		}
	}
	emit(filepath.Join(obj, "util.go"), func(names []string) bool {
		for _, n := range names {
			if n == "RBaseARM64" {
				return true
			}
		}
		return false
	})
	emit(filepath.Join(obj, "arm64", "a.out.go"), func(names []string) bool {
		for _, n := range names {
			if need[n] {
				return true
			}
		}
		return false
	})
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "objnum.go", src.String(), 0)
	if err != nil {
		log.Fatalf("objnum: %v", err)
	}
	pkg, err := (&types.Config{}).Check("objnum", fset, []*ast.File{f}, nil)
	if err != nil {
		log.Fatalf("objnum: %v", err)
	}
	var nums []int64
	for _, r := range regnames {
		n := objName(r)
		if n == "" {
			nums = append(nums, 0)
			continue
		}
		c, ok := pkg.Scope().Lookup(n).(*types.Const)
		if !ok {
			log.Fatalf("objnum: no constant %s", n)
		}
		v, exact := constant.Int64Val(c.Val())
		if !exact {
			log.Fatalf("objnum: %s = %v", n, c.Val())
		}
		nums = append(nums, v)
	}
	return nums
}
