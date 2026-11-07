package main

import (
	"fmt"
	"go/ast"
	"go/build"
	"go/constant"
	"go/parser"
	"go/token"
	"go/types"
	"log"
	"path/filepath"
	"sort"
)

// loader type-checks packages of the pinned Go tree for linux/arm64 (files selected by
// go/build), declarations only (IgnoreFuncBodies), with type errors ignored: only constant
// values are wanted, and every constant the generators emit is checked to have a known
// integer value. Packages outside the allow list are not loaded (go/types then uses a fake
// package, so constants depending on them stay unknown and are reported).
type loader struct {
	goroot string
	ctx    build.Context
	fset   *token.FileSet
	allow  map[string]bool
	pkgs   map[string]*types.Package
	files  map[string][]*ast.File
	// info records the types and constant values of every package-level expression.
	info map[string]*types.Info
}

func newLoader(goroot string, allow ...string) *loader {
	ctx := build.Default
	ctx.GOROOT = goroot
	ctx.GOOS = "linux"
	ctx.GOARCH = "arm64"
	ctx.CgoEnabled = false
	ctx.Compiler = "gc"
	l := &loader{goroot: goroot, ctx: ctx, fset: token.NewFileSet(), allow: map[string]bool{},
		pkgs: map[string]*types.Package{}, files: map[string][]*ast.File{},
		info: map[string]*types.Info{}}
	for _, p := range allow {
		l.allow[p] = true
	}
	return l
}

// Import implements types.Importer.
func (l *loader) Import(path string) (*types.Package, error) {
	if path == "unsafe" {
		return types.Unsafe, nil
	}
	if !l.allow[path] {
		return nil, fmt.Errorf("asgen: %s not loaded", path)
	}
	return l.load(path), nil
}

func (l *loader) load(path string) *types.Package {
	if p, ok := l.pkgs[path]; ok {
		return p
	}
	dir := filepath.Join(l.goroot, "src", path)
	bp, err := l.ctx.ImportDir(dir, 0)
	if err != nil {
		log.Fatalf("%s: %v", path, err)
	}
	var files []*ast.File
	for _, name := range bp.GoFiles {
		f, err := parser.ParseFile(l.fset, filepath.Join(dir, name), nil, 0)
		if err != nil {
			log.Fatal(err)
		}
		files = append(files, f)
	}
	conf := types.Config{Importer: l, IgnoreFuncBodies: true, Error: func(error) {}}
	info := &types.Info{Types: map[ast.Expr]types.TypeAndValue{}}
	p, _ := conf.Check(path, l.fset, files, info)
	l.pkgs[path] = p
	l.files[path] = files
	l.info[path] = info
	return p
}

// file returns the parsed file `name` of the loaded package path.
func (l *loader) file(path, name string) *ast.File {
	l.load(path)
	for _, f := range l.files[path] {
		if filepath.Base(l.fset.Position(f.Pos()).Filename) == name {
			return f
		}
	}
	log.Fatalf("%s: no file %s", path, name)
	return nil
}

// intConst is the integer value of the package-level constant name of path.
func (l *loader) intConst(path, name string) constant.Value {
	o := l.load(path).Scope().Lookup(name)
	c, ok := o.(*types.Const)
	if !ok {
		log.Fatalf("%s.%s is not a constant", path, name)
	}
	if c.Val().Kind() != constant.Int {
		log.Fatalf("%s.%s has no known integer value (%s)", path, name, c.Val())
	}
	return c.Val()
}

// namedConst is one emitted constant: its name, value and source line.
type namedConst struct {
	name string
	val  constant.Value
	line int
}

// constBlocks returns the integer constants of the const declarations of file name of path,
// grouped by declaration, in source order, keeping those keep accepts and skipping blank
// names. Non-integer constants (strings, floats, bools) are skipped; integer constants
// without a known value are fatal.
func (l *loader) constBlocks(path, name string, keep func(block []string, n string) bool) [][]namedConst {
	f := l.file(path, name)
	scope := l.pkgs[path].Scope()
	var out [][]namedConst
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
		var block []namedConst
		for _, s := range g.Specs {
			for _, n := range s.(*ast.ValueSpec).Names {
				if n.Name == "_" || !keep(names, n.Name) {
					continue
				}
				c, ok := scope.Lookup(n.Name).(*types.Const)
				if !ok {
					log.Fatalf("%s.%s: not a constant", path, n.Name)
				}
				if b, ok := c.Type().Underlying().(*types.Basic); ok && b.Info()&types.IsInteger == 0 {
					continue
				}
				if c.Val().Kind() != constant.Int {
					log.Fatalf("%s.%s has no known integer value (%s, type %s)", path, n.Name, c.Val(), c.Type())
				}
				block = append(block, namedConst{n.Name, c.Val(), l.fset.Position(n.Pos()).Line})
			}
		}
		if len(block) > 0 {
			out = append(out, block)
		}
	}
	return out
}

// leanKeywords are Lean 4 keywords that cannot be used as plain identifiers.
var leanKeywords = func() map[string]bool {
	m := map[string]bool{}
	for _, k := range []string{"at", "by", "do", "else", "end", "fun", "from", "have", "if", "in",
		"let", "match", "namespace", "open", "show", "then", "where", "with", "def", "theorem",
		"example", "instance", "structure", "inductive", "class", "import", "section", "variable",
		"universe", "mutual", "deriving", "local", "private", "protected", "partial", "unsafe",
		"axiom", "abbrev", "macro", "syntax", "return", "for", "unless", "try", "catch", "finally",
		"break", "continue", "mut", "calc", "suffices", "obtain", "Type", "Sort", "Prop"} {
		m[k] = true
	}
	return m
}()

// leanName is the Lean identifier for the Go name n (verbatim, guillemets for keywords).
func leanName(n string) string {
	if leanKeywords[n] {
		return "«" + n + "»"
	}
	return n
}

func sortedKeys[V any](m map[string]V) []string {
	ks := make([]string, 0, len(m))
	for k := range m {
		ks = append(ks, k)
	}
	sort.Strings(ks)
	return ks
}
