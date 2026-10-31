// Command rules2lean exports the pinned Go compiler's generic SSA rewrite rules
// (_gen/generic.rules, dec.rules, divisible.rules, divmod.rules) to Lean data under
// GoFV/Rules/Generated (docs/contracts/rules.md).
//
// It adds export.go to the pinned rulegen package with `go run -overlay`, so the export runs
// rulegen's own parser and op tables; third_party/go is not modified.
//
// usage: scripts/memcap.sh go run -C tools/rules2lean .
// (the repository root is found by walking up to lakefile.toml)
//
// env GO: go binary used for the inner build (default: "go" on PATH)
package main

import (
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
)

func main() {
	log.SetFlags(0)
	root, err := os.Getwd()
	if err != nil {
		log.Fatal(err)
	}
	for {
		if _, err := os.Stat(filepath.Join(root, "lakefile.toml")); err == nil {
			break
		}
		parent := filepath.Dir(root)
		if parent == root {
			log.Fatal("lakefile.toml not found above the working directory")
		}
		root = parent
	}
	// The worktree's third_party/go is a symlink; the go command sees the resolved path, so
	// the overlay key must use it too.
	goroot, err := filepath.EvalSymlinks(filepath.Join(root, "third_party", "go"))
	if err != nil {
		log.Fatal(err)
	}
	gen := filepath.Join(goroot, "src", "cmd", "compile", "internal", "ssa", "_gen")
	version, err := os.ReadFile(filepath.Join(goroot, "VERSION"))
	if err != nil {
		log.Fatal(err)
	}
	tmp := filepath.Join(root, "tmp", "rules2lean")
	if err := os.MkdirAll(tmp, 0755); err != nil {
		log.Fatal(err)
	}
	overlay := map[string]map[string]string{"Replace": {
		filepath.Join(gen, "zz_rules2lean.go"): filepath.Join(root, "tools", "rules2lean", "export.go"),
	}}
	ov, _ := json.Marshal(overlay)
	ovPath := filepath.Join(tmp, "overlay.json")
	if err := os.WriteFile(ovPath, ov, 0644); err != nil {
		log.Fatal(err)
	}
	goBin := os.Getenv("GO")
	if goBin == "" {
		goBin = "go"
	}
	// -outdir: should the overlay ever not apply, rulegen's own main runs and must write its
	// output to tmp, never into third_party/go.
	cmd := exec.Command(goBin, "run", "-mod=vendor", "-tags=rules2lean", "-overlay="+ovPath, ".", "-outdir="+filepath.Join(tmp, "rulegen-out"))
	cmd.Dir = gen
	cmd.Env = append(os.Environ(),
		"GOWORK=off",
		"GOFLAGS=",
		"GOFV_OUT="+filepath.Join(root, "GoFV", "Rules", "Generated"),
		"GOFV_INVENTORY="+filepath.Join(root, "docs", "contracts", "rules-inventory.md"),
		"GOFV_GOROOT="+goroot,
		"GOFV_TMP="+tmp,
		"GOFV_GOVERSION="+strings.TrimSpace(strings.SplitN(string(version), "\n", 2)[0]),
	)
	cmd.Stdout, cmd.Stderr = os.Stdout, os.Stderr
	if err := cmd.Run(); err != nil {
		fmt.Fprintln(os.Stderr, "rules2lean:", err)
		os.Exit(1)
	}
}
