#!/usr/bin/env bash
# Differential test of prove's poset and limit arithmetic (GoFV.Opt.Prove.{Poset,Limit})
# against Go (issue #24). tools/provediff, the compiler's poset.go and prove.go's limit code
# (pinned tree, docs/PINS.md) are copied into
# <repo>/tmp/provediff; the Go program writes random operation sequences with Go's results and
# internal poset states, and `lake exe prove-difftest` replays them in Lean.
#
# usage: scripts/prove-difftest.sh [-n cases] [-seed s]   (go from $GO, default `go`)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
pinned=$root/third_party/go/src
work=$root/tmp/provediff
go=${GO:-go}
rm -rf "$work"
mkdir -p "$work"
cp -r "$root/tools/provediff/." "$work/"
cp "$pinned/cmd/compile/internal/ssa/poset.go" "$work/ssa/poset.go"
# prove.go's limit arithmetic: from "// a limit records" up to "// a limitFact is".
{
  printf 'package ssa\n\nimport (\n\t"fmt"\n\t"math"\n\t"math/bits"\n)\n\n'
  sed -n '/^\/\/ a limit records/,/^\/\/ a limitFact is/p' "$pinned/cmd/compile/internal/ssa/prove.go" | sed '$d'
} > "$work/ssa/prove_limit.go"
cd "$work"
GOTOOLCHAIN=local "$root/scripts/memcap.sh" "$go" run . -o "$work/cases.txt" "$@"
cd "$root"
"$root/scripts/memcap.sh" lake build prove-difftest
"$root/scripts/memcap.sh" lake exe prove-difftest "$work/cases.txt"
