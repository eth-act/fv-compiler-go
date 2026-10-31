#!/usr/bin/env bash
# Regenerate GoFV/SSA/Op.lean from the generic op tables of the pinned Go tree (docs/PINS.md).
# The _gen op files are package main of Go's generator; they are copied with tools/opsgen
# into <repo>/tmp/opsgen and run there, so Go itself evaluates the tables. The SIMD generic
# ops (GOEXPERIMENT=simd only) are left out, see tools/opsgen/nosimd.go.
#
# usage: scripts/gen-ops.sh          (go from $GO, default `go` on PATH)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
gen=$root/third_party/go/src/cmd/compile/internal/ssa/_gen
work=$root/tmp/opsgen
rev=$(git -C "$root/third_party/go" rev-parse HEAD)
tag=$(cat "$root/third_party/go/VERSION" 2>/dev/null | head -1 || true)
rm -rf "$work"
mkdir -p "$work"
cp "$root/tools/opsgen/go.mod" "$root/tools/opsgen/opsgen.go" "$root/tools/opsgen/nosimd.go" "$work/"
for f in genericOps decOps divisibleOps divmodOps; do  # not simdgenericOps: tools/opsgen/nosimd.go
  cp "$gen/$f.go" "$work/"
done
cd "$work"
GOFLAGS=-mod=mod GOTOOLCHAIN=local \
  "$root/scripts/memcap.sh" "${GO:-go}" run . -gen "$gen" -o "$root/GoFV/SSA/Op.lean" \
  -source "Go ${tag:-?} ($rev)"
rm -rf "$work"
