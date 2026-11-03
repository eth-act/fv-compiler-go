#!/usr/bin/env bash
# Regenerate GoFV/SSA/Op.lean, GoFV/SSA/OpARM64.lean and GoFV/SSA/RegARM64.lean from the
# generic and ARM64 op tables of the pinned Go tree (docs/PINS.md). The _gen op files are
# package main of Go's generator; they are copied with tools/opsgen into <repo>/tmp/opsgen and
# run there, so Go itself evaluates the tables; the result is checked against the pinned
# opGen.go. The SIMD ops (GOEXPERIMENT=simd only) are left out, see tools/opsgen/nosimd.go.
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
cp "$root"/tools/opsgen/{go.mod,opsgen.go,opgen.go,regmask.go,nosimd.go} "$work/"
# not simdgenericOps: tools/opsgen/nosimd.go; simdARM64ops only for the names of the SIMD ops
for f in genericOps decOps divisibleOps divmodOps ARM64Ops simdARM64ops; do
  cp "$gen/$f.go" "$work/"
done
cd "$work"
GOFLAGS=-mod=mod GOTOOLCHAIN=local \
  "$root/scripts/memcap.sh" "${GO:-go}" run . -gen "$gen" -o "$root/GoFV/SSA/Op.lean" \
  -arm64 "$root/GoFV/SSA/OpARM64.lean" -regs "$root/GoFV/SSA/RegARM64.lean" \
  -source "Go ${tag:-?} ($rev)"
rm -rf "$work"
