#!/usr/bin/env bash
# Regenerate GoFV/Asm/As.lean (the obj.As opcodes of compiled arm64 code, docs/PASSES3.md §1.1)
# from the pinned Go tree (docs/PINS.md) with tools/asgen.
#
# usage: scripts/gen-asm.sh          (go from $GO, default `go` on PATH)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
rev=$(git -C "$root/third_party/go" rev-parse HEAD)
tag=$(head -1 "$root/third_party/go/VERSION" 2>/dev/null || true)
mkdir -p "$root/tmp" "$root/GoFV/Asm"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
cd "$root/tools/asgen"
GOFLAGS=-mod=mod GOTOOLCHAIN=local \
  "$root/scripts/memcap.sh" "${GO:-go}" run . -go "$root/third_party/go" \
  -o "$root/GoFV/Asm/As.lean" -source "${tag:-?} ($rev)"
