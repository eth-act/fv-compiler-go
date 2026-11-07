#!/usr/bin/env bash
# Regenerate GoFV/Asm/{As,Reg,OpAsm,Abi,Optab,ObjConst}.lean from the pinned Go tree (docs/PINS.md) with
# tools/asgen: the obj.As opcodes of compiled arm64 code (docs/PASSES3.md §1.1), the arm64
# a.out.go constants, opcodeTable[op].asm with the arm64/ssa.go branch tables, the
# internal/abi constants, the asm7.go tables (optab in buildop's sorted order, oprange) and the
# cmd/internal/obj link.go constants.
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
  -o "$root/GoFV/Asm/As.lean" -reg "$root/GoFV/Asm/Reg.lean" \
  -opasm "$root/GoFV/Asm/OpAsm.lean" -oplean "$root/GoFV/SSA/Op.lean" \
  -abi "$root/GoFV/Asm/Abi.lean" -optab "$root/GoFV/Asm/Optab.lean" -obj "$root/GoFV/Asm/ObjConst.lean" -source "${tag:-?} ($rev)"
