#!/usr/bin/env bash
# Differential test of the SSA semantics GoFV.SSA.run against native arm64 execution
# (issue #10, docs/plans/semantics.md §9).
#
# 1. Builds tools/semdiff/prog for linux/arm64 with the patched toolchain (docs/contracts/
#    export.md) under GOFV_SSA_EXPORT, so the binary is compiled from exactly the exported SSA.
# 2. `sem-difftest gen` writes N random/edge-case calls per function of tools/semdiff/prog.
# 3. Runs them natively under qemu-aarch64-static.
# 4. `sem-difftest run` runs every call on every exported section and compares with native.
#
# usage: scripts/sem-difftest.sh [--go <patched go binary>] [--n N] [--seed S]
#   default go: third_party/go-build/bin/go of this checkout, else of the exporter worktree.
# Work files go to tmp/semdiff/ (calls.txt, native.txt, export/).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
gob=$root/third_party/go-build/bin/go
[ -x "$gob" ] || gob=$(dirname "${main_root:-$root}")/fv-compiler-go-wt/exporter/third_party/go-build/bin/go
n=40 seed=1
while [ $# -gt 0 ]; do
  case $1 in
    --go) gob=$2; shift 2 ;;
    --n) n=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    *) echo "usage: $0 [--go GO] [--n N] [--seed S]" >&2; exit 2 ;;
  esac
done
[ -x "$gob" ] || { echo "sem-difftest: no patched toolchain (scripts/build-go.sh)" >&2; exit 1; }
command -v qemu-aarch64-static >/dev/null || { echo "sem-difftest: qemu-aarch64-static missing" >&2; exit 1; }

w=$root/tmp/semdiff
rm -rf "$w"; mkdir -p "$w"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
(cd "$root/tools/semdiff/prog" &&
  GOCACHE=$w/cache GO111MODULE=off GOFLAGS=-trimpath GOOS=linux GOARCH=arm64 GOTOOLCHAIN=local \
  GOFV_SSA_EXPORT=$w/export GOFV_SSA_PKG='^(main|command-line-arguments)$' \
  "$root/scripts/memcap.sh" "$gob" build -o "$w/prog.arm64" .)
rm -rf "$w/cache"

(cd "$root" && "$root/scripts/memcap.sh" lake build sem-difftest >/dev/null)
bin=$root/.lake/build/bin/sem-difftest
mapfile -t funcs < <(grep -o '"[A-Za-z0-9_]*":' "$root/tools/semdiff/prog/funcs.go" | tr -d '":')
"$bin" gen "$w/export/main" "$n" "$seed" "${funcs[@]}" >"$w/calls.txt"
qemu-aarch64-static "$w/prog.arm64" <"$w/calls.txt" >"$w/native.txt"
"$root/scripts/memcap.sh" "$bin" run "$w/export/main" "$w/calls.txt" "$w/native.txt"
