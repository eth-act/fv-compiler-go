#!/usr/bin/env bash
# Differential test of the SSA semantics GoFV.SSA.run against native arm64 execution
# (issue #10, docs/plans/semantics.md §9), and with --mach of the machine semantics runMach on the
# same functions' machine code (issue #552, docs/plans/semantics3.md §9).
#
# 1. Builds tools/semdiff/prog for linux/arm64 with the patched toolchain (docs/contracts/
#    export.md) under GOFV_SSA_EXPORT, so the binary is compiled from exactly the exported SSA
#    (and the gofv-prog files hold its machine code).
# 2. `sem-difftest gen` writes N random/edge-case calls per function of tools/semdiff/prog.
# 3. Runs them natively under qemu-aarch64-static.
# 4. `sem-difftest run` runs every call on every exported section and compares with native.
# 5. With --mach: `mach-difftest` links the functions' asm sections and runs every call under
#    runMach with the runtime hooks (GoFVTest/MachDiff.lean), comparing with native.
#
# usage: scripts/sem-difftest.sh [--go <patched go binary>] [--n N] [--seed S] [--mach]
#   default go: third_party/go-build/bin/go of this checkout (scripts/build-go.sh). The toolchain
#   must match the current patches/go (scripts/check-toolchain.sh): a stale one, e.g. built before
#   export format 4, gives spurious mismatches (recover tests "lean panicked, native returned").
# Work files go to tmp/semdiff/ (calls.txt, native.txt, export/; mach.txt with --mach).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
gob=$root/third_party/go-build/bin/go
n=40 seed=1 mach=
while [ $# -gt 0 ]; do
  case $1 in
    --go) gob=$2; shift 2 ;;
    --n) n=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    --mach) mach=1; shift ;;
    *) echo "usage: $0 [--go GO] [--n N] [--seed S] [--mach]" >&2; exit 2 ;;
  esac
done
[ -x "$gob" ] || { echo "sem-difftest: no patched toolchain at $gob (scripts/build-go.sh, or --go)" >&2; exit 1; }
"$root/scripts/check-toolchain.sh" "$gob" >&2 || exit 1
command -v qemu-aarch64-static >/dev/null || { echo "sem-difftest: qemu-aarch64-static missing" >&2; exit 1; }

w=$root/tmp/semdiff
rm -rf "$w"; mkdir -p "$w"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
(cd "$root/tools/semdiff/prog" &&
  GOCACHE=$w/cache GO111MODULE=off GOFLAGS=-trimpath GOOS=linux GOARCH=arm64 GOTOOLCHAIN=local \
  GOFV_SSA_EXPORT=$w/export GOFV_SSA_PKG='^(main|command-line-arguments)$' \
  "$root/scripts/memcap.sh" "$gob" build -o "$w/prog.arm64" .)
rm -rf "$w/cache"

(cd "$root" && "$root/scripts/memcap.sh" lake build sem-difftest ${mach:+mach-difftest} >/dev/null)
bin=$root/.lake/build/bin/sem-difftest
mapfile -t funcs < <(grep -oh '"[A-Za-z0-9_]*":' "$root"/tools/semdiff/prog/*.go | tr -d '":')
"$bin" gen "$w/export/main" "$n" "$seed" "${funcs[@]}" >"$w/calls.txt"
qemu-aarch64-static "$w/prog.arm64" <"$w/calls.txt" >"$w/native.txt"
status=0
"$root/scripts/memcap.sh" "$bin" run "$w/export/main" "$w/calls.txt" "$w/native.txt" || status=$?
if [ -n "$mach" ]; then
  "$root/scripts/memcap.sh" "$root/.lake/build/bin/mach-difftest" "$w/export/main" "$w/calls.txt" \
    "$w/native.txt" >"$w/mach.txt" || status=$?
  grep -E '^(MISMATCH|DEFINITION)' "$w/mach.txt" | head -20 || true
  tail -2 "$w/mach.txt"
fi
exit $status
