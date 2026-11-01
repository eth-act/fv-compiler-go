#!/usr/bin/env bash
# Stock sccp's map-order nondeterminism (docs/PARITY.md, "Randomized map order"): export
# main.go <n> times (default 16) with the patched toolchain, print the distinct post-sccp
# predecessor lists of f's contested block, and run `pass-parity --pass sccp` on all exports
# (expect 100%, with the runs whose order differs from the port's counted as "order replayed").
#
# usage: tests/sccp-order/run.sh [n] [go-build dir]   (default: <repo>/third_party/go-build)
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
n=${1:-16}
gob=${2:-$root/third_party/go-build}
[ -x "$gob/bin/go" ] || { echo "sccp-order: no patched toolchain at $gob (scripts/build-go.sh)" >&2; exit 1; }
out=$root/tmp/sccp-order
rm -rf "$out"; mkdir -p "$out"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp GOOS=linux GOARCH=arm64 GOFLAGS=-trimpath \
  GOTOOLCHAIN=local GO111MODULE=off
unset GOFV_SSA_FUNC GOFV_SSA_GOTEXT
for k in $(seq 1 "$n"); do
  cache=$(mktemp -d "$root/tmp/sccp-order-cache.XXXXXX")
  (cd "$here" && GOCACHE=$cache GOFV_SSA_EXPORT=$out/$k GOFV_SSA_PKG='^(main|command-line-arguments)$' \
    "$root/scripts/memcap.sh" "$gob/bin/go" build -o /dev/null main.go)
  rm -rf "$cache"
done
echo "post-sccp Preds of f's contested block (count, line):"
for k in $(seq 1 "$n"); do
  sed -n '/^pass [0-9]* "sccp"$/,/^pass /p' "$out/$k/main/f,1.ssa" | grep '^b b17 '
done | sort | uniq -c
cd "$root"
scripts/memcap.sh lake build pass-parity >/dev/null
scripts/memcap.sh .lake/build/bin/pass-parity --pass sccp "$out"
