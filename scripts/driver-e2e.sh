#!/usr/bin/env bash
# End-to-end checks of the gofv driver (docs/DRIVER.md, issue #12): build std and the corpus
# programs for linux/arm64 with the driver toolchain twice — stock (no GOFV_SSA_DRIVER) and
# with the Lean pipeline through trim (GOFV_SSA_DRIVER=gofv-ssa-opt) — compare the package archives and
# linked binaries byte for byte, run every test program of both builds under
# qemu-aarch64-static and compare their output and exit status, and summarise the driver's
# per-function statistics (GOFV_SSA_DRIVER_STATS).
#
# usage: scripts/driver-e2e.sh [--mode full|mixed] [--verified] [--sets std,test,examples]
#                              [--out DIR] [-p N] [--report-only]
#
#   --mode   GOFV_SSA_DRIVER_MODE (default full)
#   --verified  the driver runs the verified pipeline (`gofv-ssa-opt --verified`, full mode only,
#            issue #189): archives and binaries are expected to differ from stock and are only
#            counted; the programs must behave as stock. The report adds the per-function
#            verdicts (`--vstats`).
#   --out    results directory (default tmp/driver-e2e-<mode>, tmp/driver-e2e-verified)
#   -p       go build -p (default 4)
#   --report-only  keep the builds in --out, only run the programs and write the report
#
# Exit status 1 (report line "- result: FAIL") when a std archive or a program binary differs
# from stock, a driver build failed, a program's output or exit status differs, a function fell
# back to the stock passes, or nothing was compared; 0 otherwise ("- result: PASS"). With
# --verified, only a failed driver build, a differing program output or exit status, or nothing
# compared fail.
#
# Toolchain: $GOFV_DRIVER_GO (default tmp/go-driver, built by
# `GOFV_GO_DRIVER=1 GOFV_GO_BUILD=$PWD/tmp/go-driver scripts/build-go.sh`, patches 0001 and 0002). Lean
# pipeline: .lake/build/bin/gofv-ssa-opt (`lake build gofv-ssa-opt`).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
gob=${GOFV_DRIVER_GO:-$root/tmp/go-driver}
opt=$root/.lake/build/bin/gofv-ssa-opt
gosrc=$root/third_party/go
mode=full sets=std,test,examples par=4 out= reportOnly=0 verified=0
while [ $# -gt 0 ]; do
  case $1 in
    --mode) mode=$2; shift 2 ;;
    --verified) verified=1; shift ;;
    --sets) sets=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    -p) par=$2; shift 2 ;;
    --report-only) reportOnly=1; shift ;;
    *) echo "usage: $0 [--mode full|mixed] [--verified] [--sets std,test,examples] [--out DIR] [-p N] [--report-only]" >&2; exit 2 ;;
  esac
done
if [ "$verified" = 1 ] && [ "$mode" != full ]; then
  echo "driver-e2e: --verified needs --mode full" >&2; exit 2
fi
label=$mode
[ "$verified" = 0 ] || label=verified
out=${out:-$root/tmp/driver-e2e-$label}
# absolute: the builds run in other directories and the compiler opens $out/lean/stats.txt
case $out in /*) ;; *) out=$PWD/$out ;; esac
[ -x "$gob/bin/go" ] || { echo "driver-e2e: no toolchain in $gob" >&2; exit 1; }
[ "$reportOnly" = 1 ] || GOFV_GO_DRIVER=1 "$root/scripts/check-toolchain.sh" "$gob" >&2 || exit 1
[ -x "$opt" ] || { echo "driver-e2e: no $opt (lake build gofv-ssa-opt)" >&2; exit 1; }
command -v qemu-aarch64-static >/dev/null || { echo "driver-e2e: qemu-aarch64-static missing" >&2; exit 1; }

mkdir -p "$root/tmp"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
export GOOS=linux GOARCH=arm64 GOFLAGS=-trimpath GOTOOLCHAIN=local GO111MODULE=off LC_ALL=C
unset GOFV_SSA_EXPORT GOFV_SSA_DRIVER GOFV_SSA_DRIVER_PKG GOFV_SSA_DRIVER_FUNC
[ "$reportOnly" = 1 ] || { rm -rf "$out"; mkdir -p "$out"; }
gocmd=("$root/scripts/memcap.sh" "$gob/bin/go")
# The driver runs $drv with the compiler's arguments (`--list`, `--from <pass> <file>`).
drv=$opt
if [ "$verified" = 1 ]; then
  drv=$out/gofv-ssa-opt-verified
  mkdir -p "$out/lean"
  printf '#!/bin/sh\nexec %q --verified --vstats %q "$@"\n' "$opt" "$out/lean/vstats.txt" >"$drv"
  chmod +x "$drv"
fi

# Same selection as scripts/export-corpus.sh.
test_progs() {
  (cd "$gosrc/test" && for f in *.go ken/*.go; do
     [ "$(head -n1 "$f")" = "// run" ] || continue
     grep -q '^//go:build\|^// +build' "$f" && continue
     echo "$f"
   done)
}

# build <variant>: std archives (go list -export) and program binaries into $out/<variant>.
build() {
  local v=$1 dir=$out/$1 cache
  cache=$(mktemp -d "$root/tmp/driver-cache.XXXXXX")
  mkdir -p "$dir/bin"
  local env=(GOCACHE="$cache")
  if [ "$v" = lean ]; then
    env+=(GOFV_SSA_DRIVER="$drv" GOFV_SSA_DRIVER_MODE="$mode" GOFV_SSA_DRIVER_STATS="$dir/stats.txt")
  fi
  if [[ ,$sets, == *,std,* ]]; then
    env "${env[@]}" "${gocmd[@]}" build -p "$par" std >>"$dir/log" 2>&1
    env "${env[@]}" "${gocmd[@]}" list -export -f '{{.ImportPath}} {{.Export}}' std 2>>"$dir/log" |
      while read -r pkg file; do
        [ -n "$file" ] || continue
        echo "$pkg $(sha256sum <"$file" | cut -c1-16)"
      done >"$dir/std.sums"
  fi
  if [[ ,$sets, == *,test,* ]]; then
    local f u
    for f in $(test_progs); do
      u=${f%.go}; u=${u//\//_}
      if (cd "$gosrc/test" && env "${env[@]}" "${gocmd[@]}" build -o "$dir/bin/test_$u" "$f") >>"$dir/log" 2>&1; then
        echo "test_$u test/$f" >>"$dir/progs"
      fi
    done
  fi
  if [[ ,$sets, == *,examples,* ]]; then
    local d u
    for d in "$root"/examples/*/; do
      u=$(basename "$d")
      (cd "$d" && env "${env[@]}" "${gocmd[@]}" build -o "$dir/bin/examples_$u" main.go) >>"$dir/log" 2>&1 &&
        echo "examples_$u examples/$u" >>"$dir/progs"
    done
  fi
  rm -rf "$cache"
}

if [ "$reportOnly" = 0 ]; then
  echo "driver-e2e: stock build" >&2
  build stock
  echo "driver-e2e: driver build (mode $label)" >&2
  build lean
fi

report=$out/report.md
{
  echo "# driver e2e ($label mode, sets $sets)"
  echo
  if [ -f "$out/stock/std.sums" ]; then
    total=$(wc -l <"$out/stock/std.sums")
    same=$(join <(sort "$out/stock/std.sums") <(sort "$out/lean/std.sums") | awk '$2 == $3' | wc -l)
    echo "- std package archives byte-identical: $same / $total"
    [ "$verified" = 1 ] || join <(sort "$out/stock/std.sums") <(sort "$out/lean/std.sums") | awk '$2 != $3 {print "  - differs: " $1}'
  fi
  if [ -f "$out/stock/progs" ]; then
    nb=0 nsame=0 nrun=0 npass=0
    nots() { sed -E 's#^[0-9]{4}/[0-9]{2}/[0-9]{2} [0-9]{2}:[0-9]{2}:[0-9]{2} ##' "$1"; }
    while read -r b src; do
      nb=$((nb + 1))
      [ -f "$out/lean/bin/$b" ] || { echo "  - $src: driver build failed"; continue; }
      if cmp -s "$out/stock/bin/$b" "$out/lean/bin/$b"; then nsame=$((nsame + 1)); elif [ "$verified" = 0 ]; then echo "  - $src: binary differs"; fi
      # run both under qemu from the program's directory (some tests read files next to them)
      d=$gosrc/test
      case $src in examples/*) d=$root/$src ;; esac
      for v in stock lean; do
        (cd "$d" && timeout 120 qemu-aarch64-static "$out/$v/bin/$b" >"$out/$v/bin/$b.out" 2>&1; echo "exit $?" >>"$out/$v/bin/$b.out") || true
      done
      nrun=$((nrun + 1))
      # log.Fatal and friends prefix the wall-clock time (test/winbatch.go): compare without it
      if cmp -s <(nots "$out/stock/bin/$b.out") <(nots "$out/lean/bin/$b.out"); then npass=$((npass + 1)); else echo "  - $src: output differs"; fi
    done <"$out/stock/progs"
    echo "- programs: $nb built; binaries byte-identical: $nsame; run under qemu: $nrun; same output and exit status as stock: $npass"
  fi
  if [ -f "$out/lean/stats.txt" ]; then
    echo
    echo "## driver statistics (GOFV_SSA_DRIVER_STATS)"
    echo
    awk -F '\t' '
      { n++
        lean = $4; sub("lean=", "", lean); stock = $5; sub("stock=", "", stock)
        if (stock == 0 && lean > 0) full++
        else if (lean > 0) part++
        else none++
        lp += lean; sp += stock
        for (i = 6; i <= NF; i++) {
          k = $i; sub(/ .*/, "", k); d = $i; sub(/^[^ ]* /, "", d)
          if (k == "error") sub(/:.*/, "\"", d)
          else if (k != "unported") d = ""
          r[k " " d]++
        }
      }
      END {
        printf "- functions compiled: %d\n", n
        printf "- every pass (number lines through trim) by Lean: %d\n", full
        printf "- some passes by Lean, some by the stock compiler (mixed mode): %d\n", part
        printf "- all passes by the stock compiler (fallback): %d\n", none
        printf "- pass runs: Lean %d, stock %d\n", lp, sp
        print "- events by kind (and pass):"
        for (k in r) printf "  - %s: %d\n", k, r[k]
      }' "$out/lean/stats.txt"
  fi
  if [ -f "$out/lean/vstats.txt" ]; then
    echo
    echo "## verified pipeline (gofv-ssa-opt --vstats; the last run of each function)"
    echo
    awk -F '\t' '
      { last[$1 "\t" $2 "\t" $3] = $4 }
      END {
        for (k in last) {
          n++; v = last[k]
          if (v == "verified") ver++
          else if (v ~ /^error/) err++
          else { sub(/^unverified /, "", v); r[v]++ }
        }
        printf "- functions: %d; fully verified: %d; pass errors: %d\n", n, ver, err
        print "- unverified, by first unverified run:"
        for (k in r) printf "  - %s: %d\n", k, r[k]
      }' "$out/lean/vstats.txt"
  fi
} >"$report"
fail=0
if [ "$verified" = 1 ]; then
  grep -qE '^  - .*: (driver build failed|output differs)$' "$report" && fail=1
else
  grep -qE '^  - (differs: |.*: (driver build failed|binary differs|output differs)$)' "$report" && fail=1
  grep -qE '^- all passes by the stock compiler \(fallback\): [1-9]' "$report" && fail=1
fi
grep -qE '^- (std package archives byte-identical: [0-9]+ / [1-9]|programs: [1-9])' "$report" || fail=1
if [ "$fail" = 0 ]; then echo "- result: PASS" >>"$report"; else echo "- result: FAIL" >>"$report"; fi
cat "$report"
exit "$fail"
