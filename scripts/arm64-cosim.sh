#!/usr/bin/env bash
# Co-simulation of the ARM64 instruction semantics GoFV.Arm64 against qemu-aarch64-static
# (issue #552, docs/plans/semantics3.md §3 (a)).
#
# 1. `arm64-decode --words` checks the decoder round trip on the corpus' asm sections (every
#    Prog's words decode and execute to the Prog's effect; gofv-prog files, default: the
#    current quick corpus) and lists their distinct instruction words.
# 2. `arm64-cosim gen` writes N cases per decodable word (random states with edge values, the
#    word patched to fit the harness: GoFVTest/Arm64Cosim.lean).
# 3. tools/arm64cosim (built for linux/arm64) runs them under qemu-aarch64-static.
# 4. `arm64-cosim check` runs the same cases through GoFV.Arm64.step and compares registers,
#    flags, vector registers, the exit and the memory window; prints coverage per form.
#
# usage: scripts/arm64-cosim.sh [--go GO] [--n N] [--min M] [--fuzz K] [--seed S] [--words FILE] [corpus dir...]
#   --go: any Go toolchain that can cross-compile to linux/arm64 (default: `go` on PATH).
#   --n: cases per distinct word (default 4); --min: at least this many cases per form (256);
#   --fuzz: random decodable words added to the corpus' words (20000).
#   --words: reuse a word list instead of step 1.
# Work files go to tmp/arm64cosim/; kept: decode.txt (decoder round trip), report.txt
# (co-simulation coverage and mismatches), selftest.txt. Exit status 1 if either check fails.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
gob=go n=4 min=256 fuzz=20000 seed=1 words=
while [ $# -gt 0 ]; do
  case $1 in
    --go) gob=$2; shift 2 ;;
    --n) n=$2; shift 2 ;;
    --min) min=$2; shift 2 ;;
    --fuzz) fuzz=$2; shift 2 ;;
    --seed) seed=$2; shift 2 ;;
    --words) words=$2; shift 2 ;;
    --) shift; break ;;
    -*) echo "usage: $0 [--go GO] [--n N] [--min M] [--fuzz K] [--seed S] [--words FILE] [corpus dir...]" >&2; exit 2 ;;
    *) break ;;
  esac
done
dirs=("$@")
if [ ${#dirs[@]} -eq 0 ] && [ -z "$words" ]; then
  main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
  base=$(dirname "$main_root")/gofv-corpus
  pin=$(ls "$base" | head -1)
  dirs=("$base/$pin/plain")
fi
command -v qemu-aarch64-static >/dev/null || { echo "arm64-cosim: qemu-aarch64-static missing" >&2; exit 1; }

w=$root/tmp/arm64cosim
rm -rf "$w"; mkdir -p "$w"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
(cd "$root/tools/arm64cosim" &&
  GOCACHE=$w/cache GO111MODULE=off GOOS=linux GOARCH=arm64 CGO_ENABLED=0 GOTOOLCHAIN=local \
  "$root/scripts/memcap.sh" "$gob" build -trimpath -o "$w/arm64cosim" .)
rm -rf "$w/cache"
run_native() { GODEBUG=asyncpreemptoff=1 GOMAXPROCS=1 qemu-aarch64-static "$w/arm64cosim" "$@"; }
run_native -selftest >"$w/selftest.txt" || { cat "$w/selftest.txt" >&2; exit 1; }

(cd "$root" && "$root/scripts/memcap.sh" lake build arm64-cosim arm64-decode >/dev/null)
bin=$root/.lake/build/bin
status=0
if [ -z "$words" ]; then
  words=$w/words.txt
  "$root/scripts/memcap.sh" "$bin/arm64-decode" --words "$words" "${dirs[@]}" >"$w/decode.txt" \
    || status=$?
  tail -1 "$w/decode.txt"
fi
"$root/scripts/memcap.sh" "$bin/arm64-cosim" gen "$words" "$n" "$min" "$fuzz" "$seed" "$w/cases.bin"
run_native <"$w/cases.bin" >"$w/results.bin"
"$root/scripts/memcap.sh" "$bin/arm64-cosim" check "$words" "$n" "$min" "$fuzz" "$seed" "$w/results.bin" \
  >"$w/report.txt" || status=$?
rm -f "$w/cases.bin" "$w/results.bin" "$w/arm64cosim" "$w/words.txt"
tail -1 "$w/report.txt"
exit $status
