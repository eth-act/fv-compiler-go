#!/usr/bin/env bash
# Per-pass stock parity of every registered Lean pass on the corpus (docs/PARITY.md): builds
# `pass-parity` and runs it once over all files (each file is parsed once and every registered
# pass instance is checked), writing the markdown table to <out> (default <repo>/tmp/parity.md)
# and the mismatch reports to <out>.log. Exit status is pass-parity's (1 on any mismatch).
#
# usage: scripts/parity.sh [--corpus quick|full] [-j jobs] [-o out.md] [-p pass]... [corpus dir|file...]
#        default corpus: the newest ../gofv-corpus/<pin12>/plain (quick, the per-PR gate) or
#        ../gofv-corpus/<pin12>/full/plain (full, the nightly gate: all of std and cmd; issue #63)
#        (directories named exactly by a 12-hex pin; e.g. <pin12>.new being regenerated is
#        skipped), jobs 4
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
jobs=4
out=$root/tmp/parity.md
passes=()
kind=quick
usage="usage: $0 [--corpus quick|full] [-j jobs] [-o out.md] [-p pass]... [corpus...]"
while [ $# -gt 0 ]; do
  case $1 in
    --corpus) kind=$2; shift 2 ;;
    -j) jobs=$2; shift 2 ;;
    -o) out=$2; shift 2 ;;
    -p) passes+=(--pass "$2"); shift 2 ;;
    -*) echo "$usage" >&2; exit 2 ;;
    *) break ;;
  esac
done
case $kind in
  quick) sub=plain ;;
  full) sub=full/plain ;;
  *) echo "$usage" >&2; exit 2 ;;
esac
if [ $# -eq 0 ]; then
  main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
  corpus=$(ls -dt "$(dirname "$main_root")"/gofv-corpus/*/$sub 2>/dev/null \
    | grep -E "/[0-9a-f]{12}/$sub\$" | head -n 1 || true)
  [ -n "$corpus" ] || { echo "parity: no corpus under ../gofv-corpus; pass one" >&2; exit 2; }
  set -- "$corpus"
fi
mkdir -p "$(dirname "$out")"
cd "$root"
scripts/memcap.sh lake build pass-parity >/dev/null
status=0
scripts/memcap.sh .lake/build/bin/pass-parity --jobs "$jobs" --max-report 20 --table "$out" \
  --check-renumber "${passes[@]}" "$@" >"$out.log" 2>&1 || status=$?
# The corpus version (docs/PARITY.md, "Corpus versions"): CURRENT of the pin directory and the
# version directory each argument resolves to.
versions=
for c in "$@"; do
  d=$(readlink -f "$c")
  b=
  for up in "$(dirname "$c")" "$(dirname "$(dirname "$c")")"; do
    [ -f "$up/CURRENT" ] && b=$up && break
  done
  cur=$( [ -f "$b/CURRENT" ] && tr '\n' ' ' <"$b/CURRENT" || echo "-")
  versions="$versions${versions:+; }$c -> $d (CURRENT: ${cur% })"
done
{ echo; echo "corpus: $*"; echo "corpus version: $versions"; echo "commit: $(git rev-parse --short HEAD)"; } >>"$out"
cat "$out"
grep -c '^MISMATCH' "$out.log" >/dev/null && echo "mismatch reports: $out.log"
exit $status
