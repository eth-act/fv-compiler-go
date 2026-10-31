#!/usr/bin/env bash
# Per-pass stock parity of every registered Lean pass on the corpus (docs/PARITY.md): builds
# `pass-parity` and runs it once over all files (each file is parsed once and every registered
# pass instance is checked), writing the markdown table to <out> (default <repo>/tmp/parity.md)
# and the mismatch reports to <out>.log. Exit status is pass-parity's (1 on any mismatch).
#
# usage: scripts/parity.sh [-j jobs] [-o out.md] [-p pass]... [corpus dir|file...]
#        default corpus: ../gofv-corpus/<pin12>/plain (the newest one if several), jobs 4
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
jobs=4
out=$root/tmp/parity.md
passes=()
while getopts "j:o:p:" opt; do
  case $opt in
    j) jobs=$OPTARG ;;
    o) out=$OPTARG ;;
    p) passes+=(--pass "$OPTARG") ;;
    *) echo "usage: $0 [-j jobs] [-o out.md] [-p pass]... [corpus...]" >&2; exit 2 ;;
  esac
done
shift $((OPTIND - 1))
if [ $# -eq 0 ]; then
  main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
  corpus=$(ls -dt "$(dirname "$main_root")"/gofv-corpus/*/plain 2>/dev/null | head -n 1)
  [ -n "$corpus" ] || { echo "parity: no corpus under ../gofv-corpus; pass one" >&2; exit 2; }
  set -- "$corpus"
fi
mkdir -p "$(dirname "$out")"
cd "$root"
scripts/memcap.sh lake build pass-parity >/dev/null
status=0
scripts/memcap.sh .lake/build/bin/pass-parity --jobs "$jobs" --max-report 20 --table "$out" \
  "${passes[@]}" "$@" >"$out.log" 2>&1 || status=$?
{ echo; echo "corpus: $*"; echo "commit: $(git rev-parse --short HEAD)"; } >>"$out"
cat "$out"
grep -c '^MISMATCH' "$out.log" >/dev/null && echo "mismatch reports: $out.log"
exit $status
