#!/usr/bin/env bash
# Export the parity corpus (issue #5, docs/contracts/export.md): compile a fixed selection of
# std packages, the runnable single-file programs of third_party/go/test and our examples/
# with the patched toolchain (scripts/build-go.sh) for GOOS=linux GOARCH=arm64, writing
# per-function per-pass SSA dumps outside git.
#
# usage: scripts/export-corpus.sh [--out DIR] [--sets std,test,examples] [--check-determinism]
#                                 [--no-plain] [--manifest FILE]
#
#   --out DIR             default ../gofv-corpus/<pin> next to the main checkout
#   --sets                which unit sets to export (default all three)
#   --check-determinism   export everything twice (fresh build caches) and compare digests
#   --no-plain            keep only the compressed archives (DIR/<set>.tar.zst)
#   --manifest FILE       default corpus/manifest.txt in this checkout (committed)
#
# Layout: DIR/plain/<set>/<unit>/<pkgpath>/<func>,<abi>.ssa (std: one unit "std"),
# DIR/<set>.tar.zst, DIR/stats.txt. The manifest lists every unit with its file count and a
# sha256 digest of its dumps, plus the stats table (tools/ssastats).
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
gosrc=$root/third_party/go
gob=$root/third_party/go-build
pin=2aae1000ea1d4b28923b96db28acf4e3b99d6aff
out=$(dirname "${main_root:-$root}")/gofv-corpus/${pin:0:12}
sets=std,test,examples
check=0 plain=1
manifest=$root/corpus/manifest.txt
while [ $# -gt 0 ]; do
  case $1 in
    --out) out=$2; shift 2 ;;
    --sets) sets=$2; shift 2 ;;
    --check-determinism) check=1; shift ;;
    --no-plain) plain=0; shift ;;
    --manifest) manifest=$2; shift 2 ;;
    *) echo "usage: $0 [--out DIR] [--sets std,test,examples] [--check-determinism] [--no-plain] [--manifest FILE]" >&2; exit 2 ;;
  esac
done
[ -x "$gob/bin/go" ] || { echo "export-corpus: no patched toolchain, run scripts/build-go.sh" >&2; exit 1; }

# Std packages of the corpus: small leaf packages through runtime (write barriers, nosplit),
# chosen to cover every pass. Keep sorted; changing it changes the corpus.
std_pkgs=(
  bufio bytes container/heap container/list encoding/base64 encoding/binary encoding/hex
  errors fmt hash/crc32 hash/fnv internal/bytealg maps math math/bits path regexp
  regexp/syntax runtime slices sort strconv strings sync sync/atomic text/tabwriter
  unicode unicode/utf16 unicode/utf8
)

mkdir -p "$root/tmp"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp
export GOOS=linux GOARCH=arm64 GOFLAGS=-trimpath GOTOOLCHAIN=local GO111MODULE=off
unset GOFV_SSA_FUNC GOFV_SSA_GOTEXT

# Test programs: test/*.go and test/ken/*.go whose first line is "// run" and that carry no
# build constraint; those that fail to build for linux/arm64 are listed as skipped.
test_progs() {
  (cd "$gosrc/test" && for f in *.go ken/*.go; do
     [ "$(head -n1 "$f")" = "// run" ] || continue
     grep -q '^//go:build\|^// +build' "$f" && continue
     echo "$f"
   done)
}

# export_all <dest>: one complete export into <dest>/<set>/..., logging to <dest>/log.
export_all() {
  local dest=$1 cache
  cache=$(mktemp -d "$root/tmp/corpus-cache.XXXXXX")
  rm -rf "$dest"; mkdir -p "$dest"
  local gocmd=("$root/scripts/memcap.sh" "$gob/bin/go")
  if [[ ,$sets, == *,std,* ]]; then
    local re
    re="^($(IFS='|'; echo "${std_pkgs[*]}"))\$"
    GOCACHE=$cache GOFV_SSA_EXPORT=$dest/std/std GOFV_SSA_PKG=$re \
      "${gocmd[@]}" build -p 8 -o /dev/null "${std_pkgs[@]}" >>"$dest/log" 2>&1
    echo "std std" >>"$dest/units"
  fi
  if [[ ,$sets, == *,test,* ]]; then
    local f u
    for f in $(test_progs); do
      u=${f%.go}; u=${u//\//_}
      if (cd "$gosrc/test" && GOCACHE=$cache GOFV_SSA_EXPORT=$dest/test/$u GOFV_SSA_PKG='^(main|command-line-arguments)$' \
            "${gocmd[@]}" build -o /dev/null "$f") >>"$dest/log" 2>&1; then
        echo "test $u test/$f" >>"$dest/units"
      else
        rm -rf "$dest/test/$u"
        echo "skip $u test/$f" >>"$dest/units"
      fi
    done
  fi
  if [[ ,$sets, == *,examples,* ]]; then
    local d u
    for d in "$root"/examples/*/; do
      u=$(basename "$d")
      (cd "$d" && GOCACHE=$cache GOFV_SSA_EXPORT=$dest/examples/$u GOFV_SSA_PKG='^(main|command-line-arguments)$' \
         "${gocmd[@]}" build -o /dev/null main.go) >>"$dest/log" 2>&1
      echo "examples $u examples/$u" >>"$dest/units"
    done
  fi
  rm -rf "$cache"
}

# unit_digest <dir>: sha256 over the sorted (relative path, file sha256) list.
unit_digest() {
  (cd "$1" && find . -name '*.ssa' -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum) | sha256sum | cut -c1-16
}

work=$out.new
rm -rf "$work"; mkdir -p "$work"
echo "export-corpus: exporting into $work/plain" >&2
export_all "$work/plain"
if [ "$check" = 1 ]; then
  echo "export-corpus: determinism check, second export" >&2
  export_all "$work/plain2"
  if diff -r -q "$work/plain" "$work/plain2" -x log >"$work/determinism.diff"; then
    determinism="identical ($(find "$work/plain" -name '*.ssa' | wc -l) files, two exports with fresh caches)"
  else
    determinism="DIFFERENT, see $out/determinism.diff"
  fi
  rm -rf "$work/plain2"
  echo "export-corpus: determinism: $determinism" >&2
fi

statsbin=$root/tmp/ssastats
(cd "$root/tools/ssastats" && GOOS= GOARCH= GOFLAGS= GO111MODULE=on "$root/scripts/memcap.sh" "$gob/bin/go" build -o "$statsbin" .)
"$statsbin" "$work/plain" >"$work/stats.txt"

{
  echo "# gofv parity corpus manifest (generated by scripts/export-corpus.sh; do not edit)"
  echo "go $pin"
  echo "patch $(cat "$root"/patches/go/*.patch | sha256sum | cut -c1-16)"
  echo "target GOOS=linux GOARCH=arm64 GOFLAGS=-trimpath"
  echo "sets $sets"
  [ "$check" = 1 ] && echo "determinism $determinism"
  echo
  echo "# kind unit source files digest"
  while read -r kind u src; do
    case $kind in
      skip) echo "skip $u $src - -" ;;
      std) echo "std std $(IFS=,; echo "${std_pkgs[*]}") $(find "$work/plain/std" -name '*.ssa' | wc -l) $(unit_digest "$work/plain/std")" ;;
      *) echo "$kind $u $src $(find "$work/plain/$kind/$u" -name '*.ssa' 2>/dev/null | wc -l) $(unit_digest "$work/plain/$kind/$u")" ;;
    esac
  done <"$work/plain/units"
  echo
  echo "# stats (tools/ssastats)"
  cat "$work/stats.txt"
} >"$work/manifest.txt"
mkdir -p "$(dirname "$manifest")"
cp "$work/manifest.txt" "$manifest"

for s in ${sets//,/ }; do
  [ -d "$work/plain/$s" ] || continue
  tar -C "$work/plain" -cf - "$s" | zstd -q -T4 -10 --long=27 -o "$work/$s.tar.zst"
done
[ "$plain" = 1 ] || rm -rf "$work/plain"
rm -rf "$out"; mv "$work" "$out"
echo "export-corpus: done: $out (manifest $manifest)" >&2
cat "$out/stats.txt"
