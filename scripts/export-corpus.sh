#!/usr/bin/env bash
# Export a parity corpus (docs/contracts/export.md) with the patched toolchain
# (scripts/build-go.sh) for GOOS=linux GOARCH=arm64, writing per-function per-pass SSA dumps
# outside git.
#
#   quick (issue #5, the per-PR gate): a fixed selection of std packages, the runnable
#         single-file programs of third_party/go/test and our examples/;
#   full  (issue #63, the nightly gate): every package of `go list std` (internal/ and vendor/
#         included), every non-main package of `go list cmd`, and every command of cmd (one
#         unit each, their packages are all named main).
#
# usage: scripts/export-corpus.sh [--corpus quick|full] [--out DIR] [--sets SETS]
#                                 [--check-determinism] [--no-plain] [--manifest FILE]
#
#   --corpus              quick (default) or full; sets the default sets, DIR and manifest
#   --out DIR             default ../gofv-corpus/<pin12> (quick) or ../gofv-corpus/<pin12>/full
#   --sets                unit sets to export: quick std,test,examples; full stdall,cmd,cmdmain
#   --check-determinism   export everything twice (fresh build caches) and compare digests
#   --no-plain            keep only the compressed archives (DIR/<set>.tar.zst)
#   --manifest FILE       default corpus/manifest.txt (quick), corpus/manifest-full.txt (full)
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
base=$(dirname "${main_root:-$root}")/gofv-corpus/${pin:0:12}
corpus=quick out= sets= manifest=
check=0 plain=1
while [ $# -gt 0 ]; do
  case $1 in
    --corpus) corpus=$2; shift 2 ;;
    --out) out=$2; shift 2 ;;
    --sets) sets=$2; shift 2 ;;
    --check-determinism) check=1; shift ;;
    --no-plain) plain=0; shift ;;
    --manifest) manifest=$2; shift 2 ;;
    *) echo "usage: $0 [--corpus quick|full] [--out DIR] [--sets SETS] [--check-determinism] [--no-plain] [--manifest FILE]" >&2; exit 2 ;;
  esac
done
case $corpus in
  quick) : "${out:=$base}" "${sets:=std,test,examples}" "${manifest:=$root/corpus/manifest.txt}" ;;
  full) : "${out:=$base/full}" "${sets:=stdall,cmd,cmdmain}" "${manifest:=$root/corpus/manifest-full.txt}" ;;
  *) echo "export-corpus: --corpus quick|full" >&2; exit 2 ;;
esac
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
  # Full corpus: std and cmd in module mode (they are the GOROOT modules).
  if [[ ,$sets, == *,stdall,* ]]; then
    GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/stdall/std \
      "${gocmd[@]}" build -p 4 -o /dev/null std >>"$dest/log" 2>&1
    echo "stdall std std" >>"$dest/units"
  fi
  if [[ ,$sets, == *,cmd,* ]]; then
    local libs
    libs=$(GO111MODULE= GOCACHE=$cache "$gob/bin/go" list -f '{{if ne .Name "main"}}{{.ImportPath}}{{end}}' cmd)
    # shellcheck disable=SC2086
    GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/cmd/cmd GOFV_SSA_PKG='^cmd/' \
      "${gocmd[@]}" build -p 4 -o /dev/null $libs >>"$dest/log" 2>&1
    echo "cmd cmd cmd" >>"$dest/units"
  fi
  if [[ ,$sets, == *,cmdmain,* ]]; then
    local p u
    for p in $(GO111MODULE= GOCACHE=$cache "$gob/bin/go" list -f '{{if eq .Name "main"}}{{.ImportPath}}{{end}}' cmd); do
      u=${p//\//_}
      if GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/cmdmain/$u GOFV_SSA_PKG='^main$' \
           "${gocmd[@]}" build -o /dev/null "$p" >>"$dest/log" 2>&1; then
        echo "cmdmain $u $p" >>"$dest/units"
      else
        rm -rf "$dest/cmdmain/$u"
        echo "skip $u $p" >>"$dest/units"
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
  echo "corpus $corpus"
  echo "sets $sets"
  [ "$check" = 1 ] && echo "determinism $determinism"
  echo
  echo "# kind unit source files digest"
  while read -r kind u src; do
    case $kind in
      skip) echo "skip $u $src - -" ;;
      std) echo "std std $(IFS=,; echo "${std_pkgs[*]}") $(find "$work/plain/std" -name '*.ssa' | wc -l) $(unit_digest "$work/plain/std")" ;;
      stdall|cmd) echo "$kind $u $src $(find "$work/plain/$kind" -name '*.ssa' | wc -l) $(unit_digest "$work/plain/$kind")" ;;
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
# The full corpus lives inside the quick corpus directory; keep it when replacing the latter.
[ "$corpus" = quick ] && [ -d "$out/full" ] && mv "$out/full" "$work/full"
rm -rf "$out"; mv "$work" "$out"
echo "export-corpus: done: $out (manifest $manifest)" >&2
cat "$out/stats.txt"
