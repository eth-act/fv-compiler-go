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
# usage: scripts/export-corpus.sh [--corpus quick|full] [--sets SETS] [--check-determinism]
#                                 [--no-plain] [--manifest FILE] [--no-switch]
#                                 [--link-from VERSION]
#        scripts/export-corpus.sh --switch <quick|full>-v<N> [--keep-retired]
#
#   --corpus              quick (default) or full; sets the default sets and manifest
#   --sets                unit sets to export: quick std,test,examples; full stdall,cmd,cmdmain
#   --check-determinism   export everything twice (fresh build caches) and compare; the
#                         second export is compared set by set and each set is deleted right
#                         after its comparison (one export plus one set on disk at a time); a
#                         version that is not identical is never switched to
#   --link-from VERSION   after each set is exported (both exports), replace every *.ssa and
#                         *.prog file whose sha256 equals that of the same path in
#                         VERSION/plain (an existing version, e.g. full-v9) by a hard link to
#                         VERSION's file; the manifest's `link` lines count the linked, different
#                         and new files per kind (disk: unchanged dumps cost nothing)
#   --no-plain            keep only the compressed archives (<version>/<set>.tar.zst)
#   --manifest FILE       default corpus/manifest.txt (quick), corpus/manifest-full.txt (full)
#   --no-switch           export a new version but do not publish it (format changes: publish
#                         with --switch after the PR that reads the new format has merged)
#   --switch VERSION      publish an existing version (no export)
#   --keep-retired        with --switch: do not delete versions retired more than 24 hours ago
#
# Published corpora are never modified in place (docs/PARITY.md, "Corpus versions"). Each
# export writes a new version directory ../gofv-corpus/<pin12>/<kind>-v<N> (N one more than the
# highest existing version of that kind) and then switches the published names atomically:
#   ../gofv-corpus/<pin12>/plain -> quick-v<N>/plain     (quick)
#   ../gofv-corpus/<pin12>/full  -> full-v<N>            (full; readers use full/plain)
# and rewrites ../gofv-corpus/<pin12>/CURRENT ("quick quick-v<N>" / "full full-v<N>" lines). The
# previous version stays; a version that has not been current for 24 hours is deleted by
# later switches (its RETIRED file holds the time it stopped being current).
#
# Version layout: <version>/plain/<set>/<unit>/<pkgpath>/<func>,<abi>.ssa and, next to it, the
# gofv-prog companion <func>,<abi>.prog (std: one unit "std"), <version>/<set>.tar.zst,
# stats.txt, manifest.txt (also copied to the committed manifest: every unit with its .ssa and
# .prog file counts and sha256 digests of its dumps, the total sizes, plus the stats table,
# tools/ssastats), determinism.diff.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
main_root=$(git -C "$root" worktree list --porcelain | sed -n '1s/^worktree //p')
gosrc=$root/third_party/go
gob=$root/third_party/go-build
pin=2aae1000ea1d4b28923b96db28acf4e3b99d6aff
base=$(dirname "${main_root:-$root}")/gofv-corpus/${pin:0:12}
corpus=quick sets= manifest= switch_to=
check=0 plain=1 publish=1 link_from= keep_retired=0
usage="usage: $0 [--corpus quick|full] [--sets SETS] [--check-determinism] [--no-plain] [--manifest FILE] [--no-switch] [--link-from VERSION] | --switch VERSION [--keep-retired]"
while [ $# -gt 0 ]; do
  case $1 in
    --corpus) corpus=$2; shift 2 ;;
    --sets) sets=$2; shift 2 ;;
    --check-determinism) check=1; shift ;;
    --no-plain) plain=0; shift ;;
    --manifest) manifest=$2; shift 2 ;;
    --no-switch) publish=0; shift ;;
    --switch) switch_to=$2; shift 2 ;;
    --link-from) link_from=$2; shift 2 ;;
    --keep-retired) keep_retired=1; shift ;;
    *) echo "$usage" >&2; exit 2 ;;
  esac
done
case $corpus in
  quick) : "${sets:=std,test,examples}" "${manifest:=$root/corpus/manifest.txt}" ;;
  full) : "${sets:=stdall,cmd,cmdmain}" "${manifest:=$root/corpus/manifest-full.txt}" ;;
  *) echo "export-corpus: --corpus quick|full" >&2; exit 2 ;;
esac

# switch_version <version>: publish an existing version directory atomically (a new symlink
# renamed over the old name), record it in CURRENT, retire the previous version and delete
# versions retired more than 24 hours ago (unless --keep-retired).
switch_version() {
  local v=$1 kind link target prev now
  kind=${v%%-v*}
  [ -d "$base/$v" ] || { echo "export-corpus: no version $base/$v" >&2; exit 1; }
  case $kind in
    quick) link=$base/plain; target=$v/plain ;;
    full) link=$base/full; target=$v ;;
    *) echo "export-corpus: bad version $v" >&2; exit 2 ;;
  esac
  if grep -q '^determinism DIFFERENT' "$base/$v/manifest.txt" 2>/dev/null; then
    echo "export-corpus: $v is not deterministic; not switching" >&2; exit 1
  fi
  prev=$(sed -n "s/^$kind //p" "$base/CURRENT" 2>/dev/null || true)
  ln -sfn "$target" "$link.switch"
  mv -T "$link.switch" "$link"
  { grep -v "^$kind " "$base/CURRENT" 2>/dev/null || true; echo "$kind $v"; } | sort >"$base/CURRENT.new"
  mv "$base/CURRENT.new" "$base/CURRENT"
  now=$(date +%s)
  if [ -n "$prev" ] && [ "$prev" != "$v" ] && [ -d "$base/$prev" ]; then
    echo "$now" >"$base/$prev/RETIRED"
  fi
  local d r
  for d in "$base"/"$kind"-v*/; do
    d=${d%/}
    [ -f "$d/RETIRED" ] || continue
    [ "$(basename "$d")" = "$v" ] && { rm -f "$d/RETIRED"; continue; }
    r=$(cat "$d/RETIRED")
    if [ "$keep_retired" = 0 ] && [ $((now - r)) -gt 86400 ]; then rm -rf "$d"; fi
  done
  echo "export-corpus: published $v ($link -> $target)" >&2
}

if [ -n "$switch_to" ]; then
  switch_version "$switch_to"
  exit 0
fi
n=0
for d in "$base"/"$corpus"-v*; do
  [ -e "$d" ] || continue
  k=${d##*-v}; k=${k%.new}
  [[ $k =~ ^[0-9]+$ ]] && [ "$k" -gt "$n" ] && n=$k
done
version=$corpus-v$((n + 1))
out=$base/$version
if [ -n "$link_from" ]; then
  [ -d "$base/$link_from/plain" ] || { echo "export-corpus: no version $base/$link_from/plain" >&2; exit 1; }
  [ "$(stat -c %d "$base/$link_from/plain")" = "$(stat -c %d "$base")" ] ||
    { echo "export-corpus: $link_from is on another file system" >&2; exit 1; }
fi
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
    "$after_set" "$dest" std
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
    "$after_set" "$dest" test
  fi
  # Full corpus: std and cmd in module mode (they are the GOROOT modules).
  if [[ ,$sets, == *,stdall,* ]]; then
    GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/stdall/std \
      "${gocmd[@]}" build -p 4 -o /dev/null std >>"$dest/log" 2>&1
    echo "stdall std std" >>"$dest/units"
    "$after_set" "$dest" stdall
  fi
  if [[ ,$sets, == *,cmd,* ]]; then
    local libs
    libs=$(GO111MODULE= GOCACHE=$cache "$gob/bin/go" list -f '{{if and .GoFiles (ne .Name "main")}}{{.ImportPath}}{{end}}' cmd)
    # shellcheck disable=SC2086
    GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/cmd/cmd GOFV_SSA_PKG='^cmd/' \
      "${gocmd[@]}" build -p 4 -o /dev/null $libs >>"$dest/log" 2>&1
    echo "cmd cmd cmd" >>"$dest/units"
    "$after_set" "$dest" cmd
  fi
  if [[ ,$sets, == *,cmdmain,* ]]; then
    local p u
    for p in $(GO111MODULE= GOCACHE=$cache "$gob/bin/go" list -f '{{if and .GoFiles (eq .Name "main")}}{{.ImportPath}}{{end}}' cmd); do
      u=${p//\//_}
      if GO111MODULE= GOCACHE=$cache GOFV_SSA_EXPORT=$dest/cmdmain/$u GOFV_SSA_PKG='^main$' \
           "${gocmd[@]}" build -o /dev/null "$p" >>"$dest/log" 2>&1; then
        echo "cmdmain $u $p" >>"$dest/units"
      else
        rm -rf "$dest/cmdmain/$u"
        echo "skip $u $p" >>"$dest/units"
      fi
    done
    "$after_set" "$dest" cmdmain
  fi
  if [[ ,$sets, == *,examples,* ]]; then
    local d u
    for d in "$root"/examples/*/; do
      u=$(basename "$d")
      (cd "$d" && GOCACHE=$cache GOFV_SSA_EXPORT=$dest/examples/$u GOFV_SSA_PKG='^(main|command-line-arguments)$' \
         "${gocmd[@]}" build -o /dev/null main.go) >>"$dest/log" 2>&1
      echo "examples $u examples/$u" >>"$dest/units"
    done
    "$after_set" "$dest" examples
  fi
  rm -rf "$cache"
}

# link_set <dest> <set>: with --link-from, replace every *.ssa / *.prog file of <dest>/<set>
# whose sha256 equals that of the same path under $link_from/plain by a hard link to it (files
# of different sizes differ without hashing), and append "<kind> linked <n> different <n> new
# <n>" to <dest>/link.<set>.
link_set() {
  local dest=$1 set=$2
  [ -n "$link_from" ] || return 0
  : >"$dest/link.$set"
  [ -d "$dest/$set" ] || return 0
  python3 - "$dest/$set" "$base/$link_from/plain/$set" "$dest/link.$set" <<'PY'
import hashlib, os, sys
from concurrent.futures import ThreadPoolExecutor
dst, src, log = sys.argv[1:]
def digest(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.digest()
def check(rel):
    a, b = os.path.join(src, rel), os.path.join(dst, rel)
    try:
        sa = os.stat(a)
    except FileNotFoundError:
        return 'new'
    if sa.st_size != os.stat(b).st_size or digest(a) != digest(b):
        return 'different'
    tmp = b + '.gofvlink'
    os.link(a, tmp)
    os.replace(tmp, b)
    return 'linked'
for ext in ('ssa', 'prog'):
    rels = [os.path.relpath(os.path.join(d, f), dst)
            for d, _, fs in os.walk(dst) for f in fs if f.endswith('.' + ext)]
    with ThreadPoolExecutor(8) as ex:
        res = list(ex.map(check, rels))
    with open(log, 'a') as f:
        f.write(f"{ext} linked {res.count('linked')} different {res.count('different')} new {res.count('new')}\n")
PY
}

# Per-set hooks: the first export links; the second export (--check-determinism) links, then
# compares the set with the first export's and deletes it, so at most one set of the second
# export is on disk.
after_set_first() { link_set "$1" "$2"; }
after_set_second() {
  local dest=$1 set=$2
  link_set "$dest" "$set"
  if [ -d "$work/plain/$set" ] || [ -d "$dest/$set" ]; then
    diff -r -q "$work/plain/$set" "$dest/$set" >>"$work/determinism.diff" || true
  fi
  rm -rf "${dest:?}/$set"
}

# unit_digest <dir> <ext>: sha256 over the sorted (relative path, file sha256) list of the
# *.<ext> files.
unit_digest() {
  (cd "$1" && find . -name "*.$2" -print0 | LC_ALL=C sort -z | xargs -0 -r sha256sum) | sha256sum | cut -c1-16
}

# unit_cols <dir>: "<ssa files> <ssa digest> <prog files> <prog digest>" of a unit.
unit_cols() {
  local e
  for e in ssa prog; do
    printf '%s %s ' "$(find "$1" -name "*.$e" 2>/dev/null | wc -l)" "$(unit_digest "$1" "$e")"
  done | sed 's/ $//'
}

work=$out.new
rm -rf "$work"; mkdir -p "$work"
echo "export-corpus: exporting into $work/plain" >&2
after_set=after_set_first
export_all "$work/plain"
if [ "$check" = 1 ]; then
  echo "export-corpus: determinism check, second export (compared and deleted set by set)" >&2
  after_set=after_set_second
  : >"$work/determinism.diff"
  export_all "$work/plain2"
  cmp -s "$work/plain/units" "$work/plain2/units" || echo "units differ" >>"$work/determinism.diff"
  if [ ! -s "$work/determinism.diff" ]; then
    determinism="identical ($(find "$work/plain" -name '*.ssa' | wc -l) .ssa and $(find "$work/plain" -name '*.prog' | wc -l) .prog files, two exports with fresh caches)"
  else
    determinism="DIFFERENT, see $out/determinism.diff"
    publish=0
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
  echo "version $version"
  echo "sets $sets"
  [ "$check" = 1 ] && echo "determinism $determinism"
  if [ -n "$link_from" ]; then
    for s in ${sets//,/ }; do
      [ -f "$work/plain/link.$s" ] || continue
      while read -r e what1 n1 what2 n2 what3 n3; do
        echo "link $link_from $s $e $what1 $n1 $what2 $n2 $what3 $n3"
      done <"$work/plain/link.$s"
    done
  fi
  echo "bytes ssa $(find "$work/plain" -name '*.ssa' -printf '%s\n' | awk '{s+=$1} END {print s+0}') prog $(find "$work/plain" -name '*.prog' -printf '%s\n' | awk '{s+=$1} END {print s+0}')"
  echo
  echo "# kind unit source files digest progfiles progdigest (*.ssa, then the gofv-prog *.prog files)"
  while read -r kind u src; do
    case $kind in
      skip) echo "skip $u $src - - - -" ;;
      std) echo "std std $(IFS=,; echo "${std_pkgs[*]}") $(unit_cols "$work/plain/std")" ;;
      stdall|cmd) echo "$kind $u $src $(unit_cols "$work/plain/$kind")" ;;
      *) echo "$kind $u $src $(unit_cols "$work/plain/$kind/$u")" ;;
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
mv "$work" "$out"
echo "export-corpus: exported $out (manifest $manifest)" >&2
if [ "$publish" = 1 ]; then
  switch_version "$version"
else
  echo "export-corpus: not published; publish with: $0 --switch $version" >&2
fi
cat "$out/stats.txt"
