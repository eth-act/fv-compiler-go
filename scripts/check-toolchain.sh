#!/usr/bin/env bash
# Check that a patched Go toolchain matches the current patches/go/*.patch: every file the
# patches touch must equal the pinned Go source with the patches applied. A stale toolchain
# (e.g. one built before export format 4 added the `deferbits` flag) silently produces wrong
# exports: three agents saw "616 recover mismatches" in sem-difftest that were only that.
#
# usage: scripts/check-toolchain.sh <patched go binary or GOROOT>   (exit 1 if stale)
#   GOFV_GO_DRIVER=1 includes the driver patch (*-gofv-driver.patch), as build-go.sh does.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
arg=${1:?usage: check-toolchain.sh <go binary or GOROOT>}
if [ -x "$arg" ] && [ ! -d "$arg" ]; then goroot=$(cd "$(dirname "$arg")/.." && pwd); else goroot=$arg; fi
src=$root/third_party/go
pin=2aae1000ea1d4b28923b96db28acf4e3b99d6aff
shopt -s nullglob
patches=()
for p in "$root"/patches/go/*.patch; do
  case $p in *-gofv-driver.patch) [ "${GOFV_GO_DRIVER:-0}" = 1 ] || continue ;; esac
  patches+=("$p")
done
[ ${#patches[@]} -gt 0 ] || { echo "check-toolchain: no patches" >&2; exit 1; }
mkdir -p "$root/tmp"
w=$(mktemp -d "$root/tmp/check-toolchain.XXXXXX")
trap 'rm -rf "$w"' EXIT
files=$(sed -n 's|^+++ b/\([^[:space:]]*\).*|\1|p' "${patches[@]}" | sort -u)
for f in $files; do
  if git -C "$src" cat-file -e "$pin:$f" 2>/dev/null; then
    mkdir -p "$w/$(dirname "$f")"; git -C "$src" show "$pin:$f" > "$w/$f"
  fi
done
for p in "${patches[@]}"; do
  git -C "$w" apply --unsafe-paths --directory= -p1 "$p" 2>/dev/null ||
    (cd "$w" && patch -p1 -s --no-backup-if-mismatch < "$p")
done
stale=0
for f in $files; do
  if [ -e "$w/$f" ]; then
    cmp -s "$w/$f" "$goroot/$f" || { echo "check-toolchain: $goroot/$f differs from the patched source" >&2; stale=1; }
  elif [ -e "$goroot/$f" ]; then
    echo "check-toolchain: $goroot/$f should not exist" >&2; stale=1
  fi
done
if [ $stale = 1 ]; then
  echo "check-toolchain: $goroot is stale; rebuild with scripts/build-go.sh (GOFV_GO_BUILD=<dir>)" >&2
  exit 1
fi
echo "check-toolchain: $goroot matches patches/go"
