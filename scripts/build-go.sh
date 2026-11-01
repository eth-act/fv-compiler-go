#!/usr/bin/env bash
# Build the patched Go toolchain (the parity oracle, docs/contracts/export.md) in
# third_party/go-build: a fresh copy of the pinned third_party/go (docs/PINS.md) with
# patches/go/*.patch applied in name order, built by make.bash under scripts/memcap.sh.
#
# usage: scripts/build-go.sh            full rebuild (fresh copy, patches, make.bash; a few minutes)
#        scripts/build-go.sh --compile  rebuild cmd/compile from the current go-build tree (keeps
#                                       edits made there; refresh the patch with --diff first)
#        scripts/build-go.sh --repatch  re-copy and re-patch only the files the patches touch,
#                                       then rebuild cmd/compile (discards edits in go-build)
#        scripts/build-go.sh --diff     print the current go-build changes against the pinned
#                                       tree for the patched paths (to refresh a patch file:
#                                       write to tmp/ first, then copy; the paths are read from
#                                       the patches, so `--diff > patches/go/0001-…` empties it)
#
# Build directory: $GOFV_GO_BUILD, default third_party/go-build (the parity oracle).
# Patches: patches/go/*.patch in name order, except the driver patch (*-gofv-driver.patch,
# docs/DRIVER.md), which only GOFV_GO_DRIVER=1 adds: the oracle is the exporter alone. Driver
# toolchain: GOFV_GO_DRIVER=1 GOFV_GO_BUILD=$PWD/tmp/go-driver scripts/build-go.sh
# Bootstrap: $GOROOT_BOOTSTRAP, default /home/kev/work/go (go1.26), else `go env GOROOT`.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
src=$root/third_party/go
dst=${GOFV_GO_BUILD:-$root/third_party/go-build}  # GOFV_GO_BUILD: build elsewhere (e.g. a driver toolchain)
pin=2aae1000ea1d4b28923b96db28acf4e3b99d6aff
mode=${1:-full}

[ -d "$src/.git" ] || [ -f "$src/.git" ] || { echo "build-go: $src missing (scripts/fetch-third-party.sh)" >&2; exit 1; }
head=$(git -C "$src" rev-parse HEAD)
[ "$head" = "$pin" ] || { echo "build-go: $src is at $head, pin is $pin" >&2; exit 1; }

shopt -s nullglob
patches=()
for p in "$root"/patches/go/*.patch; do
  case $p in *-gofv-driver.patch) [ "${GOFV_GO_DRIVER:-0}" = 1 ] || continue ;; esac
  patches+=("$p")
done
[ ${#patches[@]} -gt 0 ] || { echo "build-go: no patches/go/*.patch" >&2; exit 1; }
# Paths touched by the patches (relative to the Go root), from their +++ headers.
touched() {
  sed -n 's|^+++ b/\([^[:space:]]*\).*|\1|p' "${patches[@]}" | sort -u
}

apply_patches() {
  for p in "${patches[@]}"; do
    git -C "$dst" apply --unsafe-paths --directory= -p1 "$p" 2>/dev/null ||
      (cd "$dst" && patch -p1 -s --no-backup-if-mismatch < "$p")
  done
}

if [ "$mode" = --diff ]; then
  rc=0
  for f in $(touched); do
    if [ -e "$src/$f" ]; then a=$src/$f; else a=/dev/null; fi
    diff -u --label "a/$f" --label "b/$f" "$a" "$dst/$f" || rc=$?
  done
  [ "$rc" -le 1 ] || exit "$rc"
  exit 0
fi

export GOROOT_BOOTSTRAP=${GOROOT_BOOTSTRAP:-/home/kev/work/go}
[ -x "$GOROOT_BOOTSTRAP/bin/go" ] || GOROOT_BOOTSTRAP=$(go env GOROOT)
mkdir -p "$root/tmp"
export TMPDIR=$root/tmp GOTMPDIR=$root/tmp

case "$mode" in
  full)
    rm -rf "$dst.new"
    mkdir -p "$dst.new"
    git -C "$src" archive --format=tar "$pin" | tar -x -C "$dst.new"
    rm -rf "$dst"
    mv "$dst.new" "$dst"
    apply_patches
    (cd "$dst/src" && GOCACHE=$root/tmp/go-build-cache "$root/scripts/memcap.sh" ./make.bash)
    ;;
  --compile)
    [ -x "$dst/bin/go" ] || { echo "build-go: no toolchain in $dst yet; run without --compile" >&2; exit 1; }
    (cd "$dst/src" && GOCACHE=$root/tmp/go-build-cache "$root/scripts/memcap.sh" "$dst/bin/go" install cmd/compile)
    ;;
  --repatch)
    [ -x "$dst/bin/go" ] || { echo "build-go: no toolchain in $dst yet; run without --repatch" >&2; exit 1; }
    for f in $(touched); do
      if git -C "$src" cat-file -e "$pin:$f" 2>/dev/null; then
        git -C "$src" show "$pin:$f" > "$dst/$f"
      else
        rm -f "$dst/$f"
      fi
    done
    apply_patches
    (cd "$dst/src" && GOCACHE=$root/tmp/go-build-cache "$root/scripts/memcap.sh" "$dst/bin/go" install cmd/compile)
    ;;
  *) echo "usage: $0 [--compile|--repatch|--diff]" >&2; exit 2 ;;
esac
"$dst/bin/go" version
