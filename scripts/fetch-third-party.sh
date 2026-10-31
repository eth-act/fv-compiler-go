#!/usr/bin/env bash
# Fetch the pinned Go source tree (docs/PINS.md) into third_party/go. Idempotent.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
tag=go1.27.3
commit=2aae1000ea1d4b28923b96db28acf4e3b99d6aff
dst=$root/third_party/go
if [ ! -d "$dst/.git" ]; then
  git clone -q --depth 1 --branch "$tag" https://go.googlesource.com/go "$dst"
fi
have=$(git -C "$dst" rev-parse HEAD)
if [ "$have" != "$commit" ]; then
  echo "third_party/go is at $have, expected $commit ($tag)" >&2
  exit 1
fi
echo "$dst"
