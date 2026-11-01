#!/usr/bin/env bash
# Keep the integrator's main checkout read-only. Agents' file tools resolve relative paths
# against it, and several stray relative-path edits landed there; with the tree read-only such
# an edit fails loudly (permission denied) instead of silently dirtying main.
# Pulls origin/main with write permission restored, then removes it again (.lake, tmp and
# third_party stay writable).
#
# usage: scripts/sync-main-checkout.sh [checkout]   (default: the main worktree of this repo)
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
main=${1:-$(git -C "$here" worktree list --porcelain | sed -n '1s/^worktree //p')}
cd "$main"
dirs() { find . \( -path ./.lake -o -path ./third_party -o -path ./tmp -o -path ./.git \) -prune -o -type d -print0; }
dirs | xargs -0 chmod u+w
git ls-files -z | xargs -0 chmod u+w
if [ -n "$(git status --porcelain --untracked-files=no)" ]; then
  echo "main checkout has local changes (a stray edit?):" >&2
  git status --short --untracked-files=no >&2
  exit 1
fi
git pull -q --rebase
git ls-files -z | xargs -0 chmod a-w
dirs | xargs -0 chmod a-w
echo "main checkout at $(git log -1 --format='%h %s' | cut -c1-80) (read-only)"
