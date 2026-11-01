#!/usr/bin/env bash
# Detect a branch that silently undoes work already on main (#191 reverted all of #190 after a
# rebase: the branch committed a stale tree on top of the commit that added the files).
# For every file the branch deletes or modifies relative to base, look at the last
# $FV_REVERT_WINDOW (default 40) main commits that touched it. Flag the file if the branch
# deletes it although one of them added it, or if the branch's version equals that file
# before one of them (the branch restores a stale copy). An intended revert should say so in
# the PR body; pass --allow <path> for each such file.
#
# usage: scripts/check-reverts.sh [--allow PATH]... [base-ref]   (exit 1 on findings)
set -euo pipefail
allow=()
while [ $# -gt 0 ] && [ "$1" = --allow ]; do allow+=("$2"); shift 2; done
base=${1:-origin/main}
window=${FV_REVERT_WINDOW:-40}
mb=$(git merge-base HEAD "$base")
status=0
allowed() { local a; for a in "${allow[@]}"; do [ "$a" = "$1" ] && return 0; done; return 1; }
while IFS=$'\t' read -r st f; do
  allowed "$f" && continue
  mine=$(git rev-list "$mb..HEAD" -- "$f")
  head_blob=$(git rev-parse -q --verify "HEAD:$f" || true)
  for c in $(git rev-list -n "$window" "$base" -- "$f"); do
    if [ "$st" = D ]; then
      if git diff-tree --no-commit-id --name-only -r --diff-filter=A "$c" -- "$f" | grep -q .; then
        echo "REVERT? branch deletes $f, added on main by $(git log -1 --format='%h %s' "$c" | cut -c1-70)"
        status=1; break
      fi
      continue
    fi
    old=$(git rev-parse -q --verify "$c^:$f" || true)
    if [ -n "$old" ] && [ "$head_blob" = "$old" ] && [ -n "$mine" ]; then
      echo "REVERT? $f on this branch equals its state before $(git log -1 --format='%h %s' "$c" | cut -c1-70)"
      status=1; break
    fi
  done
done < <(git diff --name-status "$mb" HEAD | awk -F'\t' '$1=="D"||$1=="M"{print $1"\t"$2}')
[ $status = 0 ] && echo "check-reverts: OK (no silent reverts of main)"
exit $status
