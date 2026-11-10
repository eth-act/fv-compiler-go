#!/usr/bin/env bash
# Scan the last $1 (default 60) commits of a ref (default HEAD) for squash merges that silently
# undid earlier work, as #191 did to #190: a commit that deletes a file added by one of the
# previous 8 commits, or that sets a file back to exactly its state before the previous commit
# that touched it. A commit whose message says "revert" is skipped (intended revert), and so is
# a commit listed (short hash, first column) in scripts/reverts-ack.txt together with the issue
# that tracks restoring the lost work, or, for an intended revert (check-reverts.sh --allow), the
# PR that says why.
# Used by the nightly gate (docs/GATE.md); scripts/check-reverts.sh is the per-PR check.
#
# usage: scripts/scan-history-reverts.sh [count] [ref]   (exit 1 on findings)
set -euo pipefail
count=${1:-60}; ref=${2:-HEAD}
ack=$(cd "$(dirname "$0")" && pwd)/reverts-ack.txt
status=0
for c in $(git rev-list -n "$count" --no-merges "$ref"); do
  git log -1 --format=%s "$c" | grep -qi revert && continue
  # an ack line starts with the commit's short hash, 7 or more hex digits (some lines use 8)
  [ -f "$ack" ] && grep -q "^$(git rev-parse --short=7 "$c")[0-9a-f]*\b" "$ack" && continue
  while IFS=$'\t' read -r st f; do
    if [ "$st" = D ]; then
      a=$(git log -1 --format=%H --diff-filter=A "$c^" -- "$f" || true)
      if [ -n "$a" ] && [ "$(git rev-list --count "$a..$c")" -le 8 ]; then
        echo "REVERT? $(git log -1 --format='%h %s' "$c" | cut -c1-60): deletes $f added by $(git log -1 --format='%h' "$a")"
        status=1
      fi
    else
      x=$(git log -1 --format=%H "$c^" -- "$f" || true)
      [ -z "$x" ] && continue
      old=$(git rev-parse -q --verify "$x^:$f" || true)
      if [ -n "$old" ] && [ "$(git rev-parse -q --verify "$c:$f")" = "$old" ]; then
        echo "REVERT? $(git log -1 --format='%h %s' "$c" | cut -c1-60): restores $f to before $(git log -1 --format='%h' "$x")"
        status=1
      fi
    fi
  # -M: a rename (git's default 50% similarity, e.g. each composition lift's Obj/Gxx.lean => Obj/Gyy.lean)
  # is status R, neither a deletion nor a restore
  done < <(git diff-tree --no-commit-id --name-status -r -M "$c" | awk -F'\t' '$1=="D"||$1=="M"')
done
[ $status = 0 ] && echo "scan-history-reverts: OK (last $count commits)"
exit $status
