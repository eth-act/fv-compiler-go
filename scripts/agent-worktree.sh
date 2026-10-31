#!/usr/bin/env bash
# Create an isolated git worktree for an agent: branch agent/<name> off main, at
# ../fv-compiler-go-wt/<name>, with the pinned third_party sources symlinked. Prints the path.
# Idempotent: an existing branch or worktree is reused and completed.
#
# usage: scripts/agent-worktree.sh <name> [base-ref]
set -euo pipefail
name=$1; base=${2:-main}
root=$(cd "$(dirname "$0")/.." && pwd)
wt=$(dirname "$root")/fv-compiler-go-wt/$name
if [ ! -d "$wt" ]; then
  if git -C "$root" show-ref --verify --quiet "refs/heads/agent/$name"; then
    git -C "$root" worktree add -q "$wt" "agent/$name"
  else
    git -C "$root" worktree add -q -b "agent/$name" "$wt" "$base"
  fi
fi
mkdir -p "$wt/third_party"
for d in go go-build; do
  if [ -e "$root/third_party/$d" ] && [ ! -e "$wt/third_party/$d" ]; then
    ln -s "$root/third_party/$d" "$wt/third_party/$d"
  fi
done
echo "$wt"
