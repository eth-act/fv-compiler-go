#!/usr/bin/env bash
# Axioms audit of the GoFV and GoFVTest libraries (docs/GATE.md, docs/PLAN.md §0). The verdict is
# the exit code of the compiled program `axioms-audit` (GoFVTest/AxiomsAudit.lean), which imports
# the modules without running their initializers and checks every constant they declare (every
# kind: theorems, definitions including partial/unsafe ones, opaques, axioms) with the traversal
# of Lean's `collectAxioms` (what `#print axioms` prints); `@[implemented_by]`/`@[extern]`/
# `@[export]` declarations must be allowlisted with their argument, and every imported module must
# be audited or part of the Lean toolchain. Allowed: propext, Classical.choice, Quot.sound,
# and the `_native` axioms that bv_decide/native_decide generate, listed by exact name in
# scripts/axioms-allowlist.txt with a SHA-256 pin of their statement (each checked to have the shape of
# one, of type `_ = true`; the allowlist is the trust boundary, so every line that differs from
# origin/main is printed). Anything
# else (sorryAx, a declared axiom, an unlisted _native axiom) is a violation. Not only
# GoFV/Proof: the `@[csimp]` lemmas of GoFV/Opt and GoFV/SSA decide which code the compiled
# checkers run, and GoFVTest holds the driver's executable roots.
#
# The modules must be built and up to date (`lake build GoFV GoFVTest`): the script refuses to
# audit otherwise (`lake build --no-build`), rather than read stale .oleans.
#
# usage: scripts/axioms-audit.sh [--replay | --replay-changed] [--out DIR]   (default tmp/axioms-audit)
# Writes DIR/audit.out (the program's output: VIOLATION / ALLOWLIST-ERROR / ERROR lines and the
# summary), DIR/summary.txt, DIR/stale.txt and DIR/build.txt; prints the summary. Exit 1 on a
# violation or when the audit fails.
# --replay (the nightly gate): also send every constant of the audited modules to the kernel again
# (`axioms-audit --replay`, DIR/replay.out): a declaration added under
# `set_option debug.skipKernelTC true` is in the .olean unchecked, and only a replay notices.
# The replay checks $GOFV_REPLAY_JOBS modules at a time (default: one per 4 GB of $FV_MEMCAP, so 2
# at memcap.sh's default 8G; a module whose proofs the kernel evaluates holds about 3 GB). The
# whole tree on an orb: 8.2 minutes and 14.3 GB peak RSS at FV_MEMCAP=16G (4 at a time; the
# nightly gate), 14.4 minutes and 9.0 GB at 8G, 30.5 minutes and 6.5 GB one at a time.
# --replay-changed (per PR): replay only the modules that differ from the merge base with
# origin/main and every module that imports one (`axioms-audit --replay-changed`); the whole tree
# when lakefile.toml, lean-toolchain or lake-manifest.json changed or there is no origin/main.
# Run it after the rebase onto origin/main, right before the merge: what it trusts is main.
# --print-changed: print the changed modules --replay-changed would start from, and exit.
#
# Every GoFV module and every GoFVTest module that does not define `main` must import together
# (GoFVTest/Proof/AllProof.lean checks it for GoFV/Proof), and no module may import a GoFVTest
# module that defines `main`.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
out=$root/tmp/axioms-audit
replay=0
while [ $# -gt 0 ]; do
  case $1 in
    --out) out=$2; shift 2 ;;
    --replay) replay=1; shift ;;
    --replay-changed) replay=changed; shift ;;
    --print-changed) replay=print; shift ;;
    *) echo "usage: $0 [--replay | --replay-changed | --print-changed] [--out DIR]" >&2; exit 2 ;;
  esac
done
cd "$root"
mod() { LC_ALL=C sort | sed 's|\.lean$||; s|/|.|g'; }
# the .lean files under GoFV/GoFVTest that differ from commit $1 (tracked, staged or not, and
# untracked), one per line; paths read NUL-separated and unquoted (git quotes non-ASCII paths)
changed_files() {
  { git -c core.quotePath=false diff -z --name-only --diff-filter=d "$1" -- GoFV GoFVTest
    git -c core.quotePath=false ls-files -z --others --exclude-standard -- GoFV GoFVTest
  } | tr '\0' '\n' | grep '\.lean$' || true
}
# a symlinked module's source could change with no diff under GoFV/GoFVTest
links=$(find GoFV GoFVTest -type l)
[ -z "$links" ] || { echo "axioms-audit: symlinks under GoFV/GoFVTest are not supported: $links" >&2; exit 1; }
# module names are derived from paths: a component with a dot (`GoFV/foo.bar.lean` is the module
# `GoFV.«foo.bar»`, not `GoFV.foo.bar`) or a control character would not round-trip
odd=$(find GoFV GoFVTest -name '*.*.lean' -o -name '*.*' -type d -o -name '*[[:cntrl:]]*' -o -name '* *')
[ -z "$odd" ] || { echo "axioms-audit: path names that are not module names: $odd" >&2; exit 1; }
if [ "$replay" = print ]; then
  mb=$(git merge-base origin/main HEAD)
  changed_files "$mb" | mod
  exit 0
fi
rm -rf "$out"
mkdir -p "$out"
if ! lake build --no-build GoFV GoFVTest >"$out/stale.txt" 2>&1; then
  echo "axioms-audit: the build is not up to date (run: scripts/memcap.sh lake build GoFV GoFVTest):" >&2
  grep -E '^- ' "$out/stale.txt" | head -n 10 >&2 || true
  exit 1
fi
scripts/memcap.sh lake build axioms-audit >"$out/build.txt" 2>&1 ||
  { echo "axioms-audit: building the audit program failed (see $out/build.txt)" >&2; exit 1; }
lib=$(find GoFV -name '*.lean' | mod)
[ -n "$lib" ] || { echo "axioms-audit: no GoFV modules" >&2; exit 1; }
# GoFVTest modules that define `main` (executable roots) cannot be imported together: the program
# reads each one's .olean on its own. The other GoFVTest modules are imported with the library.
roots=$(grep -lE '^(unsafe |private )?def main\b' -r GoFVTest --include='*.lean' | mod)
rest=$(find GoFVTest -name '*.lean' | mod | grep -vxF -f <(printf '%s\n' "$roots") || true)
libarg=$(printf '%s\n' "$lib" "$rest" | sed '/^$/d' | paste -sd, -)
dup=$(printf '%s\n' "$lib" "$rest" | sed '/^$/d' | sort | uniq -d)
[ -z "$dup" ] || { echo "axioms-audit: module names listed twice: $dup" >&2; exit 1; }
rootarg=$(printf '%s\n' "$roots" | sed '/^$/d' | paste -sd, -)
# every executable of the lakefile is audited (lakefile.lean, which Lake would read instead, is
# not supported)
[ ! -e lakefile.lean ] || { echo "axioms-audit: lakefile.lean is not supported" >&2; exit 1; }
exes=$(python3 -c '
import sys, tomllib
cfg = tomllib.load(open("lakefile.toml", "rb"))
for e in cfg.get("lean_exe", []):
    print(e.get("root", e["name"]))
for l in cfg.get("lean_lib", []):
    if l["name"] not in ("GoFV", "GoFVTest"):
        print("LIB " + l["name"])
')
# a here-string, not `printf … | grep -q`: under pipefail, grep exiting at its first match while
# printf still writes the ~30 KB list kills printf with SIGPIPE (status 141) and fails the check
# at random, even with 64 KB pipes (measured: PIPESTATUS (141 0) in 9 of 4,500 checks, so about
# one audit in eleven failed with "lean_exe root … is not audited" and passed on a rerun); more
# often when the machine is loaded or pipes shrink to one page past pipe-user-pages-soft
audited=$(printf '%s\n' "$lib" "$rest" "$roots")
while read -r r; do
  [ -n "$r" ] || continue
  case $r in LIB\ *) echo "axioms-audit: lean_lib ${r#LIB } is not audited" >&2; exit 1 ;; esac
  grep -qxF "$r" <<<"$audited" ||
    { echo "axioms-audit: lean_exe root $r is not audited (outside GoFV/ and GoFVTest/)" >&2; exit 1; }
done <<<"$exes"
status=0
scripts/memcap.sh lake env .lake/build/bin/axioms-audit scripts/axioms-allowlist.txt "$libarg" "$rootarg" \
  >"$out/audit.out" 2>&1 || status=$?
# kernel checking must stay on in every module (the replay re-checks only what it replays)
if grep -qi 'skipKernelTC' lakefile.toml; then
  echo "axioms-audit: lakefile.toml mentions skipKernelTC" >&2; exit 1
fi
rstatus=0
if [[ ${FV_MEMCAP:-8G} =~ ^([0-9]+)[Gg]$ ]] && [ "${BASH_REMATCH[1]}" -ge 8 ]; then
  export GOFV_REPLAY_JOBS=${GOFV_REPLAY_JOBS:-$(( BASH_REMATCH[1] / 4 ))}
else
  export GOFV_REPLAY_JOBS=${GOFV_REPLAY_JOBS:-1}
fi
if [ "$replay" = changed ]; then
  changed=""
  if mb=$(git merge-base origin/main HEAD 2>/dev/null) &&
      git diff --quiet "$mb" -- lakefile.toml lean-toolchain lake-manifest.json; then
    files=$(changed_files "$mb")
    while IFS= read -r f; do
      [ -z "$f" ] || [ -f "$f" ] || { echo "axioms-audit: changed module $f not found" >&2; exit 1; }
    done <<<"$files"
    changed=$(printf '%s\n' "$files" | sed '/^$/d' | mod | paste -sd, -)
    [ -n "$changed" ] || { replay=0; echo "replay: no module changed" >"$out/replay.out"; }
  else
    replay=1
  fi
fi
if [ "$replay" = 1 ]; then
  scripts/memcap.sh lake env .lake/build/bin/axioms-audit --replay "$libarg" "$rootarg" \
    >"$out/replay.out" 2>&1 || rstatus=$?
elif [ "$replay" = changed ]; then
  scripts/memcap.sh lake env .lake/build/bin/axioms-audit --replay-changed "$changed" "$libarg" "$rootarg" \
    >"$out/replay.out" 2>&1 || rstatus=$?
fi
{
  grep -E '^(VIOLATION|ALLOWLIST-ERROR|ERROR) ' "$out/audit.out" | head -n 50 | sed 's/^/  - /' || true
  grep -E '^(theorems|violations|RESULT)' "$out/audit.out" || true
  if [ "$status" != 0 ] && ! grep -q '^RESULT FAIL' "$out/audit.out"; then
    echo "audit failed (exit $status):"
    tail -n 5 "$out/audit.out" | cut -c1-300 | sed 's/^/  - /'
  fi
  if [ -f "$out/replay.out" ]; then
    if [ "$rstatus" = 0 ]; then
      echo "kernel replay: PASS ($(grep -E '^(replay|trusted)' "$out/replay.out" | head -n 3 | paste -sd';' -))"
    else
      echo "kernel replay: FAIL (exit $rstatus):"
      tail -n 8 "$out/replay.out" | cut -c1-300 | sed 's/^/  - /'
    fi
  fi
  if git rev-parse -q --verify origin/main >/dev/null; then
    d=$(git diff -U0 origin/main -- scripts/axioms-allowlist.txt | grep -E '^[-+][^-+]' | grep -vE '^[-+][[:space:]]*(#|$)' || true)
    [ -z "$d" ] || { echo "allowlist lines changed vs origin/main (review them: they widen what counts as proved):"; echo "$d" | sed 's/^/  /'; }
  else
    echo "allowlist: no origin/main to compare with"
  fi
} | tee "$out/summary.txt"
[ "$status" != 0 ] || status=$rstatus
exit "$status"
