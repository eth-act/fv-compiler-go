#!/usr/bin/env bash
# Self-test of scripts/axioms-audit.sh (docs/GATE.md): plants each kind of unsound declaration as
# a real module, builds it, runs the audit and requires it to fail with the expected report line;
# then checks that the clean tree passes. Run after `scripts/memcap.sh lake build GoFV GoFVTest`.
# Each case removes its files (and their build outputs) when it ends, also on failure.
#
# usage: scripts/axioms-audit-selftest.sh
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
allow=scripts/axioms-allowlist.txt
work=$root/tmp/axioms-audit-selftest
rm -rf "$work"; mkdir -p "$work"
cp "$allow" "$work/allowlist.orig"
planted=()
cleanup() {
  cp "$work/allowlist.orig" "$allow"
  for f in "${planted[@]}"; do
    rm -f "$f"
    m=${f%.lean}
    rm -f .lake/build/lib/lean/"$m".* .lake/build/ir/"$m".*
  done
  planted=()
}
trap cleanup EXIT
trap 'exit 130' INT TERM HUP  # exit runs the EXIT trap: planted files never stay behind
fails=0
z64=0000000000000000000000000000000000000000000000000000000000000000  # a pin nothing has
plant() { mkdir -p "$(dirname "$1")"; cat >"$1"; planted+=("$1"); }
# case NAME EXPECTED-REGEX...: build the planted modules, audit, require exit 1 and every line
case_() {
  local name=$1 mods=() w missing=""
  shift
  for f in "${planted[@]}"; do m=${f%.lean}; mods+=("${m//\//.}"); done
  if ! scripts/memcap.sh lake build "${mods[@]}" >"$work/$name.build" 2>&1; then
    echo "FAIL $name: the mutant did not build (see $work/$name.build)"; fails=$((fails + 1))
  elif scripts/axioms-audit.sh --out "$work/$name" >"$work/$name.log" 2>&1; then
    echo "FAIL $name: the audit passed"; fails=$((fails + 1))
  else
    for w in "$@"; do grep -qE "$w" "$work/$name/audit.out" || missing="$missing /$w/"; done
    if [ -n "$missing" ]; then
      echo "FAIL $name: no line matching$missing (see $work/$name/audit.out)"; fails=$((fails + 1))
    else
      echo "ok   $name"
    fi
  fi
  cleanup
}

# 1. a @[csimp] lemma outside GoFV/Proof proved by native_decide (was outside the audit's scope)
plant GoFV/Opt/ZzAuditCsimp.lean <<'EOF'
def zzSlow (n : Nat) : Nat := n + 0
def zzFast (n : Nat) : Nat := n
theorem zz_native : (2 : Nat) + 2 = 4 := by native_decide
@[csimp] theorem zzSlow_eq_zzFast : @zzSlow = @zzFast := by
  funext n; have := zz_native; simp [zzSlow, zzFast]
EOF
case_ csimp-native '^VIOLATION "zzSlow_eq_zzFast" "zz_native\._native\.native_decide\.ax_1_1"'

# 2. a declared axiom no theorem uses, and one used only by partial and unsafe definitions
plant GoFV/SSA/ZzAuditAxiom.lean <<'EOF'
axiom zzUnused : (1 : Nat) = 2
axiom zzBound : 5 < 3
def zzTbl : Array Nat := #[1, 2, 3]
partial def zzP (n : Nat) : Nat := if n = 0 then zzTbl[5]'zzBound else zzP (n - 1)
unsafe def zzU (n : Nat) : Nat := zzTbl[5]'zzBound + n
EOF
case_ axiom-unused '^VIOLATION "zzUnused" "zzUnused"' '^VIOLATION "zzP\._unsafe_rec" "zzBound"' \
  '^VIOLATION "zzU" "zzBound"'
plant GoFV/SSA/ZzAuditAxiom.lean <<'EOF'
axiom zzBound : 5 < 3
def zzTbl : Array Nat := #[1, 2, 3]
unsafe def zzU (n : Nat) : Nat := zzTbl[5]'zzBound + n
EOF
case_ axiom-unsafe '^VIOLATION "zzU" "zzBound"'

# 3. an initializer that fakes a passing run and exits before the audit decides
plant GoFV/SSA/ZzAuditInit.lean <<'EOF'
initialize do
  IO.println "theorems audited: 1"
  IO.println "violations: 0"
  IO.println "RESULT PASS"
  IO.Process.exit 0
axiom zzInitAx : (1 : Nat) = 2
theorem zz_init_uses : (1 : Nat) = 2 := zzInitAx
EOF
case_ initializer '^VIOLATION "zz_init_uses" "zzInitAx"'

# 4. a theorem name with a newline that would split a text report into an allowlisted line
plant GoFV/SSA/ZzAuditName.lean <<'EOF'
axiom zzNameAx : (1 : Nat) = 2
theorem «x GoFV.Proof.Witness.plF_pipeline._native.native_decide.ax_1_1
y» : (1 : Nat) = 2 := zzNameAx
EOF
case_ newline-name '^VIOLATION ".*\\ny»" "zzNameAx"'

# 5. a forged allowlisted axiom: the generated name, but of type False
plant GoFV/SSA/ZzAuditForge.lean <<'EOF'
axiom zzForge._native.native_decide.ax_1_1 : False
theorem zz_forged : (1 : Nat) = 2 := zzForge._native.native_decide.ax_1_1.elim
EOF
echo "zzForge._native.native_decide.ax_1_1 $z64" >>"$allow"
case_ forged-allow '^ALLOWLIST-ERROR "zzForge\._native\.native_decide\.ax_1_1": its type is not'

# 5b. a hand-written axiom of the generated shape: admitted only with its statement pinned
plant GoFV/SSA/ZzAuditForge2.lean <<'EOF'
axiom zzForge2._native.native_decide.ax_1_1 : decide False = true
theorem zz_forged2 : False := absurd (of_decide_eq_true zzForge2._native.native_decide.ax_1_1) id
EOF
echo "zzForge2._native.native_decide.ax_1_1 $z64" >>"$allow"
case_ forged-shape '^ALLOWLIST-ERROR "zzForge2\._native\.native_decide\.ax_1_1": its pin is [0-9a-f]{64}, the allowlist pins 0{64}'

# 5c. an implemented_by allowlist entry that matches no declaration
plant GoFV/SSA/ZzAuditNone.lean <<'EOF'
theorem zz_none : (1 : Nat) = 1 := rfl
EOF
echo "implemented_by zzNoSuchDecl zzNoSuchImpl $z64" >>"$allow"
case_ stale-impl-entry '^ALLOWLIST-ERROR "zzNoSuchDecl": no @\[implemented_by\] zzNoSuchImpl 0{64} declaration'

# 5d. a pinned statement that names a look-alike constant (`«zz.p»`, one name component, prints
# as `zz.p`): pin the honest statement, then swap the constant
lookalike() {
  plant GoFV/SSA/ZzAuditLook.lean <<EOF
def zz.p : Bool := true
def «zz.p» : Bool := false
axiom zzLook._native.native_decide.ax_1_1 : decide ($1 = true) = true
theorem zz_look : $1 = true := of_decide_eq_true zzLook._native.native_decide.ax_1_1
EOF
}
lookalike 'zz.p'
echo "zzLook._native.native_decide.ax_1_1 $z64" >>"$allow"
scripts/memcap.sh lake build GoFV.SSA.ZzAuditLook >"$work/look.build" 2>&1
scripts/axioms-audit.sh --out "$work/look" >"$work/look.log" 2>&1 || true
pin=$(sed -nE 's/^ALLOWLIST-ERROR "zzLook.*its pin is ([0-9a-f]{64}),.*/\1/p' "$work/look/audit.out")
cleanup
if [ -z "$pin" ]; then
  echo "FAIL lookalike: no pin printed (see $work/look/audit.out)"; fails=$((fails + 1))
else
  lookalike '«zz.p»'
  echo "zzLook._native.native_decide.ax_1_1 $pin" >>"$allow"
  case_ lookalike '^ALLOWLIST-ERROR "zzLook\._native\.native_decide\.ax_1_1": its pin is [0-9a-f]{64}, the allowlist pins '"$pin"
fi

# 5e. a pinned statement whose definition changes: the pin covers the definitions it names
pinbody() {
  plant GoFV/SSA/ZzAuditPin.lean <<EOF
def zzP : Bool := $1
axiom zzPin._native.native_decide.ax_1_1 : decide (zzP = true) = true
theorem zz_pin : zzP = true := of_decide_eq_true zzPin._native.native_decide.ax_1_1
EOF
}
pinbody true
echo "zzPin._native.native_decide.ax_1_1 $z64" >>"$allow"
scripts/memcap.sh lake build GoFV.SSA.ZzAuditPin >"$work/pin.build" 2>&1
scripts/axioms-audit.sh --out "$work/pin" >"$work/pin.log" 2>&1 || true
pin=$(sed -nE 's/^ALLOWLIST-ERROR "zzPin.*its pin is ([0-9a-f]{64}),.*/\1/p' "$work/pin/audit.out")
cleanup
if [ -z "$pin" ]; then
  echo "FAIL pin-closure: no pin printed (see $work/pin/audit.out)"; fails=$((fails + 1))
else
  pinbody false
  echo "zzPin._native.native_decide.ax_1_1 $pin" >>"$allow"
  case_ pin-closure '^ALLOWLIST-ERROR "zzPin\._native\.native_decide\.ax_1_1": its pin is [0-9a-f]{64}, the allowlist pins '"$pin"
fi

# 5f. a theorem two modules declare with the same statement: a sound copy that uses sorryAx and a
# copy the kernel never checked; `importModules` keeps one. The audit must see the sorryAx copy,
# the replay must check the unchecked one.
plant GoFV/SSA/ZzAuditDupA.lean <<'EOF'
import Lean
open Lean
run_meta do
  let v := mkApp2 (mkConst (.str .anonymous ("sorry" ++ "Ax")) [.zero]) (mkConst ``False) (mkConst ``false)
  addDecl (.thmDecl { name := `zzDup, levelParams := [], type := mkConst ``False, value := v })
EOF
plant GoFV/SSA/ZzAuditDupB.lean <<'EOF'
import Lean
open Lean
set_option debug.skipKernelTC true in
run_meta addDecl (.thmDecl { name := `zzDup, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
EOF
plant GoFV/SSA/ZzAuditDupC.lean <<'EOF'
import GoFV.SSA.ZzAuditDupB
theorem zz_boom : False := zzDup
EOF
for order in GoFV.SSA.ZzAuditDupA,GoFV.SSA.ZzAuditDupB,GoFV.SSA.ZzAuditDupC \
    GoFV.SSA.ZzAuditDupB,GoFV.SSA.ZzAuditDupC,GoFV.SSA.ZzAuditDupA; do
  if ! scripts/memcap.sh lake build GoFV.SSA.ZzAuditDupA GoFV.SSA.ZzAuditDupC >"$work/dup.build" 2>&1; then
    echo "FAIL dup-replay: the mutant did not build (see $work/dup.build)"; fails=$((fails + 1))
  elif scripts/memcap.sh lake env .lake/build/bin/axioms-audit --replay "$order" "" >"$work/dup.out" 2>&1; then
    echo "FAIL dup-replay ($order): the replay passed"; fails=$((fails + 1))
  elif ! grep -q "while replaying declaration 'zzDup" "$work/dup.out"; then
    echo "FAIL dup-replay ($order): no replay error for zzDup (see $work/dup.out)"; fails=$((fails + 1))
  else
    echo "ok   dup-replay ($order)"
  fi
done
case_ dup-audit '^VIOLATION "zz_boom" "sorryAx"'

# 6. sorryAx in the allowlist
plant GoFV/SSA/ZzAuditSorry.lean <<'EOF'
theorem zz_sorry : (1 : Nat) = 2 := sorry
EOF
echo "sorryAx $z64" >>"$allow"
case_ allow-sorry '^VIOLATION "zz_sorry" "sorryAx"'

# 7. a violation in an executable root (a GoFVTest module defining main)
plant GoFVTest/ZzAuditRoot.lean <<'EOF'
axiom zzRootAx : (1 : Nat) = 2
theorem zz_root : (1 : Nat) = 2 := zzRootAx
def main : IO Unit := pure ()
EOF
case_ exe-root '^VIOLATION "zz_root" "zzRootAx"'

# 8. an @[implemented_by] that is not allowlisted, and an executable root redeclaring a library name
plant GoFV/SSA/ZzAuditImpl.lean <<'EOF'
def zzImplFast (n : Nat) : Nat := n + 1
@[implemented_by zzImplFast] def zzImplSlow (n : Nat) : Nat := n
def zzColl : Nat := 1
EOF
echo "implemented_by zzImplSlow zzImplFast $z64" >>"$allow"  # listed, but with another body
plant GoFVTest/ZzAuditRoot2.lean <<'EOF'
def zzColl : Nat := 2
def main : IO Unit := pure ()
EOF
case_ impl-collision '^VIOLATION "zzImplSlow" "@\[implemented_by\] zzImplFast [0-9a-f]{64}"' \
  '^ERROR root constant "zzColl" also declared in LIB'

# 8b. a theorem added without the kernel (`debug.skipKernelTC`): the axioms audit cannot see it
# (no axiom), the kernel replay must. Per PR (`--replay-changed`): a change to ZzAuditSkipA
# replays ZzAuditSkipB, which imports it, on the unchanged modules. (The whole tree takes 8 to 30
# minutes: not here.)
plant GoFV/SSA/ZzAuditSkipA.lean <<'EOF'
def zzSkipA : Nat := 1
EOF
plant GoFV/SSA/ZzAuditSkipB.lean <<'EOF'
import Lean
import GoFV.SSA.ZzAuditSkipA
open Lean Meta
set_option debug.skipKernelTC true in
run_meta addDecl (.thmDecl { name := `zzSkipBad, levelParams := [], type := mkConst ``False, value := mkConst ``True.intro })
theorem zz_skip : False := zzSkipBad
EOF
mods() { find "$@" -name '*.lean' | LC_ALL=C sort | sed 's|\.lean$||; s|/|.|g'; }
roots=$(grep -lE '^(unsafe |private )?def main\b' -r GoFVTest --include='*.lean' | LC_ALL=C sort |
  sed 's|\.lean$||; s|/|.|g')
libarg=$( { mods GoFV; mods GoFVTest | grep -vxF -f <(printf '%s\n' "$roots"); } | paste -sd, -)
rootarg=$(printf '%s\n' "$roots" | paste -sd, -)
if ! scripts/memcap.sh lake build GoFV.SSA.ZzAuditSkipB >"$work/skip.build" 2>&1; then
  echo "FAIL skip-kernel: the mutant did not build (see $work/skip.build)"; fails=$((fails + 1))
elif scripts/memcap.sh lake env .lake/build/bin/axioms-audit --replay-changed GoFV.SSA.ZzAuditSkipA \
    "$libarg" "$rootarg" >"$work/skip.out" 2>&1; then
  echo "FAIL skip-kernel: the replay passed"; fails=$((fails + 1))
elif ! grep -q "while replaying declaration 'zzSkipBad'" "$work/skip.out"; then
  echo "FAIL skip-kernel: no replay error for zzSkipBad (see $work/skip.out)"; fails=$((fails + 1))
else
  echo "ok   skip-kernel"
fi
cleanup

# 8c. a new module with a non-ASCII name is a changed module for --replay-changed (git quotes such
# paths unless told not to), and a symlinked module is refused
plant GoFV/SSA/ZzAuditα.lean <<'EOF'
def zzAuditα : Nat := 1
EOF
# to a file first: `--print-changed | grep -q` under pipefail fails when grep exits before the
# list is written (SIGPIPE, as in axioms-audit.sh's exe check)
scripts/axioms-audit.sh --print-changed >"$work/changed.txt" 2>&1 || true
if grep -qxF 'GoFV.SSA.ZzAuditα' "$work/changed.txt"; then
  echo "ok   changed-nonascii"
else
  echo "FAIL changed-nonascii: GoFV.SSA.ZzAuditα not listed as changed"; fails=$((fails + 1))
fi
cleanup
ln -s ../../docs/GATE.md GoFV/SSA/ZzAuditLink.lean; planted+=(GoFV/SSA/ZzAuditLink.lean)
if scripts/axioms-audit.sh --print-changed >"$work/link.log" 2>&1; then
  echo "FAIL symlink: a symlinked module was accepted"; fails=$((fails + 1))
elif grep -q 'symlinks under GoFV/GoFVTest' "$work/link.log"; then
  echo "ok   symlink"
else
  echo "FAIL symlink: no symlink message (see $work/link.log)"; fails=$((fails + 1))
fi
cleanup

# 8d. a module with a dot in its file name (`GoFV.«…»`, not what the path suggests): refused
plant GoFV/SSA/ZzAudit.dot.lean <<'EOF'
def zzDot : Nat := 1
EOF
if scripts/axioms-audit.sh --print-changed >"$work/dot.log" 2>&1; then
  echo "FAIL dotted-name: a dotted module file name was accepted"; fails=$((fails + 1))
elif grep -q 'not module names' "$work/dot.log"; then
  echo "ok   dotted-name"
else
  echo "FAIL dotted-name: no message (see $work/dot.log)"; fails=$((fails + 1))
fi
cleanup

# 8e. an executable root importing a module the audit was not given: an error, and the full
# replay refuses to trust it
plant GoFV/SSA/ZzAuditHid.lean <<'EOF'
axiom zzHidAx : (1 : Nat) = 2
EOF
plant GoFV/SSA/ZzAuditLibH.lean <<'EOF'
theorem zz_libh : (1 : Nat) = 1 := rfl
EOF
plant GoFVTest/ZzAuditRootH.lean <<'EOF'
import GoFV.SSA.ZzAuditHid
theorem zz_hid : (1 : Nat) = 2 := zzHidAx
def main : IO Unit := pure ()
EOF
if ! scripts/memcap.sh lake build GoFVTest.ZzAuditRootH GoFV.SSA.ZzAuditLibH >"$work/hid.build" 2>&1; then
  echo "FAIL root-import: the mutant did not build (see $work/hid.build)"; fails=$((fails + 1))
else
  scripts/memcap.sh lake env .lake/build/bin/axioms-audit "$allow" GoFV.SSA.ZzAuditLibH GoFVTest.ZzAuditRootH \
    >"$work/hid.out" 2>&1 || true
  scripts/memcap.sh lake env .lake/build/bin/axioms-audit --replay "" GoFVTest.ZzAuditRootH \
    >"$work/hid.replay" 2>&1 && hr=0 || hr=$?
  if ! grep -q '^ERROR root "GoFVTest.ZzAuditRootH" imports "GoFV.SSA.ZzAuditHid"' "$work/hid.out"; then
    echo "FAIL root-import: no import error (see $work/hid.out)"; fails=$((fails + 1))
  elif [ "$hr" = 0 ]; then
    echo "FAIL root-import: the replay trusted the import"; fails=$((fails + 1))
  else
    echo "ok   root-import"
  fi
fi
cleanup

# 9. a stale build: the audit refuses rather than reading the old .olean
plant GoFV/SSA/ZzAuditStale.lean <<'EOF'
theorem zz_stale : (1 : Nat) = 1 := rfl
EOF
scripts/memcap.sh lake build GoFV.SSA.ZzAuditStale >"$work/stale.build" 2>&1
echo "axiom zzStaleAx : (1 : Nat) = 2" >>GoFV/SSA/ZzAuditStale.lean
if scripts/axioms-audit.sh --out "$work/stale" >"$work/stale.log" 2>&1; then
  echo "FAIL stale-build: the audit passed"; fails=$((fails + 1))
elif ! grep -q 'not up to date' "$work/stale.log"; then
  echo "FAIL stale-build: no 'not up to date' message (see $work/stale.log)"; fails=$((fails + 1))
else
  echo "ok   stale-build"
fi
cleanup

# 10. the clean tree passes
if scripts/axioms-audit.sh --out "$work/clean" >"$work/clean.log" 2>&1; then
  echo "ok   clean"
else
  echo "FAIL clean: the audit failed on the clean tree (see $work/clean.log)"; fails=$((fails + 1))
fi

echo "axioms-audit-selftest: $fails failure(s)"
[ "$fails" = 0 ]
