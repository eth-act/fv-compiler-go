import GoFV.Proof.Rules.DenT

/-!
# The obligation of a block rule (issue #151, `docs/proofs/rules.md`)

The terminator of an `If` block (`GoFV.SSA.Sem.stepTerm`) depends on its control only through
the boolean it holds: `true` goes to `Succs[0]`, `false` to `Succs[1]`, anything else is stuck.
A successor swap is therefore the same as negating the control, and `First` is an `If` on the
constant `true`. So a block rule `(If ctrl yes no) && cond => (K new… [swapped])` is sound when
the *value* rule on the control

* `ctrl && cond => (Not x)` for `(If x no yes)` (swapped), `ctrl && cond => x` for `(If x yes no)`,
* `ctrl && cond => (ConstBool [!swapped])` for `(First …)`,

is sound (`BlockRule.ctrlRule`, `Rule.SoundT`): the terminator after the rewrite refines the one
before (`GoFV.Proof.Pass.Rewrite.effStep`). `BlockRule.Sound` is that obligation; the generic block
rules (`generic.rules:1064–1066`) are all of this form. Other shapes (more controls, other kinds,
block aux fields) have no `ctrlRule` and cannot be proved.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.Rules

/-- The top op of a pattern (`Invalid` for a leaf). -/
def Pat.topOp : Pat → Op
  | .op o .. => o
  | _ => .Invalid

/-- `(Not x)`. -/
def notNode (x : Nat) : RNode := { op := .Not, ty := none, auxInt := none, aux := none, args := [.var x] }

/-- `(ConstBool [b])`. -/
def constNode (b : Bool) : RNode :=
  { op := .ConstBool, ty := none, auxInt := some (.lit .bool (.bool b)), aux := none, args := [] }

/-- The value rule on the control of an `If` block that the block rule `br` amounts to (see the
module doc); `none` for any other shape. -/
def BlockRule.ctrlRule (br : BlockRule) : Option Rule :=
  match br.kind, br.controls, br.auxInt, br.aux, br.newKind, br.newControls with
  | .If, [pat], .any, .any, .If, [(.var x, _)] =>
    some { loc := br.loc, op := Pat.topOp pat, vars := br.vars, pat, cond := br.cond, block := none,
           result := if br.swapSuccs then .build [notNode x] else .copy (.var x), pos := [] }
  | .If, [pat], .any, .any, .First, [] =>
    some { loc := br.loc, op := Pat.topOp pat, vars := br.vars, pat, cond := br.cond, block := none,
           result := .build [constNode (!br.swapSuccs)], pos := [] }
  | _, _, _, _, _, _ => none

/-- **The obligation of a block rule**: it is an `If` rule whose control rule (`ctrlRule`) is
sound (`Rule.SoundT`; `Rule.soundT_of_sound` for a control rule without table-evaluated
nodes). -/
def BlockRule.Sound (br : BlockRule) : Prop :=
  ∃ cr, BlockRule.ctrlRule br = some cr ∧ Rule.SoundT cr

end GoFV.Proof.Rules
