import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values12

/-!
# `Slicemask` of a constant (`generic.rules:768–771`)

`(Slicemask (Const64 [x])) && x > 0 => (Const64 [-1])` and `(Slicemask (Const64 [0])) =>
(Const64 [0])`, with witnesses. `Slicemask` masks at its result's width, so the rules need its argument to be a
64-bit integer (`argShapeOk`: `int` on the 64-bit target; without it a `Const64 [65536]` typed
`int16` masks to `0`).
The 32-bit forms `:768`/`:769` (no 64-bit instance) are left out (issue #69).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

set_option hygiene false in
/-- `rule_unfold`, the argument at the 64-bit shape (`argShapeOk`), the result shape split:
`Slicemask` is `poison` at every other shape and when its argument has another width. -/
macro "slicemask_unfold" : tactic => `(tactic| (
  rule_unfold
  rw [hat] at *
  generalize e.ty [] = T at *
  cases T <;> (try simp only [Ty.width?]) <;> (try exact .poison _)
  all_goals (
    rename_i w
    simp only [GoFV.SSA.Sem.Int.slicemask, GoFV.SSA.Sem.int1, Conv.const, Val.retype]
    cases w <;> (try simp [GoFV.SSA.Sem.Val.asInt]) <;> try exact .poison _)))

/-- `generic.rules:770`: `(Slicemask (Const64 [x])) && x > 0 => (Const64 [-1])` -/
theorem r_generic_770_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_770 := by
  slicemask_unfold
  have hc : 0 < (e.auxInt [0]).toBitVec.toInt := by
    rw [Int64.toInt_toBitVec]; simpa using hcond
  have hm : (e.auxInt [0]).toBitVec.msb = false := by
    rw [BitVec.msb_eq_toInt]; simp only [decide_eq_false_iff_not]; omega
  have h0 : ¬(e.auxInt [0]).toBitVec = 0#Width.w64.bits := by
    intro h; rw [h] at hc; simp at hc
  have h1 : BitVec.ofInt Width.w64.bits (-1) = -1#Width.w64.bits := by decide
  simp only [hm, h0, h1, Bool.false_eq_true, ↓reduceIte]
  exact .int _ _

/-- `generic.rules:771`: `(Slicemask (Const64 [0])) => (Const64 [0])` -/
theorem r_generic_771_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_771 := by
  slicemask_unfold
  have h0 : (e.auxInt [0]).toBitVec = 0#Width.w64.bits := by
    simp only [DV.int.injEq] at hc
    exact BitVec.eq_of_toInt_eq (by rw [Int64.toInt_toBitVec, hc]; rfl)
  simp only [h0]
  exact .int _ _

/-- `generic.rules:770` at `x = 5`. -/
theorem inst_r_generic_770 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_770
    (PEnv.ofLists [] [] (.int .w64) [([0], 5)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_770]
  rule_eval
  rfl

/-- `generic.rules:771`. -/
theorem inst_r_generic_771 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_771
    (PEnv.ofLists [] [] (.int .w64) [([0], 0)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_771]
  rule_eval

end GoFV.Proof.Rules
