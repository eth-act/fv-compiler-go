import GoFV.Proof.Low.Rules.Cmp
import GoFV.Proof.Rules.FloatCmp

/-!
# Lowering rule lemmas: float comparisons (`ARM64.rules:244-288`)

`(Eq64F x y) => (Equal (FCMPD x y))` and its `Neq`/`Less`/`Leq` and 32-bit forms: the condition
read from `FCMP`'s flags (`Arm64.fcmpFlags`) is Phase 1's predicate on `FPCompare`'s result
(`refines_fcmp32`, `refines_fcmp64`; `Eq`/`Neq` lose `ordered` by `FloatCmp`'s `rule_sem`
lemmas).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

private theorem fval_self32 (x : BitVec Width.w32.bits) :
    Arm64.fval .w32 (.int .w32 x) = .int .w32 x := by
  simp only [Arm64.fval, Width.bits]; rw [BitVec.setWidth_eq]

private theorem fval_self64 (x : BitVec Width.w64.bits) :
    Arm64.fval .w64 (.int .w64 x) = .int .w64 x := by
  simp only [Arm64.fval, Width.bits]; rw [BitVec.setWidth_eq]

/-- A 32-bit float comparison by predicate `P` on `FPCompare`'s result (Phase 1's `FOps.cmp`/`cmpC`
after `rule_sem`) as the `CSET` of a condition `c` on `FCMP`'s flags that reads `P` (`hP`). -/
theorem refines_fcmp32 {op : Op} {c : Cond} (hop : Cond.ofOp op = some c) (P : IEEE.Cmp → Bool)
    (hP : ∀ r, c.onVal (Arm64.fcmpFlags r).toVal = some (P r)) (a b : Val) :
    Refines (((Val.asInt .w32 a).elim .poison fun x => (Val.asInt .w32 b).elim .poison fun y =>
        Val.bool (P (IEEE.compare IEEE.Fmt.b32 x y))).retypeL .bool)
      ((Arm64.cset .bool op [(Arm64.fcmp .w32 false [a, b]).retypeL Ty.flags]).retypeL .bool) := by
  rcases asInt_cases .w32 a with ha | ⟨x, rfl⟩
  · simp only [ha, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases .w32 b with hb | ⟨y, rfl⟩
  · simp only [hb, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  simp only [Val.asInt_int, Option.elim, Arm64.fcmp, Bool.false_eq_true, ite_false, List.map,
    fval_self32, GoFV.SSA.Sem.int2, retypeL_flags_toVal]
  exact refines_cset_bool hop (hP _)

/-- A 64-bit float comparison by predicate `P` on `FPCompare`'s result (Phase 1's `FOps.cmp`/`cmpC`
after `rule_sem`) as the `CSET` of a condition `c` on `FCMP`'s flags that reads `P` (`hP`). -/
theorem refines_fcmp64 {op : Op} {c : Cond} (hop : Cond.ofOp op = some c) (P : IEEE.Cmp → Bool)
    (hP : ∀ r, c.onVal (Arm64.fcmpFlags r).toVal = some (P r)) (a b : Val) :
    Refines (((Val.asInt .w64 a).elim .poison fun x => (Val.asInt .w64 b).elim .poison fun y =>
        Val.bool (P (IEEE.compare IEEE.Fmt.b64 x y))).retypeL .bool)
      ((Arm64.cset .bool op [(Arm64.fcmp .w64 false [a, b]).retypeL Ty.flags]).retypeL .bool) := by
  rcases asInt_cases .w64 a with ha | ⟨x, rfl⟩
  · simp only [ha, Option.elim, retypeL_poison]; exact .poison _
  rcases asInt_cases .w64 b with hb | ⟨y, rfl⟩
  · simp only [hb, Val.asInt_int, Option.elim, retypeL_poison]; exact .poison _
  simp only [Val.asInt_int, Option.elim, Arm64.fcmp, Bool.false_eq_true, ite_false, List.map,
    fval_self64, GoFV.SSA.Sem.int2, retypeL_flags_toVal]
  exact refines_cset_bool hop (hP _)

/-- `ARM64.rules:244`: `(Eq32F x y) => (Equal (FCMPS x y))` -/
theorem r_ARM64_244_sound : ArmRule.Checked r_ARM64_244 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp32 rfl ((· == .eq)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:245`: `(Eq64F x y) => (Equal (FCMPD x y))` -/
theorem r_ARM64_245_sound : ArmRule.Checked r_ARM64_245 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp64 rfl ((· == .eq)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:252`: `(Neq32F x y) => (NotEqual (FCMPS x y))` -/
theorem r_ARM64_252_sound : ArmRule.Checked r_ARM64_252 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp32 rfl ((· != .eq)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:252`: `(Neq64F x y) => (NotEqual (FCMPD x y))` -/
theorem r_ARM64_252_2_sound : ArmRule.Checked r_ARM64_252_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp64 rfl ((· != .eq)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:263`: `(Less32F x y) => (LessThanF (FCMPS x y))` -/
theorem r_ARM64_263_sound : ArmRule.Checked r_ARM64_263 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp32 rfl ((· == .lt)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:264`: `(Less64F x y) => (LessThanF (FCMPD x y))` -/
theorem r_ARM64_264_sound : ArmRule.Checked r_ARM64_264 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp64 rfl ((· == .lt)) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:287`: `(Leq32F x y) => (LessEqualF (FCMPS x y))` -/
theorem r_ARM64_287_sound : ArmRule.Checked r_ARM64_287 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp32 rfl (fun c => c == .lt || c == .eq) (fun r => by cases r <;> rfl) _ _

/-- `ARM64.rules:288`: `(Leq64F x y) => (LessEqualF (FCMPD x y))` -/
theorem r_ARM64_288_sound : ArmRule.Checked r_ARM64_288 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals exact refines_fcmp64 rfl (fun c => c == .lt || c == .eq) (fun r => by cases r <;> rfl) _ _

end GoFV.Proof.Low.Rules
