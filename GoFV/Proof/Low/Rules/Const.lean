import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: constants (`ARM64.rules:182-184`)

`(Const<N> [val]) => (MOVDconst [int64(val)])` and `(ConstNil) => (MOVDconst [0])`: the 64-bit
constant is the same register (`refines_res64`), a narrow one agrees on its low bits at its own
shape (`topOKL`, `refines_top_int`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64
/-- `ARM64.rules:182`: `(Const16 [val]) => (MOVDconst [int64(val)])` -/
theorem r_ARM64_182_sound : ArmRule.Checked r_ARM64_182 := by
  left
  arm_unfold
  arm_shape
  arm_norm
  exact refines_top_int _ _ _ (by simp (disch := decide) only [arm_sem, rule_arith, Width.bits])

/-- `ARM64.rules:182`: `(Const32 [val]) => (MOVDconst [int64(val)])` -/
theorem r_ARM64_182_2_sound : ArmRule.Checked r_ARM64_182_2 := by
  left
  arm_unfold
  arm_shape
  arm_norm
  exact refines_top_int _ _ _ (by simp (disch := decide) only [arm_sem, rule_arith, Width.bits])

/-- `ARM64.rules:182`: `(Const64 [val]) => (MOVDconst [int64(val)])` -/
theorem r_ARM64_182_3_sound : ArmRule.Checked r_ARM64_182_3 := by
  left
  arm_unfold
  arm_norm
  exact refines_res64 _ _

/-- `ARM64.rules:182`: `(Const8 [val]) => (MOVDconst [int64(val)])` -/
theorem r_ARM64_182_4_sound : ArmRule.Checked r_ARM64_182_4 := by
  left
  arm_unfold
  arm_shape
  arm_norm
  exact refines_top_int _ _ _ (by simp (disch := decide) only [arm_sem, rule_arith, Width.bits])

/-- `ARM64.rules:184`: `(ConstNil) => (MOVDconst [0])` -/
theorem r_ARM64_184_sound : ArmRule.Checked r_ARM64_184 := by
  left
  arm_unfold
  arm_norm
  exact refines_res64 _ _

end GoFV.Proof.Low.Rules
