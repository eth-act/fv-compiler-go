import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: pointers (`ARM64.rules:306`, `308`, `1201`)

`OffPtr` as `ADDconst` (`refines_offPtr`), `Addr {sym}` as `MOVDaddr {sym}` (`refines_addr_movAddr`),
and `ADDconst [0] x` as `x` at `x`'s shape (`refines_addP_zero`, the `copyShapeOK` premise).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64
/-- `ARM64.rules:306`: `(OffPtr [off] ptr) => (ADDconst [off] ptr)` -/
theorem r_ARM64_306_sound : ArmRule.Checked r_ARM64_306 := by
  left
  arm_unfold
  arm_shape
  arm_norm
  exact refines_offPtr _ _ _

/-- `ARM64.rules:308`: `(Addr {sym} base) => (MOVDaddr {sym} base)` -/
theorem r_ARM64_308_sound : ArmRule.Checked r_ARM64_308 := by
  left
  arm_unfold
  arm_shape
  arm_norm
  exact refines_addr_movAddr _ _ _ _

/-- `ARM64.rules:1201`: `(ADDconst [0] x) => x` -/
theorem r_ARM64_1201_sound : ArmRule.Checked r_ARM64_1201 := by
  left
  arm_unfold
  arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc, hcs.symm]
  exact refines_addP_zero _ _ hty

end GoFV.Proof.Low.Rules
