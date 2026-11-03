import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64
import GoFV.Proof.Pass.RewriteTermDen

/-!
# Lowering rule lemmas: pointers (`ARM64.rules:306`, `308`, `1201`)

`OffPtr` as `ADDconst` (`refines_offPtr`), `Addr {sym}` as `MOVDaddr {sym}` (`refines_addr_movAddr`),
and `ADDconst [0] x` as `x` at a shape compatible with `x`'s (`refines_addP_zero`, the
`copyShapeOK` premise: the same shape, or two pointer shapes, `hasTy_copyCompat`).
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
  all_goals
    arm_norm
    exact refines_addr_movAddr _ _ _ _

/-- A value of a shape has every compatible shape (`copyCompat`: the same, or another pointer
shape). -/
theorem hasTy_copyCompat {s t : Ty} (h : GoFV.Opt.RewriteCheck.copyCompat s t = true) {v : Val}
    (hv : v.hasTy s = true) : v.hasTy t = true := by
  unfold GoFV.Opt.RewriteCheck.copyCompat at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rwa [← GoFV.Proof.Pass.Rewrite.tyEq_sound h]
  · obtain ⟨e, rfl⟩ : ∃ e, s = .ptr e := by cases s <;> simp_all
    obtain ⟨e', rfl⟩ : ∃ e', t = .ptr e' := by cases t <;> simp_all
    cases v <;> (try (rename_i w _; cases w)) <;> simp_all [Val.hasTy]

/-- `ARM64.rules:1201`: `(ADDconst [0] x) => x` -/
theorem r_ARM64_1201_sound : ArmRule.Checked r_ARM64_1201 := by
  left
  arm_unfold
  arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc]
  exact refines_addP_zero _ _ (hasTy_copyCompat hcs hty)

end GoFV.Proof.Low.Rules
