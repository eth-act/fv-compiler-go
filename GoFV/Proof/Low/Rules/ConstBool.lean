import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64
import GoFV.Rules.ProvenARM64

/-!
# Lowering rule lemma: `ConstBool` (`ARM64.rules:185`)

`(ConstBool [t]) => (MOVDconst [b2i(t)])`, normalised (`ProvenARM64.b2iNorm`: Go's `b2i` is Phase 1's
`bool2int`): at the boolean shape (`topOKL`) the register's bit 0 is the boolean.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64 GoFV.Rules.ProvenARM64

/-- `r_ARM64_185` with `b2i` named `bool2int`. -/
private def r185 : Rule where
  loc := ⟨"ARM64", 185⟩
  op := .ConstBool
  vars := [⟨"t", .auxInt, .bool⟩]
  pat := (.op .ConstBool none .any (.bind 0) .any .fixed [] false)
  cond := none
  block := none
  result := .build
      [{ op := .ARM64MOVDconst, ty := none, auxInt := (some (.call "bool2int" [(.var 0)] .int64)),
         aux := none, args := [] }]
  pos := []

private theorem r185_eq : b2iNorm r_ARM64_185 = r185 := by
  rfl

private theorem r185_sound : ArmRule.Checked r185 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  rcases hwf with h | h <;> rw [h] <;> exact Refines.refl _

/-- `ARM64.rules:185`: `(ConstBool [t]) => (MOVDconst [b2i(t)])`, `b2i` as `bool2int` -/
theorem r_ARM64_185_b2i_sound : ArmRule.Checked (b2iNorm r_ARM64_185) := by
  rw [r185_eq]; exact r185_sound

end GoFV.Proof.Low.Rules
