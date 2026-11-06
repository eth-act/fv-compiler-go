import GoFV.Proof.Low.Rules.BlockFlags

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

theorem r_ARM64_1003_sound : ArmRule.Checked r_ARM64_1003 := by
  left; arm_unfold; arm_norm
  trace_state
  all_goals sorry

theorem r_ARM64_1374_sound : ArmRule.Checked r_ARM64_1374 := by
  left; arm_unfold; arm_norm
  trace_state
  all_goals sorry

theorem r_ARM64_991_sound : ArmRule.Checked r_ARM64_991 := by
  left; arm_unfold; arm_norm
  trace_state
  all_goals sorry

end GoFV.Proof.Low.Rules
