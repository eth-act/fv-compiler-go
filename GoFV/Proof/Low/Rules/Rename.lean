import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: atom renames (`ARM64.rules:442-449`)

`ArmRule.Rename` of the ellipsis rules renaming an atom (`renameOp`): calls and nil checks.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:442`: `(StaticCall ...) => (CALLstatic ...)` -/
theorem r_ARM64_442_sound : ArmRule.Checked r_ARM64_442 :=
  checked_rename .StaticCall .ARM64CALLstatic rfl rfl rfl rfl rfl

/-- `ARM64.rules:443`: `(ClosureCall ...) => (CALLclosure ...)` -/
theorem r_ARM64_443_sound : ArmRule.Checked r_ARM64_443 :=
  checked_rename .ClosureCall .ARM64CALLclosure rfl rfl rfl rfl rfl

/-- `ARM64.rules:444`: `(InterCall ...) => (CALLinter ...)` -/
theorem r_ARM64_444_sound : ArmRule.Checked r_ARM64_444 :=
  checked_rename .InterCall .ARM64CALLinter rfl rfl rfl rfl rfl

/-- `ARM64.rules:449`: `(NilCheck ...) => (LoweredNilCheck ...)` -/
theorem r_ARM64_449_sound : ArmRule.Checked r_ARM64_449 :=
  checked_rename .NilCheck .ARM64LoweredNilCheck rfl rfl rfl rfl rfl

end GoFV.Proof.Low.Rules
