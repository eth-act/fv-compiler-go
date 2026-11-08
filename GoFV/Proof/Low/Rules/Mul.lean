import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: multiplications by a constant strength-reduced (`ARM64.rules:1043`, `1044`)

`(MUL x (MOVDconst [c])) && canMulStrengthReduce(config, c) => {mulStrengthReduce(v, x, c)}` and
its `MULW` form build `Config.mulRecipes`' linear combinations of `x` (`GoFV.Rules.Arm64.buildCombo`)
and make `v` a copy of the last. The validator checks such events by their effect
(`GoFV.Opt.LowerCheck.mulOKL`, `GoFV.Proof.Low.Val.mul_step`: the combinations compute `c` times
`x`'s register in the bits `v` keeps, and a pointer `x` makes the product `poison`), so the rules
carry no obligation of their own (`ArmRule.Mul`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.Proof.Low GoFV.Rules.Generated.ARM64

/-- `ARM64.rules:1043`: `(MUL x (MOVDconst [c])) && canMulStrengthReduce(config, c) => {mulStrengthReduce(v, x, c)}` -/
theorem r_ARM64_1043_sound : ArmRule.Checked r_ARM64_1043 := checked_mul rfl

/-- `ARM64.rules:1044`: `(MULW x (MOVDconst [c])) && v.Type.Size() <= 4 && canMulStrengthReduce32(config, int32(c)) => {mulStrengthReduce32(v, x, int32(c))}` -/
theorem r_ARM64_1044_sound : ArmRule.Checked r_ARM64_1044 := checked_mul rfl

end GoFV.Proof.Low.Rules
