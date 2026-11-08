import GoFV.Proof.Rules.DivisibleGen

variable [GoFV.SSA.Sem.Addrs]

/-!
# `generic.rules:315–318` (Neq): comparison with a product by an odd constant (#69)

`divisible_inv` (`DivisibleGen.lean`).
-/

namespace GoFV.Proof.Rules

theorem r_generic_315_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_315_2 := by
  divisible_inv

theorem r_generic_316_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_316_2 := by
  divisible_inv

theorem r_generic_317_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_317_2 := by
  divisible_inv

theorem r_generic_318_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_318_2 := by
  divisible_inv

end GoFV.Proof.Rules
