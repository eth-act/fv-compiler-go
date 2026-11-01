import GoFV.Proof.Rules.DivisibleGen

/-!
# `generic.rules:315–318` (Eq): comparison with a product by an odd constant (#69)

`divisible_inv` (`DivisibleGen.lean`).
-/

namespace GoFV.Proof.Rules

theorem r_generic_315_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_315 := by
  divisible_inv

theorem r_generic_316_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_316 := by
  divisible_inv

theorem r_generic_317_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_317 := by
  divisible_inv

theorem r_generic_318_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_318 := by
  divisible_inv

end GoFV.Proof.Rules
