import GoFV.Proof.Rules.DivisibleU

/-!
# `divisible.rules`: unsigned divisibility, the `Neq` forms (#69)

`x != (x / c) * c` becomes `max < rotateRight(x * m, k)` (`udiv_rot_ne`, `DivisibleU.lean`).
-/

namespace GoFV.Proof.Rules

theorem r_divisible_40_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_40 := by
  divisible_u

theorem r_divisible_56_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_56 := by
  divisible_u

theorem r_divisible_72_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_72 := by
  divisible_u

theorem r_divisible_88_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_88 := by
  divisible_u

end GoFV.Proof.Rules
