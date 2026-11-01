import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Rule lemmas: `Add` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2211`: `(Add8 right:(Rsh8Ux32 x y) left:(Lsh8x32 x z:(Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2211_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2211 := by rule_auto

end GoFV.Proof.Rules
