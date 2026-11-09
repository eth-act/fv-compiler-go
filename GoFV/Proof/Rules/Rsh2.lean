import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Rsh` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:484`: `(Rsh64x16 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_484_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_484 := by rule_auto

/-- `generic.rules:484`: `(Rsh64x32 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_484_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_484_2 := by rule_auto

/-- `generic.rules:473`: `(Rsh64x64 x (Const64 [0])) => x` -/
theorem r_generic_473_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_473_3 := by rule_auto

/-- `generic.rules:484`: `(Rsh64x64 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_484_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_484_3 := by rule_auto

/-- `generic.rules:484`: `(Rsh64x8 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_484_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_484_4 := by rule_auto

/-- `generic.rules:494`: `(Rsh8Ux16 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_494_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_494 := by rule_auto

/-- `generic.rules:494`: `(Rsh8Ux32 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_494_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_494_2 := by rule_auto

/-- `generic.rules:474`: `(Rsh8Ux64 x (Const64 [0])) => x` -/
theorem r_generic_474_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_474_4 := by rule_auto

/-- `generic.rules:494`: `(Rsh8Ux64 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_494_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_494_3 := by rule_auto

/-- `generic.rules:519`: `(Rsh8Ux64 (Rsh8x64 x _) (Const64 <t> [7] )) => (Rsh8Ux64 x (Const64 <t> [7] ))` -/
theorem r_generic_519_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_519 := by rule_auto

/-- `generic.rules:494`: `(Rsh8Ux8 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_494_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_494_4 := by rule_auto

/-- `generic.rules:493`: `(Rsh8x16 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_493_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_493 := by rule_auto

/-- `generic.rules:493`: `(Rsh8x32 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_493_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_493_2 := by rule_auto

/-- `generic.rules:473`: `(Rsh8x64 x (Const64 [0])) => x` -/
theorem r_generic_473_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_473_4 := by rule_auto

/-- `generic.rules:493`: `(Rsh8x64 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_493_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_493_3 := by rule_auto

/-- `generic.rules:493`: `(Rsh8x8 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_493_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_493_4 := by rule_auto

end GoFV.Proof.Rules
