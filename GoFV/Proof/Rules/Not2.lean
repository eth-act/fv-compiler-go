import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `Not` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Not` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:400`: `(Not (Less8 x y)) => (Leq8 y x)` -/
theorem r_generic_400_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400_4 := by rule_auto

/-- `generic.rules:401`: `(Not (Less64U x y)) => (Leq64U y x)` -/
theorem r_generic_401_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_401 := by rule_auto

/-- `generic.rules:401`: `(Not (Less32U x y)) => (Leq32U y x)` -/
theorem r_generic_401_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_401_2 := by rule_auto

/-- `generic.rules:401`: `(Not (Less16U x y)) => (Leq16U y x)` -/
theorem r_generic_401_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_401_3 := by rule_auto

/-- `generic.rules:401`: `(Not (Less8U x y)) => (Leq8U y x)` -/
theorem r_generic_401_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_401_4 := by rule_auto

/-- `generic.rules:402`: `(Not (Leq64 x y)) => (Less64 y x)` -/
theorem r_generic_402_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_402 := by rule_auto

/-- `generic.rules:402`: `(Not (Leq32 x y)) => (Less32 y x)` -/
theorem r_generic_402_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_402_2 := by rule_auto

/-- `generic.rules:402`: `(Not (Leq16 x y)) => (Less16 y x)` -/
theorem r_generic_402_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_402_3 := by rule_auto

/-- `generic.rules:402`: `(Not (Leq8 x y)) => (Less8 y x)` -/
theorem r_generic_402_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_402_4 := by rule_auto

/-- `generic.rules:403`: `(Not (Leq64U x y)) => (Less64U y x)` -/
theorem r_generic_403_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_403 := by rule_auto

/-- `generic.rules:403`: `(Not (Leq32U x y)) => (Less32U y x)` -/
theorem r_generic_403_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_403_2 := by rule_auto

/-- `generic.rules:403`: `(Not (Leq16U x y)) => (Less16U y x)` -/
theorem r_generic_403_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_403_3 := by rule_auto

/-- `generic.rules:403`: `(Not (Leq8U x y)) => (Less8U y x)` -/
theorem r_generic_403_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_403_4 := by rule_auto

end GoFV.Proof.Rules
