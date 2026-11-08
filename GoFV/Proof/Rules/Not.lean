import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Not` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Not` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:184`: `(Not (ConstBool [c])) => (ConstBool [!c])` -/
theorem r_generic_184_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_184 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq64 x y)) => (Neq64 x y)` -/
theorem r_generic_397_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq32 x y)) => (Neq32 x y)` -/
theorem r_generic_397_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_2 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq16 x y)) => (Neq16 x y)` -/
theorem r_generic_397_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_3 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq8 x y)) => (Neq8 x y)` -/
theorem r_generic_397_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_4 := by rule_auto

/-- `generic.rules:397`: `(Not (EqB x y)) => (NeqB x y)` -/
theorem r_generic_397_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_5 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq64 x y)) => (Eq64 x y)` -/
theorem r_generic_398_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq32 x y)) => (Eq32 x y)` -/
theorem r_generic_398_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_2 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq16 x y)) => (Eq16 x y)` -/
theorem r_generic_398_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_3 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq8 x y)) => (Eq8 x y)` -/
theorem r_generic_398_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_4 := by rule_auto

/-- `generic.rules:398`: `(Not (NeqB x y)) => (EqB x y)` -/
theorem r_generic_398_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_5 := by rule_auto

/-- `generic.rules:400`: `(Not (Less64 x y)) => (Leq64 y x)` -/
theorem r_generic_400_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400 := by rule_auto

/-- `generic.rules:400`: `(Not (Less32 x y)) => (Leq32 y x)` -/
theorem r_generic_400_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400_2 := by rule_auto

/-- `generic.rules:400`: `(Not (Less16 x y)) => (Leq16 y x)` -/
theorem r_generic_400_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400_3 := by rule_auto

end GoFV.Proof.Rules
