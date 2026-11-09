import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values01

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Com` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Com` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:651`: `(Com16 (Com16 x)) => x` -/
theorem r_generic_651_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_651 := by rule_auto

/-- `generic.rules:652`: `(Com16 (Const16 [c])) => (Const16 [^c])` -/
theorem r_generic_652_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_652 := by rule_auto

/-- `generic.rules:679`: `(Com16 (Add16 (Const16 [-1]) x)) => (Neg16 x)` -/
theorem r_generic_679_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_679 := by rule_auto

/-- `generic.rules:651`: `(Com32 (Com32 x)) => x` -/
theorem r_generic_651_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_651_2 := by rule_auto

/-- `generic.rules:652`: `(Com32 (Const32 [c])) => (Const32 [^c])` -/
theorem r_generic_652_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_652_2 := by rule_auto

/-- `generic.rules:679`: `(Com32 (Add32 (Const32 [-1]) x)) => (Neg32 x)` -/
theorem r_generic_679_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_679_2 := by rule_auto

/-- `generic.rules:651`: `(Com64 (Com64 x)) => x` -/
theorem r_generic_651_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_651_3 := by rule_auto

/-- `generic.rules:652`: `(Com64 (Const64 [c])) => (Const64 [^c])` -/
theorem r_generic_652_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_652_3 := by rule_auto

/-- `generic.rules:679`: `(Com64 (Add64 (Const64 [-1]) x)) => (Neg64 x)` -/
theorem r_generic_679_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_679_3 := by rule_auto

/-- `generic.rules:651`: `(Com8 (Com8 x)) => x` -/
theorem r_generic_651_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_651_4 := by rule_auto

/-- `generic.rules:652`: `(Com8 (Const8 [c])) => (Const8 [^c])` -/
theorem r_generic_652_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_652_4 := by rule_auto

/-- `generic.rules:679`: `(Com8 (Add8 (Const8 [-1]) x)) => (Neg8 x)` -/
theorem r_generic_679_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_679_4 := by rule_auto

end GoFV.Proof.Rules
