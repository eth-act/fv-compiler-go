import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13

/-!
# Rule lemmas: `Trunc` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Trunc` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:41`: `(Trunc16to8 (Const16 [c])) => (Const8 [int8(c)])` -/
theorem r_generic_41_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_41 := by rule_auto

/-- `generic.rules:79`: `(Trunc16to8 (ZeroExt8to16 x)) => x` -/
theorem r_generic_79_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_79 := by rule_auto

/-- `generic.rules:89`: `(Trunc16to8 (SignExt8to16 x)) => x` -/
theorem r_generic_89_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_89 := by rule_auto

/-- `generic.rules:752`: `(Trunc16to8 (And16 (Const16 [y]) x)) && y&0xFF == 0xFF => (Trunc16to8 x)` -/
theorem r_generic_752_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_752 := by rule_auto

/-- `generic.rules:43`: `(Trunc32to16 (Const32 [c])) => (Const16 [int16(c)])` -/
theorem r_generic_43_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_43 := by rule_auto

/-- `generic.rules:81`: `(Trunc32to16 (ZeroExt8to32 x)) => (ZeroExt8to16 x)` -/
theorem r_generic_81_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_81 := by rule_auto

/-- `generic.rules:82`: `(Trunc32to16 (ZeroExt16to32 x)) => x` -/
theorem r_generic_82_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_82 := by rule_auto

/-- `generic.rules:91`: `(Trunc32to16 (SignExt8to32 x)) => (SignExt8to16 x)` -/
theorem r_generic_91_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_91 := by rule_auto

/-- `generic.rules:92`: `(Trunc32to16 (SignExt16to32 x)) => x` -/
theorem r_generic_92_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_92 := by rule_auto

/-- `generic.rules:751`: `(Trunc32to16 (And32 (Const32 [y]) x)) && y&0xFFFF == 0xFFFF => (Trunc32to16 x)` -/
theorem r_generic_751_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_751 := by rule_auto

/-- `generic.rules:42`: `(Trunc32to8 (Const32 [c])) => (Const8 [int8(c)])` -/
theorem r_generic_42_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_42 := by rule_auto

/-- `generic.rules:80`: `(Trunc32to8 (ZeroExt8to32 x)) => x` -/
theorem r_generic_80_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_80 := by rule_auto

/-- `generic.rules:90`: `(Trunc32to8 (SignExt8to32 x)) => x` -/
theorem r_generic_90_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_90 := by rule_auto

/-- `generic.rules:750`: `(Trunc32to8 (And32 (Const32 [y]) x)) && y&0xFF == 0xFF => (Trunc32to8 x)` -/
theorem r_generic_750_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_750 := by rule_auto

/-- `generic.rules:45`: `(Trunc64to16 (Const64 [c])) => (Const16 [int16(c)])` -/
theorem r_generic_45_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_45 := by rule_auto

/-- `generic.rules:84`: `(Trunc64to16 (ZeroExt8to64 x)) => (ZeroExt8to16 x)` -/
theorem r_generic_84_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_84 := by rule_auto

end GoFV.Proof.Rules
