import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values12

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `SignExt` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`SignExt` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:109`: `(SignExt16to32 (Const16 [c])) => (Const32 [int32(c)])` -/
theorem r_generic_109_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_109 := by rule_auto

/-- `generic.rules:765`: `(SignExt16to32 (Trunc32to16 x:(Rsh32x64 _ (Const64 [s])))) && s >= 16 => x` -/
theorem r_generic_765_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_765 := by rule_auto

/-- `generic.rules:110`: `(SignExt16to64 (Const16 [c])) => (Const64 [int64(c)])` -/
theorem r_generic_110_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_110 := by rule_auto

/-- `generic.rules:762`: `(SignExt16to64 (Trunc64to16 x:(Rsh64x64 _ (Const64 [s])))) && s >= 48 => x` -/
theorem r_generic_762_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_762 := by rule_auto

/-- `generic.rules:111`: `(SignExt32to64 (Const32 [c])) => (Const64 [int64(c)])` -/
theorem r_generic_111_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_111 := by rule_auto

/-- `generic.rules:763`: `(SignExt32to64 (Trunc64to32 x:(Rsh64x64 _ (Const64 [s])))) && s >= 32 => x` -/
theorem r_generic_763_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_763 := by rule_auto

/-- `generic.rules:106`: `(SignExt8to16 (Const8 [c])) => (Const16 [int16(c)])` -/
theorem r_generic_106_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_106 := by rule_auto

/-- `generic.rules:766`: `(SignExt8to16 (Trunc16to8 x:(Rsh16x64 _ (Const64 [s])))) && s >= 8 => x` -/
theorem r_generic_766_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_766 := by rule_auto

/-- `generic.rules:2407`: `(SignExt8to16 cvt:(CvtBoolToUint8 bool)) => (ZeroExt8to16 cvt)` -/
theorem r_generic_2407_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2407 := by rule_auto

/-- `generic.rules:107`: `(SignExt8to32 (Const8 [c])) => (Const32 [int32(c)])` -/
theorem r_generic_107_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_107 := by rule_auto

/-- `generic.rules:764`: `(SignExt8to32 (Trunc32to8 x:(Rsh32x64 _ (Const64 [s])))) && s >= 24 => x` -/
theorem r_generic_764_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_764 := by rule_auto

/-- `generic.rules:2407`: `(SignExt8to32 cvt:(CvtBoolToUint8 bool)) => (ZeroExt8to32 cvt)` -/
theorem r_generic_2407_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2407_2 := by rule_auto

/-- `generic.rules:108`: `(SignExt8to64 (Const8 [c])) => (Const64 [int64(c)])` -/
theorem r_generic_108_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_108 := by rule_auto

/-- `generic.rules:761`: `(SignExt8to64 (Trunc64to8 x:(Rsh64x64 _ (Const64 [s])))) && s >= 56 => x` -/
theorem r_generic_761_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_761 := by rule_auto

/-- `generic.rules:2407`: `(SignExt8to64 cvt:(CvtBoolToUint8 bool)) => (ZeroExt8to64 cvt)` -/
theorem r_generic_2407_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2407_3 := by rule_auto

end GoFV.Proof.Rules
