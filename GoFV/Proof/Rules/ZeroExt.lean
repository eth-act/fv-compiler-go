import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `ZeroExt` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`ZeroExt` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:103`: `(ZeroExt16to32 (Const16 [c])) => (Const32 [int32(uint16(c))])` -/
theorem r_generic_103_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_103 := by rule_auto

/-- `generic.rules:758`: `(ZeroExt16to32 (Trunc32to16 x:(Rsh32Ux64 _ (Const64 [s])))) && s >= 16 => x` -/
theorem r_generic_758_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_758 := by rule_auto

/-- `generic.rules:104`: `(ZeroExt16to64 (Const16 [c])) => (Const64 [int64(uint16(c))])` -/
theorem r_generic_104_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_104 := by rule_auto

/-- `generic.rules:755`: `(ZeroExt16to64 (Trunc64to16 x:(Rsh64Ux64 _ (Const64 [s])))) && s >= 48 => x` -/
theorem r_generic_755_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_755 := by rule_auto

/-- `generic.rules:105`: `(ZeroExt32to64 (Const32 [c])) => (Const64 [int64(uint32(c))])` -/
theorem r_generic_105_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_105 := by rule_auto

/-- `generic.rules:756`: `(ZeroExt32to64 (Trunc64to32 x:(Rsh64Ux64 _ (Const64 [s])))) && s >= 32 => x` -/
theorem r_generic_756_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_756 := by rule_auto

/-- `generic.rules:100`: `(ZeroExt8to16 (Const8 [c])) => (Const16 [int16( uint8(c))])` -/
theorem r_generic_100_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_100 := by rule_auto

/-- `generic.rules:759`: `(ZeroExt8to16 (Trunc16to8 x:(Rsh16Ux64 _ (Const64 [s])))) && s >= 8 => x` -/
theorem r_generic_759_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_759 := by rule_auto

/-- `generic.rules:101`: `(ZeroExt8to32 (Const8 [c])) => (Const32 [int32( uint8(c))])` -/
theorem r_generic_101_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_101 := by rule_auto

/-- `generic.rules:757`: `(ZeroExt8to32 (Trunc32to8 x:(Rsh32Ux64 _ (Const64 [s])))) && s >= 24 => x` -/
theorem r_generic_757_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_757 := by rule_auto

/-- `generic.rules:102`: `(ZeroExt8to64 (Const8 [c])) => (Const64 [int64( uint8(c))])` -/
theorem r_generic_102_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_102 := by rule_auto

/-- `generic.rules:754`: `(ZeroExt8to64 (Trunc64to8 x:(Rsh64Ux64 _ (Const64 [s])))) && s >= 56 => x` -/
theorem r_generic_754_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_754 := by rule_auto

end GoFV.Proof.Rules
