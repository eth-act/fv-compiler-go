import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13

/-!
# Rule lemmas: `Trunc` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Trunc` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:85`: `(Trunc64to16 (ZeroExt16to64 x)) => x` -/
theorem r_generic_85_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_85 := by rule_auto

/-- `generic.rules:94`: `(Trunc64to16 (SignExt8to64 x)) => (SignExt8to16 x)` -/
theorem r_generic_94_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_94 := by rule_auto

/-- `generic.rules:95`: `(Trunc64to16 (SignExt16to64 x)) => x` -/
theorem r_generic_95_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_95 := by rule_auto

/-- `generic.rules:748`: `(Trunc64to16 (And64 (Const64 [y]) x)) && y&0xFFFF == 0xFFFF => (Trunc64to16 x)` -/
theorem r_generic_748_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_748 := by rule_auto

/-- `generic.rules:46`: `(Trunc64to32 (Const64 [c])) => (Const32 [int32(c)])` -/
theorem r_generic_46_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_46 := by rule_auto

/-- `generic.rules:86`: `(Trunc64to32 (ZeroExt8to64 x)) => (ZeroExt8to32 x)` -/
theorem r_generic_86_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_86 := by rule_auto

/-- `generic.rules:87`: `(Trunc64to32 (ZeroExt16to64 x)) => (ZeroExt16to32 x)` -/
theorem r_generic_87_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_87 := by rule_auto

/-- `generic.rules:88`: `(Trunc64to32 (ZeroExt32to64 x)) => x` -/
theorem r_generic_88_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_88 := by rule_auto

/-- `generic.rules:96`: `(Trunc64to32 (SignExt8to64 x)) => (SignExt8to32 x)` -/
theorem r_generic_96_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_96 := by rule_auto

/-- `generic.rules:97`: `(Trunc64to32 (SignExt16to64 x)) => (SignExt16to32 x)` -/
theorem r_generic_97_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_97 := by rule_auto

/-- `generic.rules:98`: `(Trunc64to32 (SignExt32to64 x)) => x` -/
theorem r_generic_98_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_98 := by rule_auto

/-- `generic.rules:749`: `(Trunc64to32 (And64 (Const64 [y]) x)) && y&0xFFFFFFFF == 0xFFFFFFFF => (Trunc64to32 x)` -/
theorem r_generic_749_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_749 := by rule_auto

/-- `generic.rules:44`: `(Trunc64to8 (Const64 [c])) => (Const8 [int8(c)])` -/
theorem r_generic_44_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_44 := by rule_auto

/-- `generic.rules:83`: `(Trunc64to8 (ZeroExt8to64 x)) => x` -/
theorem r_generic_83_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_83 := by rule_auto

/-- `generic.rules:93`: `(Trunc64to8 (SignExt8to64 x)) => x` -/
theorem r_generic_93_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_93 := by rule_auto

/-- `generic.rules:747`: `(Trunc64to8 (And64 (Const64 [y]) x)) && y&0xFF == 0xFF => (Trunc64to8 x)` -/
theorem r_generic_747_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_747 := by rule_auto

end GoFV.Proof.Rules
