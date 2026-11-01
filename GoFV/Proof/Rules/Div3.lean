import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemmas: `Div` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Div` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1098`: `(Div16u n (Const16 [c])) && isPowerOfTwo(uint16(c)) => (Rsh16Ux64 n (Const64 <typ.UInt64> [log16u(uint16(c))]))` -/
theorem r_generic_1098_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1098 := by rule_auto

/-- `generic.rules:1099`: `(Div32u n (Const32 [c])) && isPowerOfTwo(uint32(c)) => (Rsh32Ux64 n (Const64 <typ.UInt64> [log32u(uint32(c))]))` -/
theorem r_generic_1099_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1099 := by rule_auto

/-- `generic.rules:1100`: `(Div64u n (Const64 [c])) && isPowerOfTwo(uint64(c)) => (Rsh64Ux64 n (Const64 <typ.UInt64> [log64u(uint64(c))]))` -/
theorem r_generic_1100_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1100 := by rule_auto

/-- `generic.rules:1097`: `(Div8u n (Const8 [c])) && isPowerOfTwo(uint8(c)) => (Rsh8Ux64 n (Const64 <typ.UInt64> [log8u(uint8(c))]))` -/
theorem r_generic_1097_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1097 := by rule_auto

end GoFV.Proof.Rules
