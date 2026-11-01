import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemmas: `Mod` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Mod` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1128`: `(Mod16u <t> n (Const16 [c])) && isPowerOfTwo(uint16(c)) => (And16 n (Const16 <t> [c-1]))` -/
theorem r_generic_1128_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1128 := by rule_auto

/-- `generic.rules:1129`: `(Mod32u <t> n (Const32 [c])) && isPowerOfTwo(uint32(c)) => (And32 n (Const32 <t> [c-1]))` -/
theorem r_generic_1129_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1129 := by rule_auto

/-- `generic.rules:1130`: `(Mod64u <t> n (Const64 [c])) && isPowerOfTwo(uint64(c)) => (And64 n (Const64 <t> [c-1]))` -/
theorem r_generic_1130_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1130 := by rule_auto

/-- `generic.rules:1127`: `(Mod8u <t> n (Const8 [c])) && isPowerOfTwo(uint8(c)) => (And8 n (Const8 <t> [c-1]))` -/
theorem r_generic_1127_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1127 := by rule_auto

end GoFV.Proof.Rules
