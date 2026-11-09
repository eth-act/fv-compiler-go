import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Xor` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Xor` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:158`: `(Xor16 (Const16 [c]) (Const16 [d])) => (Const16 [c^d])` -/
theorem r_generic_158_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_158 := by rule_auto

/-- `generic.rules:1314`: `(Xor16 (Const16 <t> [c]) (Xor16 (Const16 <t> [d]) x)) => (Xor16 (Const16 <t> [c^d]) x)` -/
theorem r_generic_1314_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1314 := by rule_auto

/-- `generic.rules:159`: `(Xor32 (Const32 [c]) (Const32 [d])) => (Const32 [c^d])` -/
theorem r_generic_159_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_159 := by rule_auto

/-- `generic.rules:1313`: `(Xor32 (Const32 <t> [c]) (Xor32 (Const32 <t> [d]) x)) => (Xor32 (Const32 <t> [c^d]) x)` -/
theorem r_generic_1313_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1313 := by rule_auto

/-- `generic.rules:160`: `(Xor64 (Const64 [c]) (Const64 [d])) => (Const64 [c^d])` -/
theorem r_generic_160_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_160 := by rule_auto

/-- `generic.rules:1312`: `(Xor64 (Const64 <t> [c]) (Xor64 (Const64 <t> [d]) x)) => (Xor64 (Const64 <t> [c^d]) x)` -/
theorem r_generic_1312_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1312 := by rule_auto

/-- `generic.rules:157`: `(Xor8 (Const8 [c]) (Const8 [d])) => (Const8 [c^d])` -/
theorem r_generic_157_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_157 := by rule_auto

/-- `generic.rules:1315`: `(Xor8 (Const8 <t> [c]) (Xor8 (Const8 <t> [d]) x)) => (Xor8 (Const8 <t> [c^d]) x)` -/
theorem r_generic_1315_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1315 := by rule_auto

end GoFV.Proof.Rules
