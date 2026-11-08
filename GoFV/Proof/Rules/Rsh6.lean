import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Rsh` rules (part 6)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:232`: `(Rsh16x64 (Const16 [c]) (Const64 [d])) => (Const16 [c >> uint64(d)])` -/
theorem r_generic_232_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_232 := by rule_auto


/-- `generic.rules:456`: `(Rsh16x8 x (Const8 [c])) => (Rsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_456_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_456 := by rule_auto


/-- `generic.rules:448`: `(Rsh32Ux16 x (Const16 [c])) => (Rsh32Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_448_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_448 := by rule_auto


/-- `generic.rules:447`: `(Rsh32Ux32 x (Const32 [c])) => (Rsh32Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_447_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_447 := by rule_auto


/-- `generic.rules:230`: `(Rsh32Ux64 (Const32 [c]) (Const64 [d])) => (Const32 [int32(uint32(c) >> uint64(d))])` -/
theorem r_generic_230_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_230 := by rule_auto


/-- `generic.rules:498`: `(Rsh32Ux64 _ (Const64 [c])) && uint64(c) >= 32 => (Const32 [0])` -/
theorem r_generic_498_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_498_2 := by rule_auto


end GoFV.Proof.Rules
