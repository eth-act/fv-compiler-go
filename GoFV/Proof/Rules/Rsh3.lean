import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Rsh` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:458`: `(Rsh16Ux16 x (Const16 [c])) => (Rsh16Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_458_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_458 := by rule_auto


/-- `generic.rules:457`: `(Rsh16Ux32 x (Const32 [c])) => (Rsh16Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_457_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_457 := by rule_auto


/-- `generic.rules:233`: `(Rsh16Ux64 (Const16 [c]) (Const64 [d])) => (Const16 [int16(uint16(c) >> uint64(d))])` -/
theorem r_generic_233_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_233 := by rule_auto


/-- `generic.rules:499`: `(Rsh16Ux64 _ (Const64 [c])) && uint64(c) >= 16 => (Const16 [0])` -/
theorem r_generic_499_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_499_2 := by rule_auto


/-- `generic.rules:459`: `(Rsh16Ux8 x (Const8 [c])) => (Rsh16Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_459_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_459 := by rule_auto


/-- `generic.rules:455`: `(Rsh16x16 x (Const16 [c])) => (Rsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_455_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_455 := by rule_auto


/-- `generic.rules:454`: `(Rsh16x32 x (Const32 [c])) => (Rsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_454_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_454 := by rule_auto


end GoFV.Proof.Rules
