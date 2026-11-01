import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:449`: `(Rsh32Ux8 x (Const8 [c])) => (Rsh32Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_449_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_449 := by rule_auto


/-- `generic.rules:445`: `(Rsh32x16 x (Const16 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_445_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_445 := by rule_auto


/-- `generic.rules:444`: `(Rsh32x32 x (Const32 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_444_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_444 := by rule_auto


/-- `generic.rules:229`: `(Rsh32x64 (Const32 [c]) (Const64 [d])) => (Const32 [c >> uint64(d)])` -/
theorem r_generic_229_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_229 := by rule_auto


/-- `generic.rules:446`: `(Rsh32x8 x (Const8 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_446_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_446 := by rule_auto


/-- `generic.rules:438`: `(Rsh64Ux16 x (Const16 [c])) => (Rsh64Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_438_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_438 := by rule_auto


end GoFV.Proof.Rules
