import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules (part 7)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:437`: `(Rsh64Ux32 x (Const32 [c])) => (Rsh64Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_437_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_437 := by rule_auto


/-- `generic.rules:227`: `(Rsh64Ux64 (Const64 [c]) (Const64 [d])) => (Const64 [int64(uint64(c) >> uint64(d))])` -/
theorem r_generic_227_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_227 := by rule_auto


/-- `generic.rules:497`: `(Rsh64Ux64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])` -/
theorem r_generic_497_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_497_2 := by rule_auto


/-- `generic.rules:513`: `(Rsh64Ux64 <t> (Rsh64Ux64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh64Ux64 x (Const64 <t> [c+d]))` -/
theorem r_generic_513_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_513 := by rule_auto


/-- `generic.rules:439`: `(Rsh64Ux8 x (Const8 [c])) => (Rsh64Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_439_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_439 := by rule_auto


/-- `generic.rules:435`: `(Rsh64x16 x (Const16 [c])) => (Rsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_435_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_435 := by rule_auto


/-- `generic.rules:434`: `(Rsh64x32 x (Const32 [c])) => (Rsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_434_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_434 := by rule_auto


end GoFV.Proof.Rules
