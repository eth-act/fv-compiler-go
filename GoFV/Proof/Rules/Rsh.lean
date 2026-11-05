import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:491`: `(Rsh16Ux16 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_491_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_491 := by rule_auto

/-- `generic.rules:491`: `(Rsh16Ux32 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_491_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_491_2 := by rule_auto

/-- `generic.rules:474`: `(Rsh16Ux64 x (Const64 [0])) => x` -/
theorem r_generic_474_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_474 := by rule_auto

/-- `generic.rules:491`: `(Rsh16Ux64 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_491_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_491_3 := by rule_auto

/-- `generic.rules:520`: `(Rsh16Ux64 (Rsh16x64 x _) (Const64 <t> [15])) => (Rsh16Ux64 x (Const64 <t> [15]))` -/
theorem r_generic_520_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_520 := by rule_auto

/-- `generic.rules:558`: `(Rsh16Ux64 (Lsh16x64 x (Const64 [8])) (Const64 [8])) => (ZeroExt8to16 (Trunc16to8 <typ.UInt8> x))` -/
theorem r_generic_558_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_558 := by rule_auto

/-- `generic.rules:491`: `(Rsh16Ux8 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_491_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_491_4 := by rule_auto

/-- `generic.rules:490`: `(Rsh16x16 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_490_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_490 := by rule_auto

/-- `generic.rules:490`: `(Rsh16x32 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_490_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_490_2 := by rule_auto

/-- `generic.rules:473`: `(Rsh16x64 x (Const64 [0])) => x` -/
theorem r_generic_473_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_473 := by rule_auto

/-- `generic.rules:490`: `(Rsh16x64 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_490_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_490_3 := by rule_auto

/-- `generic.rules:490`: `(Rsh16x8 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_490_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_490_4 := by rule_auto

/-- `generic.rules:488`: `(Rsh32Ux16 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_488_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_488 := by rule_auto

/-- `generic.rules:488`: `(Rsh32Ux32 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_488_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_488_2 := by rule_auto

/-- `generic.rules:474`: `(Rsh32Ux64 x (Const64 [0])) => x` -/
theorem r_generic_474_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_474_2 := by rule_auto

/-- `generic.rules:488`: `(Rsh32Ux64 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_488_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_488_3 := by rule_auto

/-- `generic.rules:521`: `(Rsh32Ux64 (Rsh32x64 x _) (Const64 <t> [31])) => (Rsh32Ux64 x (Const64 <t> [31]))` -/
theorem r_generic_521_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_521 := by rule_auto

/-- `generic.rules:561`: `(Rsh32Ux64 (Lsh32x64 x (Const64 [16])) (Const64 [16])) => (ZeroExt16to32 (Trunc32to16 <typ.UInt16> x))` -/
theorem r_generic_561_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_561 := by
  -- `rule_auto`, with `bv_normalize` tried before `rule_close`'s closers: there its per-bit closer
  -- (`ext`, `simp`) fails after ~2.5 s on each of the three cases first (7.6 s of the module)
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (
    repeat rule_gen1
    try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *
    try rule_ands
    try rule_subst
    try rule_norm
    try simp_all only [rule_arith, rule_close_s]
    first
    | done
    | with_reducible rfl
    | (bv_normalize (config := { enums := false, structures := false }); done)
    | rule_close)

/-- `generic.rules:488`: `(Rsh32Ux8 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_488_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_488_4 := by rule_auto

/-- `generic.rules:487`: `(Rsh32x16 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_487_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_487 := by rule_auto

/-- `generic.rules:487`: `(Rsh32x32 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_487_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_487_2 := by rule_auto

/-- `generic.rules:473`: `(Rsh32x64 x (Const64 [0])) => x` -/
theorem r_generic_473_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_473_2 := by rule_auto

/-- `generic.rules:487`: `(Rsh32x64 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_487_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_487_3 := by rule_auto

/-- `generic.rules:487`: `(Rsh32x8 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_487_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_487_4 := by rule_auto

/-- `generic.rules:485`: `(Rsh64Ux16 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_485_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_485 := by rule_auto

/-- `generic.rules:485`: `(Rsh64Ux32 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_485_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_485_2 := by rule_auto

/-- `generic.rules:474`: `(Rsh64Ux64 x (Const64 [0])) => x` -/
theorem r_generic_474_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_474_3 := by rule_auto

/-- `generic.rules:485`: `(Rsh64Ux64 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_485_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_485_3 := by rule_auto

/-- `generic.rules:522`: `(Rsh64Ux64 (Rsh64x64 x _) (Const64 <t> [63])) => (Rsh64Ux64 x (Const64 <t> [63]))` -/
theorem r_generic_522_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_522 := by rule_auto

/-- `generic.rules:485`: `(Rsh64Ux8 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_485_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_485_4 := by rule_auto

end GoFV.Proof.Rules
