import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Lsh` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Lsh` family (`docs/proofs/rules.md`).
-/

/-! False rules (`docs/proofs/rules.md`, "Findings"); `scripts/rule-proofs.py table` reads these lines.
`CondSelect` into a shift (`generic.rules:2355`): at `bool = false` the matched value is `x`, the
result `x << 0`, `poison` when `x` is an address-less pointer in a 64-bit integer register or an
integer of another width (#69, RuleProofs17).
-- FALSE r_generic_2355 #69
-- FALSE r_generic_2355_2 #69
-- FALSE r_generic_2355_3 #69
-- FALSE r_generic_2355_4 #69
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:489`: `(Lsh16x16 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_489_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_489 := by rule_auto

/-- `generic.rules:489`: `(Lsh16x32 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_489_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_489_2 := by rule_auto

/-- `generic.rules:472`: `(Lsh16x64 x (Const64 [0])) => x` -/
theorem r_generic_472_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_472 := by rule_auto

/-- `generic.rules:489`: `(Lsh16x64 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_489_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_489_3 := by rule_auto

/-- `generic.rules:489`: `(Lsh16x8 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_489_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_489_4 := by rule_auto

/-- `generic.rules:486`: `(Lsh32x16 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_486_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_486 := by rule_auto

/-- `generic.rules:486`: `(Lsh32x32 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_486_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_486_2 := by rule_auto

/-- `generic.rules:472`: `(Lsh32x64 x (Const64 [0])) => x` -/
theorem r_generic_472_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_472_2 := by rule_auto

/-- `generic.rules:486`: `(Lsh32x64 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_486_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_486_3 := by rule_auto

/-- `generic.rules:486`: `(Lsh32x8 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_486_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_486_4 := by rule_auto

/-- `generic.rules:483`: `(Lsh64x16 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_483_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_483 := by rule_auto

/-- `generic.rules:483`: `(Lsh64x32 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_483_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_483_2 := by rule_auto

/-- `generic.rules:472`: `(Lsh64x64 x (Const64 [0])) => x` -/
theorem r_generic_472_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_472_3 := by rule_auto

/-- `generic.rules:483`: `(Lsh64x64 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_483_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_483_3 := by rule_auto

/-- `generic.rules:483`: `(Lsh64x8 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_483_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_483_4 := by rule_auto

/-- `generic.rules:492`: `(Lsh8x16 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_492_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_492 := by rule_auto

/-- `generic.rules:492`: `(Lsh8x32 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_492_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_492_2 := by rule_auto

/-- `generic.rules:472`: `(Lsh8x64 x (Const64 [0])) => x` -/
theorem r_generic_472_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_472_4 := by rule_auto

/-- `generic.rules:492`: `(Lsh8x64 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_492_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_492_3 := by rule_auto

/-- `generic.rules:492`: `(Lsh8x8 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_492_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_492_4 := by rule_auto

end GoFV.Proof.Rules
