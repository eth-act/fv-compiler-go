import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 7)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2223`: `(RotateLeft32 x (Neg8 (And8 y (Const8 [c])))) && c&31 == 31 => (RotateLeft32 x (Neg8 <y.Type> y))` -/
theorem r_generic_2223_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2223_4 := by rule_auto


/-- `generic.rules:2229`: `(RotateLeft32 x (Add64 y (Const64 [c]))) && c&31 == 0 => (RotateLeft32 x y)` -/
theorem r_generic_2229_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2229 := by rule_auto


/-- `generic.rules:2229`: `(RotateLeft32 x (Add32 y (Const32 [c]))) && c&31 == 0 => (RotateLeft32 x y)` -/
theorem r_generic_2229_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2229_2 := by rule_auto


/-- `generic.rules:2229`: `(RotateLeft32 x (Add16 y (Const16 [c]))) && c&31 == 0 => (RotateLeft32 x y)` -/
theorem r_generic_2229_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2229_3 := by rule_auto


/-- `generic.rules:2229`: `(RotateLeft32 x (Add8 y (Const8 [c]))) && c&31 == 0 => (RotateLeft32 x y)` -/
theorem r_generic_2229_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2229_4 := by rule_auto


/-- `generic.rules:2235`: `(RotateLeft32 x (Sub64 (Const64 [c]) y)) && c&31 == 0 => (RotateLeft32 x (Neg64 <y.Type> y))` -/
theorem r_generic_2235_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2235 := by rule_auto


/-- `generic.rules:2235`: `(RotateLeft32 x (Sub32 (Const32 [c]) y)) && c&31 == 0 => (RotateLeft32 x (Neg32 <y.Type> y))` -/
theorem r_generic_2235_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2235_2 := by rule_auto


/-- `generic.rules:2235`: `(RotateLeft32 x (Sub16 (Const16 [c]) y)) && c&31 == 0 => (RotateLeft32 x (Neg16 <y.Type> y))` -/
theorem r_generic_2235_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2235_3 := by rule_auto


end GoFV.Proof.Rules
