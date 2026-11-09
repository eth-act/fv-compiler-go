import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00
import GoFV.Rules.Generated.Generic.Values01

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `And` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`And` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:212`: `(And16 x (Or16 x y)) => x` -/
theorem r_generic_212_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_212 := by rule_auto

/-- `generic.rules:637`: `(And16 x x) => x` -/
theorem r_generic_637_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_637 := by rule_auto

/-- `generic.rules:638`: `(And16 (Const16 [-1]) x) => x` -/
theorem r_generic_638_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_638 := by rule_auto

/-- `generic.rules:639`: `(And16 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_639_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_639 := by rule_auto

/-- `generic.rules:640`: `(And16 (Com16 x) x) => (Const16 [0])` -/
theorem r_generic_640_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_640 := by rule_auto

/-- `generic.rules:687`: `(And16 x (And16 x y)) => (And16 x y)` -/
theorem r_generic_687_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_687 := by rule_auto

/-- `generic.rules:1254`: `(And16 (And16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (And16 i (And16 <t> z x))` -/
theorem r_generic_1254_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1254 := by rule_auto

/-- `generic.rules:212`: `(And32 x (Or32 x y)) => x` -/
theorem r_generic_212_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_212_2 := by rule_auto

/-- `generic.rules:637`: `(And32 x x) => x` -/
theorem r_generic_637_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_637_2 := by rule_auto

/-- `generic.rules:638`: `(And32 (Const32 [-1]) x) => x` -/
theorem r_generic_638_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_638_2 := by rule_auto

/-- `generic.rules:639`: `(And32 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_639_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_639_2 := by rule_auto

/-- `generic.rules:640`: `(And32 (Com32 x) x) => (Const32 [0])` -/
theorem r_generic_640_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_640_2 := by rule_auto

/-- `generic.rules:687`: `(And32 x (And32 x y)) => (And32 x y)` -/
theorem r_generic_687_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_687_2 := by rule_auto

/-- `generic.rules:1253`: `(And32 (And32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (And32 i (And32 <t> z x))` -/
theorem r_generic_1253_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1253 := by rule_auto

/-- `generic.rules:212`: `(And64 x (Or64 x y)) => x` -/
theorem r_generic_212_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_212_3 := by rule_auto

/-- `generic.rules:637`: `(And64 x x) => x` -/
theorem r_generic_637_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_637_3 := by rule_auto

/-- `generic.rules:638`: `(And64 (Const64 [-1]) x) => x` -/
theorem r_generic_638_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_638_3 := by rule_auto

/-- `generic.rules:639`: `(And64 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_639_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_639_3 := by rule_auto

/-- `generic.rules:640`: `(And64 (Com64 x) x) => (Const64 [0])` -/
theorem r_generic_640_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_640_3 := by rule_auto

/-- `generic.rules:687`: `(And64 x (And64 x y)) => (And64 x y)` -/
theorem r_generic_687_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_687_3 := by rule_auto

/-- `generic.rules:1252`: `(And64 (And64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (And64 i (And64 <t> z x))` -/
theorem r_generic_1252_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1252 := by rule_auto

/-- `generic.rules:212`: `(And8 x (Or8 x y)) => x` -/
theorem r_generic_212_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_212_4 := by rule_auto

/-- `generic.rules:637`: `(And8 x x) => x` -/
theorem r_generic_637_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_637_4 := by rule_auto

/-- `generic.rules:638`: `(And8 (Const8 [-1]) x) => x` -/
theorem r_generic_638_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_638_4 := by rule_auto

/-- `generic.rules:639`: `(And8 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_639_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_639_4 := by rule_auto

/-- `generic.rules:640`: `(And8 (Com8 x) x) => (Const8 [0])` -/
theorem r_generic_640_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_640_4 := by rule_auto

/-- `generic.rules:687`: `(And8 x (And8 x y)) => (And8 x y)` -/
theorem r_generic_687_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_687_4 := by rule_auto

/-- `generic.rules:1255`: `(And8 (And8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (And8 i (And8 <t> z x))` -/
theorem r_generic_1255_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1255 := by rule_auto

end GoFV.Proof.Rules
