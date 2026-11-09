import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Mul` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Mul` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:137`: `(Mul16 (Const16 [c]) (Const16 [d])) => (Const16 [c*d])` -/
theorem r_generic_137_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_137 := by rule_auto

/-- `generic.rules:192`: `(Mul16 (Const16 [1]) x) => x` -/
theorem r_generic_192_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_192 := by rule_auto

/-- `generic.rules:196`: `(Mul16 (Const16 [-1]) x) => (Neg16 x)` -/
theorem r_generic_196_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_196 := by rule_auto

/-- `generic.rules:199`: `(Mul16 (Const16 <t> [c]) (Neg16 x)) => (Mul16 x (Const16 <t> [-c]))` -/
theorem r_generic_199_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_199 := by rule_auto

/-- `generic.rules:201`: `(Mul16 (Neg16 x) (Neg16 y)) => (Mul16 x y)` -/
theorem r_generic_201_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_201 := by rule_auto

/-- `generic.rules:413`: `(Mul16 (Const16 <t> [c]) (Add16 <t> (Const16 <t> [d]) x)) && !isPowerOfTwo(c) => (Add16 (Const16 <t> [c*d]) (Mul16 <t> (Const16 <t> [c]) x))` -/
theorem r_generic_413_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_413 := by rule_auto

/-- `generic.rules:648`: `(Mul16 (Const16 [0]) _) => (Const16 [0])` -/
theorem r_generic_648_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_648 := by rule_auto

/-- `generic.rules:1272`: `(Mul16 (Mul16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Mul16 i (Mul16 <t> x z))` -/
theorem r_generic_1272_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1272 := by rule_auto

/-- `generic.rules:1320`: `(Mul16 (Const16 <t> [c]) (Mul16 (Const16 <t> [d]) x)) => (Mul16 (Const16 <t> [c*d]) x)` -/
theorem r_generic_1320_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1320 := by rule_auto

/-- `generic.rules:138`: `(Mul32 (Const32 [c]) (Const32 [d])) => (Const32 [c*d])` -/
theorem r_generic_138_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_138 := by rule_auto

/-- `generic.rules:192`: `(Mul32 (Const32 [1]) x) => x` -/
theorem r_generic_192_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_192_2 := by rule_auto

/-- `generic.rules:196`: `(Mul32 (Const32 [-1]) x) => (Neg32 x)` -/
theorem r_generic_196_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_196_2 := by rule_auto

/-- `generic.rules:199`: `(Mul32 (Const32 <t> [c]) (Neg32 x)) => (Mul32 x (Const32 <t> [-c]))` -/
theorem r_generic_199_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_199_2 := by rule_auto

/-- `generic.rules:201`: `(Mul32 (Neg32 x) (Neg32 y)) => (Mul32 x y)` -/
theorem r_generic_201_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_201_2 := by rule_auto

/-- `generic.rules:411`: `(Mul32 (Const32 <t> [c]) (Add32 <t> (Const32 <t> [d]) x)) && !isPowerOfTwo(c) => (Add32 (Const32 <t> [c*d]) (Mul32 <t> (Const32 <t> [c]) x))` -/
theorem r_generic_411_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_411 := by rule_auto

/-- `generic.rules:648`: `(Mul32 (Const32 [0]) _) => (Const32 [0])` -/
theorem r_generic_648_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_648_2 := by rule_auto

/-- `generic.rules:1271`: `(Mul32 (Mul32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Mul32 i (Mul32 <t> x z))` -/
theorem r_generic_1271_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1271 := by rule_auto

/-- `generic.rules:1319`: `(Mul32 (Const32 <t> [c]) (Mul32 (Const32 <t> [d]) x)) => (Mul32 (Const32 <t> [c*d]) x)` -/
theorem r_generic_1319_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1319 := by rule_auto

/-- `generic.rules:139`: `(Mul64 (Const64 [c]) (Const64 [d])) => (Const64 [c*d])` -/
theorem r_generic_139_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_139 := by rule_auto

/-- `generic.rules:192`: `(Mul64 (Const64 [1]) x) => x` -/
theorem r_generic_192_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_192_3 := by rule_auto

/-- `generic.rules:196`: `(Mul64 (Const64 [-1]) x) => (Neg64 x)` -/
theorem r_generic_196_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_196_3 := by rule_auto

/-- `generic.rules:199`: `(Mul64 (Const64 <t> [c]) (Neg64 x)) => (Mul64 x (Const64 <t> [-c]))` -/
theorem r_generic_199_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_199_3 := by rule_auto

/-- `generic.rules:201`: `(Mul64 (Neg64 x) (Neg64 y)) => (Mul64 x y)` -/
theorem r_generic_201_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_201_3 := by rule_auto

/-- `generic.rules:409`: `(Mul64 (Const64 <t> [c]) (Add64 <t> (Const64 <t> [d]) x)) && !isPowerOfTwo(c) => (Add64 (Const64 <t> [c*d]) (Mul64 <t> (Const64 <t> [c]) x))` -/
theorem r_generic_409_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_409 := by rule_auto

/-- `generic.rules:648`: `(Mul64 (Const64 [0]) _) => (Const64 [0])` -/
theorem r_generic_648_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_648_3 := by rule_auto

/-- `generic.rules:1270`: `(Mul64 (Mul64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Mul64 i (Mul64 <t> x z))` -/
theorem r_generic_1270_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1270 := by rule_auto

/-- `generic.rules:1318`: `(Mul64 (Const64 <t> [c]) (Mul64 (Const64 <t> [d]) x)) => (Mul64 (Const64 <t> [c*d]) x)` -/
theorem r_generic_1318_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1318 := by rule_auto

/-- `generic.rules:136`: `(Mul8 (Const8 [c]) (Const8 [d])) => (Const8 [c*d])` -/
theorem r_generic_136_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_136 := by rule_auto

/-- `generic.rules:192`: `(Mul8 (Const8 [1]) x) => x` -/
theorem r_generic_192_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_192_4 := by rule_auto

/-- `generic.rules:196`: `(Mul8 (Const8 [-1]) x) => (Neg8 x)` -/
theorem r_generic_196_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_196_4 := by rule_auto

end GoFV.Proof.Rules
