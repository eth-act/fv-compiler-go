import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13

/-!
# Rule lemmas: `Sub` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Sub` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1241`: `(Sub32 (Sub32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Sub32 i (Add32 <t> z x))` -/
theorem r_generic_1241_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1241 := by rule_auto

/-- `generic.rules:1247`: `(Sub32 (Add32 z i:(Const32 <t>)) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Add32 i (Sub32 <t> z x))` -/
theorem r_generic_1247_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1247 := by rule_auto

/-- `generic.rules:1289`: `(Sub32 (Const32 <t> [c]) (Sub32 (Const32 <t> [d]) x)) => (Add32 (Const32 <t> [c-d]) x)` -/
theorem r_generic_1289_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1289 := by rule_auto

/-- `generic.rules:1295`: `(Sub32 (Const32 <t> [c]) (Add32 (Const32 <t> [d]) x)) => (Sub32 (Const32 <t> [c-d]) x)` -/
theorem r_generic_1295_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1295 := by rule_auto

/-- `generic.rules:132`: `(Sub64 (Const64 [c]) (Const64 [d])) => (Const64 [c-d])` -/
theorem r_generic_132_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_132 := by rule_auto

/-- `generic.rules:391`: `(Sub64 x (Const64 <t> [c])) && x.Op != OpConst64 => (Add64 (Const64 <t> [-c]) x)` -/
theorem r_generic_391_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_391 := by rule_auto

/-- `generic.rules:422`: `(Sub64 <t> (Mul64 x y) (Mul64 x z)) => (Mul64 x (Sub64 <t> y z))` -/
theorem r_generic_422_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_422_3 := by rule_auto

/-- `generic.rules:647`: `(Sub64 x x) => (Const64 [0])` -/
theorem r_generic_647_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_647_3 := by rule_auto

/-- `generic.rules:659`: `(Sub64 (Neg64 x) (Com64 x)) => (Const64 [1])` -/
theorem r_generic_659_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_659_3 := by rule_auto

/-- `generic.rules:660`: `(Sub64 (Com64 x) (Neg64 x)) => (Const64 [-1])` -/
theorem r_generic_660_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_660_3 := by rule_auto

/-- `generic.rules:674`: `(Sub64 (Add64 t x) (Add64 t y)) => (Sub64 x y)` -/
theorem r_generic_674_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_674_3 := by rule_auto

/-- `generic.rules:774`: `(Sub64 (Add64 x y) x) => y` -/
theorem r_generic_774_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_774_3 := by rule_auto

/-- `generic.rules:775`: `(Sub64 (Add64 x y) y) => x` -/
theorem r_generic_775_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_775_3 := by rule_auto

/-- `generic.rules:776`: `(Sub64 (Sub64 x y) x) => (Neg64 y)` -/
theorem r_generic_776_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_776_3 := by rule_auto

/-- `generic.rules:777`: `(Sub64 x (Add64 x y)) => (Neg64 y)` -/
theorem r_generic_777_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_777_3 := by rule_auto

/-- `generic.rules:1228`: `(Sub64 x (Sub64 i:(Const64 <t>) z)) && (z.Op != OpConst64 && x.Op != OpConst64) => (Sub64 (Add64 <t> x z) i)` -/
theorem r_generic_1228_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1228 := by rule_auto

/-- `generic.rules:1234`: `(Sub64 x (Add64 z i:(Const64 <t>))) && (z.Op != OpConst64 && x.Op != OpConst64) => (Sub64 (Sub64 <t> x z) i)` -/
theorem r_generic_1234_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1234 := by rule_auto

/-- `generic.rules:1240`: `(Sub64 (Sub64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Sub64 i (Add64 <t> z x))` -/
theorem r_generic_1240_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1240 := by rule_auto

/-- `generic.rules:1246`: `(Sub64 (Add64 z i:(Const64 <t>)) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Add64 i (Sub64 <t> z x))` -/
theorem r_generic_1246_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1246 := by rule_auto

/-- `generic.rules:1288`: `(Sub64 (Const64 <t> [c]) (Sub64 (Const64 <t> [d]) x)) => (Add64 (Const64 <t> [c-d]) x)` -/
theorem r_generic_1288_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1288 := by rule_auto

/-- `generic.rules:1294`: `(Sub64 (Const64 <t> [c]) (Add64 (Const64 <t> [d]) x)) => (Sub64 (Const64 <t> [c-d]) x)` -/
theorem r_generic_1294_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1294 := by rule_auto

/-- `generic.rules:129`: `(Sub8 (Const8 [c]) (Const8 [d])) => (Const8 [c-d])` -/
theorem r_generic_129_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_129 := by rule_auto

/-- `generic.rules:394`: `(Sub8 x (Const8 <t> [c])) && x.Op != OpConst8 => (Add8 (Const8 <t> [-c]) x)` -/
theorem r_generic_394_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_394 := by rule_auto

/-- `generic.rules:422`: `(Sub8 <t> (Mul8 x y) (Mul8 x z)) => (Mul8 x (Sub8 <t> y z))` -/
theorem r_generic_422_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_422_4 := by rule_auto

/-- `generic.rules:647`: `(Sub8 x x) => (Const8 [0])` -/
theorem r_generic_647_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_647_4 := by rule_auto

/-- `generic.rules:659`: `(Sub8 (Neg8 x) (Com8 x)) => (Const8 [1])` -/
theorem r_generic_659_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_659_4 := by rule_auto

/-- `generic.rules:660`: `(Sub8 (Com8 x) (Neg8 x)) => (Const8 [-1])` -/
theorem r_generic_660_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_660_4 := by rule_auto

/-- `generic.rules:674`: `(Sub8 (Add8 t x) (Add8 t y)) => (Sub8 x y)` -/
theorem r_generic_674_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_674_4 := by rule_auto

/-- `generic.rules:774`: `(Sub8 (Add8 x y) x) => y` -/
theorem r_generic_774_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_774_4 := by rule_auto

/-- `generic.rules:775`: `(Sub8 (Add8 x y) y) => x` -/
theorem r_generic_775_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_775_4 := by rule_auto

end GoFV.Proof.Rules
