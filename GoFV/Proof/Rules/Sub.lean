import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values12
import GoFV.Rules.Generated.Generic.Values13

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Sub` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Sub` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:130`: `(Sub16 (Const16 [c]) (Const16 [d])) => (Const16 [c-d])` -/
theorem r_generic_130_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_130 := by rule_auto

/-- `generic.rules:393`: `(Sub16 x (Const16 <t> [c])) && x.Op != OpConst16 => (Add16 (Const16 <t> [-c]) x)` -/
theorem r_generic_393_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_393 := by rule_auto

/-- `generic.rules:422`: `(Sub16 <t> (Mul16 x y) (Mul16 x z)) => (Mul16 x (Sub16 <t> y z))` -/
theorem r_generic_422_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_422 := by rule_auto

/-- `generic.rules:647`: `(Sub16 x x) => (Const16 [0])` -/
theorem r_generic_647_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_647 := by rule_auto

/-- `generic.rules:659`: `(Sub16 (Neg16 x) (Com16 x)) => (Const16 [1])` -/
theorem r_generic_659_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_659 := by rule_auto

/-- `generic.rules:660`: `(Sub16 (Com16 x) (Neg16 x)) => (Const16 [-1])` -/
theorem r_generic_660_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_660 := by rule_auto

/-- `generic.rules:674`: `(Sub16 (Add16 t x) (Add16 t y)) => (Sub16 x y)` -/
theorem r_generic_674_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_674 := by rule_auto

/-- `generic.rules:774`: `(Sub16 (Add16 x y) x) => y` -/
theorem r_generic_774_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_774 := by rule_auto

/-- `generic.rules:775`: `(Sub16 (Add16 x y) y) => x` -/
theorem r_generic_775_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_775 := by rule_auto

/-- `generic.rules:776`: `(Sub16 (Sub16 x y) x) => (Neg16 y)` -/
theorem r_generic_776_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_776 := by rule_auto

/-- `generic.rules:777`: `(Sub16 x (Add16 x y)) => (Neg16 y)` -/
theorem r_generic_777_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_777 := by rule_auto

/-- `generic.rules:1230`: `(Sub16 x (Sub16 i:(Const16 <t>) z)) && (z.Op != OpConst16 && x.Op != OpConst16) => (Sub16 (Add16 <t> x z) i)` -/
theorem r_generic_1230_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1230 := by rule_auto

/-- `generic.rules:1236`: `(Sub16 x (Add16 z i:(Const16 <t>))) && (z.Op != OpConst16 && x.Op != OpConst16) => (Sub16 (Sub16 <t> x z) i)` -/
theorem r_generic_1236_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1236 := by rule_auto

/-- `generic.rules:1242`: `(Sub16 (Sub16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Sub16 i (Add16 <t> z x))` -/
theorem r_generic_1242_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1242 := by rule_auto

/-- `generic.rules:1248`: `(Sub16 (Add16 z i:(Const16 <t>)) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Add16 i (Sub16 <t> z x))` -/
theorem r_generic_1248_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1248 := by rule_auto

/-- `generic.rules:1290`: `(Sub16 (Const16 <t> [c]) (Sub16 (Const16 <t> [d]) x)) => (Add16 (Const16 <t> [c-d]) x)` -/
theorem r_generic_1290_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1290 := by rule_auto

/-- `generic.rules:1296`: `(Sub16 (Const16 <t> [c]) (Add16 (Const16 <t> [d]) x)) => (Sub16 (Const16 <t> [c-d]) x)` -/
theorem r_generic_1296_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1296 := by rule_auto

/-- `generic.rules:131`: `(Sub32 (Const32 [c]) (Const32 [d])) => (Const32 [c-d])` -/
theorem r_generic_131_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_131 := by rule_auto

/-- `generic.rules:392`: `(Sub32 x (Const32 <t> [c])) && x.Op != OpConst32 => (Add32 (Const32 <t> [-c]) x)` -/
theorem r_generic_392_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_392 := by rule_auto

/-- `generic.rules:422`: `(Sub32 <t> (Mul32 x y) (Mul32 x z)) => (Mul32 x (Sub32 <t> y z))` -/
theorem r_generic_422_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_422_2 := by rule_auto

/-- `generic.rules:647`: `(Sub32 x x) => (Const32 [0])` -/
theorem r_generic_647_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_647_2 := by rule_auto

/-- `generic.rules:659`: `(Sub32 (Neg32 x) (Com32 x)) => (Const32 [1])` -/
theorem r_generic_659_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_659_2 := by rule_auto

/-- `generic.rules:660`: `(Sub32 (Com32 x) (Neg32 x)) => (Const32 [-1])` -/
theorem r_generic_660_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_660_2 := by rule_auto

/-- `generic.rules:674`: `(Sub32 (Add32 t x) (Add32 t y)) => (Sub32 x y)` -/
theorem r_generic_674_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_674_2 := by rule_auto

/-- `generic.rules:774`: `(Sub32 (Add32 x y) x) => y` -/
theorem r_generic_774_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_774_2 := by rule_auto

/-- `generic.rules:775`: `(Sub32 (Add32 x y) y) => x` -/
theorem r_generic_775_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_775_2 := by rule_auto

/-- `generic.rules:776`: `(Sub32 (Sub32 x y) x) => (Neg32 y)` -/
theorem r_generic_776_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_776_2 := by rule_auto

/-- `generic.rules:777`: `(Sub32 x (Add32 x y)) => (Neg32 y)` -/
theorem r_generic_777_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_777_2 := by rule_auto

/-- `generic.rules:1229`: `(Sub32 x (Sub32 i:(Const32 <t>) z)) && (z.Op != OpConst32 && x.Op != OpConst32) => (Sub32 (Add32 <t> x z) i)` -/
theorem r_generic_1229_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1229 := by rule_auto

/-- `generic.rules:1235`: `(Sub32 x (Add32 z i:(Const32 <t>))) && (z.Op != OpConst32 && x.Op != OpConst32) => (Sub32 (Sub32 <t> x z) i)` -/
theorem r_generic_1235_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1235 := by rule_auto

end GoFV.Proof.Rules
