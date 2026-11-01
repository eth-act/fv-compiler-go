import GoFV.Proof.Rules.OneBit
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values09

/-!
# Single-bit equality tests, `OrB` form (`generic.rules:372`)

`rule_onebit` (`OneBit.lean`) for the `OrB`/`Eq` rows, and witnesses for both forms.
-/

namespace GoFV.Proof.Rules

open GoFV.Proof.Rules.KernelSafe

/-- `generic.rules:372`: `(OrB (Eq64 x cv:(Const64 [c])) (Eq64 x (Const64 [d]))) && c|d == c && oneBit(c^d) => (Eq64 (Or64 <x.Type> x (Const64 <x.Type> [c^d])) cv)` -/
theorem r_generic_372_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_372 := by
  rule_onebit

/-- `generic.rules:372`: `(OrB (Eq32 x cv:(Const32 [c])) (Eq32 x (Const32 [d]))) && c|d == c && oneBit(c^d) => (Eq32 (Or32 <x.Type> x (Const32 <x.Type> [c^d])) cv)` -/
theorem r_generic_372_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_372_2 := by
  rule_onebit

/-- `generic.rules:372`: `(OrB (Eq16 x cv:(Const16 [c])) (Eq16 x (Const16 [d]))) && c|d == c && oneBit(c^d) => (Eq16 (Or16 <x.Type> x (Const16 <x.Type> [c^d])) cv)` -/
theorem r_generic_372_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_372_3 := by
  rule_onebit

/-- `generic.rules:372`: `(OrB (Eq8 x cv:(Const8 [c])) (Eq8 x (Const8 [d]))) && c|d == c && oneBit(c^d) => (Eq8 (Or8 <x.Type> x (Const8 <x.Type> [c^d])) cv)` -/
theorem r_generic_372_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_372_4 := by
  rule_onebit

/-- `generic.rules:372` at `x = 2`, `c = 3`, `d = 2` (`c^d = 1`). -/
theorem inst_r_generic_372 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_372
    (PEnv.ofLists [([0, 0], .i64 2), ([0, 1], .i64 2)] [([], .bool), ([0], .bool), ([1], .bool)]
      (.int .w64) [([1, 0], 3), ([1, 1], 2)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_372]
  rule_eval
  rfl

/-- `generic.rules:369` at `x = 2`, `c = 3`, `d = 2` (`c^d = 1`). -/
theorem inst_r_generic_369 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_369
    (PEnv.ofLists [([0, 0], .i64 2), ([0, 1], .i64 2)] [([], .bool), ([0], .bool), ([1], .bool)]
      (.int .w64) [([1, 0], 3), ([1, 1], 2)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_369]
  rule_eval
  rfl

end GoFV.Proof.Rules
