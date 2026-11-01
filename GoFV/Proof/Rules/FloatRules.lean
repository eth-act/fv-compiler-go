import GoFV.Proof.Rules.FloatCmp
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values09

/-!
# Rule lemmas: float comparisons

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the 64-bit `OrB (Neq64F x x) (cmp …)` rules
(`generic.rules:375–386`: a NaN `x` makes `Neq x x` true and every ordered comparison false, so
the disjunction is the negated swapped comparison; `float_auto`) and of the float constant folds
(`generic.rules:622–629`, `float_const`). The constants of the comparisons are not NaN
(`auxIntOk`, check.go). The 32-bit `OrB` rules (377/378/387/388) are not proved: their constant
is the binary32 conversion of a non-NaN float64, which needs `isNaN` of `IEEE.convert`'s rounding.
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:375`: `(OrB (Neq64F x x) (Less64F x y:(Const64F [c]))) => (Not (Leq64F y x))` -/
theorem r_generic_375_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_375 := by
  float_auto

/-- `generic.rules:375`: `(OrB (Neq64F x x) (Leq64F x y:(Const64F [c]))) => (Not (Less64F y x))` -/
theorem r_generic_375_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_375_2 := by
  float_auto

/-- `generic.rules:376`: `(OrB (Neq64F x x) (Less64F y:(Const64F [c]) x)) => (Not (Leq64F x y))` -/
theorem r_generic_376_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_376 := by
  float_auto

/-- `generic.rules:376`: `(OrB (Neq64F x x) (Leq64F y:(Const64F [c]) x)) => (Not (Less64F x y))` -/
theorem r_generic_376_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_376_2 := by
  float_auto

/-- `generic.rules:381`: `(OrB (Neq64F x x) (Less64F abs:(Abs x) y:(Const64F [c]))) => (Not (Leq64F y abs))` -/
theorem r_generic_381_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_381 := by
  float_auto

/-- `generic.rules:381`: `(OrB (Neq64F x x) (Leq64F abs:(Abs x) y:(Const64F [c]))) => (Not (Less64F y abs))` -/
theorem r_generic_381_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_381_2 := by
  float_auto

/-- `generic.rules:382`: `(OrB (Neq64F x x) (Less64F y:(Const64F [c]) abs:(Abs x))) => (Not (Leq64F abs y))` -/
theorem r_generic_382_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_382 := by
  float_auto

/-- `generic.rules:382`: `(OrB (Neq64F x x) (Leq64F y:(Const64F [c]) abs:(Abs x))) => (Not (Less64F abs y))` -/
theorem r_generic_382_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_382_2 := by
  float_auto

/-- `generic.rules:385`: `(OrB (Neq64F x x) (Less64F neg:(Neg64F x) y:(Const64F [c]))) => (Not (Leq64F y neg))` -/
theorem r_generic_385_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_385 := by
  float_auto

/-- `generic.rules:385`: `(OrB (Neq64F x x) (Leq64F neg:(Neg64F x) y:(Const64F [c]))) => (Not (Less64F y neg))` -/
theorem r_generic_385_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_385_2 := by
  float_auto

/-- `generic.rules:386`: `(OrB (Neq64F x x) (Less64F y:(Const64F [c]) neg:(Neg64F x))) => (Not (Leq64F neg y))` -/
theorem r_generic_386_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_386 := by
  float_auto

/-- `generic.rules:386`: `(OrB (Neq64F x x) (Leq64F y:(Const64F [c]) neg:(Neg64F x))) => (Not (Less64F neg y))` -/
theorem r_generic_386_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_386_2 := by
  float_auto

/-- `generic.rules:622`: `(Eq32F (Const32F [c]) (Const32F [d])) => (ConstBool [c == d])` -/
theorem r_generic_622_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_622 := by
  float_const

/-- `generic.rules:623`: `(Eq64F (Const64F [c]) (Const64F [d])) => (ConstBool [c == d])` -/
theorem r_generic_623_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_623 := by
  float_const

/-- `generic.rules:624`: `(Neq32F (Const32F [c]) (Const32F [d])) => (ConstBool [c != d])` -/
theorem r_generic_624_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_624 := by
  float_const

/-- `generic.rules:625`: `(Neq64F (Const64F [c]) (Const64F [d])) => (ConstBool [c != d])` -/
theorem r_generic_625_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_625 := by
  float_const

/-- `generic.rules:626`: `(Less32F (Const32F [c]) (Const32F [d])) => (ConstBool [c < d])` -/
theorem r_generic_626_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_626 := by
  float_const

/-- `generic.rules:627`: `(Less64F (Const64F [c]) (Const64F [d])) => (ConstBool [c < d])` -/
theorem r_generic_627_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_627 := by
  float_const

/-- `generic.rules:628`: `(Leq32F (Const32F [c]) (Const32F [d])) => (ConstBool [c <= d])` -/
theorem r_generic_628_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_628 := by
  float_const

/-- `generic.rules:629`: `(Leq64F (Const64F [c]) (Const64F [d])) => (ConstBool [c <= d])` -/
theorem r_generic_629_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_629 := by
  float_const

end GoFV.Proof.Rules
