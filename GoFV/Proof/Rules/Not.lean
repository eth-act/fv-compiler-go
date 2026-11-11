import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Not` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Not` family (`docs/proofs/rules.md`). The `EqPtr`/`NeqPtr` and float variants of
`generic.rules:397`/`:398` by hand: in the semantics `NeqPtr` is `EqPtr` negated (`eqPtr neg`,
`poison` on a non-word, pointer equality by block and offset) and `Neq{32,64}F` is
`Eq{32,64}F` negated (both read `FPCompare`'s result: a NaN operand gives `un`, so `Eq` is false
and `Neq` true, as in Go), so `Not` of one is the other or `poison` (`notCmp_refines`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem in
/-- `poison` or a Boolean. -/
private def BoolOrPoison (x : Val) : Prop := x = .poison ∨ ∃ c, x = .bool c

open GoFV.SSA GoFV.SSA.Sem in
private theorem eqPtr_not (neg : Bool) (args : List Val) :
    PtrOps.eqPtr (!neg) args = Cmp.not [PtrOps.eqPtr neg args] ∧
      BoolOrPoison (PtrOps.eqPtr neg args) := by
  unfold PtrOps.eqPtr
  split
  · split
    · refine ⟨?_, .inr ⟨_, rfl⟩⟩
      simp only [Cmp.not, bool1, Val.asBool]
      cases neg <;> simp
    · exact ⟨rfl, .inl rfl⟩
  · exact ⟨rfl, .inl rfl⟩

open GoFV.SSA GoFV.SSA.Sem in
omit [GoFV.SSA.Sem.Addrs] in
private theorem fneq_not (w : Width) (args : List Val) :
    FOps.neq w args = Cmp.not [FOps.eq w args] ∧ BoolOrPoison (FOps.eq w args) := by
  unfold FOps.neq FOps.eq FOps.cmpC int2
  cases w <;> try exact ⟨rfl, .inl rfl⟩
  all_goals
    dsimp only
    split
    · split
      · refine ⟨?_, .inr ⟨_, rfl⟩⟩
        simp only [Cmp.not, bool1, Val.asBool, FOps.ordered]
        split <;> simp [bne]
      · exact ⟨rfl, .inl rfl⟩
    · exact ⟨rfl, .inl rfl⟩

open GoFV.SSA GoFV.SSA.Sem in
omit [GoFV.SSA.Sem.Addrs] in
private theorem feq_not (w : Width) (args : List Val) :
    FOps.eq w args = Cmp.not [FOps.neq w args] ∧ BoolOrPoison (FOps.neq w args) := by
  unfold FOps.neq FOps.eq FOps.cmpC int2
  cases w <;> try exact ⟨rfl, .inl rfl⟩
  all_goals
    dsimp only
    split
    · split
      · refine ⟨?_, .inr ⟨_, rfl⟩⟩
        simp only [Cmp.not, bool1, Val.asBool, FOps.ordered]
        split <;> simp [bne]
      · exact ⟨rfl, .inl rfl⟩
    · exact ⟨rfl, .inl rfl⟩

open GoFV.SSA GoFV.SSA.Sem in
/-- `Not` of a comparison `x` retyped to its matched type refines `Not x` at the top type. -/
private theorem notCmp_refines {x : Val} (hx : BoolOrPoison x) {t0 t : Ty}
    (hty : (Cmp.not [x.retype t0]).hasTy t = true) :
    Refines (Cmp.not [x.retype t0]) ((Cmp.not [x]).retype t) := by
  rcases hx with rfl | ⟨c, rfl⟩
  · simp only [retype_poison, Cmp.not, bool1, Val.asBool]; exact Refines.poison _
  · rw [retype_bool] at hty ⊢
    cases h : tyIsBool t0
    · simp only [Bool.false_eq_true, ↓reduceIte, Cmp.not, bool1, Val.asBool]
      exact Refines.poison _
    · simp only [h, ↓reduceIte] at hty ⊢
      exact refines_retype_of_hasTy hty

/-- `generic.rules:184`: `(Not (ConstBool [c])) => (ConstBool [!c])` -/
theorem r_generic_184_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_184 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq64 x y)) => (Neq64 x y)` -/
theorem r_generic_397_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq32 x y)) => (Neq32 x y)` -/
theorem r_generic_397_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_2 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq16 x y)) => (Neq16 x y)` -/
theorem r_generic_397_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_3 := by rule_auto

/-- `generic.rules:397`: `(Not (Eq8 x y)) => (Neq8 x y)` -/
theorem r_generic_397_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_4 := by rule_auto

/-- `generic.rules:397`: `(Not (EqB x y)) => (NeqB x y)` -/
theorem r_generic_397_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_5 := by rule_auto

/-- `generic.rules:397`: `(Not (EqPtr x y)) => (NeqPtr x y)` -/
theorem r_generic_397_6_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_6 := by
  rule_unfold
  obtain ⟨h, hx⟩ := eqPtr_not false [e.leaf [0, 0], e.leaf [1, 0]]
  rw [show true = !false from rfl, h]
  exact notCmp_refines hx hty

/-- `generic.rules:397`: `(Not (Eq64F x y)) => (Neq64F x y)` -/
theorem r_generic_397_7_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_7 := by
  rule_unfold
  obtain ⟨h, hx⟩ := fneq_not .w64 [e.leaf [0, 0], e.leaf [1, 0]]
  rw [h]
  exact notCmp_refines hx hty

/-- `generic.rules:397`: `(Not (Eq32F x y)) => (Neq32F x y)` -/
theorem r_generic_397_8_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_397_8 := by
  rule_unfold
  obtain ⟨h, hx⟩ := fneq_not .w32 [e.leaf [0, 0], e.leaf [1, 0]]
  rw [h]
  exact notCmp_refines hx hty

/-- `generic.rules:398`: `(Not (Neq64 x y)) => (Eq64 x y)` -/
theorem r_generic_398_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq32 x y)) => (Eq32 x y)` -/
theorem r_generic_398_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_2 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq16 x y)) => (Eq16 x y)` -/
theorem r_generic_398_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_3 := by rule_auto

/-- `generic.rules:398`: `(Not (Neq8 x y)) => (Eq8 x y)` -/
theorem r_generic_398_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_4 := by rule_auto

/-- `generic.rules:398`: `(Not (NeqB x y)) => (EqB x y)` -/
theorem r_generic_398_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_5 := by rule_auto

/-- `generic.rules:398`: `(Not (NeqPtr x y)) => (EqPtr x y)` -/
theorem r_generic_398_6_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_6 := by
  rule_unfold
  obtain ⟨h, hx⟩ := eqPtr_not true [e.leaf [0, 0], e.leaf [1, 0]]
  rw [show false = !true from rfl, h]
  exact notCmp_refines hx hty

/-- `generic.rules:398`: `(Not (Neq64F x y)) => (Eq64F x y)` -/
theorem r_generic_398_7_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_7 := by
  rule_unfold
  obtain ⟨h, hx⟩ := feq_not .w64 [e.leaf [0, 0], e.leaf [1, 0]]
  rw [h]
  exact notCmp_refines hx hty

/-- `generic.rules:398`: `(Not (Neq32F x y)) => (Eq32F x y)` -/
theorem r_generic_398_8_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_398_8 := by
  rule_unfold
  obtain ⟨h, hx⟩ := feq_not .w32 [e.leaf [0, 0], e.leaf [1, 0]]
  rw [h]
  exact notCmp_refines hx hty

/-- `generic.rules:400`: `(Not (Less64 x y)) => (Leq64 y x)` -/
theorem r_generic_400_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400 := by rule_auto

/-- `generic.rules:400`: `(Not (Less32 x y)) => (Leq32 y x)` -/
theorem r_generic_400_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400_2 := by rule_auto

/-- `generic.rules:400`: `(Not (Less16 x y)) => (Leq16 y x)` -/
theorem r_generic_400_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_400_3 := by rule_auto

end GoFV.Proof.Rules
