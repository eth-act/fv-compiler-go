import GoFV.Proof.AtomSimDen

/-!
# Applying `TermRef` to registers (issue #113)

`termRef_apply`: if `x`'s register in the source frame and `y`'s in the target frame are their
terms' values over the atoms (`DenOK`), the atoms both frames hold are refined, and the atoms'
registers are fixed by `retype` at their shapes, then `TermRef … x … y` gives
`rv FS x ⊑ rv FT y`. The valuations are the frames' atom registers (`poison` elsewhere); the
target's falls back to the source's on the atoms only the source holds.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

theorem retype_poison (t : Ty) : Val.poison.retype t = .poison := by cases t <;> rfl

/-- A context's shape of a value is `shape` of its function's value table. -/
theorem tys_shape (tabs : Tables) (f : Func) (a : ID) :
    (Ctx.make tabs f).tys[a]?.getD .other = shape f.value? tabs a := by
  cases hv : f.value? a with
  | some v => rw [tys_of_value hv]; simp [shape, hv]
  | none =>
    simp only [shape, hv, Option.map_none, Option.getD_none]
    simp only [Ctx.make, Array.getElem?_map]
    unfold Func.value? at hv
    cases h : f.valueTab[a]? with
    | none => rfl
    | some o =>
      rw [h] at hv
      cases o with
      | none => rfl
      | some v => cases hv

/-- **`TermRef` on registers.** -/
theorem termRef_apply {D E : ID → Option Value} {tabs : Tables} {x y : ID}
    (hT : TermRef D tabs x E tabs y) {FS FT : Frame} {VS VT : ID → Prop}
    (hS : DenOK D tabs FS VS) (hxS : VS x) (hG : DenOK E tabs FT VT) (hyT : VT y)
    (hrel : ∀ a, VS a → ¬ IsTerm D a → VT a → ¬ IsTerm E a → Sem.Refines (rv FS a) (rv FT a))
    (htyS : ∀ a, VS a → ¬ IsTerm D a → (rv FS a).retype (shape D tabs a) = rv FS a)
    (htyT : ∀ a, VT a → ¬ IsTerm E a → (rv FT a).retype (shape E tabs a) = rv FT a)
    (hsh : ∀ a, VS a → ¬ IsTerm D a → ¬ IsTerm E a → (E a).isSome → ¬ VT a →
      (rv FS a).retype (shape E tabs a) = rv FS a) :
    Sem.Refines (rv FS x) (rv FT y) := by
  classical
  let ρ : ID → Val := fun a => if VS a ∧ ¬ IsTerm D a then rv FS a else .poison
  let ρ' : ID → Val := fun a => if VT a ∧ ¬ IsTerm E a then rv FT a else ρ a
  obtain ⟨N, hN⟩ := (hS x hxS).2 ρ fun a ha hat => by simp [ρ, ha, hat]
  obtain ⟨m, hm⟩ := hT N
  obtain ⟨M, hM⟩ := (hG y hyT).2 ρ' fun a ha hat => by simp [ρ', ha, hat]
  have hval : ValRef ρ ρ' := fun a => by
    by_cases h1 : VT a ∧ ¬ IsTerm E a
    · by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ', ρ, h1, h2]
        exact hrel a h2.1 h2.2 h1.1 h1.2
      · simp only [ρ', ρ, h1, h2, ite_false]
        exact .poison _
    · simp only [ρ', h1, ite_false]; exact Sem.Refines.refl _
  have htD : Term.Typed D tabs ρ := fun a hat _ => by
    by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact htyS a h2 hat
    · simp only [ρ, h2, false_and, ite_false]; exact retype_poison _
  have htE : Term.Typed E tabs ρ' := fun a hat hdef => by
    by_cases h1 : VT a
    · simp only [ρ', h1, hat, not_false_eq_true, and_self, ite_true]; exact htyT a h1 hat
    · simp only [ρ', h1, false_and, ite_false]
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · simp only [ρ, h2]; exact hsh a h2.1 h2.2 hat hdef h1
      · simp only [ρ, h2, ite_false]; exact retype_poison _
  have h := hm ρ ρ' hval htD htE
  rw [hN N (Nat.le_refl N)] at h
  rw [← hM (max m M) (Nat.le_max_right m M)]
  exact Sem.Refines.trans h (den_fuel_mono E tabs ρ' m (max m M) y (Nat.le_max_left m M))

end GoFV.Proof.AtomSim
