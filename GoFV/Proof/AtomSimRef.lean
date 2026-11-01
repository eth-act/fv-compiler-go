import GoFV.Proof.AtomSimDen

/-!
# Applying `TermRef` to registers (issue #113)

`TermRefP P Q S`: `TermRef` for valuations satisfying a source-side invariant `P` (at the atoms,
and eventually at the denotations of the values of `S`), the frame-level invariant `Q` and
`MemAtoms` (memory roots hold the write of their arguments' terms, issue #151), the premise of
the atom simulation under an invariant (`AtomSim.Inv`); `TermRef` implies it (`TermRef.toP`).
The fuel on the right may depend on the valuations.

`termRef_apply`: if `x`'s register in the source frame and `y`'s in the target frame are their
terms' values over the atoms (`DenOK`), the atoms both frames hold are refined, the atoms'
registers are fixed by `retype` at their shapes, the source's registers satisfy `P` and its
memory roots hold their writes (`MemDefs`), then `TermRefP P S … x … y` gives
`rv FS x ⊑ rv FT y`. The valuations are the frames' atom registers (`poison` elsewhere); the
target's falls back to the source's on the atoms only the source holds.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- `y` in `E` refines `x` in `D` as a term over the atoms, for source valuations whose atoms
satisfy `P`, whose values of `S` eventually denote values satisfying `P`, which satisfy `Q`
and whose memory roots hold the writes of their arguments (`MemAtoms`). -/
def TermRefP (P : ID → Val → Prop) (Q : (ID → Val) → Prop) (S : ID → Prop)
    (D : ID → Option Value) (tabs : Tables) (x : ID) (E : ID → Option Value) (tabs' : Tables)
    (y : ID) : Prop :=
  ∀ ρ ρ', ValRef ρ ρ' → Term.Typed D tabs ρ → Term.Typed E tabs' ρ' →
    (∀ a, ¬ IsTerm D a → P a (ρ a)) → (∀ a, S a → ∃ N, ∀ k, N ≤ k → P a (den D tabs ρ k a)) →
    Q ρ → MemAtoms D tabs ρ → ∀ n, ∃ m, Sem.Refines (den D tabs ρ n x) (den E tabs' ρ' m y)

theorem TermRef.toP {D E : ID → Option Value} {tabs tabs' : Tables} {x y : ID}
    (h : TermRef D tabs x E tabs' y) (P : ID → Val → Prop) (Q : (ID → Val) → Prop)
    (S : ID → Prop) : TermRefP P Q S D tabs x E tabs' y := fun ρ ρ' h1 h2 h3 _ _ _ _ n =>
  let ⟨m, hm⟩ := h n
  ⟨m, hm ρ ρ' h1 h2 h3⟩

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

/-- **`TermRefP` on registers.** -/
theorem termRef_apply {P : ID → Val → Prop} {Q : (ID → Val) → Prop} {S : ID → Prop}
    {D E : ID → Option Value} {tabs : Tables} {x y : ID}
    (hT : TermRefP P Q S D tabs x E tabs y) {FS FT : Frame} {VS VT : ID → Prop}
    (hS : DenOK D tabs FS VS) (hxS : VS x) (hG : DenOK E tabs FT VT) (hyT : VT y)
    (hrel : ∀ a, VS a → ¬ IsTerm D a → VT a → ¬ IsTerm E a → Sem.Refines (rv FS a) (rv FT a))
    (htyS : ∀ a, VS a → ¬ IsTerm D a → (rv FS a).retype (shape D tabs a) = rv FS a)
    (htyT : ∀ a, VT a → ¬ IsTerm E a → (rv FT a).retype (shape E tabs a) = rv FT a)
    (hsh : ∀ a, VS a → ¬ IsTerm D a → ¬ IsTerm E a → (E a).isSome → ¬ VT a →
      (rv FS a).retype (shape E tabs a) = rv FS a)
    (hP : ∀ a, P a (rv FS a)) (hpois : ∀ a, ¬ IsTerm D a → P a .poison) (hSV : ∀ a, S a → VS a)
    (hQ : ∀ ρ : ID → Val, (∀ a, ρ a = rv FS a ∨ ρ a = .poison) → Q ρ)
    (hMS : MemDefs D tabs FS VS) :
    Sem.Refines (rv FS x) (rv FT y) := by
  classical
  let ρ : ID → Val := fun a => if VS a ∧ ¬ IsTerm D a then rv FS a else .poison
  let ρ' : ID → Val := fun a => if VT a ∧ ¬ IsTerm E a then rv FT a else ρ a
  obtain ⟨N, hN⟩ := (hS x hxS).2 ρ fun a ha hat => by simp [ρ, ha, hat]
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
  have hPρ : ∀ a, ¬ IsTerm D a → P a (ρ a) := fun a hat => by
    by_cases h2 : VS a
    · simp only [ρ, h2, hat, not_false_eq_true, and_self, ite_true]; exact hP a
    · simp only [ρ, h2, false_and, ite_false]; exact hpois a hat
  have hPS : ∀ a, S a → ∃ N, ∀ k, N ≤ k → P a (den D tabs ρ k a) := fun a ha => by
    obtain ⟨N', hN'⟩ := (hS a (hSV a ha)).2 ρ fun b hb hbt => by simp [ρ, hb, hbt]
    exact ⟨N', fun k hk => by rw [hN' k hk]; exact hP a⟩
  have hQρ : Q ρ := hQ ρ fun a => by
    by_cases h2 : VS a ∧ ¬ IsTerm D a
    · exact .inl (ite_eq_left h2)
    · exact .inr (ite_eq_right h2)
  have hMA : MemAtoms D tabs ρ := memAtoms_of hS hMS (fun a ha hat => by simp [ρ, ha, hat])
    fun a hat hne => by
      by_cases h2 : VS a ∧ ¬ IsTerm D a
      · exact h2.1
      · exact absurd (ite_eq_right h2) hne
  obtain ⟨m, h⟩ := hT ρ ρ' hval htD htE hPρ hPS hQρ hMA N
  rw [hN N (Nat.le_refl N)] at h
  rw [← hM (max m M) (Nat.le_max_right m M)]
  exact Sem.Refines.trans h (den_fuel_mono E tabs ρ' m (max m M) y (Nat.le_max_left m M))

end GoFV.Proof.AtomSim
