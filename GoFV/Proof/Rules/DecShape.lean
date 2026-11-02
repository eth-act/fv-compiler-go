import GoFV.Proof.Rules.Den
import GoFV.Proof.Retype
import GoFV.Proof.ValRefine

/-!
# Shapes of composites: selections of `Make`s (issue #17)

Facts the dec rule lemmas (`GoFV/Proof/Rules/Dec.lean`) and the validator's selection tops
(`RewriteCheck.selTop`, `GoFV/Proof/Pass/RewriteTermNat.lean`) share: `shapeSub` (a value of
one shape has the other), and a selection of component `k` of a `Make` retyped at a composite
shape gives the `k`-th argument back when the arguments have the components' shapes
(`Pat.argsOK` of the `Make`, `makeArgOk`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- `shapeSub f t`: a value of shape `f` has shape `t`. -/
theorem shapeSub_hasTy {f t : Ty} (h : shapeSub f t = true) {v : Val}
    (hv : v.hasTy f = true) : v.hasTy t = true := by
  simp only [shapeSub, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨hf, ht⟩
  · rw [← Ty.eq_of_beq h]; exact hv
  · cases f <;> simp only [isPtrTy, Bool.false_eq_true] at hf
    cases t <;> simp only [isPtrTy, Bool.false_eq_true] at ht
    rcases v with ⟨_ | _ | _ | _, _⟩ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp_all [Val.hasTy]

/-- `retype` at a shape `f` that a value's shape `t` is `shapeSub` of keeps the value. -/
theorem retype_of_shapeSub {t f : Ty} {v : Val} (hv : v.hasTy t = true) (h : shapeSub t f = true) :
    v.retype f = v :=
  Val.retype_of_hasTy (shapeSub_hasTy h hv)

/-- The components of a successful `retypeFields`. -/
theorem retypeFields_get : ∀ {fs : List (Nat × Ty)} {vs vs' : List Val},
    Val.retypeFields fs vs = some vs' → ∀ k : Nat,
      (vs'[k]? = none ∧ vs[k]? = none) ∨
        ∃ (v : Val) (f : Nat × Ty), vs[k]? = some v ∧ fs[k]? = some f ∧ vs'[k]? = some (v.retype f.2)
  | [], [], vs', h, _ => by
    simp only [Val.retypeFields, Option.some.injEq] at h; subst h; exact .inl ⟨rfl, rfl⟩
  | (o, t) :: fs, v :: vs, vs', h, k => by
    simp only [Val.retypeFields, Option.map_eq_some_iff] at h
    obtain ⟨ws, hws, rfl⟩ := h
    cases k with
    | zero => exact .inr ⟨v, (o, t), rfl, rfl, rfl⟩
    | succ k => simpa using retypeFields_get hws k
  | [], _ :: _, _, h, _ | _ :: _, [], _, h, _ => by simp [Val.retypeFields] at h

theorem makeArgOk_asAgg (T : Ty) (i : Nat) (t : Ty) : makeArgOk T.asAgg i t = makeArgOk T i t := by
  simp only [makeArgOk, fieldShape?, Ty.asAgg_asAgg]

theorem fieldShape?_asAgg (T : Ty) (i : Nat) : fieldShape? T.asAgg i = fieldShape? T i := by
  simp only [fieldShape?, Ty.asAgg_asAgg]

private theorem select_retype_make_agg (T : Ty) (hT : T.asAgg = T) (k : Nat) (vs : List Val)
    (ts : List Ty)
    (hv : ∀ i v t, vs[i]? = some v → ts[i]? = some t → v.hasTy t = true ∧ makeArgOk T i t = true)
    (hl : vs.length = ts.length) :
    Refines (Comp.select k [(Comp.make vs).retype T]) (vs.getD k .poison) := by
  unfold Comp.make
  cases T
  case agg fs n =>
    simp only [Val.retype]
    split
    · rename_i vs' hr
      simp only [Comp.select]
      rcases retypeFields_get hr k with ⟨h1, h2⟩ | ⟨v, f, h1, h2, h3⟩
      · simp [List.getD, h1, h2]; exact .poison _
      · have hk : k < ts.length := by
          rw [← hl]; exact (List.getElem?_eq_some_iff.1 h1).1
        obtain ⟨t, ht⟩ : ∃ t, ts[k]? = some t := ⟨ts[k], List.getElem?_eq_getElem hk⟩
        obtain ⟨hvt, hm⟩ := hv k v t h1 ht
        simp only [makeArgOk, fieldShape?, Ty.asAgg, h2, Option.map_some] at hm
        simp only [List.getD, h1, h3, Option.getD_some, retype_of_shapeSub hvt hm]
        exact Refines.refl _
    · exact .poison _
  case str => simp [Ty.asAgg, Ty.strAgg] at hT
  case slice => simp [Ty.asAgg, Ty.sliceAgg] at hT
  all_goals exact .poison _

/-- **Selection of a `Make`**: component `k` of `Make vs` retyped at `T` is the `k`-th argument
(or `poison`) when every argument has a shape `makeArgOk` accepts for `T`. -/
theorem select_retype_make (T : Ty) (k : Nat) (vs : List Val) (ts : List Ty)
    (hv : ∀ i v t, vs[i]? = some v → ts[i]? = some t → v.hasTy t = true ∧ makeArgOk T i t = true)
    (hl : vs.length = ts.length) :
    Refines (Comp.select k [(Comp.make vs).retype T]) (vs.getD k .poison) := by
  rw [retype_asAgg]
  rcases Val.checkLen_eq_or T ((Comp.make vs).retype T.asAgg) with h | h <;> rw [h]
  · exact select_retype_make_agg _ (Ty.asAgg_asAgg T) k vs ts
      (fun i v t h1 h2 => by rw [makeArgOk_asAgg]; exact hv i v t h1 h2) hl
  · exact .poison _

private theorem select_retype_make_get_agg (T : Ty) (hT : T.asAgg = T) (k : Nat) (vs : List Val) :
    Comp.select k [(Comp.make vs).retype T] = .poison ∨
      ∃ f v, fieldShape? T k = some f ∧ vs[k]? = some v ∧
        Comp.select k [(Comp.make vs).retype T] = v.retype f := by
  unfold Comp.make
  cases T
  case agg fs n =>
    simp only [Val.retype]
    split
    · rename_i vs' hr
      simp only [Comp.select]
      rcases retypeFields_get hr k with ⟨h1, -⟩ | ⟨v, f, h1, h2, h3⟩
      · exact .inl (by simp [List.getD, h1])
      · exact .inr ⟨f.2, v, by simp [fieldShape?, Ty.asAgg, h2], h1, by simp [List.getD, h3]⟩
    · exact .inl rfl
  case str => simp [Ty.asAgg, Ty.strAgg] at hT
  case slice => simp [Ty.asAgg, Ty.sliceAgg] at hT
  all_goals exact .inl rfl

/-- Component `k` of `Make vs` retyped at `T`: `poison`, or argument `k` retyped at component
`k`'s shape (the variadic selection `RewriteCheck.makeSelOK`, issue #17). -/
theorem select_retype_make_get (T : Ty) (k : Nat) (vs : List Val) :
    Comp.select k [(Comp.make vs).retype T] = .poison ∨
      ∃ f v, fieldShape? T k = some f ∧ vs[k]? = some v ∧
        Comp.select k [(Comp.make vs).retype T] = v.retype f := by
  rw [retype_asAgg]
  rcases Val.checkLen_eq_or T ((Comp.make vs).retype T.asAgg) with h | h <;> rw [h]
  · rw [← fieldShape?_asAgg]
    exact select_retype_make_get_agg _ (Ty.asAgg_asAgg T) k vs
  · exact .inl rfl

/-! ## The kind predicates (`kindE`) -/

/-- `IsPtrShaped` is true only of a pointer shape. -/
theorem kindE_ptrShaped_true {t : Ty} (h : kindE .ptrShaped t = some true) : ∃ e, t = .ptr e := by
  cases t <;> simp_all [kindE]

/-- `IsString` is not false only at the string shape or `.other`. -/
theorem kindE_string {t : Ty} (h : kindE .string t ≠ some false) : strShape t = true ∨ t = .other := by
  cases t <;> simp_all [kindE] <;> split at h <;> simp_all

theorem kindE_slice {t : Ty} (h : kindE .slice t ≠ some false) : sliceShape t = true ∨ t = .other := by
  cases t <;> simp_all [kindE] <;> split at h <;> simp_all

theorem kindE_inter {t : Ty} (h : kindE .inter t ≠ some false) : interShape t = true ∨ t = .other := by
  cases t <;> simp_all [kindE] <;> split at h <;> simp_all

theorem kindE_complex {t : Ty} (h : kindE .complex t ≠ some false) :
    complexShape t = true ∨ t = .other := by
  cases t <;> simp_all [kindE] <;> split at h <;> simp_all

end GoFV.Proof.Rules
