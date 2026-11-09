import GoFV.Proof.ProveCheck.Den
import GoFV.Proof.Pass.RewriteTermDen

variable [GoFV.SSA.Sem.Addrs]

/-!
# Components of composites, as prove's validator reads them (issue #24)

`canon_den`: a `SliceLen`/`StringLen`/`SliceCap` of a `SliceMake`/`StringMake` (`projOf`) has
its component's value whenever it is an integer — the composite retypes the component at its
field's shape, which is the component's own (`retypeFields_get`), and `den` is fixed by
`retype` at a value's shape (`den_retype`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

theorem pTab_cases {op : Op} {i : Nat} (h : pTab.lookup op = some i) :
    termOp op = true ∧ ∀ tabs ty ai aux args,
      GoFV.Proof.Rules.opVal tabs op ty ai aux args = Comp.select i args := by
  have hm := mem_of_lookup h
  simp only [pTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, fun _ _ _ _ _ => rfl⟩

theorem mkTab_cases {op : Op} {u : Unit} (h : mkTab.lookup op = some u) :
    termOp op = true ∧ ∀ tabs ty ai aux args,
      GoFV.Proof.Rules.opVal tabs op ty ai aux args = Comp.make args := by
  have hm := mem_of_lookup h
  simp only [mkTab, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact ⟨rfl, fun _ _ _ _ _ => rfl⟩

/-- A component of a composite retyped field by field. -/
theorem retypeFields_get : ∀ {fs : List (Nat × Ty)} {vs vs' : List Val},
    Val.retypeFields fs vs = some vs' → ∀ {i : Nat} {o : Nat} {t : Ty} {v : Val},
      fs[i]? = some (o, t) → vs[i]? = some v → vs'[i]? = some (v.retype t)
  | [], [], _, h, _, _, _, _, hf, _ => by simp at hf
  | (_, t) :: fs, v :: vs, vs', h, i, o, t', v', hf, hv => by
    simp only [Val.retypeFields] at h
    cases hr : Val.retypeFields fs vs with
    | none => rw [hr] at h; cases h
    | some ws =>
      rw [hr] at h
      cases h
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hf hv
        rw [← hf.2, ← hv]; rfl
      | succ i =>
        simp only [List.getElem?_cons_succ] at hf hv ⊢
        exact retypeFields_get hr hf hv
  | [], _ :: _, _, h, _, _, _, _, _, _ => by simp [Val.retypeFields] at h
  | _ :: _, [], _, h, _, _, _, _, _, _ => by simp [Val.retypeFields] at h

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

/-- A component's value: its component's two levels down, or `poison`. -/
theorem projOf_den (hT : Term.Typed D tabs ρ) {x y : ID} (h : projOf D tabs x = some y) :
    ∀ n, den D tabs ρ n x = .poison ∨ ∃ m, n = m + 2 ∧ den D tabs ρ n x = den D tabs ρ m y := by
  unfold projOf at h
  cases hx : D x with
  | none => rw [hx] at h; cases h
  | some v =>
  rw [hx] at h
  dsimp only at h
  split at h
  · rename_i i s hi hargs
    cases hs : D s with
    | none => rw [hs] at h; cases h
    | some sv =>
    rw [hs] at h
    dsimp only at h
    split at h
    · rename_i fs sz y' w hmk hty hy hw
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      split at h
      · rename_i hc
        cases h
        obtain ⟨hfw, hyw⟩ := hc
        obtain ⟨ht, he⟩ := pTab_cases hi
        obtain ⟨hst, hse⟩ := mkTab_cases hmk
        have hT' := width_some hw
        intro n
        rcases n with _ | _ | m
        · exact .inl rfl
        · left
          rw [den_succ_term hx ht, he, hargs]
          simp only [List.map_cons, List.map_nil, den, Comp.select]
          exact retype_poison' _
        · rw [den_succ_term hx ht, he, hargs]
          simp only [List.map_cons, List.map_nil]
          rw [den_succ_term hs hst, hse, retype_asAgg (tabs.ty sv.type), hty]
          simp only [Comp.make, Val.retype]
          cases hr : Val.retypeFields fs (sv.args.toList.map (den D tabs ρ m)) with
          | none =>
            left
            simp only [Val.checkLen_poison, Comp.select]
            exact retype_poison' _
          | some vs' =>
          rcases (Val.checkLen_eq_or (tabs.ty sv.type) (.agg vs')).symm with hc | hc <;> rw [hc]
          · left
            simp only [Comp.select]
            exact retype_poison' _
          right
          refine ⟨m, rfl, ?_⟩
          -- the field of `y`
          obtain ⟨⟨o, t⟩, hfi, htw⟩ : ∃ q, fs[i]? = some q ∧ q.2.width? = some w := by
            cases hq : fs[i]? with
            | none => rw [hq] at hfw; cases hfw
            | some q => rw [hq] at hfw; exact ⟨q, rfl, hfw⟩
          have htt := width_some htw
          dsimp only at htt
          subst htt
          have hyi : (sv.args.toList.map (den D tabs ρ m))[i]? = some (den D tabs ρ m y) := by
            rw [List.getElem?_map, Array.getElem?_toList, hy]; rfl
          unfold widthOf at hyw
          cases hyd : D y with
          | none => rw [hyd] at hyw; cases hyw
          | some yv =>
          rw [hyd] at hyw
          have hyt := width_some (by simpa using hyw)
          have hfix : (den D tabs ρ m y).retype (.int w) = den D tabs ρ m y := by
            have := GoFV.Proof.Pass.Rewrite.den_retype hT m y (by rw [hyd]; rfl)
            rwa [GoFV.Proof.Pass.Rewrite.shape_of hyd, hyt] at this
          have hg := retypeFields_get hr hfi hyi
          simp only [Comp.select, List.getD_eq_getElem?_getD, hg, Option.getD_some, hT',
            Val.retype_idem, hfix]
      · cases h
    · cases h
  · cases h

/-- `x`'s value is `poison` or a value of its `canon`ical form. -/
theorem canon_cases (hT : Term.Typed D tabs ρ) (x : ID) (n : Nat) :
    den D tabs ρ n x = .poison ∨ ∃ m, den D tabs ρ n x = den D tabs ρ m (canon D tabs x) := by
  unfold canon
  cases hp : projOf D tabs x with
  | none => exact .inr ⟨n, rfl⟩
  | some y =>
    rcases projOf_den hT hp n with e | ⟨m, -, e⟩
    · exact .inl e
    · exact .inr ⟨m, e⟩

/-- **`canon` keeps an integer value.** -/
theorem canon_den (hT : Term.Typed D tabs ρ) {K : Nat} {x : ID} {w : Width} {z : BitVec w.bits}
    (h : den D tabs ρ K x = .int w z) : den D tabs ρ K (canon D tabs x) = .int w z := by
  unfold canon
  cases hp : projOf D tabs x with
  | none => exact h
  | some y =>
    rcases projOf_den hT hp K with e | ⟨m, rfl, e⟩
    · rw [e] at h; cases h
    · rw [e] at h; exact den_stable_int h (by omega)
end

end GoFV.Proof.ProveCheck
