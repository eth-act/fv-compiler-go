import GoFV.Proof.ProveCheck.RngOp
import GoFV.Proof.ProveCheck.Proj

/-!
# The range analysis is sound (issue #24)

`rng_sound`: under assumptions that hold for the valuation `ρ` (`AsmHolds`: every path fact's
term eventually — at enough fuel — denotes its boolean, every invariant's integer values lie in
its range, every relation holds (`RelDen`), the atoms are typed), every `w`-bit integer value of
a term lies in its range. `relOf_sound` reads a path fact as a relation between its comparison's
sides.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

/-- `x ⋈ y` holds. -/
def RelHolds {n : Nat} : Rel → BitVec n → BitVec n → Prop
  | .lt s st, x, y => OrdHolds s st x y
  | .eq true, x, y => x = y
  | .eq false, x, y => x ≠ y

/-- Relation `(z, y, w, c)` holds for `ρ`: at every fuel, if `z` and `y` denote `w`-bit
integers and `y`'s is nonnegative, `z.toInt - y.toInt ≤ c`. -/
def RelDen (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) (z y : ID) (w : Width)
    (c : Int) : Prop :=
  ∀ n (Z Y : BitVec w.bits), den D tabs ρ n z = .int w Z → den D tabs ρ n y = .int w Y →
    0 ≤ Y.toInt → Z.toInt - Y.toInt ≤ c

/-- The assumptions hold for the valuation `ρ`. -/
structure AsmHolds (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) (A : Asm) : Prop where
  facts : ∀ c v, (c, v) ∈ A.facts → ∃ N, ∀ n, N ≤ n → den D tabs ρ n c = .bool v
  inv : ∀ z w r, (z, w, r) ∈ A.inv → ∀ n (y : BitVec w.bits), den D tabs ρ n z = .int w y → r.Mem y
  rels : ∀ z y w c, (z, y, w, c) ∈ A.rels → RelDen D tabs ρ z y w c
  typed : Term.Typed D tabs ρ

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem ordHolds_not {n : Nat} {s st : Bool} {x y : BitVec n} (h : ¬ OrdHolds s st x y) :
    OrdHolds s (!st) y x := by
  cases s <;> cases st <;> simp only [OrdHolds, ite_true, Bool.false_eq_true, ite_false,
    Bool.not_false, Bool.not_true] at h ⊢ <;> omega

theorem ordHolds_of_cmp {n : Nat} {s st v : Bool} {x y : BitVec n}
    (h : (if s then (if st then x.slt y else x.sle y) else (if st then x.ult y else x.ule y)) = v) :
    (if v then OrdHolds s st x y else OrdHolds s (!st) y x) := by
  have key : (if s then (if st then x.slt y else x.sle y) else (if st then x.ult y else x.ule y)) = true ↔
      OrdHolds s st x y := by
    cases s <;> cases st <;> simp only [OrdHolds, ite_true, Bool.false_eq_true, ite_false,
      BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.ult_iff_lt, BitVec.ule_iff_le,
      BitVec.lt_def, BitVec.le_def]
  cases v
  · simp only [Bool.false_eq_true, ite_false]
    exact ordHolds_not fun ho => by rw [key.2 ho] at h; cases h
  · simp only [ite_true]; exact key.1 h

/-- A comparison term evaluated at fuel `K + 1`: its value, by its kind. -/
theorem cmp_den {c a b : ID} {cv : Value} (hc : D c = some cv) (hargs : cv.args.toList = [a, b])
    {k : CmpK} (hk : cTab.lookup cv.op = some k) (K : Nat) :
    den D tabs ρ (K + 1) c =
      (cmpEval k [den D tabs ρ K a, den D tabs ρ K b]).retype (tabs.ty cv.type) := by
  rw [den_succ_term hc (cTab_term hk), cTab_opVal hk, hargs]; rfl

/-- A path fact as a relation between its comparison's arguments. -/
theorem relRaw_sound (h : AsmHolds D tabs ρ A) {c : ID} {v : Bool} (hf : (c, v) ∈ A.facts)
    {a b : ID} {w : Width} {r : Rel} (hr : relRaw D tabs (c, v) = some (a, b, w, r)) :
    ∃ N, ∀ K, N ≤ K → ∃ xa xb, den D tabs ρ K a = .int w xa ∧ den D tabs ρ K b = .int w xb ∧
      RelHolds r xa xb := by
  obtain ⟨N, hN⟩ := h.facts c v hf
  refine ⟨N, fun K hK => ?_⟩
  have hcK := hN (K + 1) (by omega)
  unfold relRaw at hr
  dsimp only at hr
  cases hc : D c with
  | none => rw [hc] at hr; cases hr
  | some cv =>
  rw [hc] at hr
  simp only at hr
  split at hr
  · -- order
    rename_i a' b' w' s st hl hk
    rw [cmp_den hc hl hk K] at hcK
    simp only [cmpEval] at hcK
    have hne : ∀ z : Val, z.retype (tabs.ty cv.type) = .bool v → z ≠ .poison := fun z e hz => by
      rw [hz, retype_poison'] at e; cases e
    have key : ∀ (f : BitVec w'.bits → BitVec w'.bits → Bool),
        (Sem.int2 w' (fun x y => .bool (f x y)) [den D tabs ρ K a', den D tabs ρ K b']).retype
          (tabs.ty cv.type) = .bool v →
        ∃ xa xb, den D tabs ρ K a' = .int w' xa ∧ den D tabs ρ K b' = .int w' xb ∧ f xa xb = v := by
      intro f e
      obtain ⟨u1, u2, xa, xb, h1, h2, h3, h4⟩ := int2_eq rfl (hne _ e)
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [← h4] at e
      exact ⟨xa, xb, h2, h3, retype_bool_eq e⟩
    have hgo : ∃ xa xb, den D tabs ρ K a' = .int w' xa ∧ den D tabs ρ K b' = .int w' xb ∧
        (if s then (if st then xa.slt xb else xa.sle xb) else (if st then xa.ult xb else xa.ule xb)) = v := by
      cases s <;> cases st <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hcK ⊢ <;>
        exact key _ hcK
    obtain ⟨xa, xb, h1, h2, h3⟩ := hgo
    have ho := ordHolds_of_cmp h3
    cases v
    · simp only [ite_false, Bool.false_eq_true] at hr ho; cases hr
      exact ⟨xb, xa, h2, h1, ho⟩
    · simp only [ite_true] at hr ho; cases hr
      exact ⟨xa, xb, h1, h2, ho⟩
  · -- equality
    rename_i a' b' w' isEq hl hk
    rw [cmp_den hc hl hk K] at hcK
    cases hr
    have hne : ∀ z : Val, z.retype (tabs.ty cv.type) = .bool v → z ≠ .poison := fun z e hz => by
      rw [hz, retype_poison'] at e; cases e
    cases isEq <;> simp only [cmpEval, Cmp.eq, Cmp.neq] at hcK
    all_goals
      obtain ⟨u1, u2, xa, xb, h1, h2, h3, h4⟩ := int2_eq rfl (hne _ hcK)
      simp only [List.cons.injEq, and_true] at h1
      obtain ⟨rfl, rfl⟩ := h1
      rw [← h4] at hcK
      have e := retype_bool_eq hcK
      refine ⟨xa, xb, h2, h3, ?_⟩
      cases v <;> simp_all [RelHolds]
  · -- bounds check
    rename_i a' b' sl hl hk
    cases hwa : widthOf D tabs a' with
    | none => rw [hwa] at hr; cases hr
    | some w' =>
    rw [hwa] at hr
    simp only at hr
    rw [cmp_den hc hl hk K] at hcK
    simp only [cmpEval, Cmp.inBounds] at hcK
    split at hcK
    · rename_i wi i nv heq
      simp only [List.cons.injEq, and_true] at heq
      obtain ⟨ha, hb⟩ := heq
      cases hn : nv.asInt wi with
      | none => rw [hn, retype_poison'] at hcK; cases hcK
      | some n' =>
        rw [hn] at hcK
        dsimp only at hcK
        split at hcK
        · rw [retype_poison'] at hcK; cases hcK
        · have e := retype_bool_eq hcK
          -- the width of `a'` is `wi`
          unfold widthOf at hwa
          cases hu : D a' with
          | none => rw [hu] at hwa; cases hwa
          | some u =>
            rw [hu] at hwa
            have hsh := (den_int_shape h.typed hu ha).resolve_right
              (by rintro ⟨e', hsh⟩; simp [hsh, Ty.width?] at hwa)
            simp only [Option.bind_some, hsh, Ty.width?, Option.some.injEq] at hwa
            subst hwa
            have hnb := asInt_eq hn
            cases sl <;> cases v <;> simp only [ite_true, Bool.false_eq_true, ite_false,
              Bool.not_false, Bool.not_true] at hr e <;> cases hr
            · refine ⟨n', i, hb ▸ hnb, ha, ?_⟩
              simp only [RelHolds, OrdHolds, Bool.false_eq_true, ite_false, ite_true]
              have : ¬ i.toNat < n'.toNat := fun hl => by
                have := BitVec.ult_iff_lt.2 (BitVec.lt_def.2 hl); rw [this] at e; cases e
              omega
            · refine ⟨i, n', ha, hb ▸ hnb, ?_⟩
              simp only [RelHolds, OrdHolds, Bool.false_eq_true, ite_false, ite_true, Bool.not_false]
              exact BitVec.lt_def.1 (BitVec.ult_iff_lt.1 e)
            · refine ⟨n', i, hb ▸ hnb, ha, ?_⟩
              simp only [RelHolds, OrdHolds, Bool.false_eq_true, ite_false, ite_true]
              have : ¬ i.toNat ≤ n'.toNat := fun hl => by
                have := BitVec.ule_iff_le.2 (BitVec.le_def.2 hl); rw [this] at e; cases e
              omega
            · refine ⟨i, n', ha, hb ▸ hnb, ?_⟩
              simp only [RelHolds, OrdHolds, Bool.false_eq_true, ite_false, Bool.not_true]
              exact BitVec.le_def.1 (BitVec.ule_iff_le.1 e)
    · rw [retype_poison'] at hcK; cases hcK
  · cases hr

/-- **A path fact as a relation** between its sides' `canon`ical forms. -/
theorem relOf_sound (h : AsmHolds D tabs ρ A) {c : ID} {v : Bool} (hf : (c, v) ∈ A.facts)
    {a b : ID} {w : Width} {r : Rel} (hr : relOf D tabs (c, v) = some (a, b, w, r)) :
    ∃ N, ∀ K, N ≤ K → ∃ xa xb, den D tabs ρ K a = .int w xa ∧ den D tabs ρ K b = .int w xb ∧
      RelHolds r xa xb := by
  unfold relOf at hr
  cases hraw : relRaw D tabs (c, v) with
  | none => rw [hraw] at hr; cases hr
  | some q =>
    obtain ⟨a', b', w', r'⟩ := q
    rw [hraw] at hr
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hr
    obtain ⟨N, hN⟩ := relRaw_sound h hf hraw
    refine ⟨N, fun K hK => ?_⟩
    obtain ⟨xa, xb, ha, hb, hab⟩ := hN K hK
    exact ⟨xa, xb, canon_den h.typed ha, canon_den h.typed hb, hab⟩

theorem val_int_eq {w : Width} {x y : BitVec w.bits} (h : Val.int w x = Val.int w y) : x = y := by
  cases h; rfl

/-- A bounds check's length is nonnegative when the check holds or fails. -/
theorem bounds_len (h : AsmHolds D tabs ρ A) {c : ID} {v : Bool} (hf : (c, v) ∈ A.facts)
    {cv : Value} (hc : D c = some cv) {sl : Bool} (hk : cTab.lookup cv.op = some (.bounds sl))
    {x0 : ID} (hx1 : cv.args[1]? = some x0) {n : Nat} {w : Width} {y : BitVec w.bits}
    (hx : den D tabs ρ n (canon D tabs x0) = .int w y) : 0 ≤ y.toInt := by
  obtain ⟨N, hN⟩ := h.facts c v hf
  have hcK := hN (max N n + 1) (by omega)
  have hxK := den_stable_int hx (Nat.le_max_right N n)
  rw [den_succ_term hc (cTab_term hk), cTab_opVal hk] at hcK
  simp only [cmpEval, Cmp.inBounds] at hcK
  split at hcK
  · rename_i wi i nv heq
    have h1 : (cv.args.toList.map (den D tabs ρ (max N n)))[1]? = some nv := by rw [heq]; rfl
    rw [List.getElem?_map, Array.getElem?_toList, hx1] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    subst h1
    cases hn : (den D tabs ρ (max N n) x0).asInt wi with
    | none => rw [hn, retype_poison'] at hcK; cases hcK
    | some n' =>
      rw [hn] at hcK
      dsimp only at hcK
      split at hcK
      · rw [retype_poison'] at hcK; cases hcK
      · rename_i hmsb
        have e := canon_den h.typed (asInt_eq hn)
        rw [hxK] at e
        obtain ⟨rfl, e'⟩ := val_int_inj e
        cases e'
        have := BitVec.msb_eq_toInt (x := y)
        rw [this] at hmsb
        simp only [decide_eq_true_eq] at hmsb
        omega
  · rw [retype_poison'] at hcK; cases hcK

/-- **The bounds of one path fact.** -/
theorem factRng_mem (h : AsmHolds D tabs ρ A) {R : Width → ID → Rng}
    (hR : ∀ w x n (y : BitVec w.bits), den D tabs ρ n x = .int w y → (R w x).Mem y)
    {fact : ID × Bool} (hf : fact ∈ A.facts) {w : Width} {x : ID} {n : Nat} {y : BitVec w.bits}
    (hx : den D tabs ρ n x = .int w y) : (factRng D tabs R w x fact).Mem y := by
  have hn := Width.one_le w
  obtain ⟨c, v⟩ := fact
  unfold factRng
  dsimp only
  cases hr : relOf D tabs (c, v) with
  | none => exact Rng.mem_top hn y
  | some q =>
    obtain ⟨a, b, w', r⟩ := q
    dsimp only
    split
    · exact Rng.mem_top hn y
    · rename_i hw
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hw
      subst hw
      refine Rng.mem_meet ?_ ?_
      · obtain ⟨N, hN⟩ := relOf_sound h hf hr
        obtain ⟨xa, xb, ha, hb, hrel⟩ := hN (max N n) (Nat.le_max_left N n)
        have hxK := den_stable_int hx (Nat.le_max_right N n)
        cases r with
        | lt s st =>
          dsimp only
          split
          · rename_i e; simp only [beq_iff_eq] at e; subst e
            rw [hxK] at ha; cases val_int_eq ha
            exact mem_boundBy_lt hn (hR _ _ _ _ hb) hrel
          · split
            · rename_i _ e; simp only [beq_iff_eq] at e; subst e
              rw [hxK] at hb; cases val_int_eq hb
              exact mem_boundBy_gt hn (hR _ _ _ _ ha) hrel
            · exact Rng.mem_top hn y
        | eq bb =>
          cases bb with
          | false => exact Rng.mem_top hn y
          | true =>
            simp only [RelHolds] at hrel
            subst hrel
            dsimp only
            split
            · rename_i e; simp only [beq_iff_eq] at e; subst e
              rw [hxK] at ha; cases val_int_eq ha
              exact hR _ _ _ _ hb
            · split
              · rename_i _ e; simp only [beq_iff_eq] at e; subst e
                rw [hxK] at hb; cases val_int_eq hb
                exact hR _ _ _ _ ha
              · exact Rng.mem_top hn y
      · cases hc : D c with
        | none => exact Rng.mem_top hn y
        | some cv =>
          dsimp only
          split
          · rename_i sl hk
            split
            · rename_i e; simp only [beq_iff_eq] at e
              obtain ⟨x0, hx0, rfl⟩ := Option.map_eq_some_iff.1 e
              exact Rng.mem_nonneg hn (bounds_len h hf hc hk hx0 hx)
            · exact Rng.mem_top hn y
          · exact Rng.mem_top hn y

/-- **An exclusion by one path fact.** -/
theorem factExcl_mem (h : AsmHolds D tabs ρ A) {R : Width → ID → Rng}
    (hR : ∀ w x n (y : BitVec w.bits), den D tabs ρ n x = .int w y → (R w x).Mem y)
    {fact : ID × Bool} (hf : fact ∈ A.facts) {w : Width} {x : ID} {n : Nat} {y : BitVec w.bits}
    (hx : den D tabs ρ n x = .int w y) {r : Rng} (hr0 : r.Mem y) :
    (factExcl D tabs R w x r fact).Mem y := by
  obtain ⟨c, v⟩ := fact
  unfold factExcl
  split
  · rename_i a b w' hr
    split
    · exact hr0
    · rename_i hw
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hw
      subst hw
      obtain ⟨N, hN⟩ := relOf_sound h hf hr
      obtain ⟨xa, xb, ha, hb, hrel⟩ := hN (max N n) (Nat.le_max_left N n)
      have hxK := den_stable_int hx (Nat.le_max_right N n)
      simp only [RelHolds] at hrel
      split
      · rename_i e; simp only [beq_iff_eq] at e; subst e
        rw [hxK] at ha; cases val_int_eq ha
        exact Rng.mem_excl hr0 (hR _ _ _ _ hb) hrel
      · split
        · rename_i _ e; simp only [beq_iff_eq] at e; subst e
          rw [hxK] at hb; cases val_int_eq hb
          exact Rng.mem_excl hr0 (hR _ _ _ _ ha) (Ne.symm hrel)
        · exact hr0
  · exact hr0

theorem foldl_mem {α : Type} {n : Nat} {y : BitVec n} {F : Rng → α → Rng} :
    ∀ {l : List α} {r : Rng}, (∀ r e, e ∈ l → r.Mem y → (F r e).Mem y) → r.Mem y →
      (l.foldl F r).Mem y
  | [], _, _, h => h
  | e :: l, r, hF, h => by
    rw [List.foldl_cons]
    exact foldl_mem (fun r e' he' => hF r e' (List.mem_cons_of_mem _ he')) (hF r e List.mem_cons_self h)

/-- **The range analysis is sound.** -/
theorem rng_sound (h : AsmHolds D tabs ρ A) :
    ∀ k w x n (y : BitVec w.bits), den D tabs ρ n x = .int w y → (rng D tabs A k w x).Mem y
  | 0, w, x, n, y, _ => Rng.mem_top (Width.one_le w) y
  | k + 1, w, x, n, y, hx => by
    have hn := Width.one_le w
    have IH := rng_sound h k
    simp only [rng]
    cases hp : projOf D tabs x with
    | some y' =>
      dsimp only
      have := canon_den h.typed hx
      simp only [canon, hp, Option.getD_some] at this
      exact IH w y' n y this
    | none =>
    dsimp only
    refine Rng.mem_norm hn (foldl_mem (fun r fact hf hr => factExcl_mem h IH hf hx hr)
      (Rng.mem_norm hn (foldl_mem (fun r fact hf hr => Rng.mem_meet hr (factRng_mem h IH hf hx))
        (foldl_mem (fun r e he hr => ?_) ?_))))
    · obtain ⟨z, w', ry⟩ := e
      dsimp only
      split
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        exact Rng.mem_meet hr (h.inv _ _ _ he _ _ hx)
      · exact hr
    · cases n with
      | zero => simp [den] at hx
      | succ m =>
      cases hd : D x with
      | none => exact Rng.mem_top hn y
      | some v =>
        dsimp only
        split
        · rename_i hc
          simp only [Bool.and_eq_true] at hc
          obtain ⟨ht, hi⟩ := hc
          split
          · rename_i c hl
            rw [den_succ_term hd ht, rTab_opVal hl] at hx
            have hty := width_some (by simpa [intAt] using hi)
            rw [hty] at hx
            simp only [Ty.width?] at hx
            exact rOpRng_mem (fun w' x' y' hy => IH w' x' m y' hy) hx
          · exact Rng.mem_top hn y
        · exact Rng.mem_top hn y

end

end GoFV.Proof.ProveCheck
