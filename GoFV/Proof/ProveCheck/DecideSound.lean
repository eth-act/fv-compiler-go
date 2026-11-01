import GoFV.Proof.ProveCheck.Lin

/-!
# Deciding comparisons is sound (issue #24)

`decides_sound`: under assumptions that hold for `ρ` (`AsmHolds`), if `decides` says the term
`c` is `.bool v`, every boolean value of `c` is `v` — from a path fact on `c`, `ConstBool`,
`Not`, the ranges of a comparison's sides (`rangeDecides_sound`) or a path fact relating them
(`relImplies_sound`); a bounds check with its length assumed nonnegative (it is `poison`
otherwise).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

/-- The value of the comparison `x ⋈ y`. -/
def relVal {n : Nat} : Rel → BitVec n → BitVec n → Bool
  | .lt true true, x, y => x.slt y
  | .lt true false, x, y => x.sle y
  | .lt false true, x, y => x.ult y
  | .lt false false, x, y => x.ule y
  | .eq true, x, y => x == y
  | .eq false, x, y => x != y

theorem relVal_lt {n : Nat} {s st : Bool} {x y : BitVec n} :
    relVal (.lt s st) x y = true ↔ OrdHolds s st x y := by
  cases s <;> cases st <;> simp only [relVal, OrdHolds, ite_true, Bool.false_eq_true, ite_false,
    BitVec.slt_iff_toInt_lt, BitVec.sle_iff_toInt_le, BitVec.ult_iff_lt, BitVec.ule_iff_le,
    BitVec.lt_def, BitVec.le_def]

theorem relVal_lt_neg {n : Nat} {s st : Bool} {x y : BitVec n}
    (h : relVal (.lt s (!st)) y x = true) : relVal (.lt s st) x y = false := by
  rw [relVal_lt] at h
  cases e : relVal (.lt s st) x y
  · rfl
  · rw [relVal_lt] at e
    cases s <;> cases st <;> simp only [OrdHolds, ite_true, Bool.false_eq_true, ite_false,
      Bool.not_false, Bool.not_true] at h e <;> omega

theorem toNat_toInt_nonneg {n : Nat} {x : BitVec n} (h : 0 ≤ x.toInt) : x.toInt = x.toNat :=
  BitVec.toInt_eq_toNat_of_msb (msb_false_of h)

theorem ord_ne {n : Nat} {s : Bool} {X Y : BitVec n} (h : OrdHolds s true X Y) : X ≠ Y := by
  rintro rfl; cases s <;> simp [OrdHolds] at h

theorem relVal_ne {n : Nat} {X Y : BitVec n} (h : X ≠ Y) : relVal (.eq false) X Y = true := by
  simpa [relVal] using h

theorem relVal_le_self {n : Nat} {s : Bool} (X : BitVec n) : relVal (.lt s false) X X = true := by
  rw [relVal_lt]; cases s <;> simp [OrdHolds]

/-- Same sides, order fact to order query. -/
theorem ord_ord {n : Nat} {s st s' st' xNN yNN : Bool} {X Y : BitVec n}
    (h : ((st || !st') && (s == s' || (s && !s' && xNN && yNN) || (!s && s' && xNN && yNN))) = true)
    (hr : OrdHolds s st X Y) (hx : xNN = true → 0 ≤ X.toInt) (hy : yNN = true → 0 ≤ Y.toInt) :
    OrdHolds s' st' X Y := by
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨hst, hsg⟩ := h
  have hX := X.isLt
  have hY := Y.isLt
  rcases hsg with (rfl | ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩) | ⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩
  · cases s <;> cases st <;> cases st' <;> simp [OrdHolds] at hst hr ⊢ <;> omega
  · have e1 := toNat_toInt_nonneg (hx h1); have e2 := toNat_toInt_nonneg (hy h2)
    cases st <;> cases st' <;> simp [OrdHolds] at hst hr ⊢ <;> omega
  · have e1 := toNat_toInt_nonneg (hx h1); have e2 := toNat_toInt_nonneg (hy h2)
    cases st <;> cases st' <;> simp [OrdHolds] at hst hr ⊢ <;> omega

/-- **A known relation implies the comparison.** -/
theorem relImplies_sound {n : Nat} {kx ky x y : ID} {kr t : Rel} {xNN yNN : Bool}
    (h : relImplies (kx, ky, kr) x y t xNN yNN = true) {X Y : BitVec n}
    (hk1 : kx = x → ky = y → RelHolds kr X Y) (hk2 : kx = y → ky = x → RelHolds kr Y X)
    (hx : xNN = true → 0 ≤ X.toInt) (hy : yNN = true → 0 ≤ Y.toInt) : relVal t X Y = true := by
  unfold relImplies at h
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have hr := hk1 hc.1 hc.2
    cases kr with
    | lt s st =>
      cases t with
      | lt s' st' => exact relVal_lt.2 (ord_ord h hr hx hy)
      | eq b' =>
        simp only [RelHolds] at hr
        cases st <;> cases b' <;> simp at h
        exact relVal_ne (ord_ne hr)
    | eq b =>
      cases b with
      | false =>
        cases t with
        | lt _ _ => simp at h
        | eq b' => cases b' <;> simp at h; exact relVal_ne hr
      | true =>
        simp only [RelHolds] at hr; subst hr
        cases t with
        | lt s' st' => cases st' <;> simp at h; exact relVal_le_self X
        | eq b' => cases b' <;> simp at h; simp [relVal]
  · split at h
    · rename_i _ hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have hr := hk2 hc.1 hc.2
      cases kr with
      | lt s st =>
        cases t with
        | lt _ _ => simp at h
        | eq b' =>
          simp only [RelHolds] at hr
          cases st <;> cases b' <;> simp at h
          exact relVal_ne (Ne.symm (ord_ne hr))
      | eq b =>
        cases b with
        | false =>
          cases t with
          | lt _ _ => simp at h
          | eq b' => cases b' <;> simp at h; exact relVal_ne (Ne.symm hr)
        | true =>
          simp only [RelHolds] at hr; subst hr
          cases t with
          | lt s' st' => cases st' <;> simp at h; exact relVal_le_self Y
          | eq b' => cases b' <;> simp at h; simp [relVal]
    · cases h

/-- **Ranges decide the comparison.** -/
theorem rangeDecides_sound {n : Nat} {rx ry : Rng} {t : Rel} {v : Bool} {X Y : BitVec n}
    (hx : rx.Mem X) (hy : ry.Mem Y) (h : rangeDecides rx ry t v = true) : relVal t X Y = v := by
  have he1 := Rng.not_empty hx
  have he2 := Rng.not_empty hy
  obtain ⟨a1, a2, a3, a4⟩ := hx
  obtain ⟨b1, b2, b3, b4⟩ := hy
  have hu : X.toNat = Y.toNat → X = Y := BitVec.eq_of_toNat_eq
  unfold rangeDecides at h
  rw [he1, he2] at h
  simp only [Bool.false_or] at h
  cases t with
  | lt s st =>
    cases v with
    | true =>
      refine relVal_lt.2 ?_
      cases s <;> cases st <;> simp [OrdHolds] at h ⊢ <;> omega
    | false =>
      cases e : relVal (.lt s st) X Y
      · rfl
      · have := relVal_lt.1 e
        cases s <;> cases st <;> simp [OrdHolds] at h this <;> omega
  | eq b =>
    have hs : X.toInt = Y.toInt → X = Y := BitVec.toInt_inj.1
    by_cases hbv : b = v
    · subst hbv
      simp only [beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq] at h
      have : X = Y := hu (by omega)
      subst this
      cases b <;> simp [relVal]
    · have hbv' : (b == v) = false := by simpa using hbv
      simp only [hbv', Bool.false_eq_true, ite_false, Bool.or_eq_true, decide_eq_true_eq] at h
      have : X ≠ Y := fun e => by subst e; omega
      cases b <;> cases v <;> simp_all [relVal]

theorem retype_bool_res {t : Ty} {z : Val} {bb : Bool} (h : z.retype t = .bool bb) :
    z ≠ .poison := fun e => by rw [e, retype_poison'] at h; cases h

/-- An order or equality comparison with a boolean value: its sides and `relVal`. -/
theorem cmp_val {w : Width} {r : Rel} {argv : List Val} {t : Ty} {bb : Bool}
    (hk : (cmpEval (match r with | .lt s st => .lt w s st | .eq b => .eq w b) argv).retype t = .bool bb) :
    ∃ X Y : BitVec w.bits, argv = [.int w X, .int w Y] ∧ relVal r X Y = bb := by
  have key : ∀ (f : BitVec w.bits → BitVec w.bits → Bool),
      (Sem.int2 w (fun x y => .bool (f x y)) argv).retype t = .bool bb →
      ∃ X Y : BitVec w.bits, argv = [.int w X, .int w Y] ∧ f X Y = bb := fun f e => by
    obtain ⟨u, v, X, Y, h1, rfl, rfl, h4⟩ := int2_eq rfl (retype_bool_res e)
    rw [← h4] at e
    exact ⟨X, Y, h1, retype_bool_eq e⟩
  cases r with
  | lt s st => cases s <;> cases st <;> exact key _ hk
  | eq b => cases b <;> exact key _ hk

theorem relVal_refl {n : Nat} (t : Rel) (X : BitVec n) : relVal t X X = t.refl := by
  cases t with
  | lt s st =>
    cases s <;> cases st <;> simp [relVal, Rel.refl, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle]
  | eq b => cases b <;> simp [relVal, Rel.refl]

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {A : Asm} {k : Nat}

theorem pairDecides_sound (h : AsmHolds D tabs ρ A) {x0 y0 : ID} {w : Width} {t : Rel} {v : Bool}
    (hp : pairDecides D tabs A k x0 y0 w t v = true) {K : Nat} {X Y : BitVec w.bits}
    (hx0 : den D tabs ρ K x0 = .int w X) (hy0 : den D tabs ρ K y0 = .int w Y) : relVal t X Y = v := by
  have hx := canon_den h.typed hx0
  have hy := canon_den h.typed hy0
  unfold pairDecides at hp
  dsimp only at hp
  generalize canon D tabs x0 = x at hp hx
  generalize canon D tabs y0 = y at hp hy
  rw [Bool.or_eq_true] at hp
  rcases hp with hp | hp
  · simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨rfl, hv⟩ := hp
    rw [hx] at hy; cases val_int_eq hy
    rw [← hv]; exact relVal_refl t X
  have hxNN : decide (0 ≤ (rng D tabs A k w x).slo) = true → 0 ≤ X.toInt := fun e => by
    obtain ⟨-, -, m3, -⟩ := rng_sound h k w x K X hx; simp at e; omega
  have hyNN : decide (0 ≤ (rng D tabs A k w y).slo) = true → 0 ≤ Y.toInt := fun e => by
    obtain ⟨-, -, m3, -⟩ := rng_sound h k w y K Y hy; simp at e; omega
  -- a relation among the facts, as values at enough fuel
  have hrel : ∀ q ∈ A.facts.filterMap (fun fact => match relOf D tabs fact with
      | some (a, b, w', r) => if w' == w then some (a, b, r) else none
      | none => none), ∀ (P : Prop), (∀ (X' Y' : BitVec w.bits),
        (q.1 = x → q.2.1 = y → RelHolds q.2.2 X Y) → (q.1 = y → q.2.1 = x → RelHolds q.2.2 Y X) → P) → P := by
    intro q hq P hP
    obtain ⟨fact, hf, hfq⟩ := List.mem_filterMap.1 hq
    cases hr : relOf D tabs fact with
    | none => rw [hr] at hfq; cases hfq
    | some z =>
      obtain ⟨a, b, w', r⟩ := z
      rw [hr] at hfq
      dsimp only at hfq
      split at hfq
      · rename_i hw
        simp only [beq_iff_eq] at hw; subst hw
        cases hfq
        obtain ⟨c, v'⟩ := fact
        obtain ⟨N, hN⟩ := relOf_sound h hf hr
        obtain ⟨xa, xb, ha, hb, hab⟩ := hN (max N K) (Nat.le_max_left _ _)
        have hxK := den_stable_int hx (Nat.le_max_right N K)
        have hyK := den_stable_int hy (Nat.le_max_right N K)
        refine hP X Y (fun e1 e2 => ?_) (fun e1 e2 => ?_)
        · dsimp only at e1 e2; subst e1; subst e2
          rw [hxK] at ha; rw [hyK] at hb; cases val_int_eq ha; cases val_int_eq hb; exact hab
        · dsimp only at e1 e2; subst e1; subst e2
          rw [hyK] at ha; rw [hxK] at hb; cases val_int_eq ha; cases val_int_eq hb; exact hab
      · cases hfq
  split at hp
  · obtain ⟨q, hq, hi⟩ := List.any_eq_true.1 hp
    obtain ⟨kx, ky, kr⟩ := q
    exact hrel _ hq _ fun _ _ h1 h2 => relImplies_sound hi h1 h2 hxNN hyNN
  · rename_i s st
    obtain ⟨q, hq, hi⟩ := List.any_eq_true.1 hp
    obtain ⟨kx, ky, kr⟩ := q
    exact hrel _ hq _ fun _ _ h1 h2 =>
      relVal_lt_neg (relImplies_sound hi h2 h1 hyNN hxNN)
  · rename_i b
    obtain ⟨q, hq, hi⟩ := List.any_eq_true.1 hp
    obtain ⟨kx, ky, kr⟩ := q
    exact hrel _ hq _ fun _ _ h1 h2 => by
      have := relImplies_sound hi h1 h2 hxNN hyNN
      cases b
      · simp only [relVal, Bool.not_false] at this ⊢; simp [bne, this]
      · simp only [relVal, Bool.not_true] at this ⊢; simpa [bne] using this

theorem ordHolds_readV {n : Nat} {s st : Bool} {X Y : BitVec n} :
    OrdHolds s st X Y ↔ (if st then readV s X < readV s Y else readV s X ≤ readV s Y) := by
  cases s <;> cases st <;> simp only [OrdHolds, readV, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem readV_inj {n : Nat} {s : Bool} {X Y : BitVec n} (h : readV s X = readV s Y) : X = Y := by
  cases s
  · exact BitVec.eq_of_toNat_eq (by simp only [readV, Bool.false_eq_true, ite_false] at h; omega)
  · exact BitVec.toInt_inj.1 (by simpa [readV] using h)

/-- Differences in the reading `s` decide the comparison. -/
theorem linIn_sound (h : AsmHolds D tabs ρ A) {s : Bool} {x y : ID} {w : Width} {t : Rel}
    {v : Bool} (ht : ∀ s' st, t = .lt s' st → s' = s) (hp : linIn D tabs A k s x y w t v = true)
    {K : Nat} {X Y : BitVec w.bits} (hx : den D tabs ρ K x = .int w X)
    (hy : den D tabs ρ K y = .int w Y) : relVal t X Y = v := by
  obtain ⟨N, hN⟩ := allEdges_sound (k := k) h s w
  have hx' := den_stable_int hx (Nat.le_max_right N K)
  have hy' := den_stable_int hy (Nat.le_max_right N K)
  have hes := hN (max N K) (Nat.le_max_left N K)
  obtain ⟨BX, hBX, ex⟩ := offOf_sound (k := k) (s := s) h hx'
  obtain ⟨BY, hBY, ey⟩ := offOf_sound (k := k) (s := s) h hy'
  unfold linIn at hp
  generalize A.facts.flatMap (factEdges D tabs A k s w) = es at hp hes
  generalize offOf D tabs A k s w x = ox at hp hBX ex
  generalize offOf D tabs A k s w y = oy at hp hBY ey
  obtain ⟨bx, cx⟩ := ox
  obtain ⟨by', cy⟩ := oy
  dsimp only at hp hBX ex hBY ey
  have d1 := fun c (hd : diffLe es bx by' c = true) => diffLe_sound hes hd hBX hBY
  have d2 := fun c (hd : diffLe es by' bx c = true) => diffLe_sound hes hd hBY hBX
  cases t with
  | lt s' st =>
    cases ht s' st rfl
    dsimp only at hp
    cases v with
    | true =>
      have := d1 _ hp
      refine relVal_lt.2 (ordHolds_readV.2 ?_)
      cases st <;> simp only [ite_true, Bool.false_eq_true, ite_false] at this ⊢ <;> omega
    | false =>
      simp only [Bool.false_eq_true, ite_false] at hp
      have := d2 _ hp
      cases e : relVal (.lt s st) X Y
      · rfl
      · have := ordHolds_readV.1 (relVal_lt.1 e)
        cases st <;> simp only [ite_true, Bool.false_eq_true, ite_false] at * <;> omega
  | eq b =>
    dsimp only at hp
    split at hp
    · rename_i hbv
      simp only [beq_iff_eq] at hbv
      subst hbv
      simp only [Bool.and_eq_true] at hp
      have h1 := d1 _ hp.1
      have h2 := d2 _ hp.2
      have : X = Y := readV_inj (s := s) (by omega)
      subst this
      cases b <;> simp [relVal]
    · rename_i hbv
      simp only [beq_iff_eq] at hbv
      have hne : X ≠ Y := by
        rintro rfl
        rcases Bool.or_eq_true_iff.1 hp with hd | hd
        · have := d1 _ hd; omega
        · have := d2 _ hd; omega
      cases b <;> cases v <;> simp_all [relVal]

theorem linDecides_sound (h : AsmHolds D tabs ρ A) {x y : ID} {w : Width} {t : Rel} {v : Bool}
    (hp : linDecides D tabs A k x y w t v = true) {K : Nat} {X Y : BitVec w.bits}
    (hx : den D tabs ρ K x = .int w X) (hy : den D tabs ρ K y = .int w Y) : relVal t X Y = v := by
  unfold linDecides at hp
  cases t with
  | lt s st => exact linIn_sound h (fun _ _ e => by cases e; rfl) hp hx hy
  | eq b =>
    rcases Bool.or_eq_true_iff.1 hp with hp | hp
    · exact linIn_sound h (fun _ _ e => by cases e) hp hx hy
    · exact linIn_sound h (fun _ _ e => by cases e) hp hx hy

theorem relDecides_sound (h : AsmHolds D tabs ρ A) {x y : ID} {w : Width} {t : Rel} {v : Bool}
    (hp : relDecides D tabs A k x y w t v = true) {K : Nat} {X Y : BitVec w.bits}
    (hx : den D tabs ρ K x = .int w X) (hy : den D tabs ρ K y = .int w Y) : relVal t X Y = v := by
  unfold relDecides at hp
  rcases Bool.or_eq_true_iff.1 hp with hr | hr
  · rcases Bool.or_eq_true_iff.1 hr with hr | hr
    · exact rangeDecides_sound (rng_sound h k w x K X hx) (rng_sound h k w y K Y hy) hr
    · exact pairDecides_sound h hr hx hy
  · exact linDecides_sound h hr hx hy

/-- **Deciding a term is sound.** -/
theorem decides_sound (h : AsmHolds D tabs ρ A) :
    ∀ fuel c v, decides D tabs A k fuel c v = true → ∀ n bb, den D tabs ρ n c = .bool bb → bb = v
  | 0, _, _, hd, _, _, _ => by simp [decides] at hd
  | fuel + 1, c, v, hd, n, bb, hc => by
    unfold decides at hd
    rcases Bool.or_eq_true_iff.1 hd with hf | hd
    · obtain ⟨N, hN⟩ := h.facts c v (List.elem_iff.1 hf)
      have := den_stable_bool hc (Nat.le_max_right N n)
      rw [hN _ (Nat.le_max_left N n)] at this
      cases this; rfl
    · cases n with
      | zero => simp [den] at hc
      | succ m =>
      cases hdc : D c with
      | none => rw [hdc] at hd; cases hd
      | some cv =>
        rw [hdc] at hd
        simp only [Bool.and_eq_true] at hd
        obtain ⟨ht, hd⟩ := hd
        rw [den_succ_term hdc ht] at hc
        split at hd
        · rename_i hl
          simp only [Bool.and_eq_true, beq_iff_eq] at hd
          obtain ⟨hop, hv⟩ := hd
          rw [hop, hl] at hc
          change (Val.bool (cv.auxInt != 0)).retype _ = _ at hc
          rw [← retype_bool_eq hc]; simpa using hv
        · rename_i a hl
          simp only [Bool.and_eq_true, beq_iff_eq] at hd
          obtain ⟨hop, hv⟩ := hd
          rw [hop, hl] at hc
          change (bool1 (!·) [den D tabs ρ m a]).retype _ = _ at hc
          unfold bool1 at hc
          dsimp only at hc
          cases ha : (den D tabs ρ m a).asBool with
          | none => rw [ha, retype_poison'] at hc; cases hc
          | some b' =>
            rw [ha] at hc
            have e := retype_bool_eq hc
            have := decides_sound h fuel a (!v) hv m b' (asBool_eq ha)
            rw [← e, this]; simp
        · rename_i a b hl
          split at hd
          · rename_i ck hk
            rw [show cv.args.toList.map (den D tabs ρ m) = [den D tabs ρ m a, den D tabs ρ m b] by
              rw [hl]; rfl, cTab_opVal hk] at hc
            unfold cmpDecides at hd
            cases ck with
            | lt w s st =>
              obtain ⟨X, Y, hl', he⟩ := cmp_val (r := .lt s st) hc
              simp only [List.cons.injEq, and_true] at hl'
              rw [← he]; exact relDecides_sound h hd hl'.1 hl'.2
            | eq w isEq =>
              obtain ⟨X, Y, hl', he⟩ := cmp_val (r := .eq isEq) hc
              simp only [List.cons.injEq, and_true] at hl'
              rw [← he]; exact relDecides_sound h hd hl'.1 hl'.2
            | bounds sl =>
              cases hwa : widthOf D tabs a with
              | none => rw [hwa] at hd; cases hd
              | some w =>
                rw [hwa] at hd
                dsimp only at hd
                simp only [cmpEval, Cmp.inBounds] at hc
                split at hc
                · rename_i wi i nv heq
                  simp only [List.cons.injEq, and_true] at heq
                  obtain ⟨ha, hb⟩ := heq
                  cases hn : nv.asInt wi with
                  | none => rw [hn, retype_poison'] at hc; cases hc
                  | some n' =>
                    rw [hn] at hc
                    dsimp only at hc
                    split at hc
                    · rw [retype_poison'] at hc; cases hc
                    · rename_i hmsb
                      have e := retype_bool_eq hc
                      unfold widthOf at hwa
                      cases hu : D a with
                      | none => rw [hu] at hwa; cases hwa
                      | some u =>
                        rw [hu] at hwa
                        have hsh := den_int_shape h.typed hu ha
                        simp only [Option.bind_some, hsh, Ty.width?, Option.some.injEq] at hwa
                        subst hwa
                        have hbN : den D tabs ρ m b = .int wi n' := hb ▸ asInt_eq hn
                        have h' : AsmHolds D tabs ρ
                            { A with inv := (canon D tabs b, wi, Rng.nonneg wi.bits) :: A.inv } :=
                          ⟨h.facts, fun z w r hz n'' y hy => by
                            rcases List.mem_cons.1 hz with e' | hz
                            · simp only [Prod.mk.injEq] at e'
                              obtain ⟨rfl, rfl, rfl⟩ := e'
                              rw [← den_int_unique (canon_den h.typed hbN) hy]
                              have := BitVec.msb_eq_toInt (x := n')
                              simp only [Bool.not_eq_true] at hmsb
                              rw [this] at hmsb; simp at hmsb
                              exact Rng.mem_nonneg (Width.one_le _) hmsb
                            · exact h.inv z w r hz n'' y hy, h.typed⟩
                        rw [← e]
                        cases v with
                        | true =>
                          simp only [ite_true] at hd
                          have := relDecides_sound h' hd ha hbN
                          cases sl <;> simpa [relVal] using this
                        | false =>
                          simp only [Bool.false_eq_true, ite_false] at hd
                          have := relDecides_sound h' hd hbN ha
                          have := relVal_lt_neg (st := !sl) (by simpa using this)
                          cases sl <;> simpa [relVal] using this
                · rw [retype_poison'] at hc; cases hc
          · cases hd
        · cases hd

end

end GoFV.Proof.ProveCheck
