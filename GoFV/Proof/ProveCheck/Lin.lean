import GoFV.Proof.ProveCheck.Value

/-!
# Differences of values from chains of path facts (issue #24)

The edges `(u, v, c)` the validator reads off the path facts (`factEdges`) say
`V(u) - V(v) ≤ c` for the values' readings `V` (`readV`: signed `toInt` or unsigned `toNat`) at
enough fuel (`factEdges_sound`); a side `x` of a fact stands for `base + c` when it is an `Add`
or `Sub` with a constant that cannot wrap around (`offOf_sound`). Paths of edges add up
(`distFrom_sound`), so `diffLe es x y c` gives `V(x) - V(y) ≤ c` (`diffLe_sound`). A relation
`z - y ≤ c` (`AsmHolds.rels`) holds only between defined values, so it serves as the last edge
of a path (`diffLeR_sound`, `relEdges_sound`, `linLe_sound`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

/-- `x` in the reading `s`: signed `toInt` or unsigned `toNat`. -/
def readV (s : Bool) {n : Nat} (x : BitVec n) : Int := if s then x.toInt else x.toNat

theorem readV_bounds {n : Nat} (hn : 1 ≤ n) (s : Bool) (x : BitVec n) :
    readMin n s ≤ readV s x ∧ readV s x ≤ readMax n s := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  cases s <;> simp only [readMin, readMax, readV, ite_true, Bool.false_eq_true, ite_false, h3, h4] <;>
    split at h7 <;> omega

theorem Rng.mem_read {n : Nat} {r : Rng} {x : BitVec n} (h : r.Mem x) (s : Bool) :
    r.lo s ≤ readV s x ∧ readV s x ≤ r.hi s := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  cases s <;> simp only [Rng.lo, Rng.hi, readV, ite_true, Bool.false_eq_true, ite_false] <;> omega

theorem nat_mod_two {m N : Nat} (h : m < 2 * N) :
    (m % N = m ∧ m < N) ∨ (m % N = m - N ∧ N ≤ m) := by
  by_cases hm : m < N
  · exact .inl ⟨Nat.mod_eq_of_lt hm, hm⟩
  · right
    refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem readV_add {n : Nat} (hn : 1 ≤ n) (s : Bool) (a b : BitVec n)
    (h1 : readMin n s ≤ readV s a + b.toInt) (h2 : readV s a + b.toInt ≤ readMax n s) :
    readV s (a + b) = readV s a + b.toInt := by
  obtain ⟨H, e1, e2, e3, e4, e5, e6, e7⟩ := reading hn b
  have ha := a.isLt
  rw [e1] at ha
  cases s
  · simp only [readV, readMin, readMax, Bool.false_eq_true, ite_false, e3] at h1 h2 ⊢
    rw [BitVec.toNat_add, e1]
    rcases nat_mod_two (m := a.toNat + b.toNat) (N := 2 * H) (by omega) with ⟨e, he⟩ | ⟨e, he⟩ <;>
      rw [e] <;> split at e7 <;> omega
  · simp only [readV, readMin, readMax, ite_true, e4] at h1 h2 ⊢
    rw [BitVec.toInt_add]
    exact Int.bmod_eq_of_le_mul_two (by rw [e1]; push_cast; omega) (by rw [e1]; push_cast; omega)

theorem readV_sub {n : Nat} (hn : 1 ≤ n) (s : Bool) (a b : BitVec n)
    (h1 : readMin n s ≤ readV s a + -b.toInt) (h2 : readV s a + -b.toInt ≤ readMax n s) :
    readV s (a - b) = readV s a + -b.toInt := by
  obtain ⟨H, e1, e2, e3, e4, e5, e6, e7⟩ := reading hn b
  have ha := a.isLt
  rw [e1] at ha
  cases s
  · simp only [readV, readMin, readMax, Bool.false_eq_true, ite_false, e3] at h1 h2 ⊢
    rw [BitVec.toNat_sub, e1]
    rcases nat_mod_two (m := 2 * H - b.toNat + a.toNat) (N := 2 * H) (by omega) with ⟨e, he⟩ | ⟨e, he⟩ <;>
      rw [e] <;> split at e7 <;> omega
  · simp only [readV, readMin, readMax, ite_true, e4] at h1 h2 ⊢
    rw [BitVec.toInt_sub, ← Int.sub_eq_add_neg]
    rw [← Int.sub_eq_add_neg] at h1 h2
    exact Int.bmod_eq_of_le_mul_two (by rw [e1]; push_cast; omega) (by rw [e1]; push_cast; omega)

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {A : Asm} {k : Nat}

/-- A `w`-bit constant's value has the signed reading `constVal` says. -/
theorem constVal_sound {w : Width} {z : ID} {c : Int} (h : constVal D w z = some c) {K : Nat}
    {Z : BitVec w.bits} (hz : den D tabs ρ K z = .int w Z) : Z.toInt = c := by
  unfold constVal at h
  cases hd : D z with
  | none => rw [hd] at h; cases h
  | some zv =>
    rw [hd] at h
    simp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨ht, hl⟩ := hc
      cases K with
      | zero => simp [den] at hz
      | succ K =>
        rw [den_succ_term hd ht, rTab_opVal hl] at hz
        have hty := retype_int_shape hz
        rw [hty] at hz
        simp only [rOpEval, Conv.const] at hz
        rw [← retype_int_val hz]
    · cases h

/-- `addConst`: `x`'s value is its base's plus `c`, whenever that does not wrap around. -/
theorem addConst_sound {w : Width} {x a : ID} {c : Int} (h : addConst D w x = some (a, c))
    {K : Nat} {X : BitVec w.bits} (hx : den D tabs ρ (K + 1) x = .int w X) :
    ∃ A' : BitVec w.bits, den D tabs ρ K a = .int w A' ∧ ∀ s,
      readMin w.bits s ≤ readV s A' + c → readV s A' + c ≤ readMax w.bits s →
      readV s X = readV s A' + c := by
  have hn := Width.one_le w
  unfold addConst at h
  cases hd : D x with
  | none => rw [hd] at h; cases h
  | some v =>
  rw [hd] at h
  simp only at h
  split at h
  · rename_i ht
    rw [den_succ_term hd ht] at hx
    split at h
    · rename_i w' a0 b0 hl hargs
      split at h
      · rename_i hw
        simp only [beq_iff_eq] at hw; subst w'
        rw [rTab_opVal hl] at hx
        have hty := retype_int_shape hx
        rw [hty] at hx
        simp only [Ty.width?, rOpEval] at hx
        obtain ⟨u, u', A0, B0, hv, rfl, rfl, hf⟩ := int2_res hx
        have hy := retype_int_val hf
        rw [hargs] at hv
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
        obtain ⟨ha0, hb0⟩ := hv
        cases hcb : constVal D w b0 with
        | some cb =>
          rw [hcb] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨A0, ha0, fun s l1 l2 => ?_⟩
          rw [← constVal_sound hcb hb0] at l1 l2 ⊢
          rw [← hy]; exact readV_add hn s A0 B0 l1 l2
        | none =>
          rw [hcb] at h
          cases hca : constVal D w a0 with
          | none => rw [hca] at h; cases h
          | some ca =>
            rw [hca] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨B0, hb0, fun s l1 l2 => ?_⟩
            rw [← constVal_sound hca ha0] at l1 l2 ⊢
            rw [← hy, BitVec.add_comm]; exact readV_add hn s B0 A0 l1 l2
      · cases h
    · rename_i w' a0 b0 hl hargs
      split at h
      · rename_i hw
        simp only [beq_iff_eq] at hw; subst w'
        cases hc : constVal D w b0 with
        | none => rw [hc] at h; cases h
        | some c' =>
        rw [hc] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [rTab_opVal hl] at hx
        have hty := retype_int_shape hx
        rw [hty] at hx
        simp only [Ty.width?, rOpEval] at hx
        obtain ⟨u, u', A0, B0, hv, rfl, rfl, hf⟩ := int2_res hx
        have hy := retype_int_val hf
        rw [hargs] at hv
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hv
        obtain ⟨ha0, hb0⟩ := hv
        refine ⟨A0, ha0, fun s l1 l2 => ?_⟩
        rw [← constVal_sound hc hb0] at l1 l2 ⊢
        rw [← hy]; exact readV_sub hn s A0 B0 l1 l2
      · cases h
    · cases h
  · cases h

/-- **`offOf`**: `x`'s value in the reading `s` is its base's plus the offset. -/
theorem offOf_sound (h : AsmHolds D tabs ρ A) {s : Bool} {w : Width} {x0 : ID} {K : Nat}
    {X : BitVec w.bits} (hx : den D tabs ρ K x0 = .int w X) :
    ∃ B : BitVec w.bits, den D tabs ρ K (offOf D tabs A k s w x0).1 = .int w B ∧
      readV s X = readV s B + (offOf D tabs A k s w x0).2 := by
  have hx' := canon_den h.typed hx
  unfold offOf
  dsimp only
  generalize canon D tabs x0 = x at hx' ⊢
  cases ha : addConst D w x with
  | none => exact ⟨X, hx', by simp⟩
  | some q =>
    obtain ⟨b, c⟩ := q
    dsimp only
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      cases K with
      | zero => simp [den] at hx'
      | succ K =>
        obtain ⟨A', hA', hread⟩ := addConst_sound ha hx'
        obtain ⟨m1, m2⟩ := Rng.mem_read (rng_sound h k w b K A' hA') s
        exact ⟨A', den_stable_int (canon_den h.typed hA') (by omega),
          hread s (by omega) (by omega)⟩
    · exact ⟨X, hx', by simp⟩

/-- An edge `V(u) - V(v) ≤ c` holds at fuel `K`. -/
def EdgeHolds (D : ID → Option Value) (tabs : Tables) (ρ : ID → Val) (s : Bool) (w : Width)
    (K : Nat) (e : ID × ID × Int) : Prop :=
  ∃ U V : BitVec w.bits, den D tabs ρ K e.1 = .int w U ∧ den D tabs ρ K e.2.1 = .int w V ∧
    readV s U - readV s V ≤ e.2.2

theorem toNat_eq_toInt {n : Nat} {x : BitVec n} (h : 0 ≤ x.toInt) : (x.toNat : Int) = x.toInt :=
  (BitVec.toInt_eq_toNat_of_msb (msb_false_of h)).symm

/-- **The edges of a path fact hold** at enough fuel. -/
theorem factEdges_sound (h : AsmHolds D tabs ρ A) {s : Bool} {w : Width} {fact : ID × Bool}
    (hf : fact ∈ A.facts) :
    ∃ N, ∀ K, N ≤ K → ∀ e ∈ factEdges D tabs A k s w fact, EdgeHolds D tabs ρ s w K e := by
  obtain ⟨c0, v0⟩ := fact
  unfold factEdges
  cases hr : relOf D tabs (c0, v0) with
  | none => exact ⟨0, fun _ _ e he => by simp at he⟩
  | some q =>
    obtain ⟨a, b, w', r⟩ := q
    dsimp only
    split
    · exact ⟨0, fun _ _ e he => by simp at he⟩
    · rename_i hw
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hw
      subst w'
      obtain ⟨N, hN⟩ := relOf_sound h hf hr
      refine ⟨N, fun K hK e he => ?_⟩
      obtain ⟨xa, xb, ha, hb, hab⟩ := hN K hK
      obtain ⟨BA, hBA, ea⟩ := offOf_sound (k := k) (s := s) h ha
      obtain ⟨BB, hBB, eb⟩ := offOf_sound (k := k) (s := s) h hb
      generalize offOf D tabs A k s w a = oa at hBA ea he
      generalize offOf D tabs A k s w b = ob at hBB eb he
      obtain ⟨ba, ca⟩ := oa
      obtain ⟨bb, cb⟩ := ob
      dsimp only at hBA ea hBB eb he
      cases r with
      | lt s' st =>
        dsimp only at he
        split at he
        · rename_i hc
          simp only [List.mem_singleton] at he
          subst he
          refine ⟨BA, BB, hBA, hBB, ?_⟩
          dsimp only
          have hrel : (if st then readV s xa < readV s xb else readV s xa ≤ readV s xb) := by
            simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hc
            simp only [RelHolds, OrdHolds] at hab
            rcases hc with rfl | ⟨n1, n2⟩
            · cases s' <;> cases st <;> simp only [readV, ite_true, Bool.false_eq_true, ite_false] at hab ⊢ <;>
                omega
            · obtain ⟨-, -, m1, -⟩ := rng_sound h k w a K xa ha
              obtain ⟨-, -, m2, -⟩ := rng_sound h k w b K xb hb
              have e1 := toNat_eq_toInt (x := xa) (by omega)
              have e2 := toNat_eq_toInt (x := xb) (by omega)
              cases s <;> cases s' <;> cases st <;>
                simp only [readV, ite_true, Bool.false_eq_true, ite_false] at hab ⊢ <;> omega
          cases st <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hrel ⊢ <;> omega
        · simp at he
      | eq bb' =>
        cases bb' with
        | false => simp at he
        | true =>
          simp only [RelHolds] at hab
          subst hab
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl
          · exact ⟨BA, BB, hBA, hBB, by dsimp only; omega⟩
          · exact ⟨BB, BA, hBB, hBA, by dsimp only; omega⟩

theorem eventually_all {α : Type} {P : α → Nat → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ N, ∀ K, N ≤ K → P a K) → ∃ N, ∀ K, N ≤ K → ∀ a ∈ l, P a K
  | [], _ => ⟨0, fun _ _ _ h => by simp at h⟩
  | a :: l, h => by
    obtain ⟨N1, h1⟩ := h a List.mem_cons_self
    obtain ⟨N2, h2⟩ := eventually_all (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨max N1 N2, fun K hK b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h1 K (by omega)
    · exact h2 K (by omega) b hb

/-- All edges of the path facts hold at enough fuel. -/
theorem allEdges_sound (h : AsmHolds D tabs ρ A) (s : Bool) (w : Width) :
    ∃ N, ∀ K, N ≤ K → ∀ e ∈ A.facts.flatMap (factEdges D tabs A k s w),
      EdgeHolds D tabs ρ s w K e := by
  obtain ⟨N, hN⟩ := eventually_all (P := fun fact K => ∀ e ∈ factEdges D tabs A k s w fact,
    EdgeHolds D tabs ρ s w K e) (l := A.facts) fun fact hf => factEdges_sound h hf
  refine ⟨N, fun K hK e he => ?_⟩
  obtain ⟨fact, hf, he⟩ := List.mem_flatMap.1 he
  exact hN K hK fact hf e he

end

/-! ## Paths of edges -/

theorem foldl_inv {α β : Type} {f : β → α → β} {Q : β → Prop} :
    ∀ {l : List α} {b : β}, (∀ b a, a ∈ l → Q b → Q (f b a)) → Q b → Q (l.foldl f b)
  | [], _, _, hb => hb
  | a :: l, b, h, hb => by
    rw [List.foldl_cons]
    exact foldl_inv (fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')) (h b a List.mem_cons_self hb)

section
variable {P : ID → Int → Prop}

theorem addDist_sound {dist : List (ID × Int)} {v : ID} {d : Int}
    (h1 : ∀ z e, (z, e) ∈ dist → P z e) (h2 : P v d) : ∀ z e, (z, e) ∈ addDist dist v d → P z e := by
  unfold addDist
  split
  · exact h1
  · intro z e he
    rcases List.mem_cons.1 he with e' | he
    · simp only [Prod.mk.injEq] at e'; obtain ⟨rfl, rfl⟩ := e'; exact h2
    · exact h1 z e he

theorem relax_sound {es : List (ID × ID × Int)}
    (hes : ∀ u v c, (u, v, c) ∈ es → ∀ d, P u d → P v (d + c)) {dist : List (ID × Int)}
    (h : ∀ z e, (z, e) ∈ dist → P z e) : ∀ z e, (z, e) ∈ relax es dist → P z e := by
  unfold relax
  refine foldl_inv (Q := fun dist => ∀ z e, (z, e) ∈ dist → P z e) (fun dist0 q hq h0 => ?_) h
  obtain ⟨u, v, c⟩ := q
  refine foldl_inv (Q := fun dist => ∀ z e, (z, e) ∈ dist → P z e) (fun acc p hp hacc => ?_) h0
  obtain ⟨z, d⟩ := p
  dsimp only
  split
  · rename_i hz
    simp only [beq_iff_eq] at hz; subst hz
    exact addDist_sound hacc (hes _ _ _ hq d (h0 _ _ hp))
  · exact hacc

theorem distFrom_sound {es : List (ID × ID × Int)}
    (hes : ∀ u v c, (u, v, c) ∈ es → ∀ d, P u d → P v (d + c)) {x : ID} (hx : P x 0) :
    ∀ z e, (z, e) ∈ distFrom es x → P z e := by
  unfold distFrom
  refine foldl_inv (Q := fun dist => ∀ z e, (z, e) ∈ dist → P z e)
    (fun dist _ _ h => relax_sound hes h) ?_
  intro z e he
  simp only [List.mem_singleton, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact hx

end

/-- **Differences along paths**, from `x`: if every edge holds at fuel `K` and `diffLe` bounds
`V(x) - V(y)`, then `y` is defined and the bound holds. -/
theorem diffLe_sound' {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {s : Bool}
    {w : Width} {K : Nat} {es : List (ID × ID × Int)}
    (hes : ∀ e ∈ es, EdgeHolds D tabs ρ s w K e) {x y : ID} {c : Int}
    (hd : diffLe es x y c = true) {X : BitVec w.bits} (hx : den D tabs ρ K x = .int w X) :
    ∃ Y : BitVec w.bits, den D tabs ρ K y = .int w Y ∧ readV s X - readV s Y ≤ c := by
  let P : ID → Int → Prop := fun z d =>
    ∃ Z : BitVec w.bits, den D tabs ρ K z = .int w Z ∧ readV s X - readV s Z ≤ d
  have hP : ∀ z e, (z, e) ∈ distFrom es x → P z e := by
    refine distFrom_sound (fun u v c huv d hu => ?_) ⟨X, hx, by omega⟩
    obtain ⟨U, hU, hd⟩ := hu
    obtain ⟨U', V, hU', hV, hc⟩ := hes _ huv
    dsimp only at hU' hV hc
    rw [hU] at hU'; cases val_int_eq hU'
    exact ⟨V, hV, by omega⟩
  unfold diffLe at hd
  obtain ⟨⟨z, e⟩, hm, hze⟩ := List.any_eq_true.1 hd
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hze
  obtain ⟨rfl, hle⟩ := hze
  obtain ⟨Z, hZ, hz⟩ := hP _ _ hm
  exact ⟨Z, hZ, by omega⟩

/-- **Differences along paths**: if every edge holds at fuel `K`, `diffLe` bounds
`V(x) - V(y)`. -/
theorem diffLe_sound {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {s : Bool}
    {w : Width} {K : Nat} {es : List (ID × ID × Int)}
    (hes : ∀ e ∈ es, EdgeHolds D tabs ρ s w K e) {x y : ID} {c : Int}
    (hd : diffLe es x y c = true) {X Y : BitVec w.bits} (hx : den D tabs ρ K x = .int w X)
    (hy : den D tabs ρ K y = .int w Y) : readV s X - readV s Y ≤ c := by
  obtain ⟨Y', hY', hle⟩ := diffLe_sound' hes hd hx
  rw [hy] at hY'; cases val_int_eq hY'
  exact hle

/-- **Differences along paths with a last edge that holds only between defined ends.** -/
theorem diffLeR_sound {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {s : Bool}
    {w : Width} {K : Nat} {es rs : List (ID × ID × Int)}
    (hes : ∀ e ∈ es, EdgeHolds D tabs ρ s w K e)
    (hrs : ∀ z y c, (z, y, c) ∈ rs → ∀ Z Y : BitVec w.bits, den D tabs ρ K z = .int w Z →
      den D tabs ρ K y = .int w Y → readV s Z - readV s Y ≤ c)
    {x y : ID} {c : Int} (hd : diffLeR es rs x y c = true) {X Y : BitVec w.bits}
    (hx : den D tabs ρ K x = .int w X) (hy : den D tabs ρ K y = .int w Y) :
    readV s X - readV s Y ≤ c := by
  unfold diffLeR at hd
  rcases Bool.or_eq_true_iff.1 hd with hd | hd
  · exact diffLe_sound hes hd hx hy
  · obtain ⟨⟨z, y', c'⟩, hm, hz⟩ := List.any_eq_true.1 hd
    simp only [Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨rfl, hz⟩ := hz
    obtain ⟨Z, hZ, hle⟩ := diffLe_sound' hes hz hx
    have := hrs z y' c' hm Z Y hZ hy
    omega

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {A : Asm} {k : Nat}

/-- **The relations' edges into `y` hold** between defined ends. -/
theorem relEdges_sound (h : AsmHolds D tabs ρ A) {w : Width} {y : ID} {K : Nat} :
    ∀ z y' c, (z, y', c) ∈ relEdges D tabs A k w y → ∀ Z Y : BitVec w.bits,
      den D tabs ρ K z = .int w Z → den D tabs ρ K y' = .int w Y →
        readV true Z - readV true Y ≤ c := by
  intro z y' c hm Z Y hZ hY
  unfold relEdges at hm
  dsimp only at hm
  split at hm
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    obtain ⟨⟨z0, y0, w0, c0⟩, hm', he⟩ := List.mem_filterMap.1 hm
    dsimp only at he
    split at he
    · rename_i hw
      simp only [Bool.and_eq_true, beq_iff_eq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp only [Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl⟩ := he
      obtain ⟨-, -, m1, -⟩ := rng_sound h k _ _ K Y hY
      simp only [readV, ite_true]
      exact h.rels _ _ _ _ hm' K Z Y hZ hY (by omega)
    · cases he
  · simp at hm

/-- **Differences from the path facts and a last relation edge are sound.** -/
theorem linLe_sound (h : AsmHolds D tabs ρ A) {s : Bool} {w : Width} {x y : ID} {c : Int}
    (hp : diffLeR (linFacts D tabs A k s w) (linRels D tabs A k s w y) x y c = true) {K : Nat}
    {X Y : BitVec w.bits} (hx : den D tabs ρ K x = .int w X) (hy : den D tabs ρ K y = .int w Y) :
    readV s X - readV s Y ≤ c := by
  obtain ⟨N, hN⟩ := allEdges_sound (k := k) h s w
  have hx' := den_stable_int hx (Nat.le_max_right N K)
  have hy' := den_stable_int hy (Nat.le_max_right N K)
  refine diffLeR_sound (hN _ (Nat.le_max_left N K)) (fun z y c hm Z Y hZ hY => ?_) hp hx' hy'
  cases s
  · simp [linRels] at hm
  · simp only [linRels, ite_true] at hm
    exact relEdges_sound h z y c hm Z Y hZ hY

end

end GoFV.Proof.ProveCheck
