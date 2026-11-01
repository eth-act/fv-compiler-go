import GoFV.Proof.Pass.WBOrder

/-!
# writebarrier: the order of the non-pure nodes of a chain (issue #36)

`np_before`, `np_before_seg`: the order of the non-pure nodes of `B` that `npOK` fixes (ranks
`NpRank`), `held_rank`: the rank of a held non-pure node listed in a segment, `npOf_kept`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-! ## Generic helpers -/

private theorem mapM_some {α β : Type} {F : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM F = some l' →
      l'.length = l.length ∧ ∀ j : Nat, l'[j]? = l[j]?.bind F
  | [], l', h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨rfl, fun _ => rfl⟩
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, l'', hl, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mapM_some hl
    refine ⟨by simp [h1], fun j => ?_⟩
    cases j with
    | zero => simp [hb]
    | succ j => simp [h2 j]

private theorem before_app {P Q : List ID} {x y : ID} (hx : x ∈ P) (hy : y ∈ Q) :
    Order.Before (P ++ Q) x y := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hy
  have hil : i < P.length := (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨i, P.length + j, by omega, ?_, ?_⟩
  · rw [List.getElem?_append_left hil]; exact hi
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact hj

private theorem before_infix {P A Q : List ID} {x y : ID} (h : Order.Before A x y) :
    Order.Before (P ++ (A ++ Q)) x y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  have hjl : j < A.length := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨P.length + i, P.length + j, by omega, ?_, ?_⟩
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by omega)]
    exact hi
  · rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left hjl]
    exact hj

private theorem flat_split {L : List (List ID)} {i j : Nat} {A A' : List ID} {x y : ID}
    (hA : L[i]? = some A) (hA' : L[j]? = some A') (hij : i < j) (hx : x ∈ A) (hy : y ∈ A') :
    Order.Before L.flatten x y := by
  rw [← List.take_append_drop j L, List.flatten_append]
  apply before_app
  · exact List.mem_flatten.2
      ⟨A, List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hij]; exact hA), hx⟩
  · exact List.mem_flatten.2
      ⟨A', List.mem_of_getElem? (i := 0) (by rw [List.getElem?_drop, Nat.add_zero]; exact hA'), hy⟩

private theorem flat_infix {L : List (List ID)} {i : Nat} {A : List ID} {x y : ID}
    (hA : L[i]? = some A) (h : Order.Before A x y) : Order.Before L.flatten x y := by
  obtain ⟨hil, hAi⟩ := List.getElem?_eq_some_iff.1 hA
  rw [← List.take_append_drop i L, List.drop_eq_getElem_cons hil, hAi, List.flatten_append,
    List.flatten_cons]
  exact before_infix h

private theorem flat_pairs {α β : Type} (a b : α → List β) : ∀ zs : List α,
    (zs.flatMap fun p => [a p, b p]).flatten = zs.flatMap fun p => a p ++ b p
  | [] => rfl
  | p :: zs => by simp [List.flatMap_cons, flat_pairs a b zs]

private theorem pairs_idx {α β : Type} (a b : α → List β) : ∀ (zs : List α) (t : Nat),
    (zs.flatMap fun p => [a p, b p])[2 * t]? = zs[t]?.map a ∧
    (zs.flatMap fun p => [a p, b p])[2 * t + 1]? = zs[t]?.map b
  | [], t => by simp
  | p :: zs, 0 => by simp
  | p :: zs, t + 1 => by
    have ih := pairs_idx a b zs t
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, List.getElem?_cons_succ,
      List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_cons_succ]
    exact ih

private theorem findIdx_some {p : ID → Bool} {L : List ID} {y : ID}
    (h : L[L.findIdx p]? = some y) : p y = true := by
  obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.1 h
  rw [← heq]; exact List.findIdx_getElem (w := hlt)

/-- The last store of a run is a `WBend` of `g`. -/
private theorem runOf_last {f g : Func} {s : Split} {r : Run} (h : runOf? f g s = some r) :
    (g.value? r.last).any (fun v => v.op == Op.WBend) = true := by
  simp only [runOf?, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨phi, hphi, pv, hpv, u1, hg1, last, hlast, src, hsc, s0, hs0, v0, hv0, rfl⟩ := h
  exact findIdx_some hlast

private theorem npOf_val {h : Func} {C : Block} {x : ID} (hx : npOf h C x = true) :
    x ∈ C.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi := by
  unfold npOf at hx
  simp only [Bool.and_eq_true] at hx
  obtain ⟨hm, hv⟩ := hx
  refine ⟨Array.contains_iff_mem.1 hm, ?_⟩
  cases hw : h.value? x with
  | none => rw [hw] at hv; cases hv
  | some v =>
    rw [hw] at hv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hv
    exact ⟨v, rfl, hv.1⟩

private theorem sameV_op' {u w : Value} (h : sameV u w = true) : u.op = w.op := by
  unfold sameV at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1.1.2

private theorem held_of_K {x : ID} (hK : c.K.getD x false = true) : c.held x = true := by
  unfold Ctx.held; rw [hK]; rfl

private theorem npOf_kept' (S : Setup c b B rs l) {x : ID} (hK : c.K.getD x false = true)
    {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {C : Block} (hC : c.g.block? s = some C)
    (hx : x ∈ C.values) : npOf c.g C x = npOf c.f B x := by
  have hxB : x ∈ B.values := S.held_seg ⟨s, hs, by rw [vals_of hC]; exact hx⟩ (held_of_K hK)
  obtain ⟨u, w, hu, hw, hsame, -⟩ :=
    keptMarks_spec (by rw [← (ctxOf_spec S.ctx).2.2.2.1]; exact hK)
  have hop := sameV_op' hsame
  unfold npOf
  simp only [Array.contains_iff_mem.2 hx, Array.contains_iff_mem.2 hxB, hu, hw, hop]

/-- The non-pure nodes of `B` as blocks: the kept ones of segment `k` (block `2 k`), the dropped
nil check and stores of run `j` (block `2 j + 1`). -/
private theorem np_blocks (S : Setup c b B rs l) {o : Array ID} (ho : schedule c.f B = some o) :
    ∃ L : List (List ID), o.toList.filter (npOf c.f B) = L.flatten ∧
      (∀ k s, (segsOf b rs)[k]? = some s → ∀ C, c.g.block? s = some C → ∀ oC,
        schedule c.g C = some oC →
        L[2 * k]? = some ((oC.toList.filter (npOf c.g C)).filter (c.K.getD · false))) ∧
      (∀ j r, rs[j]? = some r → L[2 * j + 1]? = some (ncsOf c r ++ r.src)) := by
  obtain ⟨src, k0, ks, hsrc, hm, heq⟩ := npOK_spec (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.2
  have hsrc' : o.toList.filter (npOf c.f B) = src := by
    unfold Ctx.npSeq at hsrc; rw [ho] at hsrc; exact Option.some.inj hsrc
  obtain ⟨hlen, hidx⟩ := mapM_some hm
  have hlen' : ks.length = rs.length := by
    simp only [List.length_cons, segs_length] at hlen; omega
  refine ⟨k0 :: (rs.zip ks).flatMap (fun p => [ncsOf c p.1 ++ p.1.src, p.2]), ?_, ?_, ?_⟩
  · rw [hsrc', heq, List.flatten_cons, flat_pairs]
  · intro k s hs C hC oC hoC
    have hk : (k0 :: ks)[k]? = c.keptNP s := by rw [hidx k, hs]; rfl
    have hkl : k < (k0 :: ks).length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hs).1
    obtain ⟨K, hK⟩ : ∃ K, c.keptNP s = some K := by
      rw [← hk]; exact ⟨_, List.getElem?_eq_getElem hkl⟩
    obtain ⟨C', oC', hC', hoC', rfl⟩ := keptNP_spec hK
    rw [hC] at hC'; cases hC'
    rw [hoC] at hoC'; cases hoC'
    rw [hK] at hk
    cases k with
    | zero => simpa using hk
    | succ t =>
      rw [List.getElem?_cons_succ] at hk
      have htl : t < rs.length := by rw [← hlen']; exact (List.getElem?_eq_some_iff.1 hk).1
      have hr : rs[t]? = some rs[t] := List.getElem?_eq_getElem htl
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by omega, List.getElem?_cons_succ,
        (pairs_idx _ _ _ t).2, (List.getElem?_zip_eq_some (z := (rs[t], _))).2 ⟨hr, hk⟩]
      rfl
  · intro j r hr
    have hjl : j < ks.length := by rw [hlen']; exact (List.getElem?_eq_some_iff.1 hr).1
    have hk : ks[j]? = some ks[j] := List.getElem?_eq_getElem hjl
    rw [List.getElem?_cons_succ, (pairs_idx _ _ _ j).1,
      (List.getElem?_zip_eq_some (z := (r, ks[j]))).2 ⟨hr, hk⟩]
    rfl

/-- A non-pure node of rank `q` lies in block `q`. -/
private theorem rank_mem (S : Setup c b B rs l) {L : List (List ID)}
    (hL1 : ∀ k s, (segsOf b rs)[k]? = some s → ∀ C, c.g.block? s = some C → ∀ oC,
        schedule c.g C = some oC →
        L[2 * k]? = some ((oC.toList.filter (npOf c.g C)).filter (c.K.getD · false)))
    (hL2 : ∀ j r, rs[j]? = some r → L[2 * j + 1]? = some (ncsOf c r ++ r.src))
    {x : ID} {q : Nat} (hq : NpRank c b rs x q) (hxn : npOf c.f B x = true) :
    ∃ A, L[q]? = some A ∧ x ∈ A := by
  rcases hq with ⟨k, rfl, ⟨s, hs, hx⟩, hK⟩ | ⟨j, r, rfl, hr, hx⟩
  · obtain ⟨C, hC, -, hsb, oC, hoC⟩ := S.seg_block hs
    refine ⟨_, hL1 k s hs C hC oC hoC, ?_⟩
    rw [vals_of hC] at hx
    have hnp : npOf c.g C x = true := by rw [npOf_kept' S hK hs hC hx]; exact hxn
    obtain ⟨ce, hwg⟩ := S.wg
    have hmem :=
      (schedule_topo (valuesOwn hwg hsb hC) (hwg.valuesNodup s C ⟨hsb, hC⟩) hoC).2.2 x
    exact List.mem_filter.2 ⟨List.mem_filter.2 ⟨hmem.2 ⟨hx, (npOf_val hnp).2⟩, hnp⟩, hK⟩
  · exact ⟨_, hL2 j r hr, List.mem_append.2 hx⟩

/-- A held value that is not kept is not the flag address or the constant. -/
private theorem not_lazy (S : Setup c b B rs l) {x : ID} (hK : c.K.getD x false = false)
    (hh : c.held x = true) (hl : c.isWbaddr x = true ∨ c.isConst0 x = true) : False := by
  have hL : c.Lst.getD x false = true := by
    unfold Ctx.held at hh; rw [hK] at hh; simpa using hh
  obtain ⟨-, -, -, -, hLst, hlz⟩ := ctxOf_spec S.ctx
  rw [hLst] at hL
  obtain ⟨b', -, rs', l', hch, r', hr', rfl⟩ := lastMarks_spec hL
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hr'
  have hlast := runOf_last ((chainRuns_spec hch).1 j r' hj).2.2.2
  cases hz : c.lazy with
  | none =>
    rcases hl with h | h
    · unfold Ctx.isWbaddr at h; rw [hz] at h; cases h
    · unfold Ctx.isConst0 at h; rw [hz] at h; cases h
  | some p =>
    obtain ⟨wa, c0⟩ := p
    rw [hz] at hlz
    obtain ⟨⟨w, hw, hop, -⟩, ⟨w', hw', hop', -⟩, -⟩ := lazyOK_some hlz
    rcases hl with h | h
    · unfold Ctx.isWbaddr at h; rw [hz] at h
      simp only [Option.any_some, beq_iff_eq] at h
      rw [← h, hw] at hlast
      simp only [Option.any_some, beq_iff_eq, hop] at hlast
      cases hlast
    · unfold Ctx.isConst0 at h; rw [hz] at h
      simp only [Option.any_some, beq_iff_eq] at h
      rw [← h, hw'] at hlast
      simp only [Option.any_some, beq_iff_eq, hop'] at hlast
      cases hlast

/-- Non-pure nodes of lower rank come first. -/
theorem np_before (S : Setup c b B rs l) {o : Array ID} (ho : schedule c.f B = some o)
    {x y : ID} {qx qy : Nat} (hx : NpRank c b rs x qx) (hy : NpRank c b rs y qy)
    (hxn : npOf c.f B x = true) (hyn : npOf c.f B y = true) (hlt : qx < qy) :
    Order.Before (o.toList.filter (npOf c.f B)) x y := by
  obtain ⟨L, hL, hL1, hL2⟩ := np_blocks S ho
  obtain ⟨A, hA, hxA⟩ := rank_mem S hL1 hL2 hx hxn
  obtain ⟨A', hA', hyA⟩ := rank_mem S hL1 hL2 hy hyn
  rw [hL]
  exact flat_split hA hA' hlt hxA hyA

/-- Kept non-pure nodes of one segment come in the target's schedule order. -/
theorem np_before_seg (S : Setup c b B rs l) {o : Array ID} (ho : schedule c.f B = some o)
    {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {C : Block} (hC : c.g.block? s = some C)
    {oC : Array ID} (hoC : schedule c.g C = some oC) {x y : ID}
    (hxK : c.K.getD x false = true) (hyK : c.K.getD y false = true)
    (hxn : npOf c.f B x = true) (hyn : npOf c.f B y = true)
    (hxy : Order.Before oC.toList x y) :
    Order.Before (o.toList.filter (npOf c.f B)) x y := by
  obtain ⟨L, hL, hL1, -⟩ := np_blocks S ho
  obtain ⟨-, -, -, hsb, -⟩ := S.seg_block hs
  obtain ⟨ce, hwg⟩ := S.wg
  have hmem := (schedule_topo (valuesOwn hwg hsb hC) (hwg.valuesNodup s C ⟨hsb, hC⟩) hoC).2.2
  obtain ⟨i, j, -, hi, hj⟩ := id hxy
  have hxC := ((hmem x).1 (List.mem_of_getElem? hi)).1
  have hyC := ((hmem y).1 (List.mem_of_getElem? hj)).1
  have hxg : npOf c.g C x = true := by rw [npOf_kept' S hxK hs hC hxC]; exact hxn
  have hyg : npOf c.g C y = true := by rw [npOf_kept' S hyK hs hC hyC]; exact hyn
  rw [hL]
  refine flat_infix (hL1 k s hs C hC oC hoC) ?_
  rw [Order.before_filter (fun z => c.K.getD z false) hxK hyK,
    Order.before_filter (npOf c.g C) hxg hyg]
  exact hxy

/-- A held non-pure node listed in segment `s` has rank `2 s` (kept) or is a store of run
`s - 1` (the run's last store). -/
theorem held_rank (S : Setup c b B rs l) {s x : ID} {k : Nat} (hs : (segsOf b rs)[k]? = some s)
    (hx : x ∈ vals c.g s) (hh : c.held x = true) :
    NpRank c b rs x (2 * k) ∨ ∃ j, k = j + 1 ∧ NpRank c b rs x (2 * j + 1) := by
  by_cases hK : c.K.getD x false = true
  · exact .inl (.inl ⟨k, rfl, ⟨s, hs, hx⟩, hK⟩)
  have hK' : c.K.getD x false = false := by simpa using hK
  have hok : c.roleOK b B (segsOf b rs) rs false k x = true :=
    (blockOK_spec S.ok S.hB S.ch).2.2.2.2.2.2.1 k s hs x hx
  cases hw : c.g.value? x with
  | none => unfold Ctx.roleOK at hok; rw [hw] at hok; cases hok
  | some w =>
    have hwa : c.isWbaddr x = false := by
      cases h : c.isWbaddr x
      · rfl
      · exact (not_lazy S hK' hh (.inl h)).elim
    have hc0 : c.isConst0 x = false := by
      cases h : c.isConst0 x
      · rfl
      · exact (not_lazy S hK' hh (.inr h)).elim
    have hρ : c.roleOf rs x = .held := by
      simp only [Ctx.roleOf, hwa, hc0, hh, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨-, -, h | ⟨-, j', r, hk, hr, hlast, -⟩⟩ := roleOK_held hok hw hρ
    · exact absurd h.1 hK
    · refine .inr ⟨j', hk, .inr ⟨j', r, rfl, hr, .inr ?_⟩⟩
      obtain ⟨-, -, hgl, -⟩ := runOf_spec ((chainRuns_spec S.ch).1 j' r hr).2.2.2
      rw [← hlast]; exact List.mem_of_getLast? hgl

/-- Kept values of `B` and run stores have the same op in `g`'s segment, so the same
non-purity. -/
theorem npOf_kept (S : Setup c b B rs l) {x : ID} (hK : c.K.getD x false = true)
    {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {C : Block} (hC : c.g.block? s = some C)
    (hx : x ∈ C.values) : npOf c.g C x = npOf c.f B x := by
  exact npOf_kept' S hK hs hC hx

end Setup

end GoFV.Proof.WB
