import GoFV.Proof.Pass.SegSound

/-!
# Segments: the relation (issue #151)

What the checker `GoFV.Opt.RewriteCheck.segRel` says, declaratively: a segment (`SegD`, from
`segOK`: the anchor redefined in place, its dropped and fresh values and the order of the
latter), and the relation's global and per-block facts (`segRel_spec`, `SRel`, `BlockSpec`).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck

variable {tabs : Tables} {f g : Func}

/-- The target values a segment of anchor `x` evaluates: its fresh values, then the anchor. -/
abbrev segL (x : ID) (N : List ID) : List ID := N ++ [x]

/-- What `segOK tabs f g x = some (D, N)` says. -/
structure SegD (tabs : Tables) (f g : Func) (x : ID) (D N : List ID) where
  fv : Value
  gv : Value
  hfv : f.value? x = some fv
  hgv : g.value? x = some gv
  hns : ssSame fv gv = false
  hgid : gv.id = x
  hgbl : gv.block = fv.block
  hgty : gv.type = fv.type
  hfph : fv.op ≠ .Phi
  hfop : fv.op = .Store ∨ fv.op = .SelectN ∨ fv.op = .Move
  hbm : fv.block ∈ f.blocks
  hlisted : ∃ b, f.block? fv.block = some b ∧ x ∈ b.values
  hkind : chainSeg? tabs f g x fv gv = some (D, N) ∨ callSeg? tabs f g fv gv = some (D, N) ∨
    roSeg? tabs f fv gv = some (D, N) ∨ moveSeg? tabs f g x fv gv = some (D, N)
  hD : ∀ d ∈ D, (∃ b, f.block? fv.block = some b ∧ d ∈ b.values) ∧ CSE.rootNode f d = true
  hN : ∀ n ∈ N, f.value? n = none ∧ (∃ b, g.block? fv.block = some b ∧ n ∈ b.values) ∧
    ∃ v, g.value? n = some v ∧ v.block = fv.block
  hroot : CSE.rootNode g x = true
  /-- A fresh value is a root of `g`, or an `OffPtr` of arguments of roots of the segment. -/
  hfresh : ∀ n ∈ N, CSE.rootNode g n = true ∨ ∃ v, g.value? n = some v ∧ v.op = .OffPtr ∧
    ∀ a ∈ v.args, ∃ s ∈ D ++ [x], CSE.rootNode f s = true ∧ ∃ sv, f.value? s = some sv ∧ a ∈ sv.args
  hargs : ∀ i < (segL x N).length, ∀ v, g.value? ((segL x N).getD i 0) = some v →
    ∀ a ∈ v.args, a ∈ (segL x N).take i ∨ (a ∉ D ∧ a ∉ segL x N ∧
      ∃ s ∈ D ++ [x], CSE.rootNode f s = true ∧ argReach f 8 s a = true)
  hseg : segOK tabs f g x = some (D, N)

theorem any_contains_iff {o : Option Block} {z : ID} :
    (o.any (·.values.contains z)) = true ↔ ∃ blk, o = some blk ∧ z ∈ blk.values := by
  cases o <;> simp [Array.contains_iff_mem]

theorem segOK_spec {x : ID} {D N : List ID} (h : segOK tabs f g x = some (D, N)) :
    Nonempty (SegD tabs f g x D N) := by
  have h0 := h
  unfold segOK at h
  cases hfv : f.value? x with
  | none => rw [hfv] at h; cases h
  | some fv =>
  cases hgv : g.value? x with
  | none => rw [hfv, hgv] at h; cases h
  | some gv =>
  rw [hfv, hgv] at h
  dsimp only at h
  by_cases hc : (!ssSame fv gv && gv.id == x && gv.block == fv.block && gv.type == fv.type &&
      (fv.op == .Store || fv.op == .SelectN || fv.op == .Move) && f.blocks.contains fv.block &&
      (f.block? fv.block).any (·.values.contains x)) = true
  rotate_left
  · rw [ite_eq_right hc] at h; cases h
  rw [ite_eq_left hc] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hns, hgid⟩, hgbl⟩, hgty⟩, hfph⟩, hbm⟩, hli⟩ := hc
  have hbm' : fv.block ∈ f.blocks := by simpa using hbm
  have hns' : ssSame fv gv = false := by simpa using hns
  have hfop : fv.op = .Store ∨ fv.op = .SelectN ∨ fv.op = .Move := by simpa [or_assoc] using hfph
  have hfph' : fv.op ≠ .Phi := by rcases hfop with h | h | h <;> rw [h] <;> decide
  generalize hk : (((chainSeg? tabs f g x fv gv).orElse fun _ => callSeg? tabs f g fv gv).orElse
    (fun _ => roSeg? tabs f fv gv)).orElse (fun _ => moveSeg? tabs f g x fv gv) = k at h
  cases k with
  | none => cases h
  | some p =>
  obtain ⟨D', N'⟩ := p
  dsimp only at h
  split at h
  next hcond =>
    cases h
    have hkind : chainSeg? tabs f g x fv gv = some (D, N) ∨
        callSeg? tabs f g fv gv = some (D, N) ∨ roSeg? tabs f fv gv = some (D, N) ∨
        moveSeg? tabs f g x fv gv = some (D, N) := by
      cases hch : chainSeg? tabs f g x fv gv with
      | some q => rw [hch] at hk; exact .inl hk
      | none =>
        cases hca : callSeg? tabs f g fv gv with
        | some q => rw [hch, hca] at hk; exact .inr (.inl hk)
        | none =>
          cases hro : roSeg? tabs f fv gv with
          | some q => rw [hch, hca, hro] at hk; exact .inr (.inr (.inl hk))
          | none => rw [hch, hca, hro] at hk; exact .inr (.inr (.inr hk))
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Option.isNone_iff_eq_none, Option.all_eq_true, List.contains_iff_mem,
      Bool.not_eq_true', decide_eq_true_eq] at hcond
    obtain ⟨⟨⟨⟨⟨hDl, hDr⟩, hNs⟩, hrx⟩, hrt⟩, hord⟩ := hcond
    have hN' : ∀ n ∈ N, f.value? n = none ∧ (∃ b, g.block? fv.block = some b ∧ n ∈ b.values) ∧
        ∃ v, g.value? n = some v ∧ v.block = fv.block := fun n hn => by
      obtain ⟨⟨h1, h2⟩, h3⟩ := hNs n hn
      simp only [Option.any_eq_true, beq_iff_eq] at h3
      exact ⟨h1, any_contains_iff.1 h2, h3⟩
    have hA' : ∀ i < (segL x N).length, ∀ v, g.value? ((segL x N).getD i 0) = some v →
        ∀ a ∈ v.args, a ∈ (segL x N).take i ∨ (a ∉ D ∧ a ∉ segL x N ∧
          ∃ s ∈ D ++ [x], CSE.rootNode f s = true ∧ argReach f 8 s a = true) := by
      intro i hi v hv a ha
      have := hord i hi v hv
      simp only [Array.all_eq_true'] at this
      have := this a ha
      simp only [List.any_eq_true, Bool.and_eq_true, List.mem_append,
        List.mem_singleton, Bool.not_eq_true, Bool.or_eq_true,
        List.contains_iff_mem] at this
      rcases this with h | ⟨⟨h1, h2⟩, s, hs, hr, har⟩
      · exact .inl h
      · refine .inr ⟨by simpa using h1, by simpa using h2, s, ?_, hr, har⟩
        simpa [List.mem_append] using hs
    have hF' : ∀ n ∈ N, CSE.rootNode g n = true ∨ ∃ v, g.value? n = some v ∧ v.op = .OffPtr ∧
        ∀ a ∈ v.args, ∃ s ∈ D ++ [x], CSE.rootNode f s = true ∧ ∃ sv, f.value? s = some sv ∧
          a ∈ sv.args := by
      intro n hn
      rcases hrt n hn with h | h
      · exact .inl h
      · right
        cases hgn : g.value? n with
        | none => simp [hgn] at h
        | some v =>
          simp only [hgn, Option.any_some, Bool.and_eq_true, beq_iff_eq,
            Array.all_eq_true'] at h
          refine ⟨v, rfl, h.1, fun a ha => ?_⟩
          have := h.2 a ha
          simp only [List.any_eq_true, Bool.and_eq_true, Option.any_eq_true, List.mem_append,
            List.mem_singleton, Array.contains_iff_mem] at this
          obtain ⟨s, hs, hr, sv, hsv, has⟩ := this
          exact ⟨s, by simpa [List.mem_append] using hs, hr, sv, hsv, has⟩
    exact ⟨⟨fv, gv, hfv, hgv, hns', hgid, hgbl, hgty, hfph', hfop, hbm', any_contains_iff.1 hli, hkind,
      fun d hd => ⟨any_contains_iff.1 (hDl d hd), hDr d hd⟩, hN', hrx, hF', hA', h0⟩⟩
  next => cases h

/-- The segments by anchor (`segRel`'s array). -/
theorem segArr_get (x : ID) : (segArr tabs f g)[x]?.join = segOK tabs f g x := by
  unfold segArr
  rw [Array.getElem?_map, Array.getElem?_range]
  split
  · rfl
  · rename_i hx
    unfold segOK
    have : f.value? x = none := by
      unfold Func.value?; rw [Array.getElem?_eq_none (by omega)]; rfl
    simp [this]

theorem mem_segList {x : ID} {D N : List ID} :
    (x, D, N) ∈ segList (segArr tabs f g) ↔ segOK tabs f g x = some (D, N) := by
  unfold segList
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨y, -, hy⟩
    rw [Option.map_eq_some_iff] at hy
    obtain ⟨p, hp, hpe⟩ := hy
    cases hpe
    rw [← segArr_get]; exact hp
  · intro h
    have hx : x < (segArr tabs f g).size := by
      unfold segOK at h
      cases hfv : f.value? x with
      | none => rw [hfv] at h; cases h
      | some _ => simp [segArr, lt_of_value? hfv]
    exact ⟨x, List.mem_range.2 hx, by rw [segArr_get, h]; rfl⟩

/-- The keys of `segList` are its entries' anchors, one entry each. -/
theorem segList_key {A : Array (Option (List ID × List ID))} {s s' : ID × List ID × List ID}
    (hs : s ∈ segList A) (hs' : s' ∈ segList A) (h : s.1 = s'.1) : s = s' := by
  unfold segList at hs hs'
  rw [List.mem_filterMap] at hs hs'
  obtain ⟨y, -, hy⟩ := hs
  obtain ⟨y', -, hy'⟩ := hs'
  rw [Option.map_eq_some_iff] at hy hy'
  obtain ⟨p, hp, rfl⟩ := hy
  obtain ⟨p', hp', rfl⟩ := hy'
  simp only at h
  subst h
  rw [hp] at hp'; cases hp'; rfl

/-- `z` is dropped by the segment of anchor `x`. -/
def Drop (tabs : Tables) (f g : Func) (x z : ID) : Prop :=
  ∃ D N, segOK tabs f g x = some (D, N) ∧ z ∈ D

/-- `z` is a fresh value of some segment. -/
def Fresh (tabs : Tables) (f g : Func) (z : ID) : Prop :=
  ∃ x D N, segOK tabs f g x = some (D, N) ∧ z ∈ N

theorem segOwner_some {segs : List (ID × List ID × List ID)} {z x : ID}
    (h : segOwner segs z = some x) : ∃ D N, (x, D, N) ∈ segs ∧ z ∈ D := by
  unfold segOwner at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨x', D, N⟩, hf, rfl⟩ := h
  exact ⟨D, N, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

theorem segOwner_none {segs : List (ID × List ID × List ID)} {z : ID}
    (h : segOwner segs z = none) : ∀ s ∈ segs, z ∉ s.2.1 := by
  unfold segOwner at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro s hs hz
  exact h s hs (by simpa using hz)

/-- The fresh values of a segment, in `segRel`'s list. -/
theorem news_mem {z : ID} (h : z ∈ (segList (segArr tabs f g)).flatMap (·.2.2)) :
    Fresh tabs f g z := by
  rw [List.mem_flatMap] at h
  obtain ⟨⟨x, D, N⟩, hs, hz⟩ := h
  exact ⟨x, D, N, mem_segList.1 hs, hz⟩

/-- One block of `segRel`. -/
structure BlockSpec (tabs : Tables) (f g : Func) (bid : ID) (fb gb : Block) : Prop where
  kind : gb.kind = fb.kind
  controls : gb.controls = fb.controls
  values : ∃ E : Array ID,
    gb.values = fb.values.filter (fun z => (segOwner (segList (segArr tabs f g)) z).isNone) ++ E ∧
    ∀ z ∈ E, f.value? z = none ∧ Fresh tabs f g z ∧ ∃ v, g.value? z = some v ∧ v.block = bid
  sched : ∀ oS, Sem.schedule f fb = some oS → ∃ oT, Sem.schedule g gb = some oT ∧
    oT.toList.filter (CSE.rootNode g) =
      segRoots g (segList (segArr tabs f g)) (oS.toList.filter (CSE.rootNode f))

/-- **What `segRel` says.** -/
structure SRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  size : f.valueTab.size ≤ g.valueTab.size
  value : ∀ x fv, f.value? x = some fv →
    (∃ gv, g.value? x = some gv ∧ (ssSame fv gv = true ∨ ∃ D N, segOK tabs f g x = some (D, N))) ∨
    (g.value? x = none ∧ ∃ x', Drop tabs f g x' x)
  own : ∀ z x, segOwner (segList (segArr tabs f g)) z = some x ↔ Drop tabs f g x z
  dropNone : ∀ x z, Drop tabs f g x z → g.value? z = none
  anchorNot : ∀ x D N, segOK tabs f g x = some (D, N) → ∀ x', ¬ Drop tabs f g x' x
  freshUniq : ∀ x x' D D' N N' n, segOK tabs f g x = some (D, N) →
    segOK tabs f g x' = some (D', N') → n ∈ N → n ∈ N' → x = x'
  lnd : ∀ x D N, segOK tabs f g x = some (D, N) → (segL x N).Nodup
  fresh : ∀ z gv, f.value? z = none → g.value? z = some gv → Fresh tabs f g z
  ctrls : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∀ c ∈ fb.controls, ∀ x,
    ¬ Drop tabs f g x c
  uses : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∀ z ∈ fb.values, ∀ zv,
    f.value? z = some zv → ∀ a ∈ zv.args, ∀ x, Drop tabs f g x a → z = x ∨ Drop tabs f g x z
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    BlockSpec tabs f g bid fb gb

theorem extract_append {a : Array ID} {k : Nat} (hk : k ≤ a.size) :
    a = a.extract 0 k ++ a.extract k a.size := by
  apply Array.ext (by simp; omega)
  intro i h1 h2
  simp only [Array.getElem_append, Array.size_extract, Array.getElem_extract]
  split <;> (congr 1; omega)

theorem lt_of_some {x : ID} {fv : Value} (hfv : f.value? x = some fv) : x < f.valueTab.size := by
  unfold Func.value? at hfv
  rcases Nat.lt_or_ge x f.valueTab.size with h | h
  · exact h
  · rw [Array.getElem?_eq_none h] at hfv; cases hfv

/-- Distinct segments drop distinct values (`drops.Nodup`). -/
theorem drop_uniq {segs : List (ID × List ID × List ID)} (hnd : (segs.flatMap (·.2.1)).Nodup)
    {s s' : ID × List ID × List ID} (hs : s ∈ segs) (hs' : s' ∈ segs) {z : ID} (hz : z ∈ s.2.1)
    (hz' : z ∈ s'.2.1) : s = s' := by
  induction segs with
  | nil => simp at hs
  | cons t segs ih =>
    rw [List.flatMap_cons, List.nodup_append] at hnd
    obtain ⟨h1, h2, h3⟩ := hnd
    rcases List.mem_cons.1 hs with e1 | m1 <;> rcases List.mem_cons.1 hs' with e2 | m2
    · rw [e1, e2]
    · subst e1; exact absurd rfl (h3 z hz z (List.mem_flatMap.2 ⟨s', m2, hz'⟩))
    · subst e2; exact absurd rfl (h3 z hz' z (List.mem_flatMap.2 ⟨s, m1, hz⟩))
    · exact ih h2 m1 m2

theorem nodup_of_flatMap {α β : Type} {h : α → List β} :
    ∀ {l : List α}, (l.flatMap h).Nodup → ∀ {s : α}, s ∈ l → (h s).Nodup
  | [], _, _, hs => by simp at hs
  | t :: l, hnd, s, hs => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    rcases List.mem_cons.1 hs with rfl | hs
    · exact hnd.1
    · exact nodup_of_flatMap hnd.2.1 hs

theorem segRel_spec (h : segRel tabs f g = true) : SRel tabs f g := by
  unfold segRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hnd⟩, hnn⟩, hanc⟩, hval⟩, hdn⟩, hnew⟩, huse⟩, hblk⟩ := h
  generalize hS : segList (segArr tabs f g) = segs at *
  have hmem : ∀ x D N, (x, D, N) ∈ segs ↔ segOK tabs f g x = some (D, N) := fun x D N => by
    rw [← hS]; exact mem_segList
  have hownI : ∀ z x, segOwner segs z = some x ↔ Drop tabs f g x z := fun z x => by
    constructor
    · intro ho
      obtain ⟨D, N, hs, hz⟩ := segOwner_some ho
      exact ⟨D, N, (hmem x D N).1 hs, hz⟩
    · rintro ⟨D, N, hs, hz⟩
      cases ho : segOwner segs z with
      | none => exact absurd hz (segOwner_none ho (x, D, N) ((hmem x D N).2 hs))
      | some x' =>
        obtain ⟨D', N', hs', hz'⟩ := segOwner_some ho
        have := drop_uniq hnd hs' ((hmem x D N).2 hs) hz' hz
        cases this; rfl
  have hnews : ∀ z ∈ segs.flatMap (·.2.2), Fresh tabs f g z := by
    intro z hz; rw [← hS] at hz; exact news_mem hz
  refine ⟨hcfg, hown, hsz, fun x fv hfv => ?_, by rw [← hS] at hownI; exact hownI,
    fun x z ⟨D, N, hs, hz⟩ => ?_, fun x D N hs x' hd => ?_, fun x x' D D' N N' n hs hs' hn hn' => ?_,
    fun x D N hs => ?_, fun z gv hfz hgz => ?_, fun b hb fb hfb c hc x hd => ?_,
    fun b hb fb hfb z hz zv hzv a ha x hd => ?_, fun bid hb fb hfb => ?_⟩
  · have := hval x (lt_of_some hfv)
    rw [hfv] at this
    cases hgv : g.value? x with
    | none =>
      rw [hgv] at this
      simp only [Option.isSome_iff_exists] at this
      obtain ⟨x', ho⟩ := this
      exact .inr ⟨rfl, x', (hownI x x').1 ho⟩
    | some gv =>
      rw [hgv] at this
      simp only [Bool.or_eq_true, Option.isSome_iff_exists] at this
      refine .inl ⟨gv, rfl, this.imp id fun ⟨p, hp⟩ => ⟨p.1, p.2, hp⟩⟩
  · have := hdn z (List.mem_flatMap.2 ⟨(x, D, N), (hmem x D N).2 hs, hz⟩)
    simpa using this
  · have := hanc (x, D, N) ((hmem x D N).2 hs)
    simp only [Option.isNone_iff_eq_none] at this
    rw [(hownI x x').2 hd] at this; cases this
  · have h1 : (x, D, N) ∈ segs := (hmem x D N).2 hs
    have h2 : (x', D', N') ∈ segs := (hmem x' D' N').2 hs'
    have := drop_uniq (segs := segs.map fun s => (s.1, s.2.2, s.2.1))
      (by simpa [List.flatMap_map] using hnn) (List.mem_map_of_mem h1) (List.mem_map_of_mem h2)
      (z := n) hn hn'
    simp only [Prod.mk.injEq] at this
    exact this.1
  · obtain ⟨d⟩ := segOK_spec hs
    have hN : N.Nodup := nodup_of_flatMap hnn ((hmem x D N).2 hs)
    refine List.nodup_append.2 ⟨hN, by simp, fun a ha b hb hab => ?_⟩
    rw [List.mem_singleton] at hb
    subst hb hab
    have := d.hfv
    rw [(d.hN a ha).1] at this
    cases this
  · have := hnew z
    have hz : z < g.valueTab.size := lt_of_some hgz
    simp only [hfz, hgz, Option.isSome_none, Option.isNone_some, Bool.false_or,
      List.contains_iff_mem] at this
    exact hnews z (this hz)
  · have := huse b hb
    simp only [hfb, Bool.and_eq_true, List.all_eq_true, Array.all_eq_true',
      Option.isNone_iff_eq_none] at this
    have hc' := this.1 c hc
    rw [(hownI c x).2 hd] at hc'; cases hc'
  · have := huse b hb
    simp only [hfb, Bool.and_eq_true, Array.all_eq_true', Option.all_eq_true] at this
    have h2 := this.2 z hz zv hzv
    have h3 := h2 a ha
    rw [(hownI a x).2 hd] at h3
    simp only [Bool.or_eq_true, beq_iff_eq] at h3
    rcases h3 with h3 | h3
    · exact .inl h3
    · exact .inr ((hownI z x).1 h3)
  · have := hblk bid hb
    unfold segBlockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true] at this
      obtain ⟨⟨⟨⟨⟨hk, hc⟩, hle⟩, hpre⟩, hext⟩, hsch⟩ := this
      refine ⟨gb, rfl, hk, hc, ⟨gb.values.extract (fb.values.filter fun z =>
        (segOwner segs z).isNone).size gb.values.size, ?_, ?_⟩, ?_⟩
      · rw [hS]
        conv => lhs; rw [extract_append hle]
        rw [hpre]
      · intro z hz
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hz
        have := hext i hi
        simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.contains_iff_mem,
          Option.any_eq_true, beq_iff_eq] at this
        obtain ⟨⟨h1, h2⟩, v, h3, h4⟩ := this
        exact ⟨h1, hnews _ h2, v, h3, h4⟩
      · intro oS hoS
        rw [hoS] at hsch
        simp only at hsch
        cases hoT : Sem.schedule g gb with
        | none => rw [hoT] at hsch; cases hsch
        | some oT =>
          rw [hoT] at hsch
          exact ⟨oT, rfl, by rw [hS]; simpa using hsch⟩

end GoFV.Proof.Seg
