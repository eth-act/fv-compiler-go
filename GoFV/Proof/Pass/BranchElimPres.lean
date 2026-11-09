import GoFV.Proof.Pass.BranchElimSetup

variable [GoFV.SSA.Sem.Addrs]

/-!
# branchelim keeps well-formedness and use dominance

The step checker no longer runs `check` on its result (issue #147): `DRel.wf_pres` and
`DRel.useDom_pres` derive `WF` and `Dom.UseDom` of `g` from those of `f` and the step relation
`DRel`.

- Blocks of `g`: `dom` is the merged block (`merged_exact`), the arms and `post` are emptied
  (`Dead`, `DRel.dead`), every other block is `f`'s with its predecessor edges from `post` now
  from `dom` (`galive`).
- Values of `g`: a value listed in `f` is unchanged in what `check` reads and lies in `dom` if its
  block was one of the diamond's, else in the same block (`gvalue`, `listed_g`).
- Paths: a path of `g` expands into a path of `f` (`reach_back`): each visit of `dom` becomes
  `dom`, the arm of side 0 (if any) and `post` (`expandDom`). A block on the expanded path is on
  the path of `g` or is an arm or `post` while `dom` is (`mem_expand`), and a path of `g` visits
  no emptied block (`reach_alive`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

variable {f g : Func} {s : Site}

/-- An arm or `post`: emptied by the rewrite. -/
def Dead (s : Site) (b : ID) : Prop := b = s.post ∨ s.arm0 = some b ∨ s.arm1 = some b

/-- A block of an expanded path of `g`'s path `l`: on `l`, or emptied while `dom` is on `l`. -/
def Cov (s : Site) (l : List ID) (y : ID) : Prop := y ∈ l ∨ (Dead s y ∧ s.dom ∈ l)

/-- A path of `g` (most recent block first) with each visit of `dom` expanded into `post`, the
arm of side 0 (if any) and `dom` (most recent first). -/
def expandDom (s : Site) : List ID → List ID
  | [] => []
  | y :: l => (if y = s.dom then s.post :: (s.arm0.toList ++ [s.dom]) else [y]) ++ expandDom s l

theorem regionBlock_dead {b : ID} : s.regionBlock b = true ↔ b = s.dom ∨ Dead s b :=
  regionBlock_iff

theorem map_redir_self {a : Array Edge} (h : ∀ e ∈ a, e.b ≠ s.post) : a.map s.redir = a := by
  apply Array.ext_getElem?
  intro i
  rw [Array.getElem?_map]
  cases he : a[i]? with
  | none => rfl
  | some e => simp [Site.redir, h e (Array.mem_of_getElem? he)]

theorem getElem?_map_redir {a : Array Edge} {i : Nat} {e : Edge} (h : (a.map s.redir)[i]? = some e) :
    ∃ e0, a[i]? = some e0 ∧ e = s.redir e0 := by
  rw [Array.getElem?_map] at h
  cases he : a[i]? with
  | none => rw [he] at h; cases h
  | some e0 => rw [he] at h; cases h; exact ⟨e0, rfl, rfl⟩

theorem redir_ne {e : Edge} (h : e.b ≠ s.post) : s.redir e = e := by
  simp [Site.redir, h]

theorem redir_eq {e : Edge} (h : e.b = s.post) : s.redir e = ⟨s.dom, e.i⟩ := by
  simp [Site.redir, h]

theorem mem_expand_self {l : List ID} {y : ID} (hy : y ∈ l) : y ∈ expandDom s l := by
  induction l with
  | nil => cases hy
  | cons z l ih =>
    simp only [expandDom, List.mem_append]
    rcases List.mem_cons.1 hy with rfl | hy
    · left
      by_cases hz : y = s.dom
      · rw [if_pos hz, hz]; simp
      · rw [if_neg hz]; exact List.mem_singleton.2 rfl
    · exact .inr (ih hy)

theorem mem_expand {l : List ID} {y : ID} (hy : y ∈ expandDom s l) : Cov s l y := by
  induction l with
  | nil => simp [expandDom] at hy
  | cons z l ih =>
    simp only [expandDom, List.mem_append] at hy
    rcases hy with hy | hy
    · by_cases hz : z = s.dom
      · rw [if_pos hz] at hy
        subst hz
        rcases List.mem_cons.1 hy with rfl | hy
        · exact .inr ⟨.inl rfl, List.mem_cons_self⟩
        · rcases List.mem_append.1 hy with hy | hy
          · cases h0 : s.arm0 with
            | none => simp [h0] at hy
            | some a =>
              rw [h0] at hy
              simp only [Option.toList_some, List.mem_singleton] at hy
              subst hy
              exact .inr ⟨.inr (.inl h0), List.mem_cons_self⟩
          · rw [List.mem_singleton] at hy
            subst hy
            exact .inl List.mem_cons_self
      · rw [if_neg hz, List.mem_singleton] at hy
        subst hy
        exact .inl List.mem_cons_self
    · rcases ih hy with h | ⟨h1, h2⟩
      · exact .inl (List.mem_cons_of_mem _ h)
      · exact .inr ⟨h1, List.mem_cons_of_mem _ h2⟩

private theorem nodup_flatMap {L : ID → List ID} : ∀ {l : List ID}, l.Nodup →
    (∀ y ∈ l, (L y).Nodup) →
    (∀ y ∈ l, ∀ z ∈ l, y ≠ z → ∀ v, v ∈ L y → v ∈ L z → False) → (l.flatMap L).Nodup
  | [], _, _, _ => List.nodup_nil
  | y :: l, hnd, h1, h2 => by
    rw [List.flatMap_cons, List.nodup_append]
    obtain ⟨hy, hnd'⟩ := List.nodup_cons.1 hnd
    refine ⟨h1 y List.mem_cons_self, nodup_flatMap hnd' (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
      (fun a ha b hb => h2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)), ?_⟩
    intro v hv w hw hvw
    subst hvw
    obtain ⟨z, hz, hvz⟩ := List.mem_flatMap.1 hw
    exact h2 y List.mem_cons_self z (List.mem_cons_of_mem _ hz) (fun he => hy (he ▸ hz)) v hv hvz

namespace Base

variable (S : Base f g s)
include S

theorem gblocks : g.blocks = f.blocks := S.rel.parts.2.2.2.2.2.1

theorem armShape {a : ID} (ha : s.arm0 = some a ∨ s.arm1 = some a) :
    ∃ A k j, f.block? a = some A ∧ A.preds = #[⟨s.dom, k⟩] ∧ A.succs = #[⟨s.post, j⟩] ∧
      a ≠ s.post ∧ a ≠ s.dom ∧ a ∈ f.blocks := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
  rcases ha with ha | ha
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h, -⟩ | ⟨a', A, ha', -, hIn, hA, -, hpr, hsu, hap, had⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'; exact ⟨A, 0, s.j0, hA, hpr, hsu, hap, had, hIn⟩
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h, -⟩ | ⟨a', A, ha', -, hIn, hA, -, hpr, hsu, hap, had⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'; exact ⟨A, 1, s.j1, hA, hpr, hsu, hap, had, hIn⟩

theorem post_ne_dom : s.post ≠ s.dom := by
  obtain ⟨-, -, -, -, -, -, -, h, -⟩ := S.diamond; exact h

theorem dom_not_dead : ¬ Dead s s.dom := by
  rintro (h | h | h)
  · exact S.post_ne_dom h.symm
  · obtain ⟨-, -, -, -, -, -, -, had, -⟩ := S.armShape (.inl h); exact had rfl
  · obtain ⟨-, -, -, -, -, -, -, had, -⟩ := S.armShape (.inr h); exact had rfl

theorem post_not_armB : s.arm0 ≠ some s.post ∧ s.arm1 ≠ some s.post :=
  ⟨fun h => by obtain ⟨-, -, -, -, -, -, hap, -⟩ := S.armShape (.inl h); exact hap rfl,
    fun h => by obtain ⟨-, -, -, -, -, -, hap, -⟩ := S.armShape (.inr h); exact hap rfl⟩

theorem entry_alive : ¬ Dead s f.entry := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, hB, -⟩ := hwf.blockId _ hwf.entry
  have h0 := hwf.entryPreds B hB
  rintro (h | h | h)
  · obtain ⟨P, hP, hsz, -⟩ := S.rel.shape
    rw [← h, hB] at hP; cases hP; omega
  · obtain ⟨A, k, j, hA, hpr, -⟩ := S.armShape (.inl h)
    rw [hB] at hA; cases hA; rw [hpr] at h0; simp at h0
  · obtain ⟨A, k, j, hA, hpr, -⟩ := S.armShape (.inr h)
    rw [hB] at hA; cases hA; rw [hpr] at h0; simp at h0

/-- `dom`'s successors in `f` are the arms or `post`. -/
theorem dom_succ_dead {D : Block} (hD : f.block? s.dom = some D) {e : Edge} (he : e ∈ D.succs) :
    Dead s e.b := by
  obtain ⟨D', e0, e1, hD', -, -, hs, -, h0, h1⟩ := S.diamond
  rw [hD] at hD'; cases hD'
  rw [hs] at he
  simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨-, rfl⟩ | ⟨a, A, ha, rfl, -⟩
    · exact .inl rfl
    · exact .inr (.inl ha)
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨-, rfl⟩ | ⟨a, A, ha, rfl, -⟩
    · exact .inl rfl
    · exact .inr (.inr ha)

/-- A listed block other than `dom` and the emptied ones: `f`'s block with its predecessor
edges from `post` now from `dom`. -/
theorem galive {b : ID} (hb : b ∈ f.blocks) (hbd : b ≠ s.dom) (hnd : ¬ Dead s b) :
    ∃ B B', f.block? b = some B ∧ g.block? b = some B' ∧ B'.id = B.id ∧ B'.values = B.values ∧
      B'.kind = B.kind ∧ B'.controls = B.controls ∧ B'.succs = B.succs ∧
      B'.preds = B.preds.map s.redir := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hr : s.regionBlock b = false := Bool.eq_false_iff.2 fun h => by
    rcases regionBlock_dead.1 h with h | h
    · exact hbd h
    · exact hnd h
  obtain ⟨B, hB, -⟩ := hwf.blockId b hb
  cases hc : s.changed f b with
  | false =>
    refine ⟨B, B, hB, by rw [S.rel.blkEq hc, hB], rfl, rfl, rfl, rfl, rfl, ?_⟩
    refine (map_redir_self fun e he hep => ?_).symm
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, p, hp, hps⟩ := hwf.predLink b B ⟨hb, hB⟩ i e hi
    rw [hep] at hp
    have : (s.tgts f).contains b = true := by
      unfold Site.tgts
      rw [hp]
      exact Array.contains_iff_mem.2 (Array.mem_map.2 ⟨⟨b, i⟩, Array.mem_of_getElem? hps, rfl⟩)
    unfold Site.changed at hc
    rw [this, Bool.or_true] at hc
    cases hc
  | true =>
    have ht : b ∈ s.tgts f := by
      unfold Site.changed at hc
      rw [hr, Bool.false_or] at hc
      exact Array.contains_iff_mem.1 hc
    obtain ⟨-, T, T', hT, hT', he⟩ := S.rel.target ht hbd
    rw [hB] at hT; cases hT
    refine ⟨B, T', hB, hT', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [he]

/-- A listed block that is not emptied: its predecessor edges from `post` now from `dom`. -/
theorem gpreds {b : ID} (hb : b ∈ f.blocks) (hnd : ¬ Dead s b) :
    ∃ B B', f.block? b = some B ∧ g.block? b = some B' ∧ B'.preds = B.preds.map s.redir := by
  by_cases hbd : b = s.dom
  · subst hbd
    obtain ⟨D, P, D', hD, -, hD', -, -, -, -, hpr, -⟩ := merged_exact S.rel
    exact ⟨D, D', hD, hD', hpr⟩
  · obtain ⟨B, B', hB, hB', -, -, -, -, -, hpr⟩ := S.galive hb hbd hnd
    exact ⟨B, B', hB, hB', hpr⟩

/-- An edge of `g` out of a block other than `dom` is an edge of `f`. -/
theorem gstep {p : ID} {blk : Block} (hg : g.block? p = some blk) (hpd : p ≠ s.dom) {e : Edge}
    (he : e ∈ blk.succs) : ∃ B, f.block? p = some B ∧ e ∈ B.succs := by
  cases hc : s.changed f p with
  | false => rw [S.rel.blkEq hc] at hg; exact ⟨blk, hg, he⟩
  | true =>
    by_cases hr : s.regionBlock p = true
    · have hd : Dead s p := (regionBlock_dead.1 hr).resolve_left hpd
      obtain ⟨B', hB', -, -, -, hsu, -⟩ := S.rel.dead hd
      rw [hB'] at hg; cases hg
      rw [hsu] at he; simp at he
    · have ht : p ∈ s.tgts f := by
        unfold Site.changed at hc
        rw [Bool.eq_false_iff.2 hr, Bool.false_or] at hc
        exact Array.contains_iff_mem.1 hc
      obtain ⟨-, T, T', hT, hT', heq⟩ := S.rel.target ht hpd
      rw [hT'] at hg; cases hg
      refine ⟨T, hT, ?_⟩
      rw [heq] at he; exact he

/-- A value listed in `f`: unchanged in id, in `dom` if its block was the diamond's, else in
the same block. -/
theorem gvalue {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B) {x : ID}
    (hx : x ∈ B.values) : ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ fv.id = x ∧
      fv.block = b ∧ gv.id = x ∧ gv.block = (if s.regionBlock b then s.dom else b) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨fv, hfv, hid, hblk⟩ := hwf.valueId b B ⟨hb, hB⟩ x hx
  have hvok := value_spec S.rel x
  have hgid : ∀ gv, g.value? x = some gv → gv.id = x := fun gv hgv => by
    unfold Site.valueOK at hvok
    rw [hfv, hgv] at hvok
    simp only [Bool.and_eq_true, beq_iff_eq] at hvok
    rw [hvok.1.1.1.1, hid]
  cases hc : s.changed f b with
  | true =>
    obtain ⟨-, gv, hgv, hgb⟩ :=
      movedOK_spec (S.rel.moved_changed hc (by rw [valsOf_eq hB]; exact hx))
    exact ⟨fv, gv, hfv, hgv, hid, hblk, hgid gv hgv, hgb⟩
  | false =>
    have hr : s.regionBlock b = false := by
      unfold Site.changed at hc; exact (Bool.or_eq_false_iff.1 hc).1
    rw [if_neg (by simp [hr])]
    by_cases hxc : x = s.c
    · subst hxc
      obtain ⟨-, gv, hgv, hgb⟩ := movedOK_spec S.rel.moved_c
      rw [hfv] at hgb
      exact ⟨fv, gv, hfv, hgv, hid, hblk, hgid gv hgv, by rw [hgb]; simp [hblk]⟩
    · have hk : s.skipV f x = false := by
        simp [Site.skipV, hfv, hblk, hc, hxc]
      have := S.rel.valEq hk
      exact ⟨fv, fv, hfv, by rw [this, hfv], hid, hblk, hid, hblk⟩

/-- A value listed in `f` is listed in `g`, in `dom` if its block was the diamond's. -/
theorem listed_g {a : ID} (ha : Listed f a) : Listed g a ∧
    blockOf g a = (if s.regionBlock (blockOf f a) then s.dom else blockOf f a) := by
  obtain ⟨b, B, ⟨hb, hB⟩, hx⟩ := ha
  obtain ⟨fv, gv, hfv, hgv, -, hfb, -, hgb⟩ := S.gvalue hb hB hx
  have hbo : blockOf f a = b := by unfold blockOf; rw [hfv]; simp [hfb]
  have hbg : blockOf g a = gv.block := by unfold blockOf; rw [hgv]; rfl
  refine ⟨?_, by rw [hbg, hgb, hbo]⟩
  by_cases hr : s.regionBlock b = true
  · obtain ⟨D, P, D', hD, hP, hD', -, -, -, -, -, hvs, -⟩ := merged_exact S.rel
    refine ⟨s.dom, D', ⟨by rw [S.gblocks]; exact S.domIn, hD'⟩, ?_⟩
    rw [hvs]
    simp only [Array.mem_append, mem_armVals]
    rcases regionBlock_iff.1 hr with rfl | rfl | h | h
    · rw [hD] at hB; cases hB; exact .inl (.inl (.inl hx))
    · rw [hP] at hB; cases hB; exact .inr hx
    · exact .inl (.inl (.inr (inArm_iff.2 ⟨b, B, h, hB, hx⟩)))
    · exact .inl (.inr (inArm_iff.2 ⟨b, B, h, hB, hx⟩))
  · have hbd : b ≠ s.dom := fun h => hr (regionBlock_dead.2 (.inl h))
    have hnd : ¬ Dead s b := fun h => hr (regionBlock_dead.2 (.inr h))
    obtain ⟨B1, B', hB1, hB', -, hv, -⟩ := S.galive hb hbd hnd
    rw [hB] at hB1; cases hB1
    exact ⟨b, B', ⟨by rw [S.gblocks]; exact hb, hB'⟩, by rw [hv]; exact hx⟩

/-- A value listed in a block of `g` is listed in a block of `f` (the same, or one of the
diamond's for `dom`). -/
theorem gmem {bid : ID} {gb : Block} (hin : BlockIn g bid gb) {x : ID} (hx : x ∈ gb.values) :
    ∃ X XB, BlockIn f X XB ∧ x ∈ XB.values ∧ (if s.regionBlock X then s.dom else X) = bid := by
  obtain ⟨hbm, hgb⟩ := hin
  rw [S.gblocks] at hbm
  by_cases hbd : bid = s.dom
  · subst hbd
    obtain ⟨D, P, D', hD, hP, hD', -, -, -, -, -, hvs, -⟩ := merged_exact S.rel
    rw [hD'] at hgb; cases hgb
    rw [hvs] at hx
    simp only [Array.mem_append, mem_armVals] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact ⟨s.dom, D, ⟨S.domIn, hD⟩, hx, by simp⟩
    · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 hx
      exact ⟨a, A, ⟨S.armIn (.inl ha), hA⟩, hxA,
        by rw [if_pos (regionBlock_iff.2 (.inr (.inr (.inl ha))))]⟩
    · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 hx
      exact ⟨a, A, ⟨S.armIn (.inr ha), hA⟩, hxA,
        by rw [if_pos (regionBlock_iff.2 (.inr (.inr (.inr ha))))]⟩
    · exact ⟨s.post, P, ⟨S.postIn, hP⟩, hx, by rw [if_pos (regionBlock_iff.2 (.inr (.inl rfl)))]⟩
  · by_cases hnd : Dead s bid
    · obtain ⟨B', hB', -, hv, -⟩ := S.rel.dead hnd
      rw [hB'] at hgb; cases hgb
      rw [hv] at hx; simp at hx
    · obtain ⟨B, B', hB, hB', -, hv, -⟩ := S.galive hbm hbd hnd
      rw [hB'] at hgb; cases hgb
      refine ⟨bid, B, ⟨hbm, hB⟩, by rw [← hv]; exact hx, ?_⟩
      rw [if_neg]
      intro h
      rcases regionBlock_dead.1 h with h | h
      · exact hbd h
      · exact hnd h

/-- A value listed in `g`: its source entry, and its entry in `g` unchanged but for `post`'s
`Phi`s, which became `CondSelect`s. -/
theorem gval_cases {bid : ID} {gb : Block} (hin : BlockIn g bid gb) {x : ID} (hx : x ∈ gb.values)
    {gv : Value} (hgv : g.value? x = some gv) :
    ∃ X XB fv, BlockIn f X XB ∧ x ∈ XB.values ∧ f.value? x = some fv ∧
      gv.id = x ∧ gv.block = bid ∧ gv.auxInt = fv.auxInt ∧
      ((X = s.post ∧ fv.op = .Phi ∧ gv.op = .CondSelect ∧
          gv.args = #[fv.args[s.j0]!, fv.args[s.j1]!, s.c]) ∨
        (¬ (X = s.post ∧ fv.op = .Phi) ∧ gv.op = fv.op ∧ gv.args = fv.args)) ∧
      (if s.regionBlock X then s.dom else X) = bid := by
  obtain ⟨X, XB, ⟨hXm, hXB⟩, hxX, hX⟩ := S.gmem hin hx
  obtain ⟨fv, gv', hfv, hgv', -, hfb, hgid, hgb⟩ := S.gvalue hXm hXB hxX
  rw [hgv] at hgv'; cases hgv'
  refine ⟨X, XB, fv, ⟨hXm, hXB⟩, hxX, hfv, hgid, by rw [hgb, hX], ?_⟩
  by_cases hc : X = s.post ∧ fv.op = .Phi
  · obtain ⟨hXp, hph⟩ := hc
    have hp : s.postVal f x = true := postVal_iff.2 ⟨XB, by rw [← hXp]; exact hXB, hxX⟩
    obtain ⟨gv', hgv', -, -, -, hai, hop, hargs⟩ := condSel_of S.rel hfv hp hph
    rw [hgv] at hgv'; cases hgv'
    exact ⟨hai, .inl ⟨hXp, hph, hop, hargs⟩, hX⟩
  · have hnp : ∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi :=
      fun fv' h hp hph => by
        rw [hfv] at h; cases h
        exact hc ⟨S.postVal_block hXm hXB hxX hp, hph⟩
    have hsem := (semEq_of S.rel hnp).1
    rw [hfv, hgv] at hsem
    exact ⟨hsem.2.2.2.1, .inr ⟨hc, hsem.2.1, hsem.2.2.2.2⟩, hX⟩

/-- Arm values are no `Phi`s (they are speculation-safe). -/
theorem arm_not_phi {X : ID} (ha : s.arm0 = some X ∨ s.arm1 = some X) {XB : Block}
    (hXB : f.block? X = some XB) {x : ID} (hx : x ∈ XB.values) {fv : Value}
    (hfv : f.value? x = some fv) : fv.op ≠ .Phi := by
  have harm : s.armVal f x = true := by
    unfold Site.armVal
    rcases ha with ha | ha
    · rw [inArm_iff.2 ⟨X, XB, ha, hXB, hx⟩]; rfl
    · rw [inArm_iff.2 ⟨X, XB, ha, hXB, hx⟩]; simp
  obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel harm
  rw [hfv] at hv; cases hv
  intro h; simp [specSafeOp, h] at hsafe

/-! ## Well-formedness -/

/-- The values of distinct listed blocks, in sequence, are distinct. -/
theorem nodup_vals {ce : CheckEnv} (hwf : WF ce f) {l : List ID} (hl : ∀ y ∈ l, y ∈ f.blocks)
    (hnd : l.Nodup) : (l.flatMap fun y => (valsOf f y).toList).Nodup :=
  nodup_flatMap hnd
    (fun y hy => by
      obtain ⟨B, hB, -⟩ := hwf.blockId y (hl y hy)
      rw [valsOf_eq hB]; exact hwf.valuesNodup y B ⟨hl y hy, hB⟩)
    (fun y hy z hz hne v hv hv' => by
      obtain ⟨B, hB, -⟩ := hwf.blockId y (hl y hy)
      obtain ⟨C, hC, -⟩ := hwf.blockId z (hl z hz)
      rw [valsOf_eq hB, Array.mem_toList_iff] at hv
      rw [valsOf_eq hC, Array.mem_toList_iff] at hv'
      exact hne (hwf.valueOnce y B z C ⟨hl y hy, hB⟩ ⟨hl z hz, hC⟩ v hv hv'))

/-- The diamond's blocks are distinct. -/
theorem blocks_nodup : (s.dom :: (s.arm0.toList ++ (s.arm1.toList ++ [s.post]))).Nodup := by
  obtain ⟨-, -, -, -, -, -, harms, -⟩ := S.rel.shape
  have hpd := S.post_ne_dom
  cases h0 : s.arm0 with
  | none =>
    cases h1 : s.arm1 with
    | none => simp [Ne.symm hpd]
    | some b =>
      obtain ⟨-, -, -, -, -, -, hbp, hbd, -⟩ := S.armShape (.inr h1)
      simp [Ne.symm hpd, Ne.symm hbd, hbp]
  | some a =>
    obtain ⟨-, -, -, -, -, -, hap, had, -⟩ := S.armShape (.inl h0)
    cases h1 : s.arm1 with
    | none => simp [Ne.symm hpd, Ne.symm had, hap]
    | some b =>
      obtain ⟨-, -, -, -, -, -, hbp, hbd, -⟩ := S.armShape (.inr h1)
      have hab := harms a b h0 h1
      simp [Ne.symm hpd, Ne.symm had, Ne.symm hbd, hap, hbp, hab]

theorem merged_nodup {ce : CheckEnv} (hwf : WF ce f) {D P : Block}
    (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P) :
    (D.values ++ Site.armVals f s.arm0 ++ Site.armVals f s.arm1 ++ P.values).toList.Nodup := by
  have hl : ∀ y ∈ (s.dom :: (s.arm0.toList ++ (s.arm1.toList ++ [s.post]))), y ∈ f.blocks := by
    intro y hy
    simp only [List.mem_cons, List.mem_append, Option.mem_toList, List.mem_singleton,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | h | h | rfl
    · exact S.domIn
    · exact S.armIn (.inl h)
    · exact S.armIn (.inr h)
    · exact S.postIn
  have hn := S.nodup_vals hwf hl S.blocks_nodup
  have harm : ∀ a? : Option ID,
      (Site.armVals f a?).toList = a?.toList.flatMap fun y => (valsOf f y).toList := by
    intro a?; cases a? <;> simp [Site.armVals]
  simp only [List.flatMap_cons, List.flatMap_append, ← harm, valsOf_eq hD, valsOf_eq hP,
    List.flatMap_nil, List.append_nil] at hn
  simpa [Array.toList_append, List.append_assoc] using hn

/-- **branchelim keeps well-formedness.** -/
theorem wf_g {ce : CheckEnv} (hwf : WF ce f) : WF ce g := by
  have gvid : ∀ bid b, BlockIn g bid b → ∀ vid ∈ b.values,
      ∃ v, g.value? vid = some v ∧ v.id = vid ∧ v.block = bid := by
    intro bid b hin vid hv
    obtain ⟨X, XB, ⟨hXm, hXB⟩, hxX, hX⟩ := S.gmem hin hv
    obtain ⟨-, gv, -, hgv, -, -, hgid, hgb⟩ := S.gvalue hXm hXB hxX
    exact ⟨gv, hgv, hgid, by rw [hgb, hX]⟩
  refine
    { blockId := ?_, blocksNodup := ?_, valueId := gvid, valuesNodup := ?_, valueOnce := ?_,
      predLink := ?_, succLink := ?_, arity := ?_, phiArity := ?_, boolAux := ?_,
      argListed := ?_, ctrlListed := ?_, entry := ?_, entryPreds := ?_ }
  · intro bid hb
    rw [S.gblocks] at hb
    by_cases hbd : bid = s.dom
    · subst hbd
      obtain ⟨D, P, D', -, -, hD', hid, -⟩ := merged_exact S.rel
      exact ⟨D', hD', hid⟩
    · by_cases hnd : Dead s bid
      · obtain ⟨B', hB', hid, -⟩ := S.rel.dead hnd
        exact ⟨B', hB', hid⟩
      · obtain ⟨B, B', hB, hB', hid, -⟩ := S.galive hb hbd hnd
        obtain ⟨B1, hB1, hid1⟩ := hwf.blockId bid hb
        rw [hB] at hB1; cases hB1
        exact ⟨B', hB', by rw [hid, hid1]⟩
  · rw [S.gblocks]; exact hwf.blocksNodup
  · intro bid b ⟨hbm, hgb⟩
    rw [S.gblocks] at hbm
    by_cases hbd : bid = s.dom
    · subst hbd
      obtain ⟨D, P, D', hD, hP, hD', -, -, -, -, -, hvs, -⟩ := merged_exact S.rel
      rw [hD'] at hgb; cases hgb
      rw [hvs]
      exact S.merged_nodup hwf hD hP
    · by_cases hnd : Dead s bid
      · obtain ⟨B', hB', -, hv, -⟩ := S.rel.dead hnd
        rw [hB'] at hgb; cases hgb
        rw [hv]; exact List.nodup_nil
      · obtain ⟨B, B', hB, hB', -, hv, -⟩ := S.galive hbm hbd hnd
        rw [hB'] at hgb; cases hgb
        rw [hv]; exact hwf.valuesNodup bid B ⟨hbm, hB⟩
  · intro bid1 b1 bid2 b2 h1 h2 vid hv1 hv2
    obtain ⟨v, hv, -, hb1⟩ := gvid bid1 b1 h1 vid hv1
    obtain ⟨v', hv', -, hb2⟩ := gvid bid2 b2 h2 vid hv2
    rw [hv] at hv'; cases hv'
    rw [← hb1, hb2]
  · intro bid b ⟨hbm, hgb⟩ i e he
    rw [S.gblocks] at hbm
    by_cases hnd : Dead s bid
    · obtain ⟨B', hB', -, -, hpr, -⟩ := S.rel.dead hnd
      rw [hB'] at hgb; cases hgb
      rw [hpr] at he; simp at he
    · obtain ⟨B, B', hB, hB', hpr⟩ := S.gpreds hbm hnd
      rw [hB'] at hgb; cases hgb
      rw [hpr] at he
      obtain ⟨e0, he0, rfl⟩ := getElem?_map_redir he
      obtain ⟨hm, p, hp, hps⟩ := hwf.predLink bid B ⟨hbm, hB⟩ i e0 he0
      by_cases hep : e0.b = s.post
      · rw [redir_eq hep]
        obtain ⟨D, P, D', -, hP, hD', -, -, -, hsu, -⟩ := merged_exact S.rel
        rw [hep, hP] at hp; cases hp
        exact ⟨by rw [S.gblocks]; exact S.domIn, D', hD', by rw [hsu]; exact hps⟩
      · rw [redir_ne hep]
        have hpd : e0.b ≠ s.dom := fun h => by
          rw [h] at hp
          exact hnd (S.dom_succ_dead hp (Array.mem_of_getElem? hps))
        have hpnd : ¬ Dead s e0.b := fun h => by
          rcases h with h | h | h
          · exact hep h
          all_goals
            obtain ⟨A, k, j, hA, -, hsu, -⟩ := S.armShape (by first | exact .inl h | exact .inr h)
            rw [hA] at hp; cases hp
            have hm' := Array.mem_of_getElem? hps
            rw [hsu] at hm'
            simp only [List.mem_toArray, List.mem_singleton, Edge.mk.injEq] at hm'
            exact hnd (.inl hm'.1)
        obtain ⟨B1, B1', hB1, hB1', -, -, -, -, hsu1, -⟩ := S.galive hm hpd hpnd
        rw [hp] at hB1; cases hB1
        exact ⟨by rw [S.gblocks]; exact hm, B1', hB1', by rw [hsu1]; exact hps⟩
  · intro bid b ⟨hbm, hgb⟩ j e he
    rw [S.gblocks] at hbm
    have hnext : ∀ (p : ID) (B : Block), p ∈ f.blocks → f.block? p = some B → p ≠ s.dom →
        ¬ Dead s p → B.succs[j]? = some e →
        e.b ∈ g.blocks ∧ ∃ c, g.block? e.b = some c ∧ c.preds[e.i]? = some ⟨p, j⟩ := by
      intro p B hpm hB hpd hpnd hj
      obtain ⟨hm, C, hC, hci⟩ := hwf.succLink p B ⟨hpm, hB⟩ j e hj
      have hn := S.succ_normal hpm hB hpd (fun h => hpnd (.inr (.inl h)))
        (fun h => hpnd (.inr (.inr h))) (Array.mem_of_getElem? hj)
      have hend : ¬ Dead s e.b := fun h => by
        rcases h with h | h | h
        · exact hn.1 h
        · exact hn.2.1 h
        · exact hn.2.2 h
      obtain ⟨C1, C', hC1, hC', hpr⟩ := S.gpreds hm hend
      rw [hC] at hC1; cases hC1
      refine ⟨by rw [S.gblocks]; exact hm, C', hC', ?_⟩
      rw [hpr, Array.getElem?_map, hci]
      simp [redir_ne (show (⟨p, j⟩ : Edge).b ≠ s.post from fun h => hpnd (.inl h))]
    by_cases hbd : bid = s.dom
    · subst hbd
      obtain ⟨D, P, D', hD, hP, hD', -, -, -, hsu, -⟩ := merged_exact S.rel
      rw [hD'] at hgb; cases hgb
      rw [hsu] at he
      obtain ⟨hm, C, hC, hci⟩ := hwf.succLink s.post P ⟨S.postIn, hP⟩ j e he
      have hn := S.succ_normal S.postIn hP S.post_ne_dom S.post_not_armB.1 S.post_not_armB.2
        (Array.mem_of_getElem? he)
      have hend : ¬ Dead s e.b := fun h => by
        rcases h with h | h | h
        · exact hn.1 h
        · exact hn.2.1 h
        · exact hn.2.2 h
      obtain ⟨C1, C', hC1, hC', hpr⟩ := S.gpreds hm hend
      rw [hC] at hC1; cases hC1
      refine ⟨by rw [S.gblocks]; exact hm, C', hC', ?_⟩
      rw [hpr, Array.getElem?_map, hci]
      simp [redir_eq (show (⟨s.post, j⟩ : Edge).b = s.post from rfl)]
    · by_cases hnd : Dead s bid
      · obtain ⟨B', hB', -, -, -, hsu, -⟩ := S.rel.dead hnd
        rw [hB'] at hgb; cases hgb
        rw [hsu] at he; simp at he
      · obtain ⟨B, B', hB, hB', -, -, -, -, hsu, -⟩ := S.galive hbm hbd hnd
        rw [hB'] at hgb; cases hgb
        rw [hsu] at he
        exact hnext bid B hbm hB hbd hnd he
  · intro bid b vid v ⟨hin, hvb, hgv⟩ hlen
    obtain ⟨X, XB, fv, hXin, hxX, hfv, -, -, -, hc, -⟩ := S.gval_cases hin hvb hgv
    rcases hc with ⟨-, -, hop, hargs⟩ | ⟨-, hop, hargs⟩
    · rw [hargs, hop]; rfl
    · rw [hargs, hop]
      exact hwf.arity X XB vid fv ⟨hXin, hxX, hfv⟩ (hop ▸ hlen)
  · intro bid b vid v ⟨hin, hvb, hgv⟩ hph
    obtain ⟨X, XB, fv, ⟨hXm, hXB⟩, hxX, hfv, -, -, -, hc, hX⟩ := S.gval_cases hin hvb hgv
    rcases hc with ⟨-, -, hop, -⟩ | ⟨hnot, hop, hargs⟩
    · rw [hop] at hph; cases hph
    · rw [hargs]
      have hfph : fv.op = .Phi := hop ▸ hph
      have hfa := hwf.phiArity X XB vid fv ⟨⟨hXm, hXB⟩, hxX, hfv⟩ hfph
      obtain ⟨hbm, hgb⟩ := hin
      by_cases hXd : X = s.dom
      · subst hXd
        simp only [ite_self] at hX
        subst hX
        obtain ⟨D, P, D', hD, -, hD', -, -, -, -, hpr, -⟩ := merged_exact S.rel
        rw [hD'] at hgb; cases hgb
        rw [hD] at hXB; cases hXB
        rw [hpr, Array.size_map]; exact hfa
      · have hnd : ¬ Dead s X := by
          rintro (h | h | h)
          · exact hnot ⟨h, hfph⟩
          · exact S.arm_not_phi (.inl h) hXB hxX hfv hfph
          · exact S.arm_not_phi (.inr h) hXB hxX hfv hfph
        rw [if_neg (fun h => (regionBlock_dead.1 h).elim hXd hnd)] at hX
        subst hX
        obtain ⟨B, B', hB, hB', -, -, -, -, -, hpr⟩ := S.galive hXm hXd hnd
        rw [hB'] at hgb; cases hgb
        rw [hB] at hXB; cases hXB
        rw [hpr, Array.size_map]; exact hfa
  · intro bid b vid v ⟨hin, hvb, hgv⟩ hbool
    obtain ⟨X, XB, fv, hXin, hxX, hfv, -, -, hai, hc, -⟩ := S.gval_cases hin hvb hgv
    rcases hc with ⟨-, -, hop, -⟩ | ⟨-, hop, -⟩
    · rw [hop] at hbool; exact absurd hbool (by decide)
    · rw [hai]; exact hwf.boolAux X XB vid fv ⟨hXin, hxX, hfv⟩ (hop ▸ hbool)
  · intro bid b vid v ⟨hin, hvb, hgv⟩ a ha
    obtain ⟨X, XB, fv, hXin, hxX, hfv, -, -, -, hc, -⟩ := S.gval_cases hin hvb hgv
    rcases hc with ⟨hXp, hph, -, hargs⟩ | ⟨-, -, hargs⟩
    · rw [hargs] at ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      subst hXp
      obtain ⟨hsz, -⟩ := (post_spec S.rel hXin.2 vid hxX fv hfv).1 hph
      obtain ⟨-, -, -, -, hj0, hj1, -⟩ := S.rel.shape
      have hm : ∀ j, j < 2 → fv.args[j]! ∈ fv.args := fun j hj => by
        rw [getElem!_pos fv.args j (by omega)]; exact Array.getElem_mem _
      obtain ⟨D, e0, e1, hD, -, hcD, -⟩ := S.diamond
      rcases ha with rfl | rfl | rfl
      · exact (S.listed_g (hwf.argListed _ _ _ _ ⟨hXin, hxX, hfv⟩ _ (hm _ hj0))).1
      · exact (S.listed_g (hwf.argListed _ _ _ _ ⟨hXin, hxX, hfv⟩ _ (hm _ hj1))).1
      · exact (S.listed_g (hwf.ctrlListed s.dom D ⟨S.domIn, hD⟩ s.c (by rw [hcD]; simp))).1
    · rw [hargs] at ha
      exact (S.listed_g (hwf.argListed X XB vid fv ⟨hXin, hxX, hfv⟩ a ha)).1
  · intro bid b ⟨hbm, hgb⟩ c hc
    rw [S.gblocks] at hbm
    by_cases hbd : bid = s.dom
    · subst hbd
      obtain ⟨D, P, D', -, hP, hD', -, -, hctl, -⟩ := merged_exact S.rel
      rw [hD'] at hgb; cases hgb
      rw [hctl] at hc
      exact (S.listed_g (hwf.ctrlListed s.post P ⟨S.postIn, hP⟩ c hc)).1
    · by_cases hnd : Dead s bid
      · obtain ⟨B', hB', -, -, -, -, hctl⟩ := S.rel.dead hnd
        rw [hB'] at hgb; cases hgb
        rw [hctl] at hc; simp at hc
      · obtain ⟨B, B', hB, hB', -, -, -, hctl, -⟩ := S.galive hbm hbd hnd
        rw [hB'] at hgb; cases hgb
        rw [hctl] at hc
        exact (S.listed_g (hwf.ctrlListed bid B ⟨hbm, hB⟩ c hc)).1
  · rw [S.rel.parts.2.2.1, S.gblocks]; exact hwf.entry
  · intro b hb
    rw [S.rel.parts.2.2.1] at hb
    obtain ⟨B, B', hB, hB', hpr⟩ := S.gpreds hwf.entry S.entry_alive
    rw [hB'] at hb; cases hb
    rw [hpr, Array.size_map]; exact hwf.entryPreds B hB

/-! ## Paths and use dominance -/

/-- From a path to `dom`, a path of `f` to `post` through the arm of side 0 (if any). -/
theorem toPost {L : List ID} (h : Reach f s.dom L) :
    Reach f s.post (s.post :: (s.arm0.toList ++ L)) := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, -⟩ := S.diamond
  have he0 : e0 ∈ D.succs := by rw [hs]; simp
  rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨ha, rfl⟩ | ⟨a, A, ha, rfl, -, hA, -, -, hsu, -⟩
  · rw [ha]; exact .step h hD he0
  · rw [ha]
    exact .step (.step h hD he0) hA (e := ⟨s.post, s.j0⟩) (by rw [hsu]; simp)

/-- **A path of `g` expands into a path of `f`** (to `post` for a path to `dom`). -/
theorem reach_back {b : ID} {l : List ID} (h : Reach g b l) :
    Reach f (if b = s.dom then s.post else b) (expandDom s l) := by
  induction h with
  | entry =>
    rw [S.rel.parts.2.2.1]
    by_cases hd : f.entry = s.dom
    · simp only [expandDom, if_pos hd, List.append_nil]
      have h0 : Reach f s.dom [s.dom] := hd ▸ Reach.entry
      exact S.toPost h0
    · simp only [expandDom, if_neg hd, List.append_nil]
      exact .entry
  | @step p l blk e hr hb he ih =>
    have hstep : Reach f e.b (e.b :: expandDom s l) := by
      by_cases hp : p = s.dom
      · rw [if_pos hp] at ih
        obtain ⟨D, P, D', -, hP, hD', -, -, -, hsu, -⟩ := merged_exact S.rel
        rw [hp, hD'] at hb; cases hb
        rw [hsu] at he
        exact .step ih hP he
      · rw [if_neg hp] at ih
        obtain ⟨B, hB, heB⟩ := S.gstep hb hp he
        exact .step ih hB heB
    by_cases hd : e.b = s.dom
    · simp only [expandDom, if_pos hd]
      have h1 : Reach f s.dom (s.dom :: expandDom s l) := by rw [← hd]; exact hstep
      have := S.toPost h1
      rw [show (s.post :: (s.arm0.toList ++ [s.dom])) ++ expandDom s l =
        s.post :: (s.arm0.toList ++ s.dom :: expandDom s l) by simp]
      exact this
    · simp only [expandDom, if_neg hd]
      exact hstep

/-- A path of `g` visits only listed blocks that are not emptied. -/
theorem reach_alive {b : ID} {l : List ID} (h : Reach g b l) :
    ∀ y ∈ l, y ∈ f.blocks ∧ ¬ Dead s y := by
  obtain ⟨ce, hwf⟩ := S.wf
  induction h with
  | entry =>
    intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    rw [S.rel.parts.2.2.1]
    exact ⟨hwf.entry, S.entry_alive⟩
  | @step p l blk e hr hb he ih =>
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · obtain ⟨hpm, hpd⟩ := ih p hr.mem_self
      have key : ∀ (q : ID) (B : Block), q ∈ f.blocks → f.block? q = some B → q ≠ s.dom →
          s.arm0 ≠ some q → s.arm1 ≠ some q → e ∈ B.succs → e.b ∈ f.blocks ∧ ¬ Dead s e.b := by
        intro q B hq hB hqd ha0 ha1 heB
        have hn := S.succ_normal hq hB hqd ha0 ha1 heB
        obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 heB
        refine ⟨(hwf.succLink q B ⟨hq, hB⟩ k e hk).1, fun h => ?_⟩
        rcases h with h | h | h
        · exact hn.1 h
        · exact hn.2.1 h
        · exact hn.2.2 h
      by_cases hp : p = s.dom
      · subst hp
        obtain ⟨D, P, D', -, hP, hD', -, -, -, hsu, -⟩ := merged_exact S.rel
        rw [hD'] at hb; cases hb
        rw [hsu] at he
        exact key s.post P S.postIn hP S.post_ne_dom S.post_not_armB.1 S.post_not_armB.2 he
      · obtain ⟨B, hB, heB⟩ := S.gstep hb hp he
        exact key p B hpm hB hp (fun h => hpd (.inr (.inl h))) (fun h => hpd (.inr (.inr h))) heB
    · exact ih y hy

theorem fpost {l : List ID} (h : Reach g s.dom l) : Reach f s.post (expandDom s l) := by
  have := S.reach_back h
  rwa [if_pos rfl] at this

/-- From a path of `g` to `y`, a path of `f` to `y` covered by it. -/
theorem fpath {y : ID} {l : List ID} (h : Reach g y l) :
    ∃ L, Reach f y L ∧ ∀ z ∈ L, Cov s l z := by
  have hb := S.reach_back h
  by_cases hy : y = s.dom
  · rw [if_pos hy] at hb
    have hdl : s.dom ∈ expandDom s l := mem_expand_self (by rw [← hy]; exact h.mem_self)
    obtain ⟨pre, t, he, ht⟩ := hb.suffix hdl
    refine ⟨t, by rw [hy]; exact ht, fun z hz => mem_expand ?_⟩
    rw [he]; exact List.mem_append_right _ hz
  · rw [if_neg hy] at hb
    exact ⟨_, hb, fun z hz => mem_expand hz⟩

/-- From a path of `g` along a redirected predecessor edge, a path of `f` to its source. -/
theorem fpred {e0 : Edge} {l : List ID} (h : Reach g (s.redir e0).b l) :
    ∃ L, Reach f e0.b L ∧ ∀ z ∈ L, Cov s l z := by
  by_cases hep : e0.b = s.post
  · rw [redir_eq hep] at h
    exact ⟨_, by rw [hep]; exact S.fpost h, fun z hz => mem_expand hz⟩
  · rw [redir_ne hep] at h
    exact S.fpath h

/-- A block covered by a path of `g` holding the definition of a listed value: the value's
block in `g` is on the path. -/
theorem blockOf_mem {l : List ID} (hal : ∀ y ∈ l, y ∈ f.blocks ∧ ¬ Dead s y) {a : ID}
    (ha : Listed f a) (hy : Cov s l (blockOf f a)) : blockOf g a ∈ l := by
  rw [(S.listed_g ha).2]
  split
  · rename_i hr
    rcases hy with hy | ⟨-, hd⟩
    · rcases regionBlock_dead.1 hr with h | h
      · rw [← h]; exact hy
      · exact absurd h (hal _ hy).2
    · exact hd
  · rename_i hr
    rcases hy with hy | ⟨h, -⟩
    · exact hy
    · exact absurd (regionBlock_dead.2 (.inr h)) hr

/-- **branchelim keeps use dominance.** -/
theorem useDom_g (hu : UseDom f) : UseDom g := by
  obtain ⟨ce, hwf⟩ := S.wf
  intro b gblk hbm hgb
  rw [S.gblocks] at hbm
  by_cases hbd : b = s.dom
  · subst hbd
    obtain ⟨D, P, D', hD, hP, hD', -, -, hctl, -, hpr, -⟩ := merged_exact S.rel
    have hgD : D' = gblk := Option.some.inj (hD'.symm.trans hgb)
    subst hgD
    obtain ⟨D2, e0, e1, hD2, -, hcD, hs, -, h0, h1⟩ := S.diamond
    rw [hD] at hD2; cases hD2
    have hin : BlockIn g s.dom D' := ⟨by rw [S.gblocks]; exact S.domIn, hD'⟩
    -- the paths of `f` to the diamond's blocks covered by a path of `g` to `dom`
    have paths : ∀ l, Reach g s.dom l → ∀ X, X = s.dom ∨ Dead s X →
        ∃ L, Reach f X L ∧ ∀ z ∈ L, Cov s l z := by
      intro l hl X hX
      obtain ⟨L, hL, hLc⟩ := S.fpath hl
      rcases hX with rfl | rfl | ha
      · exact ⟨L, hL, hLc⟩
      · exact ⟨_, S.fpost hl, fun z hz => mem_expand hz⟩
      · obtain ⟨A, k, j, hA, hApr, -, -, -, haIn⟩ := S.armShape ha
        obtain ⟨-, p, hp, hps⟩ := hwf.predLink X A ⟨haIn, hA⟩ 0 ⟨s.dom, k⟩ (by rw [hApr]; rfl)
        rw [hD] at hp; cases hp
        refine ⟨X :: L, Reach.step hL hD (Array.mem_of_getElem? hps), fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact .inr ⟨.inr ha, hl.mem_self⟩
        · exact hLc z hz
    -- the block of a merged value in `f`: `dom`, an arm or `post`
    have home : ∀ X, (if s.regionBlock X then s.dom else X) = s.dom → X = s.dom ∨ Dead s X := by
      intro X hX
      split at hX
      · exact regionBlock_dead.1 (by assumption)
      · exact .inl hX
    refine ⟨fun l hl vid hvid gv hgv hnp a ha => ?_, fun l hl x hx => ?_,
      fun vid hvid gv hgv hph i a e l ha he hl => ?_⟩
    · have hal := S.reach_alive hl
      obtain ⟨X, XB, fv, hXin, hxX, hfv, -, -, -, hc, hX⟩ := S.gval_cases hin hvid hgv
      rcases hc with ⟨hXp, hph, -, hargs⟩ | ⟨-, hop, hargs⟩
      · -- a former `Phi` of `post`
        subst hXp
        have hXB := hXin.2
        rw [hP] at hXB; cases hXB
        rw [hargs] at ha
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
        obtain ⟨hsz, -⟩ := (post_spec S.rel hP vid hxX fv hfv).1 hph
        obtain ⟨-, -, -, -, hj0, hj1, -⟩ := S.rel.shape
        have harg : ∀ (k : Nat) (e : Edge) (arm : Option ID) (j : Nat), D.succs[k]? = some e →
            sideOf f s.dom s.post k e = some (arm, j) → (arm = s.arm0 ∨ arm = s.arm1) → j < 2 →
            blockOf g fv.args[j]! ∈ l := by
          intro k e arm j hk hside harm hj
          obtain ⟨p, hp, hpb⟩ := S.post_pred hD hk hside hP
          have hjl : j < fv.args.size := by omega
          have hfa : fv.args[j]? = some fv.args[j]! := by
            rw [getElem!_pos fv.args j hjl, Array.getElem?_eq_getElem hjl]
          have hX : p.b = s.dom ∨ Dead s p.b := by
            rcases hpb with h | h
            · exact .inl h
            · rcases harm with rfl | rfl
              · exact .inr (.inr (.inl h))
              · exact .inr (.inr (.inr h))
          obtain ⟨L', hL', hL'c⟩ := paths l hl p.b hX
          have := (hu s.post P S.postIn hP).2.2 vid hxX fv hfv hph j _ p L' hfa hp hL'
          exact S.blockOf_mem hal
            (hwf.argListed _ _ _ _ ⟨hXin, hxX, hfv⟩ _ (Array.mem_of_getElem? hfa)) (hL'c _ this)
        rcases ha with rfl | rfl | rfl
        · exact harg 0 e0 s.arm0 s.j0 (by rw [hs]; rfl) h0 (.inl rfl) hj0
        · exact harg 1 e1 s.arm1 s.j1 (by rw [hs]; rfl) h1 (.inr rfl) hj1
        · obtain ⟨L, hL, hLc⟩ := paths l hl s.dom (.inl rfl)
          exact S.blockOf_mem hal
            (hwf.ctrlListed s.dom D ⟨S.domIn, hD⟩ s.c (by rw [hcD]; simp))
            (hLc _ ((hu s.dom D S.domIn hD).2.1 L hL s.c (by rw [hcD]; simp)))
      · rw [hargs] at ha
        obtain ⟨L, hL, hLc⟩ := paths l hl X (home X hX)
        exact S.blockOf_mem hal (hwf.argListed _ _ _ _ ⟨hXin, hxX, hfv⟩ a ha)
          (hLc _ ((hu X XB hXin.1 hXin.2).1 L hL vid hxX fv hfv (hop ▸ hnp) a ha))
    · rw [hctl] at hx
      exact S.blockOf_mem (S.reach_alive hl) (hwf.ctrlListed s.post P ⟨S.postIn, hP⟩ x hx)
        (mem_expand ((hu s.post P S.postIn hP).2.1 _ (S.fpost hl) x hx))
    · obtain ⟨X, XB, fv, ⟨hXm, hXB⟩, hxX, hfv, -, -, -, hc, hX⟩ := S.gval_cases hin hvid hgv
      rcases hc with ⟨-, -, hop, -⟩ | ⟨hnot, hop, hargs⟩
      · rw [hop] at hph; cases hph
      have hfph : fv.op = .Phi := hop ▸ hph
      have hXd : X = s.dom := by
        rcases home X hX with h | h | h | h
        · exact h
        · exact absurd ⟨h, hfph⟩ hnot
        · exact absurd hfph (S.arm_not_phi (.inl h) hXB hxX hfv)
        · exact absurd hfph (S.arm_not_phi (.inr h) hXB hxX hfv)
      subst hXd
      rw [hD] at hXB; cases hXB
      rw [hpr] at he
      obtain ⟨e0, he0, rfl⟩ := getElem?_map_redir he
      obtain ⟨L, hL, hLc⟩ := S.fpred hl
      rw [hargs] at ha
      exact S.blockOf_mem (S.reach_alive hl) (hwf.argListed _ _ _ _ ⟨⟨hXm, hD⟩, hxX, hfv⟩ a
        (Array.mem_of_getElem? ha))
        (hLc _ ((hu s.dom D S.domIn hD).2.2 vid hxX fv hfv hfph i a e0 L ha he0 hL))
  · by_cases hnd : Dead s b
    · obtain ⟨B', hB', -, hv, -, -, hctl⟩ := S.rel.dead hnd
      rw [hB'] at hgb; cases hgb
      refine ⟨fun l _ vid hvid => ?_, fun l _ x hx => ?_, fun vid hvid => ?_⟩
      · rw [hv] at hvid; simp at hvid
      · rw [hctl] at hx; simp at hx
      · rw [hv] at hvid; simp at hvid
    · obtain ⟨B, B', hB, hB', -, hv, -, hctl, -, hpr⟩ := S.galive hbm hbd hnd
      rw [hB'] at hgb; cases hgb
      have hsame : ∀ vid ∈ B.values, ∃ fv, f.value? vid = some fv ∧
          ∀ gv, g.value? vid = some gv → gv.op = fv.op ∧ gv.args = fv.args := by
        intro vid hvid
        obtain ⟨fv, hfv, -⟩ := hwf.valueId b B ⟨hbm, hB⟩ vid hvid
        have hnp : ∀ fv', f.value? vid = some fv' → s.postVal f vid = true → fv'.op ≠ .Phi :=
          fun _ _ hp => absurd (S.postVal_block hbm hB hvid hp) (fun h => hnd (.inl h))
        refine ⟨fv, hfv, fun gv hgv => ?_⟩
        have hsem := (semEq_of S.rel hnp).1
        rw [hfv, hgv] at hsem
        exact ⟨hsem.2.1, hsem.2.2.2.2⟩
      refine ⟨fun l hl vid hvid gv hgv hnp a ha => ?_, fun l hl x hx => ?_,
        fun vid hvid gv hgv hph i a e l ha he hl => ?_⟩
      · rw [hv] at hvid
        obtain ⟨fv, hfv, hfg⟩ := hsame vid hvid
        obtain ⟨hop, hargs⟩ := hfg gv hgv
        rw [hargs] at ha
        obtain ⟨L, hL, hLc⟩ := S.fpath hl
        exact S.blockOf_mem (S.reach_alive hl) (hwf.argListed _ _ _ _ ⟨⟨hbm, hB⟩, hvid, hfv⟩ a ha)
          (hLc _ ((hu b B hbm hB).1 L hL vid hvid fv hfv (hop ▸ hnp) a ha))
      · rw [hctl] at hx
        obtain ⟨L, hL, hLc⟩ := S.fpath hl
        exact S.blockOf_mem (S.reach_alive hl) (hwf.ctrlListed b B ⟨hbm, hB⟩ x hx)
          (hLc _ ((hu b B hbm hB).2.1 L hL x hx))
      · rw [hv] at hvid
        obtain ⟨fv, hfv, hfg⟩ := hsame vid hvid
        obtain ⟨hop, hargs⟩ := hfg gv hgv
        rw [hpr] at he
        obtain ⟨e0, he0, rfl⟩ := getElem?_map_redir he
        obtain ⟨L, hL, hLc⟩ := S.fpred hl
        rw [hargs] at ha
        exact S.blockOf_mem (S.reach_alive hl)
          (hwf.argListed _ _ _ _ ⟨⟨hbm, hB⟩, hvid, hfv⟩ a (Array.mem_of_getElem? ha))
          (hLc _ ((hu b B hbm hB).2.2 vid hvid fv hfv (hop ▸ hph) i a e0 L ha he0 hL))

end Base

/-- **The diamond merge keeps well-formedness** (no `check` of the result). -/
theorem DRel.wf_pres {f g : Func} {s : Site} (h : DRel f g s) {ce : CheckEnv} (hwf : WF ce f) :
    WF ce g :=
  Base.wf_g (S := ⟨⟨ce, hwf⟩, h⟩) hwf

/-- **The diamond merge keeps use dominance on paths** (no `check` of the result). -/
theorem DRel.useDom_pres {f g : Func} {s : Site} (h : DRel f g s) {ce : CheckEnv}
    (hwf : WF ce f) (hu : UseDom f) : UseDom g :=
  Base.useDom_g (S := ⟨⟨ce, hwf⟩, h⟩) hu

end GoFV.Proof.BranchElim
