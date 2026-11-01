import GoFV.Opt.BranchElimCheck
import GoFV.Proof.Pass.DeadRel
import GoFV.Proof.Speculate
import GoFV.Proof.Agree
import GoFV.Proof.Merge

/-!
# branchelim: what the step checker establishes

`DRel f g s`: `site? f s.dom s.post = some s` and `s.relB f g` (`GoFV.Opt.BranchElimCheck`).
This module unfolds the checker into the facts the simulation uses: the diamond's shape
(`site_spec`, `sideOf_spec`, `post_shape`), the conditions on arm, `dom` and `post` values,
the merged block of `g`, and the unchanged values and blocks.
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof

/-- One checked branchelim rewrite. -/
structure DRel (f g : Func) (s : Site) : Prop where
  site : site? f s.dom s.post = some s
  rel : s.relB f g = true

theorem inArm_iff {f : Func} {a? : Option ID} {x : ID} :
    Site.inArm f a? x = true ↔ ∃ a A, a? = some a ∧ f.block? a = some A ∧ x ∈ A.values := by
  unfold Site.inArm valsOf
  cases a? with
  | none => simp
  | some a =>
    cases h : f.block? a with
    | none => simp [h]
    | some A => simp [h, Array.contains_iff_mem]

theorem postVal_iff {s : Site} {f : Func} {x : ID} :
    s.postVal f x = true ↔ ∃ P, f.block? s.post = some P ∧ x ∈ P.values := by
  unfold Site.postVal valsOf
  cases h : f.block? s.post with
  | none => simp [h]
  | some P => simp [h, Array.contains_iff_mem]

theorem domVal_iff {s : Site} {f : Func} {x : ID} :
    (valsOf f s.dom).contains x = true ↔ ∃ D, f.block? s.dom = some D ∧ x ∈ D.values := by
  unfold valsOf
  cases h : f.block? s.dom with
  | none => simp [h]
  | some D => simp [h, Array.contains_iff_mem]

/-- The site of a diamond. -/
theorem site_spec {f : Func} {dom post : ID} {s : Site} (h : site? f dom post = some s) :
    s.dom = dom ∧ s.post = post ∧ ∃ D e0 e1, f.block? dom = some D ∧ D.kind = .If ∧
      D.controls = #[s.c] ∧ D.succs = #[e0, e1] ∧ post ≠ dom ∧
      sideOf f dom post 0 e0 = some (s.arm0, s.j0) ∧ sideOf f dom post 1 e1 = some (s.arm1, s.j1) := by
  unfold site? at h
  cases hD : f.block? dom with
  | none => rw [hD] at h; cases h
  | some D =>
    rw [hD] at h
    simp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hk, hcs⟩, hss⟩, hpd⟩ := hc
      split at h
      · rename_i a0 j0 a1 j1 h0 h1
        cases h
        have hsucc : D.succs = #[D.succs[0]!, D.succs[1]!] := by
          apply Array.ext
          · simp [hss]
          · intro i h1 h2
            simp only [hss] at h1
            have : i = 0 ∨ i = 1 := by omega
            rcases this with rfl | rfl <;> simp [getElem!_pos, hss]
        have hctl : D.controls = #[D.controls[0]!] := by
          apply Array.ext
          · simp [hcs]
          · intro i h1 h2
            simp only [hcs] at h1
            have : i = 0 := by omega
            subst this; simp [getElem!_pos, hcs]
        exact ⟨rfl, rfl, D, _, _, rfl, hk, hctl, hsucc, hpd, h0, h1⟩
      · cases h
    · cases h

/-- A side of the diamond: the edge enters `post` directly, or a `Plain` arm whose only
predecessor is `dom` along successor `k` and whose only successor is `post`. -/
theorem sideOf_spec {f : Func} {dom post : ID} {k : Nat} {e : Edge} {a? : Option ID} {j : Nat}
    (h : sideOf f dom post k e = some (a?, j)) :
    (a? = none ∧ e = ⟨post, j⟩) ∨
    (∃ a A, a? = some a ∧ e.b = a ∧ f.block? a = some A ∧ A.kind = .Plain ∧
      A.preds = #[⟨dom, k⟩] ∧ A.succs = #[⟨post, j⟩] ∧ a ≠ post ∧ a ≠ dom) := by
  unfold sideOf at h
  split at h
  · rename_i hp
    cases h
    exact .inl ⟨rfl, by cases e; simp_all⟩
  · rename_i hp
    split at h
    · rename_i A hA
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨⟨hk, hpr⟩, hss⟩, hsb⟩, hnd⟩ := hc
        have hs0 : A.succs = #[⟨post, (A.succs[0]?.map (·.i)).getD 0⟩] := by
          have h0 : 0 < A.succs.size := by omega
          apply Array.ext
          · simp [hss]
          · intro i h1 h2
            simp only [hss] at h1
            have : i = 0 := by omega
            subst this
            have hb : A.succs[0].b = post := by
              simpa [Array.getElem?_eq_getElem h0] using hsb
            simp [Array.getElem?_eq_getElem h0, ← hb]
        refine .inr ⟨e.b, A, rfl, rfl, hA, hk, hpr, hs0, by simpa using hp, hnd⟩
      · cases h
    · cases h

section
variable {f g : Func} {s : Site}

/-- The checker's conjuncts. -/
theorem DRel.raw (h : DRel f g s) :
    s.shapeOK f = true ∧ s.dom ∈ f.blocks ∧ g.entry = f.entry ∧ g.ownAux = f.ownAux ∧
    tabEq g.blocks f.blocks (fun _ => false) = true ∧ s.mergedOK f g = true ∧
    Site.deadOK g s.post = true ∧ Site.armDeadOK g s.arm0 = true ∧
    Site.armDeadOK g s.arm1 = true ∧ (∀ t ∈ s.tgts f, s.targetOK f g t = true) ∧
    (∀ x ∈ valsOf f s.post, (f.value? x).any (·.block == s.post) = true) ∧
    (∀ x ∈ valsOf f s.dom, s.movedOK f g s.dom x = true) ∧
    (∀ x ∈ Site.armVals f s.arm0, s.movedOK f g s.dom x = true) ∧
    (∀ x ∈ Site.armVals f s.arm1, s.movedOK f g s.dom x = true) ∧
    (∀ x ∈ valsOf f s.post, s.movedOK f g s.dom x = true) ∧
    (∀ t ∈ s.tgts f, t = s.dom ∨ ∀ x ∈ valsOf f t, s.movedOK f g t x = true) ∧
    s.movedOK f g (((f.value? s.c).map (·.block)).getD 0) s.c = true ∧
    tabEq f.valueTab g.valueTab (s.skipV f) = true ∧
    tabEq f.blockTab g.blockTab (s.changed f) = true := by
  have := h.rel
  simp only [Site.relB, Bool.and_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩,
    h14⟩, h15⟩, h16⟩, h17⟩, h18⟩, h19⟩ := this
  rw [Array.contains_iff_mem] at h2
  rw [beq_iff_eq] at h3 h4
  rw [Array.all_eq_true'] at h10 h11 h12 h13 h14 h15
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, fun t ht => ?_, h17,
    h18, h19⟩
  have := (Array.all_eq_true'.1 h16) t ht
  rw [Bool.or_eq_true, beq_iff_eq, Array.all_eq_true'] at this
  exact this

theorem DRel.parts (h : DRel f g s) :
    s.shapeOK f = true ∧ s.dom ∈ f.blocks ∧ g.entry = f.entry ∧ g.ownAux = f.ownAux ∧
      g.valueTab.size = f.valueTab.size ∧ g.blocks = f.blocks ∧ s.mergedOK f g = true := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -, -, -, -, -, -, -, -, -, -, -, h18, -⟩ := h.raw
  obtain ⟨-, hbl⟩ := tabEq_spec h5
  exact ⟨h1, h2, h3, h4, (tabEq_spec h18).1.symm, Array.ext_getElem? fun i => (hbl i rfl).symm, h6⟩

/-- A value outside the changed blocks (and not `dom`'s control) is unchanged. -/
theorem DRel.valEq (h : DRel f g s) {x : ID} (hx : s.skipV f x = false) :
    g.value? x = f.value? x := by
  obtain ⟨-, hvt⟩ := tabEq_spec h.raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold Func.value?; rw [hvt x hx]

/-- A block other than the diamond's and `post`'s successors is unchanged. -/
theorem DRel.blkEq (h : DRel f g s) {b : ID} (hb : s.changed f b = false) :
    g.block? b = f.block? b := by
  obtain ⟨-, hbt⟩ := tabEq_spec h.raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  unfold Func.block?; rw [hbt b hb]

theorem regionBlock_iff {b : ID} :
    s.regionBlock b = true ↔ b = s.dom ∨ b = s.post ∨ s.arm0 = some b ∨ s.arm1 = some b := by
  unfold Site.regionBlock
  simp only [Bool.or_eq_true, beq_iff_eq, or_assoc]

theorem movedOK_spec {blk x : ID} (h : s.movedOK f g blk x = true) :
    s.valueOK f g x = true ∧ ∃ gv, g.value? x = some gv ∧ gv.block = blk := by
  unfold Site.movedOK at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases hg : g.value? x with
  | none => rw [hg] at h; cases h.2
  | some gv =>
    rw [hg] at h
    exact ⟨gv, rfl, beq_iff_eq.1 (by simpa using h.2)⟩

theorem mem_armVals {a? : Option ID} {x : ID} :
    x ∈ Site.armVals f a? ↔ Site.inArm f a? x = true := by
  cases a? with
  | none => simp [Site.armVals, Site.inArm]
  | some a => simp [Site.armVals, Site.inArm, Array.contains_iff_mem]

/-- A value listed in a changed block is checked on its own (`movedOK`): in `g` it lies in
`dom` if the block is one of the diamond's, else in the same block. -/
theorem DRel.moved_changed (h : DRel f g s) {b x : ID} (hb : s.changed f b = true)
    (hx : x ∈ valsOf f b) : s.movedOK f g (if s.regionBlock b then s.dom else b) x = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, h13, h14, h15, h16, -⟩ := h.raw
  by_cases hr : s.regionBlock b = true
  · rw [if_pos hr]
    rcases regionBlock_iff.1 hr with rfl | rfl | ha | ha
    · exact h12 x hx
    · exact h15 x hx
    · exact h13 x (mem_armVals.2 (by unfold Site.inArm; rw [ha]; simpa [Array.contains_iff_mem]))
    · exact h14 x (mem_armVals.2 (by unfold Site.inArm; rw [ha]; simpa [Array.contains_iff_mem]))
  · rw [if_neg hr]
    unfold Site.changed at hb
    rw [Bool.eq_false_iff.2 hr, Bool.false_or, Array.contains_iff_mem] at hb
    rcases h16 b hb with hd | hall
    · exact absurd (regionBlock_iff.2 (.inl hd)) hr
    · exact hall x hx

/-- `dom`'s control is checked on its own. -/
theorem DRel.moved_c (h : DRel f g s) :
    s.movedOK f g (((f.value? s.c).map (·.block)).getD 0) s.c = true :=
  h.raw.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The values of `post` lie in `post`. -/
theorem DRel.post_block (h : DRel f g s) {x : ID} (hx : x ∈ valsOf f s.post) :
    ∃ v, f.value? x = some v ∧ v.block = s.post := by
  have := h.raw.2.2.2.2.2.2.2.2.2.2.1 x hx
  cases hv : f.value? x with
  | none => rw [hv] at this; cases this
  | some v => rw [hv] at this; exact ⟨v, rfl, beq_iff_eq.1 (by simpa using this)⟩

theorem deadOK_spec {b : ID} (h : Site.deadOK g b = true) :
    ∃ B', g.block? b = some B' ∧ B'.id = b ∧ B'.values = #[] ∧ B'.preds = #[] ∧
      B'.succs = #[] ∧ B'.controls = #[] := by
  unfold Site.deadOK at h
  split at h
  · rename_i B' hB'
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨B', hB', h1, h2, h3, h4, h5⟩
  · cases h

/-- An arm and `post` are emptied in `g`. -/
theorem DRel.dead (h : DRel f g s) {b : ID}
    (hb : b = s.post ∨ s.arm0 = some b ∨ s.arm1 = some b) :
    ∃ B', g.block? b = some B' ∧ B'.id = b ∧ B'.values = #[] ∧ B'.preds = #[] ∧
      B'.succs = #[] ∧ B'.controls = #[] := by
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, -⟩ := h.raw
  rcases hb with rfl | ha | ha
  · exact deadOK_spec h7
  · rw [ha] at h8; exact deadOK_spec (by simpa [Site.armDeadOK] using h8)
  · rw [ha] at h9; exact deadOK_spec (by simpa [Site.armDeadOK] using h9)

/-- A successor of `post` other than `dom`: outside the diamond, unchanged but for its
predecessor edges from `post` (now from `dom`) and its position. -/
theorem DRel.target (h : DRel f g s) {t : ID} (ht : t ∈ s.tgts f) (hd : t ≠ s.dom) :
    s.regionBlock t = false ∧ ∃ T T', f.block? t = some T ∧ g.block? t = some T' ∧
      T' = { T with preds := T.preds.map s.redir, pos := T'.pos } := by
  have h10 := h.raw.2.2.2.2.2.2.2.2.2.1 t ht
  unfold Site.targetOK at h10
  rw [Bool.or_eq_true, beq_iff_eq] at h10
  rcases h10 with h10 | h10
  · exact absurd h10 hd
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h10
  refine ⟨h10.1, ?_⟩
  obtain ⟨-, h10⟩ := h10
  split at h10
  · rename_i T T' hT hT'
    exact ⟨T, T', hT, hT', beq_iff_eq.1 h10⟩
  · cases h10

theorem DRel.shape (h : DRel f g s) :
    ∃ P, f.block? s.post = some P ∧ P.preds.size = 2 ∧ s.j0 ≠ s.j1 ∧ s.j0 < 2 ∧ s.j1 < 2 ∧
      (∀ a b, s.arm0 = some a → s.arm1 = some b → a ≠ b) ∧
      s.armOK f s.arm0 s.arm1 = true ∧ s.armOK f s.arm1 s.arm0 = true ∧ s.usesOK f = true ∧
      s.domOK f = true ∧ s.postOK f = true := by
  have h1 := h.parts.1
  unfold Site.shapeOK at h1
  cases hP : f.block? s.post with
  | none => rw [hP] at h1; cases h1
  | some P =>
    rw [hP] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hj⟩, hj0⟩, hj1⟩, harms⟩, ha0⟩, ha1⟩, hu⟩, hd⟩, hpo⟩ := h1
    refine ⟨P, rfl, hp, hj, hj0, hj1, (fun a b h0 h1 => ?_), ha0, ha1, hu, hd, hpo⟩
    rw [h0, h1] at harms
    simpa using harms

/-- The values of an arm. -/
theorem armOK_spec {own other : Option ID} (h : s.armOK f own other = true) {x : ID}
    (hx : Site.inArm f own x = true) :
    ∃ v, f.value? x = some v ∧ specSafeOp v.op = true ∧
      ∀ a ∈ v.args, s.postVal f a = false ∧ Site.inArm f other a = false := by
  obtain ⟨a, A, rfl, hA, hxA⟩ := inArm_iff.1 hx
  unfold Site.armOK at h
  simp only at h
  rw [valsOf_eq hA] at h
  have := (Array.all_eq_true'.1 h) x hxA
  cases hv : f.value? x with
  | none => rw [hv] at this; cases this
  | some v =>
    rw [hv] at this
    simp only [Bool.and_eq_true, Site.armArgsOK, Array.all_eq_true', Bool.not_eq_true'] at this
    exact ⟨v, rfl, this.1, fun a ha => this.2 a ha⟩

/-- An arm value (either side). -/
theorem armVal_spec (h : DRel f g s) {x : ID} (hx : s.armVal f x = true) :
    ∃ v, f.value? x = some v ∧ specSafeOp v.op = true ∧ ∀ a ∈ v.args, s.postVal f a = false := by
  obtain ⟨-, -, -, -, -, -, -, ha0, ha1, -⟩ := h.shape
  unfold Site.armVal at hx
  rcases Bool.or_eq_true_iff.1 hx with hx | hx
  · obtain ⟨v, hv, hs, ha⟩ := armOK_spec ha0 hx
    exact ⟨v, hv, hs, fun a h => (ha a h).1⟩
  · obtain ⟨v, hv, hs, ha⟩ := armOK_spec ha1 hx
    exact ⟨v, hv, hs, fun a h => (ha a h).1⟩

/-- Uses of arm values. -/
theorem uses_spec (h : DRel f g s) {bid : ID} (hb : bid ∈ f.blocks) {B : Block}
    (hB : f.block? bid = some B) :
    (∀ y ∈ B.values, ∀ yv, f.value? y = some yv → ∀ (k : Nat) a, yv.args[k]? = some a →
      s.useOK f bid yv k a = true) ∧ ∀ c ∈ B.controls, s.armVal f c = false := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hu, -⟩ := h.shape
  unfold Site.usesOK at hu
  have := (Array.all_eq_true'.1 hu) bid hb
  rw [hB] at this
  simp only [Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at this
  refine ⟨fun y hy yv hyv k a hk => ?_, this.2⟩
  have h1 := this.1 y hy
  rw [hyv] at h1
  simp only [List.all_eq_true, List.mem_range] at h1
  have hk' : k < yv.args.size := by
    rcases Nat.lt_or_ge k yv.args.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hk; cases hk
  have := h1 k hk'
  rwa [getElem!_pos yv.args k hk', show yv.args[k] = a from by
    rw [Array.getElem?_eq_getElem hk'] at hk; exact Option.some.inj hk] at this

/-- `dom`'s non-`Phi` values and control read nothing of `post`. -/
theorem dom_spec (h : DRel f g s) {D : Block} (hD : f.block? s.dom = some D) :
    (∀ x ∈ D.values, ∀ v, f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, s.postVal f a = false) ∧
      s.postVal f s.c = false := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hd, -⟩ := h.shape
  unfold Site.domOK at hd
  rw [valsOf_eq hD] at hd
  simp only [Bool.and_eq_true, Array.all_eq_true', Bool.not_eq_true'] at hd
  refine ⟨fun x hx v hv hp a ha => ?_, hd.2⟩
  have := hd.1 x hx
  rw [hv] at this
  simp only [Bool.or_eq_true, beq_iff_eq, hp, false_or, Array.all_eq_true',
    Bool.not_eq_true'] at this
  exact this a ha

/-- `post`'s `Phi`s have two arguments, none of `post`; its other values are no parameter
reads. -/
theorem post_spec (h : DRel f g s) {P : Block} (hP : f.block? s.post = some P) :
    ∀ x ∈ P.values, ∀ v, f.value? x = some v →
      (v.op = .Phi → v.args.size = 2 ∧ ∀ a ∈ v.args, s.postVal f a = false) ∧
      (v.op ≠ .Phi → v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpo⟩ := h.shape
  unfold Site.postOK at hpo
  rw [valsOf_eq hP] at hpo
  intro x hx v hv
  have := (Array.all_eq_true'.1 hpo) x hx
  rw [hv] at this
  simp only at this
  by_cases hp : v.op = .Phi
  · simp only [hp, beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
      Bool.not_eq_true'] at this
    exact ⟨fun _ => this, fun h' => absurd hp h'⟩
  · simp only [show (v.op == .Phi) = false by simpa using hp, Bool.false_eq_true, ite_false,
      Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨fun h' => absurd h' hp, fun _ => this⟩

/-- The merged block of `g`, exactly. -/
theorem merged_exact (h : DRel f g s) :
    ∃ D P D', f.block? s.dom = some D ∧ f.block? s.post = some P ∧ g.block? s.dom = some D' ∧
      D'.id = s.dom ∧ D'.kind = P.kind ∧ D'.controls = P.controls ∧ D'.succs = P.succs ∧
      D'.preds = D.preds.map s.redir ∧
      D'.values = D.values ++ Site.armVals f s.arm0 ++ Site.armVals f s.arm1 ++ P.values ∧
      (schedule g D').isSome ∧ npSeqOK f g D P D' = true := by
  have hm := h.parts.2.2.2.2.2.2
  unfold Site.mergedOK at hm
  cases hD : f.block? s.dom with
  | none => rw [hD] at hm; cases hm
  | some D =>
  cases hP : f.block? s.post with
  | none => rw [hD, hP] at hm; cases hm
  | some P =>
  cases hD' : g.block? s.dom with
  | none => rw [hD, hP, hD'] at hm; cases hm
  | some D' =>
  rw [hD, hP, hD'] at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨hid, hk⟩, hc⟩, hsu⟩, hpr⟩, hvs⟩, hsch⟩, hnp⟩ := hm
  exact ⟨D, P, D', rfl, rfl, rfl, hid, hk, hc, hsu, hpr, hvs, hsch, hnp⟩

/-- The merged block of `g`. -/
theorem merged_spec (h : DRel f g s) :
    ∃ D P D', f.block? s.dom = some D ∧ f.block? s.post = some P ∧ g.block? s.dom = some D' ∧
      D'.id = s.dom ∧ D'.kind = P.kind ∧ D'.controls = P.controls ∧ D'.succs = P.succs ∧
      (∀ x ∈ D'.values, s.regionVal f x = true) ∧ (∀ x ∈ D.values, x ∈ D'.values) ∧
      (∀ x ∈ P.values, x ∈ D'.values) ∧ (∀ x, s.armVal f x = true → x ∈ D'.values) ∧
      (schedule g D').isSome ∧ npSeqOK f g D P D' = true := by
  obtain ⟨D, P, D', hD, hP, hD', hid, hk, hc, hsu, -, hvs, hsch, hnp⟩ := merged_exact h
  refine ⟨D, P, D', hD, hP, hD', hid, hk, hc, hsu, fun x hx => ?_, fun x hx => ?_,
    fun x hx => ?_, fun x hx => ?_, hsch, hnp⟩
  · rw [hvs] at hx
    simp only [Array.mem_append, mem_armVals] at hx
    unfold Site.regionVal Site.armVal
    rcases hx with ((hx | hx) | hx) | hx
    · rw [valsOf_eq hD, Array.contains_iff_mem.2 hx]; rfl
    · simp [hx]
    · simp [hx]
    · simp [postVal_iff.2 ⟨P, hP, hx⟩]
  · rw [hvs]; simp [hx]
  · rw [hvs]; simp [hx]
  · rw [hvs]
    unfold Site.armVal at hx
    simp only [Array.mem_append, mem_armVals]
    rcases Bool.or_eq_true_iff.1 hx with hx | hx
    · exact .inl (.inl (.inr hx))
    · exact .inl (.inr hx)

/-- Every value of `f` and `g`. -/
theorem value_spec (h : DRel f g s) (x : ID) : s.valueOK f g x = true := by
  cases hk : s.skipV f x with
  | true =>
    unfold Site.skipV at hk
    rcases Bool.or_eq_true_iff.1 hk with hc | hk
    · rw [beq_iff_eq] at hc; subst hc; exact (movedOK_spec h.moved_c).1
    · cases hv : f.value? x with
      | none => rw [hv] at hk; cases hk
      | some v =>
        rw [hv, Bool.and_eq_true] at hk
        exact (movedOK_spec (h.moved_changed hk.1 (Array.contains_iff_mem.1 hk.2))).1
  | false =>
    have heq := h.valEq hk
    unfold Site.valueOK
    rw [heq]
    cases hv : f.value? x with
    | none => rfl
    | some fv =>
      have hnp : (s.postVal f x && fv.op == .Phi) = false := by
        cases hp : s.postVal f x with
        | false => rfl
        | true =>
          exfalso
          obtain ⟨P, hP, hxP⟩ := postVal_iff.1 hp
          have hxv : x ∈ valsOf f s.post := by rw [valsOf_eq hP]; exact hxP
          obtain ⟨v, hv', hvb⟩ := h.post_block hxv
          rw [hv] at hv'; cases hv'
          have : s.skipV f x = true := by
            simp [Site.skipV, hv, hvb, Site.changed, Site.regionBlock, hxv]
          rw [hk] at this; cases this
      simp [hnp]

/-- A value other than `post`'s `Phi`s is unchanged in what evaluation reads. -/
theorem semEq_of (h : DRel f g s) {x : ID}
    (hx : ∀ fv, f.value? x = some fv → s.postVal f x = true → fv.op ≠ .Phi) :
    SemEq (f.value? x) (g.value? x) ∧
      ∀ fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.type = fv.type ∧ gv.op = fv.op := by
  have hv := value_spec h x
  unfold Site.valueOK at hv
  cases hf : f.value? x with
  | none =>
    rw [hf] at hv
    cases hg : g.value? x with
    | none => exact ⟨trivial, fun _ h => nomatch h⟩
    | some _ => rw [hg] at hv; cases hv
  | some fv =>
    rw [hf] at hv
    cases hg : g.value? x with
    | none => rw [hg] at hv; cases hv
    | some gv =>
      rw [hg] at hv
      have hnc : (s.postVal f x && fv.op == .Phi) = false := by
        cases hp : s.postVal f x with
        | false => rfl
        | true => simpa using hx fv hf hp
      simp only [hnc, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop, hargs⟩ := hv
      exact ⟨⟨hid, hop, haux, hai, hargs⟩, fun fv' h' => by
        cases h'; exact ⟨gv, rfl, hty, hop⟩⟩

/-- `post`'s `Phi`s became `CondSelect`s. -/
theorem condSel_of (h : DRel f g s) {x : ID} {fv : Value} (hfv : f.value? x = some fv)
    (hp : s.postVal f x = true) (hph : fv.op = .Phi) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.op = .CondSelect ∧
      gv.args = #[fv.args[s.j0]!, fv.args[s.j1]!, s.c] := by
  have hv := value_spec h x
  unfold Site.valueOK at hv
  rw [hfv] at hv
  cases hg : g.value? x with
  | none => rw [hg] at hv; cases hv
  | some gv =>
    rw [hg] at hv
    simp only [hp, hph, beq_self_eq_true, Bool.and_self, ite_true, Bool.and_eq_true,
      beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop, hargs⟩ := hv
    exact ⟨gv, rfl, hid, hty, haux, hai, hop, hargs⟩

/-- A listed block outside the diamond is unchanged in what entering it and its terminator
read. -/
theorem block_spec (h : DRel f g s) {ce : CheckEnv} (hwf : WF ce f) {bid : ID}
    (hb : bid ∈ f.blocks) (hr : s.regionBlock bid = false) :
    ∃ fb gb, f.block? bid = some fb ∧ g.block? bid = some gb ∧ BlockAgree fb gb := by
  obtain ⟨fb, hfb, -⟩ := hwf.blockId bid hb
  cases hc : s.changed f bid with
  | false => exact ⟨fb, fb, hfb, by rw [h.blkEq hc, hfb], ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  | true =>
    have ht : bid ∈ s.tgts f := by
      unfold Site.changed at hc
      rw [hr, Bool.false_or] at hc
      exact Array.contains_iff_mem.1 hc
    have hd : bid ≠ s.dom := fun e => by
      rw [e] at hr; simp [Site.regionBlock] at hr
    obtain ⟨-, T, T', hT, hT', he⟩ := h.target ht hd
    rw [hfb] at hT; cases hT
    refine ⟨fb, T', hfb, hT', ?_⟩
    rw [he]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end

end GoFV.Proof.BranchElim
