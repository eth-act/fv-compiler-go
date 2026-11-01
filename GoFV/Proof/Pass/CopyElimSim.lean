import GoFV.Proof.Pass.CopyElimRel
import GoFV.Proof.Avail
import GoFV.Proof.Sim
import GoFV.Proof.Order

/-!
# copyelim: from the static relation to the refinement

`refines_of_rel`: if input `f` and output `g` both pass `check`, are related by `CopyRel`, and
`f` has no zero-size aggregate values in tree blocks (`EmptyFrag`), every run of `g` from the
entry is the run of `f`: the two runs visit the same blocks with equal frames.

The block step (`enter_ok`, `enter_panic`): the target's `Phi`s read related arguments, which
hold equal registers (lemma (D) of `g` at the predecessor, `ArgRel`); a `Phi` that became a
copy reads a value of a strict dominator, unchanged by the block; every other target value
evaluates, against the source's frame, to the source's register (`copyEq`: in the source frame
a copy of `g` holds its argument's register). A source panic at a root (a call,
`PanicBounds` or a nil `NilCheck`) is reached by the target too: the target evaluates before it
only values the source evaluated before it (`sched_transfer'`, with `CopyElimRank`: the roots
keep their order because their dependencies are kept, #96).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

/-! ## Setup -/

theorem cfgView_blocks {f g : Func} (h : cfgView g = cfgView f) : g.blocks = f.blocks := by
  simpa [cfgView] using congrArg Func.blocks h

theorem cfgView_entry {f g : Func} (h : cfgView g = cfgView f) : g.entry = f.entry := by
  simpa [cfgView] using congrArg Func.entry h

theorem make_eq {f g : Func} (h : cfgView g = cfgView f) : make g = make f := by
  unfold make; rw [h]

theorem cfgView_block {f g : Func} (h : cfgView g = cfgView f) {bid : ID} {fb : Block}
    (hfb : f.block? bid = some fb) :
    ∃ gb, g.block? bid = some gb ∧ gb.id = fb.id ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds := by
  have ht := congrArg (fun v : Func => v.blockTab[bid]?) h
  simp only [cfgView, Array.getElem?_map] at ht
  unfold Func.block? at hfb ⊢
  cases hf : f.blockTab[bid]? with
  | none => rw [hf] at hfb; cases hfb
  | some o =>
    rw [hf] at hfb ht
    simp at hfb; subst hfb
    cases hg : g.blockTab[bid]? with
    | none => rw [hg] at ht; cases ht
    | some og =>
      rw [hg] at ht
      cases og with
      | none => cases ht
      | some gb =>
        simp only [Option.map_some, Option.some.injEq, Block.mk.injEq] at ht
        exact ⟨gb, rfl, ht.1, ht.2.2.2.2.2.2.2.1, ht.2.2.2.2.2.2.2.2.1⟩

/-- The input fragment of copyelim's simulation: no value of a tree block has a zero-size
aggregate type (phielim would turn it into `Empty`). -/
structure EmptyFrag (tabs : Tables) (f : Func) : Prop where
  noEmpty : ∀ bid ∈ f.blocks, ((make f).depthOf bid).isSome → ∀ fb, f.block? bid = some fb →
    ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv → zeroSizeAggregate tabs fv.type ≠ .ok true

/-- `r` is `.ok true`. -/
def isOkTrue : Except String Bool → Bool
  | .ok true => true
  | _ => false

/-- Decides `EmptyFrag`: no tree value has a zero-size aggregate type. -/
def emptyFragB (tabs : Tables) (f : Func) : Bool :=
  f.blocks.all fun bid =>
    !(make f).inTree bid ||
    match f.block? bid with
    | none => true
    | some fb =>
      fb.values.all fun x => match f.value? x with
        | some fv => !isOkTrue (zeroSizeAggregate tabs fv.type)
        | none => true

theorem emptyFrag_of {tabs : Tables} {f : Func} (h : emptyFragB tabs f = true) :
    EmptyFrag tabs f := by
  unfold emptyFragB at h
  rw [Array.all_eq_true'] at h
  refine ⟨fun bid hb ht fb hfb x hx fv hfv hz => ?_⟩
  have h := h bid hb
  simp only [DomCert.Cert.inTree, ht, Bool.not_true, Bool.false_or, hfb,
    Array.all_eq_true'] at h
  have := h x hx
  simp only [hfv, hz, isOkTrue] at this
  cases this

/-- Everything the simulation uses about copyelim's input `f` and output `g`. -/
structure Setup (tabs : Tables) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  cg : CertOK g
  rel : CopyRel tabs f g
  frag : EmptyFrag tabs f

variable {tabs : Tables} {f g : Func}

/-- A block of `f`'s dominator tree. -/
def Tree (f : Func) (b : ID) : Prop := b ∈ f.blocks ∧ ((make f).depthOf b).isSome

namespace Setup

variable (S : Setup tabs f g)
include S

theorem mk_eq : make g = make f := make_eq S.rel.cfg
theorem blocks : g.blocks = f.blocks := cfgView_blocks S.rel.cfg
theorem entry : g.entry = f.entry := cfgView_entry S.rel.cfg
theorem cp : parentsOK (make f) f.entry = true := S.cf.parents

theorem treeG {b : ID} (h : Tree f b) : Tree g b := by
  unfold Tree; rw [S.blocks, S.mk_eq]; exact h

/-- The target block of a tree block. -/
theorem block {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ gb.id = fb.id ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds ∧
      gb.kind = fb.kind ∧ gb.values = fb.values ∧ gb.controls.size = fb.controls.size ∧
      ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
        ∃ c', gb.controls[k]? = some c' ∧ ArgRel g c c' := by
  obtain ⟨gb, hgb, h1, h2, h3⟩ := cfgView_block S.rel.cfg hfb
  obtain ⟨gb', hgb', h4, h5, h6, h7⟩ := S.rel.block b hb.1 hb.2 fb hfb
  rw [hgb] at hgb'; cases hgb'
  exact ⟨gb, hgb, h1, h2, h3, h4, h5, h6, h7⟩

/-- The source and target versions of a value of a tree block. -/
theorem value {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) :
    ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ fv.block = b ∧ fv.id = x ∧
      gv.block = b ∧ gv.type = fv.type ∧ ValRel tabs g fv gv ∧
      zeroSizeAggregate tabs fv.type ≠ .ok true := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨fv, hfv, hid, hblk⟩ := hwf.valueId b fb ⟨hb.1, hfb⟩ x hx
  obtain ⟨gv, hgv, h1, h2, h3⟩ := S.rel.value b hb.1 hb.2 fb hfb x hx fv hfv
  exact ⟨fv, gv, hfv, hgv, hblk, hid, h1.trans hblk, h2, h3,
    S.frag.noEmpty b hb.1 hb.2 fb hfb x hx fv hfv⟩

/-- Target values of tree blocks have their own ID. -/
theorem gid {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) {gv : Value} (hgv : g.value? x = some gv) : gv.id = x := by
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.block hb hfb
  obtain ⟨gv', hgv', hid, -⟩ := hwg.valueId b gb ⟨by rw [S.blocks]; exact hb.1, hgbb⟩ x
    (by rw [hvals]; exact hx)
  rw [hgv] at hgv'; cases hgv'; exact hid

/-- A value used in a tree block is listed in a tree block, the same one in `g`. -/
theorem used {a q : ID} (hl : Listed f a) (ha : Anc (make f) (blockOf f a) q) :
    ∃ b fb, Tree f b ∧ f.block? b = some fb ∧ a ∈ fb.values ∧ blockOf f a = b ∧
      blockOf g a = b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨b, fb, ⟨hbm, hfb⟩, hx⟩ := hl
  obtain ⟨fv, hfv, -, hblk⟩ := hwf.valueId b fb ⟨hbm, hfb⟩ a hx
  have hbo : blockOf f a = b := by unfold blockOf; rw [hfv]; exact hblk
  have hb : Tree f b := ⟨hbm, by rw [← hbo]; exact Anc.left S.cp ha⟩
  obtain ⟨-, gv, -, hgv, -, -, hgb, -⟩ := S.value hb hfb hx
  exact ⟨b, fb, hb, hfb, hx, hbo, by unfold blockOf; rw [hgv]; exact hgb⟩

/-- A value listed in a tree block is placed in `g` there. -/
theorem placedG {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) {gv : Value} (hgv : g.value? x = some gv) :
    Placed g x gv ∧ gv.block = b := by
  obtain ⟨-, gv', -, hgv', -, -, hgb, -⟩ := S.value hb hfb hx
  rw [hgv] at hgv'; cases hgv'
  obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.block hb hfb
  exact ⟨⟨hgv, by rw [hgb, S.blocks]; exact hb.1, gb, by rw [hgb]; exact hgbb,
    by rw [hvals]; exact hx⟩, hgb⟩

/-- The target's shapes agree with the source's on values of tree blocks. -/
theorem tys {b : ID} (hb : Tree f b) {fb : Block} (hfb : f.block? b = some fb) {x : ID}
    (hx : x ∈ fb.values) : (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := by
  obtain ⟨fv, gv, hfv, hgv, -, -, -, hty, -⟩ := S.value hb hfb hx
  rw [tys_of_value hfv, tys_of_value hgv, hty]

theorem params : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem paramTys : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem outs : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem locals : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

/-- A value of `g` used in a tree block is listed in a tree block of `f`, the same one. -/
theorem usedG {a q : ID} (hl : Listed g a) (ha : Anc (make f) (blockOf g a) q) :
    ∃ b fb, Tree f b ∧ f.block? b = some fb ∧ a ∈ fb.values ∧ blockOf g a = b ∧
      blockOf f a = b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨B, gB, ⟨hBm, hgB⟩, hx⟩ := hl
  obtain ⟨gv, hgv, -, hgvb⟩ := hwg.valueId B gB ⟨hBm, hgB⟩ a hx
  have hbo : blockOf g a = B := by unfold blockOf; rw [hgv]; exact hgvb
  have hBf : B ∈ f.blocks := by rw [← S.blocks]; exact hBm
  have hb : Tree f B := ⟨hBf, by rw [← hbo]; exact Anc.left S.cp ha⟩
  obtain ⟨fB, hfB, -⟩ := hwf.blockId B hBf
  obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.block hb hfB
  rw [hgB] at hgbb; cases hgbb
  have hxf : a ∈ fB.values := by rw [← hvals]; exact hx
  obtain ⟨fv, -, hfv, -, hfb, -⟩ := S.value hb hfB hxf
  exact ⟨B, fB, hb, hfB, hxf, hbo, by unfold blockOf; rw [hfv]; exact hfb⟩

/-- In a frame satisfying lemma (D) of `g` at `p`, a value used at `p` and its `ArgRel`-related
target value hold the same register. -/
theorem argEq {env : Env} {fr : Frame} {A : ID → Prop} {q a w : ID}
    (hD : DInv env (Ctx.make tabs g) A fr) (hAa : A (blockOf f a))
    (hT : Typed (Ctx.make tabs g) fr) (hl : Listed f a) (ha : Anc (make f) (blockOf f a) q)
    (hr : ArgRel g a w) : ∃ y, fr.regs[a]? = some (some y) ∧ fr.regs[w]? = some (some y) := by
  obtain ⟨b, fb, hb, hfb, hx, hbo, hbog⟩ := S.used hl ha
  obtain ⟨fv, gv, hfv, hgv, -, -, hgb, -, -, -⟩ := S.value hb hfb hx
  obtain ⟨hpl, -⟩ := S.placedG hb hfb hx hgv
  obtain ⟨y, hy, hev⟩ := hD a gv hpl (by rw [hgb, ← hbo]; exact hAa)
  rcases hr with rfl | ⟨u, hu, hop, hargs⟩
  · exact ⟨y, hy, hy⟩
  · rw [hgv] at hu; cases hu
    obtain ⟨ce, hwg⟩ := S.wg
    have hgid : gv.id = a := by
      obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.block hb hfb
      obtain ⟨gv', hgv', hid, -⟩ := hwg.valueId b gb ⟨by rw [S.blocks]; exact hb.1, hgbb⟩ a
        (by rw [hvals]; exact hx)
      rw [hgv] at hgv'; cases hgv'; exact hid
    obtain ⟨y0, hy0, rfl⟩ := evalValue_copy_inv hop hargs (hev (by rw [hop]; decide))
    obtain ⟨wv, hwv, hsh⟩ := S.rel.copyShape b hb.1 hb.2 fb hfb a hx gv w hgv hop hargs
    have := hT w y0 hy0
    rw [tys_of_value hwv] at this
    try rw [hgid] at hy
    rw [tys_of_value hgv] at hy
    refine ⟨y0, ?_, hy0⟩
    simp only [Option.getD_some] at this
    rw [hy]; simp only [Option.getD_some]; rw [← hsh y0, this]

/-- A `Phi` of a non-entry tree block that became `Copy w` copies a value of a strict
dominator. -/
theorem phiOut {b : ID} (hb : Tree f b) (hne : b ≠ f.entry) {fb : Block}
    (hfb : f.block? b = some fb) {x : ID} (hx : x ∈ fb.values) {fv gv : Value}
    (hfv : f.value? x = some fv) (hgv : g.value? x = some gv) {w : ID} (hphi : fv.op = .Phi)
    (hcopy : gv.op = .Copy) (hargs : gv.args = #[w]) (hrel : ∀ a ∈ fv.args, ArgRel g a w) :
    Anc (make f) (blockOf g w) b ∧ blockOf g w ≠ b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨gb, hgbb, -, -, -, -, hvals, -⟩ := S.block hb hfb
  have hbt := S.treeG hb
  have hU : Anc (make f) (blockOf g w) b := by
    have := uses S.cg hbt.1 hgbb hbt.2 (by rw [hvals]; exact hx) hgv (by rw [hcopy]; decide)
      (a := w) (by rw [hargs]; simp)
    rwa [S.mk_eq] at this
  refine ⟨hU, fun he => ?_⟩
  obtain ⟨e, he', hqt, hnq⟩ := rooted S.cf hb.1 hfb hb.2 hne
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he'
  have hsz := hwf.phiArity b fb x fv ⟨⟨hb.1, hfb⟩, hx, hfv⟩ hphi
  have hklt : k < fv.args.size := by rw [hsz]; exact (Array.getElem?_eq_some_iff.1 hk).1
  have hfa : fv.args[k]? = some fv.args[k] := by simp [hklt]
  have hpu := phiUse S.cf hb.1 hfb hb.2 hx hfv hphi hfa hk hqt
  have hl : Listed f fv.args[k] :=
    hwf.argListed b fb x fv ⟨⟨hb.1, hfb⟩, hx, hfv⟩ _ (Array.mem_of_getElem? hfa)
  obtain ⟨b', fb', hb', hfb', hx', hbo, hbog⟩ := S.used hl hpu
  rcases hrel _ (Array.mem_of_getElem? hfa) with hw | ⟨u, hu, hop, hua⟩
  · rw [← hw, hbog, ← hbo] at he
    exact hnq (he ▸ hpu)
  · obtain ⟨gb', hgbb', -, -, -, -, hvals', -⟩ := S.block hb' hfb'
    have hbt' := S.treeG hb'
    have hU' := uses S.cg hbt'.1 hgbb' hbt'.2 (by rw [hvals']; exact hx') hu
      (by rw [hop]; decide) (a := w) (by rw [hua]; simp)
    rw [S.mk_eq, ← hbog, he] at hU'
    rw [hbo, ← hbog] at hpu
    exact hnq (Anc.trans S.cp hU' hpu)

end Setup

end GoFV.Proof.CopyElim
