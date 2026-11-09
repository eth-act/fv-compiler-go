import GoFV.Opt.Fuse.BranchRedirectCheck
import GoFV.Proof.Pass.FuseCmpRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseBranchRedirect: what the redirect checker establishes

`RRel tabs f g st`: `g` is `f` with one checked redirect at the site `st` (`Redir.relB`). The
lemmas unfold the checker: the shape of `b`, `p` and `child` (`shape`), `b`'s control unread
elsewhere (`unread`), the decision (`decide`), the values (`value`: unchanged in what is read,
except the `Phi`s of `child`, which gain their argument along `b → child`), the touched blocks
(`gblock`: `Site.expect`), the others (`block_same`) and the function's frame.
-/

namespace GoFV.Proof.FuseRedirect

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Redir GoFV.Proof

/-- One checked redirect at site `st`. -/
structure RRel (tabs : Tables) (f g : Func) (st : Site) : Prop where
  rel : relB tabs f g st = true

variable {tabs : Tables} {f g : Func} {st : Site}

/-- The checker's conjuncts. -/
theorem RRel.parts (h : RRel tabs f g st) :
    st.shapeOK f = true ∧ st.unreadOK f = true ∧
      decideOK tabs f st.cp (st.pi == 0) st.ctl (st.out == 0) = true ∧
      st.valTabOK f g = true ∧ (∀ x ∈ [st.b, st.p, st.child, st.q], st.blockOK f g x = true) ∧
      tabEq f.blockTab g.blockTab st.touched = true ∧
      tabEq g.blocks f.blocks (fun _ => false) = true ∧ g.entry = f.entry ∧ g.ownAux = f.ownAux := by
  have hr := h.rel
  unfold relB at hr
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsh, hun⟩, hdec⟩, hval⟩, hblk⟩, htab⟩, hbl⟩, hent⟩, hown⟩ := hr
  exact ⟨hsh, hun, hdec, hval, hblk, htab, hbl, hent, hown⟩

theorem RRel.blocks (h : RRel tabs f g st) : g.blocks = f.blocks := by
  obtain ⟨-, hi⟩ := tabEq_spec h.parts.2.2.2.2.2.2.1
  exact Array.ext_getElem? fun i => (hi i rfl).symm

theorem RRel.entry (h : RRel tabs f g st) : g.entry = f.entry := h.parts.2.2.2.2.2.2.2.1

theorem RRel.ownAux (h : RRel tabs f g st) : g.ownAux = f.ownAux := h.parts.2.2.2.2.2.2.2.2

theorem RRel.decide (h : RRel tabs f g st) :
    decideOK tabs f st.cp (st.pi == 0) st.ctl (st.out == 0) = true := h.parts.2.2.1

/-- An untouched block's table entry is unchanged. -/
theorem RRel.block_same (h : RRel tabs f g st) {x : ID} (hx : st.touched x = false) :
    g.block? x = f.block? x := by
  obtain ⟨-, hi⟩ := tabEq_spec h.parts.2.2.2.2.2.1
  unfold Func.block?; rw [hi x hx]

/-- A touched block's table entry is `expect`ed. -/
theorem RRel.gblock (h : RRel tabs f g st) {x : ID} (hx : x ∈ [st.b, st.p, st.child, st.q]) :
    ∃ X, f.block? x = some X ∧ g.block? x = some (st.expect x X) := by
  have hb := h.parts.2.2.2.2.1 x hx
  unfold Site.blockOK at hb
  split at hb
  · rename_i X X' hX hX'
    simp only [beq_iff_eq] at hb
    exact ⟨X, hX, by rw [hX', hb]⟩
  · cases hb

/-- `b`'s control when it is `b`'s value. -/
theorem ctlOK_spec (h : st.ctlOK f = true) :
    ∃ v, f.value? st.ctl = some v ∧ v.id = st.ctl ∧ RewriteCheck.termOp v.op = true ∧
      st.ctl ∉ v.args := by
  unfold Site.ctlOK at h
  split at h
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
    refine ⟨v, hv, h.1.1, h.1.2, fun hm => ?_⟩
    have h2 := h.2
    rw [Array.contains_iff_mem.2 hm] at h2; cases h2
  · cases h

/-- The shape of `b`, `p` and `child` in `f`. -/
theorem RRel.shape (h : RRel tabs f g st) :
    ∃ B P C, f.block? st.b = some B ∧ f.block? st.p = some P ∧ f.block? st.child = some C ∧
      st.b ∈ f.blocks ∧ st.p ≠ st.b ∧ st.child ≠ st.b ∧ st.child ≠ f.entry ∧ st.out < 2 ∧
      st.k ≤ st.n ∧ B.kind = .If ∧ B.controls = #[st.ctl] ∧ B.succs.size = 2 ∧
      B.succs[st.out]? = some ⟨st.child, st.ai⟩ ∧ B.preds.size = st.n + 1 ∧
      B.preds[st.k]? = some ⟨st.p, st.pi⟩ ∧ B.preds[st.n]?.map (·.b) = some st.q ∧
      P.kind = .If ∧ P.controls = #[st.cp] ∧ C.preds.size = st.cn ∧
      (B.values = #[] ∨ (B.values = #[st.ctl] ∧ st.ctlOK f = true)) := by
  have hs := h.parts.1
  unfold Site.shapeOK at hs
  obtain ⟨B, hB⟩ : ∃ B, f.block? st.b = some B := by
    cases hB : f.block? st.b with
    | none => rw [hB] at hs; cases hs
    | some B => exact ⟨B, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, f.block? st.p = some P := by
    cases hP : f.block? st.p with
    | none => rw [hB, hP] at hs; cases hs
    | some P => exact ⟨P, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, f.block? st.child = some C := by
    cases hC : f.block? st.child with
    | none => rw [hB, hP, hC] at hs; cases hs
    | some C => exact ⟨C, rfl⟩
  rw [hB, hP, hC] at hs
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Array.contains_iff_mem, Bool.or_eq_true, Array.isEmpty_iff, and_assoc] at hs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hs
  exact ⟨B, P, C, hB, hP, hC, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, h16⟩

/-- When `b` holds a value, no listed value reads `ctl` and no other block has it as a
control. -/
theorem RRel.unread (h : RRel tabs f g st) {B : Block} (hB : f.block? st.b = some B)
    (hne : B.values ≠ #[]) {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) :
    (∀ x ∈ Y.values, ∀ v, f.value? x = some v → st.ctl ∉ v.args) ∧
      (y ≠ st.b → st.ctl ∉ Y.controls) := by
  have hu := h.parts.2.1
  unfold Site.unreadOK at hu
  have hv : (valsOf f st.b).isEmpty = false := by
    unfold valsOf; rw [hB]
    simpa [Array.isEmpty_iff] using hne
  rw [hv, Bool.false_or, Array.all_eq_true'] at hu
  have := hu y hy
  rw [hY] at this
  simp only [Bool.and_eq_true, Array.all_eq_true', Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true'] at this
  refine ⟨fun x hx v hfv hm => ?_, fun hyb hm => ?_⟩
  · have h1 := this.1 x hx
    rw [hfv] at h1
    simp only [Option.all_some, Bool.not_eq_true'] at h1
    rw [Array.contains_iff_mem.2 hm] at h1; cases h1
  · rcases this.2 with h2 | h2
    · exact hyb h2
    · rw [Array.contains_iff_mem.2 hm] at h2; cases h2

theorem entryFast_eq {o o' : Option Value} : st.entryFast o o' = st.entryOK o o' := by
  unfold Site.entryFast
  split <;> simp [withPtrEq]

/-- **The values.** Every value keeps what the semantics reads, except the arguments of the
`Phi`s of `child`, which gain their argument along `b → child`. A value missing in `f` is
missing in `g`. -/
theorem RRel.value (h : RRel tabs f g st) (x : ID) :
    (f.value? x = none → g.value? x = none) ∧
    ∀ v, f.value? x = some v → ∃ w, g.value? x = some w ∧ w.id = v.id ∧ w.type = v.type ∧
      w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧ w.block = v.block ∧
      (v.op = .Phi → v.block = st.child →
        st.ai < v.args.size ∧ w.args = v.args.push v.args[st.ai]!) ∧
      (¬ (v.op = .Phi ∧ v.block = st.child) → w.args = v.args) := by
  have hval := h.parts.2.2.2.1
  unfold Site.valTabOK at hval
  rw [Bool.and_eq_true, beq_iff_eq] at hval
  have hE : st.entryOK (f.value? x) (g.value? x) = true := by
    rcases Nat.lt_or_ge x f.valueTab.size with hlt | hge
    · have h' := nat_all_spec hval.2 x hlt
      rw [entryFast_eq, getElem!_pos f.valueTab x hlt,
        getElem!_pos g.valueTab x (hval.1 ▸ hlt)] at h'
      unfold Func.value?
      rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem (hval.1 ▸ hlt)]
      exact h'
    · unfold Func.value?
      rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (by omega)]
      rfl
  unfold Site.entryOK at hE
  refine ⟨fun hf => ?_, fun v hf => ?_⟩
  · rw [hf] at hE
    cases hg : g.value? x with
    | none => rfl
    | some _ => rw [hg] at hE; cases hE
  · rw [hf] at hE
    cases hg : g.value? x with
    | none => rw [hg] at hE; cases hE
    | some w =>
      rw [hg] at hE
      simp only at hE
      split at hE
      · rename_i hph
        simp only [Site.cPhi, Bool.and_eq_true, beq_iff_eq] at hph
        rw [Bool.and_eq_true, decide_eq_true_eq] at hE
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := FuseCmp.sameW_spec hE.2
        exact ⟨w, rfl, h1, h2, h3, h4, h5, h7, fun _ _ => ⟨hE.1, h6⟩,
          fun hn => absurd hph hn⟩
      · rename_i hph
        simp only [Site.cPhi, Bool.and_eq_true, beq_iff_eq] at hph
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := FuseCmp.sameW_spec hE
        exact ⟨w, rfl, h1, h2, h3, h4, h5, h7, fun a b => absurd ⟨a, b⟩ hph, fun _ => h6⟩

theorem RRel.vsize (h : RRel tabs f g st) : g.valueTab.size = f.valueTab.size := by
  have hval := h.parts.2.2.2.1
  unfold Site.valTabOK at hval
  rw [Bool.and_eq_true, beq_iff_eq] at hval
  exact hval.1.symm

end GoFV.Proof.FuseRedirect
