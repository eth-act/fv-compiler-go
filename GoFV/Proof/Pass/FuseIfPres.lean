import GoFV.Proof.Pass.FuseIfSetup
import GoFV.Proof.Pass.FuseCmpRel

/-!
# fuseBlockIf keeps well-formedness and use dominance

`Setup.wg`: the result of a checked `fuseBlockIf` rewrite of a well-formed function is well
formed; `Setup.useDom_g`: its uses are dominated on paths. Neither needs a `check` of the result:
every listed block of `g` is an unlinked arm with nothing left (`gone`) or keeps its values, kind
and controls, with successors renumbered by `rmE` and predecessors by `predsOf` (`block_core`);
every value keeps what is read or is reset to an argument-free `Invalid`, and keeps its block
but for a moved arm value (`blkOK`). Every edge of `g` has the target of an edge of `f`, so a path
of `g` is one of `f` (`reach_f`).
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.IfC GoFV.Proof Dom

variable {ce : CheckEnv} {f g : Func} {s : Site} {R : List ID}

theorem pmap_b {s : Site} {e : Edge} : (s.pmap e).b = e.b := by
  unfold Site.pmap; split
  · rename_i h; simp only [beq_iff_eq] at h; rw [h]
  · rfl

theorem pmap_ne {s : Site} {e : Edge} (h : e.b ≠ s.b) : s.pmap e = e := by
  unfold Site.pmap; split
  · rename_i h'; simp only [beq_iff_eq] at h'; rw [h'] at h; exact absurd rfl h
  · rfl

theorem pmap_b1 {s : Site} : s.pmap ⟨s.b, 1⟩ = ⟨s.b, 0⟩ := by simp [Site.pmap]

theorem pmap_b0 {s : Site} : s.pmap ⟨s.b, 0⟩ = ⟨s.b, 0⟩ := by simp [Site.pmap]

theorem invalid_argLen : Op.Invalid.argLen = 0 := rfl

theorem invalid_auxType : Op.Invalid.auxType ≠ .Bool := by decide

namespace Setup

variable (S : Setup ce f g s R)
include S

/-- An unlinked arm. -/
def Gone (s : Site) (f : Func) (y : ID) : Prop := s.unlinked f = true ∧ s.arm0 = some y

/-- An unlinked arm keeps nothing in `g`. -/
theorem gone {y : ID} (hy : y ∈ f.blocks) (hg : Gone s f y) :
    ∃ Y Y', f.block? y = some Y ∧ g.block? y = some Y' ∧ Y'.id = Y.id ∧ Y'.values = #[] ∧
      Y'.succs = #[] ∧ Y'.preds = #[] ∧ Y'.controls = #[] := by
  have h := S.rel.block y hy
  unfold Site.blockOK at h
  have h0 : (s.unlinked f && s.arm0 == some y) = true := by simp [hg.1, hg.2]
  rw [h0] at h
  simp only [ite_true] at h
  unfold Site.goneOK at h
  split at h
  · rename_i Y Y' hY hY'
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
    exact ⟨Y, Y', hY, hY', h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- The arm a gone block is: side 0's arm, with only `b`'s edge 0 in and `ss` at `j0` out. -/
theorem gone_shape {y : ID} (hg : Gone s f y) :
    s.rmT f = s.ss ∧ s.rmJ f = s.j0 ∧ ∃ A, f.block? y = some A ∧ A.preds = #[⟨s.b, 0⟩] ∧
      A.succs = #[⟨s.ss, s.j0⟩] ∧ y ≠ s.b := by
  obtain ⟨hu, ha⟩ := hg
  have hs := S.rel.side0; rw [ha] at hs
  obtain ⟨he, hab, -, A, hA, -, hAs, -⟩ := arm_spec hs
  have hpr : A.preds = #[⟨s.b, 0⟩] := by
    have := hu; unfold Site.unlinked at this; rw [ha] at this
    simpa [hA] using this
  have hr : s.rmT f = s.ss := by unfold Site.rmT; rw [ha]; simp [hu]
  have hj : s.rmJ f = s.j0 := by unfold Site.rmJ; rw [ha]; simp [hu]
  exact ⟨hr, hj, A, hA, hpr, hAs, fun h => hab (he ▸ h)⟩

/-- `b` is not gone. -/
theorem b_not_gone : ¬ Gone s f s.b := S.not_dead_b

/-- The value `x` listed in block `y` of `f`, in `g`: its ID and block. -/
theorem gval_id {y : ID} {Y : Block} (hy : y ∈ f.blocks) (hY : f.block? y = some Y) {x : ID}
    (hx : x ∈ Y.values) :
    ∃ gv, g.value? x = some gv ∧ gv.id = x ∧ gv.block = if s.moved f x then s.b else y := by
  obtain ⟨fv, hfv, hid, hb⟩ := S.wf.valueId y Y ⟨hy, hY⟩ x hx
  have hlt := lt_of_value? hfv
  have hbk := S.rel.blk x hlt
  unfold Site.blkOK at hbk
  rw [hfv] at hbk
  by_cases hxR : x ∈ R
  · obtain ⟨fv', gv, hfv', hgv, hgid, -⟩ := S.value_R hxR
    rw [hgv] at hbk
    simp only [beq_iff_eq] at hbk
    exact ⟨gv, hgv, hgid, by rw [hbk, hb]⟩
  · obtain ⟨gv, hgv, hgid, -⟩ := S.value_nR hfv hxR
    rw [hgv] at hbk
    simp only [beq_iff_eq] at hbk
    exact ⟨gv, hgv, hgid.trans hid, by rw [hbk, hb]⟩

/-- A value of `y`'s block is moved only if `y` is the gone arm. -/
theorem moved_iff {y : ID} {Y : Block} (hy : y ∈ f.blocks) (hY : f.block? y = some Y) {x : ID}
    (hx : x ∈ Y.values) : s.moved f x = true ↔ Gone s f y := by
  unfold Site.moved
  constructor
  · intro h
    simp only [Bool.and_eq_true, Option.any_eq_true, Array.contains_iff_mem] at h
    obtain ⟨hu, a, ha, hxa⟩ := h
    have := (S.mem_vals_iff hy hY hx (S.arm0_mem ha)).1 hxa
    subst this; exact ⟨hu, ha⟩
  · rintro ⟨hu, ha⟩
    simp [hu, ha, valsOf_eq hY, hx]

/-- The added values of `b`: an unlinked arm's. -/
theorem added {x : ID}
    (hx : x ∈ (if s.unlinked f then (s.arm0.map (valsOf f)).getD #[] else #[])) :
    ∃ a A, Gone s f a ∧ a ∈ f.blocks ∧ f.block? a = some A ∧ x ∈ A.values := by
  split at hx
  · rename_i hu
    cases ha : s.arm0 with
    | none => rw [ha] at hx; simp at hx
    | some a =>
      rw [ha] at hx
      have ham := S.arm0_mem ha
      obtain ⟨A, hA, -⟩ := S.wf.blockId a ham
      exact ⟨a, A, ⟨hu, ha⟩, ham, hA, by simpa [valsOf_eq hA] using hx⟩
  · simp at hx


/-- Every listed block has an entry in `g`. -/
theorem wg_block {y : ID} (hy : y ∈ f.blocks) : ∃ Y', g.block? y = some Y' ∧ True := by
  by_cases hg : Gone s f y
  · obtain ⟨-, Y', -, hY', -⟩ := S.gone hy hg; exact ⟨Y', hY', trivial⟩
  · obtain ⟨-, Y', -, hY', -⟩ := S.block_core hy hg; exact ⟨Y', hY', trivial⟩

theorem gblock {y : ID} (hy : y ∈ f.blocks) {Y' : Block} (hY' : g.block? y = some Y') :
    ∃ Y, f.block? y = some Y ∧ Y'.id = Y.id ∧
      ((Gone s f y ∧ Y'.values = #[] ∧ Y'.succs = #[] ∧ Y'.preds = #[] ∧ Y'.controls = #[]) ∨
       (¬ Gone s f y ∧ Y'.preds = s.predsOf f y Y.preds ∧
        (∀ c ∈ Y'.controls, s.inX f R c = false) ∧
        (y = s.b → Y'.controls = #[] ∧ Y'.succs = #[s.rmE f s.e1] ∧
          Y'.values = Y.values ++
            (if s.unlinked f then (s.arm0.map (valsOf f)).getD #[] else #[])) ∧
        (y ≠ s.b → Y'.values = Y.values ∧ Y'.controls = Y.controls ∧
          Y'.succs = Y.succs.map (s.rmE f)))) := by
  by_cases hg : Gone s f y
  · obtain ⟨Y, Y1, hY, hY1, hid, hv, hs, hp, hc⟩ := S.gone hy hg
    rw [hY'] at hY1; cases hY1
    exact ⟨Y, hY, hid, .inl ⟨hg, hv, hs, hp, hc⟩⟩
  · obtain ⟨Y, Y1, hY, hY1, hid, hpr, hc, -, hb, hnb⟩ := S.block_core hy hg
    rw [hY'] at hY1; cases hY1
    refine ⟨Y, hY, hid, .inr ⟨hg, hpr, hc, fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨-, a, b', c⟩ := hb h; exact ⟨a, b', c⟩
    · obtain ⟨a, -, c, d⟩ := hnb h; exact ⟨a, c, d⟩

/-- The values listed in a block of `g`: the source's, plus an unlinked arm's in `b`. -/
theorem gmem {y : ID} (hy : y ∈ f.blocks) {Y' : Block} (hY' : g.block? y = some Y') {x : ID}
    (hx : x ∈ Y'.values) :
    ∃ Y, f.block? y = some Y ∧ ¬ Gone s f y ∧
      ((x ∈ Y.values ∧ ¬ Gone s f y) ∨
       (y = s.b ∧ ∃ a A, Gone s f a ∧ a ∈ f.blocks ∧ f.block? a = some A ∧ x ∈ A.values)) := by
  obtain ⟨Y, hY, -, h⟩ := S.gblock hy hY'
  rcases h with ⟨-, hv, -⟩ | ⟨hg, -, -, hb, hnb⟩
  · rw [hv] at hx; simp at hx
  · refine ⟨Y, hY, hg, ?_⟩
    by_cases hyb : y = s.b
    · obtain ⟨-, -, hv⟩ := hb hyb
      rw [hv] at hx
      rcases Array.mem_append.1 hx with h | h
      · exact .inl ⟨h, hg⟩
      · exact .inr ⟨hyb, S.added h⟩
    · obtain ⟨hv, -⟩ := hnb hyb
      rw [hv] at hx; exact .inl ⟨hx, hg⟩

/-- **The value table entry** of a value listed in block `y` of `g`: its ID and block, and an
argument-free `Invalid`, or the source value with what is read kept. -/
theorem gvalue {y : ID} (hy : y ∈ f.blocks) {Y' : Block} (hY' : g.block? y = some Y') {x : ID}
    (hx : x ∈ Y'.values) :
    ∃ Y gv, f.block? y = some Y ∧ g.value? x = some gv ∧ gv.id = x ∧ gv.block = y ∧
      ((gv.op = .Invalid ∧ gv.args = #[]) ∨
       (x ∈ Y.values ∧ ∃ fv, f.value? x = some fv ∧ gv.op = fv.op ∧ gv.auxInt = fv.auxInt ∧
         (∀ a ∈ gv.args, s.inX f R a = false) ∧
         (fv.op = .Phi → y = s.rmT f → s.phiRm f fv.args gv.args = true) ∧
         ((fv.op = .Phi → y ≠ s.rmT f) → gv.args = fv.args))) := by
  obtain ⟨Y, hY, hng, h⟩ := S.gmem hy hY' hx
  rcases h with ⟨hxY, -⟩ | ⟨rfl, a, A, hga, ham, hA, hxA⟩
  · obtain ⟨gv, hgv, hgid, hgb⟩ := S.gval_id hy hY hxY
    have hmv : s.moved f x = false := by
      cases h : s.moved f x
      · rfl
      · exact absurd ((S.moved_iff hy hY hxY).1 h) hng
    rw [hmv] at hgb
    simp only [Bool.false_eq_true, ite_false] at hgb
    refine ⟨Y, gv, hY, hgv, hgid, hgb, ?_⟩
    by_cases hxR : x ∈ R
    · obtain ⟨-, gv', -, hgv', -, hop, hargs, -⟩ := S.value_R hxR
      rw [hgv] at hgv'; cases hgv'
      exact .inl ⟨hop, hargs⟩
    · obtain ⟨fv, hfv, -⟩ := S.wf.valueId y Y ⟨hy, hY⟩ x hxY
      obtain ⟨gv', hgv', -, -, -, hai, hop, hX, hrm, heq⟩ := S.value_nR hfv hxR
      rw [hgv] at hgv'; cases hgv'
      have hmem : ∀ {z : ID}, z ∈ f.blocks → (x ∈ valsOf f z ↔ z = y) :=
        fun hz => S.mem_vals_iff hy hY hxY hz
      refine .inr ⟨hxY, fv, hfv, hop, hai, hX, fun hp hr => hrm hp ((hmem S.rmT_mem).2 hr.symm),
        fun hn => heq fun hp hm => hn hp ((hmem S.rmT_mem).1 hm).symm⟩
  · obtain ⟨gv, hgv, hgid, hgb⟩ := S.gval_id ham hA hxA
    rw [show s.moved f x = true from (S.moved_iff ham hA hxA).2 hga] at hgb
    simp only [ite_true] at hgb
    obtain ⟨gv', hgv', -, hop, hargs⟩ :=
      S.arm0_inv hga.1 hga.2 (by rw [valsOf_eq hA]; exact hxA)
    rw [hgv] at hgv'; cases hgv'
    exact ⟨Y, gv, hY, hgv, hgid, hgb, .inl ⟨hop, hargs⟩⟩

theorem blockOf_g {a : ID} (ha : s.moved f a = false) : blockOf g a = blockOf f a := by
  unfold blockOf
  have hsz := S.rel.vsize
  cases hf : f.value? a with
  | none =>
    have : g.value? a = none := by
      rcases Nat.lt_or_ge a f.valueTab.size with hlt | hge
      · have h := S.rel.value a hlt
        unfold Site.valueOK at h
        rw [hf] at h
        cases hg : g.value? a with
        | none => rfl
        | some _ =>
          rw [hg] at h
          simp only [Bool.or_false] at h
          have := S.value_R (by simpa using h)
          obtain ⟨fv, -, hfv, -⟩ := this
          rw [hf] at hfv; cases hfv
      · unfold Func.value?; rw [Array.getElem?_eq_none (by omega)]; rfl
    rw [this]
  | some fv =>
    have hbk := S.rel.blk a (lt_of_value? hf)
    unfold Site.blkOK at hbk
    rw [hf] at hbk
    cases hg : g.value? a with
    | none =>
      have h := S.rel.value a (lt_of_value? hf)
      unfold Site.valueOK at h
      rw [hf, hg] at h
      simp only [Bool.or_false] at h
      obtain ⟨-, gv, -, hgv, -⟩ := S.value_R (by simpa using h)
      rw [hg] at hgv; cases hgv
    | some gv =>
      rw [hg] at hbk
      simp only [ha, Bool.false_eq_true, ite_false, beq_iff_eq] at hbk
      simp [hbk]

theorem not_moved {a : ID} (h : s.inX f R a = false) : s.moved f a = false := by
  cases hm : s.moved f a
  · rfl
  · exfalso
    unfold Site.moved at hm
    simp only [Bool.and_eq_true, Option.any_eq_true, Array.contains_iff_mem] at hm
    obtain ⟨-, x, hx, hax⟩ := hm
    unfold Site.inX Site.armVal at h
    simp [hx, hax] at h

/-- Predecessor `i` of a non-gone block `y` of `g`: `pmap` of predecessor `i0` of `y` in `f`,
never the removed one. -/
theorem gpred {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {i : Nat}
    {e : Edge} (he : (s.predsOf f y Y.preds)[i]? = some e) :
    ∃ i0 e0, Y.preds[i0]? = some e0 ∧ e = s.pmap e0 ∧ (y ≠ s.rmT f ∨ i0 ≠ s.rmJ f) ∧
      tIdx s f y i0 = i := by
  unfold Site.predsOf at he
  rw [Array.getElem?_map] at he
  by_cases hr : y = s.rmT f
  · rw [if_pos (by simpa using hr)] at he
    obtain ⟨C, hC, hsrc⟩ := S.rm_src
    rw [← hr, hY] at hC; cases hC
    have hjl : s.rmJ f < Y.preds.size := by
      rcases hsrc with h | ⟨_, _, _, h⟩
      · exact (Array.getElem?_eq_some_iff.1 h).1
      · exact (Array.getElem?_eq_some_iff.1 h).1
    obtain ⟨n, hn⟩ : ∃ n, Y.preds.size = n + 1 := ⟨Y.preds.size - 1, by omega⟩
    have hlast : s.last f = n := by unfold Site.last; rw [← hr, hY]; simp [hn]
    cases hi : (Cmp.swapRemove Y.preds (s.rmJ f))[i]? with
    | none => rw [hi] at he; cases he
    | some e0 =>
      rw [hi] at he
      simp only [Option.map_some, Option.some.injEq] at he
      obtain ⟨hlt, h1, h2⟩ := FuseCmp.swapRemove_get_inv hn (by omega) hi
      by_cases hij : i = s.rmJ f
      · refine ⟨n, e0, h1 hij, he.symm, .inr (by omega), ?_⟩
        unfold tIdx Site.rmI; rw [if_pos hr, hlast]; simp [hij]
      · refine ⟨i, e0, h2 hij, he.symm, .inr hij, ?_⟩
        unfold tIdx Site.rmI; rw [if_pos hr, hlast]; simp [show i ≠ n by omega]
  · rw [if_neg (by simpa using hr)] at he
    cases hi : Y.preds[i]? with
    | none => rw [hi] at he; cases he
    | some e0 =>
      rw [hi] at he
      simp only [Option.map_some, Option.some.injEq] at he
      exact ⟨i, e0, hi, he.symm, .inl hr, by unfold tIdx; rw [if_neg hr]⟩

/-- Predecessor `i0` (not the removed one) of a non-gone block `y`, in `g`. -/
theorem gpred_at {y : ID} {Y : Block} (hY : f.block? y = some Y) {i0 : Nat} {e0 : Edge}
    (h0 : Y.preds[i0]? = some e0) (hne : y ≠ s.rmT f ∨ i0 ≠ s.rmJ f) :
    (s.predsOf f y Y.preds)[tIdx s f y i0]? = some (s.pmap e0) := by
  unfold Site.predsOf tIdx
  rw [Array.getElem?_map]
  by_cases hr : y = s.rmT f
  · rw [if_pos (by simpa using hr), if_pos hr]
    obtain ⟨C, hC, hsrc⟩ := S.rm_src
    rw [← hr, hY] at hC; cases hC
    have hjl : s.rmJ f < Y.preds.size := by
      rcases hsrc with h | ⟨_, _, _, h⟩
      · exact (Array.getElem?_eq_some_iff.1 h).1
      · exact (Array.getElem?_eq_some_iff.1 h).1
    obtain ⟨n, hn⟩ : ∃ n, Y.preds.size = n + 1 := ⟨Y.preds.size - 1, by omega⟩
    have hlast : s.last f = n := by unfold Site.last; rw [← hr, hY]; simp [hn]
    have hk : i0 ≠ s.rmJ f := hne.resolve_left (fun h => h hr)
    have := FuseCmp.swapRemove_get hn (by omega) hk
    unfold Site.rmI; rw [hlast]
    by_cases hin : i0 = n
    · subst hin
      simp only [beq_self_eq_true, ite_true] at this ⊢; rw [this, h0]; rfl
    · simp only [hin, ite_false, beq_iff_eq] at this ⊢; rw [this, h0]; rfl
  · rw [if_neg (by simpa using hr), if_neg hr, h0]; rfl

/-- `b`'s edge 0 is removed (or enters the gone arm). -/
theorem e0_removed {y : ID} {i0 : Nat} (h : (⟨y, i0⟩ : Edge) = s.e0) :
    Gone s f y ∨ (y = s.rmT f ∧ i0 = s.rmJ f) := by
  have hs0 := S.rel.side0
  unfold Site.rmT Site.rmJ
  cases ha : s.arm0 with
  | none =>
    rw [ha] at hs0
    have he := direct_spec hs0
    rw [he] at h; cases h; exact .inr ⟨rfl, rfl⟩
  | some a =>
    rw [ha] at hs0
    obtain ⟨he, -⟩ := arm_spec hs0
    have hy : y = s.e0.b := by rw [← h]
    have hi : i0 = s.e0.i := by rw [← h]
    simp only
    by_cases hu : s.unlinked f = true
    · exact .inl ⟨hu, by rw [ha, ← he, ← hy]⟩
    · simp only [hu, Bool.false_eq_true, ite_false]
      exact .inr ⟨hy.trans he, hi⟩

/-- **Well-formedness is kept.** -/
theorem wg : WF ce g := by
  have hwf := S.wf
  have hbl := S.rel.blocks
  obtain ⟨B, hB, hBk, hBc, hBs⟩ := S.bB
  -- a listed block of `g` in `f`
  have hblk : ∀ bid b', BlockIn g bid b' → bid ∈ f.blocks := fun bid b' ⟨hm, _⟩ => hbl ▸ hm
  -- values of `g` listed in `g`'s blocks
  have hval : ∀ bid b', BlockIn g bid b' → ∀ vid ∈ b'.values, ∃ v, g.value? vid = some v ∧
      v.id = vid ∧ v.block = bid := fun bid b' ⟨hm, hb'⟩ vid hv => by
    obtain ⟨Y, gv, -, hgv, hid, hgb, -⟩ := S.gvalue (hbl ▸ hm) hb' hv
    exact ⟨gv, hgv, hid, hgb⟩
  -- listed in `f` ⇒ listed in `g`
  have hlisted : ∀ a, Listed f a → Listed g a := fun a ⟨y, Y, ⟨hy, hY⟩, ha⟩ => by
    by_cases hg : Gone s f y
    · obtain ⟨Bg, hBg⟩ : ∃ Bg, g.block? s.b = some Bg := by
        obtain ⟨Bg, hBg, -⟩ := S.wg_block S.rel.bIn
        exact ⟨Bg, hBg⟩
      obtain ⟨B1, hB1, -, h⟩ := S.gblock S.rel.bIn hBg
      rcases h with ⟨hgb, -⟩ | ⟨-, -, -, hb, -⟩
      · exact absurd hgb S.b_not_gone
      · obtain ⟨-, -, hv⟩ := hb rfl
        refine ⟨s.b, Bg, ⟨hbl ▸ S.rel.bIn, hBg⟩, ?_⟩
        rw [hv]
        refine Array.mem_append_right _ ?_
        rw [if_pos hg.1, hg.2]
        simpa [valsOf_eq hY] using ha
    · obtain ⟨Y1, Y', hY1, hY', -, -, -, -, hb, hnb⟩ := S.block_core hy hg
      rw [hY] at hY1; cases hY1
      refine ⟨y, Y', ⟨hbl ▸ hy, hY'⟩, ?_⟩
      by_cases hyb : y = s.b
      · obtain ⟨-, -, -, hv⟩ := hb hyb; rw [hv]; exact Array.mem_append_left _ ha
      · rw [(hnb hyb).1]; exact ha
  exact {
    blockId := fun bid hm => by
      have hm' := hbl ▸ hm
      obtain ⟨Y', hY'⟩ := S.wg_block hm'
      obtain ⟨Y, hY, hid, -⟩ := S.gblock hm' hY'.1
      obtain ⟨Y0, hY0, hid0⟩ := hwf.blockId bid hm'
      rw [hY] at hY0; cases hY0
      exact ⟨Y', hY'.1, hid.trans hid0⟩
    blocksNodup := by rw [hbl]; exact hwf.blocksNodup
    valueId := hval
    valuesNodup := fun bid b' ⟨hm, hb'⟩ => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, hY, -, h⟩ := S.gblock hm' hb'
      rcases h with ⟨-, hv, -⟩ | ⟨hg, -, -, hb, hnb⟩
      · rw [hv]; simp
      · by_cases hyb : bid = s.b
        · obtain ⟨-, -, hv⟩ := hb hyb
          rw [hv, Array.toList_append, List.nodup_append]
          refine ⟨hwf.valuesNodup bid Y ⟨hm', hY⟩, ?_, ?_⟩
          · split
            · cases ha : s.arm0 with
              | none => simp
              | some a =>
                obtain ⟨A, hA, -⟩ := hwf.blockId a (S.arm0_mem ha)
                simpa [valsOf_eq hA] using hwf.valuesNodup a A ⟨S.arm0_mem ha, hA⟩
            · simp
          · intro x hx z hz hxz
            subst hxz
            obtain ⟨a, A, hga, ham, hA, hxA⟩ := S.added (Array.mem_toList_iff.1 hz)
            have := hwf.valueOnce bid Y a A ⟨hm', hY⟩ ⟨ham, hA⟩ x (Array.mem_toList_iff.1 hx) hxA
            subst this
            exact hg hga
        · rw [(hnb hyb).1]; exact hwf.valuesNodup bid Y ⟨hm', hY⟩
    valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid h1 h2 => by
      obtain ⟨v1, hv1, -, hb1'⟩ := hval bid1 b1 hb1 vid h1
      obtain ⟨v2, hv2, -, hb2'⟩ := hval bid2 b2 hb2 vid h2
      rw [hv1] at hv2; cases hv2
      exact hb1'.symm.trans hb2'
    predLink := fun bid b' ⟨hm, hb'⟩ i e he => by
      have hm' := hbl ▸ hm
      rw [hbl]
      obtain ⟨Y, hY, -, h⟩ := S.gblock hm' hb'
      rcases h with ⟨-, -, -, hp, -⟩ | ⟨hg, hp, -, -, -⟩
      · rw [hp] at he; simp at he
      · rw [hp] at he
        obtain ⟨i0, e0, h0, rfl, hne, hti⟩ := S.gpred hm' hY he
        obtain ⟨hem, P, hP, hPs⟩ := hwf.predLink bid Y ⟨hm', hY⟩ i0 e0 h0
        refine ⟨by rw [pmap_b]; exact hem, ?_⟩
        rw [pmap_b]
        obtain ⟨P', hP'⟩ := S.wg_block hem
        obtain ⟨P1, hP1, -, hpp⟩ := S.gblock hem hP'.1
        rw [hP] at hP1; cases hP1
        refine ⟨P', hP'.1, ?_⟩
        rcases hpp with ⟨hge, -⟩ | ⟨hgn, -, -, hpb, hpnb⟩
        · -- the gone arm's only edge is the removed one
          obtain ⟨hr, hj, A, hA, -, hAs, -⟩ := S.gone_shape hge
          rw [hA] at hP; cases hP
          rw [hAs] at hPs
          have hk : e0.i = 0 := by
            rcases Nat.lt_or_ge e0.i 1 with h' | h'
            · omega
            · rw [Array.getElem?_eq_none (by simpa using h')] at hPs; cases hPs
          rw [hk] at hPs
          simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
            Edge.mk.injEq] at hPs
          rcases hne with h | h
          · exact absurd (hr ▸ hPs.1.symm) h
          · exact absurd (hj ▸ hPs.2.symm) h
        · by_cases heb : e0.b = s.b
          · obtain ⟨-, hsu, -⟩ := hpb heb
            rw [heb, hB] at hP; cases hP
            rw [hBs] at hPs
            have hk : e0.i < 2 := by
              have := (Array.getElem?_eq_some_iff.1 hPs).1; simpa using this
            rcases Nat.lt_or_ge e0.i 1 with hk0 | hk1
            · have : e0.i = 0 := by omega
              rw [this] at hPs
              simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at hPs
              rcases S.e0_removed hPs.symm with h | ⟨h1, h2⟩
              · exact absurd h hg
              · rcases hne with h | h
                · exact absurd h1 h
                · exact absurd h2 h
            · have : e0.i = 1 := by omega
              rw [this] at hPs
              simp only [List.getElem?_toArray, List.getElem?_cons_succ,
                List.getElem?_cons_zero, Option.some.injEq] at hPs
              have he0 : e0 = ⟨s.b, 1⟩ := by
                obtain ⟨b0, i1⟩ := e0; simp only at heb this; rw [heb, this]
              rw [he0, pmap_b1, hsu, hPs, rmE_eq]
              simp only [List.getElem?_toArray, List.getElem?_cons_zero, hti]
          · obtain ⟨-, -, hsu⟩ := hpnb heb
            rw [pmap_ne heb, hsu, Array.getElem?_map, hPs]
            simp only [Option.map_some, rmE_eq, hti]
    succLink := fun bid b' ⟨hm, hb'⟩ j e he => by
      have hm' := hbl ▸ hm
      rw [hbl]
      obtain ⟨Y, hY, -, h⟩ := S.gblock hm' hb'
      rcases h with ⟨-, -, hs, -⟩ | ⟨hg, -, -, hb, hnb⟩
      · rw [hs] at he; simp at he
      · -- the source edge of `f`
        obtain ⟨jj, e0, hj0, rfl, hjj⟩ : ∃ jj e0, Y.succs[jj]? = some e0 ∧ e = s.rmE f e0 ∧
            (bid ≠ s.b ∨ jj ≠ 0) ∧ (bid = s.b → j = 0 ∧ jj = 1) ∧ (bid ≠ s.b → jj = j) := by
          by_cases hyb : bid = s.b
          · obtain ⟨-, hsu, -⟩ := hb hyb
            rw [hsu] at he
            have hj : j = 0 := by
              rcases Nat.lt_or_ge j 1 with h' | h'
              · omega
              · rw [Array.getElem?_eq_none (by simpa using h')] at he; cases he
            subst hj
            simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at he
            subst hyb
            rw [hY] at hB; cases hB
            exact ⟨1, s.e1, by rw [hBs]; rfl, he.symm, .inr (by decide), fun _ => ⟨rfl, rfl⟩,
              fun h => absurd rfl h⟩
          · obtain ⟨-, -, hsu⟩ := hnb hyb
            rw [hsu, Array.getElem?_map] at he
            cases h0 : Y.succs[j]? with
            | none => rw [h0] at he; cases he
            | some e0 =>
              rw [h0] at he
              simp only [Option.map_some, Option.some.injEq] at he
              exact ⟨j, e0, h0, he.symm, .inl hyb, fun h => absurd h hyb, fun _ => rfl⟩
        obtain ⟨hne, hng⟩ := S.succ_ok hm' hY hj0 hjj.1 hg
        obtain ⟨hem, C, hC, hCp⟩ := hwf.succLink bid Y ⟨hm', hY⟩ jj e0 hj0
        rw [rmE_eq]
        refine ⟨hem, ?_⟩
        obtain ⟨C', hC'⟩ := S.wg_block hem
        obtain ⟨C1, hC1, -, hcc⟩ := S.gblock hem hC'.1
        rw [hC] at hC1; cases hC1
        refine ⟨C', hC'.1, ?_⟩
        rcases hcc with ⟨hge, -⟩ | ⟨-, hcp, -⟩
        · exact absurd hge hng
        · rw [hcp, S.gpred_at hC hCp hne]
          by_cases hyb : bid = s.b
          · obtain ⟨rfl, rfl⟩ := hjj.2.1 hyb
            rw [hyb, pmap_b1]
          · rw [pmap_ne hyb, hjj.2.2 hyb]
    arity := fun bid b' vid v ⟨⟨hm, hb'⟩, hvm, hv⟩ hlen => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, gv, hY, hgv, -, -, h⟩ := S.gvalue hm' hb' hvm
      rw [hv] at hgv; cases hgv
      rcases h with ⟨hop, hargs⟩ | ⟨hxY, fv, hfv, hop, -, -, -, heq⟩
      · rw [hop, hargs, invalid_argLen]; rfl
      · have hfl : fv.op.argLen ≠ -1 := hop ▸ hlen
        have hnp : fv.op ≠ .Phi := fun h => by rw [h] at hfl; exact hfl rfl
        rw [heq fun h => absurd h hnp, hop]
        exact hwf.arity bid Y vid fv ⟨⟨hm', hY⟩, hxY, hfv⟩ hfl
    phiArity := fun bid b' vid v ⟨⟨hm, hb'⟩, hvm, hv⟩ hph => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, gv, hY, hgv, -, -, h⟩ := S.gvalue hm' hb' hvm
      rw [hv] at hgv; cases hgv
      rcases h with ⟨hop, -⟩ | ⟨hxY, fv, hfv, hop, -, -, hrm, heq⟩
      · rw [hop] at hph; cases hph
      · have hfph : fv.op = .Phi := hop ▸ hph
        have har := hwf.phiArity bid Y vid fv ⟨⟨hm', hY⟩, hxY, hfv⟩ hfph
        obtain ⟨Y1, hY1, -, hcase⟩ := S.gblock hm' hb'
        rw [hY] at hY1; cases hY1
        rcases hcase with ⟨-, hv', -⟩ | ⟨-, hp, -⟩
        · rw [hv'] at hvm; simp at hvm
        · rw [hp]
          unfold Site.predsOf
          rw [Array.size_map]
          by_cases hr : bid = s.rmT f
          · rw [if_pos (by simpa using hr), FuseCmp.swapRemove_size]
            have hph' := hrm hfph hr
            unfold Site.phiRm at hph'
            simp only [Bool.and_eq_true, beq_iff_eq] at hph'
            omega
          · rw [if_neg (by simpa using hr), heq fun _ => hr, har]
    boolAux := fun bid b' vid v ⟨⟨hm, hb'⟩, hvm, hv⟩ haux => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, gv, hY, hgv, -, -, h⟩ := S.gvalue hm' hb' hvm
      rw [hv] at hgv; cases hgv
      rcases h with ⟨hop, -⟩ | ⟨hxY, fv, hfv, hop, hai, -⟩
      · rw [hop] at haux; exact absurd haux invalid_auxType
      · rw [hai]; exact hwf.boolAux bid Y vid fv ⟨⟨hm', hY⟩, hxY, hfv⟩ (hop ▸ haux)
    argListed := fun bid b' vid v ⟨⟨hm, hb'⟩, hvm, hv⟩ a ha => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, gv, hY, hgv, -, -, h⟩ := S.gvalue hm' hb' hvm
      rw [hv] at hgv; cases hgv
      rcases h with ⟨-, hargs⟩ | ⟨hxY, fv, hfv, -, -, -, hrm, heq⟩
      · rw [hargs] at ha; simp at ha
      · refine hlisted a (hwf.argListed bid Y vid fv ⟨⟨hm', hY⟩, hxY, hfv⟩ a ?_)
        by_cases hc : fv.op = .Phi ∧ bid = s.rmT f
        · have hph' := hrm hc.1 hc.2
          unfold Site.phiRm at hph'
          simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
            Bool.or_eq_true] at hph'
          obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
          have hkl : k < v.args.size := (Array.getElem?_eq_some_iff.1 hk).1
          -- the source index of `k`
          have hsrc : ∃ i, i < fv.args.size ∧ i ≠ s.rmJ f ∧ s.rmI f i = k := by
            have hlast : s.last f + 1 = fv.args.size := by
              have har := hwf.phiArity bid Y vid fv ⟨⟨hm', hY⟩, hxY, hfv⟩ hc.1
              unfold Site.last; rw [← hc.2, hY]; simp only [Option.map_some, Option.getD_some]
              have : 0 < Y.preds.size := by omega
              omega
            by_cases hkj : k = s.rmJ f
            · refine ⟨s.last f, by omega, fun h => by omega, ?_⟩
              unfold Site.rmI; simp [hkj]
            · refine ⟨k, by omega, hkj, ?_⟩
              unfold Site.rmI; simp [show k ≠ s.last f by omega]
          obtain ⟨i, hi, hij, rfl⟩ := hsrc
          rcases hph'.2 i hi with h | h
          · exact absurd h hij
          · rw [hk] at h
            exact Array.mem_of_getElem? h.symm
        · rwa [heq fun hp hr => hc ⟨hp, hr⟩] at ha
    ctrlListed := fun bid b' ⟨hm, hb'⟩ c hc => by
      have hm' := hbl ▸ hm
      obtain ⟨Y, hY, -, h⟩ := S.gblock hm' hb'
      rcases h with ⟨-, -, -, -, hcs⟩ | ⟨-, -, -, hb, hnb⟩
      · rw [hcs] at hc; simp at hc
      · by_cases hyb : bid = s.b
        · rw [(hb hyb).1] at hc; simp at hc
        · rw [(hnb hyb).2.1] at hc
          exact hlisted c (hwf.ctrlListed bid Y ⟨hm', hY⟩ c hc)
    entry := by rw [hbl, S.rel.entry]; exact hwf.entry
    entryPreds := fun b' hb' => by
      rw [S.rel.entry] at hb'
      obtain ⟨Y, hY, -, h⟩ := S.gblock hwf.entry hb'
      have he0 := hwf.entryPreds Y hY
      rcases h with ⟨-, -, -, hp, -⟩ | ⟨-, hp, -⟩
      · rw [hp]; rfl
      · rw [hp]
        unfold Site.predsOf
        rw [Array.size_map]
        have hr : f.entry ≠ s.rmT f := fun h => by
          obtain ⟨C, hC, hsrc⟩ := S.rm_src
          rw [← h, hY] at hC; cases hC
          rcases hsrc with h' | ⟨_, _, _, h'⟩
          · have := (Array.getElem?_eq_some_iff.1 h').1; omega
          · have := (Array.getElem?_eq_some_iff.1 h').1; omega
        rw [if_neg (by simpa using hr), he0] }

/-- **A path of `g` is a path of `f`.** -/
theorem reach_f {x : ID} {l : List ID} (hr : Reach g x l) : Reach f x l := by
  induction hr with
  | entry => rw [S.rel.entry]; exact .entry
  | @step p l blk e hr hb he ih =>
    have hpm : p ∈ f.blocks := ih.mem S.wf
    obtain ⟨Y, hY, -, h⟩ := S.gblock hpm hb
    rcases h with ⟨-, -, hs, -⟩ | ⟨-, -, -, hbb, hnb⟩
    · rw [hs] at he; simp at he
    · by_cases hyb : p = s.b
      · obtain ⟨-, hsu, -⟩ := hbb hyb
        rw [hsu] at he
        simp only [List.mem_toArray, List.mem_singleton] at he
        subst he
        obtain ⟨B, hB, -, -, hBs⟩ := S.bB
        rw [hyb] at hY; rw [hY] at hB; cases hB
        have hb' : (s.rmE f s.e1).b = s.e1.b := by rw [rmE_eq]
        rw [hb']
        exact .step ih (hyb ▸ hY) (by rw [hBs]; simp)
      · obtain ⟨-, -, hsu⟩ := hnb hyb
        rw [hsu, Array.mem_map] at he
        obtain ⟨e0, he0, rfl⟩ := he
        have hb' : (s.rmE f e0).b = e0.b := by rw [rmE_eq]
        rw [hb']
        exact .step ih hY he0

/-- **Use dominance is kept.** -/
theorem useDom_g : UseDom g := by
  have hwf := S.wf
  intro bid blk hbm hbb
  rw [S.rel.blocks] at hbm
  obtain ⟨Y, hY, -, h⟩ := S.gblock hbm hbb
  obtain ⟨hu1, hu2, hu3⟩ := S.dom bid Y hbm hY
  refine ⟨fun l hl vid hvid v hv hnp a ha => ?_, fun l hl x hx => ?_,
    fun vid hvid v hv hph i a e l ha he hr => ?_⟩
  · obtain ⟨Y1, gv, hY1, hgv, -, -, hc⟩ := S.gvalue hbm hbb hvid
    rw [hY] at hY1; cases hY1
    rw [hv] at hgv; cases hgv
    rcases hc with ⟨-, hargs⟩ | ⟨hxY, fv, hfv, hop, -, hX, -, heq⟩
    · rw [hargs] at ha; simp at ha
    · have hfnp : fv.op ≠ .Phi := hop ▸ hnp
      rw [S.blockOf_g (S.not_moved (hX a ha))]
      rw [heq fun h => absurd h hfnp] at ha
      exact hu1 l (S.reach_f hl) vid hxY fv hfv hfnp a ha
  · rcases h with ⟨-, -, -, -, hcs⟩ | ⟨-, -, hcX, hb, hnb⟩
    · rw [hcs] at hx; simp at hx
    · by_cases hyb : bid = s.b
      · rw [(hb hyb).1] at hx; simp at hx
      · rw [S.blockOf_g (S.not_moved (hcX x hx))]
        rw [(hnb hyb).2.1] at hx
        exact hu2 l (S.reach_f hl) x hx
  · obtain ⟨Y1, gv, hY1, hgv, -, -, hc⟩ := S.gvalue hbm hbb hvid
    rw [hY] at hY1; cases hY1
    rw [hv] at hgv; cases hgv
    rcases hc with ⟨hop, -⟩ | ⟨hxY, fv, hfv, hop, -, hX, hrm, heq⟩
    · rw [hop] at hph; cases hph
    · have hfph : fv.op = .Phi := hop ▸ hph
      rw [S.blockOf_g (S.not_moved (hX a (Array.mem_of_getElem? ha)))]
      rcases h with ⟨-, -, -, hp, -⟩ | ⟨-, hp, -⟩
      · rw [hp] at he; simp at he
      · rw [hp] at he
        obtain ⟨i0, e0, h0, rfl, hne, hti⟩ := S.gpred hbm hY he
        rw [pmap_b] at hr
        have hfa : fv.args[i0]? = some a := by
          by_cases hr' : bid = s.rmT f
          · have hne' := hne.resolve_left (fun h => h hr')
            unfold tIdx at hti; rw [if_pos hr'] at hti
            cases hf : fv.args[i0]? with
            | none =>
              have hlt := (Array.getElem?_eq_some_iff.1 h0).1
              have har := hwf.phiArity bid Y vid fv ⟨⟨hbm, hY⟩, hxY, hfv⟩ hfph
              have := Array.getElem?_eq_none_iff.1 hf; omega
            | some a' =>
              have h2 := phiRm_spec (hrm hfph hr') hne' hf
              rw [hti, ha] at h2
              rw [h2]
          · unfold tIdx at hti; rw [if_neg hr'] at hti
            rw [heq fun _ => hr', ← hti] at ha; exact ha
        exact hu3 vid hxY fv hfv hfph i0 a e0 l hfa h0 (S.reach_f hr)


theorem two : Two f g := ⟨⟨ce, S.wf⟩, ⟨ce, S.wg⟩, S.rel.ownAux, S.rel.vsize⟩
end Setup

end GoFV.Proof.FuseIf
