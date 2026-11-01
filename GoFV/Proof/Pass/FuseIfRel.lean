import GoFV.Opt.Fuse.IfCheck
import GoFV.Proof.Checked
import GoFV.Proof.WF

/-!
# fuseBlockIf: what the step checker establishes

`IRel f g s R`: one checked `fuseBlockIf` rewrite at the site `s` with the reset values `R`
(`IfC.Site.relB`, `GoFV.Opt.Fuse.IfCheck`), in declarative form (`relB_sound`). This module
unfolds the checker into the facts the simulation uses: the `If` block and the sides
(`bBlock`, `arm_spec`, `direct_spec`), the `Phi`s of the join block (`phis`), the reset values
(`reset`), the other values (`value`, `blk`) and the blocks of `g` (`block`).
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.IfC GoFV.Proof

/-- One checked `fuseBlockIf` rewrite (see the module doc). -/
structure IRel (f g : Func) (s : Site) (R : List ID) : Prop where
  bIn : s.b ∈ f.blocks
  ssIn : s.ss ∈ f.blocks
  ss_ne_b : s.ss ≠ s.b
  j_ne : s.j0 ≠ s.j1
  bBlock : ∃ B, f.block? s.b = some B ∧ B.kind = .If ∧ B.controls = #[s.c] ∧
    B.succs = #[s.e0, s.e1]
  ssBlock : ∃ P, f.block? s.ss = some P ∧ s.j0 < P.preds.size ∧ s.j1 < P.preds.size
  side0 : s.sideOK f s.arm0 s.e0 s.j0 = true
  side1 : s.sideOK f s.arm1 s.e1 s.j1 = true
  phis : s.phisOK f R = true
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  blocks : g.blocks = f.blocks
  reset : ∀ r ∈ R, Site.resetOK f g r = true
  arm0Inv : s.unlinked f = true → ∀ a, s.arm0 = some a → ∀ x ∈ valsOf f a, Site.invalidIn g x = true
  value : ∀ x, x < f.valueTab.size → s.valueOK f g R x = true
  blk : ∀ x, x < f.valueTab.size → s.blkOK f g x = true
  block : ∀ bid ∈ f.blocks, s.blockOK f g R bid = true

theorem relB_sound {f g : Func} {s : Site} {R : List ID}
    (h : s.relB f g R = true) : IRel f g s R := by
  unfold Site.relB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Option.all_eq_true, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh, hent⟩, hown⟩, hvs⟩, hbl⟩, hres⟩, harm⟩, hval⟩, hbk⟩, hblk⟩ := h
  unfold Site.shapeOK at hsh
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.contains_iff_mem] at hsh
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hb, hss⟩, hne⟩, hj⟩, hB⟩, hP⟩, hs0⟩, hs1⟩, hph⟩ := hsh
  refine ⟨hb, hss, hne, hj, ?_, ?_, hs0, hs1, hph, hent, hown, hvs, hbl, hres,
    fun hu a ha x hx => by
      simp only [hu, Bool.not_true, Bool.false_or, Option.all_eq_true] at harm
      exact (Array.all_eq_true'.1 (harm a ha)) x hx, fun x hx => hval x hx,
    fun x hx => hbk x hx, fun bid hbid => hblk bid hbid⟩
  · split at hB
    · rename_i B hB'
      simp only [Bool.and_eq_true, beq_iff_eq] at hB
      exact ⟨B, hB', hB.1.1, hB.1.2, hB.2⟩
    · cases hB
  · split at hP
    · rename_i P hP'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
      exact ⟨P, hP', hP.1, hP.2⟩
    · cases hP

end GoFV.Proof.FuseIf
