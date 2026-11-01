import GoFV.Proof.Pass.PhiOptFacts
import GoFV.Proof.Pass.ZCSESetup

/-!
# phiopt: what the simulation uses

`Setup tabs f g`: both functions are well-formed, `f`'s dominator certificate holds, `g` is
related to `f` by `PRel`, and `f` is in zcse's fragment (`Chained`, `NoNil`). Consequences:
the target block and value of each block and value of `f`, and what is new.

`path_step`: **edge facts hold**. If on entry to block `bid` along edge `i` every edge fact of
`(bid, i)` holds in the frame, then after the block, on entry to its successor, every edge fact
of the successor's edge holds: an `If` on `c` was just left through the successor its control
named, or the block (with a single predecessor, so entered along the fact's edge) does not
define `c`.
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree cfgView_blocks cfgView_entry cfgView_block make_eq)
open GoFV.Proof.ZCSE (Chained NoNil)

/-- Everything the simulation uses about phiopt's input `f` and output `g`. -/
structure Setup (tabs : Tables) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  rel : PRel tabs f g
  chained : Chained f
  noNil : NoNil f

variable {tabs : Tables} {f g : Func}

/-- `x` is a value listed in `f` (its register is related). -/
theorem listed_lt {ce : CheckEnv} (hwf : WF ce f) {x : ID} (h : Listed f x) :
    x < f.valueTab.size := by
  obtain ⟨bid, b, hb, hx⟩ := h
  obtain ⟨v, hv, -⟩ := hwf.valueId bid b hb x hx
  exact lt_of_value? hv

theorem not_listed {ce : CheckEnv} (hwf : WF ce f) {x : ID} (h : f.value? x = none) :
    ¬ Listed f x := by
  rintro ⟨bid, b, hb, hx⟩
  obtain ⟨v, hv, -⟩ := hwf.valueId bid b hb x hx
  rw [h] at hv; cases hv

namespace Setup

variable (S : Setup tabs f g)
include S

theorem blocks : g.blocks = f.blocks := cfgView_blocks S.rel.cfg
theorem entry : g.entry = f.entry := cfgView_entry S.rel.cfg
theorem mk_eq : make g = make f := make_eq S.rel.cfg

theorem params : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem paramTys : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem outs : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

theorem locals : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

/-- The target block of a block of `f`. -/
theorem block {b : ID} (hb : b ∈ f.blocks) {fb : Block} (hfb : f.block? b = some fb) :
    ∃ gb, g.block? b = some gb ∧ gb.id = fb.id ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds ∧
      gb.kind = fb.kind ∧ gb.controls = fb.controls ∧ (∀ x ∈ fb.values, x ∈ gb.values) ∧
      (∀ x ∈ gb.values, x ∈ fb.values ∨ (f.value? x = none ∧ newOK f g b x = true)) := by
  obtain ⟨gb, hgb, h1, h2, h3⟩ := cfgView_block S.rel.cfg hfb
  obtain ⟨gb', hgb', h4, h5, h6, h7⟩ := S.rel.block b hb fb hfb
  rw [hgb] at hgb'; cases hgb'
  exact ⟨gb, hgb, h1, h2, h3, h4, h5, h6, h7⟩

/-- Shapes agree on values of `f`. -/
theorem tys {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := by
  obtain ⟨gv, hgv, -, hty, -⟩ := S.rel.value x fv hfv
  rw [tys_of_value hfv, tys_of_value hgv, hty]

theorem gsize : f.valueTab.size ≤ g.valueTab.size := S.rel.vsize

end Setup

/-! ## Edge facts -/

/-- The successor a terminator goes to, and for an `If`, the control's value. -/
theorem stepTerm_goto_idx {fr : Frame} {b : Block} {e : Edge}
    (h : stepTerm fr b = .ok (.goto e)) :
    ∃ k, b.succs[k]? = some e ∧ (b.kind = .If → Sem.control fr b 0 = .ok (.bool (k == 0))) := by
  have hs : ∀ k, succ b k = .ok (.goto e) → b.succs[k]? = some e := fun k h => by
    unfold succ at h
    cases hk : b.succs[k]? with
    | none => rw [hk] at h; cases h
    | some e' => rw [hk] at h; cases h; rfl
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact ⟨0, hs 0 h, fun h' => by cases h'⟩
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first
            | (cases h; done)
            | exact ⟨0, hs 0 h, fun _ => by simp_all⟩
            | exact ⟨1, hs 1 h, fun _ => by simp_all⟩
            | exact ⟨_, hs _ h, fun h' => by cases h'⟩
            | (split at h <;> first | (cases h; done) | (split at h <;> cases h))
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

/-- The edge facts of `(bid, i)` hold in `fr`. -/
def PathOK (f : Func) (fr : Frame) (bid : ID) (i : Nat) : Prop :=
  ∀ c fuel d, edgeFact f c fuel bid i = some d → fr.regs[c]? = some (some (.bool d))

/-- At the entry nothing is claimed. -/
theorem pathOK_entry {ce : CheckEnv} (hwf : WF ce f) (fr : Frame) : PathOK f fr f.entry 0 := by
  intro c fuel d h
  cases fuel with
  | zero => cases h
  | succ n =>
    unfold edgeFact at h
    cases hE : f.block? f.entry with
    | none => rw [hE] at h; cases h
    | some E =>
      rw [hE] at h
      have hp := hwf.entryPreds E hE
      have : E.preds[0]? = none := by simp [hp]
      simp only [this] at h; cases h

/-- **Edge facts are preserved by a block step.** -/
theorem path_step {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {fb : Block} (hb : BlockIn f bid fb)
    {S G : Frame} {i : Nat}
    (hi : bid = f.entry ∨ i < fb.preds.size)
    (hpath : PathOK f S bid i) (hkeep : ∀ z, z ∉ fb.values → G.regs[z]? = S.regs[z]?)
    {e : Edge} (hst : stepTerm G fb = .ok (.goto e)) : PathOK f G e.b e.i := by
  obtain ⟨k, hk, hif⟩ := stepTerm_goto_idx hst
  obtain ⟨-, xb, hxb, hxp⟩ := hwf.succLink bid fb hb k e hk
  intro c fuel d h
  cases fuel with
  | zero => cases h
  | succ n =>
    unfold edgeFact at h
    rw [hxb] at h
    simp only [hxp, hb.2] at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      cases h
      have hc := hif hcond.1
      unfold Sem.control at hc
      rw [hcond.2] at hc
      simp only [Res.ofOption] at hc
      split at hc
      · rename_i y hy; cases hc
        cases hr : G.regs[c]? with
        | none => rw [hr] at hy; cases hy
        | some o => rw [hr] at hy; cases o <;> simp_all
      · cases hc
    · split at h
      · rename_i _ hcond
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
          at hcond
        have hi0 : i = 0 := by
          rcases hi with rfl | hi
          · have := hwf.entryPreds fb hb.2; omega
          · omega
        subst hi0
        rw [hkeep c (fun hm => by have := Array.contains_iff_mem.2 hm; rw [hcond.2] at this; cases this)]
        exact hpath c n d h
      · cases h

end GoFV.Proof.PhiOpt
