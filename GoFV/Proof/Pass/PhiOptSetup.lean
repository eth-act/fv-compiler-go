import GoFV.Proof.Pass.PhiOptFacts
import GoFV.Proof.Pass.ZCSESetup

variable [GoFV.SSA.Sem.Addrs]

/-!
# phiopt: what the simulation uses

`Setup tabs f g`: both functions are well-formed, `f`'s dominator certificate holds, and `g` is
related to `f` by `PRel`. Consequences: the target block and value of each block and value of
`f`, and what is new.

`path_step`: **edge facts hold**. If on entry to block `bid` along edge `i` every edge fact of
`(bid, i)` holds in the frame, then after the block, on entry to its successor, every edge fact
of the successor's edge holds: an `If` on `c` was just left through the successor its control
named, or the block (with a single predecessor, so entered along the fact's edge) does not
define `c`, or a guard of `c` dominates the block (`DomOK`, preserved by `dom_step`: a guard is
entered only from its `If`, and a block it strictly dominates is entered from a block it
dominates, which does not define `c`).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree cfgView_blocks cfgView_entry cfgView_block make_eq)

/-- Everything the simulation uses about phiopt's input `f` and output `g`. -/
structure Setup (tabs : Tables) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  rel : PRel tabs f g

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

/-- An `If` on `c` left through successor `k` holds `k == 0` in `c`'s register. -/
theorem ctrl_reg {G : Frame} {fb : Block} {c : ID} {k : Nat} (hc0 : fb.controls[0]? = some c)
    (hc : Sem.control G fb 0 = .ok (.bool (k == 0))) :
    G.regs[c]? = some (some (.bool (k == 0))) := by
  unfold Sem.control at hc
  rw [hc0] at hc
  simp only [Res.ofOption] at hc
  split at hc
  · rename_i y hy; cases hc
    cases hr : G.regs[c]? with
    | none => rw [hr] at hy; cases hy
    | some o => rw [hr] at hy; cases o <;> simp_all
  · cases hc

/-- What `ifGuard` says. -/
theorem ifGuard_spec {f : Func} {t : Cert} {c s : ID} {d : Bool} (h : ifGuard f t c s = some d) :
    s ≠ f.entry ∧ ∃ sb cv b0, f.block? s = some sb ∧ f.value? c = some cv ∧
      sb.preds.size = 1 ∧ t.anc cv.block s = true ∧ cv.block ≠ s ∧
      f.block? sb.preds[0]!.b = some b0 ∧ b0.kind = .If ∧ b0.controls[0]? = some c ∧
      d = (sb.preds[0]!.i == 0) := by
  unfold ifGuard at h
  by_cases hne : s = f.entry
  · simp [hne] at h
  simp only [hne, beq_self_eq_true, ↓reduceIte, beq_iff_eq] at h
  refine ⟨hne, ?_⟩
  cases hsb : f.block? s with
  | none => simp [hsb] at h
  | some sb =>
  cases hcv : f.value? c with
  | none => simp [hsb, hcv] at h
  | some cv =>
  simp only [hsb, hcv] at h
  by_cases hc : sb.preds.size = 1 ∧ t.anc cv.block s = true ∧ cv.block ≠ s
  · obtain ⟨h1, h2, h3⟩ := hc
    have h3' : (cv.block != s) = true := by simpa using h3
    simp only [h1, h2, h3', beq_self_eq_true, Bool.and_self, ↓reduceIte] at h
    cases hb0 : f.block? sb.preds[0]!.b with
    | none => simp [hb0] at h
    | some b0 =>
      simp only [hb0] at h
      cases hk : (b0.kind == .If && b0.controls[0]? == some c)
      · simp [hk] at h
      · simp only [hk, ↓reduceIte, Option.some.injEq] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at hk
        exact ⟨sb, cv, b0, rfl, rfl, h1, h2, h3, hb0, hk.1, hk.2, h.symm⟩
  · have : (sb.preds.size == 1 && t.anc cv.block s && cv.block != s) = false := by
      simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq,
        Bool.not_eq_true] at *
      by_cases a : sb.preds.size = 1 <;> by_cases b : t.anc cv.block s = true <;> simp_all
    simp [this] at h

/-- What `domFact` says: a guard of `c` holding `d` is a tree ancestor of `y`. -/
theorem domFact_spec {f : Func} (hp : parentsOK (make f) f.entry = true) {c y : ID} {d : Bool}
    (h : domFact f c y = some d) : ∃ s, ifGuard f (make f) c s = some d ∧ Anc (make f) s y := by
  unfold domFact at h
  obtain ⟨s, -, hs⟩ := Array.exists_of_findSome?_eq_some h
  split at hs
  · exact ⟨s, hs, (anc_iff hp).1 ‹_›⟩
  · cases hs

/-- A block a guard of `c` dominates does not define `c` (`c`'s block strictly dominates the
guard). -/
theorem guard_not_mem {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {c s y : ID} {d : Bool}
    {yb : Block} (hg : ifGuard f (make f) c s = some d) (hs : Anc (make f) s y)
    (hy : BlockIn f y yb) : c ∉ yb.values := fun hm => by
  obtain ⟨v, hv, -, hvb⟩ := hwf.valueId y yb hy c hm
  obtain ⟨-, sb, cv, b0, -, hcv, -, hanc, hne, -⟩ := ifGuard_spec hg
  rw [hv] at hcv; cases hcv
  rw [hvb] at hanc hne
  exact hne (Anc.antisymm hc.parents ((anc_iff hc.parents).1 hanc) hs)

/-- Every guard dominating block `bid` holds in `fr`. -/
def DomOK (f : Func) (fr : Frame) (bid : ID) : Prop :=
  ∀ c s d, ifGuard f (make f) c s = some d → Anc (make f) s bid →
    fr.regs[c]? = some (some (.bool d))

/-- No guard dominates the entry. -/
theorem domOK_entry (hc : CertOK f) (fr : Frame) : DomOK f fr f.entry :=
  fun _ _ _ hg hs => absurd (anc_of_entry hc.parents hs) (ifGuard_spec hg).1

/-- **Guards are preserved by a block step**: the successor is the guard, entered from its
`If`, or the guard strictly dominates it, hence dominates the block just left (`Dom.edge`),
which does not define `c`. -/
theorem dom_step {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {bid : ID} {fb : Block}
    (hb : BlockIn f bid fb) (ht : ((make f).depthOf bid).isSome) {S G : Frame}
    (hdom : DomOK f S bid) (hkeep : ∀ z, z ∉ fb.values → G.regs[z]? = S.regs[z]?)
    {e : Edge} (hst : stepTerm G fb = .ok (.goto e)) : DomOK f G e.b := by
  obtain ⟨k, hk, hif⟩ := stepTerm_goto_idx hst
  obtain ⟨-, xb, hxb, hxp⟩ := hwf.succLink bid fb hb k e hk
  intro c s d hg hs
  by_cases hse : s = e.b
  · subst hse
    obtain ⟨-, sb, cv, b0, hsb, -, hsz, -, -, hb0, hkind, hc0, rfl⟩ := ifGuard_spec hg
    rw [hxb] at hsb; cases hsb
    have hi : e.i = 0 := by have := (Array.getElem?_eq_some_iff.1 hxp).1; omega
    rw [hi] at hxp
    have hp0 : xb.preds[0]! = ⟨bid, k⟩ := by
      rw [getElem!_pos xb.preds 0 (by omega)]; exact (Array.getElem?_eq_some_iff.1 hxp).2
    rw [hp0] at hb0 ⊢
    rw [hb.2] at hb0; cases hb0
    exact ctrl_reg hc0 (hif hkind)
  · have hsb := Anc.trans hc.parents (Anc.up hc.parents hs hse)
      (edge hc hb.1 hb.2 ht (Array.mem_of_getElem? hk)).2.2
    rw [hkeep c (guard_not_mem hwf hc hg hsb hb)]
    exact hdom c s d hg hsb

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
theorem path_step {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {bid : ID} {fb : Block}
    (hb : BlockIn f bid fb) {S G : Frame} {i : Nat}
    (hi : bid = f.entry ∨ i < fb.preds.size)
    (hpath : PathOK f S bid i) (hdom : DomOK f S bid)
    (hkeep : ∀ z, z ∉ fb.values → G.regs[z]? = S.regs[z]?)
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
      exact ctrl_reg hcond.2 (hif hcond.1)
    · split at h
      · rename_i d' hd'
        cases h
        split at hd'
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
          have hi0 : i = 0 := by
            rcases hi with rfl | hi
            · have := hwf.entryPreds fb hb.2; omega
            · omega
          subst hi0
          rw [hkeep c (fun hm => by
            have := Array.contains_iff_mem.2 hm; rw [hcond.2] at this; cases this)]
          exact hpath c n _ hd'
        · cases hd'
      · obtain ⟨s, hg, hs⟩ := domFact_spec hc.parents h
        rw [hkeep c (guard_not_mem hwf hc hg hs hb)]
        exact hdom c s d hg hs

end GoFV.Proof.PhiOpt
