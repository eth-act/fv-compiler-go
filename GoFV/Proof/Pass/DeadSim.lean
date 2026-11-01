import GoFV.Proof.Pass.DeadEnter

/-!
# Removing unreachable blocks and dead values refines

`refines_of_deadRel`: if `g` keeps blocks, values and edges of `f` (`DeadRel`), both are well
formed and the roots of the kept blocks of `f` are chained, every run of `f` is a run of `g`:
lock-step simulation (`runLoop_simE`) where the target enters the same block along its own edge
index, with frames agreeing on the kept values (`R`). A run of `f` only enters kept blocks: the
target's well-formedness keeps its edges inside its blocks, and a kept block's successors are
the source's.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

variable {f g : Func} {K : ID → Prop}

/-- The simulation relation at block entries: the same kept block, frames agreeing on the kept
values, and the target's `Phi`s reading along its edge what the source's read along theirs. -/
def R (f g : Func) (K : ID → Prop) (frS : Frame) (bS iS : Nat) (frT : Frame) (bT iT : Nat) :
    Prop :=
  bT = bS ∧ K bS ∧ Agree g frS frT ∧ frS.regs.size = f.valueTab.size ∧ PhiArgs f g bS iS iT

/-- **One block step.** -/
theorem step (S : Setup f g K) {tabs : Tables} {env : Env} {frS frT : Frame}
    {bS iS bT iT : Nat} (hR : R f g K frS bS iS frT bT iT) :
    StepSimE (R f g K) (blockStep env (Ctx.make tabs f) frS bS iS)
      (blockStep env (Ctx.make tabs g) frT bT iT) := by
  obtain ⟨rfl, hb, hA, hsz, hP⟩ := hR
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb, fb, hgb, hfb, -, -, -, hk, hc, -⟩ := S.blocks hb
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl, hfb,
    hgb]
  cases hen : enterBlock env (Ctx.make tabs f) frS fb iS with
  | panic e m => simp only [S.enter_panic hb hgb hfb hA hsz hP hen]; rfl
  | stuck msg => exact True.intro
  | ok G =>
  obtain ⟨GT, hT, hAG, hszG⟩ := S.enter_ok hb hgb hfb hA hsz hP hen
  simp only [hT]
  cases hst : stepTerm G fb with
  | panic e m => exact absurd hst CopyElim.stepTerm_not_panic
  | stuck msg => exact True.intro
  | ok n =>
  have hag : ∀ c ∈ fb.controls, GT.regs[c]? = G.regs[c]? := fun c hcm =>
    hAG.2.2 c (hwg.ctrlListed _ gb ⟨S.rel.sub _ hb, hgb⟩ c (by rw [hc]; exact hcm))
  rcases stepTerm_rel hk hc hag hst with ⟨k, e, rfl, he, hf, hst'⟩ | ⟨rs, m, rfl, hst'⟩
  · obtain ⟨e', he', heb, hbe, hPe⟩ := S.rel.edge _ hb gb fb hgb hfb k e he hf
    have hgo : stepTerm GT gb = .ok (.goto e') := by rw [hst']; unfold succ; rw [he']; rfl
    simp only [hgo]
    exact ⟨GT, e', rfl, heb, hbe, hAG, hszG, hPe⟩
  · simp only [hst']
    exact ⟨rs, rfl, RefinesList.refl rs⟩

/-- **Keeping blocks, values and edges (`DeadRel`) refines.** -/
theorem refines_of_deadRel {tabs : Tables} (S : Setup f g K) : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : K f.entry := S.rel.entryK
  -- the entry block has no predecessors: its kept `Phi`s have no arguments
  have hP0 : PhiArgs f g f.entry 0 0 := by
    intro gc hgc x hx gv hgv hgph
    obtain ⟨fb, hfb, -⟩ := hwf.blockId f.entry hwf.entry
    obtain ⟨-, -, hbf, -, -, -⟩ := S.blockFacts hbg hgc hfb
    obtain ⟨gv', fv, hgv', hfv, -, -, hxf, -, hph, -⟩ := S.value hbg hgc hfb hx
    rw [hgv] at hgv'; cases hgv'
    refine ⟨fv, hfv, ?_⟩
    have h1 := hwg.phiArity _ _ _ _ ⟨⟨S.rel.sub _ hbg, hgc⟩, hx, hgv⟩ hgph
    have h2 := hwg.entryPreds gc (by rw [S.rel.entry]; exact hgc)
    have h3 := hwf.phiArity _ _ _ _ ⟨⟨hbf, hfb⟩, hxf, hfv⟩ (hph.1 hgph)
    have h4 := hwf.entryPreds fb hfb
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [params_eq S.rel.ownAux]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      S.rel.vsize
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem
      rw [hsz]
      simp only [Ctx.make, abiParams, S.rel.ownAux]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, S.rel.ownAux]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from S.rel.entry]
    exact finish_refines hd (runLoop_simE (R f g K) (fun _ _ _ _ _ _ hR => step S hR) fuel _ _ _ _
      _ _
      ⟨rfl, hbg, ⟨rfl, rfl, fun _ _ => rfl⟩, by simp [Ctx.make, entryFrame], hP0⟩
      (finish_defined hd))

end GoFV.Proof.Dead
