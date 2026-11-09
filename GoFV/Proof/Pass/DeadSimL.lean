import GoFV.Proof.Pass.DeadEnterL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Removing unreachable blocks and dead values refines under `runL`

`refinesL_of_deadRel`: Phase 1's `refines_of_deadRel` over the lowered semantics. If `g` keeps
blocks, values and edges of `f` (`DeadRel`, through `Setup`), keeps what `runL` reads beyond it
(`DeadRelL`: kept blocks' `auxInt`, the ops of `g`'s values, no dropped `PanickingL` value) and
is lowered iff `f` is (one mode `⟨f.lowered, false⟩` for both runs), every `runL` of `f` is a
`runL` of `g`: the lock-step simulation of `GoFV.Proof.Pass.DeadSim` (relation `R`) with
`runLoopL_simE`, entries by `enter_okL`/`enter_panicL`, terminators by `stepTermL_rel`.
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

variable {f g : Func} {K : ID → Prop}

/-- An activation's entry frame reads of its context the tables, parameter shapes, frame
variables, activation and number of values. -/
private theorem entryFrame_eq {env : Env} {ctx ctx' : Ctx} (htabs : ctx.tabs = ctx'.tabs)
    (hpt : ctx.paramTys = ctx'.paramTys) (hloc : ctx.locals = ctx'.locals)
    (hact : ctx.act = ctx'.act) (hsize : ctx.f.valueTab.size = ctx'.f.valueTab.size)
    (args : List Val) (mem : Mem) : entryFrame env ctx args mem = entryFrame env ctx' args mem := by
  unfold entryFrame frameMem frameAllocs
  rw [htabs, hpt, hloc, hact, hsize]

private theorem paramTys_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).paramTys = (Ctx.make tabs f).paramTys := by
  unfold Ctx.makeL; split <;> rfl

private theorem locals_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
  unfold Ctx.makeL; split <;> rfl

/-- **One block step** under `runL`. -/
theorem stepL (S : Setup f g K) (L : DeadRelL f g K) (hlow : g.lowered = f.lowered) {md : LMode}
    (hmd : md.faulting = false) {tabs : Tables} {env : Env} {frS frT : Frame}
    {bS iS bT iT : Nat} (hR : R f g K frS bS iS frT bT iT) :
    StepSimE Eq (R f g K) (blockStepL md env (Ctx.makeL tabs f) frS bS iS)
      (blockStepL md env (Ctx.makeL tabs g) frT bT iT) := by
  obtain ⟨rfl, hb, hA, hsz, hP⟩ := hR
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb, fb, hgb, hfb, -, -, -, hk, hc, -⟩ := S.blocks hb
  unfold blockStepL
  simp only [makeL_f, hfb, hgb]
  cases hen : enterBlockL md env (Ctx.makeL tabs f) frS fb iS with
  | panic e m =>
    simp only [S.enter_panicL L hlow hmd hb hgb hfb hA hsz hP hen]; exact ⟨m, rfl, rfl⟩
  | stuck msg => exact True.intro
  | ok G =>
  obtain ⟨GT, hT, hAG, hszG⟩ := S.enter_okL L hlow hb hgb hfb hA hsz hP hen
  simp only [hT]
  cases hst : stepTermL G fb with
  | panic e m => exact absurd hst stepTermL_not_panic
  | stuck msg => exact True.intro
  | ok n =>
  have hag : ∀ c ∈ fb.controls, GT.regs[c]? = G.regs[c]? := fun c hcm =>
    hAG.2.2 c (hwg.ctrlListed _ gb ⟨S.rel.sub _ hb, hgb⟩ c (by rw [hc]; exact hcm))
  rcases stepTermL_rel hk (L.auxInt _ hb gb fb hgb hfb) hc hag hst with
    ⟨k, e, rfl, he, hf, hst'⟩ | ⟨rs, m, rfl, hst'⟩
  · obtain ⟨e', he', heb, hbe, hPe⟩ := S.rel.edge _ hb gb fb hgb hfb k e he hf
    have hgo : stepTermL GT gb = .ok (.goto e') := by rw [hst']; unfold succ; rw [he']; rfl
    simp only [hgo]
    exact ⟨GT, e', rfl, heb, hbe, hAG, hszG, hPe⟩
  · simp only [hst']
    exact ⟨rs, m, rfl, RefinesList.refl rs, Mem.Refines.refl m⟩

/-- **Keeping blocks, values and edges refines under `runL`** (`refines_of_deadRel` for lowered
functions). -/
theorem refinesL_of_deadRel {tabs : Tables} (S : Setup f g K) (L : DeadRelL f g K)
    (hlow : g.lowered = f.lowered) : RefinesL tabs g tabs f := by
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
  have hentry : ∀ (env : Env) (args : List Val) (mem : Mem), entryFrame env (Ctx.makeL tabs g) args mem =
      entryFrame env (Ctx.makeL tabs f) args mem := fun env args mem =>
    entryFrame_eq (by rw [tabs_makeL, tabs_makeL])
      (by rw [paramTys_makeL, paramTys_makeL]; simp only [Ctx.make, abiParams, S.rel.ownAux])
      (by rw [locals_makeL, locals_makeL]; simp only [Ctx.make, abiParams, S.rel.ownAux])
      (by rw [act_makeL, act_makeL]; rfl) (by rw [makeL_f, makeL_f]; exact S.rel.vsize) args mem
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [hlow, params_makeL tabs g, params_eq S.rel.ownAux, ← params_makeL tabs f]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    have houts : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
      rw [outs_makeL, outs_makeL]
      simp only [Ctx.make, abiParams, S.rel.ownAux]
    have hdefers : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by
      unfold Ctx.makeL; split <;> split <;> rfl
    rw [hentry env args mem, houts, hdefers, act_makeL tabs g, act_makeL tabs f,
      show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl, makeL_f, makeL_f, S.rel.entry]
    rw [makeL_f, act_makeL] at hd
    exact finish_refines hd (runLoopL_simE (R f g K)
      (fun _ _ _ _ _ _ hR => stepL S L hlow rfl hR) fuel _ _ _ _ _ _
      ⟨rfl, hbg, ⟨rfl, rfl, fun _ _ => rfl⟩, by simp [entryFrame, makeL_f], hP0⟩
      (finish_defined hd))

end GoFV.Proof.Dead
