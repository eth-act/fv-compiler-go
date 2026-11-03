import GoFV.Proof.Pass.NilLateLBlock
import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.AvailL
import GoFV.Proof.RefineSched
import GoFV.Proof.Agree

/-!
# `late nilcheck` refines under `runSched`: the simulation

`refinesSched_of_nlRel`: if `NLRel tabs f g rm` and `f` is well formed with a certified
dominator tree, every returning or panicking `runSched` of `f` is one of `g`, with the same fuel.
Lock-step (`runLoopL_sim`) along the same blocks and edges with the relation `RR`: frames that
agree but on the removed values (`Agree`), the source's registers holding every value placed in a
strict dominator of the block (`Avail`, so the target can read the arguments of the values it
runs past a panicking removed check). Entering a block: the same `Phi`s (`phis_eq`), then
`block_sim`; the terminator reads controls, none removed.
-/

namespace GoFV.Proof.NilLateL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Opt.NilLate

variable {tabs : Tables} {f g : Func} {rm : ID → Bool}

/-! ## Terminators -/

private theorem control_congr' {fr fr' : Frame} {b : Block}
    (h : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) (k : Nat) :
    Sem.control fr' b k = Sem.control fr b k := by
  unfold Sem.control
  cases hk : b.controls[k]? with
  | none => rfl
  | some c => simp only; rw [h c (Array.mem_of_getElem? hk)]

theorem stepTermL_congr {fr fr' : Frame} {b : Block}
    (h : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) : stepTermL fr' b = stepTermL fr b := by
  unfold stepTermL stepTerm
  rw [control_congr' h 0]

/-! ## Registers -/

/-- Evaluating values keeps the registers' count and the set ones, and sets the values. -/
theorem evalAllL_sets {md : LMode} {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr fr' : Frame}, evalAllL md env ctx fr o = .ok fr' →
      fr'.regs.size = fr.regs.size ∧
      (∀ z : ID, (∃ y : Val, fr.regs[z]? = some (some y)) → ∃ y : Val, fr'.regs[z]? = some (some y)) ∧
      (∀ x ∈ o, x < fr.regs.size → ∃ y : Val, fr'.regs[x]? = some (some y))
  | [], fr, fr', h => by
    cases h; exact ⟨rfl, fun _ h => h, fun _ h => absurd h List.not_mem_nil⟩
  | x :: o, fr, fr', h => by
    rw [evalAllL_cons] at h
    cases hs : stepVL md env ctx fr x with
    | panic e m => rw [hs] at h; cases h
    | stuck msg => rw [hs] at h; cases h
    | ok y =>
      rw [hs] at h
      obtain ⟨h1, h2, h3⟩ := evalAllL_sets h
      refine ⟨by rw [h1, set_size], fun z hz => h2 z ?_, fun x' hx' hlt => ?_⟩
      · by_cases hzx : x = z
        · subst hzx
          by_cases hlt : x < fr.regs.size
          · exact ⟨y, Frame.set_regs_self hlt⟩
          · obtain ⟨y', hy'⟩ := hz
            rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hy'; cases hy'
        · obtain ⟨y', hy'⟩ := hz; exact ⟨y', by rw [Frame.set_regs_ne hzx, hy']⟩
      · rcases List.mem_cons.1 hx' with rfl | hx'
        · exact h2 _ ⟨y, Frame.set_regs_self hlt⟩
        · exact h3 x' hx' (by rw [set_size]; exact hlt)

/-- Values placed in strict dominators of `bid` have registers. -/
def Avail (f : Func) (A : ID → ID → Prop) (fr : Frame) (bid : ID) : Prop :=
  ∀ x v, Placed f x v → A v.block bid → v.block ≠ bid → ∃ y, fr.regs[x]? = some (some y)

/-- The lock-step relation. -/
def RR (f : Func) (rm : ID → Bool) (T : ID → Prop) (A : ID → ID → Prop) (FS FT : Frame)
    (bid : ID) (_i : Nat) : Prop :=
  Agree rm FS FT ∧ FS.regs.size = f.valueTab.size ∧ bid ∈ f.blocks ∧ T bid ∧ Avail f A FS bid

/-! ## Entering a block -/

theorem setPhis_agree' {rm : ID → Bool} {FS FT : Frame} (h : Agree rm FS FT)
    (ps : List (ID × Val)) :
    Agree rm { FS with regs := setPhis ps FS.regs } { FT with regs := setPhis ps FT.regs } := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [h1], by simp only [setPhis_size, h2], fun z hz => ?_⟩
  exact setPhis_agree (X := fun z => rm z = true) ps h2 (fun a ha => h3 a (by simpa using ha)) z
    (by simpa using hz)

theorem phiStepL_eq (R : NLRel tabs f g rm) {md : LMode} {FS FT : Frame} (hA : Agree rm FS FT)
    {i : Nat} {z : ID} (hz : rm z = false) :
    phiStepL md (Ctx.makeSched tabs g) FT i z = phiStepL md (Ctx.makeSched tabs f) FS i z := by
  unfold phiStepL
  rw [nlSched_f, nlSched_f]
  cases hfz : f.value? z with
  | none => rw [R.val_none hfz]
  | some w =>
    obtain ⟨w', hgw, he⟩ := R.val hz hfz
    rw [hgw]
    simp only [eV_op he, eV_args he]
    split
    · split
      · rename_i a ha
        rw [hA.2.2 a (R.usedV z w hz hfz a (Array.mem_of_getElem? ha)), R.tys hz]
      · rfl
    · rfl

/-- The source's and the target's `Phi`s are the same. -/
theorem phis_eq (R : NLRel tabs f g rm) {md : LMode} {FS FT : Frame} (hA : Agree rm FS FT)
    {i : Nat} : ∀ l : List ID,
    (l.filter (!rm ·)).filterMapM (phiStepL md (Ctx.makeSched tabs g) FT i) =
      l.filterMapM (phiStepL md (Ctx.makeSched tabs f) FS i)
  | [] => rfl
  | z :: l => by
    by_cases hz : rm z = true
    · rw [List.filter_cons_of_neg (by simp [hz]), phis_eq R hA l, List.filterMapM_cons]
      obtain ⟨v, hv, hop⟩ := R.rmOp z hz
      have hstep : phiStepL md (Ctx.makeSched tabs f) FS i z = .ok none := by
        unfold phiStepL; rw [nlSched_f, hv]; simp [hop]
      rw [hstep]; rfl
    · have hz' : rm z = false := by simpa using hz
      rw [List.filter_cons_of_pos (by simp [hz']), List.filterMapM_cons, List.filterMapM_cons,
        phiStepL_eq R hA hz', phis_eq R hA l]

/-! ## One block -/

theorem block_values {gb fb : Block}
    (h : (some gb).map eraseB = (some fb).map (eraseB ∘ dropB rm)) :
    gb.values = fb.values.filter (!rm ·) ∧ gb.id = fb.id ∧ ∀ fr, stepTermL fr gb = stepTermL fr fb := by
  simp only [Option.map_some, Option.some.injEq, Function.comp] at h
  refine ⟨?_, ?_, fun fr => ?_⟩
  · have := congrArg Block.values h; exact this
  · have := congrArg Block.id h; exact this
  · rw [← stepTermL_eraseB fr gb, h, stepTermL_eraseB]; rfl

theorem mem_orderOf {f : Func} {b : Block} {x : ID} :
    x ∈ orderOf f b ↔ x ∈ b.values ∧ ∀ v, f.value? x = some v → v.op ≠ .Phi := by
  unfold orderOf
  rw [List.mem_filter, Array.mem_toList_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv hp => ?_⟩
    rw [hv] at h2; simp [hp] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    cases hv : f.value? x with
    | none => rfl
    | some v => simp [h2 v hv]

theorem mem_phisOf {f : Func} {b : Block} {x : ID} (h : x ∈ phisOf f b) :
    x ∈ b.values ∧ ∃ v, f.value? x = some v ∧ v.op = .Phi := by
  unfold phisOf at h
  rw [List.mem_filter, Array.mem_toList_iff] at h
  refine ⟨h.1, ?_⟩
  cases hv : f.value? x with
  | none => have := h.2; rw [hv] at this; cases this
  | some v => have := h.2; rw [hv] at this; exact ⟨v, rfl, by simpa using this⟩

/-- **One block entry** of the source and the target: `StepSim RR`. -/
theorem step (R : NLRel tabs f g rm) {ce : CheckEnv} (hwf : WF ce f) {T : ID → Prop}
    {A : ID → ID → Prop} (hD : Dom.DomRel f T A) {env : Env} {FS FT : Frame} {bid : ID} {i : Nat}
    (hR : RR f rm T A FS FT bid i) :
    StepSim (RR f rm T A) (blockStepL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs f) FS bid i)
      (blockStepL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs g) FT bid i) := by
  obtain ⟨hA, hsz, hbid, hT, hav⟩ := hR
  obtain ⟨fb, hfb, hfid⟩ := hwf.blockId bid hbid
  have hgb' := R.block bid
  rw [hfb] at hgb'
  cases hgb : g.block? bid with
  | none => rw [hgb] at hgb'; cases hgb'
  | some gb =>
  rw [hgb] at hgb'
  obtain ⟨hgv, hgid, hterm⟩ := block_values hgb'
  have hnd := hwf.valuesNodup bid fb ⟨hbid, hfb⟩
  unfold blockStepL
  rw [nlSched_f, nlSched_f, hfb, hgb]
  dsimp only
  rw [enterBlockL_eq, enterBlockL_eq, hgv, Array.toList_filter, phis_eq R hA, hgid]
  cases hps : fb.values.toList.filterMapM (phiStepL ⟨f.lowered, true⟩ (Ctx.makeSched tabs f) FS i) with
  | panic e m => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg => trivial
  | ok ps =>
  obtain ⟨hps1, -, hps3, hps4⟩ := phisL_spec hnd hps
  dsimp only [Res.bind]
  rw [hfid]
  cases hso : ((Ctx.makeSched tabs f).sched[bid]?).join with
  | none => simp only [Res.ofOption]; trivial
  | some o =>
  obtain ⟨ho, hto, hbB⟩ := R.blk bid hbid fb hfb o hso
  simp only [hto, Res.ofOption, ho]
  -- the source's facts at the block's values
  have hA1 := setPhis_agree' hA ps
  have hsz1 : (setPhis ps FS.regs).size = f.valueTab.size := by rw [setPhis_size, hsz]
  have hpre : ∀ a ∈ phisOf f fb, rm a = false →
      ∃ y, (setPhis ps FS.regs)[a]? = some (some y) := by
    intro a ha _
    obtain ⟨hab, v, hv, hph⟩ := mem_phisOf ha
    obtain ⟨_, y, _, _, hy⟩ := hps4 a hab v (by rw [nlSched_f]; exact hv) hph
      (by rw [hsz]; exact lt_of_value? hv)
    exact ⟨_, hy⟩
  have hout : ∀ x ∈ orderOf f fb, rm x = false → ∀ w, f.value? x = some w → ∀ a ∈ w.args,
      fb.values.contains a = false → ∃ y, (setPhis ps FS.regs)[a]? = some (some y) := by
    intro x hx _ w hw a ha hc
    obtain ⟨hxb, hnp⟩ := mem_orderOf.1 hx
    have hanc := hD.uses hbid hfb hT hxb hw (hnp w hw) ha
    obtain ⟨b', B', hbin, ha'⟩ := hwf.argListed bid fb x w ⟨⟨hbid, hfb⟩, hxb, hw⟩ a ha
    obtain ⟨va, hva, -, hvab⟩ := hwf.valueId b' B' hbin a ha'
    have hbo : DomCert.blockOf f a = b' := by unfold DomCert.blockOf; rw [hva]; exact hvab
    have hanb : a ∉ fb.values := fun hm => by
      have : fb.values.contains a = true := by simpa using hm
      rw [hc] at this; cases this
    have hne : b' ≠ bid := fun e => by
      subst e; rw [hbin.2] at hfb; cases hfb; exact hanb ha'
    obtain ⟨y, hy⟩ := hav a va ⟨hva, by rw [hvab]; exact hbin.1, B', by rw [hvab]; exact hbin.2, ha'⟩
      (by rw [hvab, ← hbo]; exact hanc) (by rw [hvab]; exact hne)
    exact ⟨y, by rw [hps3 a (.inl hanb)]; exact hy⟩
  have hids : ∀ x ∈ orderOf f fb, ∀ w, f.value? x = some w → w.id = x := by
    intro x hx w hw
    obtain ⟨v, hv, hvid, -⟩ := hwf.valueId bid fb ⟨hbid, hfb⟩ x (mem_orderOf.1 hx).1
    rw [hw] at hv; cases hv; exact hvid
  have hsim := block_sim (env := env) (blk := fb.values) R (orderOf f fb) (phisOf f fb)
    { FS with regs := setPhis ps FS.regs } { FT with regs := setPhis ps FT.regs } hbB hA1 hsz1
    hpre hout hids
  revert hsim
  cases hev : evalAllL ⟨f.lowered, true⟩ env (Ctx.makeSched tabs f)
      { FS with regs := setPhis ps FS.regs } (orderOf f fb) with
  | stuck msg => intro; trivial
  | panic e m => intro hTev; rw [hTev]; rfl
  | ok FS' =>
  rintro ⟨FT', hTev, hA'⟩
  rw [hTev]
  dsimp only
  rw [hterm FT', stepTermL_congr (fun c hc => hA'.2.2 c (R.usedC bid fb hfb c hc))]
  obtain ⟨hs1, hs2, hs3⟩ := evalAllL_sets hev
  cases hst : stepTermL FS' fb with
  | stuck msg => trivial
  | panic e m => rfl
  | ok n =>
  cases n with
  | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | goto e =>
  refine ⟨FT', rfl, hA', by rw [hs1]; exact hsz1, ?_, ?_⟩
  · have he := Dead.stepTermL_goto_mem hst
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact (hwf.succLink bid fb ⟨hbid, hfb⟩ j e hj).1
  · have he := Dead.stepTermL_goto_mem hst
    obtain ⟨hTe, hanc⟩ := hD.edge hbid hfb hT he
    refine ⟨hTe, fun x v hpl hAx hne => ?_⟩
    have hAb := hanc v.block hAx hne
    obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hpl
    by_cases hvbid : v.block = bid
    · rw [hvbid, hfb] at hblk
      cases hblk
      by_cases hph : v.op = .Phi
      · obtain ⟨_, y, _, _, hy⟩ := hps4 x hxv v (by rw [nlSched_f]; exact hv) hph
          (by rw [hsz]; exact lt_of_value? hv)
        exact hs2 x ⟨_, hy⟩
      · refine hs3 x (mem_orderOf.2 ⟨hxv, fun v' hv' => ?_⟩) (by rw [hsz1]; exact lt_of_value? hv)
        rw [hv] at hv'; cases hv'; exact hph
    · obtain ⟨y, hy⟩ := hav x v ⟨hv, hvb, blk, hblk, hxv⟩ hAb hvbid
      have hxn : x ∉ fb.values := fun hm => by
        obtain ⟨v', hv', -, hvb'⟩ := hwf.valueId bid fb ⟨hbid, hfb⟩ x hm
        rw [hv] at hv'; cases hv'; exact hvbid hvb'
      exact hs2 x ⟨y, by rw [hps3 x (.inl hxn)]; exact hy⟩

/-! ## The run -/

private theorem entryFrame_eq {env : Env} {ctx ctx' : Ctx} (htabs : ctx.tabs = ctx'.tabs)
    (hpt : ctx.paramTys = ctx'.paramTys) (hloc : ctx.locals = ctx'.locals)
    (hact : ctx.act = ctx'.act) (hsize : ctx.f.valueTab.size = ctx'.f.valueTab.size)
    (args : List Val) (mem : Mem) : entryFrame env ctx args mem = entryFrame env ctx' args mem := by
  unfold entryFrame frameMem frameAllocs
  rw [htabs, hpt, hloc, hact, hsize]

private theorem sched_make_fields (tabs : Tables) (f : Func) :
    (Ctx.makeSched tabs f).paramTys = (Ctx.make tabs f).paramTys ∧
    (Ctx.makeSched tabs f).locals = (Ctx.make tabs f).locals ∧
    (Ctx.makeSched tabs f).outs = (Ctx.make tabs f).outs ∧
    (Ctx.makeSched tabs f).defers = (Ctx.make tabs f).defers := by
  unfold Ctx.makeSched Ctx.makeL; split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`NLRel` gives a `runSched` refinement** (same fuel), for a well-formed `f` with a certified
dominator tree. -/
theorem refinesSched_of_nlRel (R : NLRel tabs f g rm) {ce : CheckEnv} (hwf : WF ce f)
    (hc : Dom.CertOK f) : RefinesSched tabs g tabs f := by
  have hD := hc.domRel
  obtain ⟨pS, lS, oS, dS⟩ := sched_make_fields tabs f
  obtain ⟨pT, lT, oT, dT⟩ := sched_make_fields tabs g
  have hpt : (Ctx.makeSched tabs g).paramTys = (Ctx.makeSched tabs f).paramTys := by
    rw [pS, pT]; simp only [Ctx.make, abiParams, R.ownAux]
  have hloc : (Ctx.makeSched tabs g).locals = (Ctx.makeSched tabs f).locals := by
    rw [lS, lT]; simp only [Ctx.make, abiParams, R.ownAux]
  have houts : (Ctx.makeSched tabs g).outs = (Ctx.makeSched tabs f).outs := by
    rw [oS, oT]; simp only [Ctx.make, abiParams, R.ownAux]
  have hdef : (Ctx.makeSched tabs g).defers = (Ctx.makeSched tabs f).defers := by
    rw [dS, dT]; rfl
  have hentry : ∀ (env : Env) (args : List Val) (mem : Mem),
      entryFrame env (Ctx.makeSched tabs g) args mem = entryFrame env (Ctx.makeSched tabs f) args mem :=
    fun env args mem => entryFrame_eq (by rw [nlSched_tabs, nlSched_tabs]) hpt hloc R.act
      (by rw [nlSched_f, nlSched_f]; exact R.vsize) args mem
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runSched runCtxL at hd ⊢
  rw [show LMode.sched g = LMode.sched f by simp only [LMode.sched, R.lowered], R.params]
  split
  · rename_i hn; simp only [hn, ite_true] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    rw [hentry env args mem, houts, hdef, R.act, nlSched_f, nlSched_f, R.entry]
    rw [nlSched_f] at hd
    exact finish_refines hd (runLoopL_sim (RR f rm _ _) (fun _ _ _ _ hR => step R hwf hD hR) fuel _ _ _ _
      ⟨⟨rfl, rfl, fun _ _ => rfl⟩, by simp [entryFrame, nlSched_f], hwf.entry, hD.entry,
        fun _ _ _ ha hne => absurd (hD.entry_anc ha) hne⟩ (finish_defined hd))

end GoFV.Proof.NilLateL
