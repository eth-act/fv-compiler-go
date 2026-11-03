import GoFV.Proof.Pass.MoveLEnter
import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.CheckFacts

/-!
# Value motion over a fixed CFG refines under `runL` (`refinesL_of_move`, issue #385)

If `g` keeps `f`'s blocks, kinds, `auxInt`s, edges and controls and only moves, clones or
copies values in a way the validator `moveB` accepts (`GoFV.Proof.Pass.MoveLCheck`), every `runL`
of `f` is a `runL` of `g`. The proof is a lock-step simulation (`runLoopL_sim`) along the same
blocks and edges with the relation `St`: per block entry, the source's and the target's
`Phi`s agree (`enter_phis`); the source's schedule runs with the target fixed (`phaseS`), then
the target's (`phaseT`): at the end both have run their blocks and related registers agree on the
values placed in the block and its dominators; if the source panics at `r` (a call or a nil
check), the target reaches `r` (`orderOK`: every non-total value before it in the target is before
it in the source; total values never panic or get stuck) with equal arguments and panics alike.
The terminators read equal controls (`stepTermL_rel`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof Dom

variable {ok : Array Bool} {f g : Func} {tabs : Tables} {md : LMode} {env : Env}

theorem enterBlockL_ok_split {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (h : enterBlockL md env ctx fr b i = .ok fr') :
    ∃ ps o, b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = .ok fr' := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      exact ⟨ps, o, rfl, rfl, h⟩

theorem enterBlockL_of {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat} {ps : List (ID × Val)}
    {o : Array ID} (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o) :
    enterBlockL md env ctx fr b i = evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList := by
  rw [enterBlockL_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]
  rfl

private theorem frame_eq3 {a b c d : Frame} (h1 : a = { b with regs := a.regs })
    (h2 : b = { c with regs := b.regs }) (h3 : d = { c with regs := d.regs }) :
    a = { d with regs := a.regs } := by
  rw [h3]; rw [h2] at h1; exact h1

/-- A value placed in a dominator of `b` (or `b`) is available after `b`. -/
theorem placedIn_X0 {ce : CheckEnv} {h : Func} (hwf : WF ce h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {o : Array ID}
    (hm : ∀ y, y ∈ o.toList ↔ y ∈ hb.values ∧ ∃ v, h.value? y = some v ∧ v.op ≠ .Phi) {x : ID}
    (hx : PlacedIn h (fun a => Anc (make h) a b) x) : X0 h hb b x ∨ x ∈ o.toList := by
  obtain ⟨v, hpv, hanc⟩ := hx
  by_cases he : v.block = b
  · obtain ⟨hv, -, blk, hblk, hxb⟩ := hpv
    rw [he, hbb] at hblk; cases hblk
    by_cases hp : v.op = .Phi
    · exact .inl (.inr ⟨hxb, v, hv, hp⟩)
    · exact .inr ((hm x).2 ⟨hxb, v, hv, hp⟩)
  · exact .inl (.inl ⟨v, hpv, hanc, he⟩)

/-- The arguments a successor's `Phi`s read along edge `e` of `b` are placed in dominators of
`b`. -/
theorem phiArgs_edge {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID}
    {hb : Block} (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
    (ht : ((make h).depthOf b).isSome) {k : Nat} {e : Edge} (he : hb.succs[k]? = some e) :
    ∀ blk x v a, h.block? e.b = some blk → x ∈ blk.values → h.value? x = some v → v.op = .Phi →
      v.args[e.i]? = some a → PlacedIn h (fun c => Anc (make h) c b) a := by
  intro blk x v a hblk hx hv hph ha
  obtain ⟨hem, c, hc', hcp⟩ := hwf.succLink b hb ⟨hbm, hbb⟩ k e he
  rw [hblk] at hc'; cases hc'
  have hu := hc.domRel.phiUse hem hblk (hc.domRel.edge hbm hbb ht (Array.mem_of_getElem? he)).1
    hx hv hph ha hcp ht
  obtain ⟨va, hpa, hba⟩ := placed_of_listed hwf
    (hwf.argListed _ blk x v ⟨⟨hem, hblk⟩, hx, hv⟩ a (Array.mem_of_getElem? ha))
  exact ⟨va, hpa, hba ▸ hu⟩

/-- **One block step** of the simulation. -/
theorem stepL (S : Setup ok f g) (hmd : md.faulting = false) {frS frT : Frame} {b : ID} {i : Nat}
    (hR : St ok f g tabs md env frS frT b i) :
    StepSim (fun frS frT b i => St ok f g tabs md env frS frT b i)
      (blockStepL md env (Ctx.makeL tabs f) frS b i) (blockStepL md env (Ctx.makeL tabs g) frT b i) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hcf := S.cf
  have hcg := S.cg
  obtain ⟨-, hbl, hown, hlow, hcert, hall⟩ := moveWith_spec S.mv
  have H : Hyp ok f g md := ⟨hcert, hown, hlow, hmd⟩
  have hR' := hR
  obtain ⟨hb, htf, htg, hfr, hsS, hsT, hdS, hdT, -⟩ := hR
  obtain ⟨fb, gb, oT, oS, hfb, hgb, hk, hai, hsu, -, hct, hcok, hvals, hoT, hoS, hord⟩ :=
    blockOK_spec (hall b hb)
  have hbg : b ∈ g.blocks := hbl ▸ hb
  have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have hcG : (Ctx.makeL tabs g).f = g := makeL_f tabs g
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId b hb
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gb', hgb', hgid⟩ := hwg.blockId b hbg
  rw [hgb] at hgb'; cases hgb'
  have hsF : ((Ctx.makeL tabs f).sched[fb.id]?).join = some oS := by
    rw [hfid, sched_of_blockL hfb, hoS]
  have hsG : ((Ctx.makeL tabs g).sched[gb.id]?).join = some oT := by
    rw [hgid, sched_of_blockL hgb, hoT]
  obtain ⟨hrS, hmS⟩ := ready_block hwf hcf hb hfb htf hoS
  obtain ⟨hrT, hmT⟩ := ready_block hwg hcg hbg hgb htg hoT
  unfold blockStepL
  rw [hcF, hcG, hfb, hgb]
  dsimp only
  cases hen : enterBlockL md env (Ctx.makeL tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, o, hps, ho, hev⟩ := enterBlockL_panic hen
    rw [hsF] at ho; cases ho
    obtain ⟨psT, hpsT, hAvS, hclS, hAvT, hclT, hag⟩ :=
      enter_phis hwf hwg hcf hcg H hR' hfb hgb hbg hvals hps
    obtain ⟨pre, r, post, GS', hsplit, hpre, hr⟩ := evalAllL_panic_split hev
    have hrm : r ∈ oS.toList := by rw [hsplit]; simp
    obtain ⟨-, fv, hfv, -⟩ := (hmS r).1 hrm
    rw [stepVL_of (by rw [hcF]; exact hfv)] at hr
    obtain ⟨hok, hrmT, hbef⟩ := orderOK_spec hord hrm (mayPanic_of_panic hmd hfv hr)
    obtain ⟨preT, postT, hsplitT⟩ := List.append_of_mem hrmT
    obtain ⟨hrdS, -, hnrS, haS⟩ := ready_split (hsplit ▸ hrS)
    obtain ⟨hrdT, hPr, hnrT, haT⟩ := ready_split (hsplitT ▸ hrT)
    have hbS : before oS.toList r = pre := by
      rw [hsplit]; exact before_eq fun h => hnrS (.inr h)
    have hbT : before oT.toList r = preT := by
      rw [hsplitT]; exact before_eq fun h => hnrT (.inr h)
    have hfrP : { frT with regs := setPhis psT frT.regs } =
        { ({ frS with regs := setPhis ps frS.regs } : Frame) with
          regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } := by
      rw [hfr]
    obtain ⟨hAvS', hclS', hagS', hGS', -⟩ := phaseS H hAvT hclT hrdS
      (by simp [setPhis_size, hsS]) hfrP hAvS hclS hag hpre
    have hrdT' := hrdT.mono_mem (P' := fun x => ∃ gv, g.value? x = some gv ∧ gv.id = x ∧
        gv.op ≠ .Phi ∧ (totalOp gv.op = true ∨ ((X0 f fb b x ∨ x ∈ pre) ∧ okAt ok x = true)))
      fun y hy ⟨gv, hgv, hid, hph⟩ => by
        refine ⟨gv, hgv, hid, hph, ?_⟩
        obtain ⟨gv', hgv', -, hnp⟩ := valueOK_spec (hvals y ((hmT y).1 (by
          rw [hsplitT]; exact List.mem_append_left _ hy)).1)
        rw [hgv] at hgv'; cases hgv'
        rcases hnp hph with ht | ⟨hok, -⟩
        · exact .inl ht
        · by_cases ht : totalOp gv.op = true
          · exact .inl ht
          · have hnt : nonTotal g y = true := by
              unfold nonTotal; rw [hgv]; simpa using ht
            exact .inr ⟨.inr (hbS ▸ hbef y (hbT ▸ hy) hnt), hok⟩
    obtain ⟨GT', hevT, -, -, hagT', hGT', -⟩ := phaseT H hAvS' hclS' hrdT'
      (by simp [setPhis_size, hsT]) (frame_eq3 hfrP rfl hGS') hAvT hclT hagS'
    -- the target reaches `r`
    obtain ⟨gv, hgv, hgid, hgph⟩ := hPr
    obtain ⟨gv', fv', hgv', hfv', hop, hty, hsz, hrel, -, hrest⟩ :=
      okLocal_spec (okLocal_of H.cert hok)
    rw [hgv] at hgv'; cases hgv'
    rw [hfv] at hfv'; cases hfv'
    obtain ⟨haux, hai', hsx⟩ := hrest hgph
    have hfid' : fv.id = r := by
      obtain ⟨v, hv, hid, -, -⟩ := placed_in hwf hb hfb ((hmS r).1 hrm).1
      rw [hfv] at hv; cases hv; exact hid
    have hdef : ∀ c ∈ fv.args, ∃ z, GS'.regs[c]? = some (some z) :=
      evalValueL_args_def (by rw [hr]; nofun)
    have heq := evalValueL_ident (md := md) (env := env) (tabs := tabs)
      (frame_eq3 hGT' hfrP hGS') hop haux hai' (hgid.trans hfid'.symm) hsz
      (argsAgree hagT' hsz hrel
        (fun a ha => haT a (by rw [argsF_of hgv]; exact Array.mem_toList_iff.2 ha))
        (fun c hc => haS c (by rw [argsF_of hfv]; exact Array.mem_toList_iff.2 hc)) hdef)
      (by rw [hgid, hfid']; exact tys_eq H hgv hfv hty) hsx hown
    rw [hr] at heq
    have hTen : enterBlockL md env (Ctx.makeL tabs g) frT gb i = .panic e m := by
      rw [enterBlockL_of hpsT hsG, hsplitT, evalAllL_append, hevT]
      show evalAllL md env (Ctx.makeL tabs g) GT' (r :: postT) = _
      rw [evalAllL_cons, stepVL_of (by rw [hcG]; exact hgv), heq]
    rw [hTen]
    rfl
  | ok GS =>
    obtain ⟨ps, o, hps, ho, hev⟩ := enterBlockL_ok_split hen
    rw [hsF] at ho; cases ho
    obtain ⟨psT, hpsT, hAvS, hclS, hAvT, hclT, hag⟩ :=
      enter_phis hwf hwg hcf hcg H hR' hfb hgb hbg hvals hps
    have hfrP : { frT with regs := setPhis psT frT.regs } =
        { ({ frS with regs := setPhis ps frS.regs } : Frame) with
          regs := ({ frT with regs := setPhis psT frT.regs } : Frame).regs } := by
      rw [hfr]
    obtain ⟨hAvS', hclS', hagS', hGS', -⟩ := phaseS H hAvT hclT hrS
      (by simp [setPhis_size, hsS]) hfrP hAvS hclS hag hev
    have hrT' := hrT.mono_mem (P' := fun x => ∃ gv, g.value? x = some gv ∧ gv.id = x ∧
        gv.op ≠ .Phi ∧ (totalOp gv.op = true ∨ ((X0 f fb b x ∨ x ∈ oS.toList) ∧ okAt ok x = true)))
      fun y hy ⟨gv, hgv, hid, hph⟩ => by
        refine ⟨gv, hgv, hid, hph, ?_⟩
        obtain ⟨gv', hgv', -, hnp⟩ := valueOK_spec (hvals y ((hmT y).1 hy).1)
        rw [hgv] at hgv'; cases hgv'
        rcases hnp hph with ht | ⟨hok, hyf⟩
        · exact .inl ht
        · obtain ⟨gv', fv, hgv', hfv, hop, -⟩ := okLocal_spec (okLocal_of H.cert hok)
          rw [hgv] at hgv'; cases hgv'
          exact .inr ⟨.inr ((hmS y).2 ⟨hyf, fv, hfv, hop ▸ hph⟩), hok⟩
    obtain ⟨GT, hevT, -, -, hagT, -, -⟩ := phaseT H hAvS' hclS' hrT'
      (by simp [setPhis_size, hsT]) (frame_eq3 hfrP rfl hGS') hAvT hclT hagS'
    have hTen : enterBlockL md env (Ctx.makeL tabs g) frT gb i = .ok GT := by
      rw [enterBlockL_of hpsT hsG, hevT]
    rw [hTen]
    dsimp only
    obtain ⟨dS', hGSfr, hGSsz⟩ := dinvL_enter hwf hcf hb hfb hsS hdS hen
    obtain ⟨dT', hGTfr, hGTsz⟩ := dinvL_enter hwg hcg hbg hgb hsT hdT hTen
    have hagA : Agree ok f g (PlacedIn g (fun a => Anc (make g) a b))
        (PlacedIn f (fun a => Anc (make f) a b)) GT GS :=
      hagT.mono (fun x hx => placedIn_X0 hwg hbg hgb hmT hx)
        (fun y hy => placedIn_X0 hwf hb hfb hmS hy)
    have hagc : ∀ c ∈ fb.controls, GT.regs[c]? = GS.regs[c]? := fun c hc => by
      have hcg' : c ∈ gb.controls := hct ▸ hc
      obtain ⟨vg, hpg, hbg'⟩ := placed_of_listed hwg (hwg.ctrlListed b gb ⟨hbg, hgb⟩ c hcg')
      obtain ⟨vf, hpf, hbf'⟩ := placed_of_listed hwf (hwf.ctrlListed b fb ⟨hb, hfb⟩ c hc)
      exact hagA c c ⟨vg, hpg, hbg' ▸ hcg.domRel.ctrlUse hbg hgb htg hcg'⟩
        ⟨vf, hpf, hbf' ▸ hcf.domRel.ctrlUse hb hfb htf hc⟩ ⟨relFuel, hcok c hcg'⟩
    cases hst : stepTermL GS fb with
    | stuck msg => exact True.intro
    | panic e m => exact absurd hst Dead.stepTermL_not_panic
    | ok n =>
    rcases Dead.stepTermL_rel (.inl hk) hai hct hagc hst with ⟨k, e, rfl, he, -, hst'⟩ |
      ⟨rs, m, rfl, hst'⟩
    · have heg : gb.succs[k]? = some e := by rw [hsu]; exact he
      have hgo : stepTermL GT gb = .ok (.goto e) := by rw [hst']; unfold succ; rw [heg]; rfl
      rw [hgo]
      have hem : e ∈ fb.succs := Array.mem_of_getElem? he
      have hedf := hcf.domRel.edge hb hfb htf hem
      have hedg := hcg.domRel.edge hbg hgb htg (hsu ▸ hem)
      refine ⟨GT, rfl, (hwf.succLink b fb ⟨hb, hfb⟩ k e he).1, hedf.1, hedg.1,
        frame_eq3 hGTfr hfr hGSfr, by rw [hGSsz]; exact hsS, by rw [hGTsz]; exact hsT,
        dinvL_edge hcf hb hfb htf hem dS', dinvL_edge hcg hbg hgb htg (hsu ▸ hem) dT',
        fun a => Anc (make f) a b, fun a => Anc (make g) a b,
        fun a ⟨ha, hne⟩ => hedf.2 a ha hne, fun a ⟨ha, hne⟩ => hedg.2 a ha hne, hagA,
        phiArgs_edge hwf hcf hb hfb htf he, phiArgs_edge hwg hcg hbg hgb htg heg⟩
    · rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩

/-- An activation's entry frame reads of its context the tables, parameter shapes, frame
variables, activation and number of values. -/
private theorem entryFrame_rel {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs)
    (hpt : ctx'.paramTys = ctx.paramTys) (hloc : ctx'.locals = ctx.locals)
    (hact : ctx'.act = ctx.act) (args : List Val) (mem : Mem) :
    entryFrame env ctx' args mem =
      { entryFrame env ctx args mem with regs := Array.replicate ctx'.f.valueTab.size none } := by
  unfold entryFrame frameMem frameAllocs
  rw [htabs, hpt, hloc, hact]

private theorem paramTys_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).paramTys = (Ctx.make tabs f).paramTys := by
  unfold Ctx.makeL; split <;> rfl

private theorem locals_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
  unfold Ctx.makeL; split <;> rfl

/-- **Value motion validated by `moveWith` refines under `runL`.** -/
theorem refinesL_of_moveWith (S : Setup ok f g) : RefinesL tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hcf := S.cf
  have hcg := S.cg
  obtain ⟨hent, -, hown, hlow, -, -⟩ := moveWith_spec S.mv
  have hpar : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by
    rw [params_makeL, params_makeL]; simp only [Ctx.make, abiParams, hown]
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [hlow, hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    have houts : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
      rw [outs_makeL, outs_makeL]
      simp only [Ctx.make, abiParams, hown]
    have hdefers : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by
      unfold Ctx.makeL; split <;> split <;> rfl
    have hentry := entryFrame_rel (env := env) (ctx := Ctx.makeL tabs f) (ctx' := Ctx.makeL tabs g)
      (by rw [tabs_makeL, tabs_makeL])
      (by rw [paramTys_makeL, paramTys_makeL]; simp only [Ctx.make, abiParams, hown])
      (by rw [locals_makeL, locals_makeL]; simp only [Ctx.make, abiParams, hown])
      (by rw [act_makeL, act_makeL]; rfl) args mem
    rw [hentry, houts, hdefers, act_makeL tabs g, act_makeL tabs f,
      show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl, makeL_f, makeL_f, hent]
    rw [makeL_f, act_makeL] at hd
    -- the entry state
    have hT0 : ((make g).depthOf f.entry).isSome := hent ▸ hcg.domRel.entry
    have h0 : St ok f g tabs ⟨f.lowered, false⟩ env (entryFrame env (Ctx.makeL tabs f) args mem)
        { entryFrame env (Ctx.makeL tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } f.entry 0 := by
      refine ⟨hwf.entry, hcf.domRel.entry, hT0, rfl, by simp [entryFrame, makeL_f],
        by simp, dinvL_entry hcf _, ?_, fun a => Anc (make f) a f.entry ∧ a ≠ f.entry,
        fun a => Anc (make g) a f.entry ∧ a ≠ f.entry, fun _ h => h, fun _ h => h,
        fun x y hx _ _ => ?_, ?_, ?_⟩
      · have := dinvL_entry (md := ⟨f.lowered, false⟩) (env := env) (ctx := Ctx.makeL tabs g) hcg
          { entryFrame env (Ctx.makeL tabs f) args mem with
            regs := Array.replicate g.valueTab.size none }
        rw [hent] at this; exact this
      · obtain ⟨v, -, ha, hne⟩ := hx
        rw [← hent] at ha hne
        exact absurd (hcg.domRel.entry_anc ha) hne
      · intro blk x v a hblk hx hv hph ha
        have h1 := hwf.phiArity _ _ _ _ ⟨⟨hwf.entry, hblk⟩, hx, hv⟩ hph
        have h2 := hwf.entryPreds blk hblk
        rw [Array.getElem?_eq_none (by omega)] at ha; cases ha
      · intro blk x v a hblk hx hv hph ha
        rw [← hent] at hblk
        have h1 := hwg.phiArity _ _ _ _ ⟨⟨hwg.entry, hblk⟩, hx, hv⟩ hph
        have h2 := hwg.entryPreds blk hblk
        rw [Array.getElem?_eq_none (by omega)] at ha; cases ha
    exact finish_refines hd (runLoopL_sim (fun frS frT b i => St ok f g tabs ⟨f.lowered, false⟩ env frS frT b i)
      (fun _ _ _ _ hR => stepL S rfl hR) fuel _ _ _ _ h0 (finish_defined hd))

/-- **Value motion over a fixed CFG refines under `runL`** (issue #385): `g` keeps the blocks,
kinds, `auxInt`s, edges and controls of `f` and moves, clones or copies values as `moveB`
validates. -/
theorem refinesL_of_move {ce ce' : CheckEnv} {tabs : Tables} {f g : Func}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) (hm : moveB f g = true) :
    RefinesL tabs g tabs f :=
  refinesL_of_moveWith ⟨⟨ce, check_wf hf⟩, ⟨ce', check_wf hg⟩, certOK_of_check (check_domCert hf),
    certOK_of_check (check_domCert hg), hm⟩

end GoFV.Proof.MoveL
