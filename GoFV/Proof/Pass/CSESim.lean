import GoFV.Proof.Pass.CSEPhi
import GoFV.Proof.Pass.CopyElim

/-!
# cse refines its input (given one block's evaluation)

Lock-step simulation (`runLoop_sim`) in which the target's frame is the source's at every block
entry (`R`): cse moves no value, `g` has `f`'s blocks and values, arguments and controls become
representatives. At a block entry the source satisfies `SimAt` (frame size; `Pre`: entered from
the entry or along an edge of a tree block after which lemma (D) and `RepInv` hold). One block
step (`step`): the target collects the source's `Phi`s (`phis_target`), its schedule evaluates to
the source's frame by `BlockOK` (or panics alike), and its terminator reads controls holding the
source's registers (`stepTerm_rel`, `RepInv` and `ctrlUse`). `refines_of_rel`: related functions
refine; `cse_refines_of`: the validated pass refines its input, given `BlockOK` for its result.
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.CopyElim Dom GoFV.Opt

variable {tabs : Tables} {f g : Func} {rw : Array (Option ID)}

/-- The source-side invariant at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID)) (fr : Frame)
    (bid : ID) (i : Nat) : Prop where
  size : fr.regs.size = f.valueTab.size
  pre : Pre env tabs f rw fr bid i

/-- The simulation relation: the same frame, `SimAt` for the source. -/
def R (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID)) (frS frT : Frame)
    (bid : ID) (i : Nat) : Prop :=
  frT = frS ∧ SimAt env tabs f rw frS bid i

theorem control_rel {fr : Frame} {b b' : Block}
    (hc : ∀ (k : Nat) (c : ID), b.controls[k]? = some c →
      ∃ c', b'.controls[k]? = some c' ∧ fr.regs[c']? = fr.regs[c]?)
    {k : Nat} {v : Val} (h : Sem.control fr b k = .ok v) : Sem.control fr b' k = .ok v := by
  unfold Sem.control at h ⊢
  cases hk : b.controls[k]? with
  | none => simp [hk] at h
  | some c =>
    simp only [hk] at h
    obtain ⟨c', hc', hr⟩ := hc k c hk
    simp only [hc', hr]
    cases hx : (fr.regs[c]?).join with
    | none => simp [hx, Res.ofOption] at h
    | some x => simp [hx, Res.ofOption] at h ⊢; exact h

/-- The terminator reads only the controls: blocks with the same kind, successors and ID whose
controls hold the same registers step alike. -/
theorem stepTerm_rel {fr : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id)
    (hc : ∀ (k : Nat) (c : ID), b.controls[k]? = some c →
      ∃ c', b'.controls[k]? = some c' ∧ fr.regs[c']? = fr.regs[c]?)
    {n : Next} (h : stepTerm fr b = .ok n) : stepTerm fr b' = .ok n := by
  have hsucc : ∀ k, succ b' k = succ b k := fun k => by unfold succ; rw [hs, hid]
  have hctl : ∀ v, Sem.control fr b 0 = .ok v → Sem.control fr b' 0 = .ok v :=
    fun v h => control_rel hc h
  unfold stepTerm at h ⊢
  rw [hk]
  cases hb : b.kind <;> simp only [hb] at h ⊢
  all_goals
    try simp only [hsucc, hid]
    first
      | exact h
      | (cases hc0 : Sem.control fr b 0 with
          | ok v => rw [hctl v hc0]; rw [hc0] at h; exact h
          | panic e m => rw [hc0] at h; cases h
          | stuck msg => rw [hc0] at h; cases h)

theorem phiStep_not_panic {ctx : Ctx} {fr : Frame} {i : Nat} {z : ID} {e : Panic} {m : Sem.Mem} :
    phiStep ctx fr i z ≠ .panic e m := by
  unfold phiStep
  split
  · split
    · split
      · split <;> nofun
      · nofun
    · nofun
  · nofun

theorem filterMapM_phi_not_panic {ctx : Ctx} {fr : Frame} {i : Nat} {e : Panic} {m : Sem.Mem} :
    ∀ {l : List ID}, l.filterMapM (phiStep ctx fr i) ≠ .panic e m
  | [] => nofun
  | z :: l => by
    rw [List.filterMapM_cons]
    cases hz : phiStep ctx fr i z with
    | panic e' m' => exact absurd hz phiStep_not_panic
    | stuck msg => nofun
    | ok o =>
      cases o with
      | none => exact filterMapM_phi_not_panic
      | some p =>
        change (List.filterMapM (phiStep ctx fr i) l).bind (fun r => .ok (p :: r)) ≠ _
        cases hl : List.filterMapM (phiStep ctx fr i) l with
        | ok r => nofun
        | panic e' m' => exact absurd hl filterMapM_phi_not_panic
        | stuck msg => nofun

/-- A block entry that does not get stuck: its `Phi`s, its schedule, the schedule's evaluation. -/
theorem enterBlock_split {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {r : Res Frame} (h : enterBlock env ctx fr b i = r) (hr : ∀ msg, r ≠ .stuck msg) :
    ∃ ps o, b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList = r := by
  rw [enterBlock_eq] at h
  cases hps : b.values.toList.filterMapM (phiStep ctx fr i) with
  | panic e m => exact absurd hps filterMapM_phi_not_panic
  | stuck msg => rw [hps] at h; exact absurd h.symm (hr msg)
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = r at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; exact absurd h.symm (hr _)
    | some o => rw [ho] at h; exact ⟨ps, o, rfl, rfl, h⟩

theorem enterBlock_of_parts {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} {o : Array ID}
    (hps : b.values.toList.filterMapM (phiStep ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o) :
    enterBlock env ctx fr b i = evalAll env ctx { fr with regs := setPhis ps fr.regs } o.toList := by
  rw [enterBlock_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]
  rfl

/-- **One block step of cse's simulation.** -/
theorem step {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
    (hrel : CRel tabs f g rw) {env : Env} (hb : BlockOK env tabs f g rw) {fr : Frame} {bid : ID}
    {i : Nat} (hA : SimAt env tabs f rw fr bid i) :
    StepSim (R env tabs f rw) (blockStep env (Ctx.make tabs f) fr bid i)
      (blockStep env (Ctx.make tabs g) fr bid i) := by
  have hbt := pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hkind, -, -, hctl⟩ := hrel.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block hrel.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) fr fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps ∧
        schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f) ∧
        evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) fr gb i =
          evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := hrel.sched bid hbt.1 fb gb hfb hgb oS hsched
    refine ⟨ps, oS, oT, hps, hsched, hoT, hfilt, hev, enterBlock_of_parts
      (phis_target hwf hc hrel hA.pre hfb hgb hps) ?_⟩
    rw [hgid, hfid, sched_of_block hgb, hoT]
  -- `BlockOK` at this block
  have blk : ∀ ps oS oT,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps →
      schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f) →
      (∀ G, evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList =
          .ok G →
        evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList = .ok G ∧
          RepInv f rw G (fun a => Anc (make f) a bid)) ∧
      (∀ e m, evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList =
          .panic e m →
        evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList =
          .panic e m) := by
    intro ps oS oT hps hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    obtain ⟨hd0, hr0⟩ := phis_strict hwf hc hrel hA.pre hfb hps
    refine hb bid fb gb _ oS oT hbt hfb hgb (by simp [setPhis_size, hA.size]) hd0 hr0
      (fun z hz v hv hph => ?_) (phis_repInv hwf hc hrel hA.pre hfb hA.size hps) hoS hoT hfilt
    obtain ⟨a, y, -, -, h⟩ := hphiS z hz v hv hph (by rw [hA.size]; exact lt_of_value? hv)
    exact ⟨_, h⟩
  cases hen : enterBlock env (Ctx.make tabs f) fr fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, oS, oT, hps, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
    rw [hT, (blk ps oS oT hps hoS hoT hfilt).2 e m hev]
    rfl
  | ok G =>
  obtain ⟨ps, oS, oT, hps, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
  obtain ⟨hTG, hrep⟩ := (blk ps oS oT hps hoS hoT hfilt).1 G hev
  rw [hT, hTG]
  simp only
  obtain ⟨hD, -, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (pre_strict hc hA.pre).1 hen
  have hcs : ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
      ∃ c', gb.controls[k]? = some c' ∧ G.regs[c']? = G.regs[c]? := by
    intro k c hk
    rcases hctl k c hk with h | h
    · exact ⟨c, h, rfl⟩
    · refine ⟨_, h, ?_⟩
      have hcm : c ∈ fb.controls := Array.mem_of_getElem? hk
      obtain ⟨b', blk', hb', hcb⟩ := hwf.ctrlListed bid fb ⟨hbt.1, hfb⟩ c hcm
      obtain ⟨vc, hpl, -, -⟩ := placed_of_mem hwf hb'.1 hb'.2 hcb
      have hanc := ctrlUse hc hbt.1 hfb hbt.2 hcm
      rw [blockOf_placed hpl] at hanc
      exact hrep c vc hpl hanc
  cases hst : stepTerm G fb with
  | ok n =>
    rw [stepTerm_rel hkind hsucc (hgid.trans rfl) hcs hst]
    cases n with
    | goto e =>
      refine ⟨G, rfl, rfl, by rw [hGsz, hA.size], .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, hrep⟩⟩
      cases e; exact stepTerm_goto_mem hst
    | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **cse's output relation gives refinement**, given one block's evaluation (`BlockOK`). -/
theorem refines_of_rel (hwf : ∃ ce, WF ce f) (hwg : ∃ ce, WF ce g) (hc : CertOK f)
    (hrel : CRel tabs f g rw) (hb : ∀ env, BlockOK env tabs f g rw) : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := hwf
  obtain ⟨ce', hwg⟩ := hwg
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have hpty : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have hloc : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      hrel.vsize
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem
      rw [hpty, hloc, hsz]; rfl
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from cfgView_entry hrel.cfg]
    have hA0 : SimAt env tabs f rw (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
      ⟨by simp [Ctx.make, entryFrame], .inl rfl⟩
    exact finish_refines hd (runLoop_sim (R env tabs f rw)
      (fun frS frT bid i ⟨h1, h2⟩ => by subst h1; exact step hwf hc hrel (hb env) h2) fuel _ _ _ _
      ⟨rfl, hA0⟩ (finish_defined hd))

theorem cseCtx_tabs {penv : PassEnv} {c : CSE.Ctx} (h : cseCtx penv = .ok c) :
    c.tabs = penv.tables := by
  unfold cseCtx at h
  generalize penv.typ? "Mem" = o1 at h
  cases o1 with
  | none => cases h
  | some mem =>
    generalize penv.config? "ptrsize" = o2 at h
    rcases o2 with _ | ⟨⟨_ | ⟨t, _ | ⟨u, l⟩⟩⟩⟩
    · cases h
    · cases h
    · cases t with
      | word ps =>
        change (match ps.toInt? with
          | some ptrSize => (pure (CSE.Ctx.mk penv.tables penv.typeOrder
              (penv.tables.isMemory mem) ptrSize) : Except String CSE.Ctx)
          | _ => throw "cse: config ptrsize") = .ok c at h
        cases hn : ps.toInt? with
        | none => rw [hn] at h; cases h
        | some n => rw [hn] at h; cases h; rfl
      | str s => cases h
    · cases h

/-- **cse refines its input**, given `BlockOK` for every result related to it: the validated
pass returns the input or, on an input in the fragment, a result the strict checker accepts. -/
theorem cse_refines_of {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : csePass penv f = .ok out) (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ())
    (hfrag : cseFrag penv f = true)
    (hb : ∀ env tabs g rw, CRel tabs f g rw → BlockOK env tabs f g rw) :
    Refines out.tables out.func penv.tables f := by
  unfold cseFrag at hfrag
  simp only [csePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hc : cseCtx penv with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h hfrag
    simp only at h hfrag
    unfold cseChecked at h
    unfold CSE.inFrag at hfrag
    cases hr : GoFV.Opt.cseRw c f with
    | error e => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨g, rw⟩ := p
      rw [hr] at h hfrag
      simp only at h hfrag
      cases h
      simp only at hg ⊢
      split
      · rename_i hacc
        simp only [hacc, Bool.not_true, Bool.false_or] at hfrag
        have hrel := crel_sound hfrag
        rw [cseCtx_tabs hc] at hrel
        exact refines_of_rel ⟨ce, check_wf hf⟩ ⟨ce', check_wf (by simpa [hacc] using hg)⟩
          (certOK_of_check (check_domCert hf)) hrel (fun env => hb env _ _ _ hrel)
      · exact Refines.refl _ _

end GoFV.Proof.CSE
