import GoFV.Proof.Pass.ECPanic

/-!
# The conversion simulation (issue #28)

`step`: one block entry of the source is matched by the target's (`enter_ok`/`enter_panic`
and the terminators: the same edge on refined controls, or `Ret` outcomes related by `RR`).
`runLoop_simR`: lock-step simulation whose returns are related by `RR` (`runLoop_simE` with a
return relation). `cvSim_refines`: two checked functions related by `CvRel` refine each other
under monotone contracts.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

/-- One block step of the target matches the source's, returns of poison-free results related by
`RR`. -/
def StepSimR (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (RR : List Val → Mem → List Val → Mem → Prop) : Step → Step → Prop
  | .goto frS e, sT => ∃ frT e', sT = .goto frT e' ∧ R frS e.b e.i frT e'.b e'.i
  | .ret rs m, sT => Val.anyPoison rs = false → ∃ rs' m', sT = .ret rs' m' ∧ RR rs m rs' m'
  | .panic e m, sT => ∃ m', sT = .panic e m' ∧ Mem.Refines m m'
  | .stuck, _ => True

/-- Outcomes of `runLoop` related: returns of poison-free results by `RR` (`finish` gets stuck
on the others), panics alike with refined memories once the frames of activation `act` and later
are dropped. -/
inductive RunRel (RR : List Val → Mem → List Val → Mem → Prop) (act : Nat) : Outcome → Outcome → Prop
  | returned {rs : List Val} {m : Mem} {oT : Outcome} :
      (Val.anyPoison rs = false → ∃ rs' m', oT = .returned rs' m' ∧ RR rs m rs' m') →
      RunRel RR act (.returned rs m) oT
  | panicked (e : Panic) {m m' : Mem} : Mem.Refines (m.dropFrames act) (m'.dropFrames act) →
      RunRel RR act (.panicked e m) (.panicked e m')

/-- **Lock-step simulation** with a return relation. -/
theorem runLoop_simR {env : Env} {ctxS ctxT : Ctx} {act : Nat}
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop) (RR : List Val → Mem → List Val → Mem → Prop)
    (hsim : ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
      StepSimR R RR (blockStep env ctxS frS bS iS) (blockStep env ctxT frT bT iT)) :
    ∀ fuel frS bS iS frT bT iT, R frS bS iS frT bT iT → (runLoop env ctxS fuel frS bS iS).Defined →
      RunRel RR act (runLoop env ctxS fuel frS bS iS) (runLoop env ctxT fuel frT bT iT) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS bS iS frT bT iT hR hd
    have hs := hsim frS bS iS frT bT iT hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoop_blockStep env ctxS n frS bS iS
    obtain ⟨g2, r2, p2, -⟩ := runLoop_blockStep env ctxT n frT bT iT
    cases hS : blockStep env ctxS frS bS iS with
    | goto frS' e =>
      rw [hS] at hs
      obtain ⟨frT', e', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      rw [r1 _ _ hS]
      refine .returned fun hp => ?_
      obtain ⟨rs', m', hT, hr⟩ := hs hp
      exact ⟨rs', m', r2 _ _ hT, hr⟩
    | panic e m =>
      rw [hS] at hs
      obtain ⟨m', hT, hm⟩ := hs
      rw [p1 _ _ hS, p2 _ _ hT]
      exact .panicked e (hm.dropFrames act)
    | stuck => exact absurd hd (s1 hS)

/-! ## Terminators -/

/-- What a `Ret` terminator does with the value of its control. -/
def retNext (b : Block) (y : Val) : Res Next :=
  match y with
  | .tuple vs =>
    match vs.getLast?, vs.dropLast with
    | some (.mem m), rs =>
      if rs.any (fun | .poison => true | _ => false) then .stuck s!"b{b.id}: poison result"
      else .ok (.ret rs m)
    | _, _ => .stuck s!"b{b.id}: Ret without memory"
  | _ => .stuck s!"b{b.id}: Ret control is not a MakeResult"

theorem stepTerm_ret_eq {fr : Frame} {b : Block} (hk : b.kind = .Ret) :
    stepTerm fr b = (Sem.control fr b 0).bind (retNext b) := by
  unfold stepTerm; rw [hk]; rfl

theorem retNext_ok {b : Block} {y : Val} {n : Next} (h : retNext b y = .ok n) :
    ∃ rs m, n = .ret rs m ∧ retOf y = some (rs, m) := by
  cases y with
  | tuple vs =>
    simp only [retNext, retOf] at h ⊢
    cases hl : vs.getLast? with
    | none => simp only [hl] at h; cases h
    | some v =>
      cases v with
      | mem m' =>
        simp only [hl] at h ⊢
        split at h
        · cases h
        · rename_i hp; cases h
          refine ⟨_, _, rfl, ?_⟩
          split
          · rename_i hc; exact absurd hc hp
          · rfl
      | _ => simp only [hl] at h; cases h
  | _ => simp [retNext] at h

theorem retNext_of {b : Block} {y : Val} {rs : List Val} {m : Mem}
    (h : retOf y = some (rs, m)) : retNext b y = .ok (.ret rs m) := by
  cases y with
  | tuple vs =>
    simp only [retNext, retOf] at h ⊢
    cases hl : vs.getLast? with
    | none => simp only [hl] at h; cases h
    | some v =>
      cases v with
      | mem m' =>
        simp only [hl] at h ⊢
        split at h
        · cases h
        · rename_i hp; cases h
          split
          · rename_i hc; exact absurd hc hp
          · rfl
      | _ => simp only [hl] at h; cases h
  | _ => simp [retOf] at h

theorem control_ok {fr : Frame} {b : Block} {y : Val} (h : Sem.control fr b 0 = .ok y) :
    ∃ c, b.controls[0]? = some c ∧ fr.regs[c]? = some (some y) := by
  unfold Sem.control at h
  cases hc : b.controls[0]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    refine ⟨c, rfl, ?_⟩
    simp only [Res.ofOption] at h
    cases hr : fr.regs[c]? with
    | none => rw [hr] at h; cases h
    | some o =>
      rw [hr] at h
      cases o with
      | none => cases h
      | some y' => cases h; rfl

theorem control_of {fr : Frame} {b : Block} {c : ID} {y : Val} (hc : b.controls[0]? = some c)
    (hy : fr.regs[c]? = some (some y)) : Sem.control fr b 0 = .ok y := by
  unfold Sem.control; rw [hc]; simp [Res.ofOption, hy]

theorem stepTerm_goto_notRet {fr : Frame} {b : Block} {e : Edge}
    (h : stepTerm fr b = .ok (.goto e)) : b.kind ≠ .Ret := fun hk => by
  rw [stepTerm_ret_eq hk] at h
  cases hc : Sem.control fr b 0 with
  | ok y =>
    rw [hc] at h
    obtain ⟨rs, m, hn, -⟩ := retNext_ok (b := b) (y := y) h
    cases hn
  | panic e m => rw [hc] at h; cases h
  | stuck msg => rw [hc] at h; cases h

/-- Only a `Ret` returns. -/
theorem stepTerm_ret_kind {fr : Frame} {b : Block} {rs : List Val} {m : Mem}
    (h : stepTerm fr b = .ok (.ret rs m)) : b.kind = .Ret := by
  have hsucc : ∀ k e, Sem.succ b k ≠ .ok (.ret rs m) ∧ (Sem.succ b k = .ok e → ∃ e', e = .goto e') :=
    fun k e => by
      unfold Sem.succ
      refine ⟨fun h' => ?_, fun h' => ?_⟩ <;> cases hs : b.succs[k]? <;> simp [hs, Res.ofOption] at h'
      · exact ⟨_, h'.symm⟩
  unfold stepTerm at h
  cases hk : b.kind <;> simp only [hk] at h
  all_goals first
    | rfl
    | (cases h; done)
    | exact absurd h (hsucc _ (.ret rs m)).1
    | (exfalso
       cases hc0 : Sem.control fr b 0 with
       | ok v =>
         rw [hc0] at h
         simp only [bind, Res.bind] at h
         split at h <;> first | (cases h; done) | exact absurd h (hsucc _ (.ret rs m)).1
       | panic e m => rw [hc0] at h; cases h
       | stuck msg => rw [hc0] at h; cases h)

/-- A terminator that reads no control (`Plain`, `First`, and the kinds that get stuck) does
not depend on the frame. -/
theorem stepTerm_noCtrl {fr fr' : Frame} {b : Block} (h1 : ¬ (b.kind = .If ∨ b.kind = .JumpTable))
    (h2 : b.kind ≠ .Ret) : stepTerm fr b = stepTerm fr' b := by
  unfold stepTerm
  cases hk : b.kind <;>
    first | rfl | exact absurd (Or.inl hk) h1 | exact absurd (Or.inr hk) h1 | exact absurd hk h2

/-! ## One block step -/

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (env : Env) (tabs : Tables) (f g : Func) (cv : Cv) (frS : Frame)
    (bS : ID) (iS : Nat) (frT : Frame) (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt env tabs f g cv frS frT bS iS

/-- **One block step of the conversion simulation.** -/
theorem step (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} (hE : env.Mono)
    (hK : env.FrameKeep) {frS frT : Frame} {b : ID} {i : Nat}
    (hA : SimAt env tabs f g cv frS frT b i) :
    StepSimR (SimR env tabs f g cv) RR (blockStep env (Ctx.make tabs f) frS b i)
      (blockStep env (Ctx.make tabs g) frT b i) := by
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? b with
  | none => exact True.intro
  | some fb =>
  simp only
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨gb, m', hgb, hT, hm⟩ := enter_panic H hE hK hA hfb hen
    rw [hgb]; simp only; rw [hT]
    exact ⟨m', rfl, hm⟩
  | ok GS =>
  -- a terminator the source gets stuck at needs nothing of the target
  by_cases hstk : ∃ msg, stepTerm GS fb = .stuck msg
  · obtain ⟨msg, hst⟩ := hstk
    simp only; rw [hst]; exact True.intro
  have hret : fb.kind = .Ret → ∀ c, fb.controls[0]? = some c → ∀ y, GS.regs[c]? = some (some y) →
      ∃ rs m, retOf y = some (rs, m) := by
    intro hk c hc0 y hy
    have h' : stepTerm GS fb = retNext fb y := by
      rw [stepTerm_ret_eq hk, control_of hc0 hy]; rfl
    cases hr : retNext fb y with
    | ok n => obtain ⟨rs, m, -, hro⟩ := retNext_ok hr; exact ⟨rs, m, hro⟩
    | stuck msg => exact absurd ⟨msg, h'.trans hr⟩ hstk
    | panic e m => exact absurd (h'.trans hr) CopyElim.stepTerm_not_panic
  obtain ⟨gb, GT, hgb, B, hT, hGT, hszT, hszS, hrel, hlisted, hGSok, hGSq⟩ :=
    enter_ok H hE hK hA hfb hen hret
  obtain ⟨hD, hGSf, -⟩ := dinv_enter H.wf H.cf hbt.1 hfb hA.szS (CSE.pre_strict H.cf hA.pre).1 hen
  rw [hgb]; simp only; rw [hT]; simp only
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := CopyElim.cfgView_block H.rel.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  cases hst : stepTerm GS fb with
  | panic e m => exact absurd hst CopyElim.stepTerm_not_panic
  | stuck msg => exact True.intro
  | ok n =>
  cases n with
  | goto e =>
    have hnr := stepTerm_goto_notRet hst
    have hmono : Res.Rel Next.Refines (stepTerm GS fb) (stepTerm GT gb) := by
      by_cases hkc : fb.kind = .If ∨ fb.kind = .JumpTable
      · refine stepTerm_mono2 B.kind hsucc hgid fun k => ?_
        unfold Sem.control
        rw [B.controls]
        cases hk : fb.controls[k]? with
        | none => exact .stuck _ _
        | some c =>
          simp only [Res.ofOption]
          cases hy : GS.regs[c]? with
          | none => exact .stuck _ _
          | some o =>
            cases o with
            | none => exact .stuck _ _
            | some y =>
              obtain ⟨y', hy', hyy⟩ := hrel c y hy
              rw [B.ctrl hkc c (Array.mem_of_getElem? hk) y] at hyy
              rw [hy']
              exact .ok hyy
      · rw [stepTerm_noCtrl (fr := GT) (fr' := GS) (by rw [B.kind]; exact hkc)
          (by rw [B.kind]; exact hnr)]
        refine stepTerm_mono2 B.kind hsucc hgid fun k => ?_
        unfold Sem.control
        rw [B.controls, hgid]
        exact Res.Refines.refl _
    rw [hst] at hmono
    generalize stepTerm GT gb = rT at hmono
    cases hmono with
    | ok hn =>
      cases hn
      have hem : e ∈ fb.succs := CopyElim.stepTerm_goto_mem hst
      refine ⟨GT, e, rfl, rfl, rfl, hGT, hszS, hszT, ?_, hrel, hlisted, ?_, ?_, hGSok, hGSq⟩
      · rw [hGT, hGSf]; have := hA.img; rw [hA.frame] at this; exact this
      · cases e
        exact .inr ⟨b, fb, hbt.1, hfb, hbt.2, hem, hD, fun _ _ _ _ => rfl⟩
      · have hbmg : b ∈ g.blocks := H.blocks_eq ▸ hbt.1
        have htg : ((make g).depthOf b).isSome := by rw [H.make_eq]; exact hbt.2
        obtain ⟨hDT, -, -⟩ := dinv_enter H.wg H.cg hbmg hgb hA.szT hA.dinvT hT
        exact dinv_edge H.cg hbmg hgb htg (by rw [hsucc]; exact hem) hDT
  | ret rs m =>
    have hk := stepTerm_ret_kind hst
    rw [stepTerm_ret_eq hk] at hst
    cases hc : Sem.control GS fb 0 with
    | panic e m => rw [hc] at hst; cases hst
    | stuck msg => rw [hc] at hst; cases hst
    | ok y =>
    rw [hc] at hst
    obtain ⟨rs0, m0, hn, hro⟩ := retNext_ok (b := fb) (y := y) hst
    cases hn
    obtain ⟨c, hc0, hy⟩ := control_ok hc
    obtain ⟨y', hy', hyy⟩ := hrel c y hy
    intro hp
    obtain ⟨rs', m', hro', hRR⟩ := B.ret hk c hc0 y y' (hGSok c y hy) hyy rs m hro hp
      (ecQ_retQ hGSq hy hro)
    have hkT : gb.kind = .Ret := by rw [B.kind, hk]
    rw [stepTerm_ret_eq hkT, control_of (by rw [B.controls]; exact hc0) hy']
    exact ⟨rs', m', by simp only [Res.bind, retNext_of hro'], hRR⟩

end

/-! ## The simulation -/

theorem entry_images_size {ctx : Ctx} {args : List Val} (hl : args.length = ctx.params.size)
    (ht : ctx.paramTys.size = ctx.params.size) (env : Env) (mem : Mem) :
    (entryFrame env ctx args mem).images.size = ctx.params.size := by
  simp [entryFrame, Array.size_zip, hl, ht]

theorem paramTys_size (tabs : Tables) (f : Func) :
    (Ctx.make tabs f).paramTys.size = (Ctx.make tabs f).params.size := by
  simp [Ctx.make]

/-- **The conversion simulation**: a function `g` related to `f` by `CvRel` refines it under
monotone contracts that keep the caller's frame. -/
theorem cvSim_refines {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool}
    {front : ID → List ID} {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hrel : CvRel tabs f g cv isNew front RR) :
    RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) tabs g tabs f := by
  have H : Hyp tabs f g cv isNew front RR ce ce' := ⟨hrel, check_wf hf, check_wf hg,
    certOK_of_check (check_domCert hf), certOK_of_check (check_domCert hg)⟩
  have hc := AtomSim.ctx_eq (tabs := tabs) hrel.ownAux.symm
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by rw [hc]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by rw [hc]
  intro env hE args mem fuel hd
  refine ⟨fuel, ?_⟩
  change (runCtx env (Ctx.make tabs f) args mem fuel).Defined at hd
  change OutcomeRefines 0 (runCtx env (Ctx.make tabs f) args mem fuel)
    (runCtx env (Ctx.make tabs g) args mem fuel)
  unfold runCtx at hd ⊢
  rw [hpar, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act by rw [hc]]
  split
  · next hn => simp only [hn] at hd; exact hd.elim
  · next hn =>
    simp only [hn] at hd
    have hlen : args.length = (Ctx.make tabs f).params.size := by simpa using hn
    have hent : entryFrame env (Ctx.make tabs g) args mem =
        { entryFrame env (Ctx.make tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } := by
      rw [hc]; rfl
    have hA : SimAt env tabs f g cv (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs g) args mem) f.entry 0 := by
      refine ⟨by rw [hent], by simp [entryFrame, Ctx.make], by rw [hent]; simp, ?_,
        fun x y h => ?_, fun x y h => ?_, .inl rfl, ?_, fun x y h => ?_,
        ecQ_entry (hrel.entry env args mem)⟩
      · rw [entry_images_size (by rw [hpar]; exact hlen) (paramTys_size tabs g)]
      · simp only [entryFrame, Array.getElem?_replicate] at h; split at h <;> simp at h
      · simp only [entryFrame, Array.getElem?_replicate] at h; split at h <;> simp at h
      · rw [← H.entry_eq]; exact dinv_entry H.cg _
      · simp only [entryFrame, Array.getElem?_replicate] at h; split at h <;> simp at h
    have hrun := runLoop_simR (act := 0) (SimR env tabs f g cv) RR
      (fun frS bS iS frT bT iT ⟨hb, hi, hR⟩ => by
        subst hb; subst hi; exact step H hE.1 hE.2 hR) fuel _ _ _
      _ _ _ ⟨H.entry_eq, rfl, hA⟩ (finish_defined hd)
    rw [show (Ctx.make tabs f).act = 0 from rfl]
    change (finish (Ctx.make tabs f).outs 0 (runLoop env (Ctx.make tabs f) fuel
      (entryFrame env (Ctx.make tabs f) args mem) f.entry 0)).Defined at hd
    change OutcomeRefines 0 (finish (Ctx.make tabs f).outs 0 (runLoop env (Ctx.make tabs f) fuel
      (entryFrame env (Ctx.make tabs f) args mem) f.entry 0)) (finish (Ctx.make tabs f).outs 0
      (runLoop env (Ctx.make tabs g) fuel (entryFrame env (Ctx.make tabs g) args mem) g.entry 0))
    revert hd hrun
    generalize runLoop env (Ctx.make tabs f) fuel (entryFrame env (Ctx.make tabs f) args mem)
      f.entry 0 = oS
    generalize runLoop env (Ctx.make tabs g) fuel (entryFrame env (Ctx.make tabs g) args mem)
      g.entry 0 = oT
    intro hrun hd
    cases hrun with
    | @returned rs m oT hRR =>
      have hp : Val.anyPoison rs = false := by
        cases h : Val.anyPoison _ with
        | false => rfl
        | true => simp only [finish, h, ite_true] at hd; exact hd.elim
      obtain ⟨rs', m', rfl, hr⟩ := hRR hp
      exact hrel.finish _ _ _ _ hr hd
    | panicked e hm => exact .panicked e hm

end GoFV.Proof.EC
