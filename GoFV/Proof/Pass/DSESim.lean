import GoFV.Proof.Pass.DSEBlock
import GoFV.Proof.Pass.CSESim

/-!
# dse refines its input

Lock-step simulation (`runLoop_sim`) in which the target's frame agrees with the source's on
every value without pending ranges at each block entry (`SimAt`; the source enters from the
entry or along an edge of a tree block after which lemma (D) holds, `CSE.Pre` with no
substitution). One block step (`step`): the `Phi`s read arguments without pending ranges
(`phis_target`), the block's schedule evaluates to an agreeing frame or panics alike
(`Blk.okCase`, `Blk.panicCase`), and the terminator reads controls without pending ranges
(`stepTerm_congr`). `refines_of_rel`: functions related by `DRel` refine.
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DSE

variable {env : Env} {tabs : Tables} {f g : Func} {P : ID → List Iv}

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f : Func) (P : ID → List Iv) (frS frT : Frame)
    (bid : ID) (i : Nat) : Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = frS.regs.size
  frame : frT = { frS with regs := frT.regs }
  agree : ∀ z, P z = [] → frT.regs[z]? = frS.regs[z]?
  pre : CSE.Pre env tabs f #[] frS bid i

theorem repInv_nil (fr : Frame) (A : ID → Prop) : CSE.RepInv f #[] fr A :=
  fun _ _ _ _ => rfl

theorem control_congr {fr fr' : Frame} {b : Block}
    (h : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) (k : Nat) :
    Sem.control fr' b k = Sem.control fr b k := by
  unfold Sem.control
  cases hk : b.controls[k]? with
  | none => rfl
  | some c => simp only; rw [h c (Array.mem_of_getElem? hk)]

/-- The terminator reads only the controls' registers. -/
theorem stepTerm_congr {fr fr' : Frame} {b : Block}
    (h : ∀ c ∈ b.controls, fr'.regs[c]? = fr.regs[c]?) : stepTerm fr' b = stepTerm fr b := by
  unfold stepTerm
  rw [control_congr h 0]

theorem setPhis_congr {r r' : Array (Option Val)} (hs : r'.size = r.size) {z : ID}
    (h : r'[z]? = r[z]?) : ∀ ps : List (ID × Val), (setPhis ps r')[z]? = (setPhis ps r)[z]?
  | [] => h
  | (id, x) :: ps => by
    unfold setPhis
    rw [List.foldl_cons, List.foldl_cons]
    refine setPhis_congr (by simp [hs]) ?_ ps
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hz : id = z
    · subst hz; simp [Array.getElem?_setIfInBounds_self, hs]
    · rw [Array.getElem?_setIfInBounds_ne hz, Array.getElem?_setIfInBounds_ne hz, h]

/-- A `Phi`'s step reads arguments without pending ranges: the target's is the source's. -/
theorem phiStep_target {ce : CheckEnv} (hwf : WF ce f) (hrel : DRel tabs f g P)
    {frS frT : Frame} (hag : ∀ z, P z = [] → frT.regs[z]? = frS.regs[z]?) {bid : ID}
    {fb : Block} (hb : BlockIn f bid fb) {z : ID} (hz : z ∈ fb.values) (i : Nat) :
    phiStep (Ctx.make tabs g) frT i z = phiStep (Ctx.make tabs f) frS i z := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb hb z hz
  obtain ⟨gv, hgv, hsv⟩ := hrel.value z fv hfv
  unfold phiStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl,
    hfv, hgv]
  rcases hsv with hs | he
  · obtain ⟨-, hop, -, -, hty, -, hargs⟩ := sameV_spec hs
    rw [hop, hargs, tys_of_value hgv, tys_of_value hfv, hty]
    by_cases hph : fv.op = .Phi
    · simp only [hph, beq_self_eq_true, ↓reduceIte]
      cases ha : fv.args[i]? with
      | none => rfl
      | some a =>
        simp only
        have hc : P a = [] := by
          refine Classical.byContradiction fun hp => ?_
          obtain ⟨hne, -⟩ := uses_spec hfv (hrel.uses z (lt_of_value? hfv))
            (Array.mem_of_getElem? ha) hp
          exact hne hph
        rw [hag a hc]
    · have : (fv.op == .Phi) = false := by simpa using hph
      simp only [this, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨hop, hgc, -⟩ := elimV_spec he
    have h1 : (gv.op == .Phi) = false := by rw [hgc]; rfl
    have h2 : (fv.op == .Phi) = false := by rcases hop with h | h | h <;> rw [h] <;> rfl
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

theorem filterMapM_eq {F G : ID → Res (Option (ID × Val))} :
    ∀ {l : List ID}, (∀ z ∈ l, G z = F z) → l.filterMapM G = l.filterMapM F
  | [], _ => rfl
  | z :: l, h => by
    rw [List.filterMapM_cons, List.filterMapM_cons, h z List.mem_cons_self,
      filterMapM_eq fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The `Phi`s keep lemma (D) for the strict ancestors.** -/
theorem phis_strict {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {fr : Frame} {bid : ID}
    {i : Nat} (hpre : CSE.Pre env tabs f #[] fr bid i) {fb : Block}
    (hfb : f.block? bid = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid)
      { fr with regs := setPhis ps fr.regs } := by
  have hp := hc.parents
  have hbt := CSE.pre_tree hwf hc hpre
  obtain ⟨hd, -⟩ := CSE.pre_strict hc hpre
  obtain ⟨-, -, hkeep, -⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hout : ∀ z, z ∉ fb.values → (setPhis ps fr.regs)[z]? = fr.regs[z]? :=
    fun z hz => hkeep z (.inl hz)
  have hin : ∀ z v, f.value? z = some v → z ∈ fb.values → v.block = bid := fun z v hv hz => by
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hv] at hv'; cases hv'; exact hvb
  intro x v hx hb
  obtain ⟨y, hy, hev⟩ := hd x v hx hb
  refine ⟨y, by rw [show ({ fr with regs := setPhis ps fr.regs } : Frame).regs = _ from rfl,
    hout x fun hz => hb.2 (hin x v hx.1 hz), hy], fun hne => ?_⟩
  rw [← hev hne]
  refine (evalValue_congr rfl fun a ha => ?_).symm
  obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
  have hua := uses hc hvb hblk (Anc.left hp hb.1) hxv hv hne ha
  refine (hout a fun ham => ?_).symm
  obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ a ham
  have hba : blockOf f a = bid := by unfold blockOf; rw [hva]; exact hvab
  rw [hba] at hua
  exact hb.2 (Anc.antisymm hp hb.1 hua)

/-- **One block step of dse's simulation.** -/
theorem step {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : DRel tabs f g P)
    {frS frT : Frame} {bid : ID} {i : Nat} (hA : SimAt env tabs f P frS frT bid i) :
    StepSim (fun frS frT bid i => SimAt env tabs f P frS frT bid i)
      (blockStep env (Ctx.make tabs f) frS bid i) (blockStep env (Ctx.make tabs g) frT bid i) := by
  have hbt := CSE.pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hkind, hvals, hctl, hclean⟩ := hrel.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block hrel.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
        schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps frT.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := hrel.sched bid hbt.1 fb gb hfb hgb oS hsched
    refine ⟨ps, oS, oT, hps, hsched, hoT, hfilt, hev, CSE.enterBlock_of_parts ?_ ?_⟩
    · rw [hvals, filterMapM_eq fun z hz => phiStep_target hwf hrel hA.agree ⟨hbt.1, hfb⟩
        (Array.mem_toList_iff.1 hz) i]
      exact hps
    · rw [hgid, hfid, sched_of_block hgb, hoT]
  -- the block's evaluation
  have blk : ∀ ps oS oT,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps →
      schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) →
      Blk env tabs f g P bid fb gb { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis ps frT.regs } oS oT := by
    intro ps oS oT hps hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    refine ⟨hrel, ⟨ce, hwf⟩, hc, hbt, hfb, hgb, by simp [setPhis_size, hA.size],
      phis_strict hwf hc hA.pre hfb hps, fun z hz v hv hph => ?_, ?_,
      by simp [setPhis_size, hA.sizeT], fun z hz => ?_, hoS, hoT, hfilt⟩
    · obtain ⟨a, y, -, -, h⟩ := hphiS z hz v hv hph (by rw [hA.size]; exact lt_of_value? hv)
      exact ⟨_, h⟩
    · conv => lhs; rw [hA.frame]
    · exact setPhis_congr hA.sizeT (hA.agree z hz) ps
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, oS, oT, hps, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
    rw [hT, (blk ps oS oT hps hoS hoT hfilt).panicCase hev]
    rfl
  | ok G =>
  obtain ⟨ps, oS, oT, hps, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
  obtain ⟨GT, hGT, hGTf, hGTs, hGTa⟩ := (blk ps oS oT hps hoS hoT hfilt).okCase hev
  rw [hT, hGT]
  simp only
  obtain ⟨hD, -, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  have hst : stepTerm GT gb = stepTerm G fb := by
    rw [stepTerm_congr (b := gb) (fr := G) (fun c hcm => hGTa c (hclean c (hctl ▸ hcm)))]
    unfold stepTerm
    rw [hkind]
    have hsucc' : ∀ k, succ gb k = succ fb k := fun k => by unfold succ; rw [hsucc, hgid]
    have hctl' : ∀ k, Sem.control G gb k = Sem.control G fb k := fun k => by
      unfold Sem.control; rw [hctl, hgid]
    simp only [hsucc', hctl', hgid]
  rw [hst]
  cases hstp : stepTerm G fb with
  | ok n =>
    cases n with
    | goto e =>
      refine ⟨GT, rfl, by rw [hGsz, hA.size], by rw [hGTs], hGTf, hGTa, .inr ⟨bid, fb, hbt.1, hfb,
        hbt.2, ?_, hD, repInv_nil _ _⟩⟩
      cases e; exact stepTerm_goto_mem hstp
    | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hstp stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **dse's output relation gives refinement.** -/
theorem refines_of_rel (hwf : ∃ ce, WF ce f) (hc : CertOK f) (hrel : DRel tabs f g P) :
    Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := hwf
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
      unfold entryFrame frameMem frameAllocs
      rw [hpty, hloc, hsz]; rfl
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from cfgView_entry hrel.cfg]
    have hA0 : SimAt env tabs f P (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
      ⟨by simp [Ctx.make, entryFrame], rfl, rfl, fun _ _ => rfl, .inl rfl⟩
    exact finish_refines hd (runLoop_sim (fun frS frT bid i => SimAt env tabs f P frS frT bid i)
      (fun frS frT bid i h => step hwf hc hrel h) fuel _ _ _ _ hA0 (finish_defined hd))

end GoFV.Proof.DSE
