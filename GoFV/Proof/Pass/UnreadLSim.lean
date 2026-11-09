import GoFV.Proof.Pass.UnreadLBlock
import GoFV.Proof.Pass.DeadRelL

variable [GoFV.SSA.Sem.Addrs]

/-!
# elim unread autos on `runL`: the simulation

Dead auto elim's simulation (`GoFV.Proof.Pass.DAESim`) for `runL`: lock-step (`runLoopL_simD`)
in which, at each block entry (`SimAtL`), the target's registers are related to the source's
(`VR`: equal, or memories equal outside the eliminated frame temporaries `UE E`), the source's
registers avoid `UE E` and are typed (`SPrL`), the frame's inputs avoid `UE E`, and lemma (D)
holds at the predecessor (`PreL`). One block step (`stepL`): related `Phi`s (`phisL_rel`), the
block's schedule (`UBlk.okCase`, `UBlk.panicCase`), the terminator (`stepTermL_relU`: an arm64
kind reads a control that is neither a memory nor a tuple, `Arm64.taken`/`Arm64.reg` of those
are `none`, so the related target control is equal). The entry frame satisfies `SimAtL` when
the run's inputs avoid every frame temporary (`entryL_ok`); `DAE.finish_rel` turns the related
outcomes into refinement (`refinesL_of_urel`).
-/

namespace GoFV.Proof.UnreadL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.DAE GoFV.Proof.CopyElim GoFV.Opt

variable {env : Env} {tabs : Tables} {f g : Func} {E : List AuxRef}

/-! ## Block entries -/

/-- How block `bid` is entered along edge `i` with frame `fr`: it is the entry, or a successor
of a tree block `p` after which `fr` holds lemma (D) for `p`'s ancestors. -/
def PreL (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (bid : ID) (i : Nat) : Prop :=
  bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
    DInvL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) (fun a => Anc (make f) a p) fr

theorem preL_tree {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {fr : Frame} {bid : ID}
    {i : Nat} (h : PreL env tabs f fr bid i) : Tree f bid := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth hc.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge hc hp hpb hpt he).2.1⟩

theorem preL_strict (hc : CertOK f) {fr : Frame} {bid : ID} {i : Nat}
    (h : PreL env tabs f fr bid i) :
    DInvL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, hd⟩
  · exact dinvL_entry hc fr
  · exact dinvL_edge hc hp hpb hpt he hd

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAtL (env : Env) (tabs : Tables) (f : Func) (E : List AuxRef) (frS frT : Frame)
    (bid : ID) (i : Nat) : Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = frS.regs.size
  frame : frT = { frS with regs := frT.regs }
  agree : RegsRel (UE E) frS.regs frT.regs
  pr : RegsP (SPrL tabs f E) frS
  fok : FrameOK (UE E) frS
  pre : PreL env tabs f frS bid i

/-! ## `Phi`s -/

/-- One `Phi` step in source and target. -/
theorem phiStepL_rel (R : URel tabs f g E) {frS frT : Frame}
    (hag : RegsRel (UE E) frS.regs frT.regs) (i : Nat) {z : ID} {o : Option (ID × Val)}
    (h : phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i z = .ok o) :
    ∃ o', phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs g) frT i z = .ok o' ∧
      ((o = none ∧ o' = none) ∨ ∃ x x', o = some (z, x) ∧ o' = some (z, x') ∧ VR (UE E) x x') := by
  unfold phiStepL at h ⊢
  rw [makeL_f] at h ⊢
  rw [tysL_eq R z]
  cases hfv : f.value? z with
  | none => rw [hfv] at h; cases h
  | some fv =>
    rw [hfv] at h
    obtain ⟨gv, hgv, hk⟩ := R.value z fv hfv
    rw [hgv]
    dsimp only at h ⊢
    have hsg : DSE.sameV fv gv = true ∨ (fv.op ≠ .Phi ∧ gv.op ≠ .Phi) := by
      rcases hk with ⟨hs, -⟩ | ⟨he, -⟩
      · exact .inl hs
      · obtain ⟨hop, hgc, -⟩ := elimV_spec he
        refine .inr ⟨fun hp => ?_, by rw [hgc]; nofun⟩
        rw [hp] at hop
        simp [elimOps] at hop
    rcases hsg with hs | ⟨hf, hg⟩
    · obtain ⟨-, hop, -, -, -, -, hargs⟩ := DSE.sameV_spec hs
      rw [hop, hargs]
      by_cases hph : fv.op = .Phi
      · simp only [hph, beq_self_eq_true, ↓reduceIte] at h ⊢
        cases ha : fv.args[i]? with
        | none => rw [ha] at h; cases h
        | some a =>
          rw [ha] at h
          simp only at h ⊢
          cases hx : frS.regs[a]? with
          | none => rw [hx] at h; cases h
          | some ox =>
            cases ox with
            | none => rw [hx] at h; cases h
            | some x =>
              rw [hx] at h
              simp only [Option.join] at h
              cases h
              obtain ⟨x', hx', hv⟩ := hag a x hx
              rw [hx']
              exact ⟨_, rfl, .inr ⟨_, _, rfl, rfl, VR.mdRetype hv _ _⟩⟩
      · have h1 : (fv.op == .Phi) = false := by simpa using hph
        simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
        cases h
        exact ⟨none, rfl, .inl ⟨rfl, rfl⟩⟩
    · have h1 : (fv.op == .Phi) = false := by simpa using hf
      have h2 : (gv.op == .Phi) = false := by simpa using hg
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h
      exact ⟨none, rfl, .inl ⟨rfl, rfl⟩⟩

/-- **The target collects related `Phi`s.** -/
theorem phisL_rel (R : URel tabs f g E) {frS frT : Frame}
    (hag : RegsRel (UE E) frS.regs frT.regs) (i : Nat) :
    ∀ {l : List ID} {ps : List (ID × Val)},
      l.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) = .ok ps →
      ∃ ps', l.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs g) frT i) = .ok ps' ∧
        PRel (UE E) ps ps'
  | [], ps, h => by
    simp only [List.filterMapM_nil] at h
    cases h; exact ⟨[], rfl, .nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h ⊢
    cases hz : phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      obtain ⟨o', ho', hrel⟩ := phiStepL_rel R hag i hz
      rw [ho']
      cases hl : l.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) with
      | panic e m =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | stuck msg =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | ok rest =>
        obtain ⟨rest', hl', hr⟩ := phisL_rel R hag i hl
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩
        · simp only [bind, Res.bind, hl] at h
          cases h
          exact ⟨rest', by simp only [bind, Res.bind, hl'], hr⟩
        · simp only [bind, Res.bind, hl, pure] at h
          cases h
          exact ⟨_, by simp only [bind, Res.bind, hl', pure], .cons hv hr⟩

/-- **The source's `Phi`s keep its register property.** -/
theorem phisL_pr {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {fb : Block} (hb : BlockIn f bid fb)
    {fr : Frame} (hpr : RegsP (SPrL tabs f E) fr) {i : Nat} {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) fr i) =
      .ok ps) :
    RegsP (SPrL tabs f E) { fr with regs := setPhis ps fr.regs } := by
  have hnd := hwf.valuesNodup bid fb hb
  obtain ⟨hsz, hsome, hkeep, hphi⟩ := phisL_spec hnd hps
  intro z y hz
  change (setPhis ps fr.regs)[z]? = some (some y) at hz
  by_cases hin : z ∈ fb.values
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsome z hin)
    by_cases hph : v.op = .Phi
    · have hlt : z < fr.regs.size := by
        rw [← hsz]
        rcases Nat.lt_or_ge z (setPhis ps fr.regs).size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hz; cases hz
      obtain ⟨a, x, -, hx, hset⟩ := hphi z hin v hv hph hlt
      rw [hset] at hz
      cases hz
      exact ⟨mdRetype_av (tempU_UE E) _ _ (hpr a x hx).1, LMode.retype_idem _ _ _⟩
    · rw [hkeep z (.inr ⟨v, hv, hph⟩)] at hz
      exact hpr z y hz
  · rw [hkeep z (.inl hin)] at hz
    exact hpr z y hz

/-- **The `Phi`s keep lemma (D) for the strict ancestors.** -/
theorem phisL_strict {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {fr : Frame} {bid : ID}
    {i : Nat} (hpre : PreL env tabs f fr bid i) {fb : Block} (hfb : f.block? bid = some fb)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) fr i) =
      .ok ps) :
    DInvL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid)
      { fr with regs := setPhis ps fr.regs } := by
  have hp := hc.parents
  have hbt := preL_tree hwf hc hpre
  have hd := preL_strict hc hpre
  obtain ⟨-, -, hkeep, -⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hout : ∀ z, z ∉ fb.values → (setPhis ps fr.regs)[z]? = fr.regs[z]? :=
    fun z hz => hkeep z (.inl hz)
  have hin : ∀ z v, f.value? z = some v → z ∈ fb.values → v.block = bid := fun z v hv hz => by
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hv] at hv'; cases hv'; exact hvb
  intro x v hx hb
  obtain ⟨y, hy, hev⟩ := hd x v hx hb
  rw [makeL_f] at hx
  refine ⟨y, by rw [show ({ fr with regs := setPhis ps fr.regs } : Frame).regs = _ from rfl,
    hout x fun hz => hb.2 (hin x v hx.1 hz), hy], fun hne => ?_⟩
  rw [← hev hne]
  refine (evalValueL_congr rfl fun a ha => ?_).symm
  obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
  have hua := uses hc hvb hblk (Anc.left hp hb.1) hxv hv hne ha
  refine (hout a fun ham => ?_).symm
  obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ a ham
  have hba : blockOf f a = bid := by unfold blockOf; rw [hva]; exact hvab
  rw [hba] at hua
  exact hb.2 (Anc.antisymm hp hb.1 hua)

/-! ## Terminators -/

theorem taken_mem (k : BlockKind) (a : Int64) (m : Mem) : Arm64.taken k a (.mem m) = none := by
  cases k <;> rfl

theorem taken_tuple (k : BlockKind) (a : Int64) (vs : List Val) :
    Arm64.taken k a (.tuple vs) = none := by
  cases k <;> rfl

/-- An arm64 terminator that continues reads a control that is neither a memory nor a tuple. -/
theorem armCtrl_plain {fr : Frame} {b : Block} {n : Next} (ha : b.kind.isArm64 = true)
    (h : stepTermL fr b = .ok n) {v : Val} (hc : Sem.control fr b 0 = .ok v) :
    (∀ m, v ≠ .mem m) ∧ (∀ vs, v ≠ .tuple vs) := by
  unfold stepTermL at h
  simp only [ha, ↓reduceIte, bind, Res.bind, hc] at h
  constructor
  · rintro m rfl
    split at h
    · simp only [Arm64.reg] at h; cases h
    · simp only [taken_mem] at h; cases h
  · rintro vs rfl
    split at h
    · simp only [Arm64.reg] at h; cases h
    · simp only [taken_tuple] at h; cases h

/-- **The terminators on related controls** under `runL`: the same edge, or related results and
memories. -/
theorem stepTermL_relU {U : Blk → Prop} {G GT : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id) (hc : b'.controls = b.controls)
    (hai : b'.auxInt = b.auxInt) (hreg : RegsRel U G.regs GT.regs) :
    (∀ e, stepTermL G b = .ok (.goto e) → stepTermL GT b' = .ok (.goto e)) ∧
    (∀ rs m, stepTermL G b = .ok (.ret rs m) →
      ∃ rs' m', stepTermL GT b' = .ok (.ret rs' m') ∧ VRL U rs rs' ∧ Mem.EqOff U m m') := by
  by_cases ha : b.kind.isArm64 = true
  · have hsucc : ∀ k, succ b' k = succ b k := fun k => by unfold succ; rw [hs, hid]
    have arm : ∀ n, stepTermL G b = .ok n → stepTermL GT b' = .ok n := by
      intro n h
      obtain ⟨v, k, hcv, hsk, hT⟩ := Dead.stepTermL_arm ha h
      obtain ⟨v', hv', hvr⟩ := control_rel hc hreg hcv
      obtain ⟨hm, ht⟩ := armCtrl_plain ha h hcv
      rw [hvr.eq hm ht] at hv'
      rw [hT GT b' hk hai hv', hsucc, hsk]
    refine ⟨fun e h => arm _ h, fun rs m h => ?_⟩
    obtain ⟨-, k, -, hsk, -⟩ := Dead.stepTermL_arm ha h
    exact absurd hsk succ_not_ret
  · have ha' : b'.kind.isArm64 = false := by rw [hk]; exact Bool.eq_false_iff.2 ha
    rw [stepTermL_generic G (Bool.eq_false_iff.2 ha), stepTermL_generic GT ha']
    exact stepTerm_rel hk hs hid hc hreg

/-! ## One block step -/

/-- **One block step of elim unread autos' simulation.** -/
theorem stepL (hfs : env.FrameSafe) {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
    (R : URel tabs f g E) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : SimAtL env tabs f E frS frT bid i) :
    StepRelD (UE E) (fun frS frT bid i => SimAtL env tabs f E frS frT bid i)
      (blockStepL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS bid i)
      (blockStepL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) frT bid i) := by
  have hbt := preL_tree hwf hc hA.pre
  unfold blockStepL
  simp only [makeL_f]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hkind, hvals, hctl, hai⟩ := R.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block R.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS fb i = r →
      (∀ msg, r ≠ .stuck msg) →
      ∃ ps psT oS oT,
        fb.values.toList.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) =
          .ok ps ∧
        PRel (UE E) ps psT ∧ schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) ∧
        evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f)
          { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
        enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g) frT gb i =
          evalAllL ⟨f.lowered, false⟩ env (Ctx.makeL tabs g)
            { frT with regs := setPhis psT frT.regs } oT.toList := by
    intro r hen hr
    rw [enterBlockL_eq] at hen
    cases hps : fb.values.toList.filterMapM
        (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) with
    | panic e m => exact absurd hps filterMapM_phiL_not_panic
    | stuck msg => rw [hps] at hen; exact absurd hen.symm (hr msg)
    | ok ps =>
      rw [hps] at hen
      change (Res.ofOption _ ((Ctx.makeL tabs f).sched[fb.id]?).join).bind _ = r at hen
      rw [hfid, sched_of_blockL hfb] at hen
      cases hoS : schedule f fb with
      | none => rw [hoS] at hen; exact absurd hen.symm (hr _)
      | some oS =>
        rw [hoS] at hen
        obtain ⟨oT, hoT, hfilt⟩ := R.sched bid hbt.1 fb gb hfb hgb oS hoS
        obtain ⟨psT, hpsT, hpr⟩ := phisL_rel R hA.agree i hps
        refine ⟨ps, psT, oS, oT, rfl, hpr, rfl, hoT, hfilt, hen, ?_⟩
        rw [enterBlockL_eq, hvals, hpsT]
        change (Res.ofOption _ ((Ctx.makeL tabs g).sched[gb.id]?).join).bind _ = _
        rw [hgid, hfid, sched_of_blockL hgb, hoT]
        rfl
  -- the block's evaluation
  have blk : ∀ ps psT oS oT,
      fb.values.toList.filterMapM (phiStepL ⟨f.lowered, false⟩ (Ctx.makeL tabs f) frS i) =
        .ok ps →
      PRel (UE E) ps psT → schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) →
      UBlk env tabs f g E bid fb gb { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis psT frT.regs } oS oT := by
    intro ps psT oS oT hps hpr hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    refine ⟨R, hfs, ⟨ce, hwf⟩, hc, hbt, hfb, hgb, by simp [setPhis_size, hA.size],
      phisL_strict hwf hc hA.pre hfb hps, fun z hz v hv hph => ?_, ?_,
      by simp [setPhis_size, hA.sizeT], setPhis_rel hpr hA.agree hA.sizeT,
      phisL_pr hwf ⟨hbt.1, hfb⟩ hA.pr hps,
      ⟨hA.fok.images, hA.fok.closure, hA.fok.mem0⟩, hoS, hoT, hfilt⟩
    · obtain ⟨a, y, -, -, h⟩ := hphiS z hz v (by rw [makeL_f]; exact hv) hph
        (by rw [hA.size]; exact lt_of_value? hv)
      exact ⟨_, h⟩
    · conv => lhs; rw [hA.frame]
  cases hen : enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, psT, oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
    obtain ⟨m', hm', hEq, heA, hmA⟩ := (blk ps psT oS oT hps hpr hoS hoT hfilt).panicCase hev
    rw [hT, hm']
    exact ⟨m', rfl, hEq, heA, hmA⟩
  | ok G =>
  obtain ⟨ps, psT, oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
  have K := blk ps psT oS oT hps hpr hoS hoT hfilt
  obtain ⟨GT, hGT, hGTf, hGTs, hGTa⟩ := K.okCase hev
  have hGpr : RegsP (SPrL tabs f E) G := K.srcPr (fun x hx => K.memS.1 hx) hev
  rw [hT, hGT]
  simp only
  obtain ⟨hD, hGfr, hGsz⟩ := dinvL_enter hwf hc hbt.1 hfb hA.size (preL_strict hc hA.pre) hen
  obtain ⟨hgo, hret⟩ := stepTermL_relU (G := G) (GT := GT) (b := fb) (b' := gb) hkind hsucc hgid
    hctl hai hGTa
  cases hstp : stepTermL G fb with
  | ok n =>
    cases n with
    | goto e =>
      rw [hgo e hstp]
      refine ⟨GT, rfl, by rw [hGsz, hA.size], by rw [hGTs], hGTf, hGTa, hGpr, ?_,
        .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD⟩⟩
      · rw [hGfr]; exact ⟨hA.fok.images, hA.fok.closure, hA.fok.mem0⟩
      · cases e; exact Dead.stepTermL_goto_mem hstp
    | ret rs m =>
      obtain ⟨rs', m', h1, h2, h3⟩ := hret rs m hstp
      rw [h1]
      exact ⟨rs', m', rfl, h2, h3⟩
  | panic e m => exact absurd hstp Dead.stepTermL_not_panic
  | stuck msg => exact True.intro

/-! ## The loop, the entry and the refinement -/

/-- **Lock-step simulation** over `runLoopL` with related outcomes (`DAE.runLoop_simD`). -/
theorem runLoopL_simD {U : Blk → Prop} {mdS mdT : LMode} {ctxS ctxT : Ctx}
    (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepRelD U R (blockStepL mdS env ctxS frS bid i) (blockStepL mdT env ctxT frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoopL mdS env ctxS fuel frS bid i).Defined →
      ORel U (runLoopL mdS env ctxS fuel frS bid i) (runLoopL mdT env ctxT fuel frT bid i) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS frT bid i hR hd
    have hs := hsim frS frT bid i hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoopL_blockStep mdS env ctxS n frS bid i
    obtain ⟨g2, r2, p2, -⟩ := runLoopL_blockStep mdT env ctxT n frT bid i
    cases hS : blockStepL mdS env ctxS frS bid i with
    | goto frS' e =>
      rw [hS] at hs
      obtain ⟨frT', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      obtain ⟨rs', m', hT, hr, hm⟩ := hs
      rw [r1 _ _ hS, r2 _ _ hT]
      exact .ret hr hm
    | panic e m =>
      rw [hS] at hs
      obtain ⟨m', hT, hm, he, hmA⟩ := hs
      rw [p1 _ _ hS, p2 _ _ hT]
      exact .panic e hm he hmA
    | stuck => exact absurd hd (s1 hS)

private theorem defers_makeL_unread (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).defers = deferInfo tabs := by
  unfold Ctx.makeL; split <;> rfl

/-- **The entry frame** satisfies `SimAtL` when the run's inputs avoid every frame temporary. -/
theorem entryL_ok {args : List Val} {mem : Mem} (hinit : InitAvoids env args mem) :
    SimAtL env tabs f E (entryFrame env (Ctx.makeL tabs f) args mem)
      (entryFrame env (Ctx.makeL tabs f) args mem) f.entry 0 := by
  have h0 := DAE.entry_ok (env := env) (tabs := tabs) (f := f) (T := fun _ => none) (E := E) hinit
  rw [entryFrame_makeL]
  refine ⟨h0.size, rfl, rfl, h0.agree, fun z y h => ?_, h0.fok, .inl rfl⟩
  simp [entryFrame, Array.getElem?_replicate] at h

/-- The open-coded defer variables are not eliminated (`URel.nodefer`). -/
theorem deferAvoidL (R : URel tabs f g E) : DeferRel.DeferAvoid (UE E) (deferInfo tabs) 0 := by
  have hv := DeferRel.deferInfo_vars tabs
  refine ⟨fun nb hb hu => ?_, fun i sn hs hu => ?_⟩
  · obtain ⟨n, hnE, he⟩ := hu
    split at he
    · cases he
    · cases he
      have := R.nodefer _ hnE
      rw [hv.1 nb hb] at this; cases this
  · obtain ⟨n, hnE, he⟩ := hu
    split at he
    · cases he
    · cases he
      have := R.nodefer _ hnE
      rw [hv.2 i sn hs] at this; cases this

/-- **elim unread autos' output relation gives refinement under `runL`**, for frame-safe
contracts and inputs that avoid the frame temporaries. -/
theorem refinesL_of_urel {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (R : URel tabs f g E) :
    RefinesLFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem) tabs g tabs f := by
  have hpar : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := (ctxL_facts R).2.1
  have hpty : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
    simp only [Ctx.make, abiParams, R.ownAux]
  have hloc : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
    simp only [Ctx.make, abiParams, R.ownAux]
  have houts : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
    rw [outs_makeL, outs_makeL]
    simp only [Ctx.make, abiParams, R.ownAux]
  intro env args mem ⟨hfs, hinit⟩ fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [R.low, hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size := R.vsize
    have hentry : entryFrame env (Ctx.makeL tabs g) args mem =
        entryFrame env (Ctx.makeL tabs f) args mem := by
      rw [entryFrame_makeL, entryFrame_makeL]
      unfold entryFrame frameMem frameAllocs
      rw [hpty, hloc, hsz]; rfl
    rw [hentry, houts, defers_makeL_unread, defers_makeL_unread, act_makeL0, act_makeL0,
      makeL_f, makeL_f, cfgView_entry R.cfg]
    rw [makeL_f, act_makeL0, defers_makeL_unread] at hd
    exact finish_rel hfs (tempU0_UE E) (deferAvoidL R) hd (runLoopL_simD
      (fun frS frT bid i => SimAtL env tabs f E frS frT bid i)
      (fun frS frT bid i h => stepL hfs hwf hc R h) fuel _ _ _ _ (entryL_ok hinit)
      (finish_defined hd))

end GoFV.Proof.UnreadL
