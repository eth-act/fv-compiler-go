import GoFV.Proof.Pass.CSELBlock
import GoFV.Proof.Pass.CSESim
import GoFV.Proof.Pass.CopyElimL

/-!
# lowered cse refines its input on `runL`

`GoFV.Proof.CSE`'s simulation for `runL`: lock-step (`runLoopL_sim`) with the target's frame the
source's at every block entry (`RL`). A block is entered from the entry or along an edge of a
tree block after which lemma (D) (`DInvL`) and `RepInv` hold (`PreL`); the target collects the
source's `Phi`s (`phisL_target`), its schedule evaluates to the source's frame by `BlockOKL` (or
panics alike), and its terminator reads controls holding the source's registers
(`CopyElim.stepTermL_copyRel`: same kind, successors, `auxInt`). `refinesL_of_rel`: functions
related by `CRelL` refine under `runL`; `loweredCse_refinesL`: the `lowered cse` pass refines
its input when the checker `CSEL.crel` accepts its result (`CSEL.frag`).
-/

namespace GoFV.Proof.CSEL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.CopyElim GoFV.Proof.CSE Dom GoFV.Opt

variable {md : LMode} {tabs : Tables} {f g : Func} {rw : Array (Option ID)}

/-- How block `bid` is entered along edge `i` with frame `fr` (`CSE.Pre` for `runL`). -/
def PreL (md : LMode) (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID)) (fr : Frame)
    (bid : ID) (i : Nat) : Prop :=
  bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a p) fr ∧
    RepInv f rw fr (fun a => Anc (make f) a p)

theorem preL_tree {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (h : PreL md env tabs f rw fr bid i) : Tree f bid := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth hc.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge hc hp hpb hpt he).2.1⟩

theorem preL_strict (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (h : PreL md env tabs f rw fr bid i) :
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr ∧
      RepInv f rw fr (fun a => Anc (make f) a bid ∧ a ≠ bid) := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, hd, hr⟩
  · exact ⟨dinvL_entry hc fr, fun _ _ _ ⟨ha, hne⟩ => absurd (anc_of_entry hc.parents ha) hne⟩
  · have hup : ∀ a, (Anc (make f) a bid ∧ a ≠ bid) → Anc (make f) a p := fun _ ⟨ha, hne⟩ =>
      Anc.trans hc.parents (ha.up hc.parents hne) (edge hc hp hpb hpt he).2.2
    exact ⟨hd.mono hup, fun x v hx hb => hr x v hx (hup _ hb)⟩

/-- The argument a `Phi` reads holds its representative's register. -/
theorem phiArgL_rep {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (hpre : PreL md env tabs f rw fr bid i) (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb) {z : ID} (hz : z ∈ fb.values) {fv : Value}
    (hfv : f.value? z = some fv) (hph : fv.op = .Phi) {a : ID} (ha : fv.args[i]? = some a) :
    fr.regs[Opt.CSE.rep rw a]? = fr.regs[a]? := by
  rcases hpre with hbe | ⟨p, blkp, hp, hpb, hpt, he, -, hrep⟩
  · have hsz := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
    have hilt := (Array.getElem?_eq_some_iff.1 ha).1
    subst hbe
    have := hwf.entryPreds fb hfb
    omega
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, c, hcb, hcp⟩ := hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj
    rw [hfb] at hcb; cases hcb
    have hanc := phiUse hc hbt.1 hfb hbt.2 hz hfv hph ha hcp hpt
    obtain ⟨va, hpl, hba⟩ := placed_arg hwf ⟨hbt.1, hfb⟩ hz hfv (Array.mem_of_getElem? ha)
    rw [hba] at hanc
    exact hrep a va hpl hanc

/-- One `Phi` step of the target gives the source's. -/
theorem phiStepL_target {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRelL tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : PreL md env tabs f rw fr bid i)
    (hbt : Tree f bid) {fb : Block} (hfb : f.block? bid = some fb) {z : ID} (hz : z ∈ fb.values)
    {o : Option (ID × Val)} (h : phiStepL md (Ctx.makeL tabs f) fr i z = .ok o) :
    phiStepL md (Ctx.makeL tabs g) fr i z = .ok o := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
  obtain ⟨gv, hgv, -, hop, -, -, hty, -, hargs⟩ := hrel.value z fv hfv
  cases o with
  | none =>
    obtain ⟨v, hv, hne⟩ := phiStepL_none h
    rw [makeL_f, hfv] at hv; cases hv
    unfold phiStepL
    rw [makeL_f]
    simp only [hgv, show (gv.op == .Phi) = false by simpa [hop] using hne]
    rfl
  | some q =>
    obtain ⟨hq1, v, a, y, hv, hph, ha, hy, hq2⟩ := phiStepL_some h
    rw [makeL_f, hfv] at hv; cases hv
    rw [hph] at hargs
    have hga : gv.args[i]? = some (Opt.CSE.rep rw a) := by
      rw [argsRel_phi hargs, Array.getElem?_map, ha]; rfl
    have hra := phiArgL_rep hwf hc hpre hbt hfb hz hfv hph ha
    have htys : (Ctx.makeL tabs g).tys[z]? = (Ctx.makeL tabs f).tys[z]? :=
      tysL_rel hrel.lowered hfv hgv (by rw [hty])
    obtain ⟨z', x⟩ := q
    simp only at hq1 hq2
    subst hq1 hq2
    unfold phiStepL
    rw [makeL_f]
    simp only [hgv, show (gv.op == .Phi) = true by simp [hop, hph], ite_true, hga, hra, hy,
      Option.join, htys]
    rfl

/-- **The target collects the source's `Phi`s.** -/
theorem phisL_target {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRelL tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : PreL md env tabs f rw fr bid i)
    {fb gb : Block} (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps) :
    gb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs g) fr i) = .ok ps := by
  have hbt := preL_tree hwf hc hpre
  obtain ⟨gb', hgb', -, hv, -⟩ := hrel.block bid hbt.1 fb hfb
  rw [hgb] at hgb'; cases hgb'
  rw [hv]
  exact filterMapM_transfer (fun z hz o h =>
    phiStepL_target hwf hc hrel hpre hbt hfb (Array.mem_toList_iff.1 hz) h) hps

/-- **After the `Phi`s, a replaced `Phi` holds its representative's register.** -/
theorem phisL_repInv {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRelL tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : PreL md env tabs f rw fr bid i)
    {fb : Block} (hfb : f.block? bid = some fb) (hs : fr.regs.size = f.valueTab.size)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps) :
    ∀ z v, Placed f z v → v.block = bid → v.op = .Phi →
      (setPhis ps fr.regs)[Opt.CSE.rep rw z]? = (setPhis ps fr.regs)[z]? := by
  have hbt := preL_tree hwf hc hpre
  obtain ⟨-, -, -, hphiS⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  rw [makeL_f] at hphiS
  intro z v hz hvb hph
  cases hr : rw.getD z none with
  | none => simp [Opt.CSE.rep, hr]
  | some r =>
    have hrep : Opt.CSE.rep rw z = r := by simp [Opt.CSE.rep, hr]
    rw [hrep]
    obtain ⟨-, fx, frv, gx, gr, hfx, hfr, hgx, hgr, hop, hblk, -, -, blk,
      hblkr, hrb⟩ := hrel.subst z r hr
    obtain ⟨fx', frv', gx', gr', hfx', hfr', hgx', hgr', -, -, -, hshape, hga, -⟩ :=
      hrel.cong z r hr
    rw [hfx] at hfx'; cases hfx'
    rw [hfr] at hfr'; cases hfr'
    rw [hgx] at hgx'; cases hgx'
    rw [hgr] at hgr'; cases hgr'
    obtain ⟨hzv, -, blk', hblk', hzb⟩ := hz
    rw [hzv] at hfx; cases hfx
    rw [hvb, hfb] at hblk'; cases hblk'
    have hrph : frv.op = .Phi := by rw [hop, hph]
    rw [hblk hph, hvb, hfb] at hblkr; cases hblkr
    obtain ⟨gx', hgx', -, -, -, -, -, -, hax⟩ := hrel.value z v hzv
    rw [hgx] at hgx'; cases hgx'
    obtain ⟨gr', hgr', -, -, -, -, -, -, har⟩ := hrel.value r frv hfr
    rw [hgr] at hgr'; cases hgr'
    rw [hph] at hax
    rw [hrph] at har
    obtain ⟨a, y, ha, hy, hz'⟩ := hphiS z hzb v hzv hph (by rw [hs]; exact lt_of_value? hzv)
    obtain ⟨a', y', ha', hy', hr'⟩ := hphiS r hrb frv hfr hrph (by rw [hs]; exact lt_of_value? hfr)
    have hreps : Opt.CSE.rep rw a = Opt.CSE.rep rw a' := by
      have e1 : gx.args[i]? = some (Opt.CSE.rep rw a) := by
        rw [argsRel_phi hax, Array.getElem?_map, ha]; rfl
      have e2 : gx.args[i]? = some (Opt.CSE.rep rw a') := by
        rw [hga, argsRel_phi har, Array.getElem?_map, ha']; rfl
      rw [e1] at e2; exact Option.some.inj e2
    have hyy : y' = y := by
      have := (phiArgL_rep hwf hc hpre hbt hfb hrb hfr hrph ha').symm.trans
        ((congrArg (fr.regs[·]?) hreps).symm.trans (phiArgL_rep hwf hc hpre hbt hfb hzb hzv hph ha))
      rw [hy', hy] at this
      exact Option.some.inj (Option.some.inj this)
    subst hyy
    rw [hr', hz', tysL_shape hfr, tysL_shape hzv, hshape]

/-- **The `Phi`s keep lemma (D) and `RepInv` for the strict ancestors.** -/
theorem phisL_strict {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRelL tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : PreL md env tabs f rw fr bid i)
    {fb : Block} (hfb : f.block? bid = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps) :
    DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid)
        { fr with regs := setPhis ps fr.regs } ∧
      RepInv f rw { fr with regs := setPhis ps fr.regs }
        (fun a => Anc (make f) a bid ∧ a ≠ bid) := by
  have hp := hc.parents
  have hbt := preL_tree hwf hc hpre
  obtain ⟨hd, hr⟩ := preL_strict hc hpre
  obtain ⟨-, -, hkeep, -⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hout : ∀ z, z ∉ fb.values → (setPhis ps fr.regs)[z]? = fr.regs[z]? :=
    fun z hz => hkeep z (.inl hz)
  have hin : ∀ z v, f.value? z = some v → z ∈ fb.values → v.block = bid := fun z v hv hz => by
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hv] at hv'; cases hv'; exact hvb
  have hnot : ∀ z v, f.value? z = some v → (Anc (make f) v.block bid ∧ v.block ≠ bid) →
      z ∉ fb.values := fun z v hv hb hz => hb.2 (hin z v hv hz)
  refine ⟨fun x v hx hb => ?_, fun x v hx hb => ?_⟩
  · rw [makeL_f] at hx
    obtain ⟨y, hy, hev⟩ := hd x v (by rw [makeL_f]; exact hx) hb
    refine ⟨y, by rw [show ({ fr with regs := setPhis ps fr.regs } : Frame).regs = _ from rfl,
      hout x (hnot x v hx.1 hb), hy], fun hne => ?_⟩
    rw [← hev hne]
    refine (evalValueL_congr rfl fun a ha => ?_).symm
    obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
    have hua := uses hc hvb hblk (Anc.left hp hb.1) hxv hv hne ha
    refine (hout a fun ham => ?_).symm
    obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ a ham
    have hba : blockOf f a = bid := by unfold blockOf; rw [hva]; exact hvab
    rw [hba] at hua
    exact hb.2 (Anc.antisymm hp hb.1 hua)
  · change (setPhis ps fr.regs)[Opt.CSE.rep rw x]? = (setPhis ps fr.regs)[x]?
    rw [hout x (hnot x v hx.1 hb), ← hr x v hx hb]
    apply hout
    cases hrw : rw.getD x none with
    | none => simpa [Opt.CSE.rep, hrw] using hnot x v hx.1 hb
    | some r =>
      have hrep : Opt.CSE.rep rw x = r := by simp [Opt.CSE.rep, hrw]
      rw [hrep]
      obtain ⟨-, fx, frv, -, -, hfx, hfr, -, -, -, -, hanc, -⟩ := hrel.subst x r hrw
      rw [hx.1] at hfx; cases hfx
      intro hrm
      have hrb := hin r frv hfr hrm
      have ha := (anc_iff hp).1 hanc
      rw [hrb] at ha
      exact hb.2 (Anc.antisymm hp hb.1 ha)

/-! ## The block step -/

/-- The source-side invariant at the entry of block `bid` along edge `i`. -/
structure SimAtL (md : LMode) (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID))
    (fr : Frame) (bid : ID) (i : Nat) : Prop where
  size : fr.regs.size = f.valueTab.size
  pre : PreL md env tabs f rw fr bid i

/-- The simulation relation: the same frame, `SimAtL` for the source. -/
def RL (md : LMode) (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID))
    (frS frT : Frame) (bid : ID) (i : Nat) : Prop :=
  frT = frS ∧ SimAtL md env tabs f rw frS bid i

theorem enterBlockL_split {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {r : Res Frame} (h : enterBlockL md env ctx fr b i = r) (hr : ∀ msg, r ≠ .stuck msg) :
    ∃ ps o, b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps ∧
      (ctx.sched[b.id]?).join = some o ∧
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList = r := by
  rw [enterBlockL_eq] at h
  cases hps : b.values.toList.filterMapM (phiStepL md ctx fr i) with
  | panic e m => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg => rw [hps] at h; exact absurd h.symm (hr msg)
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = r at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; exact absurd h.symm (hr _)
    | some o => rw [ho] at h; exact ⟨ps, o, rfl, rfl, h⟩

theorem enterBlockL_of_parts {env : Env} {ctx : Ctx} {fr : Frame} {b : Block} {i : Nat}
    {ps : List (ID × Val)} {o : Array ID}
    (hps : b.values.toList.filterMapM (phiStepL md ctx fr i) = .ok ps)
    (ho : (ctx.sched[b.id]?).join = some o) :
    enterBlockL md env ctx fr b i =
      evalAllL md env ctx { fr with regs := setPhis ps fr.regs } o.toList := by
  rw [enterBlockL_eq, hps]
  change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _
  rw [ho]
  rfl

/-- **One block step of lowered cse's simulation.** -/
theorem stepL {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
    (hrel : CRelL tabs f g rw) {env : Env} (hb : BlockOKL md env tabs f g rw) {fr : Frame}
    {bid : ID} {i : Nat} (hA : SimAtL md env tabs f rw fr bid i) :
    StepSim (RL md env tabs f rw) (blockStepL md env (Ctx.makeL tabs f) fr bid i)
      (blockStepL md env (Ctx.makeL tabs g) fr bid i) := by
  have hbt := preL_tree hwf hc hA.pre
  unfold blockStepL
  rw [makeL_f, makeL_f]
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
  have parts : ∀ r, enterBlockL md env (Ctx.makeL tabs f) fr fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps oS oT, fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps ∧
        schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f) ∧
        evalAllL md env (Ctx.makeL tabs f) { fr with regs := setPhis ps fr.regs } oS.toList = r ∧
        enterBlockL md env (Ctx.makeL tabs g) fr gb i =
          evalAllL md env (Ctx.makeL tabs g) { fr with regs := setPhis ps fr.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := enterBlockL_split hen hr
    rw [hfid, sched_of_blockL hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := hrel.sched bid hbt.1 fb gb hfb hgb oS hsched
    refine ⟨ps, oS, oT, hps, hsched, hoT, hfilt, hev, enterBlockL_of_parts
      (phisL_target hwf hc hrel hA.pre hfb hgb hps) ?_⟩
    rw [hgid, hfid, sched_of_blockL hgb, hoT]
  have blk : ∀ ps oS oT,
      fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) = .ok ps →
      schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (Opt.CSE.rootNode f) = oS.toList.filter (Opt.CSE.rootNode f) →
      (∀ G, evalAllL md env (Ctx.makeL tabs f) { fr with regs := setPhis ps fr.regs } oS.toList =
          .ok G →
        evalAllL md env (Ctx.makeL tabs g) { fr with regs := setPhis ps fr.regs } oT.toList =
          .ok G ∧ RepInv f rw G (fun a => Anc (make f) a bid)) ∧
      (∀ e m, evalAllL md env (Ctx.makeL tabs f) { fr with regs := setPhis ps fr.regs }
          oS.toList = .panic e m →
        evalAllL md env (Ctx.makeL tabs g) { fr with regs := setPhis ps fr.regs } oT.toList =
          .panic e m) := by
    intro ps oS oT hps hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phisL_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    rw [makeL_f] at hphiS
    obtain ⟨hd0, hr0⟩ := phisL_strict hwf hc hrel hA.pre hfb hps
    refine hb bid fb gb _ oS oT hbt hfb hgb (by simp [setPhis_size, hA.size]) hd0 hr0
      (fun z hz v hv hph => ?_) (phisL_repInv hwf hc hrel hA.pre hfb hA.size hps) hoS hoT hfilt
    obtain ⟨a, y, -, -, h⟩ := hphiS z hz v hv hph (by rw [hA.size]; exact lt_of_value? hv)
    exact ⟨_, h⟩
  cases hen : enterBlockL md env (Ctx.makeL tabs f) fr fb i with
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
  obtain ⟨hD, -, hGsz⟩ := dinvL_enter hwf hc hbt.1 hfb hA.size (preL_strict hc hA.pre).1 hen
  have hcs : ∀ (k : Nat) (c : ID) (y : Val), fb.controls[k]? = some c →
      G.regs[c]? = some (some y) → ∃ c', gb.controls[k]? = some c' ∧ G.regs[c']? = some (some y) := by
    intro k c y hk hy
    rcases hctl k c hk with h | h
    · exact ⟨c, h, hy⟩
    · refine ⟨_, h, ?_⟩
      have hcm : c ∈ fb.controls := Array.mem_of_getElem? hk
      obtain ⟨b', blk', hb', hcb⟩ := hwf.ctrlListed bid fb ⟨hbt.1, hfb⟩ c hcm
      obtain ⟨vc, hpl, -, -⟩ := placed_of_mem hwf hb'.1 hb'.2 hcb
      have hanc := ctrlUse hc hbt.1 hfb hbt.2 hcm
      rw [blockOf_placed hpl] at hanc
      rw [hrep c vc hpl hanc, hy]
  have haux : gb.auxInt = fb.auxInt := hrel.aux bid hbt.1 fb gb hfb hgb
  cases hst : stepTermL G fb with
  | ok n =>
    rw [stepTermL_copyRel hkind hsucc (hgid.trans rfl) haux hcs hst]
    cases n with
    | goto e =>
      refine ⟨G, rfl, rfl, by rw [hGsz, hA.size], .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, hrep⟩⟩
      cases e; exact Dead.stepTermL_goto_mem hst
    | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst Dead.stepTermL_not_panic
  | stuck msg => exact True.intro

/-! ## Refinement -/

private theorem entryFrame_makeL_cse (env : Env) (tabs : Tables) (f : Func) (args : List Val)
    (mem : Mem) :
    entryFrame env (Ctx.makeL tabs f) args mem = entryFrame env (Ctx.make tabs f) args mem := by
  unfold Ctx.makeL; split <;> rfl

private theorem defers_makeL_cse (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).defers = (Ctx.make tabs f).defers := by
  unfold Ctx.makeL; split <;> rfl

/-- **lowered cse's output relation gives refinement on `runL`.** -/
theorem refinesL_of_rel (hwf : ∃ ce, WF ce f) (hc : CertOK f) (hrel : CRelL tabs f g rw) :
    RefinesL tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := hwf
  have hpar : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by
    rw [params_makeL, params_makeL]; simp only [Ctx.make, abiParams, hrel.ownAux]
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [hrel.lowered, hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      hrel.vsize
    have hentry : entryFrame env (Ctx.makeL tabs g) args mem =
        entryFrame env (Ctx.makeL tabs f) args mem := by
      rw [entryFrame_makeL_cse, entryFrame_makeL_cse]
      unfold entryFrame frameMem frameAllocs
      simp only [Ctx.make, abiParams, hrel.ownAux]
      rw [show g.valueTab.size = f.valueTab.size from hrel.vsize]
    have hout : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
      rw [outs_makeL, outs_makeL]; simp only [Ctx.make, abiParams, hrel.ownAux]
    have hdef : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by
      rw [defers_makeL_cse, defers_makeL_cse]; rfl
    have hact : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by
      rw [act_makeL, act_makeL]; rfl
    have hent : (Ctx.makeL tabs g).f.entry = (Ctx.makeL tabs f).f.entry := by
      rw [makeL_f, makeL_f]; exact cfgView_entry hrel.cfg
    rw [hentry, hout, hdef, hact, hent]
    have hA0 : SimAtL ⟨f.lowered, false⟩ env tabs f rw
        (entryFrame env (Ctx.makeL tabs f) args mem) f.entry 0 :=
      ⟨by rw [entryFrame_makeL_cse]; simp [Ctx.make, entryFrame], .inl rfl⟩
    exact finish_refines hd (runLoopL_sim (RL ⟨f.lowered, false⟩ env tabs f rw)
      (fun frS frT bid i ⟨h1, h2⟩ => by
        subst h1
        exact stepL hwf hc hrel (blockOKL hrel ⟨ce, hwf⟩ hc rfl env) h2) fuel _ _ _ _
      ⟨rfl, by rw [makeL_f]; exact hA0⟩ (finish_defined hd))

end GoFV.Proof.CSEL
