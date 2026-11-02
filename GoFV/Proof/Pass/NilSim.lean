import GoFV.Proof.Pass.NilBlock
import GoFV.Proof.Pass.CSESim

/-!
# nilcheckelim refines its input

Lock-step simulation (`runLoop_sim`) in which the target's frame is the source's at every block
entry: nilcheckelim moves no value between blocks, keeps the controls and the `Phi`s (in order),
and reorders a block's other values. A block is entered as in cse's proof (`CSE.Pre` with no
representatives: lemma (D) for the predecessor's ancestors). One block step: the target
collects the source's `Phi`s (`phis_target`: the `Phi`s are the same values in the same order),
its schedule evaluates to the source's frame or panics alike (`blockOK`), and its terminator
reads the same controls. `nilcheck_refines`: on inputs in `nilFrag`, the pass refines its input.
-/

namespace GoFV.Proof.Nil

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Proof.CSE GoFV.Opt

/-- No representatives (`CSE.Pre` and `RepInv` with the empty substitution). -/
def rw0 : Array (Option ID) := #[]

theorem repInv0 {f : Func} {fr : Frame} {P : ID → Prop} : RepInv f rw0 fr P :=
  fun x _ _ _ => by rw [rep_none (by simp [rw0])]

/-- The source-side invariant at the entry of block `bid` along edge `i`. -/
structure SimAt (xt : Bool) (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (bid : ID)
    (i : Nat) : Prop where
  size : fr.regs.size = f.valueTab.size
  pre : CSE.Pre env tabs f rw0 fr bid i
  /-- With the rewrite passes' seeds: the dictionary arguments' images are non-nil pointers. -/
  dict : xt = true → DictFrame tabs f fr

/-- The simulation relation: the same frame, `SimAt` for the source. -/
def R (xt : Bool) (env : Env) (tabs : Tables) (f : Func) (frS frT : Frame) (bid : ID) (i : Nat) :
    Prop :=
  frT = frS ∧ SimAt xt env tabs f frS bid i

/-- `filterMapM` of the `Phi` step only sees a list's `Phi`s. -/
theorem filterMapM_phis {ctx : Ctx} {fr : Frame} {i : Nat} :
    ∀ {l : List ID}, (∀ z ∈ l, (ctx.f.value? z).isSome) →
      l.filterMapM (phiStep ctx fr i) =
        (l.filter fun z => (ctx.f.getV z).op == .Phi).filterMapM (phiStep ctx fr i)
  | [], _ => rfl
  | z :: l, h => by
    have ih := filterMapM_phis (ctx := ctx) (fr := fr) (i := i) (l := l)
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h z List.mem_cons_self)
    have hg : ctx.f.getV z = v := by simp [Func.getV, hv]
    by_cases hph : v.op = .Phi
    · rw [List.filter_cons_of_pos (by simp [hg, hph]), List.filterMapM_cons,
        List.filterMapM_cons, ih]
    · rw [List.filter_cons_of_neg (by simp [hg, hph]), List.filterMapM_cons, ← ih]
      have : phiStep ctx fr i z = .ok none := by
        unfold phiStep; rw [hv]; simp [hph]
      rw [this]; rfl

theorem filterMapM_congr {F G : ID → Res (Option (ID × Val))} :
    ∀ {l : List ID}, (∀ z ∈ l, F z = G z) → l.filterMapM F = l.filterMapM G
  | [], _ => rfl
  | z :: l, h => by
    rw [List.filterMapM_cons, List.filterMapM_cons, h z List.mem_cons_self,
      filterMapM_congr fun y hy => h y (List.mem_cons_of_mem _ hy)]

variable {xt : Bool} {tabs : Tables} {f g : Func}

/-- **The target collects the source's `Phi`s.** -/
theorem phis_target {ce : CheckEnv} (hwf : WF ce f) (hrel : NRel xt tabs f g) {fr : Frame}
    {bid : ID} {i : Nat} (hb : bid ∈ f.blocks) {fb gb : Block} (hfb : f.block? bid = some fb)
    (hgb : g.block? bid = some gb) :
    gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) =
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) := by
  obtain ⟨gb', hgb', -, -, hperm, hphis⟩ := hrel.block bid hb fb hfb
  rw [hgb] at hgb'; cases hgb'
  have hinF : ∀ z ∈ fb.values, ∃ v, f.value? z = some v := fun z hz => by
    obtain ⟨v, hv, -⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ z hz; exact ⟨v, hv⟩
  have hinG : ∀ z ∈ gb.values, (g.value? z).isSome := fun z hz => by
    have hz' : z ∈ fb.values := by
      rw [← Array.mem_toList_iff] at hz ⊢; exact hperm.mem_iff.1 hz
    obtain ⟨v, hv⟩ := hinF z hz'
    obtain ⟨gv, hgv, -⟩ := hrel.value z v hv
    simp [hgv]
  rw [filterMapM_phis (ctx := Ctx.make tabs g) fun z hz => hinG z (Array.mem_toList_iff.1 hz),
    filterMapM_phis (ctx := Ctx.make tabs f) fun z hz => by
      obtain ⟨v, hv⟩ := hinF z (Array.mem_toList_iff.1 hz); simp [show (Ctx.make tabs f).f = f from rfl, hv]]
  have hl : (gb.values.toList.filter fun z => ((Ctx.make tabs g).f.getV z).op == .Phi) =
      fb.values.toList.filter fun z => ((Ctx.make tabs f).f.getV z).op == .Phi := by
    have := congrArg Array.toList hphis
    simp only [Array.toList_filter] at this
    exact this
  rw [hl]
  refine filterMapM_congr fun z hz => ?_
  obtain ⟨hz, hph⟩ := List.mem_filter.1 hz
  obtain ⟨v, hv⟩ := hinF z (Array.mem_toList_iff.1 hz)
  have hph' : v.op = .Phi := by
    simpa [show (Ctx.make tabs f).f = f from rfl, Func.getV, hv] using hph
  obtain ⟨gv, hgv, -, -, hty, hr⟩ := hrel.value z v hv
  have hsame : gv.op = v.op ∧ gv.args = v.args := by
    cases hr with
    | same hop hargs => exact ⟨hop, hargs⟩
    | nc h1 => rw [h1] at hph'; cases hph'
    | nn h1 => rw [h1] at hph'; cases hph'
    | nns h1 => rw [h1] at hph'; cases hph'
    | after h1 => rw [h1] at hph'; cases hph'
  have htys : (Ctx.make tabs g).tys[z]? = (Ctx.make tabs f).tys[z]? := by
    rw [tys_of_value hgv, tys_of_value hv, hty]
  unfold phiStep
  simp only [show (Ctx.make tabs g).f = g from rfl, show (Ctx.make tabs f).f = f from rfl, hgv, hv,
    hsame.1, hsame.2, htys]

/-- The `Phi`s keep lemma (D) for the strict ancestors. -/
theorem phis_dinv {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (hpre : CSE.Pre env tabs f rw0 fr bid i) {fb : Block}
    (hfb : f.block? bid = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid)
      { fr with regs := setPhis ps fr.regs } := by
  have hp := hc.parents
  have hbt := pre_tree hwf hc hpre
  obtain ⟨hd, -⟩ := pre_strict hc hpre
  obtain ⟨-, -, hkeep, -⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hout : ∀ z, z ∉ fb.values → (setPhis ps fr.regs)[z]? = fr.regs[z]? :=
    fun z hz => hkeep z (.inl hz)
  have hin : ∀ z v, f.value? z = some v → z ∈ fb.values → v.block = bid := fun z v hv hz => by
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hv] at hv'; cases hv'; exact hvb
  have hnot : ∀ z v, f.value? z = some v → (Anc (make f) v.block bid ∧ v.block ≠ bid) →
      z ∉ fb.values := fun z v hv hb hz => hb.2 (hin z v hv hz)
  intro x v hx hb
  obtain ⟨y, hy, hev⟩ := hd x v hx hb
  refine ⟨y, by rw [show ({ fr with regs := setPhis ps fr.regs } : Frame).regs = _ from rfl,
    hout x (hnot x v hx.1 hb), hy], fun hne => ?_⟩
  rw [← hev hne]
  refine (evalValue_congr rfl fun a ha => ?_).symm
  obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
  have hua := uses hc hvb hblk (Anc.left hp hb.1) hxv hv hne ha
  refine (hout a fun ham => ?_).symm
  obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ a ham
  have hba : blockOf f a = bid := by unfold blockOf; rw [hva]; exact hvab
  rw [hba] at hua
  exact hb.2 (Anc.antisymm hp hb.1 hua)

/-- **One block step of nilcheckelim's simulation.** -/
theorem step {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
    (hrel : NRel xt tabs f g) {env : Env} (hx : xt = true → env.AllocNonNil)
    (hb : BlockOK xt env tabs f g) {fr : Frame} {bid : ID}
    {i : Nat} (hA : SimAt xt env tabs f fr bid i) :
    StepSim (R xt env tabs f) (blockStep env (Ctx.make tabs f) fr bid i)
      (blockStep env (Ctx.make tabs g) fr bid i) := by
  have hbt := pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hkind, hctl, -, -⟩ := hrel.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block hrel.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) fr fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps ∧
        schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (Opt.NilCheck.root g) = oS.toList.filter (Opt.NilCheck.root g) ∧
        evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) fr gb i =
          evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := hrel.sched bid hbt.1 fb gb hfb hgb oS hsched
    refine ⟨ps, oS, oT, hps, hsched, hoT, hfilt, hev, enterBlock_of_parts
      (by rw [phis_target hwf hrel hbt.1 hfb hgb]; exact hps) ?_⟩
    rw [hgid, hfid, sched_of_block hgb, hoT]
  have blk : ∀ ps oS oT,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps →
      schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (Opt.NilCheck.root g) = oS.toList.filter (Opt.NilCheck.root g) →
      (∀ G, evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList =
          .ok G →
        evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList = .ok G) ∧
      (∀ e m, evalAll env (Ctx.make tabs f) { fr with regs := setPhis ps fr.regs } oS.toList =
          .panic e m →
        evalAll env (Ctx.make tabs g) { fr with regs := setPhis ps fr.regs } oT.toList =
          .panic e m) := by
    intro ps oS oT hps hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    refine hb bid fb gb _ oS oT hbt hfb hgb (by simp [setPhis_size, hA.size])
      (phis_dinv hwf hc hA.pre hfb hps) (fun z hz v hv hph => ?_) hoS hoT hfilt
      (fun h => ⟨hx h, (hA.dict h).images rfl⟩)
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
  have hTG := (blk ps oS oT hps hoS hoT hfilt).1 G hev
  rw [hT, hTG]
  simp only
  obtain ⟨hD, hGfr, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (pre_strict hc hA.pre).1 hen
  have hcs : ∀ (k : Nat) (c : ID), fb.controls[k]? = some c →
      ∃ c', gb.controls[k]? = some c' ∧ G.regs[c']? = G.regs[c]? :=
    fun k c hk => ⟨c, by rw [hctl]; exact hk, rfl⟩
  cases hst : stepTerm G fb with
  | ok n =>
    rw [stepTerm_rel hkind hsucc (hgid.trans rfl) hcs hst]
    cases n with
    | goto e =>
      refine ⟨G, rfl, rfl, by rw [hGsz, hA.size], .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, repInv0⟩,
        fun h => (hA.dict h).images (by rw [hGfr])⟩
      cases e; exact stepTerm_goto_mem hst
    | ret rs m => exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **nilcheckelim's output relation gives refinement**, with the rewrite passes' seeds (`xt`)
on environments and arguments where malloc-family calls return non-nil pointers and the
dictionary arguments are non-nil. -/
theorem refines_of_rel_xt (hwf : ∃ ce, WF ce f) (hc : CertOK f) (hrel : NRel xt tabs f g) :
    RefinesFrom (fun env args mem => xt = true → NilPre tabs f env args mem) tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := hwf
  have hb : ∀ env, BlockOK xt env tabs f g := fun env => blockOK hrel ⟨ce, hwf⟩ hc env
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have hpty : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  have hloc : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
    simp only [Ctx.make, abiParams, hrel.ownAux]
  intro env args mem hpre fuel hd
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
    have hA0 : SimAt xt env tabs f (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
      ⟨by simp [Ctx.make, entryFrame], .inl rfl, fun h => dictFrame_entry (hpre h).2⟩
    exact finish_refines hd (runLoop_sim (R xt env tabs f)
      (fun frS frT bid i ⟨h1, h2⟩ => by
        subst h1; exact step hwf hc hrel (fun h => (hpre h).1) (hb env) h2) fuel _ _ _ _
      ⟨rfl, hA0⟩ (finish_defined hd))

/-- **nilcheckelim's output relation gives refinement** (nilcheckelim's own seeds). -/
theorem refines_of_rel (hwf : ∃ ce, WF ce f) (hc : CertOK f) (hrel : NRel false tabs f g) :
    Refines tabs g tabs f :=
  fun env args mem fuel hd => refines_of_rel_xt hwf hc hrel env args mem nofun fuel hd

/-- **nilcheckelim's output relation with the rewrite passes' seeds gives refinement** under
`NilPre`. -/
theorem refinesFrom_of_rel (hwf : ∃ ce, WF ce f) (hc : CertOK f) (hrel : NRel true tabs f g) :
    RefinesFrom (NilPre tabs f) tabs g tabs f :=
  fun env args mem hp fuel hd => refines_of_rel_xt hwf hc hrel env args mem (fun _ => hp) fuel hd

/-- **nilcheckelim refines its input** (on inputs in `nilFrag`: the checker accepts its
output). -/
theorem nilcheck_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : nilcheckelimPass penv f = .ok out) (hf : check ce f = .ok ())
    (hfrag : nilFrag penv f = true) : Refines out.tables out.func penv.tables f := by
  unfold nilFrag at hfrag
  simp only [nilcheckelimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hr : nilcheckelim penv f with
  | error e => rw [hr] at h; cases h
  | ok g =>
    rw [hr] at h hfrag
    cases h
    exact refines_of_rel ⟨ce, check_wf hf⟩ (certOK_of_check (check_domCert hf))
      (nrel_sound hfrag)

end GoFV.Proof.Nil
