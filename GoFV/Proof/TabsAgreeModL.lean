import GoFV.Proof.TabsAgreeModLOps
import GoFV.Proof.TabsAgreeMod
import GoFV.Proof.Pass.UnreadLSim
import GoFV.Proof.Pass.CSELSim
import GoFV.Proof.Low.TabsAgreeL
import GoFV.Opt.TabsAgreeModL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Running a scheduled function in tables with extra frame temporaries (`runSched_tabsAgreeModL`)

`regalloc`'s `stackalloc` adds the `PAUTO` names of new spill slots to the tables; running its
input `f` (`runSched`) in the output tables `tabs'` allocates a frame block for each of them
(`Sem.frameLocals`). When `GoFV.Opt.tabsAgreeModL tabs tabs' f` holds (`ModAgreeL`), those are
non-forgeable names `tabs` does not define, so their blocks are `Blk.temp 0 n` (`extraX`), which no
value of `f` names and no integer converts to. Phase 1's `run_tabsAgreeMod` for `runSched`: for
inputs that hold no pointer into a frame temporary (`InitAvoids`), in an environment whose
contracts cannot tell whether temporaries they have no pointer to exist (`Env.TempOblivious`) and
keep frames safe (`Env.FrameSafe`), the source's run in `tabs` and its run in `tabs'` are a
lock-step simulation of the same function in the same context (`runLoopL` does not read the frame
variables, `runLoopL_locals`) from initial memories equal without the extra blocks (`EqX`):

* a value of `tamOpOKL` evaluates on related registers to related results (`value_relL`): its
  arguments of shapes without memories or tuples are equal (typed registers); a generic op of
  `tamMemOps` is Phase 1's (`TabsMod.memOp_rel`); an arm64 memory op of `armMemOpsL` reads and
  writes outside the extra blocks (`armMemOpL_relX`: `elim unread autos`' memory ops, the atomics
  as their generic atomic, `LoweredGetCallerSP`), and when memory ops fault it faults alike
  (`resRel_faulting`);
* the source's results and panics avoid the extra blocks (`evalValueL_avX`, the arm64 ops by
  `elim unread autos`' `UnreadL.evalValueL_av`);
* `Phi`s, terminators (`stepTermL_relX`), the loop (`runLoopL_simX`) and `finish`
  (`TabsMod.finish_rel`) keep the relation.
-/

namespace GoFV.Proof.TabsModL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.TabsMod GoFV.Proof.TabsAgree

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-! ## What the check gives -/

theorem tamOpOKL_spec {tabs : Tables} {f : Func} {fv : Value} (h : tamOpOKL tabs f fv = true) :
    fv.op = .Phi ∨ (∀ a ∈ fv.args, UnreadL.plainArg tabs f a = true) ∨
      ((∀ a ∈ fv.args.pop, UnreadL.plainArg tabs f a = true) ∧
        (fv.op ∈ tamMemOps ∨ (fv.op ∈ armMemOpsL ∧ UnreadL.memLast tabs f fv = true))) := by
  unfold tamOpOKL at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
    List.contains_iff_mem] at h
  rcases h with (h | h) | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨h1, h2⟩)

theorem idsOK_spec {f : Func} (h : idsOK f = true) {x : ID} {v : Value} (hv : f.value? x = some v) :
    v.id = x := by
  unfold idsOK at h
  have := List.all_eq_true.1 h x (List.mem_range.2 (lt_of_value? hv))
  rw [hv] at this
  simpa using this

/-- What `tabsAgreeModL` gives. -/
structure ModAgreeL (tabs tabs' : Tables) (f : Func) : Prop extends TabsMod.ModAgreeF tabs tabs' f where
  shapesL : f.valueTab.map (valueTy (typeShapesL tabs')) = f.valueTab.map (valueTy (typeShapesL tabs))
  ids : ∀ x v, f.value? x = some v → v.id = x
  opOK : ∀ x v, f.value? x = some v → tamOpOKL tabs f v = true

theorem tabsAgreeModL_sound {tabs tabs' : Tables} {f : Func} (h : tabsAgreeModL tabs tabs' f = true) :
    ModAgreeL tabs tabs' f := by
  unfold tabsAgreeModL at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hps, hdi⟩, hpty⟩, hls⟩, hext⟩, hforg⟩, hout⟩, hvals⟩, hids⟩, hops⟩ := h
  have hps' : abiParams tabs' f = abiParams tabs f := Array.toList_inj.mp hps
  have hty : ∀ p ∈ abiParams tabs f, tabs'.ty p.type = tabs.ty p.type :=
    fun p hp => Ty.eq_of_beq (hpty p (Array.mem_def.mp hp))
  refine ⟨⟨?_, hout, hls, fun l hl hn => ?_, hforg, fun id v hv => ?_⟩, ?_,
    fun x v hv => idsOK_spec hids hv, fun id v hv => hops (some v) (mem_valueTab hv)⟩
  · unfold Ctx.make
    simp only [hps', hdi]
    congr 1
    · exact Array.map_congr_left fun o ho => Ty.eq_of_beq (hvals o (Array.mem_def.mp ho)).1.1
    · exact Array.map_congr_left fun p hp => hty p (Array.mem_filter.mp hp).1
    · exact Array.map_congr_left fun p hp => by rw [hty p (Array.mem_filter.mp hp).1]
  · rcases hext l hl with h1 | h1
    · rw [h1] at hn; cases hn
    · exact h1
  · exact valueAuxAgree_sound (hvals (some v) (mem_valueTab hv)).2
  · exact Array.map_congr_left fun o ho => Ty.eq_of_beq (hvals o (Array.mem_def.mp ho)).1.2

/-! ## The context in the extended tables -/

section
variable (md : LMode) (env : Env) (ctx : Ctx) (l : Array (AuxRef × Nat × Option Nat))

theorem evalValueL_locals (fr : Frame) (v : Value) :
    evalValueL md env { ctx with locals := l } fr v = evalValueL md env ctx fr v := by
  have he : evalOpL md.faulting env { ctx with locals := l } fr v = evalOpL md.faulting env ctx fr v :=
    funext fun argv => funext fun ty => evalOpL_congr rfl rfl rfl rfl rfl rfl rfl rfl
  unfold evalValueL
  rw [he]

theorem stepVL_locals (fr : Frame) (id : ID) :
    stepVL md env { ctx with locals := l } fr id = stepVL md env ctx fr id := by
  simp only [stepVL, evalValueL_locals]

theorem evalAllL_locals : ∀ (ids : List ID) (fr : Frame),
    evalAllL md env { ctx with locals := l } fr ids = evalAllL md env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    rw [evalAllL_cons, evalAllL_cons, stepVL_locals]
    cases stepVL md env ctx fr id with
    | ok x => exact evalAllL_locals ids _
    | panic e m => rfl
    | stuck msg => rfl

theorem runLoopL_locals : ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
    runLoopL md env { ctx with locals := l } fuel fr bid i = runLoopL md env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    have he : enterBlockL md env { ctx with locals := l } = enterBlockL md env ctx := by
      funext fr b i
      have ha : evalAllL md env { ctx with locals := l } = evalAllL md env ctx :=
        funext fun fr => funext fun ids => evalAllL_locals md env ctx l ids fr
      unfold enterBlockL
      rw [ha]
    have ih : runLoopL md env { ctx with locals := l } fuel = runLoopL md env ctx fuel :=
      funext fun fr => funext fun bid => funext fun i => runLoopL_locals fuel fr bid i
    rw [runLoopL_succ, runLoopL_succ, he, ih]

end

theorem makeSched_f (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).f = f := by
  unfold Ctx.makeSched; exact makeL_f tabs f

theorem makeSched_tabs (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).tabs = tabs := by
  unfold Ctx.makeSched; exact tabs_makeL tabs f

theorem makeSched_act (tabs : Tables) (f : Func) : (Ctx.makeSched tabs f).act = 0 := by
  unfold Ctx.makeSched; rw [act_makeL]; rfl

theorem makeSched_tys (tabs : Tables) (f : Func) :
    (Ctx.makeSched tabs f).tys = (Ctx.makeL tabs f).tys := rfl

/-- `runSched`'s context in the extended tables. -/
theorem makeSched_eq {tabs tabs' : Tables} {f : Func} (A : ModAgreeL tabs tabs' f) :
    Ctx.makeSched tabs' f = { { Ctx.makeSched tabs f with tabs := tabs' } with
      locals := frameLocals tabs' (Ctx.make tabs f).params } := by
  have hctxL : Ctx.makeL tabs' f = { { Ctx.makeL tabs f with tabs := tabs' } with
      locals := frameLocals tabs' (Ctx.make tabs f).params } := by
    unfold Ctx.makeL
    by_cases hl : f.lowered = true
    · simp only [hl, ite_true, A.ctx, A.shapesL]
    · simp only [hl, Bool.false_eq_true, ite_false, A.ctx]
  unfold Ctx.makeSched
  rw [hctxL]

/-! ## The simulation relation -/

/-- What the source's frame and the target's share at a block entry or inside a block. -/
structure FInvL (X : Blk → Bool) (tabs : Tables) (f : Func) (S T : Frame) : Prop where
  sizeT : T.regs.size = S.regs.size
  frame : T = { S with regs := T.regs, mem0 := T.mem0 }
  mem0 : EqX X S.mem0 T.mem0
  agree : RegsRel X S.regs T.regs
  av : DAE.RegsP (fun _ y => Val.Avoids (fun b => X b = true) y) S
  typed : DAE.RegsP (fun x y =>
    (LMode.sched f).retype ((Ctx.makeSched tabs f).tys[x]?.getD .other) y = y) S
  fok : DAE.FrameOK (fun b => X b = true) S

/-- The fixed hypotheses of the simulation. -/
structure HypsL (env : Env) (X : Blk → Bool) (tabs : Tables) (f : Func) : Prop where
  E : env.TempOblivious
  fs : env.FrameSafe
  temp : TempX X
  ok : ∀ x fv, f.value? x = some fv → tamOpOKL tabs f fv = true
  ids : ∀ x fv, f.value? x = some fv → fv.id = x
  loc : ∀ x fv n, f.value? x = some fv → fv.aux = some n → X (frameBlk tabs 0 n) = false

theorem FInvL.set {tabs : Tables} {f : Func} {S T : Frame} (I : FInvL X tabs f S T) (x : ID)
    {y y' : Val} (hy : VR X y y') (hav : Val.Avoids U y)
    (hty : (LMode.sched f).retype ((Ctx.makeSched tabs f).tys[x]?.getD .other) y = y) :
    FInvL X tabs f (S.set x y) (T.set x y') where
  sizeT := by simp [Frame.set, I.sizeT]
  frame := by
    unfold Frame.set
    conv => lhs; rw [I.frame]
  mem0 := I.mem0
  agree := I.agree.set I.sizeT x hy
  av := DAE.regsP_set I.av hav
  typed := DAE.regsP_set (P := fun x y =>
    (LMode.sched f).retype ((Ctx.makeSched tabs f).tys[x]?.getD .other) y = y) I.typed hty
  fok := ⟨I.fok.images, I.fok.closure, I.fok.mem0⟩

/-! ## One value -/

/-- A value's symbol names no extra frame temporary. -/
theorem symOK_of {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f) {x : ID}
    {fv : Value} (hfv : f.value? x = some fv) :
    UnreadL.SymOK U (Ctx.makeSched tabs f) fv := by
  intro k a p ha hp
  unfold symAddr at hp
  dsimp only at hp
  split at hp
  · rename_i n hn
    rw [makeSched_tabs] at hp
    split at hp
    · cases hp
      intro hu
      obtain ⟨n', hn'⟩ := H.temp _ hu
      cases hn'
    · cases hp
      rw [makeSched_act]
      intro hu
      rw [H.loc x fv n hfv hn] at hu
      cases hu
    · cases hp
  · exact UnreadL.addr_notU (tempU_of H.temp) ha _ hp

theorem loc_of {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f) {x : ID}
    {fv : Value} (hfv : f.value? x = some fv) :
    ∀ n, fv.op = .LocalAddr → fv.aux = some n →
      ¬ (fun b => X b = true) (frameBlk (Ctx.makeSched tabs f).tabs (Ctx.makeSched tabs f).act n) := by
  intro n _ hn hu
  rw [makeSched_tabs, makeSched_act, H.loc x fv n hfv hn] at hu
  cases hu

theorem resRel_mdRetype {md : LMode} {t : Ty} {r r' : Res Val} (h : ResRel X r r') :
    ResRel X (r.bind fun r => .ok (md.retype t r)) (r'.bind fun r => .ok (md.retype t r)) := by
  refine ⟨fun y hy => ?_, fun e m hp => ?_⟩
  · cases r with
    | ok r =>
      obtain ⟨y', h1, h2⟩ := h.1 r rfl
      cases hy; rw [h1]; exact ⟨_, rfl, VR.mdRetype h2 md t⟩
    | panic _ _ => cases hy
    | stuck _ => cases hy
  · cases r with
    | ok r => cases hp
    | panic e' m' =>
      cases hp
      obtain ⟨m'', h1, h2⟩ := h.2 _ _ rfl
      rw [h1]; exact ⟨m'', rfl, h2⟩
    | stuck _ => cases hp

theorem tamMemOps_generic {op : Op} (h : op ∈ tamMemOps) : op.generic = true := by
  have key : tamMemOps.all Op.generic = true := by decide
  exact List.all_eq_true.1 key op h

/-- **One value in source and target frames** with related registers and initial memories. -/
theorem value_relL {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f) {S T : Frame}
    (I : FInvL X tabs f S T) {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ResRel X (evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) S fv)
      (evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) T fv) := by
  have hX := H.temp
  have hU := tempU_of hX
  by_cases hst : ∃ msg, evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) S fv = .stuck msg
  · obtain ⟨msg, hm⟩ := hst; rw [hm]; exact resRel_stuck _ _
  obtain ⟨vs, hvs⟩ := UnreadL.argVals_of_evalL (fun msg h' => hst ⟨msg, h'⟩)
  obtain ⟨vsT, hvsT, hrel⟩ := argVals_rel' (fun a _ y hy => I.agree a y hy) hvs
  rw [UnreadL.evalValueL_of_argVals hvs, UnreadL.evalValueL_of_argVals hvsT]
  apply resRel_mdRetype
  generalize (Ctx.makeSched tabs f).tys[fv.id]?.getD .other = ty
  have hfault : (LMode.sched f).faulting = true := rfl
  rw [hfault]
  have hTop : ∀ argv, fv.op ≠ .InitMem →
      evalOpL true env (Ctx.makeSched tabs f) T fv argv ty =
        evalOpL true env (Ctx.makeSched tabs f) S fv argv ty := by
    intro argv hn
    rw [I.frame]
    show evalOpL true env (Ctx.makeSched tabs f) { { S with mem0 := T.mem0 } with regs := T.regs }
      fv argv ty = _
    rw [evalOpL_frame, evalOpL_mem0 hn]
  have hplain : ∀ a ∈ fv.args, UnreadL.plainArg tabs f a = true → ∀ z,
      S.regs[a]? = some (some z) → (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs) := by
    intro a _ hp z hz
    refine UnreadL.typedL_plain (I.typed a z hz) ?_
    rw [makeSched_tys]
    unfold UnreadL.plainArg at hp
    cases hav : f.value? a with
    | none =>
      have e : (Ctx.makeL tabs f).tys[a]?.getD .other = .other := by
        rw [tys_makeL]
        unfold Func.value? at hav
        simp only [Array.getElem?_map]
        cases hx : f.valueTab[a]? with
        | none => rfl
        | some o =>
          rw [hx] at hav
          simp only [Option.join_some] at hav
          subst hav; rfl
      rw [e]; rfl
    | some av =>
      rw [hav] at hp
      rw [UnreadL.shape_arg hav]
      simpa using hp
  rcases tamOpOKL_spec (H.ok x fv hfv) with hP | hall | ⟨hpop, hmem | ⟨harm, hml⟩⟩
  · -- a `Phi` (not evaluated by the block's schedule): a constant
    have hg : fv.op.generic = true := by rw [hP]; rfl
    have hn : fv.op ∉ evalOpArms := by rw [hP]; decide
    have hr : isRoot fv.op = false := by rw [hP]; rfl
    rw [evalOpL_generic _ _ _ _ _ _ hg, evalOpL_generic _ _ _ _ _ _ hg, evalOp_pure_of hn hr,
      evalOp_pure_of hn hr]
    refine resRel_ok ?_
    rw [hP]; exact .refl _
  · have : vsT = vs := hrel.eq_of fun z hz => by
      obtain ⟨a, ha, hza⟩ := DAE.argVals_mem hvs hz
      exact hplain a ha (hall a ha) z hza
    subst this
    by_cases hin : fv.op = .InitMem
    · have hg : fv.op.generic = true := by rw [hin]; rfl
      have he : ∀ fr : Frame, evalOpL true env (Ctx.makeSched tabs f) fr fv vsT ty =
          .ok (.mem fr.mem0) := fun fr => by
        rw [evalOpL_generic _ _ _ _ _ _ hg]; simp only [evalOp, hin]; rfl
      rw [he, he]
      exact resRel_ok (.mem I.mem0)
    · rw [hTop _ hin]; exact resRel_refl _
  · -- a generic op of `tamMemOps`
    have hn : fv.op ≠ .InitMem := by
      intro h; rw [h] at hmem; revert hmem; decide
    rw [hTop _ hn]
    have hg := tamMemOps_generic hmem
    rw [evalOpL_generic _ _ _ _ _ _ hg, evalOpL_generic _ _ _ _ _ _ hg]
    cases hb : fv.args.back? with
    | none =>
      have h0 : fv.args = #[] := by rw [Array.back?_eq_none_iff] at hb; exact hb
      rw [h0] at hvs
      simp [CSE.argVals] at hvs; subst hvs
      cases hrel
      exact resRel_refl _
    | some m =>
      obtain ⟨L, w, rfl, -, hL⟩ := DAE.argVals_snoc hvs hb
      obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
      have : L' = L := hLL.eq_of fun z hz => by
        obtain ⟨a, ha, hza⟩ := hL z hz
        exact hplain a (DSE.mem_of_mem_pop ha) (hpop a ha) z hza
      subst this
      refine memOp_rel H.E hX (.inl hmem) hww fun z hz => ?_
      obtain ⟨a, -, hza⟩ := DAE.argVals_mem hvs hz
      exact I.av a z hza
  · -- an arm64 memory op on a memory-shaped last argument
    have hn : fv.op ≠ .InitMem := by
      intro h; rw [h] at harm; revert harm; decide
    rw [hTop _ hn]
    obtain ⟨m, mv, hb, hmv, hshape⟩ := UnreadL.memLast_spec hml
    obtain ⟨L, w, rfl, hwm, hL⟩ := DAE.argVals_snoc hvs hb
    obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
    have : L' = L := hLL.eq_of fun z hz => by
      obtain ⟨a, ha, hza⟩ := hL z hz
      exact hplain a (DSE.mem_of_mem_pop ha) (hpop a ha) z hza
    subst L'
    have hwt := I.typed m w hwm
    rw [makeSched_tys, UnreadL.shape_arg hmv, hshape] at hwt
    rcases UnreadL.typedL_mem hwt with ⟨M, rfl⟩ | rfl
    · obtain ⟨M', rfl, hM⟩ := VR.mem_inv hww
      have hLa : ∀ z ∈ L, Val.Avoids U z := fun z hz => by
        obtain ⟨a, -, hza⟩ := hL z hz
        exact I.av a z hza
      exact resRel_faulting hM (armMemOpL_relX H.E hX (symOK_of H hfv) harm hLa hM (I.av m _ hwm))
    · rw [hww.eq (fun _ => nofun) (fun _ => nofun)]
      exact resRel_refl _

/-! ## The source avoids the extra blocks -/

/-- A faulting op panics as the non-faulting one or with a nil fault on its last argument. -/
theorem evalOpL_true_panic {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {e : Panic} {m : Mem} (h : evalOpL true env ctx fr v argv ty = .panic e m) :
    evalOpL false env ctx fr v argv ty = .panic e m ∨
      (e = .nilDeref ∧ argv.getLast? = some (.mem m)) := by
  rw [evalOpL_eq] at h
  rw [evalOpL_eq (faulting := false)]
  by_cases hg : v.op.generic = true
  · simp only [hg, ite_true] at h ⊢; exact .inl h
  have hg' : v.op.generic = false := by simpa using hg
  simp only [hg', Bool.false_eq_true, ite_false] at h ⊢
  by_cases ha : LowerTerm.actOp v.op = true
  rotate_left
  · have ha' : LowerTerm.actOp v.op = false := by simpa using ha
    simp only [ha', Bool.false_eq_true, ite_false] at h ⊢
    exact .inl h
  simp only [ha, ite_true] at h ⊢
  cases hn : nilFaults true ctx v argv with
  | some m' =>
    rw [arm64Op_fault_some hn] at h
    cases h
    exact .inr ⟨rfl, NilLateL.nilFaults_some hn⟩
  | none =>
    by_cases hw : v.op = .ARM64LoweredNilCheck ∧ wildNil argv = true
    · exfalso
      unfold arm64Op at h; rw [hn] at h
      simp only [hw.1, hw.2, Bool.and_self, ↓reduceIte] at h
      cases h
    · have hw' : v.op = .ARM64LoweredNilCheck → wildNil argv = false :=
        fun h1 => by simpa using fun h2 => hw ⟨h1, h2⟩
      rw [arm64Op_fault_none hn hw'] at h
      exact .inl h

theorem evalValueL_avX {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f)
    {S : Frame} (hfok : DAE.FrameOK U S) (hav : DAE.RegsP (fun _ y => Val.Avoids U y) S)
    {x : ID} {fv : Value} (hfv : f.value? x = some fv) {y : Val}
    (h : evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) S fv = .ok y) : Val.Avoids U y := by
  have h' : evalValueL ⟨f.lowered, false⟩ env (Ctx.makeSched tabs f) S fv = .ok y := by
    rcases evalValueL_faults f.lowered env (Ctx.makeSched tabs f) S fv with he | ⟨m, he⟩ | ⟨msg, he⟩
    · exact he ▸ h
    · exact absurd (h.symm.trans he) nofun
    · exact absurd (h.symm.trans he) nofun
  exact UnreadL.evalValueL_av H.fs (tempU_of H.temp) rfl hfok (symOK_of H hfv) (loc_of H hfv)
    (fun a _ z hz => hav a z hz) h'

theorem evalValueL_panic_avX {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f)
    {S : Frame} (hav : DAE.RegsP (fun _ y => Val.Avoids U y) S) {fv : Value} {e : Panic} {m : Mem}
    (h : evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) S fv = .panic e m) :
    e.Avoids U ∧ m.Avoids U := by
  have hU := tempU_of H.temp
  unfold evalValueL at h
  cases hm : fv.args.toList.mapM (fun a =>
      Res.ofOption s!"v{fv.id}: argument v{a} has no value" (S.regs[a]?).join) with
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    have hargs : ∀ z ∈ argv, Val.Avoids U z := fun z hz => by
      obtain ⟨a, -, hz'⟩ := DAE.argVals_mem (UnreadL.argVals_of_mapM hm) hz
      exact hav a z hz'
    cases ho : evalOpL (LMode.sched f).faulting env (Ctx.makeSched tabs f) S fv argv
        ((Ctx.makeSched tabs f).tys[fv.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | panic e' m' =>
      rw [ho] at h
      cases h
      rcases evalOpL_true_panic ho with hf | ⟨rfl, hl⟩
      · exact UnreadL.evalOpL_panic_av H.fs hU hargs hf
      · exact ⟨trivial, hargs _ (List.mem_of_getLast? hl)⟩

/-! ## A block -/

theorem evalAllL_relX {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f) :
    ∀ (o : List ID) {S T : Frame}, FInvL X tabs f S T →
      (∀ S', evalAllL (LMode.sched f) env (Ctx.makeSched tabs f) S o = .ok S' →
        ∃ T', evalAllL (LMode.sched f) env (Ctx.makeSched tabs f) T o = .ok T' ∧
          FInvL X tabs f S' T') ∧
      (∀ e m, evalAllL (LMode.sched f) env (Ctx.makeSched tabs f) S o = .panic e m →
        ∃ m', evalAllL (LMode.sched f) env (Ctx.makeSched tabs f) T o = .panic e m' ∧
          EqX X m m' ∧ e.Avoids U ∧ m.Avoids U)
  | [], S, T, I => ⟨fun S' h => (by cases h; exact ⟨T, rfl, I⟩), fun e m h => (by cases h)⟩
  | x :: o, S, T, I => by
    rw [evalAllL_cons, evalAllL_cons]
    unfold stepVL
    rw [makeSched_f]
    cases hfv : f.value? x with
    | none => exact ⟨fun _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
    | some fv =>
    dsimp only
    have hid := H.ids x fv hfv
    have hr := value_relL H I hfv
    cases hS : evalValueL (LMode.sched f) env (Ctx.makeSched tabs f) S fv with
    | stuck msg => exact ⟨fun _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
    | panic e m =>
      obtain ⟨m', hT, hm⟩ := hr.2 e m hS
      have hpa := evalValueL_panic_avX H I.av hS
      rw [hT]
      refine ⟨fun _ h => (by simp at h), fun e' m'' h => ?_⟩
      simp only [Res.panic.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m', rfl, hm, hpa⟩
    | ok y =>
      obtain ⟨y', hT, hy⟩ := hr.1 y hS
      rw [hT]
      have hav := evalValueL_avX H I.fok I.av hfv hS
      have hty : (LMode.sched f).retype ((Ctx.makeSched tabs f).tys[x]?.getD .other) y = y := by
        rw [← hid]; exact evalValueL_typed hS
      exact evalAllL_relX H o (I.set x hy hav hty)

/-- One `Phi` step in source and target. -/
theorem phiStepL_relX {md : LMode} {ctx : Ctx} {S T : Frame} (hag : RegsRel X S.regs T.regs)
    (i : Nat) {z : ID} {o : Option (ID × Val)} (h : phiStepL md ctx S i z = .ok o) :
    ∃ o', phiStepL md ctx T i z = .ok o' ∧
      ((o = none ∧ o' = none) ∨ ∃ x x', o = some (z, x) ∧ o' = some (z, x') ∧ VR X x x') := by
  unfold phiStepL at h ⊢
  cases hfv : ctx.f.value? z with
  | none => rw [hfv] at h; cases h
  | some fv =>
    rw [hfv] at h
    dsimp only at h ⊢
    by_cases hph : fv.op = .Phi
    · simp only [hph, beq_self_eq_true, ↓reduceIte] at h ⊢
      cases ha : fv.args[i]? with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        simp only at h ⊢
        cases hx : S.regs[a]? with
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

/-- **The target collects related `Phi`s.** -/
theorem phisL_relX {md : LMode} {ctx : Ctx} {S T : Frame} (hag : RegsRel X S.regs T.regs)
    (i : Nat) :
    ∀ {l : List ID} {ps : List (ID × Val)},
      l.filterMapM (phiStepL md ctx S i) = .ok ps →
      ∃ ps', l.filterMapM (phiStepL md ctx T i) = .ok ps' ∧ PRel X ps ps'
  | [], ps, h => by
    simp only [List.filterMapM_nil] at h
    cases h; exact ⟨[], rfl, .nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h ⊢
    cases hz : phiStepL md ctx S i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      obtain ⟨o', ho', hrel⟩ := phiStepL_relX hag i hz
      rw [ho']
      cases hl : l.filterMapM (phiStepL md ctx S i) with
      | panic e m =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | stuck msg =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | ok rest =>
        obtain ⟨rest', hl', hr⟩ := phisL_relX hag i hl
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩
        · simp only [bind, Res.bind, hl] at h
          cases h
          exact ⟨rest', by simp only [bind, Res.bind, hl'], hr⟩
        · simp only [bind, Res.bind, hl, pure] at h
          cases h
          exact ⟨_, by simp only [bind, Res.bind, hl', pure], .cons hv hr⟩

/-- Setting registers that each have a property keeps a property of all registers. -/
theorem setPhis_regsP {P : ID → Val → Prop} :
    ∀ (ps : List (ID × Val)) {r : Array (Option Val)},
      (∀ z y, r[z]? = some (some y) → P z y) → (∀ p ∈ ps, P p.1 p.2) →
      ∀ z y, (setPhis ps r)[z]? = some (some y) → P z y
  | [], r, hr, _ => by simpa [setPhis] using hr
  | (id, x) :: ps, r, hr, hps => by
    unfold setPhis
    rw [List.foldl_cons]
    refine setPhis_regsP ps (fun z y hz => ?_) (fun p hp => hps p (List.mem_cons_of_mem _ hp))
    simp only [Array.set!_eq_setIfInBounds] at hz
    by_cases he : id = z
    · subst he
      by_cases hlt : id < r.size
      · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hz
        cases hz; exact hps _ List.mem_cons_self
      · simp [hlt] at hz
    · rw [Array.getElem?_setIfInBounds_ne he] at hz
      exact hr z y hz

/-- **Entering a block** in source and target. -/
theorem enterBlockL_relX {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f)
    (b : Block) (i : Nat) {S T : Frame} (I : FInvL X tabs f S T) :
    (∀ S', enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) S b i = .ok S' →
      ∃ T', enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) T b i = .ok T' ∧
        FInvL X tabs f S' T') ∧
    (∀ e m, enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) S b i = .panic e m →
      ∃ m', enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) T b i = .panic e m' ∧
        EqX X m m' ∧ e.Avoids U ∧ m.Avoids U) := by
  have hU := tempU_of H.temp
  have key : ∀ r, enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) S b i = r →
      (∀ msg, r ≠ .stuck msg) →
      ∃ (ps : List (ID × Val)) (o : Array ID),
        evalAllL (LMode.sched f) env (Ctx.makeSched tabs f)
          { S with regs := setPhis ps S.regs } o.toList = r ∧
        ∃ psT : List (ID × Val), enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) T b i =
          evalAllL (LMode.sched f) env (Ctx.makeSched tabs f)
            { T with regs := setPhis psT T.regs } o.toList ∧
        FInvL X tabs f { S with regs := setPhis ps S.regs } { T with regs := setPhis psT T.regs } := by
    intro r hen hr
    obtain ⟨ps, o, hps, hsched, hev⟩ := CSEL.enterBlockL_split hen hr
    obtain ⟨psT, hpsT, hpr⟩ := phisL_relX I.agree i hps
    have hent : ∀ p ∈ ps, ∃ (a : ID) (y : Val), S.regs[a]? = some (some y) ∧
        p.2 = (LMode.sched f).retype ((Ctx.makeSched tabs f).tys[p.1]?.getD .other) y := by
      intro p hp
      obtain ⟨-, hsome, -⟩ := filterMapM_phiL hps
      obtain ⟨h1, v, a, y, -, -, -, hy, h2⟩ := phiStepL_some (hsome p hp)
      exact ⟨a, y, hy, by rw [h1]; exact h2⟩
    refine ⟨ps, o, hev, psT, CSEL.enterBlockL_of_parts hpsT hsched, ?_⟩
    refine ⟨by simp [setPhis_size, I.sizeT], ?_, I.mem0, setPhis_rel hpr I.agree I.sizeT, ?_, ?_,
      ⟨I.fok.images, I.fok.closure, I.fok.mem0⟩⟩
    · conv => lhs; rw [I.frame]
    · refine setPhis_regsP ps I.av fun p hp => ?_
      obtain ⟨a, y, hy, he⟩ := hent p hp
      rw [he]; exact UnreadL.mdRetype_av hU _ _ (I.av a y hy)
    · refine setPhis_regsP ps I.typed fun p hp => ?_
      obtain ⟨a, y, -, he⟩ := hent p hp
      rw [he]; exact LMode.retype_idem _ _ _
  constructor
  · intro S' h
    obtain ⟨ps, o, hev, psT, hT, I0⟩ := key _ h nofun
    obtain ⟨T', h1, h2⟩ := (evalAllL_relX H o.toList I0).1 S' hev
    exact ⟨T', hT.trans h1, h2⟩
  · intro e m h
    obtain ⟨ps, o, hev, psT, hT, I0⟩ := key _ h nofun
    obtain ⟨m', h1, h2⟩ := (evalAllL_relX H o.toList I0).2 e m hev
    exact ⟨m', hT.trans h1, h2⟩

/-- **The terminators on related controls.** -/
theorem stepTermL_relX {G GT : Frame} {b : Block} (hreg : RegsRel X G.regs GT.regs) :
    (∀ e, stepTermL G b = .ok (.goto e) → stepTermL GT b = .ok (.goto e)) ∧
    (∀ rs m, stepTermL G b = .ok (.ret rs m) →
      ∃ rs' m', stepTermL GT b = .ok (.ret rs' m') ∧ VRL X rs rs' ∧ EqX X m m') := by
  by_cases ha : b.kind.isArm64 = true
  · have arm : ∀ n, stepTermL G b = .ok n → stepTermL GT b = .ok n := by
      intro n h
      obtain ⟨v, k, hcv, hsk, hT⟩ := Dead.stepTermL_arm ha h
      obtain ⟨v', hv', hvr⟩ := control_rel (b' := b) rfl hreg hcv
      obtain ⟨hm, ht⟩ := UnreadL.armCtrl_plain ha h hcv
      rw [hvr.eq hm ht] at hv'
      rw [hT GT b rfl rfl hv', hsk]
    refine ⟨fun e h => arm _ h, fun rs m h => ?_⟩
    obtain ⟨-, k, -, hsk, -⟩ := Dead.stepTermL_arm ha h
    exact absurd hsk DAE.succ_not_ret
  · rw [stepTermL_generic G (Bool.eq_false_iff.2 ha), stepTermL_generic GT (Bool.eq_false_iff.2 ha)]
    exact stepTerm_rel rfl rfl rfl rfl hreg

/-- **One block step** of the simulation. -/
theorem stepL {env : Env} {tabs : Tables} {f : Func} (H : HypsL env X tabs f) {S T : Frame}
    {bid : ID} {i : Nat} (I : FInvL X tabs f S T) :
    StepRelX X (fun S T _ _ => FInvL X tabs f S T)
      (blockStepL (LMode.sched f) env (Ctx.makeSched tabs f) S bid i)
      (blockStepL (LMode.sched f) env (Ctx.makeSched tabs f) T bid i) := by
  unfold blockStepL
  cases hfb : (Ctx.makeSched tabs f).f.block? bid with
  | none => exact True.intro
  | some b =>
  dsimp only
  have E := enterBlockL_relX H b i I
  cases hen : enterBlockL (LMode.sched f) env (Ctx.makeSched tabs f) S b i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨m', hT, hm, he, hmA⟩ := E.2 e m hen
    rw [hT]
    exact ⟨m', rfl, hm, he, hmA⟩
  | ok G =>
    obtain ⟨GT, hGT, IG⟩ := E.1 G hen
    rw [hGT]
    dsimp only
    obtain ⟨hgo, hret⟩ := stepTermL_relX (b := b) IG.agree
    cases hstp : stepTermL G b with
    | ok n =>
      cases n with
      | goto e =>
        rw [hgo e hstp]
        exact ⟨GT, rfl, IG⟩
      | ret rs m =>
        obtain ⟨rs', m', h1, h2, h3⟩ := hret rs m hstp
        rw [h1]
        exact ⟨rs', m', rfl, h2, h3⟩
    | panic e m => exact absurd hstp Dead.stepTermL_not_panic
    | stuck msg => exact True.intro

/-- **Lock-step simulation** over `runLoopL` with related outcomes. -/
theorem runLoopL_simX {md : LMode} {env : Env} {ctx : Ctx} (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepRelX X R (blockStepL md env ctx frS bid i) (blockStepL md env ctx frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoopL md env ctx fuel frS bid i).Defined →
      ORel X (runLoopL md env ctx fuel frS bid i) (runLoopL md env ctx fuel frT bid i) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS frT bid i hR hd
    have hs := hsim frS frT bid i hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoopL_blockStep md env ctx n frS bid i
    obtain ⟨g2, r2, p2, -⟩ := runLoopL_blockStep md env ctx n frT bid i
    cases hS : blockStepL md env ctx frS bid i with
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

end GoFV.Proof.TabsModL

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt TabsMod TabsModL TabsAgree

/-- **Running a scheduled function in tables with extra frame temporaries.** When
`tabsAgreeModL tabs tabs' f` holds, a defined `runSched` of `f` in `tabs` on inputs that hold no
pointer into a frame temporary, in an environment whose contracts cannot tell whether unreachable
temporaries exist and keep frames safe, has the same outcome in `tabs'` (the same results and
memory, or the same panic with the same memory once the frames are dropped). -/
theorem runSched_tabsAgreeModL {tabs tabs' : Tables} {f : Func}
    (h : tabsAgreeModL tabs tabs' f = true) {env : Env} (hE : env.TempOblivious)
    (hfs : env.FrameSafe) {args : List Val} {mem : Mem} (hinit : InitAvoids env args mem)
    {fuel : Nat} (hd : (runSched env tabs f args mem fuel).Defined) :
    OutcomeRefines 0 (runSched env tabs f args mem fuel) (runSched env tabs' f args mem fuel) := by
  have A := tabsAgreeModL_sound h
  have hX := tempX_extraX tabs tabs'
  have hU := tempU_of hX
  have H : HypsL env (extraX tabs tabs') tabs f :=
    ⟨hE, hfs, hX, A.opOK, A.ids, fun x fv n hfv hn => loc_extraX A.toModAgreeF x fv n hfv hn⟩
  have hval : ∀ id v, (Ctx.makeSched tabs f).f.value? id = some v →
      AuxAgree (Ctx.makeSched tabs f).tabs tabs' v.aux := by
    intro id v hv; rw [makeSched_f] at hv; rw [makeSched_tabs]; exact A.value id v hv
  have hloop : runLoopL (LMode.sched f) env (Ctx.makeSched tabs' f) fuel =
      runLoopL (LMode.sched f) env (Ctx.makeSched tabs f) fuel := by
    funext fr bid i
    rw [makeSched_eq A, runLoopL_locals, Low.runLoopL_tabs hval]
  have hmk : ∀ t : Tables, (Ctx.makeSched t f).params = (Ctx.make t f).params ∧
      (Ctx.makeSched t f).outs = (Ctx.make t f).outs ∧ (Ctx.makeSched t f).act = (Ctx.make t f).act ∧
      (Ctx.makeSched t f).defers = (Ctx.make t f).defers ∧
      entryFrame env (Ctx.makeSched t f) args mem = entryFrame env (Ctx.make t f) args mem := by
    intro t
    refine ⟨params_makeL t f, outs_makeL t f, act_makeL t f, ?_, ?_⟩
    · unfold Ctx.makeSched Ctx.makeL; split <;> rfl
    · show entryFrame env { Ctx.makeL t f with sched := _ } args mem = _
      rw [← entryFrame_makeL env t f args mem]
      rfl
  obtain ⟨hp1, ho1, ha1, hd1, he1⟩ := hmk tabs
  obtain ⟨hp2, ho2, ha2, hd2, he2⟩ := hmk tabs'
  have hpar : (Ctx.make tabs' f).params = (Ctx.make tabs f).params := by rw [A.ctx]
  have houts : (Ctx.make tabs' f).outs = (Ctx.make tabs f).outs := by rw [A.ctx]
  have hact : (Ctx.make tabs' f).act = (Ctx.make tabs f).act := by rw [A.ctx]
  have hdef : (Ctx.make tabs' f).defers = (Ctx.make tabs f).defers := by rw [A.ctx]
  unfold runSched runCtxL at hd ⊢
  rw [hloop, hp1, ho1, ha1, hd1, he1, hp2, ho2, ha2, hd2, he2, hpar, houts, hact, hdef,
    makeSched_f, makeSched_f]
  rw [hp1, ho1, ha1, hd1, he1, makeSched_f] at hd
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hargs : ∀ v ∈ args, Val.Avoids (fun b => extraX tabs tabs' b = true) v := fun v hv =>
      val_avoids_of hU fun a n => (hinit a n).1 v hv
    have hmem : mem.Avoids (fun b => extraX tabs tabs' b = true) :=
      mem_avoids_of hU fun a n => (hinit a n).2.1
    have hglob : ∀ g ∈ env.globals, DAE.BAv (fun b => extraX tabs tabs' b = true) g.2.data :=
      fun g hg x hx => byte_avoids_of hU fun a n => (hinit a n).2.2.2 g hg x hx
    have himg : ∀ img ∈ (args.toArray.zip (Ctx.make tabs f).paramTys).map (fun (a, t) => encode t a),
        DAE.BAv (fun b => extraX tabs tabs' b = true) img := by
      intro img hi
      simp only [Array.mem_map] at hi
      obtain ⟨⟨a, t⟩, hm, rfl⟩ := hi
      have ha : a ∈ args := by
        have := (Array.of_mem_zip hm).1
        simpa using this
      exact DAE.encode_avoids t (hargs a ha)
    have hpty : (Ctx.make tabs' f).paramTys = (Ctx.make tabs f).paramTys := by rw [A.ctx]
    have hvsz : (Ctx.make tabs' f).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size := by
      rw [A.ctx]
    have I0 : FInvL (extraX tabs tabs') tabs f (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs' f) args mem) := by
      refine ⟨by simp [entryFrame, hvsz], ?_, ?_, fun z y hz => ?_, fun z y hz => ?_,
        fun z y hz => ?_, ⟨himg, rfl, frameAllocs_avoids himg (addGlobals_avoids hglob hmem)⟩⟩
      · unfold entryFrame; rw [hpty, hvsz]
      · unfold entryFrame; rw [hpty]; exact frameMem_eqX A.toModAgreeF env _ mem
      · simp [entryFrame, Array.getElem?_replicate] at hz
      · simp [entryFrame, Array.getElem?_replicate] at hz
      · simp [entryFrame, Array.getElem?_replicate] at hz
    exact finish_rel hE hX (deferAvoid_extraX tabs tabs') hd (runLoopL_simX
      (fun S T _ _ => FInvL (extraX tabs tabs') tabs f S T)
      (fun S T bid i hA => stepL H hA) fuel _ _ _ _ I0 (finish_defined hd))

end GoFV.Proof
