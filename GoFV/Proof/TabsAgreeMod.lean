import GoFV.Proof.TabsAgreeModSim
import GoFV.Proof.TabsAgree
import GoFV.Proof.CheckFacts

/-!
# Running a function in tables with extra frame temporaries (`run_tabsAgreeMod`)

`decompose user`/`decompose builtin` add the `PAUTO` names of split variables to the definition
tables; running the source `f` in the output tables `tabs'` allocates a frame block for each of
them (`Sem.frameLocals`). When `GoFV.Opt.tabsAgreeMod tabs tabs' f` holds (`ModAgree`), those are
non-forgeable names `tabs` does not define, so their blocks are `Blk.temp 0 n` (`extraX`), which
no value of `f` names and no integer converts to. For inputs that hold no pointer into a frame
temporary (`Sem.InitAvoids`), in an environment whose contracts cannot tell whether temporaries
they have no pointer to exist (`Env.TempOblivious`), the source's run in `tabs` and its run in
`tabs'` are a lock-step simulation (`TabsAgreeModSim`) with equal registers up to memories equal
without the extra blocks (`EqX`); `finish`/`dropFrames` drop them, so the outcomes are equal: a
returning run returns the same results and memory, a panicking one panics alike with the same
memory once the frames are dropped (`run_tabsAgreeMod`). `refinesFrom_of_tabsAgreeMod` restates a
refinement against the extended tables in the input tables.
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.DSE GoFV.Proof.TabsAgree

/-- The extra frame temporaries: the `temp` blocks of activation 0 of the names `tabs'` defines
and `tabs` does not. -/
def extraX (tabs tabs' : Tables) : Blk → Bool
  | .temp 0 n => (tabs.aux? n).isNone && (tabs'.aux? n).isSome
  | _ => false

theorem tempX_extraX (tabs tabs' : Tables) : TempX (extraX tabs tabs') := by
  intro b h
  unfold extraX at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-! ## What the check gives -/

theorem frameLocals_aux {tabs : Tables} {params : Array (Option AuxRef)}
    {l : AuxRef × Nat × Option Nat} (h : l ∈ (frameLocals tabs params).toList) :
    (tabs.aux? l.1).isSome = true := by
  unfold frameLocals at h
  simp only [Array.toList_filterMap, List.toList_toArray, List.mem_filterMap, List.mem_range] at h
  obtain ⟨n, -, hn⟩ := h
  split at hn
  · rename_i heq
    split at hn
    · obtain ⟨sz, -, rfl⟩ := Option.map_eq_some_iff.1 hn
      simp [heq]
    · cases hn
  · cases hn

/-- What `tabsAgreeMod` gives. -/
structure ModAgree (tabs tabs' : Tables) (f : Func) : Prop where
  ctx : Ctx.make tabs' f =
    { Ctx.make tabs f with tabs := tabs', locals := frameLocals tabs' (Ctx.make tabs f).params }
  outargs : outargsSize tabs' = outargsSize tabs
  locals : (frameLocals tabs' (Ctx.make tabs f).params).toList.filter
    (fun l => (tabs.aux? l.1).isSome) = (Ctx.make tabs f).locals.toList
  extra : ∀ l ∈ (frameLocals tabs' (Ctx.make tabs f).params).toList,
    (tabs.aux? l.1).isSome = false → tabs'.forgeable l.1 = false
  forgeable : ∀ l ∈ (Ctx.make tabs f).locals.toList, tabs'.forgeable l.1 = tabs.forgeable l.1
  value : ∀ id v, f.value? id = some v → AuxAgree tabs tabs' v.aux
  opOK : ∀ id v, f.value? id = some v → tamOpOK tabs f v = true

theorem mem_valueTab {f : Func} {id : ID} {v : Value} (hv : f.value? id = some v) :
    some v ∈ f.valueTab.toList := by
  have h1 : f.valueTab[id]? = some (some v) := Option.join_eq_some_iff.mp hv
  exact Array.mem_def.mp (Array.mem_of_getElem? h1)

theorem tabsAgreeMod_sound {tabs tabs' : Tables} {f : Func} (h : tabsAgreeMod tabs tabs' f = true) :
    ModAgree tabs tabs' f := by
  unfold tabsAgreeMod at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hps, hpty⟩, hls⟩, hext⟩, hforg⟩, hout⟩, hvals⟩, hops⟩ := h
  have hps' : abiParams tabs' f = abiParams tabs f := Array.toList_inj.mp hps
  have hty : ∀ p ∈ abiParams tabs f, tabs'.ty p.type = tabs.ty p.type :=
    fun p hp => Ty.eq_of_beq (hpty p (Array.mem_def.mp hp))
  refine ⟨?_, hout, hls, fun l hl hn => ?_, hforg, fun id v hv => ?_, fun id v hv => ?_⟩
  · unfold Ctx.make
    simp only [hps']
    congr 1
    · exact Array.map_congr_left fun o ho => Ty.eq_of_beq (hvals o (Array.mem_def.mp ho)).1
    · exact Array.map_congr_left fun p hp => hty p (Array.mem_filter.mp hp).1
    · exact Array.map_congr_left fun p hp => by rw [hty p (Array.mem_filter.mp hp).1]
  · rcases hext l hl with h1 | h1
    · rw [h1] at hn; cases hn
    · exact h1
  · exact valueAuxAgree_sound (hvals (some v) (mem_valueTab hv)).2
  · exact hops (some v) (mem_valueTab hv)

/-- A value's aux names no extra frame temporary. -/
theorem loc_extraX {tabs tabs' : Tables} {f : Func} (A : ModAgree tabs tabs' f) (x : ID)
    (fv : Value) (n : AuxRef) (hfv : f.value? x = some fv) (hn : fv.aux = some n) :
    extraX tabs tabs' (frameBlk tabs 0 n) = false := by
  have ha : tabs'.aux? n = tabs.aux? n := by
    have := (A.value x fv hfv).lookup
    rw [hn] at this; exact this
  unfold frameBlk
  split
  · rfl
  · show ((tabs.aux? n).isNone && (tabs'.aux? n).isSome) = false
    rw [ha]; cases tabs.aux? n <;> rfl

/-! ## The context in the extended tables -/

section
variable (env : Env) (ctx : Ctx) (l : Array (AuxRef × Nat × Option Nat))

theorem evalValue_locals (fr : Frame) (v : Value) :
    evalValue env { ctx with locals := l } fr v = evalValue env ctx fr v := by
  have he : evalOp env { ctx with locals := l } fr v = evalOp env ctx fr v :=
    funext fun argv => funext fun ty => evalOp_congr rfl rfl rfl rfl rfl rfl rfl
  unfold evalValue
  rw [he]

theorem evalAll_locals : ∀ (ids : List ID) (fr : Frame),
    evalAll env { ctx with locals := l } fr ids = evalAll env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    rw [evalAll, evalAll]
    cases hv : ctx.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [evalValue_locals]
      cases evalValue env ctx fr v with
      | ok x => exact evalAll_locals ids _
      | panic e m => rfl
      | stuck msg => rfl

theorem runLoop_locals : ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
    runLoop env { ctx with locals := l } fuel fr bid i = runLoop env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    have he : enterBlock env { ctx with locals := l } = enterBlock env ctx := by
      funext fr b i
      have ha : evalAll env { ctx with locals := l } = evalAll env ctx :=
        funext fun fr => funext fun ids => evalAll_locals env ctx l ids fr
      unfold enterBlock
      rw [ha]
    have ih : runLoop env { ctx with locals := l } fuel = runLoop env ctx fuel :=
      funext fun fr => funext fun bid => funext fun i => runLoop_locals fuel fr bid i
    rw [runLoop_succ, runLoop_succ, he, ih]

end

/-! ## The entry frame -/

section
variable {U : Blk → Prop}

theorem byte_avoids_of (hU : DAE.TempU U) {x : Byte} (h : ∀ n, Byte.Avoids (· = .temp 0 n) x) :
    Byte.Avoids U x := by
  cases x with
  | frag p k => intro hu; obtain ⟨n, hn⟩ := hU _ hu; exact h n hn
  | _ => trivial

theorem mem_avoids_of (hU : DAE.TempU U) {m : Mem} (h : ∀ n, m.Avoids (· = .temp 0 n)) :
    m.Avoids U := by
  intro b a hm hb x hx
  cases x with
  | frag p k =>
    intro hu
    obtain ⟨n, hn⟩ := hU _ hu
    exact h n b a hm (fun hb' => hb (hb' ▸ hn ▸ hu)) _ hx hn
  | _ => trivial

mutual
theorem val_avoids_of (hU : DAE.TempU U) : {v : Val} → (∀ n, v.Avoids (· = .temp 0 n)) →
    Val.Avoids U v
  | .ptr p, h => by intro hu; obtain ⟨n, hn⟩ := hU _ hu; exact h n hn
  | .tuple vs, h => valList_avoids_of hU (vs := vs) h
  | .agg vs, h => valList_avoids_of hU (vs := vs) h
  | .blob bs, h => fun x hx => byte_avoids_of hU fun n => h n x hx
  | .mem m, h => mem_avoids_of hU h
  | .int _ _, _ | .bool _, _ | .empty, _ | .poison, _ => trivial
theorem valList_avoids_of (hU : DAE.TempU U) : {vs : List Val} →
    (∀ n, Val.AvoidsList (· = .temp 0 n) vs) → Val.AvoidsList U vs
  | [], _ => trivial
  | _ :: _, h => ⟨val_avoids_of hU fun n => (h n).1, valList_avoids_of hU fun n => (h n).2⟩
end

theorem addGlobals_avoids {env : Env} (hg : ∀ g ∈ env.globals, DAE.BAv U g.2.data) {m : Mem}
    (hm : m.Avoids U) : (addGlobals env m).Avoids U := by
  unfold addGlobals
  generalize env.globals = gs at hg
  induction gs generalizing m with
  | nil => exact hm
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih ?_ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨name, a⟩ := g
    simp only
    split
    · exact hm
    · exact DAE.memAvoids_set hm fun _ => hg _ List.mem_cons_self

theorem frameAllocs_avoids {ctx : Ctx} {images : Array (Array Byte)}
    (hi : ∀ img ∈ images, DAE.BAv U img) {m : Mem} (hm : m.Avoids U) :
    (frameAllocs ctx images m).Avoids U := by
  unfold frameAllocs
  have h0 := DAE.memAvoids_set (b := .outargs ctx.act)
    (a := { data := Array.replicate (outargsSize ctx.tabs) .poison }) hm
    fun _ => DAE.bav_replicate_poison _ _
  generalize m.set (.outargs ctx.act) _ = m0 at h0
  rw [← Array.foldl_toList]
  generalize ctx.locals.toList = ls
  induction ls generalizing m0 with
  | nil => exact h0
  | cons l ls ih =>
    simp only [List.foldl_cons]
    refine ih _ (DAE.memAvoids_set h0 fun _ => ?_)
    obtain ⟨n, sz, pi⟩ := l
    simp only
    split
    · rename_i img himg
      split
      · simp only [Option.bind_eq_some_iff] at himg
        obtain ⟨k, -, hk⟩ := himg
        exact hi img (Array.mem_of_getElem? hk)
      · exact DAE.bav_replicate_poison _ _
    · exact DAE.bav_replicate_poison _ _

end

variable {X : Blk → Bool}

/-- Folding allocations over a list on the target side and over its kept elements on the source
side keeps the memories `EqX`, when a kept element allocates alike and a dropped one allocates a
block of `X`. -/
theorem foldl_filter_eqX {α : Type} (keep : α → Bool) (g g' : Mem → α → Mem) :
    ∀ (l : List α),
      (∀ e ∈ l, keep e = true → ∀ m m', EqX X m m' → EqX X (g m e) (g' m' e)) →
      (∀ e ∈ l, keep e = false → ∀ m m', EqX X m m' → EqX X m (g' m' e)) →
      ∀ m m', EqX X m m' → EqX X ((l.filter keep).foldl g m) (l.foldl g' m')
  | [], _, _, _, _, h => h
  | e :: l, hk, hn, m, m', h => by
    have ihk : ∀ e ∈ l, keep e = true → ∀ m m', EqX X m m' → EqX X (g m e) (g' m' e) :=
      fun e' he' => hk e' (List.mem_cons_of_mem _ he')
    have ihn : ∀ e ∈ l, keep e = false → ∀ m m', EqX X m m' → EqX X m (g' m' e) :=
      fun e' he' => hn e' (List.mem_cons_of_mem _ he')
    cases he : keep e
    · simp only [List.filter_cons, he, Bool.false_eq_true, ↓reduceIte, List.foldl_cons]
      exact foldl_filter_eqX keep g g' l ihk ihn _ _ (hn e List.mem_cons_self he m m' h)
    · simp only [List.filter_cons, he, ↓reduceIte, List.foldl_cons]
      exact foldl_filter_eqX keep g g' l ihk ihn _ _ (hk e List.mem_cons_self he m m' h)

/-- **The frames in the input and the extended tables** are equal without the extra blocks. -/
theorem frameMem_eqX {tabs tabs' : Tables} {f : Func} (A : ModAgree tabs tabs' f) (env : Env)
    (images : Array (Array Byte)) (mem : Mem) :
    EqX (extraX tabs tabs') (frameMem env (Ctx.make tabs f) images mem)
      (frameMem env (Ctx.make tabs' f) images mem) := by
  rw [A.ctx]
  unfold frameMem frameAllocs
  dsimp only
  rw [A.outargs, ← Array.foldl_toList, ← Array.foldl_toList, ← A.locals]
  refine foldl_filter_eqX _ _ _ _ (fun e he hk m m' h => ?_) (fun e he hk m m' h => ?_) _ _ rfl
  · obtain ⟨n, sz, pi⟩ := e
    have hin : (n, sz, pi) ∈ (Ctx.make tabs f).locals.toList := by
      rw [← A.locals]; exact List.mem_filter.2 ⟨he, hk⟩
    have hb : frameBlk tabs' (Ctx.make tabs f).act n = frameBlk tabs (Ctx.make tabs f).act n := by
      unfold frameBlk; rw [A.forgeable _ hin]
    dsimp only
    rw [hb]
    exact EqX.set h _ _
  · obtain ⟨n, sz, pi⟩ := e
    have hfo := A.extra _ he hk
    have hX : extraX tabs tabs' (frameBlk tabs' (Ctx.make tabs f).act n) = true := by
      rw [frameBlk_temp hfo]
      show ((tabs.aux? n).isNone && (tabs'.aux? n).isSome) = true
      have h1 : (tabs.aux? n).isSome = false := hk
      have h2 := frameLocals_aux he
      simp only at h1 h2
      simp [h2, Option.isNone_iff_eq_none, Option.isSome_eq_false_iff.mp h1]
    dsimp only
    unfold EqX
    rw [erase_set_X hX]
    exact h

/-! ## The simulation -/

/-- **One block step** of the simulation. -/
theorem step {env : Env} {tabs : Tables} {f : Func} (H : Hyps env X tabs f) {ce : CheckEnv}
    (hwf : WF ce f) {S T : Frame} {bid : ID} {i : Nat} (hA : FInv X tabs f S T ∧ bid ∈ f.blocks) :
    StepRelX X (fun S T bid _ => FInv X tabs f S T ∧ bid ∈ f.blocks)
      (blockStep env (Ctx.make tabs f) S bid i) (blockStep env (Ctx.make tabs f) T bid i) := by
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some b =>
  dsimp only
  have E := enterBlock_rel H hwf hA.2 hfb i hA.1
  cases hen : enterBlock env (Ctx.make tabs f) S b i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨m', hT, hm⟩ := E.2 e m hen
    rw [hT]
    exact ⟨m', rfl, hm⟩
  | ok G =>
    obtain ⟨GT, hGT, IG⟩ := E.1 G hen
    rw [hGT]
    dsimp only
    obtain ⟨hgo, hret⟩ := stepTerm_rel (G := G) (GT := GT) (b := b) (b' := b) rfl rfl rfl rfl IG.agree
    cases hstp : stepTerm G b with
    | ok n =>
      cases n with
      | goto e =>
        rw [hgo e hstp]
        refine ⟨GT, rfl, IG, ?_⟩
        obtain ⟨j, hj⟩ := Array.getElem?_of_mem (CopyElim.stepTerm_goto_mem hstp)
        exact (hwf.succLink bid b ⟨hA.2, hfb⟩ j e hj).1
      | ret rs m =>
        obtain ⟨rs', m', h1, h2, h3⟩ := hret rs m hstp
        rw [h1]
        exact ⟨rs', m', rfl, h2, h3⟩
    | panic e m => exact absurd hstp CopyElim.stepTerm_not_panic
    | stuck msg => exact True.intro

end GoFV.Proof.TabsMod

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt TabsMod TabsAgree

/-- **Running a function in tables with extra frame temporaries.** When
`tabsAgreeMod tabs tabs' f` holds, a defined run of a well-formed `f` in `tabs` on inputs that
hold no pointer into a frame temporary, in an environment whose contracts cannot tell whether
unreachable temporaries exist, has the same outcome in `tabs'` (the same results and memory, or
the same panic with the same memory once the frames are dropped). -/
theorem run_tabsAgreeMod {tabs tabs' : Tables} {f : Func} {ce : CheckEnv}
    (h : tabsAgreeMod tabs tabs' f = true) (hf : check ce f = .ok ()) {env : Env}
    (hE : env.TempOblivious) {args : List Val} {mem : Mem} (hinit : InitAvoids env args mem)
    {fuel : Nat} (hd : (run env tabs f args mem fuel).Defined) :
    OutcomeRefines 0 (run env tabs f args mem fuel) (run env tabs' f args mem fuel) := by
  have A := tabsAgreeMod_sound h
  have hwf := check_wf hf
  have hX := tempX_extraX tabs tabs'
  have hU := tempU_of hX
  have H : Hyps env (extraX tabs tabs') tabs f :=
    ⟨hE, hX, A.opOK, fun x fv n hfv hn => loc_extraX A x fv n hfv hn⟩
  have hloop : runLoop env (Ctx.make tabs' f) fuel = runLoop env (Ctx.make tabs f) fuel := by
    funext fr bid i
    rw [A.ctx]
    have hH : ∀ id v, ({ (Ctx.make tabs f) with locals := (frameLocals tabs' (Ctx.make tabs f).params) } : Ctx).f.value? id = some v →
        AuxAgree ({ (Ctx.make tabs f) with locals := (frameLocals tabs' (Ctx.make tabs f).params) } : Ctx).tabs tabs' v.aux := fun id v hv => A.value id v hv
    have h1 := runLoop_tabs (ctx := { (Ctx.make tabs f) with locals := (frameLocals tabs' (Ctx.make tabs f).params) }) hH env fuel fr bid i
    exact h1.trans (runLoop_locals env (Ctx.make tabs f) (frameLocals tabs' (Ctx.make tabs f).params) fuel fr bid i)
  unfold run runCtx at hd ⊢
  rw [hloop]
  have hpar : (Ctx.make tabs' f).params = (Ctx.make tabs f).params := by rw [A.ctx]
  have houts : (Ctx.make tabs' f).outs = (Ctx.make tabs f).outs := by rw [A.ctx]
  have hact : (Ctx.make tabs' f).act = (Ctx.make tabs f).act := by rw [A.ctx]
  have hfe : (Ctx.make tabs' f).f.entry = (Ctx.make tabs f).f.entry := by rw [A.ctx]
  rw [hpar, houts, hact, hfe]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hargs : ∀ v ∈ args, Val.Avoids (fun b => extraX tabs tabs' b = true) v := fun v hv =>
      val_avoids_of hU fun n => (hinit 0 n).1 v hv
    have hmem : mem.Avoids (fun b => extraX tabs tabs' b = true) :=
      mem_avoids_of hU fun n => (hinit 0 n).2.1
    have hglob : ∀ g ∈ env.globals, DAE.BAv (fun b => extraX tabs tabs' b = true) g.2.data :=
      fun g hg x hx => byte_avoids_of hU fun n => (hinit 0 n).2.2.2 g hg x hx
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
    have hvsz : (Ctx.make tabs' f).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size := by rw [A.ctx]
    have I0 : FInv (extraX tabs tabs') tabs f (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs' f) args mem) := by
      refine ⟨by simp [Ctx.make, entryFrame], by simp [entryFrame, hvsz], ?_, ?_,
        fun z y hz => ?_, fun z y hz => ?_, typed_replicate _ _ _ rfl,
        ⟨himg, rfl, frameAllocs_avoids himg (addGlobals_avoids hglob hmem)⟩⟩
      · unfold entryFrame; rw [hpty, hvsz]
      · unfold entryFrame; rw [hpty]; exact frameMem_eqX A env _ mem
      · simp [entryFrame, Array.getElem?_replicate] at hz
      · simp [entryFrame, Array.getElem?_replicate] at hz
    exact finish_rel hX hd (runLoop_simX
      (fun S T bid _ => FInv (extraX tabs tabs') tabs f S T ∧ bid ∈ f.blocks)
      (fun S T bid i hA => step H hwf hA) fuel _ _ _ _ ⟨I0, hwf.entry⟩ (finish_defined hd))

/-- **A refinement against tables with extra frame temporaries is one against the input
tables** (`tabsAgreeMod tabs tabs' f`, for inputs and environments as in `run_tabsAgreeMod`). -/
theorem refinesFrom_of_tabsAgreeMod {P : Env → List Val → Mem → Prop} {tabs tabs' tabs'' : Tables}
    {f g : Func} {ce : CheckEnv}
    (hP : ∀ env args mem, P env args mem → env.TempOblivious ∧ InitAvoids env args mem)
    (h : tabsAgreeMod tabs tabs' f = true) (hf : check ce f = .ok ())
    (hr : RefinesFrom P tabs'' g tabs' f) : RefinesFrom P tabs'' g tabs f := by
  intro env args mem hp fuel hd
  obtain ⟨hE, hinit⟩ := hP env args mem hp
  have h1 := run_tabsAgreeMod h hf hE hinit hd
  obtain ⟨fuel', h2⟩ := hr env args mem hp fuel h1.defined_right
  exact ⟨fuel', h1.trans h2⟩

end GoFV.Proof
