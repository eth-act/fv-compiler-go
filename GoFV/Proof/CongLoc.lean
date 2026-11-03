import GoFV.Proof.CongL
import GoFV.Proof.RefineLoc
import GoFV.Proof.Frame

/-!
# `runLoc` ignores block order, positions, predictions, caches and the lowered-pass flags

`runLoc` reads of a function what `runL` reads (`eraseFL`: entry, `ownAux`, the value and block
tables up to positions, use counts and branch predictions) and its homes and temporary
registers (`f.low.regAlloc`, `f.low.tempRegs`). Functions that agree on these have the same
`runLoc`s (`runLoc_congr`), so `loop rotate` (block order and `Hotness`) refines its input by
this lemma alone.

The value-level lemmas take weaker hypotheses, for passes that move values between blocks
(`trim`):

* `evalOpL_ctxW`: an op reads of its context the tables, the activation's layout and the ops of
  its first argument (`Arm64.signExtends`);
* `LocCtxW lc lc'`: two `runLoc` contexts with the same layout, homes and temporary registers;
  `stepLoc_congrW`: a value runs alike under two such contexts when it and its arguments have the
  same shapes and its first argument the same op.
* `enterListLoc`: `enterBlockLoc` as a recursion over the block's value list
  (`enterBlockLoc_eq`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

-- Unification must never unfold the scheduler (`kahn` is a big imperative loop).
attribute [local irreducible] schedule kahn schedValid

/-! ## Ops -/

/-- Whether the first argument of `v` under `ctx` sign-extends, as `ARM64MOVDreg` reads it
(`Arm64.signExtendsIn`). -/
def sxArgLoc (ctx : Ctx) (v : Value) : Option Bool :=
  (v.args[0]?.bind ctx.f.value?).map (Arm64.signExtendsIn ctx.f.value?)

/-- What `evalOpL` reads of its context: the tables, the activation's layout and the op of the
first argument. -/
theorem evalOpL_ctxW {fa : Bool} {env : Env} {ctx ctx' : Ctx} (ht : ctx.tabs = ctx'.tabs)
    (hp : ctx.params = ctx'.params) (hpt : ctx.paramTys = ctx'.paramTys)
    (ho : ctx.outs = ctx'.outs) (hl : ctx.locals = ctx'.locals) (ha : ctx.act = ctx'.act)
    (hd : ctx.defers = ctx'.defers) (fr : Frame) (v : Value) (argv : List Val) (ty : Ty)
    (hsx : sxArgLoc ctx v = sxArgLoc ctx' v) :
    evalOpL fa env ctx fr v argv ty = evalOpL fa env ctx' fr v argv ty := by
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act, defers⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act', defers'⟩ := ctx'
  dsimp only at ht hp hpt ho hl ha hd
  subst ht hp hpt ho hl ha hd
  unfold sxArgLoc at hsx
  dsimp only at hsx
  simp only [evalOpL, arm64Op, hsx]
  rfl

theorem evalOpL_eraseV (fa : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value)
    (argv : List Val) (ty : Ty) :
    evalOpL fa env ctx fr (eraseV v) argv ty = evalOpL fa env ctx fr v argv ty := (rfl)

/-! ## Contexts -/

/-- Two `runLoc` contexts with the same tables, activation layout, homes and temporary
registers. -/
structure LocCtxW (lc lc' : LocCtx) : Prop where
  tabs : lc.ctx.tabs = lc'.ctx.tabs
  params : lc.ctx.params = lc'.ctx.params
  paramTys : lc.ctx.paramTys = lc'.ctx.paramTys
  outs : lc.ctx.outs = lc'.ctx.outs
  locals : lc.ctx.locals = lc'.ctx.locals
  act : lc.ctx.act = lc'.ctx.act
  defers : lc.ctx.defers = lc'.ctx.defers
  homes : lc.homes = lc'.homes
  temps : lc.temps = lc'.temps

theorem read_congrW {lc lc' : LocCtx} (h : LocCtxW lc lc') (s : LocState) {id : ID}
    (hty : lc.ty id = lc'.ty id) : s.read lc id = s.read lc' id := by
  unfold LocState.read LocCtx.home
  rw [h.homes, hty]

theorem write_congrW {lc lc' : LocCtx} (h : LocCtxW lc lc') (s : LocState) {id : ID}
    (hty : lc.ty id = lc'.ty id) (x : Val) : s.write lc id x = s.write lc' id x := by
  unfold LocState.write LocCtx.home LocState.setSlot
  rw [h.homes, hty, h.tabs]

theorem clobber_congrW {lc lc' : LocCtx} (h : LocCtxW lc lc') (s : LocState) (v : Value) :
    s.clobber lc v = s.clobber lc' v := by
  unfold LocState.clobber LocCtx.regOf LocCtx.home
  rw [h.homes, h.temps]

theorem stepLoc_eraseV (env : Env) (lc : LocCtx) (s : LocState) (v : Value) :
    stepLoc env lc s (eraseV v) = stepLoc env lc s v := (rfl)

/-- A value runs alike under two `LocCtxW` contexts when it and its arguments have the same
shapes there and its first argument the same op. -/
theorem stepLoc_congrW {env : Env} {lc lc' : LocCtx} (h : LocCtxW lc lc') (s : LocState)
    (v : Value) (hty : lc.ty v.id = lc'.ty v.id) (hargs : ∀ a ∈ v.args, lc.ty a = lc'.ty a)
    (hsx : sxArgLoc lc.ctx v = sxArgLoc lc'.ctx v) :
    stepLoc env lc s v = stepLoc env lc' s v := by
  have hm : v.args.toList.mapM (s.read lc) = v.args.toList.mapM (s.read lc') :=
    mapM_congr' _ fun a ha => read_congrW h s (hargs a (Array.mem_toList_iff.1 ha))
  have hw : ∀ s x, LocState.write lc s v.id x = LocState.write lc' s v.id x :=
    fun s x => write_congrW h s hty x
  unfold stepLoc
  simp only [LocCtx.home, h.homes, hm, hty, clobber_congrW h s v, hw,
    evalOpL_ctxW (fa := LMode.loc.faulting) (env := env) h.tabs h.params h.paramTys h.outs
      h.locals h.act h.defers s.fr v _ _ hsx]
  rfl

/-! ## Blocks as value lists -/

/-- `enterBlockLoc` on a list of value IDs. -/
def enterListLoc (env : Env) (lc : LocCtx) (s : LocState) : List ID → Res LocState
  | [] => .ok s
  | id :: ids =>
    match lc.ctx.f.value? id with
    | none => .stuck s!"v{id} is not in the function"
    | some v =>
      match stepLoc env lc s v with
      | .ok s' => enterListLoc env lc s' ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg

theorem enterBlockLoc_eq (env : Env) (lc : LocCtx) (s : LocState) (b : Block) :
    enterBlockLoc env lc s b = enterListLoc env lc s b.values.toList := by
  unfold enterBlockLoc
  simp only [bind_pure]
  rw [← Array.forIn_toList]
  generalize b.values.toList = l
  induction l generalizing s with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.forIn_cons, enterListLoc]
    cases lc.ctx.f.value? id with
    | none => rfl
    | some v =>
      simp only
      cases stepLoc env lc s v with
      | ok s' => exact ih s'
      | panic e m => rfl
      | stuck msg => rfl

/-! ## `eraseFL`-equal functions with the same homes run alike -/

theorem locCtxW_make (tabs : Tables) {f g : Func} (h : eraseFL f = eraseFL g)
    (hra : f.low.regAlloc = g.low.regAlloc) (htr : f.low.tempRegs = g.low.tempRegs) :
    LocCtxW (LocCtx.make tabs f) (LocCtx.make tabs g) := by
  have hc := ctxEq_makeL tabs h
  have hsize : f.valueTab.size = g.valueTab.size := by
    have e1 : (eraseFL f).valueTab.size = f.valueTab.size := Array.size_map ..
    have e2 : (eraseFL g).valueTab.size = g.valueTab.size := Array.size_map ..
    rw [← e1, ← e2, h]
  have hown : f.ownAux = g.ownAux := by have := congrArg Func.ownAux h; exact this
  refine ⟨hc.tabs, hc.params, hc.paramTys, hc.outs, hc.locals, hc.act, ?_, ?_, ?_⟩
  · show (Ctx.makeL tabs f).defers = (Ctx.makeL tabs g).defers
    unfold Ctx.makeL; split <;> split <;> rfl
  · show (LocCtx.make tabs f).homes = (LocCtx.make tabs g).homes
    unfold LocCtx.make; simp only [hsize, hra]
  · show (LocCtx.make tabs f).temps = (LocCtx.make tabs g).temps
    unfold LocCtx.make; simp only [hsize, htr]

/-- `runLoc`'s contexts of two functions with the same `eraseFL`, homes and temporary
registers. -/
structure LocEq (lc lc' : LocCtx) : Prop where
  w : LocCtxW lc lc'
  ctx : CtxEq lc.ctx lc'.ctx

theorem stepLoc_congr {env : Env} {lc lc' : LocCtx} (h : LocEq lc lc') (s : LocState)
    (v : Value) : stepLoc env lc s v = stepLoc env lc' s v := by
  have hty : ∀ id, lc.ty id = lc'.ty id := fun id => by unfold LocCtx.ty; rw [h.ctx.tys]
  refine stepLoc_congrW h.w s v (hty _) (fun a _ => hty a) ?_
  unfold sxArgLoc
  cases v.args[0]? with
  | none => rfl
  | some a =>
    simp only [Option.bind_some]
    rcases map_eraseV_eq (h.ctx.value a) with ⟨h1, h2⟩ | ⟨u, u', h1, h2, he⟩
    · rw [h1, h2]; rfl
    · rw [h1, h2]
      simp only [Option.map_some, signExtendsIn_eraseV h.ctx.value he]

theorem enterListLoc_congr {env : Env} {lc lc' : LocCtx} (h : LocEq lc lc') :
    ∀ (s : LocState) (ids : List ID), enterListLoc env lc s ids = enterListLoc env lc' s ids := by
  intro s ids
  induction ids generalizing s with
  | nil => rfl
  | cons id ids ih =>
    unfold enterListLoc
    rcases map_eraseV_eq (h.ctx.value id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      dsimp only
      rw [stepLoc_congr h, ← stepLoc_eraseV env lc' s v, he, stepLoc_eraseV]
      split <;> simp only [ih]

theorem control_congr {lc lc' : LocCtx} (h : LocEq lc lc') (s : LocState) (c : ID) :
    s.control lc c = s.control lc' c := by
  have hty : ∀ id, lc.ty id = lc'.ty id := fun id => by unfold LocCtx.ty; rw [h.ctx.tys]
  have hm : ∀ l : List ID, l.mapM (s.read lc) = l.mapM (s.read lc') := fun l =>
    mapM_congr' _ fun a _ => read_congrW h.w s (hty a)
  unfold LocState.control
  rcases map_eraseV_eq (h.ctx.value c) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
  · rw [h1, h2]
  · rw [h1, h2]
    have hop : v.op = v'.op := by have := congrArg Value.op he; exact this
    have hargs : v.args = v'.args := by have := congrArg Value.args he; exact this
    simp only [hop, hargs, hm, read_congrW h.w s (hty c), hty c]

theorem stepTermLoc_congr {lc lc' : LocCtx} (h : LocEq lc lc') (s : LocState) {b b' : Block}
    (hb : eraseB b = eraseB b') : stepTermLoc lc s b = stepTermLoc lc' s b' := by
  have hc : b.controls = b'.controls := by have := congrArg Block.controls hb; exact this
  have ht : ∀ fr, stepTermL fr b = stepTermL fr b' := fun fr => by
    rw [← stepTermL_eraseB fr b, hb, stepTermL_eraseB]
  unfold stepTermLoc
  simp only [hc, control_congr h s, ht]

theorem runLoopLoc_congr {env : Env} {lc lc' : LocCtx} (h : LocEq lc lc') :
    ∀ (fuel : Nat) (s : LocState) (bid : ID),
      runLoopLoc env lc fuel s bid = runLoopLoc env lc' fuel s bid := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro s bid
    rw [runLoopLoc_succ, runLoopLoc_succ]
    rcases map_eraseB_eq (h.ctx.block bid) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      have hv : b.values = b'.values := by have := congrArg Block.values he; exact this
      simp only
      rw [enterBlockLoc_eq, enterBlockLoc_eq, hv, enterListLoc_congr h]
      split
      · rfl
      · rfl
      · next s1 _ =>
        rw [stepTermLoc_congr h s1 he]
        split <;> simp only [ih]

/-- **Functions with the same `eraseFL`, homes and temporary registers have the same
`runLoc`s.** -/
theorem runLoc_congr {f g : Func} (h : eraseFL f = eraseFL g)
    (hra : f.low.regAlloc = g.low.regAlloc) (htr : f.low.tempRegs = g.low.tempRegs)
    (env : Env) (tabs : Tables) (args : List Val) (mem : Mem) (fuel : Nat) :
    runLoc env tabs f args mem fuel = runLoc env tabs g args mem fuel := by
  have hc := ctxEq_makeL tabs h
  have hw := locCtxW_make tabs h hra htr
  have hl : LocEq (LocCtx.make tabs f) (LocCtx.make tabs g) := ⟨hw, hc⟩
  have hsize : f.valueTab.size = g.valueTab.size := by
    have e1 : (eraseFL f).valueTab.size = f.valueTab.size := Array.size_map ..
    have e2 : (eraseFL g).valueTab.size = g.valueTab.size := Array.size_map ..
    rw [← e1, ← e2, h]
  have hsize' : (Ctx.makeL tabs f).f.valueTab.size = (Ctx.makeL tabs g).f.valueTab.size := by
    unfold Ctx.makeL; split <;> split <;> exact hsize
  have hentry : f.entry = g.entry := by have := congrArg Func.entry h; exact this
  have hent' : (Ctx.makeL tabs f).f.entry = (Ctx.makeL tabs g).f.entry := by
    unfold Ctx.makeL; split <;> split <;> exact hentry
  have hctx : ∀ f, (LocCtx.make tabs f).ctx = Ctx.makeL tabs f := fun _ => rfl
  have hdef : (Ctx.makeL tabs f).defers = (Ctx.makeL tabs g).defers := hw.defers
  unfold runLoc runCtxLoc
  simp only [runLoopLoc_congr hl]
  simp only [hctx, hc.params, hc.outs, hc.act, hdef, entryFrame_ctx hc hsize', hent']

theorem RefinesLoc.of_eraseFL {tabs : Tables} {f g : Func} (h : eraseFL g = eraseFL f)
    (hra : g.low.regAlloc = f.low.regAlloc) (htr : g.low.tempRegs = f.low.tempRegs) :
    RefinesLoc tabs g tabs f :=
  RefinesLoc.of_runLoc_eq fun env args mem fuel => runLoc_congr h hra htr env tabs args mem fuel

end GoFV.Proof
