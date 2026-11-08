import GoFV.Proof.Refine

variable [GoFV.SSA.Sem.Addrs]

/-!
# `run` ignores positions, use counts, branch predictions and caches

`eraseF f` forgets what `GoFV.SSA.run` never reads: value and block positions, use counts,
branch predictions and the analysis caches. Functions with the same erasure have the same runs
(`run_congr`). Passes that only move statement marks or refresh caches (`number lines`) refine
their input by this lemma alone.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

-- Unification must never unfold the scheduler (`kahn` is a big imperative loop).
attribute [local irreducible] schedule kahn schedValid

/-- A value without its position and use count. -/
def eraseV (v : Value) : Value := { v with pos := default, uses := 0 }

/-- A block without its position and branch prediction. -/
def eraseB (b : Block) : Block := { b with pos := default, likely := .unknown }

/-- A function without positions, use counts, branch predictions and caches. -/
def eraseF (f : Func) : Func :=
  { f with valueTab := f.valueTab.map (Option.map eraseV),
           blockTab := f.blockTab.map (Option.map eraseB), cache := {} }

theorem value?_eraseF (f : Func) (id : ID) : (eraseF f).value? id = (f.value? id).map eraseV := by
  simp only [Func.value?, eraseF, Array.getElem?_map]
  cases f.valueTab[id]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem block?_eraseF (f : Func) (id : ID) : (eraseF f).block? id = (f.block? id).map eraseB := by
  simp only [Func.block?, eraseF, Array.getElem?_map]
  cases f.blockTab[id]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- What a run reads of the function, as seen through a context: everything but erased
fields. -/
structure CtxEq (ctx ctx' : Ctx) : Prop where
  tabs : ctx.tabs = ctx'.tabs
  tys : ctx.tys = ctx'.tys
  sched : ctx.sched = ctx'.sched
  params : ctx.params = ctx'.params
  paramTys : ctx.paramTys = ctx'.paramTys
  outs : ctx.outs = ctx'.outs
  locals : ctx.locals = ctx'.locals
  act : ctx.act = ctx'.act
  value : ∀ id, (ctx.f.value? id).map eraseV = (ctx'.f.value? id).map eraseV
  block : ∀ id, (ctx.f.block? id).map eraseB = (ctx'.f.block? id).map eraseB

theorem evalValue_eraseV (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) :
    evalValue env ctx fr (eraseV v) = evalValue env ctx fr v := (rfl)

theorem evalValue_ctx {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') (fr : Frame) (v : Value) :
    evalValue env ctx fr v = evalValue env ctx' fr v := by
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
  obtain ⟨h1, h2, -, h4, -, -, -, h8, -, -⟩ := h
  dsimp only at h1 h2 h4 h8
  subst h1 h2 h4 h8
  rfl

theorem entryFrame_ctx {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx')
    (hsize : ctx.f.valueTab.size = ctx'.f.valueTab.size) (args : List Val) (mem : Mem) :
    entryFrame env ctx args mem = entryFrame env ctx' args mem := by
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
  obtain ⟨h1, -, -, -, h5, -, h7, h8, -, -⟩ := h
  dsimp only at h1 h5 h7 h8 hsize
  subst h1 h5 h7 h8
  unfold entryFrame frameMem frameAllocs
  rw [hsize]

theorem stepTerm_eraseB (fr : Frame) (b : Block) : stepTerm fr (eraseB b) = stepTerm fr b := (rfl)

/-- Two option values with equal erasures: both absent or both present with equal erasures. -/
theorem map_eraseV_eq {o o' : Option Value} (h : o.map eraseV = o'.map eraseV) :
    (o = none ∧ o' = none) ∨ ∃ v v', o = some v ∧ o' = some v' ∧ eraseV v = eraseV v' := by
  cases o <;> cases o' <;> simp_all

theorem map_eraseB_eq {o o' : Option Block} (h : o.map eraseB = o'.map eraseB) :
    (o = none ∧ o' = none) ∨ ∃ b b', o = some b ∧ o' = some b' ∧ eraseB b = eraseB b' := by
  cases o <;> cases o' <;> simp_all

theorem evalAll_congr {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') :
    ∀ (fr : Frame) (ids : List ID), evalAll env ctx fr ids = evalAll env ctx' fr ids := by
  intro fr ids
  induction ids generalizing fr with
  | nil => rfl
  | cons id ids ih =>
    unfold evalAll
    rcases map_eraseV_eq (h.value id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      dsimp only
      rw [evalValue_ctx h, ← evalValue_eraseV env ctx' fr v, he, evalValue_eraseV]
      split <;> simp only [ih]

theorem enterBlock_congr {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') (fr : Frame)
    {b b' : Block} (hb : eraseB b = eraseB b') (i : Nat) :
    enterBlock env ctx fr b i = enterBlock env ctx' fr b' i := by
  have hv : b.values = b'.values := by have := congrArg Block.values hb; exact this
  have hid : b.id = b'.id := by have := congrArg Block.id hb; exact this
  unfold enterBlock
  rw [hv, hid, h.sched]
  congr 1
  · congr 1
    funext id
    rw [h.tys]
    rcases map_eraseV_eq (h.value id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      have hop : v.op = v'.op := by have := congrArg Value.op he; exact this
      have hargs : v.args = v'.args := by have := congrArg Value.args he; exact this
      simp only [hop, hargs]
  · funext phis
    simp only [evalAll_congr h]

theorem runLoop_congr {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoop env ctx fuel fr bid i = runLoop env ctx' fuel fr bid i := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro fr bid i
    rw [runLoop_succ, runLoop_succ]
    rcases map_eraseB_eq (h.block bid) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      simp only
      rw [enterBlock_congr h fr he i]
      split
      · rfl
      · rfl
      · next fr1 _ =>
        rw [← stepTerm_eraseB fr1 b, he, stepTerm_eraseB]
        split <;> simp only [ih]

theorem schedNodes_congr {f g : Func} (hv : ∀ id, (f.value? id).map eraseV = (g.value? id).map eraseV)
    {b b' : Block} (hb : b.values = b'.values) : schedNodes f b = schedNodes g b' := by
  unfold schedNodes
  rw [hb]
  congr 1
  funext id
  rcases map_eraseV_eq (hv id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
  · rw [h1, h2]
  · rw [h1, h2]
    have hop : v.op = v'.op := by have := congrArg Value.op he; exact this
    have hargs : v.args = v'.args := by have := congrArg Value.args he; exact this
    have hid : v.id = v'.id := by have := congrArg Value.id he; exact this
    simp only [hop, hargs, hid]

theorem schedule_congr {f g : Func} (hv : ∀ id, (f.value? id).map eraseV = (g.value? id).map eraseV)
    {b b' : Block} (hb : b.values = b'.values) : schedule f b = schedule g b' := by
  unfold schedule
  rw [schedNodes_congr hv hb]

theorem map_eq_of_factor {α β γ : Type} {t t' : Array α} {G : α → γ} {H : γ → β}
    {F F' : α → β} (hF : ∀ a, F a = H (G a)) (hF' : ∀ a, F' a = H (G a))
    (h : t.map G = t'.map G) : t.map F = t'.map F' := by
  have e1 : t.map F = (t.map G).map H := by
    rw [Array.map_map]; congr 1; funext a; exact hF a
  have e2 : t'.map F' = (t'.map G).map H := by
    rw [Array.map_map]; congr 1; funext a; exact hF' a
  rw [e1, e2, h]

theorem tys_make (tabs : Tables) {f g : Func}
    (hvt : f.valueTab.map (Option.map eraseV) = g.valueTab.map (Option.map eraseV)) :
    (Ctx.make tabs f).tys = (Ctx.make tabs g).tys :=
  map_eq_of_factor (H := valueTy (typeShapes tabs))
    (fun o => by cases o <;> rfl) (fun o => by cases o <;> rfl) hvt

theorem bind_schedule_erase {f g : Func}
    (hv : ∀ id, (f.value? id).map eraseV = (g.value? id).map eraseV) (o : Option Block) :
    o.bind (schedule f) = (o.map eraseB).bind (schedule g) := by
  cases o with
  | none => simp only [Option.map_none, Option.bind_none]
  | some b =>
    rw [Option.map_some, Option.bind_some, Option.bind_some]
    exact schedule_congr hv rfl

theorem sched_make (tabs : Tables) {f g : Func}
    (hv : ∀ id, (f.value? id).map eraseV = (g.value? id).map eraseV)
    (hbt : f.blockTab.map (Option.map eraseB) = g.blockTab.map (Option.map eraseB)) :
    (Ctx.make tabs f).sched = (Ctx.make tabs g).sched :=
  map_eq_of_factor (H := fun o => o.bind (schedule f)) (G := Option.map eraseB)
    (F := fun o => o.bind (schedule f)) (F' := fun o => o.bind (schedule g))
    (bind_schedule_erase (fun _ => rfl)) (bind_schedule_erase (fun id => (hv id).symm)) hbt

theorem params_make (tabs : Tables) {f g : Func} (hown : f.ownAux = g.ownAux) :
    (Ctx.make tabs f).params = (Ctx.make tabs g).params := by
  unfold Ctx.make abiParams
  simp only [hown]

theorem ctxEq_make (tabs : Tables) {f g : Func} (h : eraseF f = eraseF g) :
    CtxEq (Ctx.make tabs f) (Ctx.make tabs g) := by
  have hv : ∀ id, (f.value? id).map eraseV = (g.value? id).map eraseV := fun id => by
    rw [← value?_eraseF, ← value?_eraseF, h]
  have hb : ∀ id, (f.block? id).map eraseB = (g.block? id).map eraseB := fun id => by
    rw [← block?_eraseF, ← block?_eraseF, h]
  have hvt : f.valueTab.map (Option.map eraseV) = g.valueTab.map (Option.map eraseV) :=
    congrArg Func.valueTab h
  have hbt : f.blockTab.map (Option.map eraseB) = g.blockTab.map (Option.map eraseB) :=
    congrArg Func.blockTab h
  have hown : f.ownAux = g.ownAux := by have := congrArg Func.ownAux h; exact this
  have hps : abiParams tabs f = abiParams tabs g := by unfold abiParams; rw [hown]
  have hp : (Ctx.make tabs f).params = (Ctx.make tabs g).params := params_make tabs hown
  refine ⟨rfl, tys_make tabs hvt, sched_make tabs hv hbt, hp, ?_, ?_, ?_, rfl, hv, hb⟩
  · unfold Ctx.make; simp only [hps]
  · unfold Ctx.make; simp only [hps]
  · unfold Ctx.make; simp only [hps]

/-- Functions with the same erasure have the same runs. -/
theorem run_congr {f g : Func} (h : eraseF f = eraseF g) (env : Env) (tabs : Tables)
    (args : List Val) (mem : Mem) (fuel : Nat) :
    run env tabs f args mem fuel = run env tabs g args mem fuel := by
  have hc := ctxEq_make tabs h
  have hsize : f.valueTab.size = g.valueTab.size := by
    have e1 : (eraseF f).valueTab.size = f.valueTab.size := Array.size_map ..
    have e2 : (eraseF g).valueTab.size = g.valueTab.size := Array.size_map ..
    rw [← e1, ← e2, h]
  have hentry : f.entry = g.entry := by have := congrArg Func.entry h; exact this
  show runCtx env (Ctx.make tabs f) args mem fuel = runCtx env (Ctx.make tabs g) args mem fuel
  unfold runCtx
  rw [hc.params]
  split
  · rfl
  · rw [runLoop_congr hc, hc.outs, hc.act, entryFrame_ctx hc hsize]
    show finish env _ (deferInfo tabs) _ (runLoop env _ fuel _ f.entry 0) =
      finish env _ (deferInfo tabs) _ (runLoop env _ fuel _ g.entry 0)
    rw [hentry]

theorem Refines.of_eraseF {tabs : Tables} {f g : Func} (h : eraseF g = eraseF f) :
    Refines tabs g tabs f :=
  Refines.of_run_eq fun env args mem fuel => run_congr h env tabs args mem fuel

end GoFV.Proof
