import GoFV.Opt.LateLowerCheck
import GoFV.Proof.Low.TabsAgreeL
import GoFV.Proof.EvalOpLDispatch

/-!
# `late lower`'s renames refine (issue #385)

`runL_normF`: undoing `late lower`'s renames (`GoFV.Opt.LateLowerCheck.normV`: `MOVDnop` to
`MOVDreg`, `ZERO` to `MOVDconst [0]`) does not change a function's `runL`s. The renamed ops are
evaluated alike (`evalValueL_normV`), have the same scheduling priority and `Phi`-ness
(`schedNodes_normF`, so `kahn` orders the blocks alike), and neither sign-extends
(`signExtendsIn_normV`). So when `renameB` accepts `g` for `f` (equal after `normV` up to
`eraseFL`, tables agreeing for `f`), `g` runs as `f` (`runL_congr`, `runL_tabsAgreeL`):
`lateLower_refinesL`.
-/

namespace GoFV.Proof.LateLowerL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LateLowerCheck GoFV.Proof

attribute [local irreducible] kahn schedValid greedy

/-! ## `normV` -/

theorem normV_cases (v : Value) :
    normV v = v ∨ (v.op = .ARM64MOVDnop ∧ normV v = { v with op := .ARM64MOVDreg }) ∨
      (v.op = .ARM64ZERO ∧ v.auxInt = 0 ∧ normV v = { v with op := .ARM64MOVDconst }) := by
  unfold normV
  split
  · rename_i h; exact .inr (.inl ⟨h, rfl⟩)
  · split
    · rename_i h; exact .inr (.inr ⟨h.1, h.2, rfl⟩)
    · exact .inl rfl

theorem normV_id (v : Value) : (normV v).id = v.id := by
  rcases normV_cases v with h | ⟨-, h⟩ | ⟨-, -, h⟩ <;> rw [h]

theorem normV_args (v : Value) : (normV v).args = v.args := by
  rcases normV_cases v with h | ⟨-, h⟩ | ⟨-, -, h⟩ <;> rw [h]

theorem normV_type (v : Value) : (normV v).type = v.type := by
  rcases normV_cases v with h | ⟨-, h⟩ | ⟨-, -, h⟩ <;> rw [h]

/-- What `runL` reads of an op other than its evaluation agrees on `normV`. -/
theorem normV_op {P : Op → Prop}
    (hr : P .ARM64MOVDreg ↔ P .ARM64MOVDnop) (hz : P .ARM64MOVDconst ↔ P .ARM64ZERO) (v : Value) :
    P (normV v).op ↔ P v.op := by
  rcases normV_cases v with h | ⟨ho, h⟩ | ⟨ho, -, h⟩
  · rw [h]
  · rw [h, ho]; exact hr
  · rw [h, ho]; exact hz

theorem normV_phi (v : Value) : ((normV v).op == .Phi) = (v.op == .Phi) := by
  have := normV_op (P := fun o => (o == .Phi) = true) (by decide) (by decide) v
  cases h1 : ((normV v).op == .Phi) <;> cases h2 : (v.op == .Phi) <;> simp_all

theorem normV_prio (v : Value) : prio (normV v).op = prio v.op := by
  rcases normV_cases v with h | ⟨ho, h⟩ | ⟨ho, -, h⟩
  · rw [h]
  · rw [h, ho]; rfl
  · rw [h, ho]; rfl

theorem normV_generic (v : Value) : (normV v).op.generic = v.op.generic := by
  rcases normV_cases v with h | ⟨ho, h⟩ | ⟨ho, -, h⟩
  · rw [h]
  · rw [h, ho]; rfl
  · rw [h, ho]; rfl

theorem value?_normF (f : Func) (id : ID) : (normF f).value? id = (f.value? id).map normV := by
  simp only [Func.value?, normF, Array.getElem?_map]
  cases f.valueTab[id]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem block?_normF (f : Func) (id : ID) : (normF f).block? id = f.block? id := rfl

theorem signExtendsIn_normV (val? : ID → Option Value) (u : Value) :
    Arm64.signExtendsIn (fun x => (val? x).map normV) (normV u) = Arm64.signExtendsIn val? u := by
  unfold Arm64.signExtendsIn
  rw [normV_args]
  have hs : Arm64.signExtends (normV u).op = Arm64.signExtends u.op := by
    rcases normV_cases u with h | ⟨ho, h⟩ | ⟨ho, -, h⟩
    · rw [h]
    · rw [h, ho]; rfl
    · rw [h, ho]; rfl
  have hl : ∀ o : Option ID, ((o.bind fun x => (val? x).map normV).map (·.op == .ARM64LDPSW)) =
      ((o.bind val?).map (·.op == .ARM64LDPSW)) := by
    intro o
    cases o with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      cases val? a with
      | none => rfl
      | some w =>
        simp only [Option.map_some, Option.some.injEq]
        have := normV_op (P := fun o => (o == .ARM64LDPSW) = true) (by decide) (by decide) w
        cases h1 : ((normV w).op == .ARM64LDPSW) <;> cases h2 : (w.op == .ARM64LDPSW) <;> simp_all
  rw [hs]
  congr 1
  rcases normV_cases u with h | ⟨ho, h⟩ | ⟨ho, -, h⟩
  · rw [h]; split <;> simp only [hl]
  · rw [h, ho]
  · rw [h, ho]

/-! ## The context -/

theorem schedNodes_normF (f : Func) (b : Block) : schedNodes (normF f) b = schedNodes f b := by
  unfold schedNodes
  congr 1
  funext id
  rw [value?_normF]
  cases f.value? id with
  | none => rfl
  | some v =>
    simp only [Option.map_some, normV_phi, normV_id, normV_args, normV_prio]

theorem schedule_normF (f : Func) (b : Block) : schedule (normF f) b = schedule f b := by
  unfold schedule
  rw [schedNodes_normF]

theorem lowered_normF (f : Func) : (normF f).lowered = f.lowered := by
  unfold Func.lowered normF
  simp only [Array.any_map]
  congr 1
  congr 1
  funext o
  cases o with
  | none => rfl
  | some v => simp only [Function.comp, Option.map_some, normV_generic]

theorem makeL_normF (tabs : Tables) (f : Func) :
    Ctx.makeL tabs (normF f) = { Ctx.makeL tabs f with f := normF f } := by
  have hty : ∀ sh : Array Ty, (normF f).valueTab.map (valueTy sh) = f.valueTab.map (valueTy sh) := by
    intro sh
    simp only [normF, Array.map_map]
    congr 1
    funext o
    cases o with
    | none => rfl
    | some v => simp only [Function.comp, Option.map_some, valueTy, normV_type]
  have hsc : (normF f).blockTab.map (fun o => o.bind (schedule (normF f))) =
      f.blockTab.map (fun o => o.bind (schedule f)) := by
    show f.blockTab.map _ = _
    congr 1
    funext o
    cases o with
    | none => rfl
    | some b => simp only [Option.bind_some, schedule_normF]
  unfold Ctx.makeL Ctx.make
  rw [lowered_normF]
  simp only [hsc]
  split
  · simp only [hty]; rfl
  · simp only [hty]; rfl

/-! ## Evaluation -/

private theorem nilFaults_none {faulting : Bool} {ctx : Ctx} {v : Value} {argv : List Val}
    (h0 : v.op.faultOnNilArg0 = false) (h1 : v.op.faultOnNilArg1 = false) :
    nilFaults faulting ctx v argv = none := by
  have hn : nilAccesses ctx v argv = [] := by unfold nilAccesses; simp [h0, h1]
  unfold nilFaults
  rw [hn]
  split
  · rfl
  · split <;> simp

theorem evalOpL_normV (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value)
    (argv : List Val) (ty : Ty) :
    evalOpL faulting env ctx fr (normV v) argv ty = evalOpL faulting env ctx fr v argv ty := by
  rcases normV_cases v with h | ⟨ho, h⟩ | ⟨ho, hk, h⟩
  · rw [h]
  · rw [h, evalOpL_eq, evalOpL_eq, ho]
    have e1 : nilFaults faulting ctx { v with op := .ARM64MOVDreg } argv = none :=
      nilFaults_none rfl rfl
    have e2 : nilFaults faulting ctx v argv = none := nilFaults_none (by rw [ho]; rfl) (by rw [ho]; rfl)
    simp only [show Op.generic .ARM64MOVDreg = false by rfl, show Op.generic .ARM64MOVDnop = false by rfl,
      show GoFV.Opt.LowerTerm.actOp .ARM64MOVDreg = true by rfl,
      show GoFV.Opt.LowerTerm.actOp .ARM64MOVDnop = true by rfl, Bool.false_eq_true, ite_false,
      ite_true]
    unfold arm64Op
    simp only [e1, e2]
    rw [ho]
    rfl
  · rw [h, evalOpL_eq, evalOpL_eq, ho]
    simp only [show Op.generic .ARM64MOVDconst = false by rfl, show Op.generic .ARM64ZERO = false by rfl,
      show GoFV.Opt.LowerTerm.actOp .ARM64MOVDconst = false by rfl,
      show GoFV.Opt.LowerTerm.actOp .ARM64ZERO = false by rfl,
      show isRoot .ARM64MOVDconst = false by rfl, show isRoot .ARM64ZERO = false by rfl,
      Bool.false_eq_true, ite_false, hk]
    rfl

theorem evalValueL_normV (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) :
    evalValueL md env ctx fr (normV v) = evalValueL md env ctx fr v := by
  unfold evalValueL
  rw [normV_args, normV_id, evalOpL_normV]

/-- The function of the context is read only through the first argument's sign extension. -/
theorem evalValueL_normCtx (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) :
    evalValueL md env { ctx with f := normF ctx.f } fr v = evalValueL md env ctx fr v := by
  have hop : ∀ o : Option ID, ((o.bind (normF ctx.f).value?).map
      (Arm64.signExtendsIn (normF ctx.f).value?)) =
      ((o.bind ctx.f.value?).map (Arm64.signExtendsIn ctx.f.value?)) := by
    intro o
    cases o with
    | none => rfl
    | some a =>
      simp only [Option.bind_some, value?_normF]
      cases ctx.f.value? a with
      | none => rfl
      | some u =>
        simp only [Option.map_some, Option.some.injEq]
        have he : (normF ctx.f).value? = fun x => (ctx.f.value? x).map normV := funext (value?_normF _)
        rw [he, signExtendsIn_normV]
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act, defers⟩ := ctx
  dsimp only at hop
  simp only [evalValueL, evalOpL_eq, arm64Op, hop]
  rfl

theorem evalAllL_normF (md : LMode) (env : Env) (ctx : Ctx) :
    ∀ (fr : Frame) (ids : List ID),
      evalAllL md env { ctx with f := normF ctx.f } fr ids = evalAllL md env ctx fr ids := by
  intro fr ids
  induction ids generalizing fr with
  | nil => rfl
  | cons id ids ih =>
    unfold evalAllL
    dsimp only
    rw [value?_normF]
    cases ctx.f.value? id with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      rw [evalValueL_normCtx, evalValueL_normV]
      split <;> simp only [ih]

theorem enterBlockL_normF (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (b : Block) (i : Nat) :
    enterBlockL md env { ctx with f := normF ctx.f } fr b i = enterBlockL md env ctx fr b i := by
  unfold enterBlockL
  dsimp only
  congr 1
  · congr 1
    funext id
    rw [value?_normF]
    cases ctx.f.value? id with
    | none => rfl
    | some v => simp only [Option.map_some, normV_phi, normV_args]
  · funext phis
    simp only [evalAllL_normF]

theorem runLoopL_normF (md : LMode) (env : Env) (ctx : Ctx) :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoopL md env { ctx with f := normF ctx.f } fuel fr bid i =
        runLoopL md env ctx fuel fr bid i := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro fr bid i
    rw [runLoopL_succ, runLoopL_succ]
    dsimp only
    rw [block?_normF]
    cases ctx.f.block? bid with
    | none => rfl
    | some b =>
      simp only
      rw [enterBlockL_normF]
      split
      · rfl
      · rfl
      · split <;> simp only [ih]

/-- **Undoing `late lower`'s renames does not change `runL`.** -/
theorem runL_normF (env : Env) (tabs : Tables) (f : Func) (args : List Val) (mem : Mem)
    (fuel : Nat) : runL env tabs (normF f) args mem fuel = runL env tabs f args mem fuel := by
  unfold runL
  rw [lowered_normF, makeL_normF]
  unfold runCtxL
  dsimp only
  split
  · rfl
  · have he : entryFrame env { Ctx.makeL tabs f with f := normF f } args mem =
        entryFrame env (Ctx.makeL tabs f) args mem := by
      unfold entryFrame
      simp only [normF, Array.size_map]
      rfl
    have hf : (Ctx.makeL tabs f).f = f := by unfold Ctx.makeL; split <;> rfl
    have hrl := runLoopL_normF ⟨f.lowered, false⟩ env (Ctx.makeL tabs f)
    rw [hf] at hrl
    rw [he, hrl]
    simp only [normF]

/-! ## The pass -/

/-- **`late lower` refines its input** (`runL`) when `renameB` accepts its result: it only
renamed `MOVDreg` to `MOVDnop` and `MOVDconst [0]` to `ZERO`. -/
theorem lateLower_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (_h : lateLower penv f = .ok out) (hv : renameB penv.tables out.tables f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  unfold renameB at hv
  rw [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨hta, he⟩ := hv
  refine RefinesL.of_runL_eq fun env args mem fuel => ?_
  rw [← runL_normF, runL_congr he, runL_normF, runL_tabsAgreeL hta]

end GoFV.Proof.LateLowerL
