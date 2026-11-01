import GoFV.Opt.TabsAgree
import GoFV.Proof.Refine

/-!
# Running a function in extended tables (`run_tabsAgree`)

Passes that extend the definition tables (`expand calls`, `decompose builtin`: new types, auxes
and slots at fresh numbers) state their refinement as `Refines out.tables out.func tabs f`: the
source runs in the input tables `tabs`. When `GoFV.Opt.tabsAgree tabs tabs' f` holds, running `f`
in `tabs'` gives the same outcome (`run_tabsAgree`), so such a refinement can be restated
against any extension (`refines_of_tabsAgree` and its `RefinesUnder`/`RefinesFrom` forms).

Proof: `Ctx.make tabs' f` is `Ctx.make tabs f` with the tables replaced (`Agree.ctx`), and every
lookup through the tables that `evalOp` (`callOp`, `memRoot`, `frameVal`, `ArgIntReg`) and
`runCtx` (`frameAllocs`) make for `f` gives the same result (`AuxAgree`), so each layer of the
semantics is equal in the two contexts (`evalOp_tabs` … `runCtx_tabs`). No case split on `Op`:
the occurrences of the context are rewritten inside `evalOp`'s and `memRoot`'s `match`.
-/

namespace GoFV.Proof.TabsAgree

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- The lookups the semantics makes through the aux `aux` of a value agree in `tabs` and
`tabs'`. -/
structure AuxAgree (tabs tabs' : Tables) (aux : Option AuxRef) : Prop where
  lookup : aux.bind tabs'.aux? = aux.bind tabs.aux?
  callee : aux.bind tabs'.callee? = aux.bind tabs.callee?
  shape : auxTy tabs' aux = auxTy tabs aux
  abiTy : ∀ abi, callABI? tabs aux = some abi →
    ∀ p ∈ abi.params.toList, tabs'.ty p.type = tabs.ty p.type

theorem AuxAgree.none (tabs tabs' : Tables) : AuxAgree tabs tabs' none :=
  ⟨rfl, rfl, rfl, fun _ h => by simp [callABI?] at h⟩

theorem AuxAgree.callABI {tabs tabs' : Tables} {aux : Option AuxRef} (h : AuxAgree tabs tabs' aux) :
    callABI? tabs' aux = callABI? tabs aux := by
  unfold callABI?; rw [h.lookup]

theorem AuxAgree.frameBlk {tabs tabs' : Tables} {n : AuxRef} (h : AuxAgree tabs tabs' (some n))
    (act : Nat) : Sem.frameBlk tabs' act n = Sem.frameBlk tabs act n := by
  have ha : tabs'.aux? n = tabs.aux? n := h.lookup
  unfold Sem.frameBlk Tables.forgeable; rw [ha]

theorem auxAgree_sound {tabs tabs' : Tables} {a : AuxRef} (h : auxAgree tabs tabs' a = true) :
    AuxAgree tabs tabs' (some a) := by
  unfold auxAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨ha, hc⟩, ht⟩, habi⟩ := h
  refine ⟨ha, hc, Ty.eq_of_beq ht, fun abi hab p hp => ?_⟩
  rw [hab] at habi
  exact Ty.eq_of_beq (List.all_eq_true.mp habi p hp)

theorem valueAuxAgree_sound {tabs tabs' : Tables} {v : Value}
    (h : valueAuxAgree tabs tabs' (some v) = true) : AuxAgree tabs tabs' v.aux := by
  rcases v with ⟨_, _, _, _, _ | a, _, _, _, _⟩
  · exact AuxAgree.none tabs tabs'
  · exact auxAgree_sound h

/-! ## The ABI lookups -/

theorem decodeArgs_tabs {tabs tabs' : Tables} (act : Nat) (m : Mem) :
    ∀ (ps : List ABIParam), (∀ p ∈ ps, tabs'.ty p.type = tabs.ty p.type) →
      ∀ pieces, decodeArgs tabs' act m ps pieces = decodeArgs tabs act m ps pieces
  | [], _, pieces => by cases pieces <;> rfl
  | p :: ps, h, pieces => by
    have ih := decodeArgs_tabs act m ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [decodeArgs, h p List.mem_cons_self, ih]

theorem encodeResults_tabs {tabs tabs' : Tables} (act : Nat) :
    ∀ (ps : List ABIParam), (∀ p ∈ ps, tabs'.ty p.type = tabs.ty p.type) →
      ∀ rs m, encodeResults tabs' act ps rs m = encodeResults tabs act ps rs m
  | [], _, [], _ => rfl
  | [], _, _ :: _, _ => rfl
  | _ :: _, _, [], _ => rfl
  | p :: ps, h, r :: rs, m => by
    have ih := encodeResults_tabs act ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [encodeResults, h p List.mem_cons_self, ih]

theorem retypeResults_tabs {tabs tabs' : Tables} :
    ∀ (ps : List ABIParam), (∀ p ∈ ps, tabs'.ty p.type = tabs.ty p.type) →
      ∀ rs, retypeResults tabs' ps rs = retypeResults tabs ps rs
  | [], _, _ => rfl
  | _ :: _, _, [] => rfl
  | p :: ps, h, r :: rs => by
    simp only [retypeResults, h p List.mem_cons_self,
      retypeResults_tabs ps (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-! ## One value -/

section
variable {ctx : Ctx} {tabs' : Tables} {v : Value}

theorem callTarget_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (argv : List Val) :
    callTarget { ctx with tabs := tabs' } v argv = callTarget ctx v argv := by
  unfold callTarget
  rw [h.callee]

theorem callOp_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (env : Env) (argv : List Val) :
    callOp env { ctx with tabs := tabs' } v argv = callOp env ctx v argv := by
  unfold callOp
  rw [callTarget_tabs h, h.callABI]
  have hP : ∀ p ∈ ((callABI? ctx.tabs v.aux).map (·.params.toList)).getD [],
      tabs'.ty p.type = ctx.tabs.ty p.type := by
    cases hc : callABI? ctx.tabs v.aux with
    | none => intro p hp; simp at hp
    | some abi => exact h.abiTy abi hc
  generalize ((callABI? ctx.tabs v.aux).map (·.params.toList)).getD [] = P at hP ⊢
  have hin : ∀ act m pieces, decodeArgs tabs' act m (P.filter (!·.out)) pieces =
      decodeArgs ctx.tabs act m (P.filter (!·.out)) pieces := fun act m =>
    decodeArgs_tabs act m _ fun p hp => hP p (List.mem_filter.mp hp).1
  have hout : ∀ act rs m, encodeResults tabs' act (P.filter (·.out)) rs m =
      encodeResults ctx.tabs act (P.filter (·.out)) rs m := fun act =>
    encodeResults_tabs act _ fun p hp => hP p (List.mem_filter.mp hp).1
  have hret := retypeResults_tabs (tabs := ctx.tabs) (tabs' := tabs') (P.filter (·.out))
    (fun p hp => hP p (List.mem_filter.mp hp).1)
  simp only [hin, hout, hret]

theorem memRoot_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (argv : List Val) :
    memRoot { ctx with tabs := tabs' } v argv = memRoot ctx v argv := by
  unfold memRoot
  rw [h.shape]
  cases hv : v.aux with
  | none => rfl
  | some n =>
    rw [hv] at h
    dsimp only
    rw [h.frameBlk]

theorem frameVal_tabs (h : AuxAgree ctx.tabs tabs' v.aux) :
    frameVal { ctx with tabs := tabs' } v = frameVal ctx v := by
  have hl : v.aux.map (fun n => Val.ptr ⟨Sem.frameBlk tabs' ctx.act n, 0⟩) =
      v.aux.map (fun n => Val.ptr ⟨Sem.frameBlk ctx.tabs ctx.act n, 0⟩) := by
    cases hv : v.aux with
    | none => rfl
    | some n => rw [hv] at h; simp only [Option.map_some, h.frameBlk]
  unfold frameVal
  rw [h.lookup, hl]

theorem argFloat_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (fr : Frame) (ty : Ty) :
    argFloat { ctx with tabs := tabs' } fr v ty = argFloat ctx fr v ty := by
  unfold argFloat
  rw [h.lookup]
  rfl

theorem evalOp_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (env : Env) (fr : Frame)
    (argv : List Val) (ty : Ty) :
    evalOp env { ctx with tabs := tabs' } fr v argv ty = evalOp env ctx fr v argv ty := by
  have ha : argVal { ctx with tabs := tabs' } fr = argVal ctx fr := rfl
  unfold evalOp
  rw [callOp_tabs h, memRoot_tabs h, frameVal_tabs h, argFloat_tabs h, ha, h.lookup]

/-- `argFloat_tabs` applies (an aux-less value agrees in any tables). -/
example (ctx : Ctx) (tabs' : Tables) (fr : Frame) (ty : Ty) :
    argFloat { ctx with tabs := tabs' } fr { (default : Value) with aux := none } ty =
      argFloat ctx fr { (default : Value) with aux := none } ty :=
  argFloat_tabs (AuxAgree.none _ _) fr ty

theorem evalValue_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (env : Env) (fr : Frame) :
    evalValue env { ctx with tabs := tabs' } fr v = evalValue env ctx fr v := by
  have he : evalOp env { ctx with tabs := tabs' } fr v = evalOp env ctx fr v :=
    funext fun argv => funext fun ty => evalOp_tabs h env fr argv ty
  unfold evalValue
  rw [he]

end

/-! ## Blocks, the loop, the activation -/

section
variable {ctx : Ctx} {tabs' : Tables}
  (H : ∀ id v, ctx.f.value? id = some v → AuxAgree ctx.tabs tabs' v.aux) (env : Env)
include H

theorem evalAll_tabs :
    ∀ (ids : List ID) (fr : Frame),
      evalAll env { ctx with tabs := tabs' } fr ids = evalAll env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    rw [evalAll, evalAll]
    cases hv : ctx.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [evalValue_tabs (H id v hv)]
      cases evalValue env ctx fr v with
      | ok x => exact evalAll_tabs ids _
      | panic e m => rfl
      | stuck msg => rfl

theorem enterBlock_tabs (fr : Frame) (b : Block) (i : Nat) :
    enterBlock env { ctx with tabs := tabs' } fr b i = enterBlock env ctx fr b i := by
  have he : evalAll env { ctx with tabs := tabs' } = evalAll env ctx :=
    funext fun fr => funext fun ids => evalAll_tabs H env ids fr
  unfold enterBlock
  rw [he]

theorem runLoop_tabs :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoop env { ctx with tabs := tabs' } fuel fr bid i = runLoop env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    have he : enterBlock env { ctx with tabs := tabs' } = enterBlock env ctx :=
      funext fun fr => funext fun b => funext fun i => enterBlock_tabs H env fr b i
    have ih : runLoop env { ctx with tabs := tabs' } fuel = runLoop env ctx fuel :=
      funext fun fr => funext fun bid => funext fun i => runLoop_tabs fuel fr bid i
    rw [runLoop_succ, runLoop_succ, he, ih]

omit H in
theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ b, ∀ a ∈ l, f b a = g b a) →
      l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: l, init, h => by
    rw [List.foldl_cons, List.foldl_cons, h init a List.mem_cons_self]
    exact foldl_congr_mem l _ fun b x hx => h b x (List.mem_cons_of_mem _ hx)

omit H in
theorem frameMem_tabs (hout : outargsSize tabs' = outargsSize ctx.tabs)
    (hforg : ∀ l ∈ ctx.locals.toList, tabs'.forgeable l.1 = ctx.tabs.forgeable l.1) :
    frameMem env { ctx with tabs := tabs' } = frameMem env ctx := by
  funext images mem
  unfold frameMem frameAllocs
  dsimp only
  rw [hout, ← Array.foldl_toList, ← Array.foldl_toList]
  refine foldl_congr_mem _ _ fun m l hl => ?_
  obtain ⟨n, sz, pi⟩ := l
  have hf : Sem.frameBlk tabs' ctx.act n = Sem.frameBlk ctx.tabs ctx.act n := by
    unfold Sem.frameBlk; rw [hforg _ hl]
  dsimp only
  rw [hf]

theorem runCtx_tabs (hout : outargsSize tabs' = outargsSize ctx.tabs)
    (hforg : ∀ l ∈ ctx.locals.toList, tabs'.forgeable l.1 = ctx.tabs.forgeable l.1)
    (args : List Val) (mem : Mem) (fuel : Nat) :
    runCtx env { ctx with tabs := tabs' } args mem fuel = runCtx env ctx args mem fuel := by
  have hl : runLoop env { ctx with tabs := tabs' } fuel = runLoop env ctx fuel :=
    funext fun fr => funext fun bid => funext fun i => runLoop_tabs H env fuel fr bid i
  have hm := frameMem_tabs env hout hforg
  have he : entryFrame env { ctx with tabs := tabs' } = entryFrame env ctx := by
    funext args mem
    unfold entryFrame
    rw [hm]
  unfold runCtx
  rw [hl, he]

end

/-! ## The check -/

/-- What `tabsAgree` gives: the same context up to the tables, and agreeing lookups. -/
structure Agree (tabs tabs' : Tables) (f : Func) : Prop where
  ctx : Ctx.make tabs' f = { Ctx.make tabs f with tabs := tabs' }
  outargs : outargsSize tabs' = outargsSize tabs
  forgeable : ∀ l ∈ (Ctx.make tabs f).locals.toList, tabs'.forgeable l.1 = tabs.forgeable l.1
  value : ∀ id v, f.value? id = some v → AuxAgree tabs tabs' v.aux

theorem tabsAgree_sound {tabs tabs' : Tables} {f : Func} (h : tabsAgree tabs tabs' f = true) :
    Agree tabs tabs' f := by
  unfold tabsAgree at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hps, hpty⟩, hls⟩, hforg⟩, hout⟩, hvals⟩ := h
  have hps' : abiParams tabs' f = abiParams tabs f := Array.toList_inj.mp hps
  have hty : ∀ p ∈ abiParams tabs f, tabs'.ty p.type = tabs.ty p.type :=
    fun p hp => Ty.eq_of_beq (hpty p (Array.mem_def.mp hp))
  refine ⟨?_, hout, hforg, fun id v hv => ?_⟩
  · unfold Ctx.make
    simp only [hps']
    congr 1
    · exact Array.map_congr_left fun o ho => Ty.eq_of_beq (hvals o (Array.mem_def.mp ho)).1
    · exact Array.map_congr_left fun p hp => hty p (Array.mem_filter.mp hp).1
    · exact Array.map_congr_left fun p hp => by rw [hty p (Array.mem_filter.mp hp).1]
    · exact Array.toList_inj.mp hls
  · have hm : some v ∈ f.valueTab.toList := by
      have h1 : f.valueTab[id]? = some (some v) := Option.join_eq_some_iff.mp hv
      exact Array.mem_def.mp (Array.mem_of_getElem? h1)
    exact valueAuxAgree_sound (hvals (some v) hm).2

end GoFV.Proof.TabsAgree

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt TabsAgree

/-- **Running a function in extended tables.** When `tabsAgree tabs tabs' f` holds, `f` has the
same outcomes in `tabs'` as in `tabs`. -/
theorem run_tabsAgree {tabs tabs' : Tables} {f : Func} (h : GoFV.Opt.tabsAgree tabs tabs' f = true)
    (env : Sem.Env) (args : List Sem.Val) (mem : Sem.Mem) (fuel : Nat) :
    run env tabs' f args mem fuel = run env tabs f args mem fuel := by
  have A := tabsAgree_sound h
  show runCtx env (Ctx.make tabs' f) args mem fuel = runCtx env (Ctx.make tabs f) args mem fuel
  rw [A.ctx]
  exact runCtx_tabs (ctx := Ctx.make tabs f) A.value env A.outargs A.forgeable args mem fuel

/-- A refinement of `f` in `tabs'` is one in `tabs` (`tabsAgree tabs tabs' f`). -/
theorem refines_of_tabsAgree {tabs tabs' tabs'' : Tables} {f g : Func}
    (h : GoFV.Opt.tabsAgree tabs tabs' f = true) (hr : Refines tabs'' g tabs' f) :
    Refines tabs'' g tabs f := by
  intro env args mem fuel hd
  rw [← run_tabsAgree h] at hd ⊢
  exact hr env args mem fuel hd

theorem refinesUnder_of_tabsAgree {P : Env → Prop} {tabs tabs' tabs'' : Tables} {f g : Func}
    (h : GoFV.Opt.tabsAgree tabs tabs' f = true) (hr : RefinesUnder P tabs'' g tabs' f) :
    RefinesUnder P tabs'' g tabs f := by
  intro env hP args mem fuel hd
  rw [← run_tabsAgree h] at hd ⊢
  exact hr env hP args mem fuel hd

theorem refinesFrom_of_tabsAgree {P : Env → List Val → Mem → Prop} {tabs tabs' tabs'' : Tables}
    {f g : Func} (h : GoFV.Opt.tabsAgree tabs tabs' f = true)
    (hr : RefinesFrom P tabs'' g tabs' f) : RefinesFrom P tabs'' g tabs f := by
  intro env args mem hP fuel hd
  rw [← run_tabsAgree h] at hd ⊢
  exact hr env args mem hP fuel hd

end GoFV.Proof
