import GoFV.Proof.TabsAgree
import GoFV.Proof.RefineL
import GoFV.Proof.Low.DenL

/-!
# Running a lowered function in extended tables (`runL_tabsAgreeL`, issue #385)

Phase 1's `run_tabsAgree` for `runL`: when `tabsAgreeL tabs tabs' f` holds (Phase 1's
`tabsAgree`, and the lowered shapes of `f`'s values, `Sem.tyOfL`, agree in both tables), `f` has
the same `runL` outcomes in `tabs'` as in `tabs`. Each layer of `runL` is equal in the two
contexts: the arm64 ops read the tables only through the aux of the value (`Sem.symAddr`,
`callABI?`, `fitPieces`, the panic-bound auxes, `callOp`, `memRoot`, `frameVal`), which
`AuxAgree` covers.
-/


namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.TabsAgree

section
variable {ctx : Ctx} {tabs' : Tables} {v : Value}

theorem symAddr_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (a : Val) :
    symAddr { ctx with tabs := tabs' } v a = symAddr ctx v a := by
  unfold symAddr
  cases hv : v.aux with
  | none => rfl
  | some n =>
    rw [hv] at h
    have hl : tabs'.aux? n = ctx.tabs.aux? n := h.lookup
    dsimp only
    rw [hl]
    split
    · rfl
    · rw [h.frameBlk]
    · rfl

theorem nilFaults_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (faulting : Bool) (argv : List Val) :
    nilFaults faulting { ctx with tabs := tabs' } v argv = nilFaults faulting ctx v argv := by
  unfold nilFaults nilAccesses
  simp only [symAddr_tabs h]

theorem fitPieces_tabs (ps : List ABIParam) (hP : ∀ p ∈ ps, tabs'.ty p.type = ctx.tabs.ty p.type) :
    ∀ pieces, fitPieces tabs' ps pieces = fitPieces ctx.tabs ps pieces := by
  induction ps with
  | nil => intro pieces; rfl
  | cons p ps ih =>
    intro pieces
    have ih' := ih (fun q hq => hP q (List.mem_cons_of_mem _ hq))
    simp only [fitPieces, hP p List.mem_cons_self, ih']

theorem arm64Op_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (faulting : Bool) (env : Env)
    (fr : Frame) (argv : List Val) (ty : Ty) :
    arm64Op faulting env { ctx with tabs := tabs' } fr v argv ty =
      arm64Op faulting env ctx fr v argv ty := by
  have hP : ∀ p ∈ ((callABI? ctx.tabs v.aux).map (·.params.toList.filter (!·.out))).getD [],
      tabs'.ty p.type = ctx.tabs.ty p.type := by
    cases hc : callABI? ctx.tabs v.aux with
    | none => intro p hp; simp at hp
    | some abi =>
      intro p hp
      simp only [Option.map_some, Option.getD_some, List.mem_filter] at hp
      exact h.abiTy abi hc p hp.1
  have hfit : ∀ pieces, fitPieces tabs'
      (((callABI? ctx.tabs v.aux).map (·.params.toList.filter (!·.out))).getD []) pieces =
      fitPieces ctx.tabs (((callABI? ctx.tabs v.aux).map (·.params.toList.filter (!·.out))).getD [])
        pieces := fitPieces_tabs _ hP
  have hgen : ∀ op : Op, AuxAgree ctx.tabs tabs' ({ v with op } : Value).aux := fun _ => h
  have hlk : ∀ n : Option AuxRef, n = v.aux → n.bind tabs'.aux? = n.bind ctx.tabs.aux? := by
    intro n hn; rw [hn]; exact h.lookup
  unfold arm64Op
  simp only [nilFaults_tabs h, symAddr_tabs h, h.callABI, hfit, callOp_tabs (hgen _),
    memRoot_tabs (hgen _), frameVal_tabs (hgen _), hlk v.aux rfl]

theorem evalOpL_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (faulting : Bool) (env : Env)
    (fr : Frame) (argv : List Val) (ty : Ty) :
    evalOpL faulting env { ctx with tabs := tabs' } fr v argv ty =
      evalOpL faulting env ctx fr v argv ty := by
  unfold evalOpL
  simp only [evalOp_tabs h, arm64Op_tabs h]

theorem evalValueL_tabs (h : AuxAgree ctx.tabs tabs' v.aux) (md : LMode) (env : Env) (fr : Frame) :
    evalValueL md env { ctx with tabs := tabs' } fr v = evalValueL md env ctx fr v := by
  have he : evalOpL md.faulting env { ctx with tabs := tabs' } fr v =
      evalOpL md.faulting env ctx fr v :=
    funext fun argv => funext fun ty => evalOpL_tabs h md.faulting env fr argv ty
  unfold evalValueL
  rw [he]

end

section
variable {ctx : Ctx} {tabs' : Tables}
  (H : ∀ id v, ctx.f.value? id = some v → AuxAgree ctx.tabs tabs' v.aux) (md : LMode) (env : Env)
include H

theorem evalAllL_tabs :
    ∀ (ids : List ID) (fr : Frame),
      evalAllL md env { ctx with tabs := tabs' } fr ids = evalAllL md env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    rw [evalAllL, evalAllL]
    cases hv : ctx.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [evalValueL_tabs (H id v hv)]
      cases evalValueL md env ctx fr v with
      | ok x => exact evalAllL_tabs ids _
      | panic e m => rfl
      | stuck msg => rfl

theorem enterBlockL_tabs (fr : Frame) (b : Block) (i : Nat) :
    enterBlockL md env { ctx with tabs := tabs' } fr b i = enterBlockL md env ctx fr b i := by
  have he : evalAllL md env { ctx with tabs := tabs' } = evalAllL md env ctx :=
    funext fun fr => funext fun ids => evalAllL_tabs H md env ids fr
  unfold enterBlockL
  rw [he]

theorem runLoopL_tabs :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoopL md env { ctx with tabs := tabs' } fuel fr bid i = runLoopL md env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    have he : enterBlockL md env { ctx with tabs := tabs' } = enterBlockL md env ctx :=
      funext fun fr => funext fun b => funext fun i => enterBlockL_tabs H md env fr b i
    have ih : runLoopL md env { ctx with tabs := tabs' } fuel = runLoopL md env ctx fuel :=
      funext fun fr => funext fun bid => funext fun i => runLoopL_tabs fuel fr bid i
    rw [GoFV.Proof.runLoopL_succ, GoFV.Proof.runLoopL_succ, he, ih]

theorem runCtxL_tabs (hout : outargsSize tabs' = outargsSize ctx.tabs)
    (hforg : ∀ l ∈ ctx.locals.toList, tabs'.forgeable l.1 = ctx.tabs.forgeable l.1)
    (args : List Val) (mem : Mem) (fuel : Nat) :
    runCtxL md env { ctx with tabs := tabs' } args mem fuel = runCtxL md env ctx args mem fuel := by
  have hl : runLoopL md env { ctx with tabs := tabs' } fuel = runLoopL md env ctx fuel :=
    funext fun fr => funext fun bid => funext fun i => runLoopL_tabs H md env fuel fr bid i
  have hm := frameMem_tabs env hout hforg
  have he : entryFrame env { ctx with tabs := tabs' } = entryFrame env ctx := by
    funext args mem
    unfold entryFrame
    rw [hm]
  unfold runCtxL
  rw [hl, he]

end

/-- **Running a lowered function in extended tables.** When `tabsAgreeL tabs tabs' f` holds, `f`
has the same `runL` outcomes in `tabs'` as in `tabs`. -/
theorem runL_tabsAgreeL {tabs tabs' : Tables} {f : Func}
    (h : GoFV.Opt.LowerCheck.tabsAgreeL tabs tabs' f = true) (env : Env) (args : List Val)
    (mem : Mem) (fuel : Nat) : runL env tabs' f args mem fuel = runL env tabs f args mem fuel := by
  unfold GoFV.Opt.LowerCheck.tabsAgreeL at h
  rw [Bool.and_eq_true] at h
  obtain ⟨ha, hs⟩ := h
  have A := tabsAgree_sound ha
  have hmap : f.valueTab.map (valueTy (typeShapesL tabs')) = f.valueTab.map (valueTy (typeShapesL tabs)) :=
    Array.map_congr_left fun o ho => Ty.eq_of_beq (List.all_eq_true.mp hs o (Array.mem_def.mp ho))
  have hctx : Ctx.makeL tabs' f = { Ctx.makeL tabs f with tabs := tabs' } := by
    unfold Ctx.makeL
    by_cases hl : f.lowered = true
    · simp only [hl, ite_true, A.ctx, hmap]
    · simp only [hl, Bool.false_eq_true, ite_false, A.ctx]
  have hc : (Ctx.makeL tabs f).tabs = tabs := by unfold Ctx.makeL; split <;> rfl
  have hval : ∀ id v, (Ctx.makeL tabs f).f.value? id = some v →
      AuxAgree (Ctx.makeL tabs f).tabs tabs' v.aux := by
    have hf : (Ctx.makeL tabs f).f = f := by unfold Ctx.makeL; split <;> rfl
    intro id v hv; rw [hf] at hv; rw [hc]; exact A.value id v hv
  have hloc : (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
    unfold Ctx.makeL; split <;> rfl
  show runCtxL _ env (Ctx.makeL tabs' f) args mem fuel = runCtxL _ env (Ctx.makeL tabs f) args mem fuel
  rw [hctx]
  exact runCtxL_tabs hval _ env (by rw [hc]; exact A.outargs)
    (by rw [hloc, hc]; exact A.forgeable) args mem fuel

end GoFV.Proof.Low
