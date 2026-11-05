import GoFV.Proof.RefineSched
import GoFV.Proof.SimL
import GoFV.Proof.Pass.SchedLEval
import GoFV.Proof.EvalOpLDispatch

/-!
# `runLF` against `runL` (`runLF_cases`)

`runLF` is `runL` with memory ops faulting (`LMode.faulting`). The two evaluate an op alike,
except that under `runLF` an access through a nil base in the nil page panics with `nilDeref`
(`nilFaults`) and a lowered nil check of a wild pointer is `stuck` (`wildNil`)
(`evalOpL_faults`). So a `runLF` run is `runL`'s, or it stops earlier: with a `nilDeref` panic
(then `finish` runs the deferred calls) or `stuck` (`runLF_cases`). On the inputs where no run
stops so (`NoNilFault`) the two are equal, which `RefinesSchedLF.schedL` uses.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- `r` (memory ops faulting) is `r'` (not faulting), a `nilDeref` panic, or `stuck`. -/
def FaultsOr {α : Type} (r r' : Res α) : Prop :=
  r = r' ∨ (∃ m, r = .panic .nilDeref m) ∨ ∃ msg, r = .stuck msg

theorem nilFaults_false (ctx : Ctx) (v : Value) (argv : List Val) :
    nilFaults false ctx v argv = none := by
  simp [nilFaults]

theorem arm64Op_faults (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (argv : List Val)
    (ty : Ty) : FaultsOr (arm64Op true env ctx fr v argv ty) (arm64Op false env ctx fr v argv ty) := by
  cases hn : nilFaults true ctx v argv with
  | some m => exact .inr (.inl ⟨m, by unfold arm64Op; rw [hn]⟩)
  | none =>
    by_cases hnc : v.op = .ARM64LoweredNilCheck
    · by_cases hw : wildNil argv = true
      · refine .inr (.inr ?_)
        unfold arm64Op; rw [hn, hnc]; simp [hw]
      · left
        unfold arm64Op; rw [hn, nilFaults_false, hnc]; simp [hw]
    · left
      unfold arm64Op
      rw [hn, nilFaults_false]
      dsimp only
      split
      all_goals first | rfl | exact absurd ‹_› hnc

theorem evalOpL_faults (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) (argv : List Val)
    (ty : Ty) : FaultsOr (evalOpL true env ctx fr v argv ty) (evalOpL false env ctx fr v argv ty) := by
  rw [evalOpL_eq, evalOpL_eq]
  split
  · exact .inl rfl
  · split
    · exact arm64Op_faults env ctx fr v argv ty
    · exact .inl rfl

theorem evalValueL_faults (low : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) :
    FaultsOr (evalValueL ⟨low, true⟩ env ctx fr v) (evalValueL ⟨low, false⟩ env ctx fr v) := by
  cases hm : SchedL.argsM fr v with
  | ok argv =>
    rw [SchedL.evalValueL_bind hm, SchedL.evalValueL_bind hm]
    dsimp only
    rcases evalOpL_faults env ctx fr v argv (ctx.tys[v.id]?.getD .other) with h | ⟨m, h⟩ | ⟨msg, h⟩
    · left; rw [h]; rfl
    · right; left; exact ⟨m, by rw [h]; rfl⟩
    · right; right; exact ⟨msg, by rw [h]; rfl⟩
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg =>
    left
    unfold evalValueL
    simp only [SchedL.argsM] at hm
    rw [hm]
    rfl

theorem evalAllL_faults (low : Bool) (env : Env) (ctx : Ctx) :
    ∀ (ids : List ID) (fr : Frame),
      FaultsOr (evalAllL ⟨low, true⟩ env ctx fr ids) (evalAllL ⟨low, false⟩ env ctx fr ids)
  | [], _ => .inl rfl
  | id :: ids, fr => by
    rw [evalAllL_cons, evalAllL_cons]
    unfold stepVL
    cases ctx.f.value? id with
    | none => exact .inl rfl
    | some v =>
      dsimp only
      rcases evalValueL_faults low env ctx fr v with h | ⟨m, h⟩ | ⟨msg, h⟩
      · rw [h]
        cases evalValueL ⟨low, false⟩ env ctx fr v with
        | ok x => exact evalAllL_faults low env ctx ids _
        | panic e m => exact .inl rfl
        | stuck msg => exact .inl rfl
      · rw [h]; exact .inr (.inl ⟨m, rfl⟩)
      · rw [h]; exact .inr (.inr ⟨msg, rfl⟩)

theorem enterBlockL_faults (low : Bool) (env : Env) (ctx : Ctx) (fr : Frame) (b : Block)
    (i : Nat) :
    FaultsOr (enterBlockL ⟨low, true⟩ env ctx fr b i) (enterBlockL ⟨low, false⟩ env ctx fr b i) := by
  rw [enterBlockL_eq, enterBlockL_eq]
  have hp : phiStepL ⟨low, true⟩ ctx fr i = phiStepL ⟨low, false⟩ ctx fr i := rfl
  rw [hp]
  cases b.values.toList.filterMapM (phiStepL ⟨low, false⟩ ctx fr i) with
  | ok ps =>
    cases (ctx.sched[b.id]?).join with
    | some o => exact evalAllL_faults low env ctx o.toList _
    | none => exact .inl rfl
  | panic e m => exact .inl rfl
  | stuck msg => exact .inl rfl

/-- **A faulting run is the run, or stops earlier** (`nilDeref` or `stuck`). -/
theorem runLoopL_faults (low : Bool) (env : Env) (ctx : Ctx) :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoopL ⟨low, true⟩ env ctx fuel fr bid i = runLoopL ⟨low, false⟩ env ctx fuel fr bid i ∨
        (∃ m, runLoopL ⟨low, true⟩ env ctx fuel fr bid i = .panicked .nilDeref m) ∨
        ¬ (runLoopL ⟨low, true⟩ env ctx fuel fr bid i).Defined
  | 0, _, _, _ => .inl rfl
  | fuel + 1, fr, bid, i => by
    rw [runLoopL_succ, runLoopL_succ]
    cases ctx.f.block? bid with
    | none => exact .inl rfl
    | some b =>
      dsimp only
      rcases enterBlockL_faults low env ctx fr b i with h | ⟨m, h⟩ | ⟨msg, h⟩
      · rw [h]
        cases enterBlockL ⟨low, false⟩ env ctx fr b i with
        | ok fr' =>
          dsimp only
          cases stepTermL fr' b with
          | ok n =>
            cases n with
            | goto e => exact runLoopL_faults low env ctx fuel fr' e.b e.i
            | ret rs m => exact .inl rfl
          | panic e m => exact .inl rfl
          | stuck msg => exact .inl rfl
        | panic e m => exact .inl rfl
        | stuck msg => exact .inl rfl
      · rw [h]; exact .inr (.inl ⟨m, rfl⟩)
      · rw [h]; exact .inr (.inr id)

/-- **`runLF` is `runL`, or stops earlier**: it is not defined (`stuck`: a nil check of a wild
pointer), or it panics with `nilDeref` (an access through a nil base in the nil page) and runs
the deferred calls (`finish`). -/
theorem runLF_cases (env : Env) (tabs : Tables) (f : Func) (args : List Val) (mem : Mem)
    (fuel : Nat) :
    runLF env tabs f args mem fuel = runL env tabs f args mem fuel ∨
      ¬ (runLF env tabs f args mem fuel).Defined ∨
      ∃ m, runLF env tabs f args mem fuel =
        finish env (Ctx.makeL tabs f).outs (Ctx.makeL tabs f).defers (Ctx.makeL tabs f).act
          (.panicked .nilDeref m) := by
  unfold runLF runL runCtxL
  split
  · exact .inl rfl
  · rcases runLoopL_faults f.lowered env (Ctx.makeL tabs f) fuel
        (entryFrame env (Ctx.makeL tabs f) args mem) (Ctx.makeL tabs f).f.entry 0 with
      h | ⟨m, h⟩ | h
    · rw [h]; exact .inl rfl
    · rw [h]; exact .inr (.inr ⟨m, rfl⟩)
    · exact .inr (.inl fun hd => h (finish_defined hd))

/-! ## Functions without faulting ops -/

section
variable (low : Bool) (env : Env) (ctx : Ctx)
  (H : ∀ id v, ctx.f.value? id = some v → ∀ fr,
    evalValueL ⟨low, true⟩ env ctx fr v = evalValueL ⟨low, false⟩ env ctx fr v)
include H

theorem evalAllL_eq_of : ∀ (ids : List ID) (fr : Frame),
    evalAllL ⟨low, true⟩ env ctx fr ids = evalAllL ⟨low, false⟩ env ctx fr ids
  | [], _ => rfl
  | id :: ids, fr => by
    rw [evalAllL_cons, evalAllL_cons]
    unfold stepVL
    cases hv : ctx.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [H id v hv fr]
      cases evalValueL ⟨low, false⟩ env ctx fr v with
      | ok x => exact evalAllL_eq_of ids _
      | panic e m => rfl
      | stuck msg => rfl

theorem runLoopL_eq_of : ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
    runLoopL ⟨low, true⟩ env ctx fuel fr bid i = runLoopL ⟨low, false⟩ env ctx fuel fr bid i
  | 0, _, _, _ => rfl
  | fuel + 1, fr, bid, i => by
    rw [runLoopL_succ, runLoopL_succ]
    cases ctx.f.block? bid with
    | none => rfl
    | some b =>
      dsimp only
      have he : enterBlockL ⟨low, true⟩ env ctx fr b i =
          enterBlockL ⟨low, false⟩ env ctx fr b i := by
        rw [enterBlockL_eq, enterBlockL_eq]
        have hp : phiStepL ⟨low, true⟩ ctx fr i = phiStepL ⟨low, false⟩ ctx fr i := rfl
        rw [hp]
        cases b.values.toList.filterMapM (phiStepL ⟨low, false⟩ ctx fr i) with
        | ok ps =>
          cases (ctx.sched[b.id]?).join with
          | some o => exact evalAllL_eq_of low env ctx H o.toList _
          | none => rfl
        | panic e m => rfl
        | stuck msg => rfl
      rw [he]
      cases enterBlockL ⟨low, false⟩ env ctx fr b i with
      | ok fr' =>
        dsimp only
        cases stepTermL fr' b with
        | ok n =>
          cases n with
          | goto e => exact runLoopL_eq_of fuel fr' e.b e.i
          | ret rs m => rfl
        | panic e m => rfl
        | stuck msg => rfl
      | panic e m => rfl
      | stuck msg => rfl

end

/-- A function none of whose values is evaluated by `arm64Op` (no memory op, no nil check) has
no nil-page access: `runLF` is `runL` on every input. -/
theorem noNilFault_of_noAct {tabs : Tables} {f : Func}
    (hb : f.valueTab.all (fun o => o.all fun v => !GoFV.Opt.ScheduleCheck.actOp v.op) = true)
    (env : Env) (args : List Val) (mem : Mem) : NoNilFault tabs f env args mem := by
  have h : ∀ id v, f.value? id = some v → v.op ∉ GoFV.Opt.ScheduleCheck.actOps := by
    intro id v hv hm
    unfold Func.value? at hv
    cases hx : f.valueTab[id]? with
    | none => rw [hx] at hv; cases hv
    | some o =>
      rw [hx] at hv
      simp only [Option.join_some] at hv
      subst hv
      obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.1 hx
      have := Array.all_eq_true.1 hb id hlt
      rw [hget] at this
      simp [GoFV.Opt.ScheduleCheck.actOp, hm] at this
  intro fuel
  unfold runLF runL runCtxL
  rw [runLoopL_eq_of f.lowered env (Ctx.makeL tabs f) (fun id v hv fr => ?_)]
  rw [makeL_f] at hv
  have hop : ∀ argv ty, evalOpL true env (Ctx.makeL tabs f) fr v argv ty =
      evalOpL false env (Ctx.makeL tabs f) fr v argv ty := by
    intro argv ty
    cases hg : v.op.generic
    · rw [SchedL.evalOpL_nonact hg (h id v hv), SchedL.evalOpL_nonact hg (h id v hv)]
    · rw [evalOpL_generic _ _ _ _ _ _ hg, evalOpL_generic _ _ _ _ _ _ hg]
  unfold evalValueL
  simp only [hop]
  rfl

end GoFV.Proof
