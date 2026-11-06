import GoFV.Opt.Verified
import GoFV.Opt.LowerChecked
import GoFV.Opt.Lower
import GoFV.Opt.CheckLower
import GoFV.Opt.Pair
import GoFV.Opt.LoweredCSE
import GoFV.Opt.LoweredCSECheck
import GoFV.Opt.ElimUnreadAutos
import GoFV.Opt.TupleSelectors
import GoFV.Opt.Licm
import GoFV.Opt.Tighten
import GoFV.Opt.Critical
import GoFV.Opt.LikelyAdjust
import GoFV.Opt.Layout
import GoFV.Opt.Schedule
import GoFV.Opt.ScheduleCheck
import GoFV.Opt.NilCheckLate
import GoFV.Opt.NilLateCheck
import GoFV.Opt.FlagAlloc
import GoFV.Opt.Regalloc
import GoFV.Opt.RegallocCheck
import GoFV.Opt.LoopRotate
import GoFV.Opt.Trim
import GoFV.Proof.Pass.DeadcodePassL
import GoFV.Proof.Pass.UnreadLRel
import GoFV.Proof.Pass.MoveLCheck
import GoFV.Proof.Pass.CriticalL
import GoFV.Proof.Pass.LicmL
import GoFV.Proof.Pass.TrimLocCheck

/-!
# The verified pipeline through `trim` (issues #385, #189)

`verifiedPipelineFull` runs `verifiedPipeline` (`number lines` … `rewrite tern`), then the
passes from `lower` to `trim` (`loweredVPasses`, `compile.go`'s `passes` with their `required`
flags, `GoFV.SSA.loweredPasses`). The function changes form along the way, and so does the
semantics a pass theorem speaks about (`docs/plans/semantics2.md` §2): the state records its
`Layer` (`gen`: `run`; `low`: `runL`; `sched`: `runSched`; `loc`: `runLoc`). Each lowered pass
runs as a `LStep`:

- `proven run rel wf guard`: `run` is the pass (for `lower`, the checked `lowerChecked`) with a
  theorem concluding `rel` (an `LRel`: the layers of its input and output and its
  precondition), on inputs and outputs that pass `check` (when `wf`) and that `guard` (the
  theorem's remaining hypotheses: fragments, validators such as `moveB`, `critRelB`,
  `scheduleCheck`, `nilLateB`, `checkRA`, `trimRelB`, decided after the run) accepts;
- `stock run`: the stock port; no theorem.

A proven run whose hypotheses fail is dropped when the pass is optional (`skipped`) and kept
`unverified` when it is required, as in `verifiedPipeline`. A result equal to the input (function
and tables) in the same layer is the `identity`. `lower` (required) also runs the stock port: when
the checked result differs, the stock result is kept and the run is `unverified (checked
variant incomplete)`. A `schedule` run adds its input to `FState.nnf`: the refinement of
`schedule` holds on the inputs on which that function does not fault in the nil page
(`NoNilFault`, `GoFV.Proof.RefinesSchedLF.schedL`), a precondition of the end-to-end theorem.

The result is `fullyVerified` when every verdict is `proven`, `identity` or `skipped`, the
state is allocated (`loc`) and it has no `InvertFlags` (`Func.noInvertFlags`, as Go's codegen
requires); then `runLoc` of it refines `run` of the input
(`GoFV.Proof.PipelineFull.verifiedPipelineFull_refines`), and its flags are machine `NZCV`: only
`InvertFlags` reads their ghost component (`docs/plans/semantics2.md` §3).
-/

namespace GoFV.Opt

open GoFV.SSA

/-- The autos a pass created (`fe.SplitSlot`, `f.NewLocal`: each appends to `curfn.Dcl`): the
`name` aux values `out` defines and `input` does not. -/
def newAutos (input out : Tables) : Nat := Id.run do
  let mut k := 0
  for h : i in [0:out.auxes.size] do
    if let some { kind := .name .., .. } := out.auxes[i] then
      if (input.aux? i).isNone then k := k + 1
  return k

namespace Verified

/-- The form of a pipeline state and the semantics its theorems use (`docs/plans/semantics2.md`
§1, §2): generic (`run`), lowered (`runL`), scheduled (`runSched`), allocated (`runLoc`). -/
inductive Layer where
  | gen
  | low
  | sched
  | loc
  deriving DecidableEq, Repr, Inhabited

/-- The relation a lowered pass theorem concludes (`GoFV.Proof.PipelineFull.lrelHolds`). -/
inductive LRel where
  /-- `run` → `runL` under monotone contracts (`lower_refines_run`). -/
  | lower
  /-- `RefinesL`. -/
  | low
  /-- `RefinesLFrom (FrameSafe ∧ InitAvoids)` (elim unread autos). -/
  | lowFrame
  /-- `runL` → `runSched` on the inputs where the input does not fault in the nil page
  (`schedule`). -/
  | sched
  /-- `RefinesSched`. -/
  | schedS
  /-- `RefinesLS`: `runSched` → `runLoc` (`regalloc`). -/
  | ls
  /-- `RefinesLoc`. -/
  | loc
  deriving DecidableEq, Repr, Inhabited

/-- The layer of a relation's source. -/
def LRel.src : LRel → Layer
  | .lower => .gen
  | .low | .lowFrame | .sched => .low
  | .schedS | .ls => .sched
  | .loc => .loc

/-- The layer of a relation's target. -/
def LRel.tgt : LRel → Layer
  | .lower | .low | .lowFrame => .low
  | .sched | .schedS => .sched
  | .ls | .loc => .loc

/-- How the verified pipeline runs a pass from `lower` on (module doc). -/
inductive LStep where
  | proven (run : Pass) (rel : LRel) (wf : Bool) (guard : PassEnv → Func → PassOut → Bool)
  | stock (run : Pass)

end Verified

/-- One entry of `compile.go`'s `passes` from `lower` on (none has a `disabled` condition for
linux/arm64). -/
structure LPass where
  name : String
  required : Bool := false
  /-- The layer of the pass's result. -/
  out : Verified.Layer
  step : Verified.LStep
  /-- For a required pass run in a checked variant: the stock port (`StockPass.full`). -/
  full : Option Pass := none

/-- Whether `ssa.Compile` runs pass `p`: `optimize || required`. -/
def LPass.enabled (p : LPass) (env : PassEnv) : Except String Bool :=
  match env.flag "optimize" with
  | .error e => .error e
  | .ok optimize => .ok (optimize || p.required)

namespace Verified

open GoFV.Proof

/-- `lower_refines_run`'s hypotheses: a generic input without fused multiply-add shapes. -/
def lowerGuard (_ : PassEnv) (f : Func) (_ : PassOut) : Bool :=
  f.lowered == false && decide (FmaContract.contractAll f = f)

/-- `deadcode_refinesL`'s fragments (`DeadFrag`, `DeadFragL`) and form. -/
def deadGuardL (penv : PassEnv) (f : Func) (out : PassOut) : Bool :=
  Dead.deadFragB penv.tables f && Dead.deadFragLB penv.tables f && out.func.lowered == f.lowered

/-- `copyelim_refinesL`'s fragments (`CopyFrag`, `EmptyFrag`, `CopyLFrag`) and form. -/
def copyGuardL (penv : PassEnv) (f : Func) (out : PassOut) : Bool :=
  CopyElim.copyFrag penv.tables f && CopyElim.emptyFragB penv.tables f &&
    out.func.lowered == f.lowered && CopyElim.copyLFragB penv.tables f out.func

/-- The value-motion validator of `tighten`, `phi tighten`, `tighten tuple selectors`. -/
def moveGuard (_ : PassEnv) (f : Func) (out : PassOut) : Bool := MoveL.moveB f out.func

/-- `licm_refinesL`'s hypotheses: the unhoisted result passes `check`, `critical`'s relation to
the input, the motion validator to the output. -/
def licmGuard (penv : PassEnv) (f : Func) (out : PassOut) : Bool :=
  let u := MoveL.unhoist f out.func
  checkOK (checkEnv penv out.tables) u && Crit.critRelB f u && MoveL.moveB u out.func

/-- `regalloc`: the input runs alike in the output's tables (`tabsAgreeL`) and `checkRA`
accepts (`checkRA_sound`). -/
def regallocGuard (penv : PassEnv) (f : Func) (out : PassOut) : Bool :=
  LowerCheck.tabsAgreeL penv.tables out.tables f &&
    (RegallocCheck.checkRA out.tables f out.func).toBool

/-- `tabs` without the `AuxCall.Reg`/`ResultReg` caches (`CallABI.reg := none` in every call
aux). `regalloc` fills them (`op.go:137-190`) and only `regalloc` reads them (no runner does),
but they make the call auxes of its input differ between its input and output tables, so
`tabsAgreeL` would reject every function with a call; before `regalloc` they are empty. -/
def eraseCallRegs (tabs : Tables) : Tables :=
  { tabs with auxes := tabs.auxes.map fun
      | some d@{ kind := .call fn (some a), .. } =>
        some { d with kind := .call fn (some { a with reg := none }) }
      | d => d }

/-- `regalloc` without the call-register caches in its output tables (`eraseCallRegs`): the
verified pipeline's `regalloc` step. Go reads the caches only in `regalloc`, so the compiler
after it does not depend on them. -/
def regallocV : Pass := fun env f => do
  let out ← Regalloc.regallocPass env f
  pure { out with tables := eraseCallRegs out.tables }

def noGuardL (_ : PassEnv) (_ : Func) (_ : PassOut) : Bool := true

def deadcodeStepL : LStep := .proven deadcodePass .low true deadGuardL

end Verified

open Verified GoFV.Proof in
/-- `compile.go` `passes`, `lower` … `trim`, in order (`GoFV.SSA.loweredPasses`). -/
def loweredVPasses : Array LPass := #[
  { name := "lower", required := true, out := .low,
    step := .proven lowerChecked .lower false lowerGuard, full := some lower },
  { name := "addressing modes", out := .low, step := .stock addressingModesPass },
  { name := "late lower", required := true, out := .low, step := .stock lateLower },
  { name := "pair", out := .low, step := .stock pairPass },
  { name := "lowered deadcode for cse", out := .low, step := deadcodeStepL },
  { name := "lowered cse", out := .low,
    step := .proven loweredCsePass .low true fun penv f _ => CSEL.frag penv f },
  { name := "elim unread autos", out := .low,
    step := .proven elimUnreadAutosPass .lowFrame true fun penv f _ => unreadLFrag penv f },
  { name := "tighten tuple selectors", required := true, out := .low,
    step := .proven tightenTupleSelectorsPass .low true moveGuard },
  { name := "lowered deadcode", required := true, out := .low, step := deadcodeStepL },
  { name := "checkLower", required := true, out := .low,
    step := .proven checkLowerPass .low false noGuardL },
  { name := "loop invariant", out := .low, step := .proven licmPass .low true licmGuard },
  { name := "late phielim and copyelim", out := .low,
    step := .proven copyelimPass .low true copyGuardL },
  { name := "tighten", required := true, out := .low,
    step := .proven tightenPass .low true moveGuard },
  { name := "late deadcode", out := .low, step := deadcodeStepL },
  { name := "critical", required := true, out := .low,
    step := .proven criticalPass .low true fun _ f out => Crit.critRelB f out.func },
  { name := "phi tighten", out := .low, step := .proven phiTightenPass .low true moveGuard },
  { name := "likelyadjust", out := .low, step := .proven likelyadjustPass .low false noGuardL },
  { name := "layout", required := true, out := .low,
    step := .proven layoutPass .low false noGuardL },
  { name := "schedule", required := true, out := .sched,
    step := .proven schedulePass .sched true fun penv f out =>
      scheduleCheck penv.tables f out.func },
  { name := "late nilcheck", out := .sched,
    step := .proven nilcheckelim2Pass .schedS true fun penv f out =>
      NilLate.nilLateB penv.tables f out.func },
  { name := "flagalloc", required := true, out := .sched, step := .stock flagallocPass },
  { name := "regalloc", required := true, out := .loc,
    step := .proven regallocV .ls false regallocGuard },
  { name := "loop rotate", out := .loc, step := .proven loopRotatePass .loc false noGuardL },
  { name := "trim", out := .loc,
    step := .proven trimPass .loc false fun _ f out => TrimLoc.trimRelB f out.func }
]

namespace Verified

/-- The verified pipeline's state from `lower` on. -/
structure FState where
  st : VState
  layer : Layer := .gen
  /-- The inputs (tables, function) of the `schedule` runs: the end-to-end theorem assumes that
  they do not fault in the nil page (`NoNilFault`). -/
  nnf : List (Tables × Func) := []
  /-- `len(curfn.Dcl)` (`PassEnv.dclLen`): the input's, plus the autos the passes created. -/
  dclLen : Nat := 0
  /-- Every verdict of the passes before `lower` is `Verdict.ok`. -/
  genVerified : Bool := true

/-- `f` has no `InvertFlags`: Go's codegen fails on one (`ssaGenValue`), and it is the only op
that reads a flags value's ghost component `g` (`Sem.invertFlags`), so the machine-level flags of
an `InvertFlags`-free function are its `NZCV`. -/
def _root_.GoFV.SSA.Func.noInvertFlags (f : Func) : Bool :=
  f.valueTab.all fun | some v => v.op != .ARM64InvertFlags | none => true

/-- Every verdict is `ok`, the state is allocated (its `runLoc` refines the input's `run`), and
it has no `InvertFlags` (`Func.noInvertFlags`). -/
def FState.fullyVerified (s : FState) : Bool :=
  s.st.verified && s.layer == .loc && s.st.func.noInvertFlags

/-- Whether pass `p`'s result `out` passes `check` (not tried on allocated functions, which are
not SSA, and whose theorems do not ask for it). -/
def outWf (env : PassEnv) (p : LPass) (out : PassOut) : Bool :=
  p.out != .loc && (check (checkEnv env out.tables) out.func).toBool

/-- `s` with pass `p`'s result `out` (`wf`: whether it passes `check`; verdict `v`; `nnf` the
recorded `schedule` inputs). -/
def FState.adopt (s : FState) (p : LPass) (out : PassOut) (wf : Bool) (v : Verdict)
    (nnf : List (Tables × Func)) : FState :=
  { s with st := s.st.adopt p.name out wf v, layer := p.out, nnf
           dclLen := s.dclLen + newAutos s.st.tables out.tables }

/-- `s` after pass `p` with its result dropped. -/
def FState.skip (s : FState) (p : LPass) (why : String) : FState :=
  { s with st := s.st.skip p.name why }

/-- Why a proven step's theorem does not apply to `s` and the result `out` (`wf`: whether `out`
passes `check`), if so. -/
def FState.whyNot (s : FState) (penv : PassEnv) (rel : LRel) (wfReq : Bool)
    (guard : PassEnv → Func → PassOut → Bool) (out : PassOut) (wf : Bool) : Option String :=
  if s.layer != rel.src then some "layer"
  else if wfReq && !s.st.wf then some "input fails check"
  else if wfReq && !wf then some "output fails check"
  else if !guard penv s.st.func out then some "rejected"
  else none

/-- `s` continued with the result `out` of pass `p`: the identity when nothing changed in the
same layer; else `bad` (why its theorem does not apply, given whether `out` passes `check`)
decides between `proven` (with the `schedule` inputs `nnf`) and, for a required pass,
`unverified` or, for an optional one, `skipped`. -/
def FState.next (s : FState) (env : PassEnv) (p : LPass) (out : PassOut)
    (bad : Bool → Option String) (nnf : List (Tables × Func)) : FState :=
  if s.st.same out && s.layer == p.out then s.adopt p out s.st.wf .identity s.nnf
  else
    let wf := outWf env p out
    match bad wf with
    | none => s.adopt p out wf .proven nnf
    | some why => if p.required then s.adopt p out wf (.unverified why) s.nnf else s.skip p why

/-- The `nnf` after a proven run of `rel` on `s`. -/
def FState.nnfAfter (s : FState) (rel : LRel) : List (Tables × Func) :=
  if rel == .sched then (s.st.tables, s.st.func) :: s.nnf else s.nnf

/-- The environment of pass `name` on `s`. -/
def FState.passEnv (s : FState) (env : PassEnv) (name : String) : PassEnv :=
  { s.st.passEnv env name with dclLen := s.dclLen }

/-- Run pass `p` on `s` (module doc). -/
def runPassL (env : PassEnv) (s : FState) (p : LPass) : Except VError FState :=
  let penv := s.passEnv env p.name
  match p.enabled penv with
  | .error e => .error ⟨p.name, e⟩
  | .ok false => .ok s
  | .ok true =>
    match p.step with
    | .stock run =>
      match run penv s.st.func with
      | .error e => .error ⟨p.name, e⟩
      | .ok out =>
        .ok (if s.st.same out && s.layer == p.out then s.adopt p out s.st.wf .identity s.nnf
          else s.adopt p out (outWf env p out) (.unverified "no theorem") s.nnf)
    | .proven run rel wfReq guard =>
      match run penv s.st.func with
      | .error e => .error ⟨p.name, e⟩
      | .ok out =>
        match p.full with
        | none => .ok (s.next env p out (s.whyNot penv rel wfReq guard out) (s.nnfAfter rel))
        | some full =>
          match full penv s.st.func with
          | .error e => .error ⟨p.name, e⟩
          | .ok so =>
            if decide (so.func = out.func) then
              .ok (s.next env p out (s.whyNot penv rel wfReq guard out) (s.nnfAfter rel))
            else .ok (s.adopt p so (outWf env p so) (.unverified "checked variant incomplete") s.nnf)

/-- Run the passes `ps` in order. -/
def runPassesL (env : PassEnv) : List LPass → FState → Except VError FState
  | [], s => .ok s
  | p :: ps, s =>
    match runPassL env s p with
    | .error e => .error e
    | .ok s' => runPassesL env ps s'

/-- The layer of the input of pass `start` (an index into `stockPasses ++ loweredVPasses`). -/
def startLayer (start : Nat) : Layer :=
  if start ≤ stockPasses.size then .gen
  else ((loweredVPasses[start - stockPasses.size - 1]?).map (·.out)).getD .loc

end Verified

open Verified in
/-- **The verified pipeline through `trim`**: `verifiedPipeline` from `start`, then the passes
from `lower` on (`loweredVPasses`, from `start - stockPasses.size` when `start` is past
`rewrite tern`), with the input's `dcllen` `dcl` (module doc).
`GoFV.Proof.PipelineFull.verifiedPipelineFull_refines`: a `fullyVerified` result refines `f`. -/
def verifiedPipelineFull (env : PassEnv) (f : Func) (start : Nat := 0)
    (zv : Array (ID × Nat) := #[]) (dcl : Nat := 0) : Except VError FState :=
  match verifiedPipeline env f start zv with
  | .error e => .error e
  | .ok st =>
    runPassesL env (loweredVPasses.toList.drop (start - stockPasses.size))
      { st, layer := startLayer start, dclLen := dcl + newAutos env.tables st.tables
        genVerified := st.verified }

end GoFV.Opt
