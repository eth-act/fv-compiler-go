import GoFV.Opt.NumberLines
import GoFV.Opt.CopyElim
import GoFV.Opt.Deadcode
import GoFV.Opt.ShortCircuit
import GoFV.Opt.Decompose
import GoFV.Opt.Opt
import GoFV.Opt.ZCSE
import GoFV.Opt.CSE
import GoFV.Opt.PhiOptCheck
import GoFV.Opt.NilCheck
import GoFV.Opt.NilCheckRel
import GoFV.Opt.ProveCheck.Check
import GoFV.Opt.KnownBitsCheck
import GoFV.Opt.Fuse
import GoFV.Opt.ExpandCalls
import GoFV.Opt.SoftFloat
import GoFV.Opt.BranchElim
import GoFV.Opt.ElimDeadAutos
import GoFV.Opt.DeadAutosCheck
import GoFV.Opt.SccpCheck
import GoFV.Opt.CheckBCE
import GoFV.Opt.DeadStore
import GoFV.Opt.DeadStoreCheck
import GoFV.Opt.MemCombine
import GoFV.Opt.WriteBarrier
import GoFV.Opt.ReschedChecks
import GoFV.Opt.CpuFeatures
import GoFV.Opt.TabsAgree
import GoFV.Proof.Pass.CopyFrag
import GoFV.Proof.Pass.DeadFrag

/-!
# The verified generic pipeline (issue #189)

`stockPasses` is `compile.go`'s `passes` table from `number lines` to `rewrite tern` (the passes
before `lower`), each with its `required` flag, its Go `disabled` condition and how the verified
pipeline runs it (`Verified.Step`):

- `proven run rel guard`: `run` is the pass (or its checked, proven-only variant: `optChecked`,
  `proveChecked`, …) whose refinement theorem concludes `rel` (`Refines`, `RefinesUnder
  Env.Mono` or `RefinesFrom (FrameSafe ∧ InitAvoids)`) when the input and the output pass
  `check` and `guard` (the theorem's fragment hypothesis, decided) accepts the input;
- `stock run`: the stock port; no theorem.

`verifiedPipeline` runs the enabled passes in order (`ssa.Compile`'s test: `optimize ||
required`, not `disabled`) and checks the function between passes (`check` once on the input
and once on each changed result, never inside a pass). Per pass run it records a `Verdict`:

- `proven`: the theorem's hypotheses hold;
- `identity`: the result's function equals the input's, and so do the tables or at least what
  the function can observe of them (`tabsAgree`; `Refines.refl`, any pass);
- `skipped why`: an optional proven pass whose input is outside its theorem (`why`: the input
  fails `check`, or the guard rejects it) or whose output fails `check`: its result is dropped
  and the input kept (the identity is a refinement);
- `unverified why`: a stock port that changed the function, or a required proven pass in one of
  the situations of `skipped` (the result is kept: later stock passes need it).

The result is `verified` when every verdict is `proven`, `identity` or `skipped`; then it refines
the input (`GoFV.Proof.Pipeline.verifiedPipeline_refines`). The function, tables, effects and
type-object classes are chained as in the driver (`docs/DRIVER.md`), so with every pass proven
and every guard accepting, the result is the stock pipeline's except where a checked variant
undoes a rewrite.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Verified

/-- The refinement a pass theorem concludes (`GoFV.Proof.Pipeline.relHolds`). -/
inductive Rel where
  /-- `Refines`. -/
  | refines
  /-- `RefinesUnder Env.Mono`. -/
  | mono
  /-- `RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem)`. -/
  | frameSafe
  deriving DecidableEq, Repr, Inhabited

/-- How the verified pipeline runs a stock pass. -/
inductive Step where
  /-- The pass `run` has a theorem concluding `rel` on inputs `guard` accepts (both sides
  passing `check`). -/
  | proven (run : Pass) (rel : Rel) (guard : PassEnv → Func → Bool)
  /-- The stock port; no theorem. -/
  | stock (run : Pass)

end Verified

/-- One entry of `compile.go`'s `passes` (before `lower`). -/
structure StockPass where
  name : String
  required : Bool := false
  /-- `required: buildcfg.Experiment.SIMD` (`cpufeatures`). -/
  requiredSimd : Bool := false
  /-- Go's `disabled` condition (the export has no section for a disabled pass). -/
  disabled : PassEnv → Except String Bool := fun _ => pure false
  /-- How `verifiedPipeline` runs it. -/
  step : Verified.Step

/-- Whether `ssa.Compile` runs pass `p` for this function: `optimize || required`, and not
`disabled`. -/
def StockPass.enabled (p : StockPass) (env : PassEnv) : Except String Bool :=
  match env.flag "optimize" with
  | .error e => .error e
  | .ok optimize =>
    match (if p.requiredSimd then env.flag "exp.simd" else pure p.required : Except String Bool) with
    | .error e => .error e
    | .ok required =>
      if !optimize && !required then .ok false
      else match p.disabled env with
        | .error e => .error e
        | .ok d => .ok !d

namespace Verified

open GoFV.Proof.CopyElim GoFV.Proof.Dead

/-- `copyelim_refines`' fragment (`CopyFrag`, `EmptyFrag`), decided. -/
def copyGuard (env : PassEnv) (f : Func) : Bool := copyFrag env.tables f && emptyFragB env.tables f

/-- `deadcode_refines`' fragment (`DeadFrag`), decided. -/
def deadGuard (env : PassEnv) (f : Func) : Bool := deadFragB env.tables f

/-- No fragment hypothesis. -/
def noGuard (_ : PassEnv) (_ : Func) : Bool := true

def deadcodeStep : Step := .proven deadcodePass .refines deadGuard
def optStep : Step := .proven optChecked .mono noGuard

end Verified

open Verified in
/-- `compile.go` `passes`, `number lines` … `rewrite tern`, in order. -/
def stockPasses : Array StockPass := #[
  { name := "number lines", required := true, step := .proven numberLinesPass .refines noGuard },
  { name := "early phielim and copyelim", step := .proven copyelimPass .refines copyGuard },
  { name := "early deadcode", step := deadcodeStep },
  { name := "short circuit", step := .stock shortcircuitPass },
  { name := "decompose user", required := true, step := .stock Decompose.decomposeUserPass },
  { name := "pre-opt deadcode", step := deadcodeStep },
  { name := "opt", required := true, step := optStep },
  { name := "zero arg cse", required := true, step := .proven zcsePass .refines noGuard },
  { name := "opt deadcode", required := true, step := deadcodeStep },
  { name := "generic cse", step := .proven csePass .refines cseFrag },
  { name := "phiopt", step := .proven phioptPass .refines noGuard },
  { name := "gcse deadcode", required := true, step := deadcodeStep },
  { name := "nilcheckelim", step := .proven nilcheckelimPass .refines nilFrag },
  { name := "prove", step := .proven proveChecked .mono noGuard },
  { name := "divisible", required := true, step := .proven divisibleChecked .mono noGuard },
  { name := "divmod", required := true, step := .proven divmodChecked .mono noGuard },
  { name := "middle opt", required := true, step := optStep },
  { name := "known bits", step := .proven knownBitsPass .mono noGuard },
  { name := "early fuse", step := .stock fuseEarlyPass },
  { name := "expand calls", required := true, step := .stock expandCallsPass },
  { name := "decompose builtin", required := true,
    step := .stock Decompose.postExpandCallsDecomposePass },
  { name := "softfloat", required := true, step := .proven softfloatPass .refines noGuard },
  { name := "branchelim", step := .proven branchelimPass .refines noGuard },
  { name := "late opt", required := true, step := optStep },
  { name := "dead auto elim", step := .proven elimDeadAutosPass .frameSafe daeFrag },
  { name := "sccp", step := .proven sccpChecked .mono noGuard },
  { name := "generic deadcode", required := true, step := deadcodeStep },
  { name := "late fuse", step := .stock fuseLatePass },
  { name := "check bce", step := .proven checkbcePass .refines noGuard },
  { name := "dse", step := .proven dsePass .refines dseFrag },
  { name := "memcombine", step := .stock memcombinePass },
  { name := "writebarrier", required := true, step := .stock writebarrierPass },
  { name := "insert resched checks", disabled := reschedChecksDisabled,
    step := .stock reschedChecksPass },
  { name := "cpufeatures", requiredSimd := true, disabled := simdDisabled,
    step := .stock cpufeaturesPass },
  { name := "rewrite tern", disabled := simdDisabled, step := .stock rewriteTernPass }
]

/-- Index of stock pass `name`. -/
def passIndex? (name : String) : Option Nat := stockPasses.findIdx? (·.name == name)

/-- The `*types.Type` object classes after a pass that turned `input` into `out` (#101): the
reported objects in order (`.of w` takes `w`'s class at that point), then a value keeps its
class if it is still in the function and either was reported or has its input type number. -/
def nextZvar (input : Func) (out : PassOut) (zv : Std.HashMap ID Nat) (next : Nat) :
    Std.HashMap ID Nat × Nat := Id.run do
  let mut run := zv
  let mut next := next
  let mut reported : Std.HashSet ID := {}
  for (id, o) in out.typeObjs do
    reported := reported.insert id
    match o with
    | .canonical => run := run.erase id
    | .fresh => run := run.insert id next; next := next + 1
    | .of w => match run[w]? with
      | some c => run := run.insert id c
      | none => run := run.erase id
  let keep (id : ID) : Bool := match out.func.value? id with
    | none => false
    | some v => reported.contains id || (input.value? id).any (·.type == v.type)
  return (run.filter fun id _ => keep id, next)

namespace Verified

/-- What the verified pipeline concluded about one pass run (module doc). -/
inductive Verdict where
  | proven
  | identity
  | skipped (why : String)
  | unverified (why : String)
  deriving DecidableEq, Repr, Inhabited

/-- The verdict keeps the pipeline's result a refinement of its input. -/
def Verdict.ok : Verdict → Bool
  | .unverified _ => false
  | _ => true

def Verdict.toString : Verdict → String
  | .proven => "proven"
  | .identity => "identity"
  | .skipped why => s!"skipped ({why})"
  | .unverified why => s!"unverified ({why})"

instance : ToString Verdict := ⟨Verdict.toString⟩

/-- A pass failed (`Except.error`: Go's `Fatalf` or an uncovered configuration). -/
structure VError where
  pass : String
  msg : String

/-- The verified pipeline's state. -/
structure VState where
  func : Func
  tables : Tables
  /-- `func` passes `check` (with `tables` and the environment's `typs`). -/
  wf : Bool
  /-- Every verdict so far is `Verdict.ok`. -/
  verified : Bool := true
  /-- Number of passes run so far (the section index of the state). -/
  ran : Nat := 0
  /-- The last pass run. -/
  last : String := "start"
  /-- The frontend side effects of the passes whose results were kept, in order. -/
  effects : Array Effect := #[]
  /-- `*types.Type` object classes (`nextZvar`; the next pass's `PassEnv.zvar`). -/
  zvar : Std.HashMap ID Nat := {}
  nextClass : Nat := 1
  /-- One verdict per pass run. -/
  log : Array (String × Verdict) := #[]

/-- The checker environment of the pipeline's states. -/
def checkEnv (env : PassEnv) (tabs : Tables) : CheckEnv := { tabs, typs := env.typs }

/-- The initial state: `f` with the environment's tables and the input section's `zvar`. -/
def VState.init (env : PassEnv) (f : Func) (zv : Array (ID × Nat) := #[]) : VState :=
  { func := f, tables := env.tables, wf := (check (checkEnv env env.tables) f).toBool
    zvar := zv.foldl (fun m (v, c) => m.insert v c) {}
    nextClass := zv.foldl (fun n (_, c) => max n (c + 1)) 1 }

/-- The environment of stock pass `name` on state `st`. -/
def VState.passEnv (st : VState) (env : PassEnv) (name : String) : PassEnv :=
  { env with passName := name, tables := st.tables, zvar := fun v => st.zvar.getD v 0 }

/-- `st` after pass `name` with its result dropped. -/
def VState.skip (st : VState) (name : String) (why : String) : VState :=
  { st with ran := st.ran + 1, last := name, log := st.log.push (name, .skipped why) }

/-- `st` continued with pass `name`'s result `out` (verdict `v`, `wf` whether `out.func` passes
`check`). -/
def VState.adopt (st : VState) (name : String) (out : PassOut) (wf : Bool) (v : Verdict) :
    VState :=
  let z := nextZvar st.func out st.zvar st.nextClass
  { func := out.func, tables := out.tables, wf, verified := st.verified && v.ok
    ran := st.ran + 1, last := name, effects := st.effects ++ out.effects, zvar := z.1
    nextClass := z.2, log := st.log.push (name, v) }

/-- Whether `out` leaves the function and the tables of `st` unchanged. -/
def VState.same (st : VState) (out : PassOut) : Bool :=
  decide (out.func = st.func) && decide (out.tables.posBases = st.tables.posBases) &&
    decide (out.tables.types = st.tables.types) && decide (out.tables.auxes = st.tables.auxes) &&
    decide (out.tables.slots = st.tables.slots)

/-- Continue `st` with the result `out` of pass `p`. `claim`: `none` if `p` is proven and its
input is in its theorem's hypotheses (guard, `check`), else why not. A result with the input's
function and tables the function cannot tell from the input's (`tabsAgree`: e.g. a padded slot
table) is the identity. Otherwise its function is checked: a proven pass whose output fails
`check` is unverified when required, else dropped. -/
def VState.continue (st : VState) (env : PassEnv) (p : StockPass) (out : PassOut)
    (claim : Option String) : VState :=
  if st.same out then st.adopt p.name out st.wf .identity
  else
    let wf := (check (checkEnv env out.tables) out.func).toBool
    if decide (out.func = st.func) && tabsAgree st.tables out.tables st.func then
      st.adopt p.name out wf .identity
    else
    match claim with
    | some why => st.adopt p.name out wf (.unverified why)
    | none =>
      if wf then st.adopt p.name out wf .proven
      else if p.required then st.adopt p.name out wf (.unverified "output fails check")
      else st.skip p.name "output fails check"

/-- Run stock pass `p` on `st` (module doc). -/
def runPass (env : PassEnv) (st : VState) (p : StockPass) : Except VError VState :=
  let penv := st.passEnv env p.name
  match p.enabled penv with
  | .error e => .error ⟨p.name, e⟩
  | .ok false => .ok st
  | .ok true =>
    match p.step with
    | .stock run =>
      match run penv st.func with
      | .error e => .error ⟨p.name, e⟩
      | .ok out => .ok (st.continue env p out (some "no theorem"))
    | .proven run _ guard =>
      let why : Option String :=
        if !st.wf then some "input fails check"
        else if !guard penv st.func then some "fragment"
        else none
      match why, p.required with
      | some w, false => .ok (st.skip p.name w)
      | _, _ =>
        match run penv st.func with
        | .error e => .error ⟨p.name, e⟩
        | .ok out => .ok (st.continue env p out why)

/-- Run the passes `ps` in order. -/
def runPasses (env : PassEnv) : List StockPass → VState → Except VError VState
  | [], st => .ok st
  | p :: ps, st =>
    match runPass env st p with
    | .error e => .error e
    | .ok st' => runPasses env ps st'

end Verified

open Verified in
/-- **The verified generic pipeline**: the stock passes from index `start` (default `number
lines`) to `rewrite tern` on `f`, with the input tables `env.tables` and input `zvar` classes
`zv` (module doc). `GoFV.Proof.Pipeline.verifiedPipeline_refines`: a `verified` result refines
`f`. -/
def verifiedPipeline (env : PassEnv) (f : Func) (start : Nat := 0) (zv : Array (ID × Nat) := #[]) :
    Except VError VState :=
  runPasses env (stockPasses.toList.drop start) (VState.init env f zv)

end GoFV.Opt
