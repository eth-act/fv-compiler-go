import GoFV.Opt.NumberLines
import GoFV.Opt.CopyElim
import GoFV.Opt.Deadcode
import GoFV.Opt.ShortCircuit
import GoFV.Opt.DecomposeCheck
import GoFV.Opt.Opt
import GoFV.Opt.ZCSE
import GoFV.Opt.CSE
import GoFV.Opt.PhiOptCheck
import GoFV.Opt.NilCheck
import GoFV.Opt.NilCheckRel
import GoFV.Opt.ProveCheck.Check
import GoFV.Opt.KnownBitsCheck
import GoFV.Opt.Fuse
import GoFV.Opt.ExpandCallsCheck
import GoFV.Opt.SoftFloat
import GoFV.Opt.BranchElim
import GoFV.Opt.ElimDeadAutos
import GoFV.Opt.DeadAutosCheck
import GoFV.Opt.SccpCheck
import GoFV.Opt.CheckBCE
import GoFV.Opt.DeadStore
import GoFV.Opt.DeadStoreCheck
import GoFV.Opt.MemCombine.Check
import GoFV.Opt.WriteBarrierCheck
import GoFV.Opt.ReschedChecks
import GoFV.Opt.CpuFeatures
import GoFV.Opt.TabsAgree
import GoFV.Proof.Pass.CopyFrag
import GoFV.Proof.Pass.DeadFrag

variable [GoFV.SSA.Sem.Addrs]

/-!
# The verified generic pipeline (issue #189)

`stockPasses` is `compile.go`'s `passes` table from `number lines` to `rewrite tern` (the passes
before `lower`), each with its `required` flag, its Go `disabled` condition and how the verified
pipeline runs it (`Verified.Step`):

- `proven run rel guard`: `run` is the pass (or its checked, proven-only variant: `optChecked`,
  `proveChecked`, …) whose refinement theorem concludes `rel` (`Refines`, `RefinesUnder
  Env.Mono`, `RefinesFrom (FrameSafe ∧ InitAvoids)` or, for the checked rewrite passes,
  `RefinesFrom (RwPre tabs fe f)`: also malloc-family contracts that return non-nil pointers,
  non-nil dictionary arguments of the input, the runtime's `memclrNoHeapPointers`/`memmove`
  contracts, if present, and the input's and the frontend's read-only symbols holding their
  exported bytes, issue
  #151) when the input and the output pass
  `check` and `guard` (the theorem's fragment hypothesis, decided) accepts the input;
- `stock run`: the stock port; no theorem.

`verifiedPipeline` runs the enabled passes in order (`ssa.Compile`'s test: `optimize ||
required`, not `disabled`) and checks the function between passes (`check` once on the input
and once on each changed result, never inside a pass). Per pass run it records a `Verdict`:

- `proven`: the theorem's hypotheses hold;
- `identity`: the result's function equals the input's, and so do the tables or at least what
  the function can observe of them (`tabsAgree`; `Refines.refl`, any pass);
- `skipped why`: an optional proven pass whose input is outside its theorem (`why`: the input
  fails `check`, the guard rejects it, its dictionary parameters, `NilCheck.dictParams`,
  differ from the pipeline input's, or it names read-only symbols, `RewriteCheck.roSyms`, or its
  tables have `ifaceeq`/`efaceeq` descriptor symbols, `RewriteCheck.eqSyms`, the pipeline's
  precondition does not name, `pipelineEq`)
  or whose output fails `check`: its result is dropped and the input kept (the identity is a
  refinement);
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
  /-- `RefinesFrom (RwPre tabs fe f)` on the pass's input `f` in `tabs` with the frontend tables
  `fe` (the checked rewrite passes): monotone contracts, malloc-family contracts that return
  non-nil pointers (`Env.AllocNonNil`), non-nil dictionary arguments
  (`NilCheck.dictParams tabs f`), the runtime's `memclrNoHeapPointers`/`memmove` contracts, if
  present (`Env.MemOps`), the read-only symbols `RewriteCheck.roPass tabs fe f` holding their
  exported bytes (`RoImage`), inputs that hold no pointer into a frame temporary
  (`InitAvoids`), and `ifaceeq`/`efaceeq` contracts on the descriptor symbols of `tabs` and `fe`
  (`Env.IfaceEq` of `RewriteCheck.eqPass tabs fe`). -/
  | rw
  /-- `RefinesFrom WbPre` (writebarrier): the memory with the global image has a defined,
  read-only write-barrier flag and no write-barrier buffer, and the contracts keep that. -/
  | wb
  /-- `RefinesFrom DecPre` (decompose user/builtin): monotone contracts that cannot tell whether
  unreachable frame temporaries exist (`Env.TempOblivious`) and inputs holding no pointer into a
  frame temporary (`InitAvoids`). -/
  | dec
  /-- `RefinesUnder (fun env => env.Mono ∧ env.FrameKeep)` (expand calls): monotone contracts
  that keep the caller's frame blocks and return no memory (`Env.FrameKeep`). -/
  | frameKeep
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
  /-- For a required pass run in a checked variant: the stock port. When the variant's result
  differs from it, the stock result is kept and the run is unverified, since later passes and
  `lower` need every rewrite (an undone `PtrIndex` or `IMake` rewrite is not lowered). -/
  full : Option Pass := none

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

/-- Largest value table `proveChecked` validates (the largest corpus functions have about 5,000
values and take a few seconds). -/
def proveMaxValues : Nat := 20000

/-- `prove`'s guard: a size limit, not a fragment of its theorem. Skipping the optional pass keeps
the input, which is sound; it keeps `proveChecked`'s cost bounded on generated giants. -/
def proveGuard (_ : PassEnv) (f : Func) : Bool := f.valueTab.size ≤ proveMaxValues

/-- `writebarrier_refines`' acceptance test (`writebarrierChecked` without the error): the stock
result is accepted by `WBCheck.wbOK` and the input runs alike in its tables. A rejected result is
kept (the pass is required) and marked unverified. -/
def wbGuard (env : PassEnv) (f : Func) : Bool :=
  match writebarrier env f with
  | .ok out => tabsAgree env.tables out.tables f && WBCheck.wbOK out.tables f out.func
  | .error _ => true

def deadcodeStep : Step := .proven deadcodePass .refines deadGuard
def optStep : Step := .proven optChecked .rw noGuard

end Verified

open Verified in
/-- `compile.go` `passes`, `number lines` … `rewrite tern`, in order. -/
def stockPasses : Array StockPass := #[
  { name := "number lines", required := true, step := .proven numberLinesPass .refines noGuard },
  { name := "early phielim and copyelim", step := .proven copyelimPass .refines copyGuard },
  { name := "early deadcode", step := deadcodeStep },
  { name := "short circuit", step := .proven shortcircuitPass .refines noGuard },
  { name := "decompose user", required := true,
    step := .proven Decompose.decomposeUserPass .dec Decompose.decUserFrag },
  { name := "pre-opt deadcode", step := deadcodeStep },
  { name := "opt", required := true, step := optStep, full := some opt },
  { name := "zero arg cse", required := true, step := .proven zcsePass .refines noGuard },
  { name := "opt deadcode", required := true, step := deadcodeStep },
  { name := "generic cse", step := .proven csePass .refines cseFrag },
  { name := "phiopt", step := .proven phioptPass .refines noGuard },
  { name := "gcse deadcode", required := true, step := deadcodeStep },
  { name := "nilcheckelim", step := .proven nilcheckelimPass .refines nilFrag },
  { name := "prove", step := .proven proveChecked .mono proveGuard },
  { name := "divisible", required := true, step := .proven divisibleChecked .rw noGuard,
    full := some divisible },
  { name := "divmod", required := true, step := .proven divmodChecked .rw noGuard,
    full := some divmod },
  { name := "middle opt", required := true, step := optStep, full := some opt },
  { name := "known bits", step := .proven knownBitsPass .mono noGuard },
  { name := "early fuse", step := .proven fuseEarlyPass .refines noGuard },
  { name := "expand calls", required := true,
    step := .proven expandCallsPass .frameKeep expandCallsFrag },
  { name := "decompose builtin", required := true,
    step := .proven Decompose.postExpandCallsDecomposePass .dec Decompose.decBuiltinFrag },
  { name := "softfloat", required := true, step := .proven softfloatPass .refines noGuard },
  { name := "branchelim", step := .proven branchelimPass .refines noGuard },
  { name := "late opt", required := true, step := optStep, full := some opt },
  { name := "dead auto elim", step := .proven elimDeadAutosPass .frameSafe daeFrag },
  { name := "sccp", step := .proven sccpChecked .mono noGuard },
  { name := "generic deadcode", required := true, step := deadcodeStep },
  { name := "late fuse", step := .proven fuseLatePass .refines noGuard },
  { name := "check bce", step := .proven checkbcePass .refines noGuard },
  { name := "dse", step := .proven dsePass .refines dseFrag },
  { name := "memcombine", step := .proven memcombineChecked .mono noGuard },
  { name := "writebarrier", required := true,
    step := .proven writebarrierPass .wb wbGuard },
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
  /-- The input's dictionary parameters (`NilCheck.dictParams`), which the precondition of the
  `rw` steps names: a proven pass runs only on states with the same ones. -/
  dict : List Nat := []
  /-- The read-only symbols the pipeline's precondition pins (`pipelineRo`): the input's and every
  one defined in the frontend tables. A proven `rw` step runs only on states whose read-only
  symbols are among them. -/
  ro : List (String × Sem.Alloc) := []
  /-- The `runtime.ifaceeq`/`efaceeq` descriptor symbols the pipeline's precondition names
  (`pipelineEq`): those of the input's tables and the frontend's. A proven `rw` step runs only on
  states whose tables' descriptor symbols are among them. -/
  eq : List String × List String := ([], [])
  /-- One verdict per pass run. -/
  log : Array (String × Verdict) := #[]

/-- The checker environment of the pipeline's states. -/
def checkEnv (env : PassEnv) (tabs : Tables) : CheckEnv := { tabs, typs := env.typs }

/-- The read-only symbols the pipeline's precondition `RoImage` pins for input `f`: those `f`
names and every one the export file's frontend defines. Passes take new symbols (e.g. the data
of a `ConstString` opt materialises, `generic.rules:1022`) from the frontend, so pinning only
`f`'s made every proven pass after such a rewrite unverified (#293). -/
def pipelineRo (env : PassEnv) (f : Func) : List (String × Sem.Alloc) :=
  RewriteCheck.roSyms env.tables f ++ RewriteCheck.roAll env.frontend ++
    RewriteCheck.roStrs env.tables ++ RewriteCheck.roStrs env.frontend

/-- The `runtime.ifaceeq`/`efaceeq` descriptor symbols the pipeline's precondition `Env.IfaceEq`
names: those of the environment's tables and of its frontend tables (`RewriteCheck.eqPass`), so
a pass that resolves a descriptor or takes a symbol from the frontend keeps them. -/
def pipelineEq (env : PassEnv) : List String × List String :=
  RewriteCheck.eqPass env.tables env.frontend

/-- The initial state: `f` with the environment's tables and the input section's `zvar`. -/
def VState.init (env : PassEnv) (f : Func) (zv : Array (ID × Nat) := #[]) : VState :=
  { func := f, tables := env.tables, wf := (check (checkEnv env env.tables) f).toBool
    zvar := zv.foldl (fun m (v, c) => m.insert v c) {}
    nextClass := zv.foldl (fun n (_, c) => max n (c + 1)) 1
    dict := NilCheck.dictParams env.tables f
    ro := pipelineRo env f
    eq := pipelineEq env }

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
    nextClass := z.2, log := st.log.push (name, v), dict := st.dict, ro := st.ro, eq := st.eq }

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
        else if NilCheck.dictParams st.tables st.func != st.dict then
          some "dictionary parameters changed"
        else if !(RewriteCheck.roSyms st.tables st.func).all st.ro.contains then
          some "read-only symbols changed"
        else if !((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
            (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) then
          some "descriptor symbols changed"
        else none
      match why, p.required with
      | some w, false => .ok (st.skip p.name w)
      | _, _ =>
        match run penv st.func with
        | .error e => .error ⟨p.name, e⟩
        | .ok out =>
          match p.full with
          | none => .ok (st.continue env p out why)
          | some full =>
            match full penv st.func with
            | .error e => .error ⟨p.name, e⟩
            | .ok so =>
              if decide (so.func = out.func) then .ok (st.continue env p out why)
              else .ok (st.continue env p so (some "checked variant incomplete"))

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
