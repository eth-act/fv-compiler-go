import GoFVTest.Parity.Registry

/-!
# The Lean generic pipeline

`compile.go`'s `passes` table from `number lines` up to (not including) `lower`, with each
pass's `required` flag; `disabled` comes from the registered port (`PassEntry.disabled`). A pass
runs iff `optimize || required` and it is not disabled, as in `ssa.Compile`. The pipeline
chains the registered Lean ports and stops at the first enabled pass without a port
(`docs/DRIVER.md`).
-/

namespace GoFVTest.Driver

open GoFV.SSA GoFV.Opt GoFVTest.Parity

/-- One entry of `compile.go`'s `passes` (before `lower`). -/
structure StockPass where
  name : String
  required : Bool := false
  /-- `required: buildcfg.Experiment.SIMD` (`cpufeatures`). -/
  requiredSimd : Bool := false

/-- `compile.go` `passes`, `number lines` … `rewrite tern`, in order. -/
def stockPasses : Array StockPass := #[
  { name := "number lines", required := true },
  { name := "early phielim and copyelim" },
  { name := "early deadcode" },
  { name := "short circuit" },
  { name := "decompose user", required := true },
  { name := "pre-opt deadcode" },
  { name := "opt", required := true },
  { name := "zero arg cse", required := true },
  { name := "opt deadcode", required := true },
  { name := "generic cse" },
  { name := "phiopt" },
  { name := "gcse deadcode", required := true },
  { name := "nilcheckelim" },
  { name := "prove" },
  { name := "divisible", required := true },
  { name := "divmod", required := true },
  { name := "middle opt", required := true },
  { name := "known bits" },
  { name := "early fuse" },
  { name := "expand calls", required := true },
  { name := "decompose builtin", required := true },
  { name := "softfloat", required := true },
  { name := "branchelim" },
  { name := "late opt", required := true },
  { name := "dead auto elim" },
  { name := "sccp" },
  { name := "generic deadcode", required := true },
  { name := "late fuse" },
  { name := "check bce" },
  { name := "dse" },
  { name := "memcombine" },
  { name := "writebarrier", required := true },
  { name := "insert resched checks" },
  { name := "cpufeatures", requiredSimd := true },
  { name := "rewrite tern" }
]

/-- The registered port of stock pass `name`. -/
def port? (name : String) : Option PassEntry := registry.find? (·.names.contains name)

/-- Whether `ssa.Compile` runs pass `p` for this function: `optimize || required`, and not
`disabled`. Passes without a port and with a Go `disabled` condition do not exist (all three
such passes are registered). -/
def enabled (env : PassEnv) (p : StockPass) : Except String Bool := do
  let optimize ← env.flag "optimize"
  let required ← if p.requiredSimd then env.flag "exp.simd" else pure p.required
  if !optimize && !required then return false
  match port? p.name with
  | some e => return !(← e.disabled { env with passName := p.name })
  | none => return true

/-- Why the pipeline stopped. -/
inductive Stop where
  /-- Every enabled pass up to `lower` ran. -/
  | done
  /-- The enabled pass `pass` has no Lean port. -/
  | unported (pass : String)
  /-- Pass `pass` failed (`Except.error`: Go's `Fatalf` or an uncovered configuration). -/
  | error (pass : String) (msg : String)
  /-- The `step` callback stopped the run after pass `pass`. -/
  | halted (pass : String)
  deriving Inhabited, BEq

/-- The pipeline's state: the function, the tables in force, and the last pass run. -/
structure State where
  func : Func
  tables : Tables
  /-- Number of passes run so far (the section index of the state). -/
  ran : Nat := 0
  last : String := "start"
  /-- The frontend side effects of the passes run so far, in order. -/
  effects : Array Effect := #[]
  /-- `*types.Type` object classes of values with a non-canonical object (the input's `zvar`,
  then what the passes report, `PassOut.typeObjs`); the next pass's `PassEnv.zvar` (#101). -/
  zvar : Std.HashMap ID Nat := {}
  /-- The next unused class. -/
  nextClass : Nat := 1

/-- The initial state of a segment whose input section is `func` with `zvar` classes `zv`. -/
def State.ofSection (func : Func) (tables : Tables) (zv : Array (ID × Nat)) : State :=
  { func, tables, zvar := zv.foldl (fun m (v, c) => m.insert v c) {}
    nextClass := zv.foldl (fun n (_, c) => max n (c + 1)) 1 }

/-- The classes after a pass that turned `input` into `out`: the reported objects in order
(`.of w` takes `w`'s class at that point), then a value keeps its class if it is still in the
function and either was reported or has its input type number. -/
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

/-- Index of stock pass `name`. -/
def passIndex? (name : String) : Option Nat := stockPasses.findIdx? (·.name == name)

/-- Run the enabled passes from index `start` until `lower` or the first unported or failing
pass. `step` sees each pass's result (name, state after it) and may stop the run (`false`).
Returns why it stopped and the last state (the input of the pass it stopped at). -/
def runFrom {m : Type → Type} [Monad m] (env : PassEnv) (st : State) (start : Nat := 0)
    (step : String → State → m Bool := fun _ _ => pure true) : m (Stop × State) := do
  let mut st := st
  for h : i in [start:stockPasses.size] do
    let p := stockPasses[i]
    let zv := st.zvar
    let penv := { env with passName := p.name, tables := st.tables, zvar := fun v => zv.getD v 0 }
    match enabled penv p with
    | .error e => return (.error p.name e, st)
    | .ok false => continue
    | .ok true => pure ()
    let some e := port? p.name | return (.unported p.name, st)
    match e.run penv st.func with
    | .error msg => return (.error p.name msg, st)
    | .ok out =>
      let (zvar, nextClass) := nextZvar st.func out st.zvar st.nextClass
      st := { func := out.func, tables := out.tables, ran := st.ran + 1, last := p.name
              effects := st.effects ++ out.effects, zvar, nextClass }
      if !(← step p.name st) then return (.halted p.name, st)
  return (.done, st)

end GoFVTest.Driver
