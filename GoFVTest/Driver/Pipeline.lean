import GoFVTest.Parity.Registry
import GoFV.Opt.Verified

/-!
# The Lean generic pipeline

`GoFV.Opt.stockPasses` (`compile.go`'s `passes` table from `number lines` up to, not including,
`lower`), with `StockPass.enabled` (`optimize || required`, not `disabled`, as in
`ssa.Compile`). The pipeline chains the registered Lean ports and stops at the first enabled pass
without a port (`docs/DRIVER.md`). `GoFV.Opt.verifiedPipeline` is the verified variant.
-/

namespace GoFVTest.Driver

open GoFV.SSA GoFV.Opt GoFVTest.Parity

/-- The registered port of stock pass `name`. -/
def port? (name : String) : Option PassEntry := registry.find? (·.names.contains name)

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
    match p.enabled penv with
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
