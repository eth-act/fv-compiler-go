import GoFV.SSA.Export
import GoFV.SSA.TypeCmp

/-!
# The pass interface

A Lean pass is a port of one stock pass function (`deadcode`, `zcse`, …). It reads the
function and the context the stock pass can observe — the pass name (`f.pass.name`), the
export's fixed configuration, `Config.Types`, the type order and the definition tables in force
for its input section — and returns the new function and tables (input tables plus the objects
it created at fresh numbers, or redefinitions of objects it mutated). `Except.error` is Go's
`Fatalf` or a configuration the port does not cover.

Parity (`docs/PARITY.md`): `lake exe pass-parity` runs every registered pass on the exported
input of each of its pipeline instances and compares with the stock output.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- What a pass can observe besides the function. -/
structure PassEnv where
  /-- `f.pass.name`: the stock pass name (`"opt deadcode"`, …). -/
  passName : String
  /-- `base.Ctxt.Pkgpath`. -/
  pkg : GoStr
  /-- `f.Name`. -/
  funcName : GoStr
  /-- `f.ABISelf.Which()`. -/
  abi : Nat
  /-- `f.NoSplit`. -/
  nosplit : Bool
  pgohot : Bool
  /-- The export's `config` lines (`docs/contracts/export.md`, "Fixed configuration"). -/
  config : Array (String × Array Token)
  /-- `Config.Types` and the SSA pseudo-types (`typs` of section 0). -/
  typs : Array (String × TypeRef)
  /-- `types.(*Type).Compare`. -/
  typeOrder : TypeOrder
  /-- The definition tables in force for the input section. -/
  tables : Tables

/-- A pass's result. -/
structure PassOut where
  func : Func
  /-- The input tables plus the pass's new or redefined objects. -/
  tables : Tables

/-- A pass port. -/
abbrev Pass := PassEnv → Func → Except String PassOut

namespace PassEnv

/-- The value tokens of `config <key>`. -/
def config? (e : PassEnv) (key : String) : Option (Array Token) :=
  (e.config.find? (·.1 == key)).map (·.2)

/-- A `0`/`1` config flag; error if absent or not a flag. -/
def flag (e : PassEnv) (key : String) : Except String Bool :=
  match e.config? key with
  | some #[.word "0"] => pure false
  | some #[.word "1"] => pure true
  | _ => throw s!"config {key}: missing or not 0/1"

/-- `typ.<name>` (`Config.Types`) or an SSA pseudo-type (`Mem`, …). -/
def typ? (e : PassEnv) (name : String) : Option TypeRef :=
  (e.typs.find? (·.1 == name)).map (·.2)

/-- The definition of type `t`. -/
def type? (e : PassEnv) (t : TypeRef) : Option TypeDef := e.tables.type? t

end PassEnv

/-- A pass that only changes the function. -/
@[inline] def Pass.ofFunc (p : PassEnv → Func → Except String Func) : Pass :=
  fun env f => do return { func := ← p env f, tables := env.tables }

/-- A registered pass: the stock name(s) of its pipeline instances, the port, and Go's
`disabled` condition (`compile.go` pass table): a disabled pass does not run and the export has
no section for it. -/
structure PassEntry where
  /-- The Go function (`deadcode`, `copyelim`, …): `pass-parity --pass <fn>` selects every
  instance. -/
  fn : String
  /-- Stock pass names this port implements (`"early deadcode"`, …, `"generic deadcode"`). -/
  names : Array String
  run : Pass
  /-- `p.disabled` for this configuration (e.g. `!buildcfg.Experiment.PreemptibleLoops`). -/
  disabled : PassEnv → Except String Bool := fun _ => pure false

end GoFV.Opt
