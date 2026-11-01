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
  /-- Frontend objects: the definitions of the whole export file (latest wins). Only for
  objects a pass obtains from the frontend rather than computes (`fe.Syslook`,
  `reflectdata.TypeLinksym`: `*obj.LSym` contents such as read-only data, relocations and
  `rtype` facts), looked up by symbol name; never function state. The pass still numbers what
  it creates itself. -/
  frontend : Tables := {}
  /-- The input section's `zvar`: type-object class of zero-argument values whose type number
  has several `*types.Type` objects (`zcse` keys on the pointer); absent: class 0. -/
  zvar : ID → Nat := fun _ => 0
  /-- The file's `ptrcache`: whether `types.NewPtr` of a type number returns a shared object
  (else a fresh one; #101). -/
  ptrCache : TypeRef → Bool := fun _ => false

/-- A frontend side effect of a pass: compiler state outside the function and the definition
tables that the stock pass changes (`docs/DRIVER.md`, "Effects"). The driver replays the
effects of the passes it imports, in order. -/
inductive Effect where
  /-- `reflectdata.MarkTypeSymUsedInInterface(sym, curfn)` (`rewriteFixedLoad`): an
  `R_USEIFACE` relocation from the function's symbol to the symbol aux `sym`. -/
  | useIface (sym : AuxRef)
  deriving DecidableEq, Inhabited, Repr

/-- The `*types.Type` object a pass gave a value it created or retyped (#101): `zcse` keys
zero-argument values on the type pointer, and the backend's `types.NewPtr` makes a fresh object
when the element has no cached pointer type (`PassEnv.ptrCache`). The chained pipeline turns
these into the next pass's `PassEnv.zvar`. -/
inductive TypeObj where
  /-- The type number's canonical object (`zvar` class 0). -/
  | canonical
  /-- A new object, distinct from every other. -/
  | fresh
  /-- The object value `v` had (its type, e.g. `v.Type` in a rule result). -/
  | of (v : ID)
  deriving DecidableEq, Inhabited, Repr

/-- A pass's result. -/
structure PassOut where
  func : Func
  /-- The input tables plus the pass's new or redefined objects. -/
  tables : Tables
  /-- The pass's frontend side effects, in the order the stock pass causes them. -/
  effects : Array Effect := #[]
  /-- Type objects of the values the pass created or retyped, in order (a later entry for a
  value wins). Other values keep their object if their type number is unchanged, else get the
  canonical one. -/
  typeObjs : Array (ID × TypeObj) := #[]

/-- A pass port. -/
abbrev Pass := PassEnv → Func → Except String PassOut

/-- A decimal integer (`String.toInt?` on the config's digits; written over `String.toList` so
that the kernel can evaluate passes in non-vacuity witnesses). -/
def decInt? (s : String) : Option Int :=
  let digits (cs : List Char) : Option Nat :=
    if cs.isEmpty then none else
    cs.foldl (fun acc c => acc.bind fun n =>
      if c.isDigit then some (n * 10 + (c.toNat - '0'.toNat)) else none) (some 0)
  match s.toList with
  | '-' :: cs => (digits cs).map fun n => -(n : Int)
  | cs => (digits cs).map Int.ofNat

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

/-- The `*obj.LSym` aux named `name` (with ABI `abi`, if given) in `tabs`: its number and
definition. LSyms are interned by name and ABI, so this is Go's pointer identity. -/
def findSym? (tabs : Tables) (name : GoStr) (abi : Option Nat := none) :
    Option (AuxRef × AuxDef) := Id.run do
  for h : i in [0:tabs.auxes.size] do
    if let some d := tabs.auxes[i] then
      if let .sym n a .. := d.kind then
        if n == name && abi.all (· == a) then return some (i, d)
  return none

/-- The frontend's definition of the symbol `name` (`frontend`): for symbols a pass obtains
from the frontend (`fe.Syslook`, `reflectdata.TypeLinksym`, relocation targets). -/
def frontendSym? (e : PassEnv) (name : GoStr) (abi : Option Nat := none) : Option AuxDef :=
  (findSym? e.frontend name abi).map (·.2)

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
  /-- For a pass whose stock result depends on Go's randomized map iteration (`sccp`): the
  port rerun with the iteration order recovered from the stock output (arguments: input
  function, stock output function). The harness calls it when the deterministic run differs
  and counts an exact match as "order replayed" (`docs/PARITY.md`). -/
  replay : Option (PassEnv → Func → Func → Except String PassOut) := none

end GoFV.Opt
