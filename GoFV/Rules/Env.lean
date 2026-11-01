import GoFV.SSA.Alloc
import GoFV.SSA.TypeCmp
import GoFV.SSA.XPosMap
import GoFV.Rules.Helpers.Sym
import GoFV.Opt.Pass
import Std.Data.HashMap

/-!
# The rewrite context

What a rule (and `applyRewrite`) can observe besides the function: the pass name, the fixed
`Config` values of the export, `Config.Types`, the type order; and the mutable state: the
function, the definition tables (rules create types with `PtrTo` and symbols with
`fe.StringData`) and `pendingLines` (`f.cachedLineStarts` as an `xposmap`).
-/

namespace GoFV.Rules

open GoFV.SSA

/-- Read-only context of a rewrite pass. -/
structure RwEnv where
  /-- `f.pass.name`. -/
  passName : String
  /-- `Config.arch`. -/
  arch : String
  ptrSize : Int
  regSize : Int
  bigEndian : Bool
  /-- `ctxt.Arch.Alignment`. -/
  archAlign : Int
  /-- `Config.Race`. -/
  race : Bool
  /-- `fe.Debug_checknil()`. -/
  debugNil : Bool
  /-- `ir.Syms.Zerobase.Name`. -/
  zerobase : GoStr
  /-- `rttype.Type` fields the export records (`config rttype.<name>`), by name. -/
  rtFields : Array (String × Sym.RtField)
  /-- `rttype.PtrType.OffsetOf("Elem")`. -/
  rtElemOff : Int
  /-- `Config.Types` fields and SSA pseudo-types by name. -/
  typs : Array (String × TypeRef)
  typeOrder : TypeOrder
  /-- The export file's final tables (`PassEnv.frontend`): symbols the frontend provides. -/
  frontend : Tables := {}
  deriving Inhabited

/-- Mutable state of a rewrite pass. -/
structure RwState where
  f : Func
  tables : Tables
  /-- `pendingLines` (`f.cachedLineStarts`), `none` when the function has none. -/
  pending : Option XPosMap
  /-- Frontend types copied into the tables: file number → table number. -/
  imported : Std.HashMap Nat Nat := {}
  /-- Number of value and block rules fired (statistics: `opt-proven-probe`). -/
  fired : Nat := 0
  /-- Frontend side effects so far (`PassOut.effects`). -/
  effects : Array GoFV.Opt.Effect := #[]

/-- The rewrite monad. Errors are Go's `Fatalf`/panics or constructs the port does not cover. -/
abbrev RwM := ReaderT RwEnv (EStateM String RwState)

namespace RwM

@[inline] def fail {α} (msg : String) : RwM α := throw msg

@[inline] def liftE {α} (x : Except String α) : RwM α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

@[inline] def getF : RwM Func := return (← get).f

/-- Apply a function update (keeps the state uniquely referenced). -/
@[inline] def modF (g : Func → Func) : RwM Unit :=
  modify fun s => { s with f := g s.f }

/-- Run a function update that also returns a result. -/
@[inline] def modFGet {α} (g : Func → Func × α) : RwM α :=
  modifyGet fun s => let (f, a) := g s.f; (a, { s with f })

/-- The value `id`. -/
@[inline] def val (id : ID) : RwM Value := do
  match (← get).f.value? id with
  | some v => return v
  | none => throw s!"v{id} not in the function"

@[inline] def blk (id : ID) : RwM Block := do
  match (← get).f.block? id with
  | some b => return b
  | none => throw s!"b{id} not in the function"

@[inline] def tables : RwM Tables := return (← get).tables

/-- Lift a type query. -/
@[inline] def ty {α} (q : Tables → Except String α) : RwM α := do liftE (q (← get).tables)

/-- `typ.<name>` or a pseudo-type (`Mem`, `Void`, …). -/
def typ (name : String) : RwM TypeRef := do
  match (← read).typs.find? (·.1 == name) with
  | some (_, t) => return t
  | none => throw s!"typs has no {name}"

end RwM

end GoFV.Rules
