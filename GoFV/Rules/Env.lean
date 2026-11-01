import GoFV.SSA.Alloc
import GoFV.SSA.TypeCmp
import GoFV.SSA.XPosMap
import GoFV.Rules.Helpers.Sym
import GoFV.Opt.Pass
import GoFV.Rules.GoVal
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
  /-- `PassEnv.ptrCache`: whether `t.PtrTo()` returns a shared object. -/
  ptrCache : TypeRef → Bool := fun _ => false
  deriving Inhabited

/-- One step of a rewrite pass, as the rewrite validator replays it (`GoFV.Opt.RewriteCheck`,
issue #113). -/
inductive RwEvent where
  /-- Value rule `rule` (its index in `v`'s op row of the table) fired at `v` with bindings
  `binds`; `defs`: `v` and then the result's nodes in node order (`Result.build`; empty
  otherwise), as built. -/
  | rule (v : ID) (rule : Nat) (binds : Array GVal) (defs : Array Value)
  /-- Argument `i` of `v` replaced by `src`, the source of the copy it was. -/
  | copyArg (v : ID) (i : Nat) (src : ID)
  /-- Control `i` of block `b` replaced by `c`, the argument of the copy it was. -/
  | control (b : ID) (i : Nat) (c : ID)
  /-- The phi `v` became a copy (`phielimValue`); `def` is its new definition. -/
  | phielim (v : ID) («def» : Value)
  /-- Block rule `rule` (its index in `b`'s kind row of the table) fired at `b`; `ctrls`: the
  block's controls after it. -/
  | blockRule (b : ID) (rule : Nat) (ctrls : Array ID)

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
  /-- Type objects of the values made so far (`PassOut.typeObjs`). -/
  typeObjs : Array (ID × GoFV.Opt.TypeObj) := #[]
  /-- The steps taken, if recorded (`some`). -/
  log : Option (Array RwEvent) := none

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

/-- Record a step if the log is on (`RwState.log`). -/
@[inline] def logEv (e : Unit → RwEvent) : RwM Unit :=
  modify fun s =>
    let l := s.log
    let s := { s with log := none }
    match l with
    | some l => { s with log := some (l.push (e ())) }
    | none => s

end RwM

end GoFV.Rules
