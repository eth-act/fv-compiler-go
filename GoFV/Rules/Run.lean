import GoFV.Rules.Apply
import GoFV.Opt.Pass

/-!
# Rewrite passes

`rewritePass s removeDead` is a pass (`GoFV.Opt.Pass`) running `applyRewrite` with the rule set
`s`: `opt`/`middle opt`/`late opt` (generic rules), `divisible`, `divmod`. The rewrite context
comes from the export's fixed configuration.
-/

namespace GoFV.Rules

open GoFV.SSA GoFV.Opt

namespace RwEnv

private def word (e : PassEnv) (key : String) : Except String String :=
  match e.config? key with
  | some #[.word w] => .ok w
  | _ => .error s!"config {key}: missing or not a word"

private def str (e : PassEnv) (key : String) : Except String GoStr :=
  match e.config? key with
  | some #[.str s] => .ok s
  | _ => .error s!"config {key}: missing or not a string"

private def int (e : PassEnv) (key : String) : Except String Int := do
  let w ← word e key
  match w.toInt? with
  | some i => return i
  | none => throw s!"config {key}: not an integer"

/-- `rttype.<name> <offset>:<kind>:<size>`. -/
private def rtField (e : PassEnv) (name : String) : Except String (String × Sym.RtField) := do
  let w ← word e s!"rttype.{name}"
  match w.splitOn ":" with
  | [o, k, s] =>
    match o.toInt?, TypeKind.ofName? k, s.toInt? with
    | some o, some k, some s => return (name, { name, offset := o, kind := k, size := s })
    | _, _, _ => throw s!"config rttype.{name}: bad value {w}"
  | _ => throw s!"config rttype.{name}: bad value {w}"

/-- The rewrite context of a pass. -/
def ofPassEnv (e : PassEnv) : Except String RwEnv := do
  let fields ← ["Size_", "PtrBytes", "Hash", "Kind_", "GCData"].mapM (rtField e)
  let elem ← rtField e "PtrType.Elem"
  return {
    passName := e.passName
    arch := ← word e "arch"
    ptrSize := ← int e "ptrsize"
    regSize := ← int e "regsize"
    bigEndian := ← e.flag "bigendian"
    archAlign := ← int e "archalign"
    race := ← e.flag "race"
    debugNil := ← e.flag "debugnil"
    zerobase := ← str e "zerobase"
    rtFields := fields.toArray
    rtElemOff := elem.2.offset
    typs := e.typs
    typeOrder := e.typeOrder
    frontend := e.frontend
    ptrCache := e.ptrCache }

end RwEnv

/-- `rewritePass t removeDead` with the number of rules fired. -/
def rewritePassFired (t : Interp.Table) (removeDead : Bool) (env : PassEnv) (f : Func) :
    Except String (PassOut × Nat) := do
  let rw ← RwEnv.ofPassEnv env
  let st : RwState := { f, tables := env.tables, pending := XPosMap.ofCache f.cache.lineStarts }
  match (Apply.applyRewrite t removeDead).run rw |>.run st with
  | .ok _ s =>
    let f := s.f
    let f := { f with cache := { f.cache with lineStarts := s.pending.map (·.toCache) } }
    return ({ func := f, tables := s.tables, effects := s.effects, typeObjs := s.typeObjs }, s.fired)
  | .error e _ => throw e

/-- A pass running `applyRewrite` with the rule table `t`; `removeDead` is Go's
`removeDeadValues`. -/
def rewritePass (t : Interp.Table) (removeDead : Bool) : Pass := fun env f =>
  (·.1) <$> rewritePassFired t removeDead env f

end GoFV.Rules
