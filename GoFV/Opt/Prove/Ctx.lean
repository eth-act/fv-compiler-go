import GoFV.Opt.Pass
import GoFV.Opt.CanCondSelect
import GoFV.SSA.Alloc

/-!
# prove: what the pass reads besides the function

`Ctx` is built once per run from the `PassEnv`: per type number the `*types.Type` facts prove
asks (`Size`, `IsBoolean`, `IsInteger`, `IsSigned`, `IsPtrShaped`, the element size of slices),
and the `Config` fields (`arch`, `PtrSize`, `RegSize`, `haveCondSelect`), `types.Types[TBOOL]`
and the type order (the constant cache's `Type.Compare`). Also the value predicates of
`prove.go` that only look at ops and arguments (`isConstDelta`, `isCleanExt`).
-/

namespace GoFV.Opt.Prove

open GoFV.SSA

/-- The facts prove reads about one type. -/
structure TyInfo where
  /-- `t.Size()` (`BADWIDTH` for an uncalculated `TSSA` type, as Go); `none` if the export has
  `?` for another type (never calculated). -/
  size? : Option Int := none
  isBool : Bool := false
  isInteger : Bool := false
  isSigned : Bool := false
  isPtrShaped : Bool := false
  /-- `t.Elem().Size()` for slices (`none` if not a slice or not calculated). -/
  elemSize? : Option Int := none
  deriving Inhabited

structure Ctx where
  ty : Array TyInfo
  tables : Tables
  typeOrder : TypeOrder
  arch : String
  ptrSize : Int
  regSize : Int
  haveCondSelect : Bool
  /-- `types.Types[types.TBOOL]`. -/
  boolType : TypeRef
  deriving Inhabited

namespace Ctx

def tyInfo (tabs : Tables) (t : TypeRef) : TyInfo :=
  match tabs.type? t with
  | none => {}
  | some d =>
    let elemSize? := match d.kind, d.tail with
      | .SLICE, .elem e => (tabs.type? e).bind (·.size)
      | _, _ => none
    let size? := match d.size with
      | some s => some s
      | none => if d.kind == .SSA then some GoFV.Rules.Ty.badWidth else none
    { size?, isBool := d.kind == .BOOL,
      isInteger := GoFV.Rules.Ty.isIntegerKind d.kind,
      isSigned := GoFV.Rules.Ty.isSignedKind d.kind,
      isPtrShaped := GoFV.Rules.Ty.isPtrShapedKind d.kind, elemSize? }

def configInt (env : PassEnv) (key : String) : Except String Int :=
  match env.config? key with
  | some #[.word w] => match decInt? w with
    | some i => pure i
    | none => throw s!"config {key}: not an integer"
  | _ => throw s!"config {key}: missing"

/-- Build the context of a run. -/
def ofEnv (env : PassEnv) : Except String Ctx := do
  let arch ← match env.config? "arch" with
    | some #[.word w] => pure w
    | _ => throw "config arch: missing"
  let some boolType := env.typ? "Bool" | throw "typs: no Bool"
  let ty := (Array.range env.tables.types.size).map (tyInfo env.tables)
  return { ty, tables := env.tables, typeOrder := env.typeOrder, arch,
           ptrSize := ← configInt env "ptrsize", regSize := ← configInt env "regsize",
           haveCondSelect := ← env.flag "havecondselect", boolType }

@[inline] def info (cx : Ctx) (t : TypeRef) : TyInfo := cx.ty[t]?.getD {}
/-- `t.Size()` (0 for an uncalculated size; `Prove.checkSizes` rejects those up front). -/
@[inline] def size (cx : Ctx) (t : TypeRef) : Int := ((cx.info t).size?).getD 0
@[inline] def isBool (cx : Ctx) (t : TypeRef) : Bool := (cx.info t).isBool
@[inline] def isInteger (cx : Ctx) (t : TypeRef) : Bool := (cx.info t).isInteger
@[inline] def isSigned (cx : Ctx) (t : TypeRef) : Bool := (cx.info t).isSigned
@[inline] def isPtrShaped (cx : Ctx) (t : TypeRef) : Bool := (cx.info t).isPtrShaped
/-- `uint(t.Size()) * 8`. -/
@[inline] def bits (cx : Ctx) (t : TypeRef) : Nat := (cx.size t).toNat * 8
/-- `Type.Compare(a, b) == CMPeq`. -/
@[inline] def sameType (cx : Ctx) (a b : TypeRef) : Bool := cx.typeOrder.eq a b

end Ctx

/-! ## Value predicates -/

/-- `isConstDelta(v)`: `v` is `w + delta` (signed) with a constant `delta`. -/
def isConstDelta (f : Func) (v : ID) : Option (ID × Int64) :=
  let x := f.getV v
  let cop : Op := match x.op with
    | .Add32 | .Sub32 => .Const32
    | .Add16 | .Sub16 => .Const16
    | .Add8 | .Sub8 => .Const8
    | _ => .Const64
  match x.op with
  | .Add64 | .Add32 | .Add16 | .Add8 =>
    let a0 := f.getV x.args[0]!
    let a1 := f.getV x.args[1]!
    if a0.op == cop then some (x.args[1]!, a0.auxInt)
    else if a1.op == cop then some (x.args[0]!, a1.auxInt)
    else none
  | .Sub64 | .Sub32 | .Sub16 | .Sub8 =>
    let a1 := f.getV x.args[1]!
    if a1.op == cop && a1.auxInt != -a1.auxInt then some (x.args[0]!, -a1.auxInt) else none
  | _ => none

/-- `isCleanExt(v)`: a value-preserving sign or zero extension. -/
def isCleanExt (cx : Ctx) (f : Func) (v : ID) : Bool :=
  let x := f.getV v
  match x.op with
  | .SignExt8to16 | .SignExt8to32 | .SignExt8to64 | .SignExt16to32 | .SignExt16to64
  | .SignExt32to64 => cx.isSigned (f.getV x.args[0]!).type && cx.isSigned x.type
  | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64 | .ZeroExt16to32 | .ZeroExt16to64
  | .ZeroExt32to64 => !cx.isSigned (f.getV x.args[0]!).type
  | _ => false

end GoFV.Opt.Prove
