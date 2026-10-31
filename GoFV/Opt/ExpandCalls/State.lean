import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.ConstCache
import GoFV.SSA.ABI
import GoFV.SSA.TypeNew
import GoFV.Rules.Helpers.Types
import Std.Data.HashMap.Basic

/-!
# expand calls: state and helpers

`expandState` (`expand_calls.go:898`), `registerCursor` (`:810`), `offsetFrom` (`:918`),
`invalidateRecursively` (`:973`, `value.go:400`) and the type/aux/value accessors the
rewriting functions share. linux/arm64 only: `RegSize` 8, little endian (the `Int64Hi/Lo`
paths of 32-bit targets are reported as errors).
-/

namespace GoFV.Opt.ExpandCalls

open GoFV.SSA

/-- What the pass reads besides the function (fixed for one run). -/
structure Ctx where
  /-- `x.sp`. -/
  sp : ID
  ptrSize : Int
  fixedFrameSize : Int
  /-- `abi.ABIConfig` by `Which()` (`config abi0`, `abi1`). -/
  abiConfigs : Array ABIConfig
  /-- `types.TypeMem`, `types.TypeResultMem` and the `Config.Types` entries used. -/
  mem : TypeRef
  resultMem : TypeRef
  int : TypeRef
  uintptr : TypeRef
  bytePtr : TypeRef
  unsafePtr : TypeRef
  float32 : TypeRef
  float64 : TypeRef
  order : TypeOrder
  /-- New types and aux values get numbers `≥` these (past the tables and `typeorder`). -/
  typeFloor : Nat
  auxFloor : Nat

/-- `selKey` (`:891`) with the container's ID and the type's number. -/
structure SelKey where
  src : ID
  off : Int64
  size : Int
  typ : TypeRef
  deriving BEq, Hashable

structure St where
  f : Func
  tabs : Tables
  wideSelects : Std.HashMap ID ID := {}
  commonSelectors : Std.HashMap SelKey ID := {}
  commonArgs : Std.HashMap SelKey ID := {}
  memForCall : Std.HashMap ID ID := {}
  /-- `*rc.regValues` of the call or exit being rewritten. -/
  regValues : Array ID := #[]

abbrev M := ReaderT Ctx (StateT St (Except String))

/-! ## Function access -/

@[inline] def getF : M Func := return (← get).f
@[inline] def setF (f : Func) : M Unit := modify fun s => { s with f }
@[inline] def modF (g : Func → Func) : M Unit := modify fun s => { s with f := g s.f }

def val (v : ID) : M Value := do
  match (← getF).value? v with
  | some x => return x
  | none => throw s!"value v{v} not in the function"

@[inline] def modV (v : ID) (g : Value → Value) : M Unit := modF (·.modV v g)

/-- `b.NewValue*(pos, op, t, auxint, aux, args...)`. -/
def newV (b : ID) (pos : Pos) (op : Op) (t : TypeRef) (auxInt : Int64 := 0)
    (aux : Option AuxRef := none) (args : Array ID := #[]) : M ID := do
  let (f, v) := (← getF).newValueArgs b pos op t auxInt aux args
  setF f
  return v

/-! ## Types -/

def tdef (t : TypeRef) : M TypeDef := do
  match (← get).tabs.type? t with
  | some d => return d
  | none => throw s!"type t{t} not defined"

def tsize (t : TypeRef) : M Int := do
  match (← tdef t).size with
  | some s => return s
  | none => throw s!"type t{t}: size not calculated"

def talign (t : TypeRef) : M Int := do
  match (← tdef t).align with
  | some s => return s
  | none => throw s!"type t{t}: alignment not calculated"

def telem (t : TypeRef) : M TypeRef := do
  match (← tdef t).tail with
  | .elem e | .array e _ => return e
  | _ => throw s!"type t{t}: Elem of a type without element"

/-- `types.NewPtr(t)`. -/
def ptrTo (t : TypeRef) : M TypeRef := do
  let c ← read
  let s ← get
  let (p, tabs) ← s.tabs.ptrTo c.typeFloor c.ptrSize t
  set { s with tabs }
  return p

/-- `types.NewResults(ts)`. -/
def newResults (ts : Array TypeRef) : M TypeRef := do
  let c ← read
  let s ← get
  let (r, tabs) ← s.tabs.newResults c.typeFloor c.mem c.resultMem ts
  set { s with tabs }
  return r

/-- `t` as an aux value (`NewValue*A(…, t, …)`, Go's `typeToAux`). -/
def typeAux (t : TypeRef) : M AuxRef := do
  let s ← get
  let (tabs, a) ← GoFV.Rules.Ty.typeAux s.tabs t
  set { s with tabs }
  return a

def canSSA (t : TypeRef) : M Bool := do
  GoFV.SSA.canSSA (← get).tabs (← read).ptrSize typeFuel t

def regTypes : M RegTypes := do
  let c ← read
  return { bytePtr := c.bytePtr, int := c.int, unsafePtr := c.unsafePtr, float32 := c.float32,
           float64 := c.float64 }

/-! ## Aux values -/

def auxDef (a : AuxRef) : M AuxDef := do
  match (← get).tabs.aux? a with
  | some d => return d
  | none => throw s!"aux a{a} not defined"

/-- The `abiInfo` of a call aux, with its `ABIConfig`. -/
def callABI (aux : Option AuxRef) : M (CallABI × ABIConfig) := do
  let some a := aux | throw "call without aux"
  match (← auxDef a).kind with
  | .call _ (some info) =>
    match (← read).abiConfigs[info.abi]? with
    | some c => return (info, c)
    | none => throw s!"no ABI config {info.abi}"
  | _ => throw s!"aux a{a} is not an AuxCall with ABI info"

/-- A fresh `&AuxNameOffset{name, off}` (`:651`). -/
def newNameOffset (name : AuxRef) (off : Int64) : M AuxRef := do
  let sym ← match (← auxDef name).kind with
    | .name sym .. => pure sym
    | _ => throw s!"aux a{name} is not an ir.Name"
  let c ← read
  let s ← get
  let n := max c.auxFloor s.tabs.auxes.size
  let fmt := sym ++ GoStr.ofString ("+" ++ toString off.toInt)
  set { s with tabs := s.tabs.add (.aux n { fmt, kind := .nameOff name off.toInt }) }
  return n

/-! ## `registerCursor` -/

/-- `registerCursor` (`:810`); `regValues` is `St.regValues` when `collect`. -/
structure Cursor where
  storeDest : Option ID
  storeOffset : Int64
  regs : Array Nat
  nextSlice : Nat
  config : ABIConfig
  collect : Bool

/-- `rc.init(regs, info, result, storeDest, storeOffset)`. -/
def Cursor.init (regs : Array Nat) (config : ABIConfig) (collect : Bool) (storeDest : Option ID)
    (storeOffset : Int64) : Cursor :=
  { storeDest, storeOffset, regs, nextSlice := 0, config, collect }

@[inline] def Cursor.hasRegs (c : Cursor) : Bool := !c.regs.isEmpty

/-- `types.RoundUp(o, r)`: `(o + r - 1) &^ (r - 1)`. -/
@[inline] def roundUp (o r : Int64) : Int64 := (o + r - 1) &&& ~~~(r - 1)

/-- `rc.next(t)`: the aligned cursor, and the advanced one. -/
def Cursor.next (c : Cursor) (t : TypeRef) : M (Cursor × Cursor) := do
  let al := Int64.ofInt (← talign t)
  let sz := Int64.ofInt (← tsize t)
  let c := { c with storeOffset := roundUp c.storeOffset al }
  let rc := c
  let c := { c with storeOffset := roundUp (c.storeOffset + sz) al }
  if c.nextSlice < c.regs.size then
    let w ← numParamRegs (← get).tabs t
    return (rc, { c with nextSlice := (c.nextSlice + w) % 256 })
  return (rc, c)

/-- `rc.addArg(v)`. -/
def Cursor.addArg (c : Cursor) (v : ID) : M Unit := do
  if !c.collect then throw "registerCursor.addArg without regValues"
  modify fun s => { s with regValues := s.regValues.push v }

/-- `rc.ArgOpAndRegisterFor()`. -/
def Cursor.argOpAndRegisterFor (c : Cursor) : M (Op × Int64) := do
  match c.regs[c.nextSlice]? with
  | some r => return GoFV.SSA.argOpAndRegisterFor c.config r
  | none => throw "registerCursor: register slice out of range"

/-! ## `offsetFrom`, `invalidateRecursively` -/

def isPtrKind (t : TypeRef) : M Bool := return (← tdef t).kind == .PTR

/-- `x.offsetFrom(b, from, offset, pt)` (`:918`). -/
def offsetFrom (b src : ID) (offset : Int64) (pt : TypeRef) : M ID := do
  let ft := (← val src).type
  if offset == 0 then
    if ft == pt then return src
    let fk := (← tdef ft).kind
    if (fk == .PTR || fk == .UNSAFEPTR) && (← isPtrKind pt) then return src
  let mut src := src
  let mut offset := offset
  for _ in [0:(← getF).valueTab.size + 1] do
    let x ← val src
    if x.op != .OffPtr then break
    offset := offset + x.auxInt
    src := x.args[0]!
  let c ← read
  if src == c.sp then
    let s ← get
    let (f, v) := s.f.constOffPtrSP (s.tabs.typeEq c.order typeFuel) pt offset c.sp
    setF f
    return v
  let pos := (← val src).pos.withNotStmt
  newV b pos .OffPtr pt offset none #[src]

/-- `v.invalidateRecursively()` (`value.go:400`): `OpInvalid`, arguments whose use count drops
to zero recursively; nothing is freed. -/
def invalidateRec : Nat → ID → M Unit
  | 0, _ => throw "invalidateRecursively: too deep"
  | fuel + 1, v => do
    modF (·.unCache v)
    modV v fun x => { x with op := .Invalid }
    for a in (← val v).args do
      let x ← val a
      if x.uses == 0 then throw s!"invalidateRecursively: v{a} would get negative uses"
      modF (·.decUses a)
      if x.uses == 1 then invalidateRec fuel a
    modV v fun x => { x with args := #[], auxInt := 0, aux := none }

def invalidateRecursively (v : ID) : M Unit := do
  invalidateRec ((← getF).valueTab.size + 1) v

end GoFV.Opt.ExpandCalls
