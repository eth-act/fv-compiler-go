import GoFV.Opt.Pass
import GoFV.SSA.ConstCache
import GoFV.Rules.Helpers.Types

/-!
# memcombine: state, configuration and value builders (`memcombine.go:88-128,757-841`)

The monad `M` threads the function and the definition tables (a widened store's `Aux` is the
`*types.Type` of its new value, which may need a new `type` aux). `splitPtr`/`BaseAddress` and
the builders `sizeType`, `truncate`, `zeroExtend`, `leftShift`, `rightShift`, `byteSwap` are
verbatim ports; `clobber` is `reset(OpInvalid)`.
-/

namespace GoFV.Opt.MemCombine

open GoFV.SSA

/-- What memcombine reads of `Config` and `types.Types`. -/
structure Cfg where
  regSize : Int64
  bigEndian : Bool
  /-- `arch == "S390X"`. -/
  s390x : Bool
  bswap64 : Bool
  bswap32 : Bool
  bswap16 : Bool
  bool : TypeRef
  u16 : TypeRef
  u32 : TypeRef
  u64 : TypeRef
  /-- `Type.Compare == CMPeq` (constant cache). -/
  sameType : TypeRef → TypeRef → Bool
  /-- Run `memcombineStores` after `memcombineLoads`. The checked pass (`memcombineChecked`)
  combines loads only (issue #35). -/
  stores : Bool := true

structure St where
  f : Func
  tabs : Tables

abbrev M := ReaderT Cfg (StateT St (Except String))

@[inline] def getF : M Func := return (← get).f
@[inline] def modF (g : Func → Func) : M Unit := modify fun s => { s with f := g s.f }
@[inline] def val (v : ID) : M Value := return (← getF).getV v
@[inline] def op (v : ID) : M Op := return (← val v).op
@[inline] def arg (v : ID) (i : Nat) : M ID := do
  match (← val v).args[i]? with
  | some a => return a
  | none => throw s!"v{v}: no argument {i}"

/-- `t.Size()` as Go `int64`. -/
def size (t : TypeRef) : M Int64 := do
  match GoFV.Rules.Ty.size (← get).tabs t with
  | .ok s => return Int64.ofInt s
  | .error e => throw e

/-- `v.Aux.(*types.Type).Size()`. -/
def auxSize (v : ID) : M Int64 := do
  match GoFV.Rules.Ty.ofAux (← get).tabs (← val v).aux with
  | .ok t => size t
  | .error e => throw e

/-- `typeToAux(t)`. -/
def typeAux (t : TypeRef) : M AuxRef := do
  let s ← get
  match GoFV.Rules.Ty.typeAux s.tabs t with
  | .ok (tabs, a) => set { s with tabs }; return a
  | .error e => throw e

/-- `c.haveByteSwap(size)`. -/
def haveByteSwap (n : Int64) : M Bool := do
  let c ← read
  match n.toInt with
  | 8 => return c.bswap64
  | 4 => return c.bswap32
  | 2 => return c.bswap16
  | _ => throw s!"bad size {n}"

/-- `BaseAddress{ptr, idx}` (`idx = none` is Go's nil). -/
structure BaseAddress where
  ptr : ID
  idx : Option ID
  deriving DecidableEq

/-- `splitPtr(ptr)`: the base address and the constant offset peeled off. -/
def splitPtr (f : Func) : Nat → ID → Option ID → Int64 → BaseAddress × Int64
  | 0, ptr, idx, off => (⟨ptr, idx⟩, off)
  | fuel + 1, ptr, idx, off =>
    let x := f.getV ptr
    if x.op == .OffPtr then splitPtr f fuel x.args[0]! idx (off + x.auxInt)
    else if x.op == .AddPtr then
      if idx.isSome then (⟨ptr, idx⟩, off) else
      let i := x.args[1]!
      let ix := f.getV i
      let isC (a : ID) := let o := (f.getV a).op; o == .Const32 || o == .Const64
      let (off, i) :=
        if ix.op == .Add32 || ix.op == .Add64 then
          if isC ix.args[0]! then (off + (f.getV ix.args[0]!).auxInt, ix.args[1]!)
          else if isC ix.args[1]! then (off + (f.getV ix.args[1]!).auxInt, ix.args[0]!)
          else (off, i)
        else (off, i)
      splitPtr f fuel x.args[0]! (some i) off
    else (⟨ptr, idx⟩, off)

/-- `splitPtr(ptr)`; every step follows an argument, so the number of values bounds it. -/
def split (ptr : ID) : M (BaseAddress × Int64) := do
  let f ← getF
  return splitPtr f (f.vidLast + 1) ptr none 0

/-- `b.NewValue{1,2}(pos, op, t, args...)`. -/
def newValue (b : ID) (pos : Pos) (o : Op) (t : TypeRef) (args : Array ID) : M ID := do
  let (f, v) := (← getF).newValueArgs b pos o t (args := args)
  modF fun _ => f
  return v

/-- `f.ConstInt64(types.Types[TUINT64], c)` and friends. -/
def constInt (o : Op) (t : TypeRef) (c : Int64) : M ID := do
  let (f, v) := (← getF).constVal (← read).sameType o t c true
  modF fun _ => f
  return v

/-- `clobber(v)`. -/
def clobber (v : ID) : M Unit := modF (·.resetValue v .Invalid)

/-- `sizeType(size)`. -/
def sizeType (n : Int64) : M TypeRef := do
  let c ← read
  match n.toInt with
  | 8 => return c.u64
  | 4 => return c.u32
  | 2 => return c.u16
  | _ => throw s!"bad size {n}"

/-- `truncate(b, pos, v, from, to)`. -/
def truncate (b : ID) (pos : Pos) (v : ID) (frm to : Int64) : M ID := do
  let c ← read
  match (frm * 10 + to).toInt with
  | 82 => newValue b pos .Trunc64to16 c.u16 #[v]
  | 84 => newValue b pos .Trunc64to32 c.u32 #[v]
  | 42 => newValue b pos .Trunc32to16 c.u16 #[v]
  | _ => throw s!"bad sizes {frm} {to}"

/-- `zeroExtend(b, pos, v, from, to)`. -/
def zeroExtend (b : ID) (pos : Pos) (v : ID) (frm to : Int64) : M ID := do
  let c ← read
  match (frm * 10 + to).toInt with
  | 24 => newValue b pos .ZeroExt16to32 c.u32 #[v]
  | 28 => newValue b pos .ZeroExt16to64 c.u64 #[v]
  | 48 => newValue b pos .ZeroExt32to64 c.u64 #[v]
  | _ => throw s!"bad sizes {frm} {to}"

/-- `leftShift(b, pos, v, shift)` (`rightShift` with `right`). -/
def shiftBy (right : Bool) (b : ID) (pos : Pos) (v : ID) (shift : Int64) : M ID := do
  let s ← constInt .Const64 (← read).u64 shift
  let t := (← val v).type
  let o ← match (← size t).toInt with
    | 8 => pure (if right then Op.Rsh64Ux64 else .Lsh64x64)
    | 4 => pure (if right then Op.Rsh32Ux64 else .Lsh32x64)
    | 2 => pure (if right then Op.Rsh16Ux64 else .Lsh16x64)
    | n => throw s!"bad size {n}"
  newValue b pos o t #[v, s]

/-- `byteSwap(b, pos, v)`. -/
def byteSwap (b : ID) (pos : Pos) (v : ID) : M ID := do
  let t := (← val v).type
  let o ← match (← size t).toInt with
    | 8 => pure Op.Bswap64
    | 4 => pure .Bswap32
    | 2 => pure .Bswap16
    | n => throw s!"bad size {n}"
  newValue b pos o t #[v]

end GoFV.Opt.MemCombine
