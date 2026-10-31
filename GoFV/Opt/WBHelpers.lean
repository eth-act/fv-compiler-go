import GoFV.SSA.Alloc
import GoFV.Rules.Helpers.Types
import GoFV.Rules.Helpers.Sym
import Std.Data.HashMap.Basic

/-!
# writebarrier helpers (`writebarrier.go`)

Ports of the address classifiers and the known-zero analysis of `writebarrier.go` (go1.27.3):
`IsStackAddr`, `IsGlobalAddr`, `IsReadOnlyGlobalAddr`, `IsNewObject` (register-result form:
`f.ABIDefault == f.ABI1` with integer parameter registers, as on arm64), `ZeroRegion`,
`computeZeroMap`, `mightBeHeapPointer`, `mightContainHeapPointer`, `needwb`, `needWBsrc`,
`needWBdst`. Values are compared by ID (Go compares `*Value`s; a freed value's struct is reused
with its ID). The zero map is keyed by memory value ID, like Go's `map[ID]ZeroRegion`.
`Except.error` is Go's `Fatalf` or a failed type assertion.
-/

namespace GoFV.Opt.WB

open GoFV.SSA GoFV.SSA.Func

/-- Walk bound for pointer chains (each step follows an argument to an older value). -/
def fuel0 (f : Func) : Nat := f.valueTab.size + 1

/-- Skip `OffPtr`, `AddPtr`, `PtrIndex`, `Copy` (`IsStackAddr`/`IsGlobalAddr`). -/
def skipAddr (f : Func) : Nat → ID → ID
  | 0, v => v
  | n + 1, v =>
    let x := f.getV v
    match x.op with
    | .OffPtr | .AddPtr | .PtrIndex | .Copy => skipAddr f n x.args[0]!
    | _ => v

/-- Follow `OffPtr` links summing their offsets: the base and the offset. -/
def offBase (f : Func) : Nat → ID → Int → ID × Int
  | 0, v, off => (v, off)
  | n + 1, v, off =>
    let x := f.getV v
    if x.op == .OffPtr then offBase f n x.args[0]! (off + x.auxInt.toInt) else (v, off)

/-- `IsStackAddr(v)`. -/
def isStackAddr (f : Func) (v : ID) : Bool :=
  match (f.getV (skipAddr f (fuel0 f) v)).op with
  | .SP | .LocalAddr | .SelectNAddr | .GetCallerSP => true
  | _ => false

/-- `IsReadOnlyGlobalAddr(v)`. -/
def isReadOnlyGlobalAddr (f : Func) (tabs : Tables) (v : ID) : Except String Bool := do
  let x := f.getV v
  if x.op == .ConstNil then return true
  if x.op == .Addr && x.aux.isSome then
    return (← GoFV.Rules.Sym.lsym tabs x.aux).kind == "SRODATA"
  return false

/-- `IsGlobalAddr(v)`. -/
def isGlobalAddr (f : Func) (tabs : Tables) (v : ID) : Except String Bool := do
  let x := f.getV (skipAddr f (fuel0 f) v)
  if x.op == .Addr && (f.getV x.args[0]!).op == .SB then return true
  if x.op == .ConstNil then return true
  if x.op == .Load then return ← isReadOnlyGlobalAddr f tabs x.args[0]!
  return false

/-- `isNewObject(aux)`: the call's `Fn` is `runtime.newobject`. -/
def isNewObjectCall (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  return (← GoFV.Rules.Sym.callFnName tabs a) == some "runtime.newobject"

/-- `isSpecializedMalloc(aux)`. -/
def isSpecializedMalloc (tabs : Tables) (a : Option AuxRef) : Except String Bool := do
  match ← GoFV.Rules.Sym.callFnName tabs a with
  | none => return false
  | some n =>
    let n := n.bytes
    return GoFV.Rules.Sym.startsWith n "runtime.mallocgcSmallNoScanSC".toUTF8 ||
      GoFV.Rules.Sym.startsWith n "runtime.mallocgcSmallScanNoHeaderSC".toUTF8 ||
      GoFV.Rules.Sym.startsWith n "runtime.mallocgcTinySC".toUTF8

/-- `t.IsUnsafePtr()`. -/
def isUnsafePtr (tabs : Tables) (t : TypeRef) : Bool :=
  ((tabs.type? t).map (·.kind)) == some .UNSAFEPTR

/-- `IsNewObject(v, select1)` in the register-result form: the memory state at which the
object `v` points to is freshly allocated and zeroed. -/
def isNewObject (f : Func) (tabs : Tables) (select1 : Array (Option ID)) (v : ID) :
    Except String (Option ID) := do
  let x := f.getV v
  if x.op != .SelectN || x.auxInt != 0 then return none
  let some mem := (select1[x.args[0]!]?).join | return none
  let call := (f.getV mem).args[0]!
  let c := f.getV call
  if c.op != .StaticCall then return none
  let ok ← if ← isNewObjectCall tabs c.aux then pure true
    else if ← isSpecializedMalloc tabs c.aux then pure !(isUnsafePtr tabs x.type)
    else pure false
  if !ok then return none
  return if x.args[0]! == call then some mem else none

/-- `ZeroRegion`: `base` 0 is Go's nil. -/
structure ZeroRegion where
  base : ID := 0
  mask : UInt64 := 0
  deriving BEq, Inhabited

/-- `zeroes map[ID]ZeroRegion`. -/
abbrev ZeroMap := Std.HashMap ID ZeroRegion

/-- Go's `x << n` on `uint64` (0 for `n ≥ 64`). -/
@[inline] def shl (x : UInt64) (n : Int) : UInt64 :=
  if n ≥ 64 then 0 else x <<< n.toNat.toUInt64

/-- `v.MemoryArg()` for a store op (the last argument). -/
@[inline] def memArg (f : Func) (v : ID) : ID := (f.getV v).args.back!

/-- `f.computeZeroMap(select1)`. -/
def computeZeroMap (f : Func) (tabs : Tables) (ptrSize : Int) (localPkgRuntime : Bool)
    (select1 : Array (Option ID)) : Except String ZeroMap := do
  let mut zeroes : ZeroMap := {}
  -- new objects
  for b in f.blocks do
    for v in (f.getB b).values do
      if let some mem ← isNewObject f tabs select1 v then
        let t := (f.getV v).type
        if localPkgRuntime && isUnsafePtr tabs t then continue
        let esize ← GoFV.Rules.Ty.size tabs (← GoFV.Rules.Ty.elem tabs t)
        let nptr := min 64 (esize.tdiv ptrSize)
        zeroes := zeroes.insert mem { base := v, mask := shl 1 nptr - 1 }
  -- stores to those new objects; every round that changes the map changes an entry
  let mut done := false
  for _ in [0:65 * (f.valueTab.size + 1)] do
    let mut changed := false
    for b in f.blocks do
      for v in (f.getB b).values do
        let x := f.getV v
        if x.op != .Store then continue
        let some z0 := zeroes[memArg f v]? | continue
        let mut z := z0
        let t ← GoFV.Rules.Ty.ofAux tabs x.aux
        let mut size ← GoFV.Rules.Ty.size tabs t
        let (ptr, off0) := offBase f (fuel0 f) x.args[0]! 0
        let mut off := off0
        if ptr != z.base then continue
        let d := off.tmod ptrSize
        if d != 0 then
          off := off - d
          size := size + d
        let d := size.tmod ptrSize
        if d != 0 then size := size + (ptrSize - d)
        let minimum := max off 0
        let maximum := min (off + size) (64 * ptrSize)
        if minimum < maximum then
          for k in [0:((maximum - minimum + ptrSize - 1) / ptrSize).toNat] do
            let bit := (minimum + k * ptrSize).tdiv ptrSize
            z := { z with mask := z.mask &&& ~~~(shl 1 bit) }
        if z.mask == 0 then continue
        if (zeroes.getD v {}) != z then
          zeroes := zeroes.insert v z
          changed := true
    if !changed then
      done := true
      break
  if !done then throw "computeZeroMap: no fixpoint"
  return zeroes

/-- `mightBeHeapPointer(v)`. -/
def mightBeHeapPointer (f : Func) (tabs : Tables) (v : ID) : Except String Bool :=
  return !(← isGlobalAddr f tabs v)

/-- `mightContainHeapPointer(ptr, size, mem, zeroes)`. -/
def mightContainHeapPointer (f : Func) (tabs : Tables) (ptrSize : Int) (ptr : ID) (size : Int)
    (mem : ID) (zeroes : ZeroMap) : Except String Bool := do
  if ← isReadOnlyGlobalAddr f tabs ptr then return false
  let (ptr, off) := offBase f (fuel0 f) ptr 0
  if off.tmod ptrSize != 0 then return true
  if size.tmod ptrSize != 0 then throw s!"v{ptr}: unaligned pointer write"
  if off < 0 || off + size > 64 * ptrSize then return true
  let z := zeroes.getD mem {}
  if ptr != z.base then return true
  let m := shl (shl 1 (size.tdiv ptrSize) - 1) (off.tdiv ptrSize)
  return z.mask &&& m != m

/-- `needwb(v, zeroes)` for a `Store`/`Move`/`Zero` `v`. -/
def needwb (f : Func) (tabs : Tables) (ptrSize : Int) (v : ID) (zeroes : ZeroMap) :
    Except String Bool := do
  let x := f.getV v
  let t ← GoFV.Rules.Ty.ofAux tabs x.aux
  if !(← GoFV.Rules.Ty.hasPointers tabs t) then return false
  let dst := x.args[0]!
  if isStackAddr f dst then return false
  let size ← GoFV.Rules.Ty.size tabs t
  if ← mightContainHeapPointer f tabs ptrSize dst size (memArg f v) zeroes then return true
  match x.op with
  | .Store => if !(← mightBeHeapPointer f tabs x.args[1]!) then return false
  | .Zero => return false
  | .Move =>
    if !(← mightContainHeapPointer f tabs ptrSize x.args[1]! size x.args[2]! zeroes) then
      return false
  | _ => throw s!"v{v}: store op unknown"
  return true

/-- `needWBsrc(v)`. -/
def needWBsrc (f : Func) (tabs : Tables) (v : ID) : Except String Bool :=
  return !(← isGlobalAddr f tabs v)

/-- `needWBdst(ptr, mem, zeroes)`. -/
def needWBdst (f : Func) (ptrSize : Int) (ptr mem : ID) (zeroes : ZeroMap) : Bool :=
  let (ptr, off) := offBase f (fuel0 f) ptr 0
  if off.tmod ptrSize != 0 then true
  else if off < 0 || off ≥ 64 * ptrSize then true
  else
    let z := zeroes.getD mem {}
    if ptr != z.base then true
    else (z.mask >>> (off.tdiv ptrSize).toNat.toUInt64) &&& 1 == 0

end GoFV.Opt.WB
