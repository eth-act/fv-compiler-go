import GoFV.SSA.Alloc
import GoFV.Rules.Helpers.Types

/-!
# Pointer and value-shape helpers (`rewrite.go`)

`isSamePtr`, `isStackPtr`, `disjoint` (with `disjointTypes`), `isNonNegative`, `isConstZero`,
`isVolatile` (`writebarrier.go`), `isDirectAndComparableType`/`Iface`. They walk argument chains
of the function graph; the walks are bounded by `fuel` (Go recurses without bound, but the
chains are acyclic on every function the compiler accepts).
-/

namespace GoFV.Rules.Ptr

open GoFV.SSA

/-- Default walk bound. -/
def fuel0 : Nat := 10000

@[inline] def arg (f : Func) (v : ID) (i : Nat) : ID := (f.getV v).args[i]!

/-- Follow `OffPtr [0]` links. -/
def skipOff0 (f : Func) : Nat → ID → ID
  | 0, p => p
  | n + 1, p =>
    let x := f.getV p
    if x.op == .OffPtr && x.auxInt == 0 then skipOff0 f n x.args[0]! else p

/-- `isSamePtr(p1, p2)`. -/
def isSamePtr (f : Func) : Nat → ID → ID → Bool
  | 0, _, _ => false
  | n + 1, p1, p2 =>
    if p1 == p2 then true else
    let (p1, p2, ok) :=
      if (f.getV p1).op != (f.getV p2).op then
        let p1 := skipOff0 f fuel0 p1
        let p2 := skipOff0 f fuel0 p2
        (p1, p2, p1 == p2 || (f.getV p1).op == (f.getV p2).op)
      else (p1, p2, true)
    if p1 == p2 then true else
    if !ok then false else
    let x1 := f.getV p1
    let x2 := f.getV p2
    match x1.op with
    | .OffPtr => x1.auxInt == x2.auxInt && isSamePtr f n x1.args[0]! x2.args[0]!
    | .Addr | .LocalAddr => x1.aux == x2.aux
    | .AddPtr => x1.args[1]! == x2.args[1]! && isSamePtr f n x1.args[0]! x2.args[0]!
    | _ => false

/-- `isStackPtr(v)`. -/
def isStackPtr (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, v =>
    let x := f.getV v
    if x.op == .OffPtr || x.op == .AddPtr then isStackPtr f n x.args[0]! else
    x.op == .SP || x.op == .LocalAddr

/-- `isVolatile(v)` (`writebarrier.go`). -/
def isVolatile (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, v =>
    let x := f.getV v
    match x.op with
    | .OffPtr | .AddPtr | .PtrIndex | .Copy | .SelectNAddr => isVolatile f n x.args[0]!
    | o => o == .SP

/-- `disjointTypes(t1, t2)`. -/
def disjointTypes (tabs : Tables) (ptrSize : Int) (t1 t2 : TypeRef) : Except String Bool := do
  if (← Ty.isKind .UNSAFEPTR tabs t1) || (← Ty.isKind .UNSAFEPTR tabs t2) then return false
  if !(← Ty.isKind .PTR tabs t1) || !(← Ty.isKind .PTR tabs t2) then return false
  let t1 ← Ty.elem tabs t1
  let t2 ← Ty.elem tabs t2
  if (← Ty.notInHeap tabs t1) || (← Ty.notInHeap tabs t2) then return false
  let isPtrShaped (t : TypeRef) : Except String Bool := do
    -- `int(t.Size()) == types.PtrSize && t.HasPointers()`, short-circuit as Go
    if (← Ty.size tabs t) == ptrSize then Ty.hasPointers tabs t else return false
  if (← isPtrShaped t1) && !(← Ty.hasPointers tabs t2) then return true
  if (← isPtrShaped t2) && !(← Ty.hasPointers tabs t1) then return true
  return false

/-- `baseAndOffset(ptr)` of `disjoint`. -/
def baseAndOffset (f : Func) : Nat → ID → Int → ID × Int
  | 0, p, off => (p, off)
  | n + 1, p, off =>
    let x := f.getV p
    if x.op == .OffPtr then baseAndOffset f n x.args[0]! (off + x.auxInt.toInt) else
    if x.op.nilCheck then (x.args[0]!, off) else (p, off)

/-- `overlap(offset1, size1, offset2, size2)`. -/
@[inline] def overlap (o1 s1 o2 s2 : Int) : Bool :=
  if o1 ≥ o2 && o2 + s2 > o1 then true
  else if o2 ≥ o1 && o1 + s1 > o2 then true
  else false

/-- `disjoint(p1, n1, p2, n2)`. Sizes are Go `int64`s. -/
def disjoint (f : Func) (tabs : Tables) (ptrSize : Int) (p1 : ID) (n1 : Int) (p2 : ID)
    (n2 : Int) : Except String Bool := do
  if n1 == 0 || n2 == 0 then return true
  if p1 == p2 then return false
  if ← disjointTypes tabs ptrSize (f.getV p1).type (f.getV p2).type then return true
  let (p1, off1) := baseAndOffset f fuel0 p1 0
  let (p2, off2) := baseAndOffset f fuel0 p2 0
  if isSamePtr f fuel0 p1 p2 then
    return !overlap off1 n1 off2 n2
  let o1 := (f.getV p1).op
  let o2 := (f.getV p2).op
  match o1 with
  | .Addr | .LocalAddr =>
    if o2 == .Addr || o2 == .LocalAddr || o2 == .SP then return true
    return (o2 == .Arg || o2 == .ArgIntReg) && (f.getV (arg f p1 0)).op == .SP
  | .Arg | .ArgIntReg =>
    return o2 == .SP || o2 == .LocalAddr
  | .SP =>
    return o2 == .Addr || o2 == .LocalAddr || o2 == .Arg || o2 == .ArgIntReg || o2 == .SP
  | _ => return false

/-- `isNonNegative(v)`. -/
def isNonNegative (f : Func) (tabs : Tables) : Nat → ID → Except String Bool
  | 0, _ => .ok false
  | n + 1, v => do
    let x := f.getV v
    if !(← Ty.isInteger tabs x.type) then throw s!"isNonNegative bad type: v{v}"
    let c := x.auxInt.toInt
    match x.op with
    | .Const64 => return c ≥ 0
    | .Const32 => return x.auxInt.toInt32.toInt ≥ 0
    | .Const16 => return x.auxInt.toInt16.toInt ≥ 0
    | .Const8 => return x.auxInt.toInt8.toInt ≥ 0
    | .StringLen | .SliceLen | .SliceCap
    | .ZeroExt8to64 | .ZeroExt16to64 | .ZeroExt32to64
    | .ZeroExt8to32 | .ZeroExt16to32 | .ZeroExt8to16
    | .Ctz64 | .Ctz32 | .Ctz16 | .Ctz8
    | .Ctz64NonZero | .Ctz32NonZero | .Ctz16NonZero | .Ctz8NonZero
    | .BitLen64 | .BitLen32 | .BitLen16 | .BitLen8 => return true
    | .Rsh64Ux64 | .Rsh32Ux64 =>
      let by_ := f.getV x.args[1]!
      return by_.op == .Const64 && by_.auxInt > 0
    | .Rsh64x64 | .Rsh32x64 | .Rsh8x64 | .Rsh16x64 | .Rsh32x32 | .Rsh64x32
    | .SignExt32to64 | .SignExt16to64 | .SignExt8to64 | .SignExt16to32 | .SignExt8to32 =>
      isNonNegative f tabs n x.args[0]!
    | .And64 | .And32 | .And16 | .And8 =>
      if ← isNonNegative f tabs n x.args[0]! then return true
      isNonNegative f tabs n x.args[1]!
    | .Mod64 | .Mod32 | .Mod16 | .Mod8 | .Div64 | .Div32 | .Div16 | .Div8
    | .Or64 | .Or32 | .Or16 | .Or8 | .Xor64 | .Xor32 | .Xor16 | .Xor8 =>
      if !(← isNonNegative f tabs n x.args[0]!) then return false
      isNonNegative f tabs n x.args[1]!
    | _ => return false

/-- `isConstZero(v)`. -/
def isConstZero (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, v =>
    let x := f.getV v
    match x.op with
    | .ConstNil => true
    | .Const64 | .Const32 | .Const16 | .Const8 | .ConstBool | .Const32F | .Const64F =>
      x.auxInt == 0
    | .StringMake | .IMake | .ComplexMake =>
      isConstZero f n x.args[0]! && isConstZero f n x.args[1]!
    | .SliceMake =>
      isConstZero f n x.args[0]! && isConstZero f n x.args[1]! && isConstZero f n x.args[2]!
    | .StringPtr | .StringLen | .SlicePtr | .SliceLen | .SliceCap | .ITab | .IData
    | .ComplexReal | .ComplexImag => isConstZero f n x.args[0]!
    | _ => false

end GoFV.Rules.Ptr
