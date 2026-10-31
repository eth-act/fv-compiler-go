import GoFV.SSA.Alloc

/-!
# Constant cache

`f.constVal` and the `f.Const*` constructors (`func.go:663-760`, `docs/PASSES.md` §1.2): a
cached value with the same op and a `Type.Compare`-equal type is reused from the line
`f.constants[c]` (scanned in slice order); otherwise a new value is created at the end of
`f.Entry.Values` with `src.NoXPos` and appended to that line. Removal (`unCache`) and the magic
keys are in `GoFV.SSA.Alloc`, because `reset` and `freeValue` need them.

`sameType` is `Type.Compare(a, b) == CMPeq` (rank equality in the export's `typeorder`, see
`GoFV.SSA.TypeCmp`); it is a parameter so this module does not depend on the type tables.
-/

namespace GoFV.SSA.Func

/-- Append `v` to cache line `k`, inserting the line in key order if it is new. -/
def cacheAppend (f : Func) (k : Int64) (v : ID) : Func :=
  match f.constLine? k with
  | some li => { f with consts := f.consts.modify li fun (k, vs) => (k, vs.push v) }
  | none =>
    let pos := (f.consts.findIdx? (·.1 > k)).getD f.consts.size
    { f with consts := f.consts.insertIdx! pos (k, #[v]) }

/-- `f.constVal(op, t, c, setAuxInt)`. -/
def constVal (f : Func) (sameType : TypeRef → TypeRef → Bool) (op : Op) (t : TypeRef)
    (c : Int64) (setAuxInt : Bool) : Func × ID :=
  let line := match f.constLine? c with
    | some li => f.consts[li]!.2
    | none => #[]
  match line.find? (fun v => let x := f.getV v; x.op == op && sameType x.type t) with
  | some v => (f, v)
  | none =>
    let (f, v) := f.newValueArgs f.entry Pos.none op t (if setAuxInt then c else 0)
    (f.cacheAppend c v, v)

/-- `f.ConstBool(t, c)`. -/
def constBool (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Bool) : Func × ID :=
  f.constVal eq .ConstBool t (if c then 1 else 0) true
/-- `f.ConstInt8(t, c)`. -/
def constInt8 (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Int8) : Func × ID :=
  f.constVal eq .Const8 t c.toInt64 true
/-- `f.ConstInt16(t, c)`. -/
def constInt16 (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Int16) : Func × ID :=
  f.constVal eq .Const16 t c.toInt64 true
/-- `f.ConstInt32(t, c)`. -/
def constInt32 (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Int32) : Func × ID :=
  f.constVal eq .Const32 t c.toInt64 true
/-- `f.ConstInt64(t, c)`. -/
def constInt64 (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Int64) : Func × ID :=
  f.constVal eq .Const64 t c true
/-- `f.ConstFloat32(t, c)`, with `c` given as the bits of a `float64` that is exactly a
`float32` (`math.Float64bits(float64(float32(c)))`, computed by the caller). -/
def constFloat32Bits (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (bits : Int64) :
    Func × ID :=
  f.constVal eq .Const32F t bits true
/-- `f.ConstFloat64(t, c)`, with `c` given as `math.Float64bits(c)`. -/
def constFloat64Bits (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (bits : Int64) :
    Func × ID :=
  f.constVal eq .Const64F t bits true
/-- `f.ConstSlice(t)`. -/
def constSlice (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) : Func × ID :=
  f.constVal eq .ConstSlice t constSliceMagic false
/-- `f.ConstInterface(t)`. -/
def constInterface (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) : Func × ID :=
  f.constVal eq .ConstInterface t constInterfaceMagic false
/-- `f.ConstNil(t)`. -/
def constNil (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) : Func × ID :=
  f.constVal eq .ConstNil t constNilMagic false
/-- `f.ConstEmptyString(t)`: `emptyAux` is the aux number of `StringToAux("")` (a `stringAux`,
compared by value). The aux is set on the returned value whether or not it was cached. -/
def constEmptyString (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef)
    (emptyAux : AuxRef) : Func × ID :=
  let (f, v) := f.constVal eq .ConstString t constEmptyStringMagic false
  (f.modV v fun x => { x with aux := some emptyAux }, v)
/-- `f.ConstOffPtrSP(t, c, sp)`. -/
def constOffPtrSP (f : Func) (eq : TypeRef → TypeRef → Bool) (t : TypeRef) (c : Int64)
    (sp : ID) : Func × ID :=
  let (f, v) := f.constVal eq .OffPtr t c true
  if (f.getV v).args.isEmpty then (f.addArg v sp, v) else (f, v)

end GoFV.SSA.Func
