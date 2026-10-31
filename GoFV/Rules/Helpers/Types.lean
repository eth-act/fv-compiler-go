import GoFV.SSA.Export

/-!
# `*types.Type` queries used by the rules

The `types.Type` methods the rule expressions and `rewrite.go` helpers call
(docs/contracts/rules.md, helper inventory), over the exported type tables. Types are table
numbers (`TypeRef`); equal numbers are identical types (`docs/contracts/export.md`). A size the
compiler never calculated (`?`) is an error: Go would compute it, the export cannot.
-/

namespace GoFV.Rules.Ty

open GoFV.SSA

/-- The definition of `t`. -/
@[inline] def get (tabs : Tables) (t : TypeRef) : Except String TypeDef :=
  match tabs.type? t with
  | some d => .ok d
  | none => .error s!"type t{t} not defined"

def kind (tabs : Tables) (t : TypeRef) : Except String TypeKind := return (← get tabs t).kind

/-- `t.Size()`. -/
def size (tabs : Tables) (t : TypeRef) : Except String Int := do
  match (← get tabs t).size with
  | some s => return s
  | none => throw s!"type t{t}: size not calculated"

/-- `t.Alignment()`. -/
def alignment (tabs : Tables) (t : TypeRef) : Except String Int := do
  match (← get tabs t).align with
  | some s => return s
  | none => throw s!"type t{t}: alignment not calculated"

def isIntegerKind : TypeKind → Bool
  | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT | .UINT
  | .UINTPTR => true
  | _ => false

def isSignedKind : TypeKind → Bool
  | .INT8 | .INT16 | .INT32 | .INT64 | .INT => true
  | _ => false

/-- `IsPtrShaped`: `PTR`, `UNSAFEPTR`, `MAP`, `CHAN`, `FUNC`. -/
def isPtrShapedKind : TypeKind → Bool
  | .PTR | .UNSAFEPTR | .MAP | .CHAN | .FUNC => true
  | _ => false

def isInteger (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return isIntegerKind (← kind tabs t)
def isSigned (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return isSignedKind (← kind tabs t)
def isPtrShaped (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return isPtrShapedKind (← kind tabs t)
def isFloat (tabs : Tables) (t : TypeRef) : Except String Bool := do
  let k ← kind tabs t; return k == .FLOAT32 || k == .FLOAT64
def isComplex (tabs : Tables) (t : TypeRef) : Except String Bool := do
  let k ← kind tabs t; return k == .COMPLEX64 || k == .COMPLEX128
def isKind (k : TypeKind) (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return (← kind tabs t) == k

/-- `t.Elem()` of a pointer, slice or array. -/
def elem (tabs : Tables) (t : TypeRef) : Except String TypeRef := do
  match (← get tabs t).tail with
  | .elem e => return e
  | .array e _ => return e
  | _ => throw s!"type t{t}: Elem of a type without element"

/-- `t.NumElem()` of an array. -/
def numElem (tabs : Tables) (t : TypeRef) : Except String Int := do
  match (← get tabs t).tail with
  | .array _ n => return n
  | _ => throw s!"type t{t}: NumElem of a non-array"

/-- `t.NumFields()`. -/
def numFields (tabs : Tables) (t : TypeRef) : Except String Nat := do
  match (← get tabs t).tail with
  | .struct fs => return fs.size
  | .results ts => return ts.size
  | .func _ _ _ fs => return fs.size
  | _ => throw s!"type t{t}: NumFields of a non-struct"

/-- `t.FieldType(i)` (tuples and results included, as Go's). -/
def fieldType (tabs : Tables) (t : TypeRef) (i : Nat) : Except String TypeRef := do
  match (← get tabs t).tail with
  | .struct fs =>
    match fs[i]? with
    | some f => return f.type
    | none => throw s!"type t{t}: no field {i}"
  | .tuple a b => if i = 0 then return a else if i = 1 then return b else
      throw s!"type t{t}: no tuple field {i}"
  | .results ts =>
    match ts[i]? with
    | some x => return x
    | none => throw s!"type t{t}: no result {i}"
  | _ => throw s!"type t{t}: FieldType of a non-struct"

/-- `t.FieldOff(i)`. -/
def fieldOff (tabs : Tables) (t : TypeRef) (i : Nat) : Except String Int := do
  match (← get tabs t).tail with
  | .struct fs =>
    match fs[i]? with
    | some { offset := some o, .. } => return o
    | _ => throw s!"type t{t}: no offset for field {i}"
  | _ => throw s!"type t{t}: FieldOff of a non-struct"

/-- `t.HasPointers()`; needs a calculated size. -/
def hasPointers (tabs : Tables) (t : TypeRef) : Except String Bool := do
  let d ← get tabs t
  if d.size.isNone then throw s!"type t{t}: HasPointers needs the size"
  return d.flags.hasptr

def notInHeap (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return (← get tabs t).flags.notinheap

/-- `types.IsDirectIface(t)`. -/
def isDirectIface (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return (← get tabs t).flags.direct

/-- `types.IsComparable(t)`. -/
def isComparable (tabs : Tables) (t : TypeRef) : Except String Bool :=
  return (← get tabs t).flags.comparable

/-- The fields of a struct type. -/
def fields (tabs : Tables) (t : TypeRef) : Except String (Array GoFV.SSA.Field) := do
  match (← get tabs t).tail with
  | .struct fs => return fs
  | _ => throw s!"type t{t}: Fields of a non-struct"

end GoFV.Rules.Ty
