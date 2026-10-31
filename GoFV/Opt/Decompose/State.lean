import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.TypeNew
import GoFV.Rules.Helpers.Types
import Std.Data.HashMap.Basic

/-!
# decompose: state, named values and slot splitting

The state `decomposeUser`/`decomposeBuiltin` (`decompose.go`) work on: the function, the
definition tables, `f.Names` and `f.NamedValues` and `f.CanonicalLocalSplits`.

`f.NamedValues` is a Go map keyed by `LocalSlot` *contents* (`SlotDef`, with `SplitOf` as a
slot reference, i.e. a pointer), so two `f.Names` entries with equal contents share one value
list, and keys may be present with an empty list (`maybeAppend` inserts nil entries, the
struct keys `decomposeUserStructInto` keeps are dropped from `f.Names` but stay in the map).
The `Func` carries it as `names` (per `f.Names` entry) plus `namedx` (the other keys);
`ofFunc`/`toFunc` convert.

`f.SplitSlot` (`func.go:266`) caches in `f.CanonicalLocalSplits` by (parent slot, offset,
type) and otherwise calls `fe.SplitSlot` (`ssagen/ssa.go:7997`): a non-`PAUTO` or address-taken
parent keeps its `*ir.Name` (`{N, t, parent.Off+off}`); otherwise a new `PAUTO` local named
parent name + suffix (used, `EscNever`, the parent name's position) becomes the slot
`{n, t, 0, SplitOf parent, SplitOffset off}`. Every cache miss is a new `*LocalSlot`, so a new
slot number (and, for a new local, a new aux number).
-/

namespace GoFV.Opt.Decompose

open GoFV.SSA

/-- What the pass reads besides the function. -/
structure Ctx where
  ptrSize : Int
  regSize : Int
  bigEndian : Bool
  bytePtr : TypeRef
  int : TypeRef
  uintptr : TypeRef
  int32 : TypeRef
  uint32 : TypeRef
  float32 : TypeRef
  float64 : TypeRef
  /-- New types get numbers `≥` this (past the tables and `typeorder`). -/
  typeFloor : Nat

structure St where
  f : Func
  tabs : Tables
  /-- `f.Names`. -/
  names : Array SlotRef
  /-- `f.NamedValues`, keyed by slot contents. -/
  nv : Std.HashMap SlotDef (Array ID)
  /-- `f.CanonicalLocalSplits` (insertion order; `toFunc` sorts as exported). -/
  splits : Array (SplitKey × SlotRef)

/-- The decompose monad; errors are Go's `Fatalf` or unported configurations. -/
abbrev M := ReaderT Ctx (EStateM String St)

/-- Bound on the recursion through nested aggregate types (Go recurses by type depth). -/
def typeFuel : Nat := 1000

@[inline] def liftE {α} (x : Except String α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-- Lift a type query. -/
@[inline] def ty {α} (q : Tables → Except String α) : M α := do liftE (q (← get).tabs)

@[inline] def getF : M Func := return (← get).f

@[inline] def modF (g : Func → Func) : M Unit := modify fun s => { s with f := g s.f }

@[inline] def modFGet {α} (g : Func → Func × α) : M α :=
  modifyGet fun s => let (f, a) := g s.f; (a, { s with f })

/-- The value `id` (`default`, i.e. `OpInvalid`, if freed: Go zeroes freed values). -/
@[inline] def val (id : ID) : M Value := return (← getF).getV id

/-- The contents of slot `s`. -/
def slotDef (s : SlotRef) : M SlotDef := do
  match (← get).tabs.slot? s with
  | some d => return d
  | none => throw s!"slot s{s} not defined"

/-- `f.NamedValues[*s]` (nil if absent). -/
def named (s : SlotRef) : M (Array ID) := do
  return ((← get).nv[← slotDef s]?).getD #[]

/-- `f.NamedValues[*s] = vs`. -/
def setNamed (s : SlotRef) (vs : Array ID) : M Unit := do
  let k ← slotDef s
  modify fun st => { st with nv := st.nv.insert k vs }

/-- `f.NamedValues[*s] = append(f.NamedValues[*s], v)`. -/
def appendNamed (s : SlotRef) (v : ID) : M Unit := do
  let k ← slotDef s
  modify fun st => { st with nv := st.nv.insert k ((st.nv[k]?.getD #[]).push v) }

/-- `delete(f.NamedValues, *s)`. -/
def deleteNamed (s : SlotRef) : M Unit := do
  let k ← slotDef s
  modify fun st => { st with nv := st.nv.erase k }

/-- `maybeAppend` (`decompose.go:112`): append `s` unless its contents are already a key of
`f.NamedValues` (nil entries count), inserting a nil entry. -/
def maybeAppend (ss : Array SlotRef) (s : SlotRef) : M (Array SlotRef) := do
  let k ← slotDef s
  if (← get).nv.contains k then return ss
  modify fun st => { st with nv := st.nv.insert k #[] }
  return ss.push s

/-- `maybeAppend2`. -/
def maybeAppend2 (ss : Array SlotRef) (s1 s2 : SlotRef) : M (Array SlotRef) := do
  maybeAppend (← maybeAppend ss s1) s2

/-! ## Types -/

def isStruct (t : TypeRef) : M Bool := return (← ty (Rules.Ty.kind · t)) == .STRUCT
def isArray (t : TypeRef) : M Bool := return (← ty (Rules.Ty.kind · t)) == .ARRAY

/-- `isStructNotSIMD` (`decompose.go:466`). SIMD types exist only under `GOEXPERIMENT=simd`,
which the pass entry rejects. -/
def isStructNotSIMD (t : TypeRef) : M Bool := isStruct t

/-- `types.NewPtr(e)`. -/
def ptrTo (e : TypeRef) : M TypeRef := do
  let c ← read
  let (t, tabs) ← liftE ((← get).tabs.ptrTo c.typeFloor c.ptrSize e)
  modify fun s => { s with tabs }
  return t

/-! ## Slots -/

/-- A new `*LocalSlot` at a fresh number. -/
def mintSlot (d : SlotDef) : M SlotRef := do
  let s ← get
  let n := max s.tabs.slots.size 1
  set { s with tabs := s.tabs.add (.slot n d) }
  return n

/-- A new aux at a fresh number. -/
def mintAux (d : AuxDef) : M AuxRef := do
  let s ← get
  let n := max s.tabs.auxes.size 1
  set { s with tabs := s.tabs.add (.aux n d) }
  return n

/-- The `*ir.Name` aux `a`: symbol name, class, type, address-taken flag and position. -/
def nameAux (a : AuxRef) : M (GoStr × NameClass × TypeRef × Bool × Pos) := do
  match (← get).tabs.aux? a with
  | some { kind := .name sym cls t _ _ flags pos, .. } => return (sym, cls, t, flags.addrtaken, pos)
  | some _ => throw s!"aux a{a} is not an ir.Name"
  | none => throw s!"aux a{a} not defined"

/-- `f.SplitSlot(name, sfx, offset, t)` (`func.go:266`) with `fe.SplitSlot`. -/
def splitSlot (name : SlotRef) (sfx : GoStr) (off : Int) (t : TypeRef) : M SlotRef := do
  let key : SplitKey := { parent := name, off, type := t }
  if let some (_, s) := (← get).splits.find? (·.1 == key) then return s
  let pd ← slotDef name
  let (sym, cls, _, addrtaken, npos) ← nameAux pd.name
  let ls : SlotDef ←
    if cls != .PAUTO || addrtaken then
      pure { name := pd.name, type := t, off := pd.off + off, splitOf := none, splitOffset := 0 }
    else
      -- `types.CalcSize(t)`: the export would redefine a type whose size becomes known.
      if (← ty (Rules.Ty.get · t)).size.isNone then
        throw s!"SplitSlot: type t{t} has no calculated size"
      let nsym := sym ++ sfx
      let a ← mintAux { fmt := nsym, kind := .name nsym .PAUTO t 0 3 { used := true } npos }
      pure { name := a, type := t, off := 0, splitOf := some name, splitOffset := off }
  let s ← mintSlot ls
  modify fun st => { st with splits := st.splits.push (key, s) }
  return s

/-- `f.SplitString` (`func.go:194`). -/
def splitString (name : SlotRef) : M (SlotRef × SlotRef) := do
  let c ← read
  let p ← splitSlot name ".ptr" 0 c.bytePtr
  let l ← splitSlot name ".len" c.ptrSize c.int
  return (p, l)

/-- `f.SplitInterface` (`func.go:203`): the suffix depends on the type of the slot's
`*ir.Name`. -/
def splitInterface (name : SlotRef) : M (SlotRef × SlotRef) := do
  let c ← read
  let (_, _, nt, _, _) ← nameAux (← slotDef name).name
  let sfx := if (← ty (Rules.Ty.get · nt)).flags.emptyiface then ".type" else ".itab"
  let i ← splitSlot name sfx 0 c.uintptr
  let d ← splitSlot name ".data" c.ptrSize c.bytePtr
  return (i, d)

/-- `f.SplitSlice` (`func.go:217`). -/
def splitSlice (name : SlotRef) : M (SlotRef × SlotRef × SlotRef) := do
  let c ← read
  let pt ← ptrTo (← ty (Rules.Ty.elem · (← slotDef name).type))
  let p ← splitSlot name ".ptr" 0 pt
  let l ← splitSlot name ".len" c.ptrSize c.int
  let k ← splitSlot name ".cap" (c.ptrSize + c.ptrSize) c.int
  return (p, l, k)

/-- `f.SplitComplex` (`func.go:226`). -/
def splitComplex (name : SlotRef) : M (SlotRef × SlotRef) := do
  let c ← read
  let s := (← ty (Rules.Ty.size · (← slotDef name).type)) / 2
  let t := if s == 8 then c.float64 else c.float32
  let r ← splitSlot name ".real" 0 t
  let i ← splitSlot name ".imag" (← ty (Rules.Ty.size · t)) t
  return (r, i)

/-- `f.SplitInt64` (`func.go:239`). -/
def splitInt64 (name : SlotRef) : M (SlotRef × SlotRef) := do
  let c ← read
  let t := if (← ty (Rules.Ty.isSigned · (← slotDef name).type)) then c.int32 else c.uint32
  let ts ← ty (Rules.Ty.size · t)
  if c.bigEndian then
    let hi ← splitSlot name ".hi" 0 t
    let lo ← splitSlot name ".lo" ts c.uint32
    return (hi, lo)
  let hi ← splitSlot name ".hi" ts t
  let lo ← splitSlot name ".lo" 0 c.uint32
  return (hi, lo)

/-- `f.SplitStruct(name, i)` (`func.go:252`): suffix `FieldName(i)` (no separator). -/
def splitStruct (name : SlotRef) (i : Nat) : M SlotRef := do
  let st := (← slotDef name).type
  let fs ← ty (Rules.Ty.fields · st)
  let some fld := fs[i]? | throw s!"type t{st}: no field {i}"
  splitSlot name fld.name (← ty (Rules.Ty.fieldOff · st i)) fld.type

/-- `f.SplitArray(name)` (`func.go:256`). -/
def splitArray (name : SlotRef) : M SlotRef := do
  let arr := (← slotDef name).type
  if (← ty (Rules.Ty.numElem · arr)) != 1 then throw "bad array size"
  splitSlot name "[0]" 0 (← ty (Rules.Ty.elem · arr))

end GoFV.Opt.Decompose
