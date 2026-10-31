import GoFV.SSA.Export
import GoFV.SSA.TypeCmp

/-!
# Types created by passes

`types.NewPtr` and `types.NewResults` over the export's
tables. The export numbers types by identity key (kind, `LinkString`, flags, `String()`;
`docs/contracts/export.md`), so a "new" Go type object whose key is already in the tables *is*
that table entry; only a key the tables do not have gets a new definition. New definitions go at
fresh numbers `≥ floor` (callers pass a floor past both the tables and the file's `typeorder`, so
a new type is never mistaken for a ranked one); `pass-parity` pairs them with the stock output's
(`GoFVTest/Parity/Renumber.lean`).

`Type.Compare` on a new type (the constant cache's `CMPeq` test) cannot use `typeorder`;
`typeEq` falls back to Go's structural rule for unnamed pointers (`Compare` of two `PTR`s with
nil symbols compares their elements, `types/type.go:1083-1210`).
-/

namespace GoFV.SSA.Tables

/-- The first type number satisfying `p`. -/
def findType? (tabs : Tables) (p : TypeDef → Bool) : Option TypeRef :=
  tabs.types.findIdx? fun d => match d with
    | some d => p d
    | none => false

/-- A new type definition at the first free number `≥ floor`. -/
def mintType (tabs : Tables) (floor : Nat) (d : TypeDef) : TypeRef × Tables :=
  let n := max floor tabs.types.size
  (n, tabs.add (.type n d))

/-- `types.NewPtr(e)` (`types/type.go:622`): the existing unnamed `PTR` to `e`, else a new one
with the fields the export gives such pointers on the corpus: `PtrSize` size/alignment;
pointer data, `hasptr` and `direct` unless `e` is not-in-heap; `noalg` inherited from `e`, which
also drops `comparable` and moves `TypeSymName`'s `noalg.` prefix in front of the `*`;
`String()` `*` ++ elem. -/
def ptrTo (tabs : Tables) (floor : Nat) (ptrSize : Int) (e : TypeRef) :
    Except String (TypeRef × Tables) := do
  if let some t := tabs.findType? (fun d => d.kind == .PTR && !d.flags.named && d.tail == .elem e)
  then return (t, tabs)
  let some ed := tabs.type? e | throw s!"NewPtr: type t{e} not defined"
  let inHeap := !ed.flags.notinheap
  let noalg := ed.flags.noalg
  let noalgPfx := GoStr.ofString "noalg."
  let symName :=
    if ed.symName.size == 0 then ed.symName
    else if noalg && ed.symName.bytes.extract 0 noalgPfx.size == noalgPfx.bytes then
      noalgPfx ++ GoStr.ofString "*" ++ ⟨ed.symName.bytes.extract noalgPfx.size ed.symName.size⟩
    else GoStr.ofString "*" ++ ed.symName
  let d : TypeDef :=
    { kind := .PTR, size := some ptrSize, align := some ptrSize
      ptrdata := some (if inHeap then ptrSize else 0)
      flags := { hasptr := inHeap, noalg, direct := inHeap, comparable := !noalg }
      str := GoStr.ofString "*" ++ ed.str
      symName
      tail := .elem e }
  return tabs.mintType floor d

/-- `types.NewResults(ts)` (`types/type.go:585`): `resultMem` (`types.TypeResultMem`) for
`[mem]`, else the `RESULTS` type with these components (numbered by its components). -/
def newResults (tabs : Tables) (floor : Nat) (mem resultMem : TypeRef) (ts : Array TypeRef) :
    Except String (TypeRef × Tables) := do
  if ts == #[mem] then return (resultMem, tabs)
  if let some t := tabs.findType? (fun d => d.kind == .RESULTS && d.tail == .results ts) then
    return (t, tabs)
  let mut str : GoStr := GoStr.ofString ""
  for h : i in [0:ts.size] do
    let some d := tabs.type? ts[i] | throw s!"NewResults: type t{ts[i]} not defined"
    str := if i == 0 then d.str else str ++ GoStr.ofString "," ++ d.str
  let d : TypeDef :=
    { kind := .RESULTS, size := none, align := none, ptrdata := none, flags := {}, str
      symName := GoStr.ofString "", tail := .results ts }
  return tabs.mintType floor d

/-- `t.Compare(u) == CMPeq` for types of the tables, including types created after `typeorder`
was taken: ranked types compare by rank; otherwise two unnamed pointers compare by element. -/
def typeEq (o : TypeOrder) (tabs : Tables) : Nat → TypeRef → TypeRef → Bool
  | 0, a, b => a == b
  | fuel + 1, a, b =>
    if a == b then true else
    match o.rank? a, o.rank? b with
    | some x, some y => x == y
    | _, _ =>
      match tabs.type? a, tabs.type? b with
      | some da, some db =>
        match da.kind, db.kind, da.tail, db.tail with
        | .PTR, .PTR, .elem ea, .elem eb =>
          !da.flags.named && !db.flags.named && typeEq o tabs fuel ea eb
        | _, _, _, _ => false
      | _, _ => false

end GoFV.SSA.Tables
