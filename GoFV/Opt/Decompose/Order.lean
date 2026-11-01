import GoFV.Opt.Decompose.State

/-!
# decompose: names in and out of the `Func`

`ofFunc` reads `f.Names`/`f.NamedValues`/`f.CanonicalLocalSplits` from the `Func`; `toFunc`
writes them back. Go maps have no order, so the `Func` keeps the two that a pass changes as the
export orders them (`patches/go/0001-gofv-ssa-export.patch`, `section`):

- the export numbers the objects the section creates while writing it: `names` first (a slot,
  then its `*ir.Name`, its type and its `SplitOf` slot); then the `namedx` keys in
  `slotValueOrder` (the aux number of the slot's `*ir.Name`, `2^31-1` if not yet numbered, the
  slot's content key, `slotOrder(SplitOf)`); then the `splits` entries in content order
  (`slotOrder(parent)`, `uint64(Off)^(1<<63)`, `Type.LinkString()`, `slotOrder(slot)`), where
  `slotOrder` is the slot's export number if it has one, else its content key (`gofvSlotKey`).
  New slots and names get numbers in that walk order, past every number of the input tables;
  `exportNums`/`Nums.visitKey` replay it.
- it then writes `namedx` sorted by the numbers of (name, type, `Off`, `SplitOf`,
  `SplitOffset`), and `splits` sorted by the numbers of (parent, `Off`, type, slot), so the
  order does not change between sections when the maps do not.

`Type.LinkString()` is `TypeSymName` without the `noalg.` prefix of no-alg types (`""` when the
export has no size for the type). On the corpus no two `splits` entries share parent and offset
and no two `namedx` keys share a name, so these tie breaks are never reached there.
-/

namespace GoFV.Opt.Decompose

open GoFV.SSA

/-- `f.Names`, `f.NamedValues` and `f.CanonicalLocalSplits` from `f`. -/
def ofFunc (tabs : Tables) (f : Func) : Except String St := do
  let mut nv : Std.HashMap SlotDef (Array ID) := {}
  for (s, vs) in f.names do
    let some d := tabs.slot? s | throw s!"slot s{s} not defined"
    nv := nv.insert d vs
  for (k, vs) in f.namedx do
    nv := nv.insert k vs
  return { f, tabs, names := f.names.map (·.1), nv, splits := f.splits }

/-- Export numbers of the slots and aux objects the section creates (`≥` the floors), in the
order the export assigns them while writing `names`. -/
structure Nums where
  slots : Std.HashMap SlotRef Nat := {}
  auxes : Std.HashMap AuxRef Nat := {}
  nextSlot : Nat
  nextAux : Nat

/-- `x.slot(ls)` while writing `names`: number the slot, then its name, then its parent. -/
def Nums.visit (tabs : Tables) (slotFloor auxFloor : Nat) : Nat → Nums → SlotRef → Nums
  | 0, n, _ => n
  | fuel + 1, n, s =>
    if s < slotFloor || n.slots.contains s then n else
    let n := { n with slots := n.slots.insert s n.nextSlot, nextSlot := n.nextSlot + 1 }
    match tabs.slot? s with
    | none => n
    | some d =>
      let n := if d.name < auxFloor || n.auxes.contains d.name then n
        else { n with auxes := n.auxes.insert d.name n.nextAux, nextAux := n.nextAux + 1 }
      match d.splitOf with
      | some p => Nums.visit tabs slotFloor auxFloor fuel n p
      | none => n

/-- `x.slotInline(k)`: number the key's name, then its `SplitOf` slot. -/
def Nums.visitKey (tabs : Tables) (slotFloor auxFloor : Nat) (n : Nums) (k : SlotDef) : Nums :=
  let n := if k.name < auxFloor || n.auxes.contains k.name then n
    else { n with auxes := n.auxes.insert k.name n.nextAux, nextAux := n.nextAux + 1 }
  match k.splitOf with
  | some p => Nums.visit tabs slotFloor auxFloor typeFuel n p
  | none => n

/-- The export number of a slot (input numbers below the floor are kept). -/
def Nums.slotNum (slotFloor : Nat) (n : Nums) : Option SlotRef → Nat
  | none => 0
  | some s => if s < slotFloor then s else (n.slots[s]?).getD (2 ^ 31 - 1)

/-- The export number of an aux object. -/
def Nums.auxNum (auxFloor : Nat) (n : Nums) (a : AuxRef) : Nat :=
  if a < auxFloor then a else (n.auxes[a]?).getD (2 ^ 31 - 1)

/-- `x.slotValueLess(a, b)` on numbered keys. Types compare by the pass's numbers: the type
tie break needs equal name numbers, which never happens on the corpus. -/
def slotValueLess (slotFloor auxFloor : Nat) (n : Nums) (a b : SlotDef) : Bool :=
  let na := n.auxNum auxFloor a.name
  let nb := n.auxNum auxFloor b.name
  if na != nb then na < nb else
  if a.type != b.type then a.type < b.type else
  if a.off != b.off then a.off < b.off else
  let pa := n.slotNum slotFloor a.splitOf
  let pb := n.slotNum slotFloor b.splitOf
  if pa != pb then pa < pb else a.splitOffset < b.splitOffset

def exportNums (tabs : Tables) (slotFloor auxFloor : Nat) (names : Array SlotRef) : Nums :=
  names.foldl (Nums.visit tabs slotFloor auxFloor typeFuel)
    { nextSlot := max slotFloor 1, nextAux := max auxFloor 1 }

/-- Go's `%d`. -/
private def dec (i : Int) : ByteArray := (toString i).toUTF8

/-- Go's `%0<w>d` of a non-negative number. -/
private def decPad (w : Nat) (n : Nat) : ByteArray :=
  let s := toString n
  ("".pushn '0' (w - s.length) ++ s).toUTF8

private def lit (s : String) : ByteArray := s.toUTF8

/-- `Type.LinkString()` from the export's `TypeSymName`. -/
def linkString (tabs : Tables) (t : TypeRef) : ByteArray :=
  match tabs.type? t with
  | none => .empty
  | some d =>
    let p := "noalg.".toUTF8
    if d.flags.noalg && d.symName.bytes.extract 0 p.size == p then
      d.symName.bytes.extract p.size d.symName.size
    else d.symName.bytes

/-- `gofvSlotKey(ls)`: `name@file:line|LinkString|Off|SplitOffset|(parent key)`. -/
def slotKey (tabs : Tables) : Nat → Option SlotDef → ByteArray
  | _, none => lit "-"
  | 0, some _ => .empty
  | fuel + 1, some d =>
    let (name, pos) := match tabs.aux? d.name with
      | some { kind := .name sym _ _ _ _ _ p, .. } =>
        (sym.bytes, dec p.index ++ lit ":" ++ dec p.line)
      | _ => (.empty, .empty)
    let parent := slotKey tabs fuel (d.splitOf.bind tabs.slot?)
    name ++ lit "@" ++ pos ++ lit "|" ++ linkString tabs d.type ++ lit "|" ++ dec d.off ++
      lit "|" ++ dec d.splitOffset ++ lit "|(" ++ parent ++ lit ")"

/-- `x.slotOrder(ls)` (`-` for nil, as `gofvSlotKey`). -/
def slotOrder (tabs : Tables) (slotFloor : Nat) (n : Nums) (s : Option SlotRef) : ByteArray :=
  match s with
  | none => lit "1" ++ lit "-"
  | some s =>
    if s < slotFloor then lit "0" ++ decPad 10 s
    else match n.slots[s]? with
      | some k => lit "0" ++ decPad 10 k
      | none => lit "1" ++ slotKey tabs typeFuel (tabs.slot? s)

/-- `x.slotValueOrder(k)`. -/
def slotValueOrder (tabs : Tables) (slotFloor auxFloor : Nat) (n : Nums) (k : SlotDef) :
    ByteArray :=
  let an := if k.name < auxFloor then k.name else (n.auxes[k.name]?).getD (2 ^ 31 - 1)
  decPad 10 an ++ lit "|" ++ slotKey tabs typeFuel (some k) ++ lit "|" ++
    slotOrder tabs slotFloor n k.splitOf

/-- Go's string `<` on bytes. -/
def bytesLt (a b : ByteArray) : Bool := Id.run do
  let m := min a.size b.size
  for i in [0:m] do
    if a[i]! < b[i]! then return true
    if a[i]! > b[i]! then return false
  return a.size < b.size

/-- Write the names state back into the function, with the export's map orders, and the
export numbers of the slots and names the section writing meets (`names`, then `namedx`,
`splits` and `canon` in their written order, each sorted with the numbers given so far, as
`section` does). -/
def toFunc (s : St) (slotFloor auxFloor : Nat) : Except String (Func × Nums) := do
  let tabs := s.tabs
  let mut names : Array (SlotRef × Array ID) := #[]
  let mut inNames : Std.HashMap SlotDef Unit := {}
  for n in s.names do
    let some d := tabs.slot? n | throw s!"slot s{n} not defined"
    names := names.push (n, (s.nv[d]?).getD #[])
    inNames := inNames.insert d ()
  let mut nums := exportNums tabs slotFloor auxFloor s.names
  let extra := s.nv.fold (init := #[]) fun acc k vs =>
    if inNames.contains k then acc
    else acc.push (slotValueOrder tabs slotFloor auxFloor nums k, (k, vs))
  let extra := (extra.qsort (fun a b => bytesLt a.1 b.1)).map (·.2)
  for (k, _) in extra do nums := nums.visitKey tabs slotFloor auxFloor k
  let namedx := extra.qsort (fun a b => slotValueLess slotFloor auxFloor nums a.1 b.1)
  let splits := s.splits.map fun (k, v) =>
    let key := slotOrder tabs slotFloor nums (some k.parent) ++ lit "|" ++
      decPad 20 ((k.off + 2 ^ 63) % 2 ^ 64).toNat ++ lit "|" ++ linkString tabs k.type ++
      lit "|" ++ slotOrder tabs slotFloor nums (some v)
    (key, (k, v))
  let splits := (splits.qsort (fun a b => bytesLt a.1 b.1)).map (·.2)
  for (k, v) in splits do
    nums := Nums.visit tabs slotFloor auxFloor typeFuel nums k.parent
    nums := Nums.visit tabs slotFloor auxFloor typeFuel nums v
  let splits := splits.qsort fun (ka, va) (kb, vb) =>
    let pa := nums.slotNum slotFloor (some ka.parent)
    let pb := nums.slotNum slotFloor (some kb.parent)
    if pa != pb then pa < pb else
    if ka.off != kb.off then ka.off < kb.off else
    if ka.type != kb.type then ka.type < kb.type else
    nums.slotNum slotFloor (some va) < nums.slotNum slotFloor (some vb)
  -- `canon` is numbered in content order (`slotOrder(v)|slotValueOrder(k)`) before it is sorted
  let canonKey (e : SlotDef × SlotRef) : ByteArray :=
    slotOrder tabs slotFloor nums (some e.2) ++ lit "|" ++
      slotValueOrder tabs slotFloor auxFloor nums e.1
  let canon := (s.f.canon.map fun e => (canonKey e, e)).qsort (fun a b => bytesLt a.1 b.1)
  for (_, k, v) in canon do
    nums := nums.visitKey tabs slotFloor auxFloor k
    nums := Nums.visit tabs slotFloor auxFloor typeFuel nums v
  return ({ s.f with names, namedx, splits }, nums)

/-- Move the slots the pass created (`≥ slotFloor`) to the numbers the export gives them
(`nums`; slots the export does not meet follow, in creation order). The stock compiler's
slots are numbered by the export of each section, so a later pass that orders slots by number
(`toFunc` sorting `splits` and `namedx` by the numbers of earlier slots) sees the stock order
only with the export's numbering, not with creation order (#79). Names (aux values) keep their
creation order: the driver creates the new autos in number order, which must be the order
`fe.SplitSlot` appended them to `Curfn.Dcl`. -/
def renumberSlots (slotFloor : Nat) (nums : Nums) (tabs : Tables) (f : Func) : Tables × Func :=
  Id.run do
  let mut ren : Std.HashMap SlotRef SlotRef := {}
  let mut next := nums.nextSlot
  for i in [slotFloor:tabs.slots.size] do
    if (tabs.slot? i).isNone then continue
    match nums.slots[i]? with
    | some k => ren := ren.insert i k
    | none => ren := ren.insert i next; next := next + 1
  let sl (s : SlotRef) : SlotRef := ren.getD s s
  let sd (d : SlotDef) : SlotDef := { d with splitOf := d.splitOf.map sl }
  let mut slots := tabs.slots.extract 0 slotFloor
  slots := slots ++ Array.replicate (next - slots.size) none
  for i in [slotFloor:tabs.slots.size] do
    if let some d := tabs.slot? i then slots := slots.set! (sl i) (some (sd d))
  let f := { f with
    names := f.names.map fun (s, vs) => (sl s, vs)
    namedx := f.namedx.map fun (k, vs) => (sd k, vs)
    splits := f.splits.map fun (k, s) => ({ k with parent := sl k.parent }, sl s)
    canon := f.canon.map fun (k, s) => (sd k, sl s) }
  return ({ tabs with slots }, f)

end GoFV.Opt.Decompose
