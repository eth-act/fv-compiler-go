import GoFV.Opt.Decompose.State

/-!
# decompose: names in and out of the `Func`

`ofFunc` reads `f.Names`/`f.NamedValues`/`f.CanonicalLocalSplits` from the `Func`; `toFunc`
writes them back. Go maps have no order, so the `Func` keeps the two that a pass changes as the
export orders them (`patches/go/0001-gofv-ssa-export.patch`, `section`):

- `namedx` (keys not in `f.Names`) sorted by `slotValueOrder`: the aux number of the slot's
  `*ir.Name` (`2^31-1` if not yet numbered), the slot's content key, `slotOrder(SplitOf)`;
- `splits` sorted by `slotOrder(parent)`, `uint64(Off)^(1<<63)`, `Type.LinkString()`,
  `slotOrder(slot)`;

where `slotOrder` is the slot's export number if it has one, else its content key
(`gofvSlotKey`). Both compare formatted strings. The export numbers objects the section
creates while writing it, `names` first (a slot, then its `*ir.Name`, its type and its
`SplitOf` slot), so new slots and names get numbers in that walk order, past every number of
the input tables; `exportNums` replays that walk.

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

/-- Write the names state back into the function, with the export's map orders. -/
def toFunc (s : St) (slotFloor auxFloor : Nat) : Except String Func := do
  let tabs := s.tabs
  let mut names : Array (SlotRef × Array ID) := #[]
  let mut inNames : Std.HashMap SlotDef Unit := {}
  for n in s.names do
    let some d := tabs.slot? n | throw s!"slot s{n} not defined"
    names := names.push (n, (s.nv[d]?).getD #[])
    inNames := inNames.insert d ()
  let nums := exportNums tabs slotFloor auxFloor s.names
  let extra := s.nv.fold (init := #[]) fun acc k vs =>
    if inNames.contains k then acc
    else acc.push (slotValueOrder tabs slotFloor auxFloor nums k, (k, vs))
  let namedx := (extra.qsort (fun a b => bytesLt a.1 b.1)).map (·.2)
  let splits := s.splits.map fun (k, v) =>
    let key := slotOrder tabs slotFloor nums (some k.parent) ++ lit "|" ++
      decPad 20 ((k.off + 2 ^ 63) % 2 ^ 64).toNat ++ lit "|" ++ linkString tabs k.type ++
      lit "|" ++ slotOrder tabs slotFloor nums (some v)
    (key, (k, v))
  let splits := (splits.qsort (fun a b => bytesLt a.1 b.1)).map (·.2)
  return { s.f with names, namedx, splits }

end GoFV.Opt.Decompose
