import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Layout
import Std.Data.HashMap

/-!
# The global image (`docs/plans/semantics.md` §3.4, "Globals"; phase P2)

The initial contents of the global allocations a function can reach, built from its whole
export file (every section's definitions), so every section of one function runs against the
same image:

- `SRODATA` symbols: their exported bytes, read-only, `R_ADDR`/`R_WEAKADDR` relocations as
  pointer fragments to the target symbol (other relocation kinds: poison bytes);
- string data symbols (`go:string."…"`) that are only named (relocation targets, the data
  symbol of a `str` aux): the string's bytes, read-only;
- type descriptors (`type:T`, `typeinfo` set) that are not yet read-only data: the header the
  runtime contracts and fixed loads read (`Size_` at 0, `PtrBytes` at 8, `Hash` at 16, `Kind_`
  at 23, export `config rttype.*`) from the `rtype` line or the type table, the rest poison;
- static closures (`F·f`, the `funcval` of a function without captured variables): one word
  pointing to the code symbol `F`, read-only;
- other symbols the function takes the address of (`Addr`): zero bytes, writable, as large as
  the largest pointee type of those `Addr`s (their contents belong to the environment; zero is
  the state of `runtime.writeBarrier` with the GC off, and of package variables before their
  initialisation); `runtime.writeBarrier` is read-only (only the GC, an environment contract,
  changes it).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- Go's `strconv.Unquote` of a double-quoted literal (the escapes `strconv.Quote` writes),
as bytes. -/
def goUnquote (s : String) : Option (Array UInt8) := do
  let cs := s.toList
  guard (cs.length ≥ 2 && cs.head? == some '"' && cs.getLast? == some '"')
  let body := (cs.drop 1).dropLast
  let hex (c : Char) : Option Nat :=
    if c.isDigit then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go (fuel : Nat) (cs : List Char) (out : Array UInt8) : Option (Array UInt8) :=
    match fuel, cs with
    | 0, _ => none
    | _, [] => some out
    | fuel + 1, '\\' :: c :: rest =>
      let simple (b : Nat) := go fuel rest (out.push (UInt8.ofNat b))
      match c with
      | 'a' => simple 7 | 'b' => simple 8 | 'f' => simple 12 | 'n' => simple 10
      | 'r' => simple 13 | 't' => simple 9 | 'v' => simple 11 | '\\' => simple 92
      | '"' => simple 34 | '\'' => simple 39
      | 'x' => match rest with
        | h1 :: h2 :: rest' => do
          let v := (← hex h1) * 16 + (← hex h2)
          go fuel rest' (out.push (UInt8.ofNat v))
        | _ => none
      | 'u' | 'U' =>
        let n := if c == 'u' then 4 else 8
        let ds := rest.take n
        if ds.length != n then none else do
          let v ← ds.foldlM (fun acc d => do return acc * 16 + (← hex d)) 0
          go fuel (rest.drop n) (out ++ (String.singleton (Char.ofNat v)).toUTF8.toList.toArray)
      | _ =>
        let ds := (c :: rest).take 3
        if ds.length == 3 && ds.all (fun d => '0' ≤ d && d ≤ '7') then
          go fuel (rest.drop 2) (out.push (UInt8.ofNat (ds.foldl (fun a d => a * 8 + (d.toNat - 48)) 0)))
        else none
    | fuel + 1, c :: rest => go fuel rest (out ++ (String.singleton c).toUTF8.toList.toArray)
  go (body.length + 1) body #[]

/-- The read-only allocation holding `bytes`. -/
def roAlloc (bytes : Array UInt8) : Alloc :=
  { data := bytes.map fun x => .b (BitVec.ofNat 8 x.toNat), writable := false }

/-- The contents of a string data symbol from its name, `go:string."…"`. -/
def stringSymAlloc? (name : String) : Option Alloc :=
  if name.startsWith "go:string." then (goUnquote (name.drop 10).toString).map roAlloc else none

/-- The allocation of an `SRODATA` symbol with its relocations. -/
def rodataAlloc (data : ByteArray) (size : Int) (relocs : Array Reloc) : Alloc :=
  let n := max size.toNat data.size
  let bytes : Array Byte := (List.range n).toArray.map fun i =>
    if h : i < data.size then .b (BitVec.ofNat 8 data[i].toNat) else .b 0
  let bytes := relocs.foldl (fun bs r =>
    let off := r.off.toNat
    -- `RelocType(-32767)` is `R_WEAK | R_ADDR` (itab method entries)
    if (r.type == "R_ADDR" || r.type == "R_WEAKADDR" || r.type == "RelocType(-32767)") &&
        r.siz == 8 then
      putBytes bs off (ptrBytes ⟨.global r.target.toStringLossy, BitVec.ofInt 64 r.add⟩)
    else putBytes bs off (Array.replicate r.siz.toNat .poison)) bytes
  { data := bytes, writable := false }

/-- The header of the type descriptor of `t` (56 bytes, `internal/abi.Type`). -/
def typeDescAlloc (tabs : Tables) (t : TypeRef) (rt : Option RType) : Alloc :=
  let size := (rt.bind (·.size)).orElse fun _ => (tabs.type? t).bind (·.size)
  let ptr := (rt.bind (·.ptrdata)).orElse fun _ => (tabs.type? t).bind (·.ptrdata)
  let word (o : Option Int) (n : Nat) : Array Byte :=
    match o with
    | some x => intBytes n (BitVec.ofInt (8 * n) x).toNat
    | none => Array.replicate n .poison
  let data := word size 8 ++ word ptr 8 ++ word (rt.bind (·.hash)) 4 ++
    Array.replicate 3 .poison ++ word (rt.bind (·.abiKind)) 1 ++ Array.replicate 32 .poison
  { data, writable := false }

/-- The global image of an export file (`docs/plans/semantics.md` §3.4). -/
def globalImage (e : ExportFile) : List (String × Alloc) := Id.run do
  let mut tabs : Tables := {}
  let mut img : Std.HashMap String Alloc := {}
  let mut named : Array String := #[]
  let mut sizes : Std.HashMap String Nat := {}
  for s in e.sections do
    tabs := tabs.addAll s.defs
    for d in s.defs do
      match d with
      | .aux _ { kind := .sym name _ kind size _ ti _ data relocs rt, .. } =>
        match kind, data, ti with
        | "SRODATA", some data, _ =>
          img := img.insert name.toStringLossy (rodataAlloc data size relocs)
          for r in relocs do named := named.push r.target.toStringLossy
        | _, _, some t =>
          if !img.contains name.toStringLossy then
            img := img.insert name.toStringLossy (typeDescAlloc tabs t rt)
        | _, _, _ => pure ()
      | .aux _ { kind := .str _ dataSym, .. } => named := named.push dataSym.toStringLossy
      | _ => pure ()
    -- non-rodata symbols whose address is taken: size from the pointee types
    let f := s.func
    for bid in f.blocks do
      for vid in ((f.block? bid).map (·.values)).getD #[] do
        let some v := f.value? vid | continue
        if v.op != .Addr then continue
        let some { kind := .sym name .., .. } := v.aux.bind tabs.aux? | continue
        let elem := match (tabs.type? v.type).map (·.tail) with
          | some (.elem t) => (typeSize? tabs t).getD 0
          | _ => 0
        let k := name.toStringLossy
        sizes := sizes.insert k (max elem (sizes.getD k 0))
  for k in named do
    if !img.contains k then
      if let some a := stringSymAlloc? k then img := img.insert k a
  for (k, n) in sizes.toList do
    if !img.contains k then
      if k.endsWith "·f" then
        let code := (k.dropEnd 2).toString
        img := img.insert k { data := ptrBytes ⟨.global code, 0⟩, writable := false }
      -- the write-barrier flag belongs to the GC: read-only for programs (§9, writebarrier)
      else if k == "runtime.writeBarrier" then
        img := img.insert k { data := Array.replicate (max n 4) (.b 0), writable := false }
      else img := img.insert k { data := Array.replicate n (.b 0) }
  return img.toList

end GoFV.SSA.Sem
