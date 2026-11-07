import GoFV.Asm.Prog

/-!
# DWARF symbol writer (`cmd/internal/obj/dwarf.go` `dwCtxt`, `obj/data.go`; `docs/PASSES3.md` E2)

The per-function DWARF symbols (debug info, location lists, range lists, the line program,
the abstract function) as `obj.LSym`s being written: `P` grows by `prepwrite`, relocations are
appended in order. `DwM` carries them by symbol number (the `.prog` file's numbering) with the
child-DIE references (`RecordDclReference`) and child DIE offsets (`RecordChildDieOffsets`)
that `dwCtxt` hands to the `DwarfFixupTable`. Every write appends at `Size` (the
`dwarf.Context` methods always write at `ls.Size`), so `P` and `Size` stay equal.
-/

namespace GoFV.Dwarf

open GoFV.Asm

/-- A symbol being written: its `P` and `R` (`Size` is `P.size`). -/
structure DSym where
  data : ByteArray := .empty
  relocs : Array Reloc := #[]
  deriving Inhabited

structure DwSt where
  syms : Std.HashMap Nat DSym := {}
  /-- `RecordDclReference`: (symbol, relocation index, abstract function, `ChildIndex`). -/
  dieRefs : Array (Nat × Nat × Nat × Int) := #[]
  /-- `RecordChildDieOffsets`: (abstract function, (`ChildIndex`, offset) per child). -/
  dieOffs : Option (Nat × Array (Int × Int)) := none
  deriving Inhabited

abbrev DwM := StateT DwSt (Except String)

namespace DwM

def fail {α} (msg : String) : DwM α := throw msg

def sym (s : Nat) : DwM DSym := return ((← get).syms[s]?).getD {}

def modifySym (s : Nat) (f : DSym → DSym) : DwM Unit :=
  modify fun st => { st with syms := st.syms.insert s (f ((st.syms[s]?).getD {})) }

/-- `ctxt.Size(s)` / `CurrentOffset(s)`: `s.Size`. -/
def size (s : Nat) : DwM Int := return (← sym s).data.size

/-- Little-endian bytes of the low `n` bytes of `v` (two's complement). -/
def leBytes (n : Nat) (v : Int) : ByteArray := Id.run do
  let u := (v % (2 ^ (8 * n) : Nat)).toNat
  let mut b := ByteArray.empty
  for k in [0:n] do b := b.push ((u >>> (8 * k)) % 256).toUInt8
  return b

/-- `AddBytes(s, b)`: `WriteBytes` at `Size`. -/
def addBytes (s : Nat) (b : ByteArray) : DwM Unit :=
  modifySym s fun d => { d with data := d.data ++ b }

/-- `AddUint8`. -/
def addUint8 (s : Nat) (b : UInt8) : DwM Unit := addBytes s (ByteArray.mk #[b])

/-- `AddInt(s, size, i)`: `WriteInt` at `Size` (sizes 1, 2, 4, 8). -/
def addInt (s : Nat) (size : Nat) (i : Int) : DwM Unit := do
  unless size == 1 || size == 2 || size == 4 || size == 8 do fail s!"WriteInt: bad integer size: {size}"
  addBytes s (leBytes size i)

/-- `AddString(s, v)`: the bytes of `v` and a zero byte. -/
def addString (s : Nat) (v : ByteArray) : DwM Unit := do
  addBytes s v
  addInt s 1 0

/-- `writeAddr` at `Size`: `siz` zero bytes and a relocation of type `t`. -/
def writeAddr (s : Nat) (siz : Nat) (rsym : Nat) (roff : Int) (t : String) : DwM Unit := do
  let off ← size s
  modifySym s fun d => { d with data := d.data ++ leBytes siz 0,
                                relocs := d.relocs.push { off, siz, type := t, add := roff, sym := some rsym } }

/-- `AddAddress(s, data, value)` (pointer size 8): `R_ADDR` to `data`, or the plain integer
when `data` is nil. -/
def addAddress (s : Nat) (data : Option Nat) (value : Int) : DwM Unit :=
  match data with
  | some r => writeAddr s 8 r value "R_ADDR"
  | none => addInt s 8 value

/-- `AddCURelativeAddress(s, data, value)`: `R_ADDRCUOFF`, pointer size. -/
def addCURelativeAddress (s : Nat) (data : Nat) (value : Int) : DwM Unit :=
  writeAddr s 8 data value "R_ADDRCUOFF"

/-- `AddDWARFAddrSectionOffset(s, t, ofs)`: 4 bytes (not AIX), `R_DWARFSECREF`. -/
def addDWARFAddrSectionOffset (s : Nat) (t : Nat) (ofs : Int) : DwM Unit :=
  writeAddr s 4 t ofs "R_DWARFSECREF"

/-- `objabi.FuncCountToDwTxtAddrFlavor`. -/
def dwTxtAddrFlavor (fncount : Nat) : DwM (String × Nat) :=
  if fncount ≤ 127 then pure ("R_DWTXTADDR_U1", 1)
  else if fncount ≤ 16383 then pure ("R_DWTXTADDR_U2", 2)
  else if fncount ≤ 2097151 then pure ("R_DWTXTADDR_U3", 3)
  else if fncount ≤ 268435455 then pure ("R_DWTXTADDR_U4", 4)
  else fail "package has more than 268435455 functions"

/-- `WriteDwTxtAddrx(s, Size, rsym, maxFuncs)`: a zero blob of the flavor's size and an
`R_DWTXTADDR_U*` relocation (no addend). `AddIndirectTextRef` and the DWARF 5 location
lists pass `DwTextCount * 2`. -/
def writeDwTxtAddrx (s : Nat) (rsym : Nat) (maxFuncs : Nat) : DwM Unit := do
  let (t, sz) ← dwTxtAddrFlavor maxFuncs
  writeAddr s sz rsym 0 t

/-- `dwarf.AppendUleb128`. -/
partial def appendUleb128 (b : ByteArray) (v : Nat) : ByteArray :=
  let c := (v % 128).toUInt8
  let v := v / 128
  if v != 0 then appendUleb128 (b.push (c ||| 0x80)) v else b.push c

/-- `dwarf.AppendSleb128`. -/
partial def appendSleb128 (b : ByteArray) (v : Int) : ByteArray :=
  let c := (v % 128).toNat.toUInt8
  let v := v / 128  -- arithmetic shift right by 7 (`Int./` floors for a positive divisor)
  if (v == 0 && c &&& 0x40 == 0) || (v == -1 && c &&& 0x40 != 0) then b.push c
  else appendSleb128 (b.push (c ||| 0x80)) v

/-- `Uleb128put(ctxt, s, v)`: `v` as an unsigned LEB128 of `uint64(v)`. -/
def uleb128put (s : Nat) (v : Int) : DwM Unit :=
  addBytes s (appendUleb128 .empty (v % (2 ^ 64 : Nat)).toNat)

/-- `Sleb128put`. -/
def sleb128put (s : Nat) (v : Int) : DwM Unit := addBytes s (appendSleb128 .empty v)

/-- `RecordDclReference(from, to, dclIdx, inlIndex)`: the last relocation of `from` refers to
child `dclIdx` of `to`. -/
def recordDclReference (frm to : Nat) (dclIdx : Int) : DwM Unit := do
  let n := (← sym frm).relocs.size
  if n == 0 then fail "RecordDclReference: no relocation"
  modify fun st => { st with dieRefs := st.dieRefs.push (frm, n - 1, to, dclIdx) }

/-- `RecordChildDieOffsets(s, vars, offsets)` with the vars' `ChildIndex`. -/
def recordChildDieOffsets (s : Nat) (offs : Array (Int × Int)) : DwM Unit :=
  modify fun st => { st with dieOffs := some (s, offs) }

end DwM

end GoFV.Dwarf
