import GoFV.Dwarf.Sym
import GoFV.Dwarf.Const

/-!
# The DWARF line program of a function (`cmd/internal/obj/dwarf.go:21-203`; `docs/PASSES3.md` E2)

`generateDebugLinesSymbol` writes the state-machine part of `.debug_line` for one function
into its `SDWARFLINES` symbol: `DW_LNE_set_address` with an `R_ADDR` to the text symbol, then
for every Prog with a known line whose successor has another PC: file changes (package file
numbers, 1-based), `prologue_end` (once, after the first Prog positioned `PosPrologueEnd`),
statement toggles and the PC/line advance (`putpclcdelta`: special opcodes with
`LINE_BASE` -4, `LINE_RANGE` 10, `OPCODE_BASE` 11), then `advance_pc` to the end of the
function and `DW_LNE_end_sequence`. It reads the final Prog list (`Pc`, `Pos`), the file
numbers and lines of the positions (`getFileIndexAndLine`) and the function size.
-/

namespace GoFV.Dwarf

open GoFV.Asm
open GoFV.SSA (Pos)
open DwM

def LINE_BASE : Int := -4
def LINE_RANGE : Int := 10
def OPCODE_BASE : Int := 11
def PC_RANGE : Int := (255 - OPCODE_BASE) / LINE_RANGE

/-- `uint64(x)`. -/
private def u64 (x : Int) : Nat := (x % (2 ^ 64 : Nat)).toNat

/-- `putpclcdelta` (`dwarf.go:115-203`): the shortest encoding of a PC delta (`uint64`) and a
line delta (`int64`). -/
def putpclcdelta (s : Nat) (deltaPC : Nat) (deltaLC : Int) : DwM Unit := do
  let dpc : Int := deltaPC
  let mut opcode : Int :=
    if deltaLC < LINE_BASE then
      if dpc ≥ PC_RANGE then OPCODE_BASE + LINE_RANGE * PC_RANGE
      else OPCODE_BASE + LINE_RANGE * dpc
    else if deltaLC < LINE_BASE + LINE_RANGE then
      if dpc ≥ PC_RANGE then
        let o := OPCODE_BASE + (deltaLC - LINE_BASE) + LINE_RANGE * PC_RANGE
        if o > 255 then o - LINE_RANGE else o
      else OPCODE_BASE + (deltaLC - LINE_BASE) + LINE_RANGE * dpc
    else if dpc ≤ PC_RANGE then
      min 255 (OPCODE_BASE + (LINE_RANGE - 1) + LINE_RANGE * dpc)
    else
      -- opcode 255 when deltaPC - PC_RANGE is one of the values whose +1 needs one more byte
      let x := dpc - PC_RANGE
      if x == PC_RANGE || [7, 16, 21, 28, 35, 42, 49, 56, 63].any (fun k => x == 2 ^ k - 1) then 255
      else OPCODE_BASE + LINE_RANGE * PC_RANGE - 1
  if opcode < OPCODE_BASE || opcode > 255 then fail s!"produced invalid special opcode {opcode}"
  -- Subtract the amounts the opcode adds (uint64 arithmetic for the PC delta).
  let deltaPC := u64 (dpc - (opcode - OPCODE_BASE) / LINE_RANGE)
  let deltaLC := deltaLC - ((opcode - OPCODE_BASE) % LINE_RANGE + LINE_BASE)
  if deltaPC != 0 then
    if (deltaPC : Int) ≤ PC_RANGE then
      opcode := opcode - LINE_RANGE * (PC_RANGE - deltaPC)
      if opcode < OPCODE_BASE then fail s!"produced invalid special opcode {opcode}"
      addUint8 s DW_LNS_const_add_pc.toUInt8
    else if 2 ^ 14 ≤ deltaPC && deltaPC < 2 ^ 16 then
      addUint8 s DW_LNS_fixed_advance_pc.toUInt8
      addInt s 2 deltaPC
    else
      addUint8 s DW_LNS_advance_pc.toUInt8
      uleb128put s deltaPC
  if deltaLC != 0 then
    addUint8 s DW_LNS_advance_line.toUInt8
    sleb128put s deltaLC
  addUint8 s opcode.toNat.toUInt8

/-- `generateDebugLinesSymbol(s, lines)` (`dwarf.go:36-113`) for the Prog list `progs` (from
`Text` along `Link`, with final `Pc`s) of the text symbol `textSym` of size `size`;
`fileLine p` is `getFileIndexAndLine(p)` (file number, `int32` relative line). -/
def generateDebugLinesSymbol (textSym lines : Nat) (progs : Array Prog) (size : Int)
    (fileLine : Pos → Except String (Int × Int)) : DwM Unit := do
  let some text := progs[0]? | fail "generateDebugLinesSymbol: no Progs"
  addUint8 lines 0
  uleb128put lines (1 + 8)
  addUint8 lines DW_LNE_set_address.toUInt8
  addAddress lines (some textSym) 0
  let mut stmt := true
  let mut line : Int := 1
  let mut pc := text.pc
  let mut lastpc : Int := 0
  let mut fileIndex : Int := 1
  let mut prologue := false
  let mut wrotePrologue := false
  for h : k in [0:progs.size] do
    let p := progs[k]
    -- `PosPrologueEnd` is xlogue 1 (`cmd/internal/src/pos.go`)
    prologue := prologue || p.pos.xlogue == 1
    if p.pos.line == 0 || (match progs[k + 1]? with | some q => q.pc == p.pc | none => false) then
      continue
    let newStmt := p.pos.isStmt != Pos.notStmt
    let (fi, newLine) ← liftExcept (fileLine p.pos)
    let newFileIndex := fi + 1
    let mut wrote := false
    if newFileIndex != fileIndex then
      addUint8 lines DW_LNS_set_file.toUInt8
      uleb128put lines newFileIndex
      fileIndex := newFileIndex
      wrote := true
    if prologue && !wrotePrologue then
      addUint8 lines DW_LNS_set_prologue_end.toUInt8
      wrotePrologue := true
      wrote := true
    if stmt != newStmt then
      addUint8 lines DW_LNS_negate_stmt.toUInt8
      stmt := newStmt
      wrote := true
    if line != newLine || wrote then
      lastpc := p.pc
      putpclcdelta lines (u64 (p.pc - pc)) (newLine - line)
      line := newLine
      pc := p.pc
  let lastlen := u64 (size - (lastpc - text.pc))
  addUint8 lines DW_LNS_advance_pc.toUInt8
  uleb128put lines lastlen
  addUint8 lines 0
  uleb128put lines 1
  addUint8 lines DW_LNE_end_sequence.toUInt8
where
  liftExcept {α} (e : Except String α) : DwM α := match e with
    | .ok a => pure a
    | .error m => throw m

end GoFV.Dwarf
