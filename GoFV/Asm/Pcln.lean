import GoFV.Asm.Link
import Std.Data.HashSet

/-!
# `MarkUnsafePoints` and `linkpcln`

Ports of the two steps `Flushplist` runs after `span7` (`docs/PASSES3.md` D6, D7):

* `markUnsafePoints` = `obj.MarkUnsafePoints` (`cmd/internal/obj/plist.go:334-407`), called by
  `span7` (`arm64/asm7.go`) with `c.isUnsafePoint` and `c.isRestartable`;
* `linkpcln` = `obj.linkpcln` (`cmd/internal/obj/pcln.go:262-359`) with `funcpctab`,
  `pctospadj`, `pctofileline`, `pctoinline` (the local inlining tree of `inl.go`) and
  `pctopcdata`.

Positions: a `GoFV.SSA.Pos` is an `src.XPos`; `ctxt.PosTable.Pos(xpos)` is the base of index
`xpos.index` in `AsmCtxt.posBases` (nil for index 0) with the same `lico`. `getFileIndexAndLine`
(`line.go:21-27`) gives the base's `FileIndex()` (the export's `<fileindex>`) and
`Pos.RelLine()` (`src/pos.go:90-97`), `b.Line() + (p.Line() - b.Pos().Line())`. The export does
not record `b.Pos()`: it is line 1 for file bases (`NewFileBase`, `src/pos.go:203-214`) and for
inlining copies of them (`NewInliningBase` keeps `pos`), which are the only bases with base line
and column 1 the compiler makes besides line directives; a base with another line or column
comes from a `//line` directive (`NewLinePragmaBase`), whose position the export lacks, so
`relLine` fails on it instead of guessing.
-/

namespace GoFV.Asm

open GoFV.SSA (Pos PosBase GoStr)

/-- `ctxt.Arch.MinLC` for arm64 (`cmd/internal/sys/arch.go:126-131`, `ArchARM64.MinLC = 4`). -/
def minLC : Int := 4

/-- Go's `int32(x)`. -/
private def int32 (x : Int) : Int := x.toInt32.toInt

/-- Go's `uint64(x)` of an `int64`. -/
private def uint64 (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- `binary.PutUvarint` appended to `dst` (`encoding/binary/varint.go`). -/
def putUvarint (dst : ByteArray) (x : Nat) : ByteArray :=
  if x < 0x80 then dst.push x.toUInt8
  else putUvarint (dst.push (x % 0x80 + 0x80).toUInt8) (x / 0x80)
termination_by x
decreasing_by omega

/-- `binary.PutVarint` appended to `dst`: zig-zag (`ux := uint64(x) << 1; if x < 0 { ux = ^ux }`),
then `PutUvarint`. -/
def putVarint (dst : ByteArray) (x : Int) : ByteArray :=
  putUvarint dst (if x ≥ 0 then (2 * x).toNat else (-2 * x - 1).toNat)

/-! ## `MarkUnsafePoints` -/

/-- One iteration of `MarkUnsafePoints`' loop body (`plist.go:351-405`) for `p` after `prev`:
returns `none` for `break`, else the `p` the loop's post statement continues from, and the
updated `prevPcdata`, `prevRestart`. -/
private def markUnsafeStep (isUnsafePoint : Prog → Bool) (isRestartable : Nat → AsmM Bool)
    (prev p : Nat) (prevPcdata prevRestart : Int) : AsmM (Option Nat × Int × Int) := do
  let pp ← AsmM.getP p
  if pp.as == .PCDATA && pp.from_.offset == Abi.PCDATA_UnsafePoint then
    return (some p, pp.to.offset, prevRestart)
  if prevPcdata == Abi.UnsafePointUnsafe then
    return (some p, prevPcdata, prevRestart) -- already unsafe
  if isUnsafePoint pp then
    let q ← AsmM.startUnsafePoint prev
    AsmM.modP q fun x => { x with pc := pp.pc }
    AsmM.setLink q (some p)
    -- Advance to the end of unsafe point.
    let mut p := p
    repeat
      let some n ← AsmM.linkOf p | break
      if !isUnsafePoint (← AsmM.getP n) then break
      p := n
    let some _ ← AsmM.linkOf p
      | return (none, prevPcdata, prevRestart) -- Reached the end, don't bother marking the end
    let e ← AsmM.endUnsafePoint p prevPcdata
    let some l ← AsmM.linkOf e | throw "MarkUnsafePoints: EndUnsafePoint Prog has no Link"
    let lpc := (← AsmM.getP l).pc
    AsmM.modP e fun x => { x with pc := lpc }
    return (some e, prevPcdata, prevRestart)
  if ← isRestartable p then
    let mut val := Abi.UnsafePointRestart1
    if val == prevRestart then
      val := Abi.UnsafePointRestart2
    let prevRestart := val
    let q ← AsmM.appendp prev
    AsmM.modP q fun x =>
      { x with as := .PCDATA,
               from_ := { x.from_ with type := .CONST, offset := Abi.PCDATA_UnsafePoint },
               to := { x.to with type := .CONST, offset := val },
               pc := pp.pc }
    AsmM.setLink q (some p)
    let some n ← AsmM.linkOf p
      | return (none, prevPcdata, prevRestart) -- Reached the end, don't bother marking the end
    if ← isRestartable n then
      -- Next Prog is also restartable. No need to mark the end of this sequence.
      return (some p, prevPcdata, prevRestart)
    let e ← AsmM.appendp p
    AsmM.modP e fun x =>
      { x with as := .PCDATA,
               from_ := { x.from_ with type := .CONST, offset := Abi.PCDATA_UnsafePoint },
               to := { x.to with type := .CONST, offset := prevPcdata } }
    let some l ← AsmM.linkOf e | throw "MarkUnsafePoints: appended Prog has no Link"
    let lpc := (← AsmM.getP l).pc
    AsmM.modP e fun x => { x with pc := lpc }
    return (some e, prevPcdata, prevRestart)
  return (some p, prevPcdata, prevRestart)

/-- `obj.MarkUnsafePoints(ctxt, cursym.Func().Text, newprog, isUnsafePoint, isRestartable)`
(`plist.go:334-407`): brackets the unsafe sequences with `PCDATA $UnsafePoint` Progs and marks
the restartable ones. `isUnsafePoint` reads only the Prog; `isRestartable` takes the Prog ID. -/
def markUnsafePoints (isUnsafePoint : Prog → Bool) (isRestartable : Nat → AsmM Bool) :
    AsmM Unit := do
  let mut prev := (← get).text
  let mut prevPcdata : Int := -1 -- entry PC data value
  let mut prevRestart : Int := 0
  let mut cur ← AsmM.linkOf prev
  repeat
    let some p := cur | break
    let (r, pd, pr) ← markUnsafeStep isUnsafePoint isRestartable prev p prevPcdata prevRestart
    prevPcdata := pd
    prevRestart := pr
    let some p := r | break
    cur ← AsmM.linkOf p
    prev := p

/-! ## `linkpcln` -/

/-- The attributes of the pc-value table symbols: `AttrContentAddressable | AttrPcdata`
(`pcln.go:28-32`, `pcln.go:323-327`). -/
def pcdataAttr : Nat := Obj.AttrContentAddressable.toNat ||| Obj.AttrPcdata.toNat

/-- `&LSym{Type: objabi.SRODATA, Attribute: AttrContentAddressable | AttrPcdata, Align: 1}` with
contents `dst` (`Size = len(dst)`, `P = dst`). -/
private def setPcdataSym (sym : Nat) (dst : ByteArray) : AsmM Unit := do
  AsmM.setSymData sym { sym, kind := "SRODATA", size := dst.size, align := 1, attr := pcdataAttr,
                        data := dst, relocs := #[] }
  modify fun s => { s with symAlign := s.symAlign.insert sym 1 }

/-- `funcpctab(ctxt, cursym, desc, valfunc, arg)` (`pcln.go:25-136`): a new pc-value table
symbol for the text symbol. `valfunc oldval p phase` returns the `int32` value; its state (the
`arg` and closure state of Go's valfuncs) is `σ`. The `fn.Text == nil` case cannot occur (the
text symbol always has its `TEXT` Prog); `ctxt.Debugpcln` logging is not ported. -/
def funcpctab {σ : Type} (valfunc : Int → Prog → Int → StateT σ AsmM Int) :
    StateT σ AsmM Nat := do
  let sym ← (AsmM.freshSym : AsmM Nat)
  let mut dst := ByteArray.empty
  let mut val : Int := -1
  let mut oldval := val
  let st ← getThe AsmSt
  let textP ← (AsmM.getP st.text : AsmM Prog)
  let mut pc := textP.pc
  let order ← (AsmM.listOrder : AsmM (Array Nat))
  let mut started := false
  for i in [0:order.size] do
    let p ← (AsmM.getP order[i]! : AsmM Prog)
    -- Update val. If it's not changing, keep going.
    val ← valfunc val p 0
    if val == oldval && started then
      val ← valfunc val p 1
      continue
    -- If the pc of the next instruction is the same as the pc of this instruction, this
    -- instruction is not a real instruction.
    if h : i + 1 < order.size then
      let nxt ← (AsmM.getP order[i + 1] : AsmM Prog)
      if nxt.pc == p.pc then
        val ← valfunc val p 1
        continue
    if started then
      let pcdelta := (p.pc - pc).tdiv minLC
      dst := putUvarint dst (uint64 pcdelta)
      pc := p.pc
    let delta := int32 (val - oldval)
    dst := putVarint dst delta
    oldval := val
    started := true
    val ← valfunc val p 1
  if started then
    let size := (← getThe AsmSt).textSize
    let v := (size - pc).tdiv minLC
    if v < 0 then
      throw s!"negative pc offset: {v}"
    dst := putUvarint dst (uint64 v)
    -- add terminating varint-encoded 0, which is just 0
    dst := dst.push 0
  (setPcdataSym sym dst : AsmM Unit)
  return sym

/-- The base of `ctxt.PosTable.Pos(xpos)` (`src/xpos.go` `PosTable.Pos`): `none` for index 0,
else the registered base and its `FileIndex` (`none`: not registered). -/
def posBaseOf (xpos : Pos) : AsmM (Option (PosBase × Option Int)) := do
  if xpos.index == 0 then return none
  match (← read).posBases[xpos.index]? with
  | some b => return some b
  | none => throw s!"PosTable.Pos: no position base p{xpos.index}"

/-- `src.Pos.RelLine()` (`src/pos.go:90-97`) of a position with base `b` and line `line`, as
`int32` (`getFileIndexAndLine`'s `int32(pos.RelLine())`). `b.Pos().Line()` is 1 for file bases
and their inlining copies; the export does not record it for line-directive bases. -/
def relLine (b : Option PosBase) (line : Nat) : AsmM Int := do
  match b with
  | none => return 0
  | some b =>
    if b.line == 0 then
      -- base line is unknown => relative line is unknown
      return 0
    if b.line != 1 || b.col != 1 then
      throw s!"getFileIndexAndLine: line-directive position base {repr b}: the export lacks \
        its position (b.Pos().Line())"
    let basePosLine : Int := 1
    return int32 (b.line + (line - basePosLine))

/-- `ctxt.getFileIndexAndLine(xpos)` (`line.go:21-27`): `pos.FileIndex()` and
`int32(pos.RelLine())` of `InnermostPos(xpos)`, the zero `Pos` if not known. -/
def getFileIndexAndLine (xpos : Pos) : AsmM (Int × Int) := do
  let base ← posBaseOf xpos
  -- pos.IsKnown(): base != nil || Line() != 0
  let (base, line) := if base.isSome || xpos.line != 0 then (base, xpos.line) else (none, 0)
  let f ← match base with
    | none => pure (-1)
    | some (_, some fi) => pure fi
    | some (_, none) => throw "PosBase has no file index"
  let l ← relLine (base.map (·.1)) line
  return (f, l)

/-- `pctofileline` (`pcln.go:142-153`): the file number (`isFile`, Go's non-nil `arg`, which
also records it in `UsedFiles`, the state) or the line number at `p`. -/
def pctofileline (isFile : Bool) (oldval : Int) (p : Prog) (phase : Int) :
    StateT (Std.HashSet Nat) AsmM Int := do
  if p.as == .TEXT || p.as == .NOP || p.pos.line == 0 || phase == 1 then
    return oldval
  let (f, l) ← (getFileIndexAndLine p.pos : AsmM (Int × Int))
  if !isFile then
    return l
  -- pcln.UsedFiles[goobj.CUFileIndex(f)] = struct{}{}
  modify fun s => s.insert (f % (2 ^ 32 : Int)).toNat
  return int32 f

/-- `pcinlineState` (`pcln.go:157-160`): `globalToLocal` and the local tree. -/
structure PcinlineState where
  globalToLocal : Std.HashMap Nat Nat := {}
  localTree : Array InlNode := #[]
  deriving Inhabited

/-- `(*pcinlineState).addBranch` (`pcln.go:164-184`): the local index of global node
`globalIndex`, adding it and its parents to the local tree (`localIndex` after the parents). -/
partial def addBranch (globalIndex : Int) : StateT PcinlineState AsmM Int := do
  if globalIndex < 0 then
    return -1
  let g := globalIndex.toNat
  if let some localIndex := (← getThe PcinlineState).globalToLocal[g]? then
    return localIndex
  let some call := (← (read : AsmM AsmCtxt)).inls[g]?
    | throw s!"addBranch: no inlining tree node {g}"
  let parent ← addBranch (match call.parent with | some k => (k : Int) | none => -1)
  let s ← getThe PcinlineState
  let localIndex := s.localTree.size
  set { s with localTree := s.localTree.push
                 { parent, pos := call.pos, func := call.func, name := call.name, parentPC := 0 },
               globalToLocal := s.globalToLocal.insert g localIndex }
  return localIndex

/-- `(*pcinlineState).pctoinline` (`pcln.go:202-222`): the local inlining index at `p`, −1 if
`p` is not the result of inlining. -/
def pctoinline (oldval : Int) (p : Prog) (phase : Int) : StateT PcinlineState AsmM Int := do
  if phase == 1 then
    return oldval
  let some (posBase, _) ← (posBaseOf p.pos : AsmM _) | return -1
  let globalIndex := posBase.inl
  if globalIndex < 0 then
    return -1
  return int32 (← addBranch globalIndex)

/-- `(*pcinlineState).setParentPC` (`pcln.go:186-197`) with `InlTree.setParentPC`
(`inl.go:107-109`). -/
def PcinlineState.setParentPC (s : PcinlineState) (globalIndex : Int) (pc : Int) :
    PcinlineState :=
  if globalIndex < 0 then s else
  match s.globalToLocal[globalIndex.toNat]? with
  | none => s
  | some localIndex =>
    { s with localTree := s.localTree.modify localIndex fun n => { n with parentPC := pc } }

/-- `pctospadj` (`pcln.go:228-242`): the SP adjustment in effect, `p.Spadj` applied after `p`. -/
def pctospadj (oldval : Int) (p : Prog) (phase : Int) : StateT Unit AsmM Int := do
  let oldval := if oldval == -1 then 0 else oldval -- starting
  if phase == 0 then
    return oldval
  let v := int32 (oldval + int32 p.spadj)
  if v < -10000 || v > 1100000000 then
    throw s!"overflow in spadj: {oldval} + {p.spadj} = {v}"
  return v

/-- `pctopcdata` (`pcln.go:249-260`) for table `arg`: the value of the last `PCDATA $arg`. -/
def pctopcdata (arg : Nat) (oldval : Int) (p : Prog) (phase : Int) : StateT Unit AsmM Int := do
  if phase == 0 || p.as != .PCDATA || p.from_.offset != (arg : Int) then
    return oldval
  if int32 p.to.offset != p.to.offset then
    throw s!"overflow in PCDATA instruction: {p.to.offset}"
  return int32 p.to.offset

/-- Go's `1 << uint64(s)` as `uint32` (0 for shifts ≥ 32). -/
private def shl32 (s : Int) : UInt32 :=
  let u := uint64 s
  if u ≥ 32 then 0 else (1 : UInt32) <<< u.toUInt32

/-- Go's `x >> uint64(s) & 1` on a `uint32`. -/
private def bit32 (x : UInt32) (s : Int) : UInt32 :=
  let u := uint64 s
  if u ≥ 32 then 0 else (x >>> u.toUInt32) &&& 1

/-- Go's `a[i]` index check. -/
private def idx (n : Nat) (i : Int) (what : String) : AsmM Nat :=
  if 0 ≤ i && i < n then pure i.toNat else throw s!"linkpcln: {what} index {i} out of range"

/-- `linkpcln(ctxt, cursym)` (`pcln.go:262-359`): the pc-value tables (`Pcsp`, `Pcfile`,
`Pcline`, `Pcinline`, `Pcdata`), `UsedFiles` (ascending), the local inlining tree with the
`ParentPC`s of the inline marks, and the `Funcdata` slots. -/
def linkpcln : AsmM Unit := do
  let order ← AsmM.listOrder
  let mut npcdata : Int := 0
  let mut nfuncdata : Int := 0
  for id in order do
    let p ← AsmM.getP id
    -- Find the highest ID of any used PCDATA table (ignoring all-−1 tables).
    if p.as == .PCDATA && p.from_.offset ≥ npcdata && p.to.offset != -1 then
      npcdata := p.from_.offset + 1
    -- Find the highest ID of any FUNCDATA table.
    if p.as == .FUNCDATA && p.from_.offset ≥ nfuncdata then
      nfuncdata := p.from_.offset + 1
  let npc := npcdata.toNat
  let nfn := nfuncdata.toNat
  let mut pcdata : Array (Option Nat) := Array.replicate npc none
  let mut funcdata : Array (Option Nat) := Array.replicate nfn none

  let (pcsp, _) ← (funcpctab pctospadj).run ()
  let (pcfile, used) ← (funcpctab (pctofileline true)).run {}
  let (pcline, _) ← (funcpctab (pctofileline false)).run {}

  -- Check that all the Progs used as inline markers are still reachable (issue #40473).
  let fn := (← get).fn
  let mut inlMarkProgs : Std.HashSet Nat := {}
  for (mp, _) in fn.inlMarks do
    inlMarkProgs := inlMarkProgs.insert mp
  for id in order do
    inlMarkProgs := inlMarkProgs.erase id
  if inlMarkProgs.size > 0 then
    throw "one or more instructions used as inline markers are no longer reachable"

  let (pcinline, st) ← (funcpctab pctoinline).run {}
  let mut st := st
  for (mp, gid) in fn.inlMarks do
    st := st.setParentPC gid (int32 (← AsmM.getP mp).pc)

  -- tabulate which pc and func data we have.
  let mut havepc : Array UInt32 := Array.replicate ((npc + 31) / 32) 0
  let mut havefunc : Array UInt32 := Array.replicate ((nfn + 31) / 32) 0
  for id in order do
    let p ← AsmM.getP id
    if p.as == .FUNCDATA then
      let k ← idx havefunc.size (p.from_.offset.tdiv 32) "havefunc"
      if bit32 havefunc[k]! (p.from_.offset.tmod 32) != 0 then
        throw s!"multiple definitions for FUNCDATA ${p.from_.offset}"
      havefunc := havefunc.modify k (· ||| shl32 (p.from_.offset.tmod 32))
    if p.as == .PCDATA && p.to.offset != -1 then
      let k ← idx havepc.size (p.from_.offset.tdiv 32) "havepc"
      havepc := havepc.modify k (· ||| shl32 (p.from_.offset.tmod 32))

  -- pcdata.
  for i in [0:npc] do
    if bit32 havepc[i / 32]! (i % 32 : Nat) == 0 then
      -- use an empty symbol.
      let sym ← AsmM.freshSym
      setPcdataSym sym .empty
      pcdata := pcdata.set! i (some sym)
    else
      let (sym, _) ← (funcpctab (pctopcdata i)).run ()
      pcdata := pcdata.set! i (some sym)

  -- funcdata
  if nfn > 0 then
    for id in order do
      let p ← AsmM.getP id
      if p.as != .FUNCDATA then continue
      if p.to.type != .MEM || p.to.offset != 0 then
        throw s!"bad funcdata: Prog {id}"
      let i ← idx funcdata.size p.from_.offset "Funcdata"
      funcdata := funcdata.set! i p.to.sym

  let usedFiles := used.toArray.qsort (· < ·)
  modify fun s =>
    { s with pcln := { pcsp := some pcsp, pcfile := some pcfile, pcline := some pcline,
                       pcinline := some pcinline, pcdata, funcdata },
             usedFiles,
             inlTree := st.localTree }

end GoFV.Asm
