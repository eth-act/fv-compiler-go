import GoFV.Gen.Frame
import GoFV.Gen.Liveness
import GoFV.Gen.ArgLive
import GoFV.Gen.Meta
import GoFV.Gen.Arm64Value
import GoFV.Gen.Arm64ValueRt
import GoFV.Gen.Arm64Block
import GoFV.Gen.Defframe
import GoFV.Asm.Abi

/-!
# `genssa` (C2, C5) and the I3 entry point

Port of `ssagen.genssa` (`cmd/compile/internal/ssagen/ssa.go:6990-7409`) as `ssagen.Compile` runs
it after `buildssa` (`pgen.go:312-314`): `objw.NewProgs`/`SetText` (`objw/prog.go:45-64,191`),
`emitOpenDeferInfo` (the tail of `buildssa`, `ssa.go:597`; it allocates no Prog), `liveness.
Compute`, `emitArgInfo`, `liveness.ArgLiveness`, the `OpenCodedDeferInfo` FUNCDATA,
`emitWrappedFuncInfo`, the block loop with `State.DebugFriendlySetPosFrom` (`ssa.go:6796-6833`)
and the first-statement handling, the no-code generic ops, `CheckLoweredPhi` (`ssa.go:7811`)
and the `OpConvert` check, inline marks (`Arch.Ginsnop`), stack map / unsafe-point / argument
liveness PCDATA, the empty-infinite-loop NOP, the `BlockExit` NOP, the open-coded defer
`deferreturn` exit, inline-mark resolution (incl. the frameless-leaf NOP splice), branch
resolution with statement relaxing (`Block.FirstPossibleStmtValue`, `ssa/numberlines.go:63-79`),
jump tables, and `defframe`.

Not ported (never active for linux/arm64 in the corpus): PGO hot-block alignment
(`base.Debug.AlignHot` is `amd64`/`386` only), the print/HTML/dump paths and the call of
`BuildFuncDebug` (it allocates no Prog and changes none; `GoFV.Dwarf.buildFuncDebug` is its
port). The `valueToProgAfter` table its `GetPC` callback reads is kept (`GenState.progAfter`).
-/

namespace GoFV.Gen

open GoFV.SSA GoFV.Asm

namespace Genssa

/-- `lineMax` (`cmd/internal/src/pos.go:332`). -/
def lineMax : Nat := (1 <<< 20) - 2

/-- `XPos.AtColumn1`: `makeLico(line, 1).withIsStmt()`. -/
def atColumn1 (p : Pos) : Pos :=
  let (line, col) := if p.line ≥ lineMax then (lineMax, 0) else (p.line, 1)
  Pos.withIsStmt { p with line, col, xlogue := 0, stmt := 0 }

/-- `XPos.WithBogusLine`: `makeBogusLico()` (line 1, statement). -/
def withBogusLine (p : Pos) : Except String Pos :=
  if p.index == 0 then
    .error "Assigning a bogus line to XPos with no file will cause mysterious downstream failures."
  else .ok { p with line := 1, col := 0, xlogue := 0, stmt := Pos.isStmtMark }

/-- `ssa.notStmtBoundary`. -/
def notStmtBoundary : Op → Bool
  | .Copy | .Phi | .VarDef | .VarLive | .Unknown | .FwdRef | .Arg | .ArgIntReg | .ArgFloatReg =>
    true
  | _ => false

/-- `PosTable.Pos(p).Base().InliningIndex()` (−1 without a base). -/
def inliningIndex (p : Pos) : GenM Int := do
  if p.index == 0 then return -1
  match (← GenM.env).tabs.posBase? p.index with
  | some b => return b.inl
  | none => throw s!"pos base p{p.index}: not defined"

/-- `v.ResultReg()`. -/
def resultReg (v : Value) : GenM Int := do
  match (← GenM.env).loc? v.id with
  | some (.pair (some r) _) | some (.reg r) => GenM.lift (Env.objReg r)
  | l => throw s!"nil reg for value: v{v.id} ({repr l})"

/-- `State.DebugFriendlySetPosFrom` (`ssa.go:6796`). -/
def debugFriendlySetPosFrom (v : Value) : GenM Unit := do
  match v.op with
  | .Phi | .Copy | .LoadReg | .StoreReg => GenM.setPos v.pos.withNotStmt
  | _ =>
    let p := v.pos
    let cur := (← get).pos
    if p != Pos.none then
      if p.isStmt != Pos.isStmtMark then
        if cur.isStmt == Pos.isStmtMark && cur.sameFileAndLine p then return
        GenM.setPos p.withNotStmt
      else GenM.setPos p
    else GenM.setPos cur.withNotStmt

/-- `CheckLoweredPhi` (`ssa.go:7811`). -/
def checkLoweredPhi (v : Value) : GenM Unit := do
  if ← GenM.isMemory v.type then return
  let env ← GenM.env
  let loc := env.loc? v.id
  for a in v.args do
    if env.loc? a != loc then
      throw s!"phi arg at different location than phi: v{v.id} @ {repr loc}, but arg v{a} @ {repr (env.loc? a)}"

/-- `Arch.SSAGenValue`: part A, else part B. -/
def ssaGenValue (v : Value) : GenM Unit := do
  if ← Arm64.ssaGenValueA v then return
  if ← Arm64.ssaGenValueB v then return
  throw s!"genValue not implemented: v{v.id} {v.op.exportName}"

/-- A `PCDATA $PCDATA_ArgLiveIndex, $idx` (`pp.Prog`). -/
def argLivePCDATA (idx : Int) : GenM Unit := do
  let p ← GenM.prog .PCDATA
  GenM.modP p fun x => { x with from_ := GenM.constAddr Abi.PCDATA_ArgLiveIndex,
                                to := GenM.constAddr idx }

/-- `b.FirstPossibleStmtValue()`. -/
def firstPossibleStmtValue (b : Block) : GenM (Option Value) := do
  let env ← GenM.env
  for vid in b.values do
    let v ← GenM.lift (env.value vid)
    if notStmtBoundary v.op then continue
    return some v
  return none

/-- `bstart[b]`. -/
def bstartOf (b : ID) : GenM Nat := do
  match ((← get).bstart[b]?).join with
  | some p => pure p
  | none => throw s!"b{b}: no block start"

/-- The blocks, values, tails and fix-ups of `genssa` after the FUNCDATA prefix
(`ssa.go:7019-7404`), on the function with the first-statement value repositioned. -/
def body (openDeferInfo : Option Nat) (argLiveBlockMap argLiveValueMap : Std.HashMap ID Int)
    (firstPos0 : Pos) : GenM Unit := do
  let env ← GenM.env
  let f := env.f
  let flagN ← GenM.lift env.flagN
  let mut firstPos := firstPos0
  let mut inlMarks : Std.HashMap Nat Int := {}
  let mut inlMarkList : Array Nat := #[]
  let mut inlMarksByPos : Std.HashMap Pos (Array Nat) := {}
  let mut argLiveIdx : Int := -1
  for i in [0:f.blocks.size] do
    let b ← GenM.lift (env.block f.blocks[i]!)
    modify fun s => { s with lineRunStart := none }
    GenM.setPos (← get).pos.withNotStmt
    let start := (← get).next
    modify fun s => { s with bstart := s.bstart.set! b.id (some start) }
    if let some idx := argLiveBlockMap[b.id]? then
      if idx != argLiveIdx then
        argLiveIdx := idx
        argLivePCDATA idx
    for vid in b.values do
      let v ← GenM.lift (env.value vid)
      debugFriendlySetPosFrom v
      if v.op.resultInArg0 then
        let some a0 := v.args[0]? | throw s!"v{v.id}: resultInArg0 without argument"
        if (← resultReg v) != (← GenM.lift (env.reg a0)) then
          throw s!"input[0] and output not in same register v{v.id}"
      match v.op with
      | .InitMem | .Arg | .SP | .SB | .Select0 | .Select1 | .SelectN | .MakeResult | .GetG
      | .VarDef | .VarLive | .KeepAlive | .WBend => pure ()
      | .Phi => checkLoweredPhi v
      | .Convert =>
        let some a0 := v.args[0]? | throw s!"v{v.id}: Convert without argument"
        if (← GenM.lift (env.reg a0)) != (← GenM.lift (env.reg v.id)) then
          throw s!"OpConvert should be a no-op: v{a0}; v{v.id}"
      | .InlMark =>
        let p ← Arm64.ginsnop
        inlMarks := inlMarks.insert p v.auxInt.toInt32.toInt
        inlMarkList := inlMarkList.push p
        let pos := atColumn1 v.pos
        inlMarksByPos := inlMarksByPos.insert pos ((inlMarksByPos.getD pos #[]).push p)
        firstPos := Pos.none
      | _ =>
        if firstPos != Pos.none && v.op != .ArgIntReg && v.op != .ArgFloatReg &&
            v.op != .LoadReg && v.op != .StoreReg then
          GenM.setPos firstPos
          firstPos := Pos.none
        let live := (← get).live
        modify fun s => { s with nextLive := live.get v.id, nextUnsafe := live.getUnsafe v.id }
        ssaGenValue v
      if let some idx := argLiveValueMap[v.id]? then
        if idx != argLiveIdx then
          argLiveIdx := idx
          argLivePCDATA idx
      modify fun s => { s with progAfter := s.progAfter.insert v.id s.next }
    -- Empty infinite loop: a hardware NOP so that debuggers are less confused.
    let mut bpos := b.pos
    if start == (← get).next && b.succs.size == 1 && b.succs[0]!.b == b.id then
      let p ← Arm64.ginsnop
      GenM.modP p fun x => { x with pos := x.pos.withIsStmt }
      if bpos == Pos.none then
        bpos := (← GenM.getP p).pos
        if bpos == Pos.none then bpos := (← GenM.getP (← get).text).pos
      bpos ← GenM.lift (withBogusLine bpos)
    let live := (← get).live
    modify fun s => { s with nextUnsafe := live.getUnsafeBlock b.id }
    let next := if i + 1 < f.blocks.size && flagN == 0 then some f.blocks[i + 1]! else none
    GenM.setPos bpos
    Arm64.ssaGenBlock { b with pos := bpos } next
  -- A call that does not return must still have its return address inside the function.
  if let some last := f.blocks.back? then
    if (← GenM.lift (env.block last)).kind == .Exit then
      let _ ← Arm64.ginsnop
  -- Open-coded defers: a disconnected `deferreturn` call and return for panic recovery.
  if openDeferInfo.isSome then
    let live := (← get).live
    modify fun s => { s with nextLive := live.deferReturn }
    let p ← GenM.prog .CALL
    let y ← GenM.sym (GoStr.ofString "runtime.deferreturn") 1
    GenM.modP p fun x => { x with to := { x.to with type := .MEM, name := .EXTERN, sym := some y } }
    for o in (← GenM.ownABI).outParams do
      if o.regs.isEmpty then continue
      let (rts, offs) ← GenM.lift (registerTypesAndOffsets env o)
      let some a := o.name | throw "open-coded defer: result without a name"
      let n ← GenM.auxName a
      for k in [0:o.regs.size] do
        let some t := rts[k]? | throw s!"open-coded defer: no register type {k}"
        let some off := offs[k]? | throw s!"open-coded defer: no register offset {k}"
        let reg ← GenM.lift (objRegForAbiReg o.regs[k]!)
        let _ ← Arm64.loadRegResult t reg n off
    let _ ← GenM.prog .RET
  -- Inline marks: reuse instructions at the same position where possible.
  if !inlMarkList.isEmpty then
    let mut hasCall := false
    for pid in ← GenM.listOrder do
      let p ← GenM.getP pid
      if p.as == .NOP || p.as == .FUNCDATA || p.as == .PCDATA || p.as == .TEXT ||
          p.as == .PCALIGN || p.as == .PCALIGNMAX then continue
      if inlMarks.contains pid then continue
      if p.as == .CALL || p.as == .DUFFCOPY || p.as == .DUFFZERO then hasCall := true
      let pos := atColumn1 p.pos
      let marks := inlMarksByPos.getD pos #[]
      if marks.isEmpty then continue
      for m in marks do
        GenM.modP pid fun x => { x with pos := x.pos.withIsStmt }
        modify fun s => { s with inlMarks := s.inlMarks.push (pid, inlMarks.getD m 0) }
        GenM.modP m fun x => { x with as := .NOP, pos := Pos.none, from_ := {}, to := {} }
      inlMarksByPos := inlMarksByPos.erase pos
    for p in inlMarkList do
      if (← GenM.getP p).as != .NOP then
        modify fun s => { s with inlMarks := s.inlMarks.push (p, inlMarks.getD p 0) }
    if (← read).frame.stksize == 0 && !hasCall then
      -- Frameless leaf: its first instruction must not come from an inlined callee (#58300).
      for pid in ← GenM.listOrder do
        let p ← GenM.getP pid
        if p.as == .FUNCDATA || p.as == .PCDATA || p.as == .TEXT || p.as == .NOP then continue
        if (← inliningIndex p.pos) >= 0 then
          let nop ← Arm64.ginsnop
          GenM.modP nop fun x => { x with pos := env.genin.fnPos.withIsStmt }
          -- Unlink it from the end of the list, then splice it in right before `p`.
          for x in ← GenM.listOrder do
            if (← GenM.linkOf x) == some nop then
              GenM.setLink x (← GenM.linkOf nop)
              break
          for x in ← GenM.listOrder do
            if (← GenM.linkOf x) == some pid then
              GenM.setLink nop (some pid)
              GenM.setLink x (some nop)
              break
        break
  -- Resolve branches, and relax DefaultStmt into NotStmt.
  for br in (← get).branches do
    let t ← bstartOf br.target
    let p ← GenM.getP br.prog
    if p.to.type != .BRANCH then throw "setting branch target when type is not TYPE_BRANCH"
    GenM.modP br.prog fun x => { x with to := { x.to with val := .target t } }
    if p.pos.isStmt != Pos.isStmtMark then
      GenM.modP br.prog fun x => { x with pos := x.pos.withNotStmt }
    else
      let tb ← GenM.lift (env.block br.target)
      if let some v0 ← firstPossibleStmtValue tb then
        if v0.pos.line == p.pos.line && v0.pos.isStmt == Pos.isStmtMark then
          GenM.modP br.prog fun x => { x with pos := x.pos.withNotStmt }
  -- Resolve jump table destinations.
  for jt in (← get).jumpTables do
    let b ← GenM.lift (env.block jt)
    let mut targets : Array Nat := #[]
    for e in b.succs do targets := targets.push (← bstartOf e.b)
    let some a := b.aux | throw s!"b{jt}: jump table without aux"
    let (nm, abi) ← GenM.lift (env.lsymOf a)
    let y ← GenM.sym nm abi
    modify fun s => { s with jumpTableSyms := s.jumpTableSyms.push (y, targets) }

/-- `genssa` in `GenM`, from `NewProgs` to `defframe`. -/
def run : GenM Unit := do
  let env ← GenM.env
  let some (tn, tabi) := env.inSyms[env.genin.text.sym]?
    | throw s!"text symbol y{env.genin.text.sym}: not defined"
  GenM.newProgs env.genin.fnPos (← GenM.sym tn tabi)
  emitOpenDeferInfo
  Liveness.compute
  emitArgInfo
  let (argLiveBlockMap, argLiveValueMap) ← argLiveness
  let openDeferInfo := (← get).aux.openCodedDeferInfo
  if let some y := openDeferInfo then
    let p ← GenM.prog .FUNCDATA
    GenM.modP p fun x => { x with from_ := GenM.constAddr Abi.FUNCDATA_OpenCodedDeferInfo,
                                  to := { x.to with type := .MEM, name := .EXTERN, sym := some y } }
  emitWrappedFuncInfo
  let f := env.f
  modify fun s => { s with bstart := Array.replicate (f.bidLast + 1) none }
  -- The first statement of the entry block moves to the function start.
  let some entry := f.block? f.entry | throw "no entry block"
  let mut firstPos := Pos.none
  let mut env' := env
  for vid in entry.values do
    let v ← GenM.lift (env.value vid)
    if v.pos.isStmt == Pos.isStmtMark && v.op != .Arg && v.op != .ArgIntReg &&
        v.op != .ArgFloatReg && v.op != .LoadReg && v.op != .StoreReg then
      firstPos := v.pos
      let v' : Value := { v with pos := firstPos.withDefaultStmt }
      env' := { env with f := { f with valueTab := f.valueTab.set! vid (some v') } }
      break
  withReader (fun c => { c with env := env' }) do
    body openDeferInfo argLiveBlockMap argLiveValueMap firstPos
    defframe

end Genssa

/-- C1–C6: `genssa` with `defframe`, on the frame `fr`. -/
def genssa (env : Env) (fr : FrameOut) : Except String GenOut := do
  let regArgs ← regArgsOf env
  let init : GenState := { dcl := fr.dcl, regArgs }
  let act : GenM GenOut := do
    Genssa.run
    return { st := ← get, order := ← GenM.listOrder }
  let (out, _) ← (act.run (Ctx.ofFrame env fr)).run init
  return out

end GoFV.Gen
