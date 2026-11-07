import GoFV.Gen.Progs

/-!
# `ssagen.State` helpers used by the arm64 emitters

Ports of `State.Prog`, `Br`, `SetPos`, `AddAux`, `AddrAuto`, `ssa.AutoVar`, `Call`, `TailCall`,
`PrepareCall`, `UseArgs`, `SpillSlotAddr` and the name accessors they need
(`ssagen/ssa.go:6755-6789,7680-7713,7857-7942,8146-8153`; `docs/PASSES3.md` C2, C3).
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm

namespace GenM

/-- `State.Prog`: `pp.Prog`, then floats a statement mark to the start of the same-line run
(`lineRunStart`, reset at block starts). -/
def sprog (as : As) : GenM Nat := do
  let p ← prog as
  if losesStmtMark as then return p
  let pp ← getP p
  match (← get).lineRunStart with
  | some r =>
    let rp ← getP r
    if rp.pos.line != pp.pos.line then
      modify fun s => { s with lineRunStart := some p }
    else if pp.pos.isStmt == Pos.isStmtMark then
      modP r fun x => { x with pos := x.pos.withIsStmt }
      modP p fun x => { x with pos := x.pos.withNotStmt }
  | none => modify fun s => { s with lineRunStart := some p }
  return p

/-- `State.Pc`: the placeholder the next Prog fills. -/
def pc : GenM Nat := return (← get).next

/-- `State.SetPos`. -/
def setPos (pos : Pos) : GenM Unit := modify fun s => { s with pos }

/-- `State.Br`: a branch to block `target`, resolved at the end of `genssa`. -/
def br (as : As) (target : ID) : GenM Nat := do
  let p ← sprog as
  modP p fun x => { x with to := { x.to with type := .BRANCH } }
  modify fun s => { s with branches := s.branches.push { prog := p, target } }
  return p

/-- `State.UseArgs`. -/
def useArgs (n : Int) : GenM Unit :=
  modify fun s => if s.maxarg < n then { s with maxarg := n } else s

/-! ## Names -/

def nameInfo (n : Nat) : GenM NameInfo := do lift ((← env).name n)

/-- `n.FrameOffset()` after `AllocFrame`. -/
def frameOffset (n : Nat) : GenM Int := do
  match ((← read).offsets[n]?).join with
  | some o => pure o
  | none => throw s!"name n{n}: no frame offset"

/-- `n.Linksym()`, interned. -/
def nameSym (n : Nat) : GenM Nat := do
  let x ← nameInfo n
  sym x.d.linkName x.d.linkAbi

/-- `n.IsOutputParamInRegisters()`. -/
def outRegs (n : Nat) : GenM Bool := do
  return ((← env).inFlags[n]?).any (·.outregs)

/-- `NAME_PARAM` for `PPARAM` and stack-assigned `PPARAMOUT`, else `NAME_AUTO` (`AddAux2`,
`AddrAuto`). -/
def nameClass (n : Nat) : GenM AddrName := do
  let x ← nameInfo n
  if x.cls == "PPARAM" || (x.cls == "PPARAMOUT" && !(← outRegs n)) then return .PARAM
  return .AUTO

/-- The `Dcl` name of an `*ir.Name` aux. -/
def auxName (a : AuxRef) : GenM Nat := do
  match (← env).nameOfAux? a with
  | some n => pure n
  | none => throw s!"aux a{a} is not a Dcl name"

/-- `ssa.AutoVar`: the name and offset of the `LocalSlot` home of `v`. -/
def autoVar (v : ID) : GenM (Nat × Int) := do
  match (← env).loc? v with
  | some (.slot k) => return (← auxName k.name, k.off)
  | l => throw s!"v{v}: AutoVar of {repr l}"

/-! ## Addresses -/

/-- `AddAux2`: adds `offset` and the aux symbol of `v` to the memory or address operand `a`. -/
def addAux2 (a : Addr) (v : Value) (offset : Int) : GenM Addr := do
  if a.type != .MEM && a.type != .ADDR then throw s!"v{v.id}: bad AddAux addr"
  let a := { a with offset := a.offset + offset }
  match v.aux with
  | none => return a
  | some x =>
    match (← lift ((← env).auxDef x)).kind with
    | .call (some fn) _ =>
      let (nm, abi) ← lift ((← env).lsymOf fn)
      return { a with name := .EXTERN, sym := some (← sym nm abi) }
    | .sym nm abi .. => return { a with name := .EXTERN, sym := some (← sym nm abi) }
    | .name .. =>
      let n ← auxName x
      return { a with name := ← nameClass n, sym := some (← nameSym n),
                      offset := a.offset + (← frameOffset n) }
    | _ => throw s!"v{v.id}: aux not implemented in AddAux"

/-- `AddAux`: `AddAux2` with `v.AuxInt`. -/
def addAux (a : Addr) (v : Value) : GenM Addr := addAux2 a v v.auxInt.toInt

/-- `AddrAuto`: the stack slot home of `v` as a memory operand off `REGSP`. -/
def addrAuto (v : Value) : GenM Addr := do
  let (n, off) ← autoVar v.id
  return { type := .MEM, sym := some (← nameSym n), reg := regSP,
           offset := (← frameOffset n) + off, name := ← nameClass n }
where
  /-- `arm64.REGSP` (`Arch.REGSP`). -/
  regSP : Int := 8383

/-- `SpillSlotAddr`. -/
def spillSlotAddr (spill : RegSpill) (baseReg : Int) (extraOffset : Int) : Addr :=
  { type := .MEM, name := .NONE, reg := baseReg, offset := spill.off + extraOffset }

/-! ## Calls -/

/-- The `*AuxCall` callee symbol of `v` (`none`: not an `AuxCall`, or `Fn == nil`). -/
def callSym? (v : Value) : GenM (Option (GoStr × Nat)) := do
  match v.aux with
  | none => return none
  | some x =>
    match (← lift ((← env).auxDef x)).kind with
    | .call (some fn) _ => return some (← lift ((← env).lsymOf fn))
    | _ => return none

/-- `State.PrepareCall`: checks the stack map (`wbZero`/`wbMove` calls have none) and records
the outgoing argument size. -/
def prepareCall (v : Value) : GenM Unit := do
  let idx := (← get).live.get v.id
  if idx == stackMapDontCare then
    let fn ← callSym? v
    let ok := match fn with
      | some (nm, abi) =>
        abi == 1 && (nm.toStringLossy == "runtime.wbZero" || nm.toStringLossy == "runtime.wbMove")
      | none => false
    unless ok do throw s!"missing stack map index for v{v.id}"
  useArgs v.auxInt.toInt

/-- `State.Call`: a `CALL` to the `AuxCall` symbol, or through `(Rarg0)` (arm64: `TYPE_MEM`). -/
def call (v : Value) : GenM Nat := do
  let pPosIsStmt := (← get).pos.isStmt
  prepareCall v
  let p ← sprog .CALL
  modP p fun x => { x with pos := if pPosIsStmt == Pos.isStmtMark then v.pos.withIsStmt
                                  else v.pos.withNotStmt }
  match ← callSym? v with
  | some (nm, abi) =>
    let y ← sym nm abi
    modP p fun x => { x with to := { x.to with type := .MEM, name := .EXTERN, sym := some y } }
  | none =>
    let some a0 := v.args[0]? | throw s!"v{v.id}: indirect call without argument"
    let r ← lift ((← env).reg a0)
    modP p fun x => { x with to := { x.to with type := .MEM, reg := r } }
  return p

/-- `State.TailCall`: `Call` with `RET`. -/
def tailCall (v : Value) : GenM Nat := do
  let p ← call v
  modP p fun x => { x with as := .RET }
  return p

end GenM

end GoFV.Gen
