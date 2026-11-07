import GoFV.Gen.State
import GoFV.SSA.TypePred
import GoFV.Asm.Reg
import GoFV.Asm.OpAsm

/-!
# `arm64.ssaGenBlock` (C4)

Port of `ssaGenBlock` with `blockJump`, `leJumps`, `gtJumps` (`cmd/compile/internal/arm64/ssa.go:
1968-2093`; the tables are generated into `GoFV.Asm.ARM64`) and of `State.oneJump`/`CombJump`
(`cmd/compile/internal/ssagen/ssa.go:7643-7677`), plus the `Config.Types` pseudo-type lookup the
block and genssa ports use for `IsFlags`/`IsMemory`.
-/

namespace GoFV.Gen

open GoFV.SSA

/-- A `Config.Types` pseudo-type (`typs` line of section 0, e.g. `Flags`, `Mem`). -/
def GenM.typsRef (name : String) : GenM TypeRef := do
  let env ← GenM.env
  match env.file.sections[0]? |>.bind (·.typs) |>.bind (·.find? (·.1 == name)) with
  | some (_, t) => pure t
  | none => throw s!"typs: no {name}"

/-- `t.IsFlags()` (`t == types.TypeFlags`). -/
def GenM.isFlags (t : TypeRef) : GenM Bool := return t == (← GenM.typsRef "Flags")

/-- `t.IsMemory()`. -/
def GenM.isMemory (t : TypeRef) : GenM Bool := do
  return (← GenM.env).tabs.isMemory (← GenM.typsRef "Mem") t

end GoFV.Gen

namespace GoFV.Gen.Arm64

open GoFV.SSA GoFV.Asm GoFV.Asm.ARM64

/-- `b.Succs[i].Block()`. -/
private def succ (b : Block) (i : Nat) : GenM ID := do
  match b.succs[i]? with
  | some e => pure e.b
  | none => throw s!"b{b.id}: no successor {i}"

/-- `b.Controls[i].Reg()`. -/
private def controlReg (b : Block) (i : Nat) : GenM Int := do
  let some c := b.controls[i]? | throw s!"b{b.id}: no control {i}"
  GenM.lift ((← GenM.env).reg c)

/-- `State.oneJump` (`ssagen/ssa.go:7649`). -/
def oneJump (b : Block) (jump : As × Nat) : GenM Unit := do
  let p ← GenM.br jump.1 (← succ b jump.2)
  GenM.modP p fun x => { x with pos := b.pos }

/-- `State.CombJump` (`ssagen/ssa.go:7656`). -/
def combJump (b : Block) (next : Option ID) (jumps : Array (Array (As × Nat))) : GenM Unit := do
  let j (i k : Nat) : GenM (As × Nat) :=
    match (jumps[i]?).bind (·[k]?) with
    | some x => pure x
    | none => throw s!"CombJump: no jump [{i}][{k}]"
  let s0 ← succ b 0
  let s1 ← succ b 1
  if next == some s0 then
    oneJump b (← j 0 0); oneJump b (← j 0 1)
  else if next == some s1 then
    oneJump b (← j 1 0); oneJump b (← j 1 1)
  else
    let q ← if b.likely != .unlikely then do
        oneJump b (← j 1 0); oneJump b (← j 1 1)
        GenM.br .JMP s1
      else do
        oneJump b (← j 0 0); oneJump b (← j 0 1)
        GenM.br .JMP s0
    GenM.modP q fun x => { x with pos := b.pos }

/-- The conditional branch of `ssaGenBlock`'s two-way cases: the branch Prog whose operands the
caller completes. -/
private def condBranch (b : Block) (next : Option ID) : GenM Nat := do
  let some (asm, invasm) := blockJump b.kind | throw s!"b{b.id}: no blockJump for {repr b.kind}"
  let s0 ← succ b 0
  let s1 ← succ b 1
  if next == some s0 then GenM.br invasm s1
  else if next == some s1 then GenM.br asm s0
  else if b.likely != .unlikely then do
    let p ← GenM.br asm s0
    let _ ← GenM.br .JMP s1
    pure p
  else do
    let p ← GenM.br invasm s1
    let _ ← GenM.br .JMP s0
    pure p

/-- C4: `arm64.ssaGenBlock` (`arm64/ssa.go:1997`). -/
def ssaGenBlock (b : Block) (next : Option ID) : GenM Unit := do
  match b.kind with
  | .Plain | .Defer =>
    let s0 ← succ b 0
    if next != some s0 then
      let _ ← GenM.br .JMP s0
  | .Exit | .RetJmp => pure ()
  | .Ret => let _ ← GenM.sprog .RET
  | .ARM64EQ | .ARM64NE | .ARM64LT | .ARM64GE | .ARM64LE | .ARM64GT | .ARM64ULT | .ARM64UGT
  | .ARM64ULE | .ARM64UGE | .ARM64Z | .ARM64NZ | .ARM64ZW | .ARM64NZW | .ARM64FLT | .ARM64FGE
  | .ARM64FLE | .ARM64FGT | .ARM64LTnoov | .ARM64GEnoov =>
    let p ← condBranch b next
    let some c := b.controls[0]? | throw s!"b{b.id}: no control 0"
    let cv ← GenM.lift ((← GenM.env).value c)
    unless ← GenM.isFlags cv.type do
      let r ← controlReg b 0
      GenM.modP p fun x => { x with from_ := { x.from_ with type := .REG, reg := r } }
  | .ARM64TBZ | .ARM64TBNZ =>
    let p ← condBranch b next
    let r ← controlReg b 0
    GenM.modP p fun x =>
      { x with from_ := { x.from_ with offset := b.auxInt.toInt, type := .CONST }, reg := r }
  | .ARM64LEnoov => combJump b next leJumps
  | .ARM64GTnoov => combJump b next gtJumps
  | .ARM64JUMPTABLE =>
    -- MOVD (TABLE)(IDX<<3), Rtmp; JMP (Rtmp). `genIndexedOperand(OpARM64MOVDloadidx8, …)`.
    let base ← controlReg b 1
    let idx ← controlReg b 0
    let p ← GenM.sprog .MOVD
    GenM.modP p fun x =>
      -- `REG_LSL | 3<<5 | idx&31`: the three bit fields are disjoint, so `|` is `+`.
      { x with from_ := { type := .MEM, reg := base, index := REG_LSL + (3 <<< 5 : Nat) + idx % 32 },
               to := { x.to with type := .REG, reg := REGTMP } }
    let p ← GenM.sprog .JMP
    GenM.modP p fun x => { x with to := { x.to with type := .MEM, reg := REGTMP } }
    modify fun s => { s with jumpTables := s.jumpTables.push b.id }
  | k => throw s!"branch not implemented: b{b.id} {repr k}"

end GoFV.Gen.Arm64
