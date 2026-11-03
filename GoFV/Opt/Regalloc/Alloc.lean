import GoFV.Opt.Regalloc.State

/-!
# Register choice, spills and use lists

`allocReg`, `makeSpill`, `allocValToReg` (`regalloc.go`, go1.27.3, lines 488-726) and the use
list operations `addUse`, `advanceUses`, `dropIfUnused`, `liveAfterCurrentInstruction`,
`setState` (lines 918-998). The wasm-only paths (`OnWasmStack`) do not apply to arm64.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA

/-- `s.allocReg(mask, v)` (`vid = 0` for the temporary-register dummy `tmpVal`). -/
def allocReg (mask : RegMask) (vid : ID) : M Nat := do
  let c ← read
  let mask := (mask.inter c.allocatable).minus (← get).nospill
  if mask.isEmpty then fatal s!"no register available for v{vid}"
  let s ← get
  -- an unused register if there is one
  if let some r := (mask.minus s.used).pick? then
    set { s with usedSinceBlockStart := s.usedSinceBlockStart.addReg r }
    return r
  -- else evict the value whose next use is farthest away (strictly greater: lowest register on ties)
  let mut r := 0
  let mut maxuse : Int := -1
  for t in [0:c.numRegs] do
    if !mask.hasReg t then continue
    let v := s.regs[t]!.v
    let some u := (s.values[v]?.map (·.uses)).bind (·.head?) |
      fatal s!"allocReg: v{v} in register {t} has no next use"
    if u.dist > maxuse then
      r := t
      maxuse := u.dist
  if maxuse == -1 then fatal "couldn't find register to spill"
  -- move the evicted value to a free register first if it would otherwise be lost
  let v2 := s.regs[r]!.v
  let v2v ← val v2
  let m := ((c.compatRegs v2v.type).minus s.used).minus s.tmpused |>.removeReg r
  let vi2 ← vs v2
  if !m.isEmpty && !vi2.remat && vi2.regs.count == 1 then
    modify fun s => { s with usedSinceBlockStart := s.usedSinceBlockStart.addReg r }
    let r2 ← pickReg m
    let cp ← newValue1 (← get).curBlock v2v.pos .Copy v2v.type (← get).regs[r]!.c
    setCopy cp false
    setOrig cp v2
    assignReg r2 v2 cp
  let s ← get
  if !s.usedSinceBlockStart.hasReg r && s.startRegsMask.hasReg r then
    set { s with startRegsMask := s.startRegsMask.removeReg r }
  freeReg r
  modify fun s => { s with usedSinceBlockStart := s.usedSinceBlockStart.addReg r }
  return r

/-- `s.makeSpill(v, b)`: the (lazily created, blockless, argumentless) `StoreReg` of `v`, widening
the dominator-tree interval of its restores by `b`. -/
def makeSpill (v : Value) (b : ID) : M ID := do
  let s ← get
  let vi := s.values[v.id]!
  let node := s.sdom[b]?.getD default
  if vi.spill != 0 then
    modVS v.id fun x => { x with restoreMin := min x.restoreMin node.entry
                                 restoreMax := max x.restoreMax node.exit }
    return vi.spill
  let spill ← newValueNoBlock .StoreReg v.type v.pos
  setOrig spill v.id
  modVS v.id fun x => { x with spill, restoreMin := node.entry, restoreMax := node.exit }
  return spill

/-- `s.allocValToReg(v, mask, nospill, pos)`: a value equal to `v` in a register of `mask`. -/
def allocValToReg (v : Value) (mask : RegMask) (nospill : Bool) (pos : Pos) : M ID := do
  let c ← read
  let vi ← vs v.id
  let pos := pos.withNotStmt
  -- already in a requested register
  if !(mask.inter vi.regs).isEmpty then
    let mask := mask.inter vi.regs
    let mut r ← pickReg mask
    if mask.hasReg c.spReg then r := c.spReg
    if !c.allocatable.hasReg r then return v.id
    let s ← get
    if s.regs[r]!.v != v.id || s.regs[r]!.c == 0 then fatal "bad register state"
    let ns := if nospill then s.nospill.addReg r else s.nospill
    set { s with nospill := ns, usedSinceBlockStart := s.usedSinceBlockStart.addReg r }
    return s.regs[r]!.c
  let r ← allocReg mask v.id
  let vi ← vs v.id
  let b := (← get).curBlock
  let mut cv : ID := 0
  if !vi.regs.isEmpty then
    -- copy from a register v is already in (a fixed register preferred)
    let mut current := v.id
    if (vi.regs.minus c.allocatable).isEmpty then
      let r2 ← pickReg vi.regs
      let s ← get
      if s.regs[r2]!.v != v.id then fatal "bad register state"
      current := s.regs[r2]!.c
      set { s with usedSinceBlockStart := s.usedSinceBlockStart.addReg r2 }
    cv ← newValue1 b pos .Copy v.type current
  else if ← rematerializeable v then
    cv ← copyIntoWithXPos v b pos
    let some out := (← regspec (← val cv)).outputs.head? | fatal s!"no output spec for v{cv}"
    if (mask.inter out.regs).isEmpty then
      setOrig cv v.id
      assignReg (← allocReg out.regs v.id) v.id cv
      cv ← newValue1 b pos .Copy v.type cv
  else
    let spill ← makeSpill v b
    cv ← newValue1 b pos .LoadReg v.type spill
    let sourceMask := c.compatRegs v.type
    if !sourceMask.hasReg r then
      setOrig cv v.id
      assignReg (← allocReg sourceMask v.id) v.id cv
      cv ← newValue1 b pos .Copy v.type cv
  setOrig cv v.id
  assignReg r v.id cv
  if (← val cv).op == .LoadReg && isGReg c r then fatal s!"allocValToReg.OpLoadReg targeting g: v{cv}"
  if nospill then modify fun s => { s with nospill := s.nospill.addReg r }
  return cv

/-- `s.addUse(id, dist, pos)` (calls come with nonincreasing `dist`). -/
def addUse (id : ID) (dist : Int) (pos : Pos) : M Unit := do
  let vi ← vs id
  if let some u := vi.uses.head? then
    if dist > u.dist then fatal "uses added in wrong order"
  modVS id fun x => { x with uses := ⟨dist, pos⟩ :: x.uses }

/-- `s.dropIfUnused(v)`. -/
def dropIfUnused (v : Value) : M Unit := do
  let s ← get
  let some vi := s.values[v.id]? | return
  if !vi.needReg then return
  let mut nextCall := s.nextCall[s.curIdx]!
  if v.op.call then
    nextCall := if s.curIdx == s.nextCall.size - 1 then maxInt32 else s.nextCall[s.curIdx + 1]!
  match vi.uses.head? with
  | none => freeRegs vi.regs
  | some u => if !v.op.fixedReg && u.dist > nextCall then freeRegs vi.regs

/-- `s.advanceUses(v)`: consume the uses of `v`'s arguments; free the registers of arguments
that are dead or next used after a call. -/
def advanceUses (v : Value) : M Unit := do
  for a in v.args do
    let ai ← vs a
    if !ai.needReg then continue
    let some _ := ai.uses.head? | fatal s!"advanceUses: v{a} has no use"
    let rest := ai.uses.tail
    modVS a fun x => { x with uses := rest }
    let aop := (← val a).op
    let nc := (← get).nextCall[(← get).curIdx]!
    match rest.head? with
    | none => freeRegs ai.regs
    | some u => if !aop.fixedReg && u.dist > nc then freeRegs (← vs a).regs
  dropIfUnused v

/-- `s.liveAfterCurrentInstruction(v)`. -/
def liveAfterCurrentInstruction (v : ID) : M Bool := do
  let us := (← vs v).uses
  let some u := us.head? | fatal s!"u is nil, v = v{v}"
  let d := u.dist
  let rest := us.dropWhile (·.dist == d)
  return match rest.head? with
    | some u => u.dist > d
    | none => false

/-- `s.setState(regs)`. -/
def setState (regs : Array EndReg) : M Unit := do
  freeRegs (← get).used
  for x in regs do assignReg x.r x.v x.c

end GoFV.Opt.Regalloc
