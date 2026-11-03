import GoFV.Opt.Regalloc.Alloc
import Std.Data.HashMap.Basic
import Std.Data.HashSet.Basic

/-!
# Allocating one block

The block loop of `regAllocState.regalloc` (`regalloc.go`, go1.27.3, lines 1064-2262): use
lists and `nextCall`, the start state (entry, single predecessor, or merge with phi registers),
dynamic desired registers, the per-value allocation (fixed registers, selectors, `KeepAlive`,
rematerialization, inputs, `resultInArg0`, clobbers, temporaries, outputs), control values,
loop-header preloading and the end state with its live spills.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA GoFV.Util

/-- Desired registers of one scheduled value: `out` and inputs 0-2. -/
structure DEntry where
  out : Regs4 := #[0, 0, 0, 0]
  ins : Array Regs4 := #[#[0, 0, 0, 0], #[0, 0, 0, 0], #[0, 0, 0, 0]]
  deriving Inhabited

@[inline] def modBlk (b : ID) (g : Block → Block) : M Unit := modF fun f => f.modB b g
@[inline] def pushValue (b v : ID) : M Unit := modBlk b fun x => { x with values := x.values.push v }

/-- `s.clobberRegs(m)`. -/
def clobberRegs (m : RegMask) : M Unit := do
  let c ← read
  let mut m := m.inter (c.allocatable.inter c.gpMask)
  for _ in [0:130] do
    let some r := m.pick? | return
    m := m.removeReg r
    let x ← newValue0 (← get).curBlock Pos.none .ClobberReg c.void
    setHome x (.reg r)

/-- The register `home(id)[i]` of a `LocPair` (`i < 2`) or `LocResults`. -/
def componentReg (id : ID) (i : Nat) (results : Bool) : M Nat := do
  match ← getHome id, results with
  | some (.pair a b), false => match (if i == 0 then a else b) with
    | some r => return r
    | none => fatal s!"v{id}: no register for tuple component {i}"
  | some (.results rs), true => match rs[i]?.join with
    | some r => return r
    | none => fatal s!"v{id}: no register for result {i}"
  | _, _ => fatal s!"v{id}: no tuple/results home"

/-- Start state of a merge block: choose the primary predecessor, allocate the phis and save
`startRegs` (`regalloc.go:1201-1415`). -/
def startMerge (b : Block) (phis : Array ID) (live : SparseSet) : M Unit := do
  let c ← read
  let f ← getF
  -- primary predecessor: fewest live spills; ties by likely branch or visit order
  let mut sel : Option Nat := none
  for i in [0:b.preds.size] do
    let s ← get
    let pb := b.preds[i]!.b
    if s.blockOrder[pb]! ≥ s.blockOrder[b.id]! then continue
    match sel with
    | none => sel := some i
    | some j =>
      let pSel := b.preds[j]!.b
      let n := s.spillLive[pb]!.size
      let nSel := s.spillLive[pSel]!.size
      if n < nSel then sel := some i
      else if n == nSel then
        if likelyBranch f (f.getB pb) && !likelyBranch f (f.getB pSel) ||
            s.blockOrder[pb]! < s.blockOrder[pSel]! then sel := some i
  let some idx := sel | fatal s!"bad visitOrder, no predecessor of b{b.id} has been visited before it"
  let p := b.preds[idx]!.b
  setState (← get).endRegs[p]!
  -- phis whose argument from p is in an allocatable register take it
  let mut phiRegs : Array Nat := #[]
  let mut phiUsed : RegMask := {}
  for v in phis do
    if !(← vs v).needReg then
      phiRegs := phiRegs.push RegMask.noReg
      continue
    let a := (← val v).args[idx]!
    let m := ((← vs a).regs.minus phiUsed).inter c.allocatable
    match m.pick? with
    | some r =>
      phiUsed := phiUsed.addReg r
      phiRegs := phiRegs.push r
    | none => phiRegs := phiRegs.push RegMask.noReg
  -- release the phi inputs' registers (saving a still-live input in a free register)
  for i in [0:phis.size] do
    let v := phis[i]!
    if !(← vs v).needReg then continue
    let a ← val (← val v).args[idx]!
    let r := phiRegs[i]!
    if r == RegMask.noReg then continue
    if live.contains a.id then
      let s ← get
      let m := ((c.compatRegs a.type).minus s.used).minus phiUsed
      let ai := s.values[a.id]!
      if !m.isEmpty && !ai.remat && ai.regs.count == 1 then
        let r2 ← pickReg m
        let cp ← newValue1 p a.pos .Copy a.type s.regs[r]!.c
        setCopy cp false
        setOrig cp a.id
        assignReg r2 a.id cp
        modify fun s => { s with endRegs := s.endRegs.modify p (·.push ⟨r2, a.id, cp⟩) }
    freeReg r
  modBlk b.id fun x => { x with values := x.values ++ phis }
  -- the other phis: a register an argument holds at the end of another predecessor, else any
  for i in [0:phis.size] do
    let v ← val phis[i]!
    if !(← vs v.id).needReg then continue
    if phiRegs[i]! != RegMask.noReg then continue
    let mut m := ((c.compatRegs v.type).minus phiUsed).minus (← get).used
    for i2 in [0:b.preds.size] do
      if i2 == idx then continue
      let o ← origOf v.args[i2]!
      let ri := match (← get).endRegs[b.preds[i2]!.b]!.find? (·.v == o) with
        | some er => if o != 0 then er.r else RegMask.noReg
        | none => RegMask.noReg
      if ri != RegMask.noReg && m.hasReg ri then
        m := RegMask.single ri
        break
    if let some r := m.pick? then
      phiRegs := phiRegs.set! i r
      phiUsed := phiUsed.addReg r
  for i in [0:phis.size] do
    let v := phis[i]!
    if !(← vs v).needReg then continue
    let r := phiRegs[i]!
    if r == RegMask.noReg then
      modVS v fun x => { x with spill := v }   -- stack-based phi: starts life spilled
      continue
    assignReg r v v
  -- drop non-phi values that are no longer live
  for r in [0:c.numRegs] do
    if phiUsed.hasReg r then continue
    let v := (← get).regs[r]!.v
    if v != 0 && !live.contains v then freeReg r
  -- save the start state for the merge edges
  let mut regList : Array StartReg := #[]
  for r in [0:c.numRegs] do
    let s ← get
    let v := s.regs[r]!.v
    if v == 0 then continue
    if phiUsed.hasReg r then continue
    let some u := s.values[v]!.uses.head? | fatal s!"start register v{v} has no use"
    regList := regList.push ⟨r, v, s.regs[r]!.c, u.pos⟩
    modify fun s => { s with startRegsMask := s.startRegsMask.addReg r }
  modify fun s => { s with startRegs := s.startRegs.set! b.id regList }

/-- Allocate the arguments of `v` (`regalloc.go:1643-1725`). -/
def allocArgs (v : Value) (rs : RegInfo) (d : DEntry) (avoid : RegMask) : M (Array ID) := do
  let c ← read
  let mut args : Array ID := Array.replicate v.args.size 0
  for i in [0:v.args.size] do
    if !(← vs v.args[i]!).needReg then args := args.set! i v.args[i]!
  -- singleton constraints already satisfied
  for i in rs.inputs do
    let a := v.args[i.idx]!
    if i.regs.count == 1 && !(i.regs.inter (← vs a).regs).isEmpty then
      args := args.set! i.idx (← allocValToReg (← val a) i.regs true v.pos)
  -- singleton constraints whose register is free
  for _ in [0:rs.inputs.length + 1] do
    let mut freed := false
    for i in rs.inputs do
      if args[i.idx]! != 0 then continue
      let a := v.args[i.idx]!
      if i.regs.count == 1 && !(i.regs.minus (← get).used).isEmpty then
        args := args.set! i.idx (← allocValToReg (← val a) i.regs true v.pos)
        let oldregs := (← vs a).regs
        if (oldregs.minus rs.clobbers).isEmpty || !(← liveAfterCurrentInstruction a) then
          freeRegs ((oldregs.minus i.regs).minus (← get).nospill)
          freed := true
    if !freed then break
  -- the rest, most constrained first
  for i in rs.inputs do
    if args[i.idx]! != 0 then continue
    let a := v.args[i.idx]!
    let mut mask := i.regs
    if (mask.inter (← vs a).regs).isEmpty then
      mask := (mask.inter c.allocatable).minus (← get).nospill
      if i.idx < 3 then
        for r in d.ins[i.idx]! do
          if r != RegMask.noReg && (mask.minus (← get).used).hasReg r then
            mask := RegMask.single r
            break
      if !(mask.minus avoid).isEmpty then mask := mask.minus avoid
    if (mask.inter (← vs a).regs).hasReg c.spReg then mask := RegMask.single c.spReg
    args := args.set! i.idx (← allocValToReg (← val a) mask true v.pos)
  return args

/-- `resultInArg0`: make sure clobbering input 0 (or 1 of a commutative op) loses no value
(`regalloc.go:1727-1828`); returns the possibly swapped arguments. -/
def resultInArg0Prep (v : Value) (rs : RegInfo) (d : DEntry) (avoid : RegMask)
    (args : Array ID) : M (Array ID) := do
  let c ← read
  let comm := v.op.commutative
  let swap (a : Array ID) : Array ID := (a.set! 0 a[1]!).set! 1 a[0]!
  let a0 := v.args[0]!
  if !(← liveAfterCurrentInstruction a0) then return args
  if comm then
    if !(← liveAfterCurrentInstruction v.args[1]!) then return swap args
  if (← vs a0).remat then return args
  if comm then
    if (← vs v.args[1]!).remat then return swap args
  if (← vs a0).regs.count ≥ 2 then return args
  if comm then
    if (← vs v.args[1]!).regs.count ≥ 2 then return swap args
  let a0v ← val a0
  let mut m := (c.compatRegs a0v.type).minus (← get).used
  if m.isEmpty then return args
  let out0 := (rs.outputs.head?.map (·.regs)).getD {}
  for r in d.out do
    if r != RegMask.noReg && (m.inter out0).hasReg r then
      return args.set! 0 (← allocValToReg a0v (RegMask.single r) true v.pos)
  for r in d.ins[0]! do
    if r != RegMask.noReg && m.hasReg r then
      let cp ← allocValToReg a0v (RegMask.single r) true v.pos
      setCopy cp false
      return args
  if comm then
    for r in d.ins[1]! do
      if r != RegMask.noReg && m.hasReg r then
        let cp ← allocValToReg (← val v.args[1]!) (RegMask.single r) true v.pos
        setCopy cp false
        return swap args
  if !(m.minus avoid).isEmpty then m := m.minus avoid
  let cp ← allocValToReg a0v m true v.pos
  setCopy cp false
  let mut args := args
  if out0.hasReg (← homeReg cp) then
    if let some (.reg r) ← getHome args[0]! then
      if d.ins[0]!.contains r then args := args.set! 0 cp
  return args

/-- Allocate the outputs of `v` (`regalloc.go:1910-2013`); returns the possibly swapped args. -/
def allocOutputs (v : Value) (rs : RegInfo) (d : DEntry) (avoid : RegMask) (tmpReg : Nat)
    (second : Option Regs4) (args : Array ID) : M (Array ID) := do
  let c ← read
  let mut args := args
  let mut outRegs : Array Nat := Array.replicate 32 RegMask.noReg
  let mut maxOutIdx : Int := -1
  let mut used : RegMask := {}
  if tmpReg != RegMask.noReg then used := used.addReg tmpReg
  for out in rs.outputs do
    if out.regs.isEmpty then continue
    let mut mask := (out.regs.inter c.allocatable).minus used
    if mask.isEmpty then fatal s!"can't find any output register v{v.id}"
    let sused := (← get).used
    if v.op.resultInArg0 && out.idx == 0 then
      if !v.op.commutative then
        let r ← homeReg args[0]!
        if !mask.hasReg r then fatal s!"resultInArg0 value's input cannot be an output of v{v.id}"
        mask := RegMask.single r
      else
        let r0 ← homeReg args[0]!
        let r1 ← homeReg args[1]!
        let mut found := false
        for r in d.out do
          if (r == r0 || r == r1) && (mask.minus sused).hasReg r then
            mask := RegMask.single r
            found := true
            if r == r1 then args := (args.set! 0 args[1]!).set! 1 args[0]!
            break
        if !found then mask := RegMask.single r0
    if out.idx == 0 then
      for r in d.out do
        if r != RegMask.noReg && (mask.minus sused).hasReg r then
          mask := RegMask.single r
          break
    if out.idx == 1 then
      if let some prefs := second then
        for r in prefs do
          if r != RegMask.noReg && (mask.minus sused).hasReg r then
            mask := RegMask.single r
            break
    if !(((mask.minus avoid).minus (← get).nospill).minus sused).isEmpty then
      mask := mask.minus avoid
    let r ← allocReg mask v.id
    if (out.idx : Int) > maxOutIdx then maxOutIdx := out.idx
    outRegs := outRegs.set! out.idx r
    used := used.addReg r
    modify fun s => { s with tmpused := s.tmpused.addReg r }
  let regOf (r : Nat) : Option Nat := if r == RegMask.noReg then none else some r
  if c.isTuple v.type then
    setHome v.id (.pair (regOf outRegs[0]!) (regOf outRegs[1]!))
  else if c.isResults v.type then
    setHome v.id (.results ((Array.range (maxOutIdx + 1).toNat).map fun i => regOf outRegs[i]!))
  else if outRegs[0]! != RegMask.noReg then
    assignReg outRegs[0]! v.id v.id
  if tmpReg != RegMask.noReg then
    modify fun s => { s with tempRegs := some ((s.tempRegs.getD #[]).push (v.id, tmpReg)) }
  return args

/-- Allocate one scheduled value (`regalloc.go:1504-2027`). -/
def allocValue (b : ID) (v : Value) (d : DEntry) (avoid : RegMask)
    (second : Option Regs4) : M Unit := do
  let c ← read
  let rs ← regspec v
  if v.op == .Phi then fatal s!"phi v{v.id} not at start of block"
  if v.op.fixedReg then
    match v.op with
    | .SP => assignReg c.spReg v.id v.id; modify fun s => { s with sp := v.id }
    | .SB => assignReg c.sbReg v.id v.id; modify fun s => { s with sb := v.id }
    | .ARM64ZERO => assignReg c.zeroReg v.id v.id
    | _ => fatal s!"unknown fixed-register op v{v.id}"
    pushValue b v.id
    advanceUses v
    return
  if v.op == .Select0 || v.op == .Select1 || v.op == .SelectN then
    if (← vs v.id).needReg then
      let r ← if v.op == .SelectN then componentReg v.args[0]! v.auxInt.toInt.toNat true
        else componentReg v.args[0]! (if v.op == .Select1 then 1 else 0) false
      assignReg r v.id v.id
    pushValue b v.id
    advanceUses v
    return
  if v.op == .GetG && c.hasGReg then
    if (← get).regs[c.gReg]!.v != 0 then freeReg c.gReg
    assignReg c.gReg v.id v.id
    pushValue b v.id
    advanceUses v
    return
  if v.op == .Arg then
    modVS v.id fun x => { x with spill := v.id }
    pushValue b v.id
    advanceUses v
    return
  if v.op == .KeepAlive then
    advanceUses v
    let a ← val v.args[0]!
    let ai ← vs a.id
    let tabs := (← get).tabs
    let isName := match a.aux with
      | some x => match (tabs.aux? x).map (·.kind) with
        | some (AuxKind.name ..) => true
        | _ => false
      | none => false
    if ai.regs.isEmpty && !ai.remat then
      let sp ← makeSpill a b
      modF fun f => f.setArg v.id 0 sp
    else if isName && ai.remat then
      let a1 := v.args[1]!
      modF fun f => (f.modV v.id fun x => { x with op := .VarLive }).setArgs1 v.id a1
      modF fun f => f.modV v.id fun x => { x with aux := a.aux }
    else
      let a1 := v.args[1]!
      modF fun f => (f.modV v.id fun x => { x with op := .Copy }).setArgs1 v.id a1
    pushValue b v.id
    return
  if rs.inputs.isEmpty && rs.outputs.isEmpty then
    if c.doClobber && v.op.call then clobberRegs rs.clobbers
    freeRegs rs.clobbers
    pushValue b v.id
    advanceUses v
    return
  if (← vs v.id).remat then
    -- issued before each use instead (`allocValToReg`)
    for a in v.args do modF fun f => f.decUses a
    advanceUses v
    return
  let mut args ← allocArgs v rs d avoid
  if v.op.resultInArg0 then args ← resultInArg0Prep v rs d avoid args
  -- keep a copy of a live input the op clobbers
  for i in [0:2] do
    if !(i == 0 && rs.clobbersArg0 || i == 1 && rs.clobbersArg1) then continue
    let a := v.args[i]!
    if !(← liveAfterCurrentInstruction a) then continue
    if (← vs a).remat then continue
    if (← vs a).regs.count ≥ 2 then continue
    let av ← val a
    let m := (c.compatRegs av.type).minus (← get).used
    if m.isEmpty then continue
    let cp ← allocValToReg av m true v.pos
    setCopy cp false
  -- temporary register
  let mut tmpReg := RegMask.noReg
  if v.op.needIntTemp then
    let mut m := c.allocatable.inter c.gpMask
    for out in rs.outputs do
      if out.regs.count == 1 then m := m.minus out.regs
    if !((m.minus avoid).minus (← get).nospill).isEmpty then m := m.minus avoid
    tmpReg ← allocReg m 0
    modify fun s => { s with nospill := s.nospill.addReg tmpReg, tmpused := s.tmpused.addReg tmpReg }
  if rs.clobbersArg0 then freeReg (← homeReg args[0]!)
  if rs.clobbersArg1 then
    if !(rs.clobbersArg0 && (← getHome args[0]!) == (← getHome args[1]!)) then
      freeReg (← homeReg args[1]!)
  if !v.op.resultNotInArgs then
    modify fun s => { s with tmpused := s.nospill, nospill := {} }
    advanceUses v
  if c.doClobber && v.op.call then
    let s ← get
    clobberRegs ((rs.clobbers.minus s.tmpused).minus s.nospill)
  freeRegs rs.clobbers
  modify fun s => { s with tmpused := s.tmpused.union rs.clobbers }
  args ← allocOutputs v rs d avoid tmpReg second args
  if v.op.resultNotInArgs then
    modify fun s => { s with nospill := {} }
    advanceUses v
  modify fun s => { s with tmpused := {} }
  for i in [0:args.size] do
    let a := args[i]!
    modF fun f => f.setArg v.id i a
  pushValue b v.id
  dropIfUnused v

/-- Preload values used soon after the merge into a loop header (`regalloc.go:2068-2165`). -/
def preloadLoop (b : Block) (desired : Desired) : M Unit := do
  let c ← read
  if c.hasGReg && (← get).regs[c.gReg]!.v != 0 then freeReg c.gReg
  let s ← get
  let top := b.succs[0]!.b
  if s.blockOrder[b.id]! > s.blockOrder[top]! then return
  let some n := s.nest | fatal "loop preload without a loop nest"
  let some l ← liftE (n.at? top) | return
  if (n.loop l).header != top || (n.loop l).unavoidableCall then return
  let f ← getF
  let mut phiArgs : Std.HashSet ID := {}
  for v in (f.getB top).values do
    let x := f.getV v
    if x.op == .Phi then phiArgs := phiArgs.insert x.args[b.succs[0]!.i]!
  let lives := s.live.get![b.id]!
  let mut likelyUsedRegs : RegMask := {}
  for l in lives do
    if l.dist < unlikelyDistance then likelyUsedRegs := likelyUsedRegs.union (← vs l.id).regs
  for l in lives do
    if l.dist ≥ unlikelyDistance then continue
    let vid := l.id
    let vi ← vs vid
    let v ← val (← origOf vid)
    if phiArgs.contains vid then
      if !(vi.regs.inter (c.compatRegs v.type)).isEmpty then continue
    else
      if !vi.regs.isEmpty then continue
      if vi.remat then continue
    let mut m := (c.compatRegs v.type).minus likelyUsedRegs
    if m.isEmpty then continue
    let mut done := false
    for (id, regs) in desired.entries do
      if done then break
      if id != v.id then continue
      for r in regs do
        if r != RegMask.noReg && m.hasReg r then
          m := RegMask.single r
          done := true
          break
    if !(m.minus desired.avoid).isEmpty then m := m.minus desired.avoid
    let _ ← allocValToReg v m false b.pos
    likelyUsedRegs := likelyUsedRegs.union (← vs v.id).regs

/-- Allocate block `bid` (one iteration of the `visitOrder` loop). -/
def allocBlock (bid : ID) (live0 : SparseSet) : M SparseSet := do
  let c ← read
  modify fun s => { s with curBlock := bid, startRegsMask := {}, usedSinceBlockStart := {} }
  let b ← blk bid
  let nvals := b.values.size
  -- use lists, the values that may be live in a register, and `nextCall`, walking backwards
  let mut live := live0.clear
  if let some lv := (← get).live then
    for e in lv[bid]! do
      addUse e.id (nvals + e.dist) e.pos
      live := live.add e.id
  for v in b.controls do
    if (← vs v).needReg then
      addUse v nvals b.pos
      live := live.add v
  let mut nextCall : Array Int := Array.replicate nvals 0
  let mut nc := maxInt32
  for k in [0:nvals] do
    let i := nvals - 1 - k
    let v ← val b.values[i]!
    live := live.remove v.id
    if v.op == .Phi then
      nextCall := nextCall.set! i nc
      continue
    if v.op.call then
      live := live.clear
      let s ← get
      if s.sp != 0 && !s.values[s.sp]!.uses.isEmpty then live := live.add s.sp
      if s.sb != 0 && !s.values[s.sb]!.uses.isEmpty then live := live.add s.sb
      nc := i
    for a in v.args do
      if !(← vs a).needReg then continue
      addUse a i v.pos
      live := live.add a
    nextCall := nextCall.set! i nc
  modify fun s => { s with nextCall }
  -- split off the phis; rebuild the schedule
  let f ← getF
  let nphi := (b.values.findIdx? fun v => (f.getV v).op != .Phi).getD nvals
  let phis := b.values.extract 0 nphi
  let oldSched := b.values.extract nphi nvals
  modBlk bid fun x => { x with values := #[] }
  if bid == f.entry then
    if nphi > 0 then fatal "phis in entry block"
  else if b.preds.size == 1 then
    setState (← get).endRegs[b.preds[0]!.b]!
    if nphi > 0 then fatal "phis in single-predecessor block"
    for r in [0:c.numRegs] do
      let v := (← get).regs[r]!.v
      if v != 0 && !live.contains v then freeReg r
  else
    startMerge b phis live
  for i in [0:phis.size] do
    modify fun s => { s with curIdx := i }
    dropIfUnused (← val phis[i]!)
  -- desired registers: static, overridden by the successors' actual registers, then walked back
  let mut desired : Desired := ((← get).desired[bid]?).getD {}
  for e in b.succs do
    for x in (← get).startRegs[e.b]! do desired := desired.add x.v x.r
    for vid in (← blk e.b).values do
      let v ← val vid
      if v.op != .Phi then break
      if !(← vs v.id).needReg then continue
      let mut rp : Option Nat := none
      if let some (.reg r) ← getHome v.id then rp := some r
      else
        for a in v.args do
          if let some (.reg r) ← getHome a then
            rp := some r
            break
      let some r := rp | continue
      desired := desired.add v.args[e.i]! r
  let mut dinfo : Array DEntry := Array.replicate oldSched.size {}
  let mut second : Std.HashMap ID Regs4 := {}
  for k in [0:oldSched.size] do
    let i := oldSched.size - 1 - k
    let v ← val oldSched[i]!
    let (prefs, d) := desired.remove v.id
    desired := d
    let rs ← regspec v
    desired := desired.clobber rs.clobbers
    for j in rs.inputs do
      if j.regs.count != 1 then continue
      desired := desired.clobber j.regs
      desired := desired.add v.args[j.idx]! (← pickReg j.regs)
    if v.op.resultInArg0 || v.op == .Select0 then
      if v.op.commutative then desired := desired.addList v.args[1]! prefs
      desired := desired.addList v.args[0]! prefs
    let mut de : DEntry := { out := prefs }
    for j in [0:min v.args.size 3] do
      de := { de with ins := de.ins.set! j (desired.get v.args[j]!) }
    dinfo := dinfo.set! i de
    if v.op == .Select1 && prefs[0]! != RegMask.noReg then
      second := second.insert v.args[0]! prefs
  -- the scheduled values
  for idx in [0:oldSched.size] do
    modify fun s => { s with curIdx := nphi + idx }
    let v ← val oldSched[idx]!
    allocValue bid v dinfo[idx]! desired.avoid (second.get? v.id)
  -- control values
  let controls := (← blk bid).controls
  for i in [0:controls.size] do
    let v ← val controls[i]!
    if !(← vs v.id).needReg then continue
    let cv ← allocValToReg v (c.compatRegs v.type) false b.pos
    modF fun f => f.replaceControl bid i cv
  for v in controls do
    let vi ← vs v
    if !vi.needReg then continue
    let rest := vi.uses.tail
    modVS v fun x => { x with uses := rest }
    if rest.isEmpty then freeRegs vi.regs
  if b.succs.size == 1 then preloadLoop b desired
  -- end state
  let mut regList : Array EndReg := #[]
  for r in [0:c.numRegs] do
    let x := (← get).regs[r]!
    if x.v != 0 then regList := regList.push ⟨r, x.v, x.c⟩
  modify fun s => { s with endRegs := s.endRegs.set! bid regList }
  if let some lv := (← get).live then
    for e in lv[bid]! do
      let vi ← vs e.id
      if !vi.regs.isEmpty then continue
      if vi.remat then continue
      let sp ← makeSpill (← val (← origOf e.id)) bid
      modify fun s => { s with spillLive := s.spillLive.modify bid (·.push sp) }
    for e in lv[bid]! do
      let us := (← vs e.id).uses
      match us with
      | [_] => modVS e.id fun x => { x with uses := [] }
      | [] => fatal s!"live at end, no uses v{e.id}"
      | _ => fatal s!"live at end, too many uses v{e.id}"
  let s ← get
  if s.startRegsMask.count != s.startRegs[bid]!.size then
    set { s with startRegs := s.startRegs.set! bid (s.startRegs[bid]!.filter fun sr => s.startRegsMask.hasReg sr.r) }
  return live

end GoFV.Opt.Regalloc
