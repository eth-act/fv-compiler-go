import GoFV.Opt.Regalloc.State
import Std.Data.HashMap.Basic

/-!
# Spill placement

`placeSpills` (`regalloc.go`, go1.27.3, lines 2307-2428): each lazily created `StoreReg` goes
to the deepest block of the dominator tree, below the definition, that dominates all restores,
is no deeper in the loop nest, and has the value in a register on entry (bounded search of 100
steps, shared between the descent and the sibling scan).
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA

/-- `mustBeFirst(op)`. -/
def mustBeFirst (op : Op) : Bool :=
  op == .ARM64LoweredGetClosurePtr || op == .Phi || op == .ArgIntReg || op == .ArgFloatReg

/-- The loop depth of block `b` (0 outside loops or without a nest). -/
def depthOf (b : ID) : M Int := do
  let some n := (← get).nest | return 0
  match ← liftE (n.at? b) with
  | some l => return (n.loop l).depth
  | none => return 0

/-- `s.placeSpills()`. -/
def placeSpills : M Unit := do
  let mut start : Std.HashMap ID (Array ID) := {}
  let mut after : Std.HashMap ID (Array ID) := {}
  let nvals := (← get).values.size
  for i in [0:nvals] do
    let vi := (← get).values[i]!
    let spill := vi.spill
    if spill == 0 then continue
    if (← val spill).block != 0 then continue   -- `Arg`s and stack phis are already placed
    let vid ← origOf i
    if vid == 0 then fatal s!"nil v, s.orig[{i}]"
    let v ← val vid
    let mut best := v.block
    let mut bestArg := v.id
    let mut bestDepth ← depthOf best
    let mut b := best
    let mut k := 0
    let sdom := (← get).sdom
    let node (x : ID) : SdomNode := sdom[x]?.getD default
    for _ in [0:100] do
      if k ≥ 100 then break
      -- the child of b in the dominator tree that dominates all restores
      let p := b
      let mut found : Option ID := none
      let mut ch := Analysis.SparseTree.child sdom p
      for _ in [0:100] do
        let some cc := ch | break
        if k ≥ 100 then break
        if (node cc).entry ≤ vi.restoreMin && (node cc).exit ≥ vi.restoreMax then
          found := some cc
          break
        ch := Analysis.SparseTree.sibling sdom cc
        k := k + 1
      let some nb := found | break
      b := nb
      let depth ← depthOf b
      if depth > bestDepth then
        k := k + 1
        continue
      let blk ← blk b
      if blk.preds.size == 1 then
        if let some e := (← get).endRegs[blk.preds[0]!.b]!.find? (·.v == v.id) then
          best := b
          bestArg := e.c
          bestDepth := depth
      else
        if let some e := (← get).startRegs[b]!.find? (·.v == v.id) then
          best := b
          bestArg := e.c
          bestDepth := depth
      k := k + 1
    modF fun f => (f.modV spill fun x => { x with block := best }).addArg spill bestArg
    if best == v.block && !mustBeFirst v.op then
      after := after.insert v.id ((after.getD v.id #[]).push spill)
    else
      start := start.insert best ((start.getD best #[]).push spill)
  -- insert the spills into the schedules
  let f ← getF
  for bid in f.blocks do
    let b := f.getB bid
    let nfirst := (b.values.findIdx? fun v => !mustBeFirst (f.getV v).op).getD b.values.size
    let mut vals := (b.values.extract 0 nfirst) ++ start.getD bid #[]
    for v in b.values.extract nfirst b.values.size do
      vals := vals.push v ++ after.getD v #[]
    modF fun f => f.modB bid fun x => { x with values := vals }

end GoFV.Opt.Regalloc
