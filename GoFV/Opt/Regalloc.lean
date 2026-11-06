import GoFV.Opt.Regalloc.Live
import GoFV.Opt.Regalloc.Block
import GoFV.Opt.Regalloc.Spill
import GoFV.Opt.Regalloc.StackAlloc
import GoFV.Opt.Regalloc.Shuffle

/-!
# `regalloc` (pass 56)

Exact port of the stock register allocator for arm64 (`regalloc.go`, `stackalloc.go`,
go1.27.3; spec sheet `docs/PASSES2.md` §4 "regalloc", issue #410): `init`, the block loop,
`placeSpills`, `stackalloc`, `shuffle`, and the removal of unused opportunistic copies. The
output sets `f.RegAlloc`, `f.tempRegs`, the cached CFG analyses it computes (postorder, idom,
sdom, loop nest with `containsUnavoidableCall`), the `AuxCall.Reg`/`ResultReg` caches (aux
redefinitions) and the autos `f.NewLocal` creates (new `name` auxes).

Go removes the unused copies while ranging over a map; only the order of the value free list
depends on it, and from `regalloc` on the export lists the free list sorted (format 5), as
this port returns it.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA

/-- `isLeaf(f)`: no calls other than tail calls. -/
def isLeaf (f : Func) : Bool :=
  f.blocks.all fun b => (f.getB b).values.all fun v =>
    let op := (f.getV v).op
    !(op.call && !op.tailCall)

/-- `regAllocState.init` without `computeLive` (the configuration and the initial state). -/
def mkCfg (env : PassEnv) (f : Func) : Except String Cfg := do
  match env.config? "arch" with
  | some #[.word "arm64"] => pure ()
  | _ => throw "regalloc: only arm64 is supported"
  let regs := ARM64.registers
  let find (nm : String) : Except String Nat :=
    match regs.find? (·.name == nm) with
    | some r => pure r.num
    | none => throw s!"no {nm} register found"
  let spReg ← find "SP"
  let sbReg ← find "SB"
  let gReg ← find "g"
  let zeroReg ← find "ZERO"
  let hasGReg ← env.flag "hasgreg"
  let mut allocatable := ((ARM64.gpRegMask.union ARM64.fpRegMask).union ARM64.specialRegMask).union
    ARM64.simdRegMask
  allocatable := (allocatable.removeReg spReg).removeReg sbReg
  if hasGReg then allocatable := allocatable.removeReg gReg
  allocatable := allocatable.removeReg zeroReg
  if (← env.flag "framepointer") && ARM64.framepointerReg ≥ 0 then
    allocatable := allocatable.removeReg ARM64.framepointerReg.toNat
  if ARM64.linkReg != -1 && isLeaf f then allocatable := allocatable.removeReg ARM64.linkReg.toNat
  let typ (n : String) : Except String TypeRef :=
    match env.typ? n with
    | some t => pure t
    | none => throw s!"typs: no {n}"
  let clobber ← env.flag "clobberdeadreg"
  return { env, tabs := env.tables, numRegs := regs.size, spReg, sbReg, gReg, zeroReg, hasGReg,
           allocatable, gpMask := ARM64.gpRegMask, fpMask := ARM64.fpRegMask
           intParamRegs := ARM64.paramIntReg.toArray, floatParamRegs := ARM64.paramFloatReg.toArray
           mem := ← typ "Mem", flags := ← typ "Flags", void := ← typ "Void", int128 := ← typ "Int128"
           doClobber := clobber && f.blocks.size ≤ 10000 }

/-- The pass body (`s.init` from the loop over values on, `s.regalloc`). -/
def run : M Unit := do
  let c ← read
  let f ← getF
  let nb := f.bidLast + 1
  let mut blockOrder := Array.replicate nb 0
  for i in [0:f.blocks.size] do blockOrder := blockOrder.set! f.blocks[i]! i
  modify fun s => { s with blockOrder }
  for bid in f.blocks do
    for vid in (f.getB bid).values do
      let v := f.getV vid
      if c.needRegister v.type then
        let remat ← rematerializeable v
        modify fun s => { s with values := s.values.modify vid fun x => { x with needReg := true, remat }
                                 orig := s.orig.set! vid vid }
  computeLive
  modify fun s => { s with endRegs := Array.replicate nb #[], startRegs := Array.replicate nb #[]
                           spillLive := Array.replicate nb #[] }
  let (t, f) := (← getF).sdom
  modify fun s => { s with sdom := t, f }
  -- the blocks
  if f.blocks[0]? != some f.entry then fatal "entry block must be first"
  let mut live := Util.SparseSet.new (f.vidLast + 1)
  for bid in f.blocks do live ← allocBlock bid live
  placeSpills
  let stacklive ← stackalloc (← get).spillLive
  shuffle stacklive
  -- erase the copies never used (to a fixed point: a copy can be the only use of another)
  for _ in [0:(← get).copies.size + 1] do
    let mut progress := false
    let cs := (← get).copies
    for cid in [0:cs.size] do
      if cs[cid]! != some false then continue
      let cf ← getF
      let some cv := cf.value? cid | continue
      if cv.uses != 0 then continue
      modF fun f => (f.resetArgs cid).freeValue cid
      modify fun s => { s with copies := s.copies.set! cid none }
      progress := true
    if !progress then break
  let f ← getF
  for bid in f.blocks do
    modF fun f => f.modB bid fun x => { x with values := x.values.filter fun v => (f.value? v).isSome }

/-- The `regalloc` pass. -/
def regallocPass : Pass := fun env f => do
  let cfg ← mkCfg env f
  let nv := f.vidLast + 1
  let st : St := { f, tabs := env.tables, values := Array.replicate nv {}
                   orig := Array.replicate nv 0, regs := Array.replicate cfg.numRegs {}
                   dcl := env.dclLen }
  let ((), s) ← (run.run cfg).run st
  let f := s.f
  -- values left out of every block (rematerializable originals) are gone from the function
  let mut inBlock := Array.replicate (f.vidLast + 1) false
  for b in f.blocks do
    for v in (f.getB b).values do inBlock := inBlock.set! v true
  let valueTab := (Array.range f.valueTab.size).map fun i =>
    if inBlock[i]?.getD false then f.valueTab[i]! else none
  let entries := (Array.range s.homes.size).filterMap fun i => s.homes[i]!.map (i, ·)
  -- `f.RegAlloc` starts as `f.Cache.locs[:0]` (a slice of an array): never nil
  let regAlloc := some (s.homes.size, entries)
  let tempRegs := s.tempRegs.map (·.qsort (·.1 < ·.1))
  let freeValues := (f.freeValues.toArray.qsort (· < ·)).toList
  let f := { f with valueTab, freeValues, low := { f.low with regAlloc, tempRegs } }
  return { func := f, tables := s.tabs }

/-- `tabs` with the register caches `regalloc` stores in the call auxes (`AuxCall.Reg`,
`ResultReg`) filled in as the driver's importer replays them: `regspec` of every call and
`MakeResult` of the allocated `f`, in block and value order, from the caches of `tabs`. The
verified pipeline drops them (`Verified.eraseCallRegs`); its driver output needs them, because
the importer checks that every call aux it fills renders as the Lean output's. -/
def fillCallRegs (env : PassEnv) (f : Func) (tabs : Tables) : Except String Tables := do
  let cfg ← mkCfg { env with tables := tabs } f
  let go : M Unit := f.blocks.forM fun b => (f.getB b).values.forM fun id =>
    match f.value? id with
    | some v => if v.op.call || v.op == .MakeResult then discard (regspec v) else pure ()
    | none => pure ()
  let ((), s) ← (go.run cfg).run { f, tabs, values := #[], orig := #[], regs := #[] }
  return s.tabs

end GoFV.Opt.Regalloc
