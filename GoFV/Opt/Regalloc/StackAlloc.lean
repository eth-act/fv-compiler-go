import GoFV.Opt.Regalloc.State
import Std.Data.HashMap.Basic

/-!
# Stack slots

`stackalloc` (`stackalloc.go`, go1.27.3), called by regalloc before the merge edges are fixed
up: every value without a home that needs one (spills, stack phis, `Arg`s) gets a `LocalSlot`.
Liveness by backward path exploration from the use blocks (ascending value IDs, LIFO queue),
an interference graph (adjacency lists in sparse-set order), names from `f.Names` first, then
anonymous autos reused per `LinkString` (the first index no interfering value uses).
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA GoFV.Util

/-- `stackValState`. -/
structure StackVal where
  typ : TypeRef := 0
  spill : ID := 0
  needSlot : Bool := false
  isArg : Bool := false
  defBlock : ID := 0
  /-- `useBlocks`: `(block, liveout)`. -/
  useBlocks : Array (ID × Bool) := #[]
  deriving Inhabited

/-- `sv.addUseBlock(b, liveout)`: appended unless equal to the last entry. -/
def StackVal.addUseBlock (sv : StackVal) (b : ID) (liveout : Bool) : StackVal :=
  if sv.useBlocks.back? == some (b, liveout) then sv
  else { sv with useBlocks := sv.useBlocks.push (b, liveout) }

/-- `hasAnyArgOp(v)`. -/
def hasAnyArgOp (op : Op) : Bool := op == .Arg || op == .ArgIntReg || op == .ArgFloatReg

/-- `stackalloc(f, spillLive)`: assigns the slots and returns the stack values live at the end
of each block. -/
def stackalloc (spillLive : Array (Array ID)) : M (Array (Array ID)) := do
  let c ← read
  let f ← getF
  let n := f.vidLast + 1
  let nb := f.bidLast + 1
  -- value states
  let mut sv : Array StackVal := Array.replicate n {}
  for bid in f.blocks do
    for vid in (f.getB bid).values do
      let v := f.getV vid
      let needSlot := c.slotType v.type && (← getHome vid).isNone && !(← rematerializeable v)
      sv := sv.modify vid fun x => { x with typ := v.type, needSlot, isArg := hasAnyArgOp v.op,
                                            defBlock := bid }
      if v.op == .StoreReg then sv := sv.modify v.args[0]! fun x => { x with spill := vid }
  -- liveness: use blocks
  for bid in f.blocks do
    let b := f.getB bid
    for sp in spillLive[bid]! do
      sv := sv.modify sp (·.addUseBlock bid true)
    for vid in b.values do
      let v := f.getV vid
      for i in [0:v.args.size] do
        let a := v.args[i]!
        let mut useBlock := bid
        let mut forceLiveout := false
        if v.op == .Phi then
          useBlock := b.preds[i]!.b
          forceLiveout := true
          let sp := sv[a]!.spill
          if sp != 0 then sv := sv.modify sp (·.addUseBlock useBlock true)
        if !sv[a]!.needSlot then continue
        sv := sv.modify a (·.addUseBlock useBlock forceLiveout)
  -- liveness: walk back from the uses to the definition
  let mut live : Array (Array ID) := Array.replicate nb #[]
  let push (live : Array (Array ID)) (b vid : ID) : Array (Array ID) :=
    if live[b]!.back? == some vid then live else live.modify b (·.push vid)
  let mut seen := SparseSet.new nb
  for vid in [0:n] do
    let x := sv[vid]!
    if !x.needSlot then continue
    seen := seen.clear
    let mut bq : Array ID := #[]
    for (b, lo) in x.useBlocks do
      if lo then live := push live b vid
      bq := bq.push b
    -- every block enters the queue once per predecessor edge of a newly seen block
    for _ in [0:x.useBlocks.size + f.blocks.foldl (fun s b => s + (f.getB b).preds.size) 0 + 1] do
      if bq.isEmpty then break
      let work := bq.back!
      bq := bq.pop
      if seen.contains work || work == x.defBlock then continue
      seen := seen.add work
      for e in (f.getB work).preds do
        live := push live e.b vid
        bq := bq.push e.b
  -- interference graph
  let mut interfere : Array (Array ID) := Array.replicate n #[]
  let mut ls := SparseSet.new n
  for bid in f.blocks do
    let b := f.getB bid
    ls := ls.clear.addAll live[bid]!.toList
    for k in [0:b.values.size] do
      let v := f.getV b.values[b.values.size - 1 - k]!
      if sv[v.id]!.needSlot then
        ls := ls.remove v.id
        for id in ls.contents do
          if c.env.typeOrder.eq sv[v.id]!.typ sv[id]!.typ || hasAnyArgOp v.op || sv[id]!.isArg then
            interfere := interfere.modify v.id (·.push id)
            interfere := interfere.modify id (·.push v.id)
      for a in v.args do
        if sv[a]!.needSlot then ls := ls.add a
      if hasAnyArgOp v.op && sv[v.id]!.needSlot then ls := ls.add v.id
  -- names
  let tabs := (← get).tabs
  let mut names : Array (Option SlotDef) := Array.replicate n none
  for (sref, vals) in f.names do
    let some name := tabs.slot? sref | fatal s!"slot s{sref} not defined"
    for vid in vals do
      let v := f.getV vid
      if v.op == .ArgIntReg || v.op == .ArgFloatReg then
        let some a := v.aux | fatal s!"v{vid} has nil Aux"
        let some { kind := .nameOff an off, .. } := tabs.aux? a | fatal s!"v{vid}: aux is not an AuxNameOffset"
        if name.name != an || name.off != off then continue
      else
        let cls := match tabs.aux? name.name with
          | some { kind := .name _ cls .., .. } => some cls
          | _ => none
        if cls == some .PPARAM && v.op != .Arg then continue
      if vid < names.size && names[vid]!.isNone then names := names.set! vid (some name)
  -- arguments
  for vid in (f.getB f.entry).values do
    let v := f.getV vid
    if !hasAnyArgOp v.op then continue
    let some a := v.aux | fatal s!"v{vid} has nil Aux"
    if v.op == .Arg then
      setHome vid (.slot { name := a, type := v.type, off := v.auxInt.toInt, splitOf := none, splitOffset := 0 })
  -- slots
  let mut locations : Std.HashMap TypeRef (Array SlotDef) := {}
  let mut slots : Array Int := Array.replicate n (-1)
  let mut used : Array Bool := Array.replicate n false
  for bid in f.blocks do
    for vid in (f.getB bid).values do
      let v := f.getV vid
      if !sv[vid]!.needSlot then continue
      if hasAnyArgOp v.op then continue
      let name := if v.op == .StoreReg then names[v.args[0]!]! else names[vid]!
      let mut named := false
      if let some name := name then
        if c.env.typeOrder.eq v.type name.type then
          let mut clash := false
          for id in interfere[vid]! do
            if let some (.slot h) ← getHome id then
              if h.name == name.name && h.off == name.off then
                clash := true
                break
          if !clash then
            setHome vid (.slot name)
            named := true
      if named then continue
      let key := c.env.typeLink v.type
      let mut locs := locations.getD key #[]
      for i in [0:locs.size] do used := used.set! i false
      for xid in interfere[vid]! do
        let s := slots[xid]!
        if s ≥ 0 then used := used.set! s.toNat true
      let i := ((Array.range locs.size).find? fun i => !used[i]!).getD locs.size
      if i == locs.size then
        let a ← newLocal v.pos v.type
        locs := locs.push { name := a, type := v.type, off := 0, splitOf := none, splitOffset := 0 }
        locations := locations.insert key locs
      setHome vid (.slot locs[i]!)
      slots := slots.set! vid i
  return live

end GoFV.Opt.Regalloc
