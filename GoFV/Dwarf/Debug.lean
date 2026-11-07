import GoFV.Gen.Frame
import GoFV.Dwarf.Const
import GoFV.Dwarf.Sym
import GoFV.SSA.Alloc
import GoFV.SSA.OpARM64
import GoFV.SSA.Analysis.CfgCache
import GoFV.Util.PdqSort
import GoFV.Util.SparseSet
import Std.Data.TreeMap

/-!
# `ssa.BuildFuncDebug` (E1, `docs/PASSES3.md`)

Port of the optimized-code location list builder `ssa.BuildFuncDebug`
(`cmd/compile/internal/ssa/debug.go`, go1.27.3) as `genssa` calls it
(`ssagen/ssa.go:7346-7356`, `Flag_locationlists` on, `-N` off, `base.Debug.LocationLists` 0, so no
logging and "run until converged"), with `ssagen.StackOffset` (`pgen.go:381-403`) as the
`stackOffset` callback:

* `PopulateABIInRegArgOps` (regabi): the slot canonicalizer (`slotCanonicalizer`), the dead
  `ArgIntReg`/`ArgFloatReg` values it synthesizes for the register pieces of the named input
  parameters (`f.OwnAux`'s ABI analysis, the same assignment `ABIAnalyzeFuncType(f.Type)`
  computes) that have none, homed in their parameter register, and the slots it appends to
  `f.Names`/`f.NamedValues`;
* the var/slot canonicalisation (`varParts`, `VarDef` stack-only vars, the `varOffset` sort with
  Go's `slices.SortFunc`, `GoFV.Util.PdqSort`), `initializeCache`, `valueNames`;
* `liveness` (`mergePredecessors`, `processValue`; the `abt.T` sets are persistent maps, which
  is what their applicative updates are), `buildLocationLists`, `updateVar`,
  `writePendingEntry` (the DWARF location expressions; `ARM64DWARFRegisters`).

The result is `FuncDebug.Slots`, `Vars`, `VarSlots` and `LocationLists` in SSA coordinates
(`BlockStart` = -10000, `BlockEnd` = -20000, `FuncEnd` = -30000 as value IDs). PC resolution
(`GetPC`), `RegOutputParams` (set by `buildssa`) and the DIE writer are not here.

The synthesized values take their IDs from `f.newValueNoBlock` (the free list first). The export
writes the free list sorted once `f.RegAlloc` is set (Go's order comes from a map iteration in
`regalloc`), so those IDs may differ from Go's; they are not observable in the result: the values
are zero-width and must-be-first, so their list entries start at `BlockStart`, and
`valueNames` is indexed by ID only.
-/

namespace GoFV.Dwarf

open GoFV.SSA
open GoFV.Gen (Env)
open GoFV.Util (SparseSet)

/-! ## Locations -/

/-- `ssa.VarLoc`: `RegisterSet` (bit = dense register number) and `StackOffset` (`some off` ⇔
`onStack()`, `off` = `stackOffsetValue()`). -/
structure VarLoc where
  regs : UInt64 := 0
  stack : Option Int := none
  deriving DecidableEq, Inhabited, Repr

namespace VarLoc

def absent (l : VarLoc) : Bool := l.regs == 0 && l.stack.isNone

/-- `loc.intersect(other)`. -/
def intersect (l o : VarLoc) : VarLoc :=
  { regs := l.regs &&& o.regs,
    stack := if l.stack.isSome && o.stack.isSome && l.stack == o.stack then l.stack else none }

end VarLoc

/-- `canMerge(pending, new)`. -/
def canMerge (p n : VarLoc) : Bool :=
  if p.absent && n.absent then true
  else if p.absent || n.absent then false
  else if p.stack.isSome && p.stack != n.stack then false
  else p.regs &&& n.regs == p.regs

/-- The set bits of `m`, lowest first (`bits.TrailingZeros64` loops, `pickReg`). -/
def bitsOf (m : UInt64) : Array Nat := Id.run do
  let mut out := #[]
  for i in [0:64] do
    if (m >>> i.toUInt64) &&& 1 != 0 then out := out.push i
  return out

/-- `firstReg(set)`: 0 for the empty set. -/
def firstReg (m : UInt64) : Nat := ((bitsOf m)[0]?).getD 0

@[inline] def bit (r : Nat) : UInt64 := (1 : UInt64) <<< r.toUInt64

/-- `ARM64DWARFRegisters[objNum]` (`obj/arm64/a.out.go`; Go's map lookup yields 0 for the
registers it lacks: `ZERO`, `SP`, `SB`). -/
def dwarfReg (obj : Int) : Nat :=
  if 8192 ≤ obj ∧ obj ≤ 8222 then (obj - 8192).toNat
  else if 8224 ≤ obj ∧ obj ≤ 8255 then (obj - 8224 + 64).toNat
  else 0

/-- `BlockStart.ID`, `BlockEnd.ID`, `FuncEnd.ID`. -/
def blockStartID : Int := -10000
def blockEndID : Int := -20000
def funcEndID : Int := -30000

/-- `abt.T` of `*liveSlot`: slot ID → location, iterated in ascending key order. -/
abbrev LiveMap := Std.TreeMap Nat VarLoc

/-- `BlockDebug`. -/
structure BlockDebug where
  startState : LiveMap := {}
  endState : LiveMap := {}
  lastCheckedTime : Int := 0
  lastChangedTime : Int := 0
  relevant : Bool := false
  everProcessed : Bool := false
  deriving Inhabited

/-- `pendingEntry`. -/
structure Pending where
  present : Bool := false
  startBlock : Int := 0
  startValue : Int := 0
  pieces : Array VarLoc := #[]
  deriving Inhabited

/-- `BuildFuncDebug`'s result. -/
structure DebugOut where
  /-- `f.Entry.ID` (`FuncDebug.EntryID`, set by `genssa`). -/
  entry : ID
  /-- `Slots` by `SlotID`. -/
  slots : Array SlotDef
  /-- `Vars` by `VarID` (`*ir.Name` aux numbers). -/
  vars : Array AuxRef
  varSlots : Array (Array Nat)
  /-- `LocationLists` by `VarID` (empty lists included). -/
  lists : Array (Array GoFV.Asm.LocEntry)
  /-- The values `PopulateABIInRegArgOps` synthesized, in entry-block order. -/
  synthesized : Array ID
  deriving Inhabited

/-! ## Names -/

/-- The `*ir.Name` of an aux number: `Sym().Name` and class. -/
def nameOf (tabs : Tables) (a : AuxRef) : Except String (GoStr × NameClass) :=
  match tabs.aux? a with
  | some { kind := .name sym cls .., .. } => pure (sym, cls)
  | _ => throw s!"aux a{a} is not an *ir.Name"

/-- `!ir.IsSynthetic(n) && IsVarWantedForDebug(n)`. -/
def wantedForDebug (tabs : Tables) (a : AuxRef) : Except String Bool := do
  let (sym, _) ← nameOf tabs a
  let b := sym.bytes
  if b.size == 0 then throw s!"IsSynthetic: name a{a} with an empty symbol"
  let c0 := b[0]!
  if c0 == '.'.toNat.toUInt8 || c0 == '~'.toNat.toUInt8 then return false
  let b := if c0 == '&'.toNat.toUInt8 then b.extract 1 b.size else b
  if b.size > 0 && b[0]! == '#'.toNat.toUInt8 then
    let p := "#yield".toUTF8
    return b.size ≥ p.size && b.extract 0 p.size == p
  return true

def slotDef (tabs : Tables) (s : SlotRef) : Except String SlotDef :=
  match tabs.slot? s with
  | some d => pure d
  | none => throw s!"no slot s{s}"

def typeSize (tabs : Tables) (t : TypeRef) : Except String Int :=
  match tabs.type? t with
  | some { size := some w, .. } => pure w
  | some _ => throw s!"type t{t}: size not calculated"
  | none => throw s!"no type t{t}"

/-- The top of a slot's `SplitOf` chain. -/
def topSlot (tabs : Tables) (s : SlotDef) : Except String SlotDef := do
  let mut s := s
  for _ in [0:typeFuel] do
    match s.splitOf with
    | none => return s
    | some p => s ← slotDef tabs p
  throw "SplitOf chain too long"

/-- `varOffset(slot)`. -/
def varOffset (tabs : Tables) (s : SlotDef) : Except String Int := do
  let mut off := s.off
  let mut s := s
  for _ in [0:typeFuel] do
    match s.splitOf with
    | none => return off
    | some p =>
      off := off + s.splitOffset
      s ← slotDef tabs p
  throw "SplitOf chain too long"

/-! ## `PopulateABIInRegArgOps` -/

/-- `slotKey`: name, offset, width, canonical index of `SplitOf`, `SplitOffset`. -/
abbrev SlotKeyT := AuxRef × Int × Int × Nat × Int

/-- `slotCanonicalizer` (`slkeys[0]` is the nil slot). -/
structure Canon where
  map : Std.HashMap SlotKeyT Nat := {}
  keys : Array SlotDef := #[default]

/-- `sc.lookup(ls)`: the canonical index and whether it was already present. -/
def Canon.lookup (tabs : Tables) : Nat → Canon → SlotDef → Except String (Nat × Bool × Canon)
  | 0, _, _ => throw "slotCanonicalizer: SplitOf chain too long"
  | fuel + 1, sc, ls => do
    let (split, sc) ← match ls.splitOf with
      | none => pure (0, sc)
      | some p => do
        let (i, _, sc) ← Canon.lookup tabs fuel sc (← slotDef tabs p)
        pure (i, sc)
    let k : SlotKeyT := (ls.name, ls.off, ← typeSize tabs ls.type, split, ls.splitOffset)
    if let some i := sc.map[k]? then return (i, true, sc)
    let rv := sc.keys.size
    return (rv, false, { map := sc.map.insert k rv, keys := sc.keys.push ls })

/-- `f.Names` (as slot values) and `f.NamedValues`, with the homes of the values. -/
structure NamesIn where
  f : Func
  names : Array SlotDef
  named : Std.HashMap SlotDef (Array ID)
  homes : Std.HashMap ID Location
  synthesized : Array ID

/-- `addToNV(v, sl)`. -/
def addToNV (s : NamesIn) (v : ID) (sl : SlotDef) : NamesIn :=
  match s.named[sl]? with
  | none => { s with names := s.names.push sl, named := s.named.insert sl #[v] }
  | some vs => if vs.contains v then s else { s with named := s.named.insert sl (vs.push v) }

/-- The `abi.ABIParamResultInfo` of `f.OwnAux` (`ABIAnalyze(fn.Type(), true)`, the assignment
`ABIAnalyzeFuncType(f.Type)` computes). -/
def ownABI (env : Env) : Except String CallABI := do
  let some a := env.f.ownAux | throw "PopulateABIInRegArgOps: no f.OwnAux"
  match (← env.auxDef a).kind with
  | .call _ (some info) => pure info
  | _ => throw s!"PopulateABIInRegArgOps: f.OwnAux a{a} has no ABI info"

/-- `isNamedRegParam(p)`. -/
def isNamedRegParam (tabs : Tables) (p : ABIParam) : Except String Bool := do
  let some a := p.name | return false
  let (sym, _) ← nameOf tabs a
  if sym.bytes == "_".toUTF8 then return false
  return !p.regs.isEmpty

/-- `PopulateABIInRegArgOps(f)`. -/
def populateABIInRegArgOps (env : Env) (s : NamesIn) : Except String NamesIn := do
  let tabs := env.tabs
  let info ← ownABI env
  let cfg ← GoFV.Gen.abiConfigOf env info.abi
  let mut sc : Canon := {}
  for sl in s.names do
    let (_, _, sc') ← Canon.lookup tabs typeFuel sc sl
    sc := sc'
  let mut s := s
  let some entry := s.f.block? s.f.entry | throw "no entry block"
  let pos : Pos := match entry.values[0]? >>= s.f.value? with
    | some v => v.pos
    | none => default
  for vid in entry.values do
    let some v := s.f.value? vid | throw s!"no value v{vid}"
    if v.op == .ArgIntReg || v.op == .ArgFloatReg then
      let some a := v.aux | throw s!"v{vid}: no aux"
      let .nameOff n off := (← env.auxDef a).kind | throw s!"v{vid}: aux is not an AuxNameOffset"
      let sl : SlotDef := { name := n, type := v.type, off, splitOf := none, splitOffset := 0 }
      let (idx, _, sc') ← Canon.lookup tabs typeFuel sc sl
      sc := sc'
      s := addToNV s vid sc.keys[idx]!
    else if v.op.call then break
  let mut newValues : Array ID := #[]
  for inp in info.inParams do
    if !(← isNamedRegParam tabs inp) then continue
    let some n := inp.name | continue
    let (types, offsets) ← GoFV.Gen.registerTypesAndOffsets env inp
    for h : k in [0:types.size] do
      let t := types[k]
      let some o := offsets[k]? | throw s!"PopulateABIInRegArgOps: no offset {k}"
      let piece : SlotDef := { name := n, type := t, off := o, splitOf := none, splitOffset := 0 }
      let (_, found, sc') ← Canon.lookup tabs typeFuel sc piece
      sc := sc'
      if found then continue
      let some reg := inp.regs[k]? | throw s!"PopulateABIInRegArgOps: no register {k}"
      let (op, auxInt) := argOpAndRegisterFor cfg reg
      let (f, id) := s.f.newValueNoBlock op t pos
      let f := f.modV id fun v => { v with auxInt, block := s.f.entry }
      s := { s with f }
      newValues := newValues.push id
      s := addToNV s id piece
      let fi := cfg.floatIndexFor reg
      let r ← if fi >= 0 then
          match ARM64.paramFloatReg[fi.toNat]? with
          | some r => pure r
          | none => throw s!"no float param register {fi}"
        else match ARM64.paramIntReg[reg]? with
          | some r => pure r
          | none => throw s!"no int param register {reg}"
      s := { s with homes := s.homes.insert id (.reg r) }
  let f := s.f.modB s.f.entry fun b => { b with values := newValues ++ b.values }
  return { s with f, synthesized := newValues }

/-! ## The analysis state -/

structure Ctx where
  f : Func
  tabs : Tables
  homes : Std.HashMap ID Location
  /-- `ssagen.StackOffset`. -/
  stackOffset : SlotDef → Except String Int

structure DState where
  slots : Array SlotDef
  slotVars : Array Nat
  varSlots : Array (Array Nat)
  varParts : Std.HashMap AuxRef (Array Nat)
  valueNames : Array (Array Nat)
  curSlots : Array VarLoc
  curRegs : Array (Array Nat)
  changedVars : SparseSet
  changedSlots : SparseSet
  pending : Array Pending
  lists : Array (Array GoFV.Asm.LocEntry)
  bd : Array BlockDebug
  alloc : Array Bool
  deriving Inhabited

abbrev DbgM := StateT DState (Except String)

namespace DbgM

def value (c : Ctx) (id : ID) : DbgM Value :=
  match c.f.value? id with | some v => pure v | none => throw s!"no value v{id}"

def block (c : Ctx) (id : ID) : DbgM Block :=
  match c.f.block? id with | some b => pure b | none => throw s!"no block b{id}"

def bd (b : ID) : DbgM BlockDebug := return (← get).bd[b]!

def modBd (b : ID) (g : BlockDebug → BlockDebug) : DbgM Unit :=
  modify fun s => { s with bd := s.bd.modify b g }

/-- `reg, _ := f.getHome(v.ID).(*Register)`. -/
def homeReg (c : Ctx) (v : ID) : Option Nat :=
  match c.homes[v]? with | some (.reg r) => some r | _ => none

/-- `f.getHome(v.ID).(LocalSlot)`. -/
def homeSlot (c : Ctx) (v : ID) : DbgM SlotDef :=
  match c.homes[v]? with
  | some (.slot k) => pure k
  | l => throw s!"v{v}: home {repr l} is not a LocalSlot"

/-- `stateAtPC.reset(live)`. -/
def reset (live : LiveMap) : DbgM Unit := modify fun s => Id.run do
  let mut slots := s.curSlots.map fun _ => {}
  let mut regs := s.curRegs.map fun _ => #[]
  for (k, l) in live.toList do
    slots := slots.set! k l
    for r in bitsOf l.regs do regs := regs.modify r (·.push k)
  return { s with curSlots := slots, curRegs := regs }

def addChangedVar (slot : Nat) : DbgM Unit := modify fun s =>
  { s with changedVars := s.changedVars.add s.slotVars[slot]! }

/-- `mergePredecessors(b, blockLocs, previousBlock, forLocationLists)`. -/
def mergePredecessors (c : Ctx) (b : ID) (prev : Option ID) (forLL : Bool) :
    DbgM (LiveMap × Bool) := do
  let blk ← block c b
  let locs ← bd b
  let mut blockChanged := !locs.everProcessed
  let updating := locs.everProcessed
  let st ← get
  let mut preds : Array ID := #[]
  for e in blk.preds do
    if st.alloc[e.b]! && st.bd[e.b]!.everProcessed then preds := preds.push e.b
  modBd b fun x => { x with everProcessed := true }
  modify fun s => { s with changedVars := s.changedVars.clear }
  let markChangedVars (slots merged : LiveMap) : DbgM Unit := do
    if !forLL then return
    for (k, v) in slots.toList do
      match merged.get? k with
      | some m => if v != m then addChangedVar k
      | none => addChangedVar k
  let rst (ours : LiveMap) (changed : Bool) : DbgM Unit := do
    if !(forLL || changed) then return
    reset ours
  if preds.isEmpty then
    if let some p := prev then
      throw s!"block b{b} with no predecessors is not first block, has previous b{p}"
    rst {} blockChanged
    return ({}, blockChanged)
  let l0 ← bd preds[0]!
  let p0 := l0.endState
  if preds.size == 1 then
    if let some pb := prev then
      if preds[0]! != pb then markChangedVars (← bd pb).endState p0
    modBd b fun x => { x with startState := p0 }
    blockChanged := blockChanged || l0.lastChangedTime > locs.lastCheckedTime
    rst p0 blockChanged
    return (p0, blockChanged)
  if updating then
    let mut i := preds.size
    while i > 0 do
      i := i - 1
      let pred := preds[i]!
      if (← bd pred).lastChangedTime > locs.lastCheckedTime then continue
      preds := preds.set! i preds.back!
      preds := preds.pop
    if preds.isEmpty then
      blockChanged := false
      rst locs.startState blockChanged
      if let some pb := prev then markChangedVars (← bd pb).endState locs.startState
      return (locs.startState, blockChanged)
  let mut baseID := preds[0]!
  let mut baseState := p0
  for pred in preds.extract 1 preds.size do
    let es := (← bd pred).endState
    if es.size < baseState.size then
      baseState := es
      baseID := pred
  reset {}
  let ss0 := (← bd b).startState
  let mut newState := if updating then ss0 else baseState
  let st ← get
  let mut slotLocs := st.curSlots
  let mut regs := st.curRegs
  for (k, x0) in newState.toList do
    let mut x := x0
    for other in preds do
      if !updating && other == baseID then continue
      match st.bd[other]!.endState.get? k with
      | none => x := {}; break
      | some y =>
        x := x.intersect y
        if x.absent then
          x := {}
          break
    if x.absent then
      if !x0.absent then
        blockChanged := true
        newState := newState.erase k
      slotLocs := slotLocs.set! k {}
      continue
    if x != x0 then
      blockChanged := true
      newState := newState.insert k x
    slotLocs := slotLocs.set! k x
    for r in bitsOf x.regs do regs := regs.modify r (·.push k)
  modify fun s => { s with curSlots := slotLocs, curRegs := regs }
  if let some pb := prev then markChangedVars (← bd pb).endState newState
  modBd b fun x => { x with startState := newState }
  return (newState, blockChanged)

/-- `processValue(v, vSlots, vReg)`: whether some slot was set. -/
def processValue (c : Ctx) (v : Value) (vSlots : Array Nat) (vReg : Option Nat) : DbgM Bool := do
  let mut changed := false
  let clob := v.op.regInfo.clobbers
  if clob.v2 != 0 then throw s!"v{v.id}: clobbers beyond register 63"
  let setSlot (slot : Nat) (loc : VarLoc) : DbgM Unit := modify fun s =>
    { s with changedVars := s.changedVars.add s.slotVars[slot]!,
             changedSlots := s.changedSlots.add slot, curSlots := s.curSlots.set! slot loc }
  for r in bitsOf clob.v1 do
    for slot in (← get).curRegs[r]! do
      let last := (← get).curSlots[slot]!
      if last.absent then throw s!"at v{v.id}: slot {slot} in register {r} with no location entry"
      setSlot slot { regs := last.regs &&& ~~~(bit r), stack := last.stack }
      changed := true
    modify fun s => { s with curRegs := s.curRegs.set! r #[] }
  if v.op == .VarDef then
    let some n := v.aux | throw s!"v{v.id}: VarDef without aux"
    if ← wantedForDebug c.tabs n then
      let some parts := (← get).varParts[n]? | throw s!"v{v.id}: no varParts for a{n}"
      let slotID := parts[0]!
      let off ← c.stackOffset (← get).slots[slotID]!
      setSlot slotID { regs := 0, stack := some off }
      changed := true
  else if v.op == .Arg then
    let home ← homeSlot c v.id
    let off ← c.stackOffset home
    for slot in vSlots do
      setSlot slot { regs := 0, stack := some off }
      changed := true
  else if v.op == .StoreReg then
    let home ← homeSlot c v.id
    let off ← c.stackOffset home
    for slot in vSlots do
      let last := (← get).curSlots[slot]!
      if last.absent then break
      setSlot slot { regs := last.regs, stack := some off }
      changed := true
  else if let some r := vReg then
    for slot in (← get).curRegs[r]! do
      let last := (← get).curSlots[slot]!
      setSlot slot { regs := last.regs &&& ~~~(bit r), stack := last.stack }
      changed := true
    modify fun s => { s with curRegs := s.curRegs.set! r vSlots }
    for slot in vSlots do
      let last := (← get).curSlots[slot]!
      setSlot slot { regs := bit r ||| last.regs, stack := last.stack }
      changed := true
  return changed

/-- `liveness()`. -/
def liveness (c : Ctx) : DbgM Unit := do
  let (po, _) := c.f.postorder
  let mut counterTime : Int := 1
  let mut converged := false
  let mut k := 0
  -- every unconverged pass shrinks some block's start state (finite), so the bound is not hit
  for _ in [0:100000] do
    if converged then break
    converged := true
    let mut i := po.size
    while i > 0 do
      i := i - 1
      let b := po[i]!
      modify fun s => { s with alloc := s.alloc.set! b true }
      let (startState, blockChanged) ← mergePredecessors c b none false
      modBd b fun x => { x with lastCheckedTime := counterTime }
      counterTime := counterTime + 1
      if blockChanged then
        converged := false
        let mut changed := false
        modify fun s => { s with changedSlots := s.changedSlots.clear }
        for vid in (← block c b).values do
          let v ← value c vid
          let mut slots := (← get).valueNames[vid]!
          let source : Option ID ← match v.op with
            | .StoreReg => pure v.args[0]?
            | .LoadReg => do
              let some a := v.args[0]? | pure none
              let av ← value c a
              match av.op with
              | .Arg | .Phi => pure (some a)
              | .StoreReg => pure av.args[0]?
              | _ => pure none
            | _ => pure none
          if let some src := source then
            if k == 0 then
              slots := slots ++ (← get).valueNames[src]!
              modify fun s => { s with valueNames := s.valueNames.set! vid slots }
          let ch ← processValue c v slots (homeReg c vid)
          changed := changed || ch
        modBd b fun x => { x with relevant := x.relevant || changed }
        if !changed then
          modBd b fun x => { x with endState := startState }
        else
          let mut ss := startState
          let st ← get
          for id in st.changedSlots.contents do
            let slotLoc := st.curSlots[id]!
            if slotLoc.absent then
              ss := ss.erase id
              continue
            if ss.get? id != some slotLoc then ss := ss.insert id slotLoc
          modBd b fun x => { x with endState := ss }
        modBd b fun x => { x with lastChangedTime := counterTime }
      counterTime := counterTime + 1
    k := k + 1
  if !converged then throw "liveness did not converge"

/-- `writePendingEntry(varID, endBlock, endValue)`. -/
def writePendingEntry (c : Ctx) (varID : Nat) (endBlock endValue : Int) : DbgM Unit := do
  let st ← get
  let p := st.pending[varID]!
  if !p.present then return
  if p.startBlock == endBlock && p.startValue == endValue then return
  let vs := st.varSlots[varID]!
  let mut expr := ByteArray.empty
  for h : i in [0:vs.size] do
    let slotID := vs[i]
    let loc := p.pieces[i]!
    let slot := st.slots[slotID]!
    if !loc.absent then
      if let some off := loc.stack then
        if off == 0 then expr := expr.push DW_OP_call_frame_cfa.toUInt8
        else expr := DwM.appendSleb128 (expr.push DW_OP_fbreg.toUInt8) off
      else
        let some r := ARM64.registers[firstReg loc.regs]? | throw "no register"
        let regnum := dwarfReg r.objNum
        if regnum < 32 then expr := expr.push (DW_OP_reg0 + regnum).toUInt8
        else expr := DwM.appendUleb128 (expr.push DW_OP_regx.toUInt8) regnum
    if vs.size > 1 then
      let w ← typeSize c.tabs slot.type
      expr := DwM.appendUleb128 (expr.push DW_OP_piece.toUInt8) (w % (2 ^ 64 : Nat)).toNat
  let e : GoFV.Asm.LocEntry :=
    { startBlock := p.startBlock, startValue := p.startValue, endBlock, endValue, expr }
  modify fun s => { s with lists := s.lists.modify varID (·.push e) }

/-- `updateVar(varID, b, v)`. -/
def updateVar (c : Ctx) (varID : Nat) (b : ID) (v : Int) : DbgM Unit := do
  let st ← get
  let cur := st.curSlots
  let vs := st.varSlots[varID]!
  let empty := vs.all fun s => cur[s]!.absent
  if empty then
    writePendingEntry c varID b v
    modify fun s => { s with pending := s.pending.modify varID fun p =>
      { present := false, startBlock := 0, startValue := 0, pieces := p.pieces.map fun _ => {} } }
    return
  let p := st.pending[varID]!
  if p.present then
    let mut merge := true
    for h : i in [0:vs.size] do
      if !canMerge p.pieces[i]! cur[vs[i]]! then
        merge := false
        break
    if merge then return
  writePendingEntry c varID b v
  let np : Pending :=
    { present := true, startBlock := b, startValue := v, pieces := vs.map fun s => cur[s]! }
  modify fun s => { s with pending := s.pending.set! varID np }

def updateChanged (c : Ctx) (b : ID) (v : Int) : DbgM Unit := do
  for varID in (← get).changedVars.contents do updateVar c varID b v
  modify fun s => { s with changedVars := s.changedVars.clear }

/-- `buildLocationLists(blockLocs)`. -/
def buildLocationLists (c : Ctx) : DbgM Unit := do
  let mut prevBlock : Option ID := none
  for b in c.f.blocks do
    if !(← get).alloc[b]! then throw s!"buildLocationLists: block b{b} not reached by liveness"
    discard <| mergePredecessors c b prevBlock true
    updateChanged c b blockStartID
    if !(← bd b).relevant then continue
    let blk ← block c b
    let mustBeFirst (v : Value) : Bool :=
      v.op == .Phi || v.op == .ARM64LoweredGetClosurePtr || v.op == .ArgIntReg ||
        v.op == .ArgFloatReg
    let blockPrologComplete (v : Value) : Bool :=
      if b != c.f.entry then !v.op.zeroWidth else v.op == .InitMem
    for vid in blk.values do
      let v ← value c vid
      if blockPrologComplete v then break
      if !mustBeFirst v && v.op != .Arg then continue
      let changed ← processValue c v (← get).valueNames[vid]! (homeReg c vid)
      if changed then updateChanged c v.block blockStartID
    let mut zeroWidthPending := false
    let mut prologComplete := false
    for vid in blk.values do
      let v ← value c vid
      if blockPrologComplete v then prologComplete := true
      let changed ← processValue c v (← get).valueNames[vid]! (homeReg c vid)
      if v.op.zeroWidth then
        if prologComplete && mustBeFirst v then
          throw s!"Unexpected placement of op v{vid} appearing after non-pseudo-op at beginning of block b{b}"
        if changed then
          if mustBeFirst v || v.op == .Arg then continue
          zeroWidthPending := true
        continue
      if !changed && !zeroWidthPending then continue
      zeroWidthPending := false
      updateChanged c v.block vid
    for varID in (← get).changedVars.contents do updateVar c varID b blockEndID
    prevBlock := some b
  for varID in [0:(← get).lists.size] do
    writePendingEntry c varID (-1) funcEndID

end DbgM

/-! ## `BuildFuncDebug` -/

/-- `ssagen.StackOffset(slot)` (`pgen.go:381`) over the frame after `AllocFrame` (`Dcl` with
frame offsets and the `outregs` flag, by `.prog` name number). -/
def stackOffsetOf (env : Env) (frame : Std.HashMap Nat (Int × Bool)) (fixedFrameSize : Int)
    (framePointer : Bool) (s : SlotDef) : Except String Int := do
  let (_, cls) ← nameOf env.tabs s.name
  let frameOf : Except String (Int × Bool) :=
    match env.nameOfAux? s.name >>= (frame[·]?) with
    | some x => pure x
    | none => throw s!"StackOffset: name a{s.name} not in Dcl"
  let auto (o : Int) : Int :=
    let o := if fixedFrameSize == 0 then o - 8 else o
    if framePointer then o - 8 else o
  let off ← match cls with
    | .PPARAM | .PPARAMOUT =>
      let (o, outregs) ← frameOf
      pure (if outregs then auto o else o + fixedFrameSize)
    | .PAUTO => do pure (auto (← frameOf).1)
    | _ => pure 0
  return off + s.off

private def configInt (env : Env) (k : String) : Except String Int :=
  match env.config? k with
  | some #[.word w] => match w.toInt? with
    | some n => pure n
    | none => throw s!"config {k}: not a number"
  | _ => throw s!"config {k}: missing"

/-- `BuildFuncDebug(ctxt, f, 0, StackOffset, rval)` on the function after `trim` (`genssa` does
not change the function before it) and `dcl`, the `Dcl` after `AllocFrame` (frame offsets and
flags; the `frame` section's `out` and `opt` lines). -/
def buildFuncDebug (env : Env) (dcl : Array GoFV.Asm.DclEntry) : Except String DebugOut := do
  let tabs := env.tabs
  let f0 := env.f
  if f0.low.regAlloc.isNone then throw "BuildFuncDebug on a function that has not been fully processed"
  let fixed ← configInt env "fixedframesize"
  let fp := (← configInt env "framepointer") != 0
  let frame : Std.HashMap Nat (Int × Bool) :=
    dcl.foldl (fun m d => m.insert d.name (d.off, d.flags.outregs)) {}
  -- f.Names, f.NamedValues, f.RegAlloc
  let mut names : Array SlotDef := #[]
  let mut named : Std.HashMap SlotDef (Array ID) := {}
  for (s, vs) in f0.names do
    let d ← slotDef tabs s
    names := names.push d
    named := named.insert d vs
  for (k, vs) in f0.namedx do named := named.insert k vs
  let mut homes : Std.HashMap ID Location := {}
  if let some (_, es) := f0.low.regAlloc then
    for (id, l) in es do homes := homes.insert id l
  -- regabi: PopulateABIInRegArgOps
  let s ← populateABIInRegArgOps env { f := f0, names, named, homes, synthesized := #[] }
  let f := s.f
  -- vars and slots
  let mut varParts : Std.HashMap AuxRef (Array Nat) := {}
  let mut slots : Array SlotDef := #[]
  let mut vars : Array AuxRef := #[]
  for h : i in [0:s.names.size] do
    let slot := s.names[i]
    slots := slots.push slot
    if !(← wantedForDebug tabs slot.name) then continue
    let top ← topSlot tabs slot
    if !varParts.contains top.name then vars := vars.push top.name
    varParts := varParts.insert top.name ((varParts.getD top.name #[]).push i)
  for b in f.blocks do
    let some blk := f.block? b | throw s!"no block b{b}"
    for vid in blk.values do
      let some v := f.value? vid | throw s!"no value v{vid}"
      if v.op == .VarDef then
        let some n := v.aux | throw s!"v{vid}: VarDef without aux"
        if !(← wantedForDebug tabs n) then continue
        if !varParts.contains n then
          slots := slots.push { name := n, type := v.type, off := 0, splitOf := none, splitOffset := 0 }
          varParts := varParts.insert n #[slots.size - 1]
          vars := vars.push n
  let mut varSlots : Array (Array Nat) := #[]
  let mut slotVars : Array Nat := Array.replicate slots.size 0
  let offs ← slots.mapM (varOffset tabs)
  for h : varID in [0:vars.size] do
    let n := vars[varID]
    let parts := GoFV.Util.PdqSort.sortFunc
      (fun a b => let x := offs[a]!; let y := offs[b]!; if x < y then -1 else if x > y then 1 else 0)
      (varParts.getD n #[])
    varParts := varParts.insert n parts
    varSlots := varSlots.push parts
    for sl in parts do slotVars := slotVars.set! sl varID
  -- initializeCache, valueNames
  let nv := f.vidLast + 1
  let mut valueNames : Array (Array Nat) := Array.replicate nv #[]
  for h : i in [0:s.names.size] do
    let slot := s.names[i]
    if !(← wantedForDebug tabs slot.name) then continue
    for v in s.named.getD slot #[] do
      if v < nv then valueNames := valueNames.modify v (·.push i)
      else throw s!"NamedValues: v{v} out of range"
  let nb := f.bidLast + 1
  let st : DState :=
    { slots, slotVars, varSlots, varParts, valueNames,
      curSlots := Array.replicate slots.size {}, curRegs := Array.replicate ARM64.registers.size #[],
      changedVars := SparseSet.new vars.size, changedSlots := SparseSet.new slots.size,
      pending := varSlots.map fun vs => { pieces := vs.map fun _ => {} },
      lists := Array.replicate vars.size #[],
      bd := Array.replicate nb {}, alloc := Array.replicate nb false }
  let c : Ctx := { f, tabs, homes := s.homes, stackOffset := stackOffsetOf env frame fixed fp }
  let ((), st) ← (do DbgM.liveness c; DbgM.buildLocationLists c).run st
  return { entry := f.entry, slots := st.slots, vars, varSlots := st.varSlots, lists := st.lists,
           synthesized := s.synthesized }

end GoFV.Dwarf
