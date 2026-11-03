import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.ABI
import GoFV.SSA.OpARM64
import GoFV.SSA.RegARM64
import GoFV.SSA.RegMask
import GoFV.SSA.TypePred
import GoFV.SSA.Analysis.CfgCache
import GoFV.Util.SparseMapPos
import GoFV.Util.SparseSet

/-!
# Register allocator state

The state of `regAllocState` (`regalloc.go`, go1.27.3, lines 274-410) and its register
primitives: `freeReg`, `freeRegs`, `assignReg`, `setOrig`, `setHome`, `compatRegs`, `regspec`
(with the lazy `AuxCall.Reg`/`ResultReg` mutation of `op.go:137-190`), `rematerializeable` and
the desired-register lists (`desiredState`, lines 3423-3553).

Values are IDs; `0` is Go's `nil` (IDs start at 1). `f.RegAlloc` is kept as `homes` (an array
indexed by value ID, extended with `none` by `setHome`) and converted to `Lowered.regAlloc` at the
end of the pass.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA GoFV.Util

/-- Fixed configuration of one run. -/
structure Cfg where
  env : PassEnv
  /-- The input tables (types never change during regalloc). -/
  tabs : Tables
  numRegs : Nat
  spReg : Nat
  sbReg : Nat
  gReg : Nat
  zeroReg : Nat
  hasGReg : Bool
  allocatable : RegMask
  gpMask : RegMask
  fpMask : RegMask
  intParamRegs : Array Nat
  floatParamRegs : Array Nat
  /-- `types.TypeMem`, `TypeFlags`, `TypeVoid`, `TypeInt128`. -/
  mem : TypeRef
  flags : TypeRef
  void : TypeRef
  int128 : TypeRef
  doClobber : Bool

/-- One `use` record: distance from the block start and position of the use. -/
structure UseRec where
  dist : Int
  pos : Pos
  deriving Inhabited

/-- `valState` (`regalloc.go:286`), for pre-regalloc values. `uses` is Go's linked list, head
first (nondecreasing distances). -/
structure ValState where
  regs : RegMask := {}
  uses : List UseRec := []
  spill : ID := 0
  restoreMin : Int := 0
  restoreMax : Int := 0
  needReg : Bool := false
  remat : Bool := false
  deriving Inhabited

/-- `regState`: original value and its current copy in a register (`0`: free). -/
structure RegState where
  v : ID := 0
  c : ID := 0
  deriving Inhabited

structure EndReg where
  r : Nat
  v : ID
  c : ID
  deriving Inhabited

structure StartReg where
  r : Nat
  v : ID
  c : ID
  pos : Pos
  deriving Inhabited

/-- `liveInfo`. -/
structure LiveInfo where
  id : ID
  dist : Int
  pos : Pos
  deriving Inhabited

/-- Four registers in priority order, `noReg` for unused slots. -/
abbrev Regs4 := Array Nat

def noRegs4 : Regs4 := #[RegMask.noReg, RegMask.noReg, RegMask.noReg, RegMask.noReg]

/-- `desiredState` (`regalloc.go:3423`). -/
structure Desired where
  entries : Array (ID × Regs4) := #[]
  avoid : RegMask := {}
  deriving Inhabited

namespace Desired

/-- `get(vid)`. -/
def get (d : Desired) (vid : ID) : Regs4 :=
  match d.entries.find? (·.1 == vid) with
  | some (_, rs) => rs
  | none => noRegs4

/-- `add(vid, r)`. -/
def add (d : Desired) (vid : ID) (r : Nat) : Desired :=
  let d := { d with avoid := d.avoid.addReg r }
  match d.entries.findIdx? (·.1 == vid) with
  | none => { d with entries := d.entries.push (vid, #[r, RegMask.noReg, RegMask.noReg, RegMask.noReg]) }
  | some i =>
    let rs := d.entries[i]!.2
    if rs[0]! == r then d else
    -- found at `j ≥ 1`: `copy(regs[1:], regs[:j])`; else `copy(regs[1:], regs[:])` (`j = 3`)
    let j := ((List.range' 1 3).find? (rs[·]! == r)).getD 3
    let out := (Array.range 4).map fun k => if k == 0 then r else if k ≤ j then rs[k - 1]! else rs[k]!
    { d with entries := d.entries.set! i (vid, out) }

/-- `addList(vid, regs)`: in reverse, so that the first entry ends up highest priority. -/
def addList (d : Desired) (vid : ID) (rs : Regs4) : Desired := Id.run do
  let mut d := d
  for k in [0:4] do
    let r := rs[3 - k]!
    if r != RegMask.noReg then d := d.add vid r
  return d

/-- `clobber(m)`. -/
def clobber (d : Desired) (m : RegMask) : Desired := Id.run do
  let mut es := d.entries
  let mut i := 0
  for _ in [0:d.entries.size + 1] do
    if i ≥ es.size then break
    let (id, rs) := es[i]!
    let kept := rs.filter fun r => r != RegMask.noReg && !m.hasReg r
    if kept.isEmpty then
      es := (es.set! i es[es.size - 1]!).pop
      continue
    es := es.set! i (id, kept ++ Array.replicate (4 - kept.size) RegMask.noReg)
    i := i + 1
  return { entries := es, avoid := d.avoid.minus m }

/-- `remove(vid)`: swap-remove the entry and return its registers. -/
def remove (d : Desired) (vid : ID) : Regs4 × Desired :=
  match d.entries.findIdx? (·.1 == vid) with
  | none => (noRegs4, d)
  | some i =>
    let rs := d.entries[i]!.2
    let es := d.entries
    (rs, { d with entries := (es.set! i es[es.size - 1]!).pop })

/-- `merge(x)`: whether the avoid mask changed. -/
def merge (d x : Desired) : Bool × Desired :=
  let old := d.avoid
  let d := { d with avoid := d.avoid.union x.avoid }
  let d := x.entries.foldl (fun d (id, rs) => d.addList id rs) d
  (old != d.avoid, d)

end Desired

/-- The cached loop nest in the form regalloc reads it: `b2l` by block ID (`b2lSize` slots). -/
structure Nest where
  nest : LoopNest
  b2l : Array (Option Nat)

namespace Nest

def ofLoopNest (ln : LoopNest) : Nest :=
  { nest := ln
    b2l := ln.b2l.foldl (fun a (b, l) => if b < a.size then a.set! b (some l) else a)
      (Array.replicate ln.b2lSize none) }

/-- `loopnest.b2l[b]` (Go panics on an index past the slice). -/
def at? (n : Nest) (b : ID) : Except String (Option Nat) :=
  if h : b < n.b2l.size then pure n.b2l[b] else throw s!"loopnest.b2l[b{b}] out of range"

def loop (n : Nest) (i : Nat) : GoFV.SSA.Loop := n.nest.loops[i]!

end Nest

/-- `regAllocState` plus the function and tables being rewritten. -/
structure St where
  f : Func
  tabs : Tables
  /-- `f.RegAlloc`. -/
  homes : Array (Option Location) := #[]
  /-- `f.tempRegs` in insertion order (keys are distinct). -/
  tempRegs : Option (Array (ID × Nat)) := none
  values : Array ValState
  /-- `orig` (0 = nil). -/
  orig : Array ID
  regs : Array RegState
  nospill : RegMask := {}
  used : RegMask := {}
  usedSinceBlockStart : RegMask := {}
  tmpused : RegMask := {}
  curBlock : ID := 0
  endRegs : Array (Array EndReg) := #[]
  startRegs : Array (Array StartReg) := #[]
  startRegsMask : RegMask := {}
  spillLive : Array (Array ID) := #[]
  /-- `copies`: by value ID, `some used` for the opportunistic copies. -/
  copies : Array (Option Bool) := #[]
  nest : Option Nest := none
  blockOrder : Array Nat := #[]
  nextCall : Array Int := #[]
  curIdx : Nat := 0
  sp : ID := 0
  sb : ID := 0
  live : Option (Array (Array LiveInfo)) := none
  desired : Array Desired := #[]
  sdom : Analysis.SparseTree := #[]
  /-- `len(curfn.Dcl)`: the number of the next `.autotmp_<n>`. -/
  dcl : Nat := 0

abbrev M := ReaderT Cfg (StateT St (Except String))

@[inline] def fatal {α} (msg : String) : M α := throw msg

@[inline] def liftE {α} (x : Except String α) : M α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

@[inline] def getF : M Func := return (← get).f
@[inline] def modF (g : Func → Func) : M Unit := modify fun s => { s with f := g s.f }
@[inline] def val (id : ID) : M Value := return (← get).f.getV id
@[inline] def blk (id : ID) : M Block := return (← get).f.getB id
@[inline] def vs (id : ID) : M ValState := return (← get).values[id]!
@[inline] def modVS (id : ID) (g : ValState → ValState) : M Unit :=
  modify fun s => { s with values := s.values.modify id g }

/-! ## Types -/

def kind? (c : Cfg) (t : TypeRef) : Option TypeKind := (c.tabs.type? t).map (·.kind)

/-- `t.IsTuple()`. -/
def Cfg.isTuple (c : Cfg) (t : TypeRef) : Bool := kind? c t == some .TUPLE
/-- `t.IsResults()`. -/
def Cfg.isResults (c : Cfg) (t : TypeRef) : Bool := kind? c t == some .RESULTS
def Cfg.isMemory (c : Cfg) (t : TypeRef) : Bool := c.tabs.isMemory c.mem t

/-- `v.needRegister()`. -/
def Cfg.needRegister (c : Cfg) (t : TypeRef) : Bool :=
  !c.isMemory t && t != c.void && t != c.flags && !c.isTuple t

/-- The `needSlot` type test of `stackalloc` (tuples are not excluded there). -/
def Cfg.slotType (c : Cfg) (t : TypeRef) : Bool := !c.isMemory t && t != c.void && t != c.flags

/-- `s.compatRegs(t)` (no SIMD types without the experiment; `fp32`/`fp64` masks are empty on
arm64). -/
def Cfg.compatRegs (c : Cfg) (t : TypeRef) : RegMask :=
  if c.isTuple t || t == c.flags then {} else
  let k := kind? c t
  let m := if k == some .FLOAT32 || k == some .FLOAT64 || t == c.int128 then c.fpMask else c.gpMask
  m.inter c.allocatable

/-! ## Values -/

/-- `v.rematerializeable()`. -/
def rematerializeable (v : Value) : M Bool := do
  if !v.op.rematerializeable then return false
  for a in v.args do
    if !(← val a).op.fixedReg then return false
  return true

/-- `f.setHome(v, loc)`. -/
def setHome (id : ID) (loc : Location) : M Unit :=
  modify fun s => { s with homes := Func.tabPut s.homes id loc }

/-- `f.getHome(vid)`. -/
def getHome (id : ID) : M (Option Location) := return ((← get).homes[id]?).join

/-- The register home of `id` (Go's `getHome(id).(*Register)`, which panics otherwise). -/
def homeReg (id : ID) : M Nat := do
  match ← getHome id with
  | some (.reg r) => return r
  | _ => fatal s!"v{id} has no register home"

/-- `s.setOrig(c, v)`. -/
def setOrig (c v : ID) : M Unit := do
  let s ← get
  let o := if v < s.orig.size then s.orig[v]! else 0
  let orig := if c < s.orig.size then s.orig else s.orig ++ Array.replicate (c + 1 - s.orig.size) 0
  if orig[c]! != 0 then fatal s!"orig value set twice v{c} v{v}"
  set { s with orig := orig.set! c o }

@[inline] def origOf (id : ID) : M ID := do
  let s ← get
  return if id < s.orig.size then s.orig[id]! else 0

def isGReg (c : Cfg) (r : Nat) : Bool := c.hasGReg && c.gReg == r

/-! ## Registers -/

/-- `s.freeReg(r)`. -/
def freeReg (r : Nat) : M Unit := do
  let c ← read
  if !c.allocatable.hasReg r && !isGReg c r then return
  let s ← get
  let v := s.regs[r]!.v
  if v == 0 then fatal s!"tried to free an already free register {r}"
  set { s with regs := s.regs.set! r {}, used := s.used.removeReg r
               values := s.values.modify v fun x => { x with regs := x.regs.removeReg r } }

/-- `s.freeRegs(m)`. -/
def freeRegs (m : RegMask) : M Unit := do
  for _ in [0:130] do
    match (m.inter (← get).used).pick? with
    | some r => freeReg r
    | none => return

/-- `s.assignReg(r, v, c)`. -/
def assignReg (r : Nat) (v c : ID) : M Unit := do
  let cfg ← read
  modVS v fun x => { x with regs := x.regs.addReg r }
  setHome c (.reg r)
  if !cfg.allocatable.hasReg r && !isGReg cfg r then return
  let s ← get
  if s.regs[r]!.v != 0 then
    fatal s!"tried to assign register {r} to v{v}/v{c} but it is already used by v{s.regs[r]!.v}"
  set { s with regs := s.regs.set! r { v, c }, used := s.used.addReg r }

@[inline] def pickReg (m : RegMask) : M Nat := do
  match m.pick? with
  | some r => return r
  | none => fatal "can't pick a register from an empty set"

/-! ## Value construction (`func.go`, `value.go`) -/

/-- `b.NewValue1(pos, op, t, a)`. -/
def newValue1 (b : ID) (pos : Pos) (op : Op) (t : TypeRef) (a : ID) : M ID := do
  let s ← get
  let (f, id) := s.f.newValueArgs b pos op t (args := #[a])
  set { s with f }
  return id

/-- `b.NewValue0(pos, op, t)`. -/
def newValue0 (b : ID) (pos : Pos) (op : Op) (t : TypeRef) : M ID := do
  let s ← get
  let (f, id) := s.f.newValue0 b pos op t
  set { s with f }
  return id

/-- Shared part of `copyInto`/`copyIntoWithXPos`: a clone of `v` at the end of `b`. -/
def cloneInto (v : Value) (b : ID) (pos : Pos) : M ID := do
  for a in v.args do
    if (← read).isMemory (← val a).type then
      fatal s!"can't move a value with a memory arg v{v.id}"
  let s ← get
  let (f, id) := s.f.newValueArgs b pos v.op v.type v.auxInt v.aux v.args
  set { s with f }
  return id

/-- `v.copyInto(b)`. -/
def copyInto (v : Value) (b : ID) : M ID := cloneInto v b v.pos.withNotStmt

/-- `v.copyIntoWithXPos(b, pos)`. -/
def copyIntoWithXPos (v : Value) (b : ID) (pos : Pos) : M ID :=
  let pos := if v.pos.isStmt == Pos.isStmtMark && pos.isStmt != Pos.isStmtMark &&
      v.pos.sameFileAndLine pos then pos.withIsStmt else pos
  cloneInto v b pos

/-- `f.newValueNoBlock(op, t, pos)`. -/
def newValueNoBlock (op : Op) (t : TypeRef) (pos : Pos) : M ID := do
  let s ← get
  let (f, id) := s.f.newValueNoBlock op t pos
  set { s with f }
  return id

/-- Record `c` in `s.copies` with `used`. -/
def setCopy (c : ID) (used : Bool) : M Unit :=
  modify fun s => { s with copies := Func.tabPut s.copies c used }

def copyState? (c : ID) : M (Option Bool) := return ((← get).copies[c]?).join

/-- A new aux at a fresh number. -/
def mintAux (d : AuxDef) : M AuxRef := do
  let s ← get
  let n := max s.tabs.auxes.size 1
  set { s with tabs := s.tabs.add (.aux n d) }
  return n

/-- `f.NewLocal(pos, t)` (`typecheck.TempAt` + `SetNonMergeable`): a new `PAUTO` named
`.autotmp_<len(curfn.Dcl)>`, appended to the frontend's declarations. -/
def newLocal (pos : Pos) (t : TypeRef) : M AuxRef := do
  let c ← read
  if ((c.tabs.type? t).bind (·.size)).isNone then
    fatal s!"NewLocal: type t{t} has no calculated size"
  let s ← get
  let nm := GoStr.ofString s!".autotmp_{s.dcl}"
  set { s with dcl := s.dcl + 1 }
  mintAux { fmt := nm, kind := .name nm .PAUTO t 0 3
                                 { used := true, autotmp := true, nonmergeable := true } pos }

/-! ## Register specifications -/

/-- `archRegForAbiReg(r, c)`. -/
def archRegForAbiReg (c : Cfg) (r : Nat) : Nat :=
  if r < c.intParamRegs.size then c.intParamRegs[r]! else c.floatParamRegs[r - c.intParamRegs.size]!

/-- `AuxCall.Reg(i, c)` on aux `a` (whose `reg` is non-nil): the cached constraints, built and
stored in the aux on first use. -/
def auxCallReg (a : AuxRef) (d : AuxDef) (fn : Option AuxRef) (abi : CallABI) (i : RegInfo) :
    M RegInfo := do
  let c ← read
  let cur := abi.reg.getD {}
  if !cur.clobbers.isEmpty then return cur
  if abi.inRegs + abi.outRegs == 0 then return i
  let mut k := i.inputs.length
  let mut ins := cur.inputs.toArray
  for p in abi.inParams do
    for r in p.regs do
      ins := ins.push ⟨k, RegMask.single (archRegForAbiReg c r)⟩
      k := k + 1
  ins := ins ++ i.inputs.toArray
  k := i.outputs.length
  let mut outs := cur.outputs.toArray
  for p in abi.outParams do
    for r in p.regs do
      outs := outs.push ⟨k, RegMask.single (archRegForAbiReg c r)⟩
      k := k + 1
  outs := outs ++ i.outputs.toArray
  let r : RegInfo := { cur with inputs := ins.toList, outputs := outs.toList, clobbers := i.clobbers }
  modify fun s => { s with tabs := s.tabs.add (.aux a { d with kind := .call fn (some { abi with reg := some r }) }) }
  return r

/-- `AuxCall.ResultReg(c)` on the function's own aux. -/
def resultReg (a : AuxRef) (d : AuxDef) (fn : Option AuxRef) (abi : CallABI) : M RegInfo := do
  let c ← read
  let cur := abi.reg.getD {}
  if abi.outRegs == 0 then return cur
  if !cur.inputs.isEmpty then return cur
  let mut k := 0
  let mut ins : Array RegIdx := #[]
  for p in abi.outParams do
    for r in p.regs do
      ins := ins.push ⟨k, RegMask.single (archRegForAbiReg c r)⟩
      k := k + 1
  let r : RegInfo := { cur with inputs := ins.toList }
  modify fun s => { s with tabs := s.tabs.add (.aux a { d with kind := .call fn (some { abi with reg := some r }) }) }
  return r

/-- `AuxInt8()`. -/
def auxInt8 (v : Value) : Int := (v.auxInt.toInt8).toInt

/-- `s.regspec(v)`. -/
def regspec (v : Value) : M RegInfo := do
  let c ← read
  match v.op with
  | .Convert =>
    let m := c.allocatable.inter c.gpMask
    return { inputs := [⟨0, m⟩], outputs := [⟨0, m⟩] }
  | .ArgIntReg =>
    let i := auxInt8 v
    let some r := c.intParamRegs[i.toNat]? | fatal s!"ArgIntReg index {i}"
    return { outputs := [⟨0, RegMask.single r⟩] }
  | .ArgFloatReg =>
    let i := auxInt8 v
    let some r := c.floatParamRegs[i.toNat]? | fatal s!"ArgFloatReg index {i}"
    return { outputs := [⟨0, RegMask.single r⟩] }
  | op =>
    if op.call then
      if let some a := v.aux then
        if let some d := (← get).tabs.aux? a then
          if let .call fn (some abi) := d.kind then
            if abi.inRegs + abi.outRegs > 0 then return ← auxCallReg a d fn abi op.regInfo
    if op == .MakeResult then
      if let some a := (← get).f.ownAux then
        if let some d := (← get).tabs.aux? a then
          if let .call fn (some abi) := d.kind then
            if abi.inRegs + abi.outRegs > 0 then return ← resultReg a d fn abi
    return op.regInfo

/-- `b.likelyBranch()` (`block.go:415`). -/
def likelyBranch (f : Func) (b : Block) : Bool :=
  !b.preds.isEmpty && b.preds.all fun e =>
    let p := f.getB e.b
    p.succs.size == 1 || (p.succs.size == 2 &&
      (p.likely == .likely && p.succs[0]!.b == b.id || p.likely == .unlikely && p.succs[1]!.b == b.id))

/-- `branchDistance(b, s)`. -/
def branchDistance (b : Block) (s : ID) : Int :=
  if b.succs.size == 2 then
    if b.succs[0]!.b == s && b.likely == .likely || b.succs[1]!.b == s && b.likely == .unlikely then 1
    else if b.succs[0]!.b == s && b.likely == .unlikely || b.succs[1]!.b == s && b.likely == .likely then 100
    else 10
  else 10

def likelyDistance : Int := 1
def normalDistance : Int := 10
def unlikelyDistance : Int := 100
def maxInt32 : Int := 2147483647

end GoFV.Opt.Regalloc
