import GoFV.Opt.Regalloc.State
import Std.Data.HashMap.Basic

/-!
# Merge edges

`shuffle` and `edgeState` (`regalloc.go`, go1.27.3, lines 2430-2919): for each edge into a
merge block, move the values the predecessor ends with (registers and dominating stack slots)
into the locations the merge block starts with (`startRegs` and the phi homes), with temporary
registers, cycle breaking and emergency spills to fresh autos.

`contents` is Go's `map[Location]contentRecord` (looked up and overwritten only; `erase` keeps
the entry), `cache` the per-value representative lists with `cachedVals` as their key order.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA

/-- `contentRecord`. -/
structure Content where
  vid : ID
  c : ID
  final : Bool
  pos : Pos
  deriving Inhabited

/-- `dstRecord`; `splice` is the phi argument `(phi, index)` to rewrite. -/
structure Dst where
  loc : Location
  vid : ID
  splice : Option (ID × Nat)
  pos : Pos
  deriving Inhabited

/-- `edgeState`. -/
structure Edge where
  p : ID := 0
  b : ID := 0
  cache : Std.HashMap ID (Array ID) := {}
  cachedVals : Array ID := #[]
  /-- `contents` for registers (by number) and slots. -/
  regContents : Array (Option Content) := Array.replicate 64 none
  slotContents : Array (SlotDef × Content) := #[]
  extra : Array Dst := #[]
  usedRegs : RegMask := {}
  uniqueRegs : RegMask := {}
  finalRegs : RegMask := {}
  rematRegs : RegMask := {}
  deriving Inhabited

abbrev EM := StateT Edge M

def contentsAt (loc : Location) : EM (Option Content) := do
  let e ← get
  match loc with
  | .reg r => return (e.regContents[r]?).join
  | .slot k => return (e.slotContents.find? (·.1 == k)).map (·.2)
  | _ => return none

def setContents (loc : Location) (cr : Content) : EM Unit := do
  match loc with
  | .reg r => modify fun e => { e with regContents := e.regContents.set! r (some cr) }
  | .slot k => modify fun e =>
      match e.slotContents.findIdx? (·.1 == k) with
      | some i => { e with slotContents := e.slotContents.set! i (k, cr) }
      | none => { e with slotContents := e.slotContents.push (k, cr) }
  | _ => throw "shuffle: location is neither a register nor a slot"

/-- `e.set(loc, vid, c, final, pos)`. -/
def eSet (loc : Location) (vid c : ID) (final : Bool) (pos : Pos) : EM Unit := do
  setHome c loc
  setContents loc ⟨vid, c, final, pos⟩
  let e ← get
  let a := e.cache.getD vid #[]
  let cachedVals := if a.isEmpty then e.cachedVals.push vid else e.cachedVals
  let a := a.push c
  set { e with cache := e.cache.insert vid a, cachedVals }
  if let .reg r := loc then
    let e ← get
    if e.usedRegs.hasReg r then throw s!"register {r} is already set (v{vid}/v{c})"
    let mut e := { e with usedRegs := e.usedRegs.addReg r }
    if final then e := { e with finalRegs := e.finalRegs.addReg r }
    if a.size == 1 then e := { e with uniqueRegs := e.uniqueRegs.addReg r }
    if a.size == 2 then
      if let some (.reg t) ← getHome a[0]! then e := { e with uniqueRegs := e.uniqueRegs.removeReg t }
    if (← vs vid).remat then e := { e with rematRegs := e.rematRegs.addReg r }
    set e

/-- `e.erase(loc)`. -/
def erase (loc : Location) : EM Unit := do
  let some cr ← contentsAt loc | return
  if cr.c == 0 then return
  let vid := cr.vid
  if cr.final then modify fun e => { e with extra := e.extra.push ⟨loc, vid, none, cr.pos⟩ }
  let mut a := (← get).cache.getD vid #[]
  for i in [0:a.size] do
    if (← getHome a[i]!) == some loc then
      a := (a.set! i a[a.size - 1]!).pop
      break
  modify fun e => { e with cache := e.cache.insert vid a }
  if let .reg r := loc then
    modify fun e => { e with usedRegs := e.usedRegs.removeReg r, rematRegs := e.rematRegs.removeReg r
                             finalRegs := if cr.final then e.finalRegs.removeReg r else e.finalRegs }
  if a.size == 1 then
    if let some (.reg r) ← getHome a[0]! then
      modify fun e => { e with uniqueRegs := e.uniqueRegs.addReg r }

/-- `e.findRegFor(typ)`: a register for a temporary copy, spilling one if none is free. -/
def findRegFor (typ : TypeRef) : EM Location := do
  let c ← read
  let e ← get
  let m := c.compatRegs typ
  if let some r := (m.minus e.usedRegs).pick? then return .reg r
  if let some r := ((m.minus e.uniqueRegs).minus e.finalRegs).pick? then return .reg r
  if let some r := (m.minus e.uniqueRegs).pick? then return .reg r
  if let some r := (m.inter e.rematRegs).pick? then return .reg r
  for vid in e.cachedVals do
    for cv in (← get).cache.getD vid #[] do
      if let some (.reg r) ← getHome cv then
        if m.hasReg r then
          let x ← val cv
          if !(← rematerializeable x) then
            let s ← newValue1 (← get).p x.pos .StoreReg x.type cv
            let n ← newLocal x.pos x.type
            eSet (.slot { name := n, type := x.type, off := 0, splitOf := none, splitOffset := 0 })
              vid s false x.pos
          return .reg r
  throw s!"can't find empty register on edge b{e.p}->b{e.b}"

/-- `(*splice).Uses--; *splice = x; x.Uses++`. -/
def splice (sp : Option (ID × Nat)) (x : ID) : EM Unit := do
  if let some (phi, i) := sp then modF fun f => f.setArg phi i x

/-- `e.processDest(loc, vid, splice, pos)`: whether progress was made. -/
def processDest (loc : Location) (vid : ID) (sp : Option (ID × Nat)) (pos : Pos) : EM Bool := do
  let pos := pos.withNotStmt
  let occ := (← contentsAt loc).getD ⟨0, 0, false, Pos.none⟩
  if occ.vid == vid then
    setContents loc ⟨vid, occ.c, true, pos⟩
    splice sp occ.c
    if (← copyState? occ.c).isSome then setCopy occ.c true
    return true
  -- never overwrite the last copy of a value that must survive
  if ((← get).cache.getD occ.vid #[]).size == 1 then
    if !(← vs occ.vid).remat && !(← val (← origOf occ.vid)).op.fixedReg then return false
  let v ← val (← origOf vid)
  let mut c : ID := 0
  let mut src : Option Location := none
  if v.op.fixedReg then
    c := v.id
    src ← getHome v.id
  else
    for w in (← get).cache.getD vid #[] do
      let h ← getHome w
      let isReg := match h with | some (.reg _) => true | _ => false
      if src.isNone || isReg then
        c := w
        src := h
  let dstReg := match loc with | .reg _ => true | _ => false
  let srcReg := match src with | some (.reg _) => true | _ => false
  erase loc
  let p := (← get).p
  let remat := (← vs vid).remat
  let mut x : ID := 0
  if c == 0 || remat then
    if !remat then throw s!"can't find source for b{p}->b{(← get).b}: v{v.id}"
    if let .reg dr := loc then
      let some out := (← regspec v).outputs.head? | throw s!"no output spec for v{v.id}"
      if !out.regs.hasReg dr then
        if srcReg then
          x ← newValue1 p pos .Copy (← val c).type c
        else
          x ← copyInto v p
          let r ← findRegFor (← val x).type
          erase r
          eSet r vid x false pos
          x ← newValue1 p pos .Copy (← val x).type x
      else
        x ← copyInto v p
    else
      let r ← findRegFor v.type
      erase r
      x ← copyIntoWithXPos v p pos
      eSet r vid x false pos
      let .slot k := loc | throw "shuffle: stack destination is not a slot"
      x ← newValue1 p pos .StoreReg k.type x
  else
    let ct := (← val c).type
    if srcReg then
      if dstReg then x ← newValue1 p pos .Copy ct c
      else
        let .slot k := loc | throw "shuffle: stack destination is not a slot"
        x ← newValue1 p pos .StoreReg k.type c
    else
      if dstReg then x ← newValue1 p pos .LoadReg ct c
      else
        let r ← findRegFor ct
        erase r
        let t ← newValue1 p pos .LoadReg ct c
        eSet r vid t false pos
        let .slot k := loc | throw "shuffle: stack destination is not a slot"
        x ← newValue1 p pos .StoreReg k.type t
  eSet loc vid x true pos
  if let .reg r := loc then
    if (← val x).op == .LoadReg && isGReg (← read) r then
      throw s!"processDest.OpLoadReg targeting g: v{x}"
  splice sp x
  return true

/-- `e.process()`. -/
def process (dsts : Array Dst) : EM Unit := do
  let mut dsts := dsts
  -- every round either satisfies a destination or breaks a cycle with a new copy
  for _ in [0:100000] do
    if dsts.isEmpty then return
    let mut rest : Array Dst := #[]
    for d in dsts do
      if !(← processDest d.loc d.vid d.splice d.pos) then rest := rest.push d
    if rest.size < dsts.size then
      dsts := rest ++ (← get).extra
      modify fun e => { e with extra := #[] }
      continue
    -- no progress: break a cycle by copying the first destination's occupant to a temporary
    let d := dsts[0]!
    let some cr ← contentsAt d.loc | throw "shuffle: cycle location has no contents"
    if cr.c == 0 then throw "shuffle: cycle location has no contents"
    let ct := (← val cr.c).type
    let r ← findRegFor ct
    erase r
    let pos := d.pos.withNotStmt
    let p := (← get).p
    let c ← match d.loc with
      | .reg _ => newValue1 p pos .Copy ct cr.c
      | _ => newValue1 p pos .LoadReg ct cr.c
    eSet r cr.vid c false pos
    if let .reg rr := r then
      if (← val c).op == .LoadReg && isGReg (← read) rr then
        throw s!"process.OpLoadReg targeting g: v{c}"
  throw "shuffle: too many rounds"

/-- `e.setup(idx, srcReg, dstReg, stacklive)` followed by `e.process()` for edge `p → b`. -/
def shuffleEdge (b : Block) (idx : Nat) (stacklive : Array ID) : M Unit := do
  let p := b.preds[idx]!.b
  let s ← get
  let srcReg := s.endRegs[p]!
  let dstReg := s.startRegs[b.id]!
  let run : EM Unit := do
    for x in srcReg do eSet (.reg x.r) x.v x.c false Pos.none
    for spillID in stacklive do
      let v ← origOf spillID
      let spill := (← vs v).spill
      let sb := (← val spill).block
      if !Analysis.SparseTree.isAncestorEq (← getThe St).sdom sb p then continue
      let some h ← getHome spillID | throw s!"stack-live v{spillID} has no home"
      eSet h v spill false Pos.none
    let mut dsts : Array Dst := dstReg.map fun x => ⟨.reg x.r, x.v, none, x.pos⟩
    for vid in b.values do
      let v ← val vid
      if v.op != .Phi then break
      let some loc ← getHome vid | continue
      dsts := dsts.push ⟨loc, v.args[idx]!, some (vid, idx), v.pos⟩
    process dsts
  let _ ← run.run { p, b := b.id }

/-- `s.shuffle(stacklive)`. -/
def shuffle (stacklive : Array (Array ID)) : M Unit := do
  for bid in (← getF).blocks do
    let b ← blk bid
    if b.preds.size ≤ 1 then continue
    for i in [0:b.preds.size] do
      shuffleEdge (← blk bid) i stacklive[b.preds[i]!.b]!

end GoFV.Opt.Regalloc
