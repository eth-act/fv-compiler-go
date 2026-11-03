import GoFV.Opt.Regalloc.State

/-!
# Liveness and desired registers

`computeLive`, `computeDesired`, `updateLive` and `computeUnavoidableCalls` (`regalloc.go`,
go1.27.3, lines 2946-3383 and 3555-3623). Sparse maps are `GoFV.Util.SparseMapPos`, whose dense
order (insertion, in-place update, swap-removal) becomes the order of the live lists.
-/

namespace GoFV.Opt.Regalloc

open GoFV.SSA GoFV.Util

abbrev LiveMap := SparseMapPos Pos

/-- `updateLive(t, live)`: the map's entries in dense order. -/
def liveOf (t : LiveMap) : Array LiveInfo :=
  t.contents.map fun e => { id := e.key, dist := e.val.1, pos := e.val.2 }

/-- Fill `t` (cleared) with a live list. -/
def mapOf (t : LiveMap) (l : Array LiveInfo) : LiveMap :=
  l.foldl (fun t e => t.set e.id e.dist e.pos) t.clear

/-- Add `d` to every distance (in place, dense order). -/
def addAll (t : LiveMap) (d : Int) : LiveMap :=
  { t with dense := t.dense.map fun e => { e with val := (e.val.1 + d, e.val.2) } }

/-- `b.containsCall()`. -/
def containsCall (f : Func) (b : Block) : Bool :=
  b.kind == .Defer || b.values.any fun v => (f.getV v).op.call

/-- `loopnest.computeUnavoidableCalls()`: sets `containsUnavoidableCall` of every loop without a
call-free path from its header back to the header or out of the loop (never resets a set bit). -/
def computeUnavoidableCalls (f : Func) (n : Nest) : Except String Nest := do
  let nb := f.bidLast + 1
  let mut hasCall := Array.replicate nb false
  for b in f.blocks do
    if containsCall f (f.getB b) then hasCall := hasCall.set! b true
  let mut loops := n.nest.loops
  for li in [0:loops.size] do
    let l := loops[li]!
    let mut found := SparseSet.new nb
    let mut tovisit : Array ID := #[l.header]
    let mut free := false
    -- each block enters `tovisit` at most once (`found`), plus the header
    for _ in [0:nb + 2] do
      if free || tovisit.isEmpty then break
      let cur := tovisit.back!
      tovisit := tovisit.pop
      if hasCall[cur]! then continue
      for e in (f.getB cur).succs do
        let nbk := e.b
        if nbk == l.header then free := true; break
        if found.contains nbk then continue
        let nl ← n.at? nbk
        match nl with
        | none => continue
        | some x =>
          if loops[x]!.depth ≤ l.depth && x != li then continue
        tovisit := tovisit.push nbk
        found := found.add nbk
    if !free then loops := loops.modify li fun l => { l with unavoidableCall := true }
  return { n with nest := { n.nest with loops } }

/-- `s.computeDesired()`. -/
def computeDesired (po : Array ID) : M Unit := do
  let f ← getF
  let some n := (← get).nest | fatal "computeDesired without a loop nest"
  let maxPreds := f.blocks.foldl (fun m b => max m (f.getB b).preds.size) 0
  let mut phiPrefs : Array Desired := Array.replicate maxPreds {}
  -- Go iterates until the avoid masks stop growing (bounded by the mask bits per block)
  for _ in [0:(f.bidLast + 1) * 130 + 2] do
    let mut changed := false
    for bid in po do
      let b ← blk bid
      let mut desired := (← get).desired[bid]!
      for i in [0:b.preds.size] do
        phiPrefs := phiPrefs.set! i {}
      let headerLoop : Option Nat := match ← n.at? bid with
        | some l => if (n.loop l).header == bid then some l else none
        | none => none
      let mut i := b.values.size
      -- non-phis, backwards
      for _ in [0:b.values.size] do
        if i == 0 then break
        let v ← val b.values[i - 1]!
        if v.op == .Phi then break
        i := i - 1
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
      -- the rest (the phis), backwards
      for _ in [0:i] do
        let v ← val b.values[i - 1]!
        i := i - 1
        let (prefs, d) := desired.remove v.id
        desired := d
        if prefs[0]! == RegMask.noReg then continue
        for r in prefs do
          if r != RegMask.noReg then desired := { desired with avoid := desired.avoid.minus (RegMask.single r) }
        for pidx in [0:v.args.size] do
          if let some hl := headerLoop then
            if (← n.at? b.preds[pidx]!.b) == some hl then continue
          phiPrefs := phiPrefs.modify pidx fun d => d.addList v.args[pidx]! prefs
      for pidx in [0:b.preds.size] do
        let p := b.preds[pidx]!.b
        let (c1, d1) := ((← get).desired[p]!).merge desired
        modify fun s => { s with desired := s.desired.set! p d1 }
        let (c2, d2) := ((← get).desired[p]!).merge phiPrefs[pidx]!
        modify fun s => { s with desired := s.desired.set! p d2 }
        changed := c1 || changed
        changed := c2 || changed
    if !changed || (!n.nest.irreducible && n.nest.loops.isEmpty) then return
  fatal "computeDesired did not converge"

/-- `s.computeLive()`. -/
def computeLive : M Unit := do
  let f0 ← getF
  if f0.blocks.size == 1 then return
  let (po, f1) := f0.postorder
  modify fun s => { s with f := f1 }
  let nb := f1.bidLast + 1
  let nv := f1.vidLast + 1
  modify fun s => { s with live := some (Array.replicate nb #[]), desired := Array.replicate nb {} }
  let (_, f2) ← liftE f1.loopnest
  modify fun s => { s with f := f2 }
  let some ln := f2.cache.loopnest | fatal "no loop nest"
  let n ← liftE (computeUnavoidableCalls f2 (Nest.ofLoopNest ln))
  modify fun s => { s with nest := some n, f := { s.f with cache := { s.f.cache with loopnest := some n.nest } } }
  let f ← getF
  let mut live : LiveMap := SparseMapPos.new nv
  let mut t : LiveMap := SparseMapPos.new nv
  let loopy := !n.nest.loops.isEmpty && !n.nest.irreducible
  -- `loopLiveIn` by loop index; `numCalls` by block ID
  let mut loopLiveIn : Array (Option (Array LiveInfo)) := Array.replicate n.nest.loops.size none
  let mut numCalls : Array Int := Array.replicate nb 0
  let mut lv := (← get).live.get!
  let values := (← get).values
  let needReg (id : ID) : Bool := (values[id]?.map (·.needReg)).getD false
  -- Go iterates to a fixed point (irreducible CFGs only); each round grows some live set
  for _ in [0:nb * nv + 2] do
    let mut changed := false
    for bid in po do
      let b := f.getB bid
      live := mapOf live lv[bid]!
      let mut update := false
      for e in b.succs do
        let succ := f.getB e.b
        let delta := branchDistance b e.b
        for vid in succ.values do
          let v := f.getV vid
          if v.op != .Phi then break
          let arg := v.args[e.i]!
          if needReg arg && (!live.contains arg || delta < live.get arg) then
            live := live.set arg delta v.pos
            update := true
      if update then lv := lv.set! bid (liveOf live)
      live := addAll live b.values.size
      for c in b.controls do
        if needReg c then live := live.set c b.values.size b.pos
      for k in [0:b.values.size] do
        let i := b.values.size - 1 - k
        let v := f.getV b.values[i]!
        live := live.remove v.id
        if v.op == .Phi then continue
        if v.op.call then
          if loopy then numCalls := numCalls.modify bid (· + 1)
          live := addAll live unlikelyDistance
          let rematIDs := (live.contents.filter fun e => (values[e.key]?.map (·.remat)).getD false).map (·.key)
          for r in rematIDs do live := live.remove r
        for a in v.args do
          if needReg a then live := live.set a i v.pos
      if loopy then
        if let some l ← n.at? bid then
          if (n.loop l).header == bid then loopLiveIn := loopLiveIn.set! l (some (liveOf live))
      for e in b.preds do
        let p := e.b
        let delta := branchDistance (f.getB p) bid
        t := mapOf t lv[p]!
        let mut upd := false
        for e in live.contents do
          let d := e.val.1 + delta
          if !t.contains e.key || d < t.get e.key then
            upd := true
            t := t.set e.key d e.val.2
        if !upd then continue
        lv := lv.set! p (liveOf t)
        changed := true
    if !changed || loopy || n.nest.loops.isEmpty then break
  if !loopy then
    modify fun s => { s with live := some lv }
    computeDesired po
    return
  -- propagate live-ins from outer to inner loops, in depth order
  let order := (Array.range n.nest.loops.size).qsort fun a b => (n.loop a).depth < (n.loop b).depth
  let mut loopset : LiveMap := SparseMapPos.new nv
  for li in order do
    let some o := (n.loop li).outer | continue
    let livein := (loopLiveIn[li]!).getD #[]
    loopset := mapOf loopset livein
    let mut update := false
    for l in (loopLiveIn[o]!).getD #[] do
      if !loopset.contains l.id then
        loopset := loopset.set l.id l.dist l.pos
        update := true
    if update then loopLiveIn := loopLiveIn.set! li (some (liveOf loopset))
  -- live-ins of loop headers to the loop's blocks (distance unknown: −1)
  for bid in po do
    let some l ← n.at? bid | continue
    let headerLive := (loopLiveIn[l]!).getD #[]
    loopset := mapOf loopset lv[bid]!
    let mut update := false
    for e in headerLive do
      if !loopset.contains e.id then
        loopset := loopset.set e.id (-1) Pos.none
        update := true
    if update then lv := lv.set! bid (liveOf loopset)
  -- fill in unknown distances from successors
  let mut unfinished := po
  for _ in [0:nb * nv + 2] do
    if unfinished.isEmpty then break
    let mut next := #[]
    for bid in unfinished do
      let b := f.getB bid
      live := live.clear
      let mut unfinishedValues : Int := 0
      for l in lv[bid]! do
        if l.dist == -1 then unfinishedValues := unfinishedValues + 1
        live := live.set l.id l.dist l.pos
      let mut update := false
      for e in b.succs do
        let succ := f.getB e.b
        for l in lv[e.b]! do
          if !live.contains l.id || l.dist == -1 then continue
          let dist := succ.values.size + l.dist + branchDistance b e.b + numCalls[e.b]! * unlikelyDistance
          let v := live.get l.id
          if v == -1 then
            unfinishedValues := unfinishedValues - 1
            update := true
            live := live.set l.id dist l.pos
          else if dist < v then
            update := true
            live := live.set l.id dist l.pos
      if update then lv := lv.set! bid (liveOf live)
      if unfinishedValues > 0 then next := next.push bid
    unfinished := next
  if !unfinished.isEmpty then fatal "computeLive: distances did not converge"
  -- sort by (dist, ID): a total order on distinct values
  for bid in f.blocks do
    lv := lv.set! bid (lv[bid]!.qsort fun a b => a.dist < b.dist || (a.dist == b.dist && a.id < b.id))
  modify fun s => { s with live := some lv }
  computeDesired po

end GoFV.Opt.Regalloc
