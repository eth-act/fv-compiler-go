import GoFV.Gen.LiveCore
import GoFV.Gen.Intervals

/-!
# Stack slot merging (`liveness.MergeLocals`)

Port of `cmd/compile/internal/liveness/mergelocals.go` (go1.27.3) as `AllocFrame`
(`GoFV.Gen.allocFrame`) calls it:

* `MergeLocalsState` with `Subsumed`, `IsLeader`, `Leader`, `Followers`, `check` (lines 40–263);
* `collectMergeCandidates`, `genRegions`, `nextRegion`, `nameLess` (296–393, 632–690);
* `setupHashBisection` (424–444): only reachable with a non-empty `-d=mergelocalshash`, which the
  corpus never sets — it fails loudly instead;
* `populateIndirectUseTable` (470–625) with its evictions;
* liveness over the candidates (`newliveness` with `conservativeWrites`, `prologue`, `solve`:
  `GoFV.Gen.Live`, LivePort's port of `plive.go`), `computeIntervals` (831–1019) with the
  `IntervalsBuilder` of `GoFV.Gen.Intervals` (whose `Live`/`Kill` errors Go ignores here);
* `performMerging`, `mergeVisitRegion` (706–825).

Names are `.prog` name numbers; `Dcl` order and flags are the caller's (`Used` as `AllocFrame`
recomputed it). Type facts (size, alignment, pointers) are the `.prog` ones (`NameInfo`); `n.Pos()`
(`nameLess`'s last tie breaker, `fmt.Sprintf("%v", pos)` of a `src.XPos` = `{index lico}`) is the
position of the name's `.ssa` aux.

The only Go map whose iteration order could leak into the result is `rawcands` (the pruned
candidate list is re-sorted with the unstable `sort.Slice`): a `nameLess` tie there would make
Go's result depend on map order, so the port fails loudly on one.
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm (DclEntry)

/-- Go's `<` on strings: byte-wise lexicographic. -/
def goStrLt (a b : GoStr) : Bool := Id.run do
  let n := min a.bytes.size b.bytes.size
  for i in [0:n] do
    let x := a.bytes[i]!
    let y := b.bytes[i]!
    if x != y then return x < y
  return a.bytes.size < b.bytes.size

/-- Stable merge sort with a fallible strict "less" (`sort.SliceStable`, `slices.SortStableFunc`):
for a strict weak order every stable sort yields the same permutation, so this equals Go's
insertion-sort/`symMerge` result. -/
partial def stableSortM {α} [Inhabited α] (lt : α → α → Except String Bool) (a : Array α) :
    Except String (Array α) := do
  if a.size ≤ 1 then return a
  let mid := a.size / 2
  let l ← stableSortM lt (a.extract 0 mid)
  let r ← stableSortM lt (a.extract mid a.size)
  let mut out : Array α := Array.mkEmpty a.size
  let mut i := 0
  let mut j := 0
  while i < l.size && j < r.size do
    -- take the right element only if it is strictly less (keeps equal elements in order)
    if ← lt r[j]! l[i]! then
      out := out.push r[j]!
      j := j + 1
    else
      out := out.push l[i]!
      i := i + 1
  return out ++ l.extract i l.size ++ r.extract j r.size

/-- `liveness.MergeLocalsState`: the participating autos and, per auto, its partition (indices
into `vars`, leader first; the members of a partition share one array, as Go's slice). -/
structure MergeLocalsState where
  vars : Array Nat := #[]
  partition : Std.HashMap Nat (Array Nat) := {}
  deriving Inhabited

namespace MergeLocalsState

/-- `Subsumed(n)`. -/
def subsumed (mls : MergeLocalsState) (n : Nat) : Bool :=
  match mls.partition[n]? with
  | some sl => mls.vars[sl[0]!]! != n
  | none => false

/-- `IsLeader(n)`. -/
def isLeader (mls : MergeLocalsState) (n : Nat) : Bool :=
  match mls.partition[n]? with
  | some sl => mls.vars[sl[0]!]! == n
  | none => false

/-- `Leader(n)`. -/
def leader (mls : MergeLocalsState) (n : Nat) : Except String Nat :=
  match mls.partition[n]? with
  | some sl =>
    if mls.vars[sl[0]!]! == n then throw "variable is not subsumed" else pure mls.vars[sl[0]!]!
  | none => throw "not a merge candidate"

/-- `Followers(n, tmp)`: the followers of leader `n`, stably sorted by symbol name. -/
def followers (mls : MergeLocalsState) (env : Env) (n : Nat) : Except String (Array Nat) := do
  let some sl := mls.partition[n]? | throw "no entry for leader"
  if mls.vars[sl[0]!]! != n then throw "followers invoked on subsumed var"
  let tmp := (sl.extract 1 sl.size).map (mls.vars[·]!)
  let syms ← tmp.mapM fun k => return (k, (← env.name k).d.sym)
  let sorted ← stableSortM (fun a b => pure (goStrLt a.2 b.2)) syms
  return sorted.map (·.1)

/-- `(*MergeLocalsState).check()`. -/
def check (mls : MergeLocalsState) (env : Env) : Except String Unit := do
  let sym (k : Nat) : Except String String := return (← env.name k).d.sym.toStringLossy
  let mut seenv : Std.HashMap Nat Nat := {}
  for h : ii in [0:mls.vars.size] do
    let v := mls.vars[ii]
    if let some prev := seenv[v]? then
      throw s!"duplicate var {← sym v} in vslots: {ii} and {prev}"
    seenv := seenv.insert v ii
  for (k, sl) in mls.partition.toList do
    if sl.size < 2 then throw s!"k={← sym k} slice len {sl.size} invalid"
    for v in sl do
      if v ≥ mls.vars.size then throw s!"k={← sym k} vslot {v} out of range of m.v"
  let mut used : Std.HashSet Nat := {}
  for (k, sl) in mls.partition.toList do
    let mut foundk := false
    for h : i in [0:sl.size] do
      let v := sl[i]
      let vv := mls.vars[v]!
      if i == 0 then
        if !mls.isLeader vv then throw s!"k={← sym k} slpos 0 vslot {v} IsLeader is false"
      else
        if !mls.subsumed vv then throw s!"k={← sym k} slpos {i} vslot {v} Subsumed is false"
        if (← mls.leader vv) != mls.vars[sl[0]!]! then
          throw s!"k={← sym k} slpos {i} vslot {v} Leader mismatch"
      if vv == k then
        foundk := true
        if used.contains v then throw s!"k={← sym k} val slice used violation at slpos {i}"
        used := used.insert v
    if !foundk then throw s!"k={← sym k} slice value missing k"
    let vl ← env.name mls.vars[sl[0]!]!
    for v in sl.extract 1 sl.size do
      let vv ← env.name mls.vars[v]!
      if (← vv.size) > (← vl.size) then throw s!"k={← sym k} follower larger than leader"
      if (← vv.hasPointers) && !(← vl.hasPointers) then
        throw s!"k={← sym k} follower hasptr=true but leader hasptr=false"
      if (← vv.align) > (← vl.align) then throw s!"k={← sym k} follower align greater than leader"

end MergeLocalsState

namespace MergeLocals

/-- A candidate with the facts `nameLess`/`nextRegion` read. -/
structure Cand where
  n : Nat
  hasPtr : Bool
  align : Int
  size : Int
  sym : GoStr
  /-- `fmt.Sprintf("%v", n.Pos())`. -/
  pos : String
  deriving Inhabited

/-- `candRegion`. -/
structure CandRegion where
  st : Nat
  en : Nat
  deriving Inhabited

/-- `nameLess(ci, cj)`. -/
def nameLess (ci cj : Cand) : Bool :=
  if ci.hasPtr != cj.hasPtr then ci.hasPtr
  else if ci.align != cj.align then cj.align < ci.align
  else if ci.size != cj.size then cj.size < ci.size
  else if ci.sym != cj.sym then goStrLt ci.sym cj.sym
  else ci.pos < cj.pos

/-- `nextRegion(cands, idx)`: the end of the region starting at `idx` (`none`: Go's `-1`). -/
def nextRegion (cands : Array Cand) (idx : Nat) : Option Nat := Id.run do
  let n := cands.size
  if idx >= n then return none
  let c0 := cands[idx]!
  let mut szprev := c0.size
  let mut alnprev := c0.align
  for j in [idx + 1:n] do
    let cj := cands[j]!
    if cj.size > szprev then return some (j - 1)
    if cj.align > alnprev then return some (j - 1)
    szprev := cj.size
    alnprev := cj.align
  return some (n - 1)

/-- `genRegions(cands)`: the pruned candidates and their regions (empty if fewer than two). -/
def genRegions (cands : Array Cand) : Array Cand × Array CandRegion := Id.run do
  let mut pruned : Array Cand := #[]
  let mut regions : Array CandRegion := #[]
  let mut st := 0
  -- each iteration advances `st`
  for _ in [0:cands.size + 1] do
    let some en := nextRegion cands st | break
    if st == en then
      st := st + 1
      continue
    let pst := pruned.size
    let pen := pst + (en - st)
    pruned := pruned ++ cands.extract st (en + 1)
    regions := regions.push { st := pst, en := pen }
    st := en + 1
  if pruned.size < 2 then return (#[], #[])
  return (pruned, regions)

/-- `ssa.IsMergeCandidate(n)` (`ssa/func.go:869`) with `base.Debug.MergeLocals != 0`. -/
def isMergeCandidate (env : Env) (d : DclEntry) : Except String Bool := do
  if (← env.flagN) != 0 then return false
  let x ← env.name d.name
  if x.cls != "PAUTO" then return false
  if (← x.size) <= 3 * 8 then return false
  if d.flags.addrtaken || d.flags.nonmergeable || d.flags.opendeferslot then return false
  return true

/-- The facts of a candidate (its position from its `.ssa` aux). -/
def cand (env : Env) (n : Nat) : Except String Cand := do
  let x ← env.name n
  let some a := x.d.aux | throw s!"mergelocals: n{n} has no .ssa aux (position unknown)"
  let .name _ _ _ _ _ _ p := (← env.auxDef a).kind
    | throw s!"mergelocals: aux a{a} of n{n} is not a name"
  return { n, hasPtr := ← x.hasPointers, align := ← x.align, size := ← x.size, sym := x.d.sym,
           pos := s!"\{{p.index} {p.lico}}" }

/-- `populateIndirectUseTable(cands)`: the indirect upwards-exposed uses (value → names) and
the candidates and regions left after evictions (`none`: fewer than two). -/
def populateIndirectUseTable (env : Env) (mem : TypeRef) (cands : Array Cand) :
    Except String (Option (Std.HashMap ID (Array Nat) × Array Cand × Array CandRegion)) := do
  let mut indirectUE : Std.HashMap ID (Array Nat) := {}
  let mut rawcands : Std.HashSet Nat := cands.foldl (fun s c => s.insert c.n) {}
  for bid in env.f.blocks do
    let b ← env.block bid
    -- value → (name, remaining uses)
    let mut pendingUses : Std.HashMap ID (Nat × Nat) := {}
    let mut blockIndirectUE : Std.HashMap ID (Array Nat) := {}
    for vid in b.values do
      let v ← env.value vid
      let (n?, e) ← Live.affectedVar env v
      if let some (.dcl n) := n? then
        if rawcands.contains n then
          if e.addr && v.uses != 0 then
            if pendingUses.contains v.id then
              throw s!"internal error: apparent multiple defs for SSA value {v.id}"
            pendingUses := pendingUses.insert v.id (n, v.uses)
      for h : idx in [0:v.args.size] do
        let arg := v.args[idx]
        let some nc := pendingUses[arg]? | continue
        let sink := if idx == 0 then v.op.addrSinkArg0 else if idx == 1 then v.op.addrSinkArg1
          else false
        if !sink then
          if env.tabs.isMemory mem v.type then continue
          if pendingUses.contains v.id then continue
          pendingUses := pendingUses.insert v.id (nc.1, v.uses)
        blockIndirectUE := blockIndirectUE.insert v.id
          ((blockIndirectUE.getD v.id #[]).push nc.1)
        let count := nc.2 - 1
        if count == 0 then pendingUses := pendingUses.erase arg
        else pendingUses := pendingUses.insert arg (nc.1, count)
    let mut evicted : Std.HashSet Nat := {}
    for (_, nc) in pendingUses.toList do
      rawcands := rawcands.erase nc.1
      evicted := evicted.insert nc.1
    for (id, sl) in blockIndirectUE.toList do
      for n in sl do
        if evicted.contains n then continue
        indirectUE := indirectUE.insert id ((indirectUE.getD id #[]).push n)
  if rawcands.size < 2 then return none
  -- `pruned` in `rawcands` map order, then `sort.Slice` (unstable) by `nameLess`: unique iff
  -- `nameLess` has no ties among them.
  let pruned := cands.filter (rawcands.contains ·.n)
  let pruned ← stableSortM (fun a b => pure (nameLess a b)) pruned
  for i in [1:pruned.size] do
    let a := pruned[i-1]!
    let b := pruned[i]!
    if !nameLess a b && !nameLess b a then
      throw s!"mergelocals: nameLess tie between n{a.n} and n{b.n} (Go map order decides)"
  let (pruned, regions) := genRegions pruned
  if pruned.size < 2 then return none
  return some (indirectUE, pruned, regions)

/-- `computeIntervals()`: the live intervals of every candidate. -/
def computeIntervals (env : Env) (lv : Live.Lv) (cands : Array Cand)
    (indirectUE : Std.HashMap ID (Array Nat)) : Except String (Array Intervals) := do
  let nvars := lv.vars.size
  let mut ib : Array IntervalsBuilder := Array.replicate cands.size {}
  let mut liveout := Live.Bv.new nvars
  let mut ninstr : Nat := 0
  for bid in env.f.blocks do ninstr := ninstr + (← env.block bid).values.size
  let mut iidx : Int := (ninstr : Int) - 1
  for k' in [0:env.f.blocks.size] do
    let k := env.f.blocks.size - 1 - k'
    let b ← env.block env.f.blocks[k]!
    let some be := lv.be[b.id]? | throw s!"mergelocals: no block effects for b{b.id}"
    for j in [0:nvars] do
      let isLive ← liveout.get j
      let blockLiveOut ← be.liveout.get j
      if isLive then
        if !blockLiveOut then ib := ib.modify j (·.kill! iidx)
      else if blockLiveOut then
        ib := ib.modify j (·.live! iidx)
    liveout := be.liveout
    for i' in [0:b.values.size] do
      let i := b.values.size - 1 - i'
      let v ← env.value b.values[i]!
      let (pos, e) ← lv.valueEffects v
      let becomeslive := e &&& Live.uevar != 0
      let iskilled := e &&& Live.varkill != 0
      if becomeslive && iskilled then throw "should never happen"
      if iskilled && (← liveout.get pos.toNat) then
        ib := ib.modify pos.toNat (·.kill! iidx)
        liveout ← liveout.unset pos.toNat
      else if becomeslive && !(← liveout.get pos.toNat) then
        ib := ib.modify pos.toNat (·.live! iidx)
        liveout ← liveout.set pos.toNat
      for n in indirectUE.getD v.id #[] do
        if let some p := lv.idx[n]? then
          if !(← liveout.get p) then
            ib := ib.modify p (·.live! iidx)
            liveout ← liveout.set p
      iidx := iidx - 1
  if iidx != -1 then throw "iidx underflow"
  let mut ivs : Array Intervals := #[]
  for h : i in [0:cands.size] do
    match ib[i]!.finish with
    | .ok r => ivs := ivs.push r
    | .error err =>
      throw s!"interval construct error for var {cands[i].sym.toStringLossy} ({ninstr} instrs): {err}"
  return ivs

/-- `mergeVisitRegion(mls, st, en)`. -/
def mergeVisitRegion (mls : MergeLocalsState) (cands : Array Cand) (ivs : Array Intervals)
    (st en : Nat) : MergeLocalsState := Id.run do
  let n := en - st + 1
  let mut used : Array Bool := Array.replicate n false
  let nxt (used : Array Bool) (slot : Nat) : Option Nat := Id.run do
    for c in [slot - st:n] do
      if used[c]! then continue
      return some (c + st)
    return none
  let mut navail := n
  let mut mls := mls
  -- each iteration marks at least the leader used
  for _ in [0:n + 1] do
    if navail < 2 then break
    let some leader := nxt used st | break
    used := used.set! (leader - st) true
    navail := navail - 1
    let mut elems : Array Nat := #[leader]
    let mut lints := ivs[leader]!
    let mut succ? := nxt used (leader + 1)
    for _ in [0:n + 1] do
      let some succ := succ? | break
      if !used[succ - st]! then
        if !lints.overlaps ivs[succ]! then
          elems := elems.push succ
          lints := lints.merge ivs[succ]!
      succ? := nxt used (succ + 1)
    if elems.size > 1 then
      let off := mls.vars.size
      let sl := (Array.range elems.size).map (off + ·)
      for candslot in elems do
        mls := { mls with vars := mls.vars.push cands[candslot]!.n,
                          partition := mls.partition.insert cands[candslot]!.n sl }
      navail := navail - (elems.size - 1)
      for e in elems do used := used.set! (e - st) true
  return mls

end MergeLocals

open MergeLocals in
/-- `liveness.MergeLocals(fn, f)` on `Dcl` as `AllocFrame` has marked it (`none`: Go's nil). -/
def mergeLocals (env : Env) (dcl : Array DclEntry) : Except String (Option MergeLocalsState) := do
  -- collectMergeCandidates
  let mut raw : Array Cand := #[]
  for d in dcl do
    if !d.flags.used then continue
    if !(← isMergeCandidate env d) then continue
    raw := raw.push (← cand env d.name)
  if raw.size < 2 then return none
  raw ← stableSortM (fun a b => pure (nameLess a b)) raw
  let (initial, _) := genRegions raw
  if initial.size < 2 then return none
  -- setupHashBisection
  match env.progConfig? "mergelocalshash" with
  | some (.str s) => if s.size != 0 then
      throw "mergelocals: hash bisection (-d=mergelocalshash) not ported"
  | _ => throw "prog config mergelocalshash: missing"
  let mem ← match (env.file.sections[0]?.bind (·.typs)).bind
      fun ts => (ts.find? (·.1 == "Mem")).map (·.2) with
    | some t => pure t
    | none => throw "mergelocals: typs: no Mem"
  let some (indirectUE, cands, regions) ← populateIndirectUseTable env mem initial
    | return none
  if cands.size < 2 then return none
  let mut nameToSlot : Std.HashMap Nat Nat := {}
  for h : i in [0:cands.size] do nameToSlot := nameToSlot.insert cands[i].n i
  let usedOf : Std.HashMap Nat Bool := dcl.foldl (fun m d => m.insert d.name d.flags.used) {}
  let lv ← Live.newliveness env (cands.map (·.n)) nameToSlot 0 (fun n => usedOf.getD n false)
    (conservativeWrites := true)
  let lv ← lv.prologue
  let lv ← lv.solve
  let ivs ← computeIntervals env lv cands indirectUE
  -- performMerging
  let mut mls : MergeLocalsState := {}
  for cr in regions do mls := mergeVisitRegion mls cands ivs cr.st cr.en
  if mls.vars.size == 0 then return none
  match mls.check env with
  | .ok () => return some mls
  | .error e => throw s!"invalid mergelocals state: {e}"

end GoFV.Gen
