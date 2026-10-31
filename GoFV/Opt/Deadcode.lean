import GoFV.Opt.CopyElim
import GoFV.SSA.Live
import GoFV.SSA.XPosMap

/-!
# deadcode (`deadcode.go:174-305`)

One port for the five in-scope instances (`early`, `pre-opt`, `opt`, `gcse`, `generic
deadcode`; `docs/PASSES.md`, deadcode):

1. `ReachableBlocks`; remove edges from unreachable to reachable blocks (`removeEdge`,
   swap-with-last; the successor index is not advanced after a removal); turn reachable
   `BlockFirst` blocks into `Plain` (`removeEdge(1)`, `Likely = BranchUnknown`).
2. `copyelim`.
3. `liveValues`; prune `f.Names`/`f.NamedValues` to live values (deduplicated, order kept;
   empty entries dropped).
4. Statement marks: `f.cachedLineStarts` is cleared and used as `pendingLines`; dead values
   with `PosIsStmt` in reachable blocks record their line; the mark moves to the last-discovered
   live value of that line in the same block, else to the block of the recorded index if its
   position has that line. Leftover entries stay in the cache (exported).
5. Free dead values (`f.Blocks` × `b.Values` order, compacting `b.Values`), then unreachable
   blocks (`f.Blocks` order, compacting `f.Blocks`): this order fixes the free lists.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Deadcode

/-- Remove the edges from unreachable blocks to reachable ones (`deadcode.go:184-196`). -/
def removeDeadEdges (reachable : Array Bool) (f : Func) : Func := Id.run do
  let mut f := f
  for b in f.blocks do
    if reachable.getD b false then continue
    let mut i := 0
    for _ in [0:2 * (f.getB b).succs.size + 1] do
      let ss := (f.getB b).succs
      if h : i < ss.size then
        if reachable.getD ss[i].b false then f := f.removeEdge b i
        else i := i + 1
      else break
  return f

/-- Reachable `BlockFirst` blocks become `Plain` (`deadcode.go:199-208`). -/
def removeFirstEdges (reachable : Array Bool) (f : Func) : Func :=
  f.blocks.foldl (init := f) fun f b =>
    if !reachable.getD b false || (f.getB b).kind != .First then f else
    (f.removeEdge b 1).modB b fun x => { x with kind := .Plain, likely := .unknown }

/-- Keep the live values of each name, deduplicated, and drop names left empty
(`deadcode.go:221-245`). -/
def pruneNames (live : Array Bool) (f : Func) : Func :=
  let names := f.names.filterMap fun (s, vs) =>
    let (kept, _) := vs.foldl (init := (#[], (∅ : Std.HashSet ID))) fun (kept, seen) v =>
      if live.getD v false && !seen.contains v then (kept.push v, seen.insert v) else (kept, seen)
    if kept.isEmpty then none else some (s, kept)
  { f with names }

/-- Unlink dead values and record lost statement boundaries (`deadcode.go:248-262`). -/
def unlink (reachable live : Array Bool) (f : Func) (pending : XPosMap) :
    Except String (Func × XPosMap) := do
  let mut f := f
  let mut pending := pending
  let blocks := f.blocks
  for h : i in [0:blocks.size] do
    let b := blocks[i]
    let r := reachable.getD b false
    if !r then f := f.resetControls b
    for v in (f.getB b).values do
      if !live.getD v false then
        f := f.resetArgs v
        let p := (f.getV v).pos
        if p.isStmt == Pos.isStmtMark && r then
          pending ← pending.set p (i : Int)
  return (f, pending)

/-- Give lost statement marks a new home (`deadcode.go:264-282`). -/
def moveStmts (order : Array ID) (f : Func) (pending : XPosMap) : Func × XPosMap := Id.run do
  let mut f := f
  let mut pending := pending
  for w in order.reverse do
    let x := f.getV w
    if let some j := pending.get x.pos then
      if f.blocks[j.toNat]? == some x.block then
        let p := x.pos.withIsStmt
        f := f.modV w fun y => { y with pos := p }
        pending := pending.remove p
  for (j, l, bi) in pending.entries do
    let some b := f.blocks[bi.toNat]? | continue
    let p := (f.getB b).pos
    if (p.line : Int) == l && p.index == j then
      f := f.modB b fun y => { y with pos := p.withIsStmt }
  return (f, pending)

/-- Free dead values and unreachable blocks (`deadcode.go:284-305`). -/
def freeDead (reachable live : Array Bool) (f : Func) : Except String Func := do
  let mut f := f
  for b in f.blocks do
    let mut kept := #[]
    for v in (f.getB b).values do
      if live.getD v false then kept := kept.push v
      else f := f.freeValue v
    f := f.modB b fun x => { x with values := kept }
  let mut blocks := #[]
  for b in f.blocks do
    if reachable.getD b false then blocks := blocks.push b
    else
      if !(f.getB b).values.isEmpty then throw s!"live values in unreachable block b{b}"
      f := f.freeBlock b
  return { f with blocks }

end Deadcode

/-- `deadcode(f)`; `tables` give type sizes (copyelim) and position bases (inlining
indices). -/
def deadcode (tables : Tables) (f : Func) : Except String Func := do
  let reachable := f.reachableBlocks
  let f := Deadcode.removeDeadEdges reachable f
  let f := Deadcode.removeFirstEdges reachable f
  let f ← copyelim tables f
  let (live, order) := f.liveValuesOrder tables reachable
  let f := Deadcode.pruneNames live f
  let some pending := XPosMap.ofCache f.cache.lineStarts
    | throw "deadcode: f.cachedLineStarts is nil"
  let (f, pending) ← Deadcode.unlink reachable live f pending.clear
  let (f, pending) := Deadcode.moveStmts order f pending
  let f := { f with cache := { f.cache with lineStarts := some pending.toCache } }
  Deadcode.freeDead reachable live f

/-- The `deadcode` pass (all instances). -/
def deadcodePass : Pass := Pass.ofFunc fun env f => deadcode env.tables f

end GoFV.Opt
