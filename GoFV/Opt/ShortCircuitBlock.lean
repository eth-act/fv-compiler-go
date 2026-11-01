import GoFV.Opt.Fuse.Basic
import GoFV.SSA.Edges

/-!
# `shortcircuitBlock` (`shortcircuit.go:104-556`)

`shortcircuitBlock f b` redirects the predecessor `p` of the `If` block `b` that supplies a
`ConstBool` to `b`'s control phi straight to the successor `t` that constant selects, fixing the
other phis of `b` with one of the five `shortcircuitPhiPlan` shapes. It is split into the guards
(`siteOf`: the rewrite's site, `none` if it does not fire) and the rewrite itself (`applySite`),
so the checked step (`ShortCircuitBlockCheck.lean`) can keep the input only when the rewrite
fires.

The map iterations of the Go code are order-independent (`docs/PASSES.md`, short circuit):
`replaceUses` over `flowsTo`'s block set rewrites disjoint blocks; the others compute booleans.
-/

namespace GoFV.Opt.ShortCircuit

open GoFV.SSA GoFV.Opt.Fuse

/-! ## `flowsTo` (`shortcircuit.go:556`) -/

structure DfsState where
  seen : Array ID := #[]
  visited : Array ID := #[]
  hasPathToT : Bool := false
  fullyExplored : Bool := true
  isDAG : Bool := true

/-- `boundedDFS(b)`; the recursion depth is at most `cap + 2` (every frame adds to `seen`). -/
def boundedDFS (f : Func) (t : ID) (cap : Nat) : Nat → DfsState → ID → DfsState
  | 0, s, _ => { s with fullyExplored := false }
  | fuel + 1, s, b =>
    if s.seen.contains b then s
    else if s.visited.contains b then { s with isDAG := false }
    else if b == t then { s with hasPathToT := true }
    else if s.seen.size > cap then { s with fullyExplored := false }
    else
      let s := { s with seen := s.seen.push b, visited := s.visited.push b }
      let succs := (f.getB b).succs
      let rec loop : Nat → DfsState → DfsState
        | 0, s => { s with visited := s.visited.erase b }
        | k + 1, s =>
          let s := boundedDFS f t cap fuel s succs[succs.size - (k + 1)]!.b
          if !(s.isDAG && s.fullyExplored) then s else loop k s
      loop succs.size s

/-- `v.flowsTo(t, cap)`: the explored block set (`seen`, DFS order) or `none`. -/
def flowsTo (f : Func) (v t : ID) (cap : Nat) : Option (Array ID) :=
  let s := boundedDFS f t cap (cap + 3) {} v
  if s.hasPathToT && s.fullyExplored && s.isDAG then
    if s.seen.all fun b => b == v || (f.getB b).preds.all fun e => s.seen.contains e.b then
      some s.seen
    else none
  else none

/-! ## Phi plans (`shortcircuit.go:278-495`) -/

/-- The five CFG shapes of `shortcircuitPhiPlan`, with the blocks their fix-up needs. -/
inductive Plan where
  /-- `t` and the `flowsTo` set `U` of `u` merge at `m`. -/
  | merge (t m : ID) (visited : Array ID)
  /-- `u`'s `flowsTo` set flows into `t`. -/
  | uIntoT (t : ID) (visited : Array ID)
  /-- `t` falls into `u`. -/
  | tIntoU (t u : ID)
  /-- `t` exits. -/
  | tExits (t u : ID)
  /-- `u` exits. -/
  | uExits (t u : ID)
  deriving Inhabited

/-- `shortcircuitPhiPlan(b, ctl, cidx, ti)`, evaluated before the CFG changes. -/
def phiPlan (f : Func) (b : ID) (ti : Nat) : Option Plan := Id.run do
  let bb := f.getB b
  let t := bb.succs[ti]!.b
  let u := bb.succs[1 - ti]!.b
  let p0 := bb.preds[0]!.b
  let p1 := bb.preds[1]!.b
  if p0 == t || p1 == t || p0 == u || p1 == u then return none
  let tb := f.getB t
  let ub := f.getB u
  if tb.preds.size == 1 && tb.succs.size == 1 && ub.preds.size == 1 &&
      (f.getB tb.succs[0]!.b).preds.size == 2 then
    let m := tb.succs[0]!.b
    if let some visited := flowsTo f u m 5 then return some (.merge t m visited)
  if tb.preds.size == 2 && ub.preds.size == 1 then
    if let some visited := flowsTo f u t 5 then return some (.uIntoT t visited)
  if ub.preds.size == 2 && tb.preds.size == 1 && tb.succs.size == 1 && tb.succs[0]!.b == u then
    return some (.tIntoU t u)
  if tb.preds.size == 1 && ub.preds.size == 1 && tb.succs.size == 0 then
    return some (.tExits t u)
  if ub.preds.size == 1 && tb.preds.size == 1 && ub.succs.size == 0 then
    return some (.uExits t u)
  return none

/-- A new phi `(argQ, argP)` in `t` at `v`'s position replacing `v`'s uses in `t`. -/
def splitPhi (f : Func) (v t argQ argP : ID) : Func × ID :=
  let x := f.getV v
  let (f, phi) := f.newValueArgs t x.pos .Phi x.type (args := #[argQ, argP])
  (replaceUses f t v phi, phi)

/-- The plan's `fixPhi(v, i)` (after the CFG changes; `i` is `v`'s index in `b.Values`). -/
def fixPhi (plan : Plan) (cidx : Nat) (f : Func) (v : ID) (i : Nat) : Func :=
  let args := (f.getV v).args
  let argP := args[cidx]!
  let argQ := args[1 - cidx]!
  match plan with
  | .merge t m visited =>
    let (f, phi) := splitPhi f v t argQ argP
    let f := visited.foldl (fun f bb => replaceUses f bb v argQ) f
    if (f.getV v).uses == 0 then f else
    let f := moveTo f v m i
    if (f.getB m).preds[0]!.b == t then f.setArgs v #[phi, argQ] else f.setArgs v #[argQ, phi]
  | .uIntoT t visited =>
    let f := visited.foldl (fun f bb => replaceUses f bb v argQ) f
    (moveTo f v t i).setArgs v #[argQ, argQ, argP]
  | .tIntoU t u =>
    let (f, phi) := splitPhi f v t argQ argP
    if (f.getV v).uses == 0 then f else
    (moveTo f v u i).setArgs v #[argQ, phi]
  | .tExits t u =>
    let (f, _) := splitPhi f v t argQ argP
    if (f.getV v).uses == 0 then f else
    (moveTo f v u i).setArgs v #[argQ]
  | .uExits t u =>
    let f := replaceUses f u v argQ
    (moveTo f v t i).setArgs v #[argQ, argP]

/-! ## `shortcircuitBlock` (`shortcircuit.go:104`) -/

/-- Unwrap the `Copy`/`Not` chain of `b`'s control (`shortcircuit.go:111-118`): the phi
candidate, the number of values in the chain, and the negation parity. -/
def unwrapControl (f : Func) (b : ID) : Nat → ID → Nat → Nat → ID × Nat × Nat
  | 0, ctl, nval, swap => (ctl, nval, swap)
  | fuel + 1, ctl, nval, swap =>
    let x := f.getV ctl
    if x.uses == 1 && x.block == b && (x.op == .Copy || x.op == .Not) then
      unwrapControl f b fuel x.args[0]! (nval + 1) (if x.op == .Not then 1 - swap else swap)
    else (ctl, nval, swap)

/-- After `fixPhi` moved `phi` to another block: that block's other phis that use `phi` take
the matching argument of `phi` instead, then `phielimValue(phi)` or `phi.reset(OpInvalid)`. -/
def afterMove (f : Func) (phi : ID) : Func := Id.run do
  let mut f := f
  for v in (f.getB (f.getV phi).block).values do
    let x := f.getV v
    if x.op != .Phi || v == phi then continue
    for j in [0:x.args.size] do
      if (f.getV v).args[j]! == phi then f := f.setArg v j (f.getV phi).args[j]!
  if (f.getV phi).uses != 0 then return (f.phielimValue phi).1
  return f.resetValue phi .Invalid

/-- The loop over `b.Values` fixing the other phis (`shortcircuit.go:224-256`); a moved phi
leaves another value at index `i`, which is reprocessed. -/
def fixOtherPhis (plan : Plan) (cidx : Nat) (b ctl : ID) : Nat → Func → Nat → Func
  | 0, f, _ => f
  | fuel + 1, f, i =>
    let vals := (f.getB b).values
    if h : i < vals.size then
      let phi := vals[i]
      let x := f.getV phi
      if x.uses == 0 || phi == ctl || x.op != .Phi then fixOtherPhis plan cidx b ctl fuel f (i + 1)
      else
        let f := fixPhi plan cidx f phi i
        if (f.getV phi).block == b then fixOtherPhis plan cidx b ctl fuel f (i + 1)
        else fixOtherPhis plan cidx b ctl fuel (afterMove f phi) i
    else f

/-- The site of a `shortcircuitBlock` rewrite: the `If` block `b`, its control phi `ctl`, the
predecessor `p = b.Preds[cidx]` (its successor `pi`) supplying a `ConstBool`, the successor edge
`te` of `b` that constant selects, and the plan for `b`'s other phis. -/
structure Site where
  b : ID
  ctl : ID
  cidx : Nat
  p : ID
  pi : Nat
  te : Edge
  plan : Option Plan
  deriving Inhabited

/-- The guards of `shortcircuitBlock(b)` (`shortcircuit.go:104-176`): its site if it fires. -/
def siteOf (f : Func) (b : ID) : Option Site := Id.run do
  let bb := f.getB b
  if bb.kind != .If then return none
  let (ctl, nval, swap) := unwrapControl f b (bb.values.size + 1) bb.controls[0]! 1 0
  let cx := f.getV ctl
  if cx.op != .Phi || cx.block != b || cx.uses != 1 then return none
  let isPhi (w : ID) : Bool := (f.getV w).op == .Phi
  let nOtherPhi := bb.values.countP fun w => isPhi w && w != ctl
  if nOtherPhi > 0 && bb.preds.size != 2 then return none
  if bb.values.size != nval + nOtherPhi then return none
  if nOtherPhi > 0 then
    -- every value of `b` is a phi or in the control chain; a phi's argument in `b.Values`
    -- that is a phi other than itself rejects
    for v in bb.values do
      if !isPhi v then continue
      for a in (f.getV v).args do
        if a != v && isPhi a && bb.values.contains a then return none
  let some cidx := cx.args.findIdx? fun a => (f.getV a).op == .ConstBool | return none
  let pe := bb.preds[cidx]!
  let ti := (1 ^^^ (f.getV cx.args[cidx]!).auxInt ^^^ swap.toInt64).toInt.toNat
  let te := bb.succs[ti]!
  if pe.b == b || te.b == b then return none
  let mut plan : Option Plan := none
  if nOtherPhi > 0 then
    match phiPlan f b ti with
    | some pl => plan := some pl
    | none => return none
  return some { b, ctl, cidx, p := pe.b, pi := pe.i, te, plan }

/-- The rewrite of `shortcircuitBlock(b)` at its site (`shortcircuit.go:178-275`). -/
def applySite (f : Func) (s : Site) : Func := Id.run do
  let b := s.b
  let t := s.te.b
  let mut f := (f.removePred b s.cidx).removePhiArg b s.ctl s.cidx
  let tn := (f.getB t).preds.size
  f := f.modB s.p fun x => { x with succs := x.succs.set! s.pi ⟨t, tn⟩ }
  f := f.modB t fun x => { x with preds := x.preds.push ⟨s.p, s.pi⟩ }
  for v in (f.getB t).values do
    let x := f.getV v
    if x.op != .Phi then continue
    f := f.addArg v x.args[s.te.i]!
  if let some pl := s.plan then
    let n := (f.getB b).values.size
    f := fixOtherPhis pl s.cidx b s.ctl (2 * n + 2) f 0
    for v in (f.getB b).values do
      if (f.getV v).uses == 0 then f := f.resetValue v .Invalid
  if (f.getB b).preds.size == 0 then f := f.modB b fun x => { x with kind := .Invalid }
  return (f.phielimValue s.ctl).1

/-- `shortcircuitBlock(b)`. -/
def shortcircuitBlock (f : Func) (b : ID) : Func × Bool :=
  match siteOf f b with
  | none => (f, false)
  | some s => (applySite f s, true)

end GoFV.Opt.ShortCircuit
