import GoFV.Opt.Fuse.Basic
import GoFV.SSA.Edges

/-!
# fuseBlockIf (`fuse.go:68-186`)

An `If` block `b` whose two successors (each possibly an empty `Plain` block) converge on the
same block `ss`, with every used phi of `ss` agreeing on the two incoming arguments, drops its
branch: `b.removeEdge(0)`; a now pred-less empty `s0` is unlinked (`s0.removeEdge(0)`), its
(dead) values appended to `b`, and it becomes `BlockInvalid`; `b` becomes `Plain` with
`Likely = BranchUnknown` and no controls; then dead removeable values of `b` (and transitively
their arguments) are `reset(OpInvalid)` through a LIFO worklist (left in place).
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

/-- `isEmpty(b)` (`fuse.go:175`): no value is used, a call, side-effecting, void or a nil
check. -/
def isEmpty (tv : TypeView) (f : Func) (b : ID) : Bool :=
  (f.getB b).values.all fun id =>
    let v := f.getV id
    !(v.uses > 0 || v.op.call || v.op.hasSideEffects || v.type == tv.void || v.op.nilCheck)

/-- The dead-value worklist of `fuseBlockIf` (`fuse.go:157-168`): pop `v`; if it is unused and
removeable, push its arguments and `reset(OpInvalid)` it. -/
def walkDead (tv : TypeView) : Nat → Func → List ID → Except String Func
  | _, f, [] => pure f
  | 0, _, _ :: _ => throw "fuseBlockIf: worklist bound exceeded"
  | fuel + 1, f, v :: rest =>
    let x := f.getV v
    if x.uses == 0 && tv.removeable x then
      walkDead tv fuel (f.resetValue v .Invalid) (x.args.toList.reverse ++ rest)
    else walkDead tv fuel f rest

/-- Bound on worklist pops (each value pushes its arguments at most once, when it is reset). -/
def walkFuel : Nat := 1 <<< 40

/-- `fuseBlockIf(b)`. -/
def fuseBlockIf (tv : TypeView) (f : Func) (b : ID) : Except String (Func × Bool) := do
  let bb := f.getB b
  if bb.kind != .If then return (f, false)
  let plainEmpty (s : ID) : Bool := (f.getB s).kind == .Plain && isEmpty tv f s
  let e0 := bb.succs[0]!
  let (s0, ss0, i0) :=
    if !plainEmpty e0.b then (b, e0.b, e0.i)
    else let e := (f.getB e0.b).succs[0]!; (e0.b, e.b, e.i)
  let e1 := bb.succs[1]!
  let (s1, ss1, i1) :=
    if !plainEmpty e1.b then (b, e1.b, e1.i)
    else let e := (f.getB e1.b).succs[0]!; (e1.b, e.b, e.i)
  let mut s0 := s0
  let mut ss0 := ss0
  if ss0 != ss1 then
    if plainEmpty s0 && plainEmpty s1 then
      if s0 == ss1 then
        s0 := b; ss0 := ss1
      else if ss0 == s1 then
        -- `s1, ss1 = b, ss0`: neither is read again
        pure ()
      else return (f, false)
    else return (f, false)
  let ss := ss0
  for v in (f.getB ss).values do
    let x := f.getV v
    if x.op == .Phi && x.uses > 0 && x.args[i0]! != x.args[i1]! then return (f, false)
  let mut f := f.removeEdge b 0
  if s0 != b && (f.getB s0).preds.size == 0 then
    f := f.removeEdge s0 0
    let vals := (f.getB s0).values
    for v in vals do
      f := f.modV v fun x => { x with block := b }
    f := f.modB b fun x => { x with values := x.values ++ vals }
    f := f.modB s0 fun x =>
      { x with kind := .Invalid, values := #[], succs := #[], preds := #[] }
  f := f.modB b fun x => { x with kind := .Plain, likely := .unknown }
  f := f.resetControls b
  let walk := (f.getB b).values.foldr (init := []) fun v acc =>
    let x := f.getV v
    if x.uses == 0 && tv.removeable x then v :: acc else acc
  -- the worklist pops the last element first
  f ← walkDead tv walkFuel f walk.reverse
  return (f, true)

end GoFV.Opt.Fuse
