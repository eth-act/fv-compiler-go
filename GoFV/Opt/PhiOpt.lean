import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache
import GoFV.Rules.Helpers.Types

/-!
# phiopt (`phiopt.go`, `lca.go`)

Two sweeps over `f.Blocks` with the dominator tree `f.Sdom()` taken once (the CFG is never
changed; `docs/PASSES.md`, phiopt):

1. Blocks with two predecessors whose predecessor chains (through single-pred single-succ
   blocks) meet at one `If` block `b0`: integer phis of `0`/`1` constants become
   `ZeroExt8toN (CvtBoolToUint8 [Not] ctrl)` (or a `Copy` for one byte; `phioptint`), boolean
   phis become `Copy`/`Not` of the control or `OrB`/`AndB` with a dominating value.
2. "Strengthened": the first boolean phi of two different `ConstBool`s per block is replaced by
   a `Copy`/`Not` of the control of the `If` block that dominates both predecessors through
   distinct single-pred successors (`convertPhi`). As in Go, a match of the special cases (a
   predecessor is the dominating `If`) that fails the dominance test moves on to the next phi;
   every other outcome ends the block.

`lcaRange.find` (an Euler-tour range-minimum structure) returns the lowest common ancestor in
the dominator tree, which is unique, so it is computed here by walking `f.Idom()`; on blocks
outside the tree (never reached after `opt deadcode`) Go returns `f.Entry` for one such block
and panics for two distinct ones; so does the port.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Analysis

namespace PhiOpt

/-- Walk up from `(pb, b)` while `b` has a single successor and a single predecessor; `fuel`
bounds the walk (a cycle of such blocks is unreachable, removed by `opt deadcode`). -/
def walkUp (f : Func) : Nat → ID → ID → Except String (ID × ID)
  | 0, _, b => throw s!"phiopt: unbounded predecessor chain at b{b}"
  | fuel + 1, pb, b =>
    let x := f.getB b
    if x.succs.size == 1 && x.preds.size == 1 then walkUp f fuel b x.preds[0]!.b
    else pure (pb, b)

/-- `lca.find(a, b)` over the immediate dominators `idom` (`lca.go:105`). -/
def lcaFind (f : Func) (idom : Array (Option ID)) (a b : ID) : Except String ID := do
  if a == b then return a
  let inTree (x : ID) : Bool := x == f.entry || (idom[x]?).join.isSome
  match inTree a, inTree b with
  | true, true =>
    -- dominators of `a` (fuel: tree depth < number of blocks)
    let n := f.bidLast + 1
    let mut anc := Array.replicate n false
    let mut x := a
    for _ in [0:n] do
      anc := anc.set! x true
      match (idom[x]?).join with
      | some p => x := p
      | none => break
    let mut y := b
    for _ in [0:n] do
      if anc.getD y false then return y
      match (idom[y]?).join with
      | some p => y := p
      | none => break
    throw s!"phiopt: no common dominator of b{a} and b{b}"
  | true, false | false, true => return f.entry
  | false, false => throw s!"phiopt: lca of unreachable blocks b{a}, b{b}"

/-- `phioptint(v, b0, reverse)`. -/
def phioptint (tabs : Tables) (uint8 : TypeRef) (f : Func) (v b0 : ID) (reverse : Nat) :
    Except String Func := do
  let x := f.getV v
  let a0 := f.getV x.args[0]!
  let a1 := f.getV x.args[1]!
  if a0.op != a1.op then return f
  match a0.op with
  | .Const8 | .Const16 | .Const32 | .Const64 => pure ()
  | _ => return f
  let negate ←
    if a0.auxInt == 0 && a1.auxInt == 1 then pure true
    else if a0.auxInt == 1 && a1.auxInt == 0 then pure false
    else return f
  let negate := if reverse == 1 then !negate else negate
  let mut f := f
  let mut a := (f.getB b0).controls[0]!
  if negate then
    let (f', n) := f.newValueArgs x.block x.pos .Not (f.getV a).type (args := #[a])
    f := f'
    a := n
  f := f.addArg v a
  let (f', cvt) := f.newValueArgs x.block x.pos .CvtBoolToUint8 uint8 (args := #[a])
  f := f'
  let op ← match ← Rules.Ty.size tabs x.type with
    | 1 => pure Op.Copy
    | 2 => pure Op.ZeroExt8to16
    | 4 => pure Op.ZeroExt8to32
    | 8 => pure Op.ZeroExt8to64
    | n => throw s!"phiopt: v{v}: bad int size {n}"
  return (f.resetValue v op).addArg v cvt

/-- `ops[c]` with `ops = [OpNot, OpCopy]`. -/
@[inline] def notOrCopy (c : Int64) : Op := if c == 0 then .Not else .Copy

/-- `convertPhi(b, v, reverse)`. -/
def convertPhi (f : Func) (b v : ID) (reverse : Nat) : Func :=
  let op := notOrCopy (f.getV (f.getV v).args[reverse]!).auxInt
  (f.resetValue v op).addArg v (f.getB b).controls[0]!

/-- `v.reset(op); v.SetArgs2(a, b)`. -/
@[inline] def reset2 (f : Func) (v : ID) (op : Op) (a b : ID) : Func :=
  (f.resetValue v op).setArgs v #[a, b]

/-- The boolean-phi rewrites of the first sweep; `none` when no rule applies. -/
def boolPhi (sdom : SparseTree) (f : Func) (b b0 v : ID) (reverse : Nat) : Option Func :=
  let x := f.getV v
  let ctrl := (f.getB b0).controls[0]!
  let r := x.args[reverse]!
  let nr := x.args[1 - reverse]!
  let rv := f.getV r
  let nrv := f.getV nr
  if (f.getV x.args[0]!).op == .ConstBool && (f.getV x.args[1]!).op == .ConstBool &&
      rv.auxInt != nrv.auxInt then
    some ((f.resetValue v (notOrCopy rv.auxInt)).addArg v ctrl)
  else if rv.op == .ConstBool && rv.auxInt == 1 && sdom.isAncestorEq nrv.block b then
    some (reset2 f v .OrB ctrl nr)
  else if nrv.op == .ConstBool && nrv.auxInt == 0 && sdom.isAncestorEq rv.block b then
    some (reset2 f v .AndB ctrl r)
  else if nr == ctrl && sdom.isAncestorEq rv.block b then
    some (reset2 f v .AndB ctrl r)
  else if r == ctrl && sdom.isAncestorEq nrv.block b then
    some (reset2 f v .OrB ctrl nr)
  else none

/-- The first sweep on block `b`. -/
def sweep1Block (tabs : Tables) (uint8 : TypeRef) (sdom : SparseTree) (f : Func) (b : ID) :
    Except String Func := do
  let bb := f.getB b
  if bb.preds.size != 2 || bb.values.isEmpty then return f
  let fuel := f.blocks.size + 1
  let (pb0, b0) ← walkUp f fuel b bb.preds[0]!.b
  if (f.getB b0).kind != .If then return f
  let (pb1, b1) ← walkUp f fuel b bb.preds[1]!.b
  if b1 != b0 then return f
  let s := (f.getB b0).succs
  let reverse : Nat ←
    if s[0]!.b == pb0 && s[1]!.b == pb1 then pure 0
    else if s[0]!.b == pb1 && s[1]!.b == pb0 then pure 1
    else throw s!"phiopt: b{b}: invalid predecessors"
  let mut f := f
  for v in bb.values do
    let x := f.getV v
    if x.op != .Phi then continue
    let k ← Rules.Ty.kind tabs x.type
    if Rules.Ty.isIntegerKind k then f ← phioptint tabs uint8 f v b0 reverse
    if k != .BOOL then continue
    if let some f' := boolPhi sdom f b b0 v reverse then f := f'
  return f

/-- The strengthened sweep on block `b` (`lca` is built on first use, as in Go; building it is
pure, so only its inputs are threaded). -/
def sweep2Block (sdom : SparseTree) (idom : Array (Option ID)) (f : Func) (b : ID) :
    Except String Func := do
  let bb := f.getB b
  if bb.preds.size != 2 || bb.values.isEmpty then return f
  let mut f := f
  for v in bb.values do
    let x := f.getV v
    if x.op != .Phi then continue
    let a0 := f.getV x.args[0]!
    let a1 := f.getV x.args[1]!
    if a0.op != .ConstBool || a1.op != .ConstBool then continue
    if a0.auxInt == a1.auxInt then continue
    let pb0 := bb.preds[0]!.b
    let pb1 := bb.preds[1]!.b
    let parent := sdom.parent b
    if (f.getB pb0).kind == .If && parent == some pb0 then
      let ei := bb.preds[0]!.i
      let sb1 := (f.getB pb0).succs[1 - ei]!.b
      if sdom.isAncestorEq sb1 pb1 then
        f := convertPhi f pb0 v ei
        break
    else if (f.getB pb1).kind == .If && parent == some pb1 then
      let ei := bb.preds[1]!.i
      let sb0 := (f.getB pb1).succs[1 - ei]!.b
      if sdom.isAncestorEq sb0 pb0 then
        f := convertPhi f pb1 v (1 - ei)
        break
    else
      let b0 ← lcaFind f idom pb0 pb1
      let x0 := f.getB b0
      if x0.kind != .If then break
      let sb0 := x0.succs[0]!.b
      let sb1 := x0.succs[1]!.b
      let reverse : Nat ←
        if sdom.isAncestorEq sb0 pb0 && sdom.isAncestorEq sb1 pb1 then pure 0
        else if sdom.isAncestorEq sb1 pb0 && sdom.isAncestorEq sb0 pb1 then pure 1
        else break
      if (f.getB sb0).preds.size != 1 || (f.getB sb1).preds.size != 1 then break
      f := convertPhi f b0 v reverse
      break
  return f

end PhiOpt

open PhiOpt in
/-- `phiopt(f)`; `uint8` is `Config.Types.UInt8`. -/
def phiopt (tabs : Tables) (uint8 : TypeRef) (f : Func) : Except String Func := do
  let (sdom, f) := f.sdom
  let f ← f.blocks.foldlM (sweep1Block tabs uint8 sdom) f
  -- `makeLCArange` reads `f.Idom()`, already cached by `f.Sdom()`
  let (idom, f) := f.idom
  f.blocks.foldlM (sweep2Block sdom idom) f

end GoFV.Opt
