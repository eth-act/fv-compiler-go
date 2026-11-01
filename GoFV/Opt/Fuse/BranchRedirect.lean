import GoFV.Opt.Prove.FactsTable
import GoFV.SSA.Edges

/-!
# fuseBranchRedirect (`fuse_branchredirect.go`)

For each `If` block `b` (backwards over `f.Blocks`) that is empty or contains only its control
(used once), and each `If` predecessor `p` of `b` (`p ≠ b`): assume the branch `p → b`, then
try each branch of `b` under a checkpoint of prove's facts table; if one is unsatisfiable,
redirect `p` straight to the other successor `child` (unless `child = b`): `b.removePred(k)`
(swap-with-last) with `removePhiArg` on `b`'s phis, `p.Succs[pk.i] = {child, len(child.Preds)}`,
append the predecessor to `child` and the corresponding argument to each of its phis, and
reprocess index `k`. A non-entry `b` left without predecessors becomes `BlockInvalid` (its
successors, controls and values stay). The facts table only reads the function
(`newFactsTable`, `addBranchRestrictions`); `cleanup` has no effect on it.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA GoFV.Opt.Prove

/-- Redirect `p` (predecessor `k` of `b`, reached through `b.Preds[k]`) to `b.Succs[out]`. -/
def redirect (f : Func) (b : ID) (k : Nat) (out : Nat) : Func := Id.run do
  let pk := (f.getB b).preds[k]!
  let p := pk.b
  let se := (f.getB b).succs[out]!
  let child := se.b
  let mut f := f.removePred b k
  let cn := (f.getB child).preds.size
  f := f.modB p fun x => { x with succs := x.succs.set! pk.i ⟨child, cn⟩ }
  for v in (f.getB b).values do
    if (f.getV v).op == .Phi then f := f.removePhiArg b v k
  f := f.modB child fun x => { x with preds := x.preds.push ⟨p, pk.i⟩ }
  let ai := (f.getB b).succs[out]!.i
  for v in (f.getB child).values do
    let x := f.getV v
    if x.op == .Phi then f := f.addArg v x.args[ai]!
  return f

/-- The facts-table decision for predecessor `k` of `b`: `some out` if `b`'s branch `1 - out` is
unsatisfiable after `p`'s branch into `b` (and `b.Succs[out]` is not `b`). -/
def tryPredOut (pv : Prover) (f : Func) (ft : FactsTable) (b : ID) (k : Nat) :
    FactsTable × Option Nat := Id.run do
  let pk := (f.getB b).preds[k]!
  let p := pk.b
  if (f.getB p).kind != .If || p == b then return (ft, none)
  let pbranch := if pk.i == 1 then Branch.negative else Branch.positive
  let mut ft := pv.addBranchRestrictions f ft.checkpoint p pbranch
  for (j, bbranch) in [(0, Branch.positive), (1, Branch.negative)] do
    let ft' := pv.addBranchRestrictions f ft.checkpoint b bbranch
    let unsat := ft'.unsat
    ft := ft'.restore
    if !unsat then continue
    let out := 1 - j
    if (f.getB b).succs[out]!.b == b then continue
    return (ft.restore, some out)
  return (ft.restore, none)

/-- Try predecessor `k` of `b`: `some f'` if it was redirected (`k` is then reprocessed). -/
def tryPred (pv : Prover) (f : Func) (ft : FactsTable) (b : ID) (k : Nat) :
    FactsTable × Option Func :=
  let (ft, o) := tryPredOut pv f ft b k
  (ft, o.map (redirect f b k))

/-- The predecessor loop of one block (`k--` after a redirect reprocesses index `k`). -/
def predLoop (pv : Prover) (b : ID) : Nat → Func → FactsTable → Nat → Bool →
    Func × FactsTable × Bool
  | 0, f, ft, _, changed => (f, ft, changed)
  | fuel + 1, f, ft, k, changed =>
    if k < (f.getB b).preds.size then
      match tryPred pv f ft b k with
      | (ft, some f) => predLoop pv b fuel f ft k true
      | (ft, none) => predLoop pv b fuel f ft (k + 1) changed
    else (f, ft, changed)

/-- `fuseBranchRedirect(f)`. -/
def fuseBranchRedirect (pv : Prover) (f : Func) : Except String (Func × Bool) := do
  let mut ft := (FactsTable.new pv.cx f).checkpoint
  let mut f := f
  let mut changed := false
  let blocks := f.blocks
  for idx in [0:blocks.size] do
    let b := blocks[blocks.size - 1 - idx]!
    let bb := f.getB b
    if bb.kind != .If then continue
    let ctl := f.getV bb.controls[0]!
    if (ctl.block != b && bb.values.size != 0) ||
        ((bb.values.size != 1 || ctl.uses != 1) && ctl.block == b) then continue
    -- every redirect removes one predecessor of `b`
    let n := bb.preds.size
    let (f', ft', c) := predLoop pv b (2 * n + 2) f ft 0 false
    f := f'; ft := ft'; changed := c || changed
    if (f.getB b).preds.size == 0 && b != f.entry then
      f := f.modB b fun x => { x with kind := .Invalid }
  if let some e := ft.err then throw e
  return (f, changed)

end GoFV.Opt.Fuse
