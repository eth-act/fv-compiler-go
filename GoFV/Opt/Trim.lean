import GoFV.Opt.Pass
import GoFV.Opt.NumberLines
import GoFV.SSA.Alloc

/-!
# trim (`trim.go`)

Port of `trim` (go1.27.3; docs/PASSES2.md, trim, #412). One scan of `f.Blocks`: a `Plain`
non-entry block `b` whose successor `s ≠ b` has `b` as its only predecessor, or whose values are
all phis, is spliced out. `b`'s first predecessor takes `b`'s slot `j` in `s.Preds`, the others
are appended. A statement mark of `b` moves to `s`'s first value that is not a poor statement op
(if on the same line), else to `s` itself. If `s` had several predecessors, `s`'s phis get
`b`'s phi's arguments (or their own argument at `j` repeated) for the new edges (`mergePhi`),
and `b`'s phis still used are padded with self references; unused ones are dropped (not
freed). `b`'s remaining values move to the front of `s`. Removed blocks are not freed (their
`FlagsLiveAtEnd`/`Hotness` leave with them: the export lists those of `f.Blocks`); the CFG
caches are invalidated if any block was removed. `RegAlloc` is untouched.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Trim

/-- `emptyBlock(b)`: all values are phis. -/
def emptyBlock (f : Func) (blk : Block) : Bool := blk.values.all fun v => (f.getV v).op == .Phi

/-- `trimmableBlock(b)`. -/
def trimmable (f : Func) (blk : Block) : Bool :=
  if blk.kind != .Plain || blk.id == f.entry then false else
  match blk.succs[0]? with
  | none => false
  | some e => e.b != blk.id && ((f.getB e.b).preds.size == 1 || emptyBlock f blk)

/-- `mergePhi(v, i, b)`. -/
def mergePhi (f : Func) (v : ID) (i : Nat) (b : ID) : Except String Func := do
  let some u := (f.getV v).args[i]? | throw s!"mergePhi: v{v} has no argument {i}"
  let ux := f.getV u
  if ux.block == b then
    if ux.op != .Phi then throw s!"value v{u} is not a phi operation"
    let f := f.setArg v i ux.args[0]!
    return f.addArgs v (ux.args.extract 1 ux.args.size)
  else
    let mut f := f
    for _ in [1:(f.getB b).preds.size] do
      f := f.addArg v (f.getV v).args[i]!
    return f

/-- Splice the trimmable block `b` out (`trim.go:20-104`). -/
def splice (f : Func) (b : ID) : Except String Func := do
  let blk := f.getB b
  let bPos := blk.pos
  let bIsStmt := bPos.isStmt == Pos.isStmtMark
  let some (pe : Edge) := blk.preds[0]? | throw s!"trim: b{b} has no predecessor"
  let p := pe.b
  let i := pe.i
  let some (se : Edge) := blk.succs[0]? | throw s!"trim: b{b} has no successor"
  let s := se.b
  let j := se.i
  let ns := (f.getB s).preds.size
  let mut f := f.modB p fun x => { x with succs := x.succs.set! i ⟨s, j⟩ }
  f := f.modB s fun x => { x with preds := x.preds.set! j ⟨p, i⟩ }
  for e in blk.preds.extract 1 blk.preds.size do
    let n := (f.getB s).preds.size
    f := f.modB e.b fun x => { x with succs := x.succs.set! e.i ⟨s, n⟩ }
    f := f.modB s fun x => { x with preds := x.preds.push ⟨e.b, e.i⟩ }
  -- preserve a statement boundary
  if bIsStmt then
    let mut sawStmt := false
    for v in (f.getB s).values do
      let x := f.getV v
      if NumberLines.isPoorStatementOp x.op then continue
      if x.pos.sameFileAndLine bPos then f := f.modV v fun y => { y with pos := y.pos.withIsStmt }
      sawStmt := true
      break
    let spos := (f.getB s).pos
    if !sawStmt && spos.sameFileAndLine bPos then
      f := f.modB s fun y => { y with pos := spos.withIsStmt }
  let mut bvals := blk.values
  if ns > 1 then
    for v in (f.getB s).values do
      if (f.getV v).op == .Phi then f ← mergePhi f v j b
    let mut keep : Array ID := #[]
    for v in bvals do
      let x := f.getV v
      if x.op == .Phi then
        if x.uses == 0 then
          f := (f.resetArgs v)
          f := { f with valueTab := f.valueTab.set! v none }
          continue
        let args := x.args
        f := f.resetArgs v
        for _ in [0:j] do f := f.addArg v v
        f := f.addArg v args[0]!
        for _ in [j + 1:ns] do f := f.addArg v v
        f := f.addArgs v (args.extract 1 args.size)
      keep := keep.push v
    bvals := keep
  for v in bvals do
    f := f.modV v fun y => { y with block := s }
  f := f.modB s fun y => { y with values := bvals ++ y.values }
  return f

end Trim

open Trim in
/-- `trim(f)`. -/
def trim (f : Func) : Except String Func := do
  let mut f := f
  let mut keep : Array ID := #[]
  for b in f.blocks do
    if !trimmable f (f.getB b) then
      keep := keep.push b
      continue
    f ← splice f b
    -- the block object leaves the function with its `FlagsLiveAtEnd` and `Hotness`
    f := { f with blockTab := f.blockTab.set! b none
                  low := { f.low with flagsLive := f.low.flagsLive.filter (· != b)
                                      hotness := f.low.hotness.filter (·.1 != b) } }
  if keep.size < f.blocks.size then
    f := { f.invalidateCFG with blocks := keep }
  return f

/-- The `trim` pass. -/
def trimPass : Pass := Pass.ofFunc fun _ f => trim f

end GoFV.Opt
