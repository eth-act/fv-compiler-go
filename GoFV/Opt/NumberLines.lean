import GoFV.Opt.Pass
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.XPosMap
import Std.Data.HashMap.Basic

/-!
# number lines (`numberlines.go`)

Port of `numberLines` (`ssa/numberlines.go:111-262`, go1.27.3; docs/PASSES.md, number lines).
Only positions change: walking the reachable blocks in reverse (cached) postorder, the first
"good" value of each block and every value starting a new line get `IsStmt`, other values with
a statement-capable position get `DefaultStmt`; an effectively empty block takes its line from
its predecessors. The pass leaves `f.postorder()` cached and replaces `f.cachedLineStarts` with
an empty `xposmap` over the noted files and line ranges.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace NumberLines

/-- `isPoorStatementOp` (`numberlines.go:13`). -/
def isPoorStatementOp : Op → Bool
  | .Addr | .LocalAddr | .OffPtr | .StructSelect | .Phi | .ITab | .IData | .IMake | .StringMake
  | .SliceMake | .StructMake | .ConstBool | .Const8 | .Const16 | .Const32 | .Const64 | .Const32F
  | .Const64F | .SB | .SP | .ArgIntReg | .ArgFloatReg => true
  | _ => false

@[inline] private def vpos (f : Func) (v : ID) : Pos := ((f.value? v).map (·.pos)).getD default
@[inline] private def vop (f : Func) (v : ID) : Op := ((f.value? v).map (·.op)).getD default
@[inline] private def setVPos (f : Func) (v : ID) (p : Pos) : Func :=
  { f with valueTab := f.valueTab.modify v (Option.map fun x => { x with pos := p }) }
@[inline] private def setBPos (f : Func) (b : ID) (p : Pos) : Func :=
  { f with blockTab := f.blockTab.modify b (Option.map fun x => { x with pos := p }) }

/-- `nextGoodStatementIndex(v, i, b)` (`numberlines.go:31`): from a poor statement op at index
`i`, the index of the next non-poor value on the same file and line (skipping not-statement
values), if no other line intervenes; else `i`. -/
def nextGoodStatementIndex (f : Func) (vals : Array ID) (v : ID) (i : Nat) : Nat := Id.run do
  if i + 1 ≥ vals.size then return i
  if !isPoorStatementOp (vop f v) then return i
  let vp := vpos f v
  for j in [i + 1:vals.size] do
    let u := vals[j]!
    let up := vpos f u
    if up.isStmt == Pos.notStmt then continue
    if up.sameFileAndLine vp then
      if isPoorStatementOp (vop f u) then continue
      return j
    return i
  return i

/-- `note(p)`: widen file `p.index`'s line range to include `p.line`. -/
@[inline] def note (ranges : Std.HashMap Nat (Nat × Nat)) (p : Pos) : Std.HashMap Nat (Nat × Nat) :=
  match ranges[p.index]? with
  | none => ranges.insert p.index (p.line, p.line)
  | some (first, last) =>
    if p.line < first || p.line > last then ranges.insert p.index (min first p.line, max last p.line)
    else ranges

end NumberLines

open NumberLines in
/-- `numberLines(f)`. -/
def numberLines (f : Func) : Func := Id.run do
  let (po, f) := f.postorder
  let mut f := f
  let mut endlines : Array Pos := Array.replicate (f.bidLast + 1) Pos.none
  let mut ranges : Std.HashMap Nat (Nat × Nat) := {}
  for k in [0:po.size] do
    let b := po[po.size - 1 - k]!
    let some blk := f.block? b | continue
    let vals := blk.values
    let mut firstPos := Pos.none
    let mut firstPosIndex : Option Nat := none
    if blk.pos.isStmt != Pos.notStmt then ranges := note ranges blk.pos
    for h : i in [0:vals.size] do
      let p := vpos f vals[i]
      if p.isStmt != Pos.notStmt then
        ranges := note ranges p
        let i := nextGoodStatementIndex f vals vals[i] i
        firstPosIndex := some i
        firstPos := vpos f vals[i]!
        f := setVPos f vals[i]! firstPos.withDefaultStmt
        break
    let some fpi := firstPosIndex
      | -- effectively empty block: check the block's own Pos, consider preds
        let mut line := Pos.none
        for e in blk.preds do
          let el := endlines.getD e.b Pos.none
          if !el.sameFileAndLine line then
            if line == Pos.none then
              line := el
              continue
            else
              line := Pos.none
              break
        if blk.pos.isStmt == Pos.notStmt then
          f := setBPos f b line
          endlines := endlines.set! b line
          continue
        let bpos := if line == Pos.none || !line.sameFileAndLine blk.pos then blk.pos.withIsStmt
          else blk.pos
        f := setBPos f b bpos
        endlines := endlines.set! b bpos
        continue
    if blk.preds.isEmpty then
      -- the entry block
      f := setVPos f vals[fpi]! firstPos.withIsStmt
    else
      -- differing pred
      for e in blk.preds do
        if !(endlines.getD e.b Pos.none).sameFileAndLine firstPos then
          f := setVPos f vals[fpi]! firstPos.withIsStmt
          break
    let mut i := fpi + 1
    for _ in [0:vals.size] do
      if i ≥ vals.size then break
      let p := vpos f vals[i]!
      if p.isStmt == Pos.notStmt then
        i := i + 1
        continue
      ranges := note ranges p
      i := nextGoodStatementIndex f vals vals[i]! i
      let v := vals[i]!
      let vp := vpos f v
      if !vp.sameFileAndLine firstPos then
        firstPos := vp
        f := setVPos f v vp.withIsStmt
      else
        f := setVPos f v vp.withDefaultStmt
      i := i + 1
    if blk.pos.isStmt != Pos.notStmt && !blk.pos.sameFileAndLine firstPos then
      let bpos := blk.pos.withIsStmt
      f := setBPos f b bpos
      firstPos := bpos
    endlines := endlines.set! b firstPos
  let xm := XPosMap.new (ranges.fold (fun acc i (first, last) => acc.push (i, first, last)) #[])
  return { f with cache := { f.cache with lineStarts := some xm.toCache } }

/-- The `number lines` pass (no configuration dependence; `debug`/`stats` output only). -/
def numberLinesPass : Pass := Pass.ofFunc fun _ f => pure (numberLines f)

end GoFV.Opt
