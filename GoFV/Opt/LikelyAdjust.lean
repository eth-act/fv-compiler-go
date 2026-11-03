import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache

/-!
# likelyadjust (`likelyadjust.go:83-209`)

`likelyadjust` (docs/PASSES2.md, likelyadjust, issue #405): one walk of the cached (possibly
stale) postorder with the cached `f.loopnest()` (built and cached if absent). Each block gets a
`certain` and `local` unlikeliness (default 0, call 1, return 2, exit 3); a two-successor block
whose prediction is `BranchUnknown` gets one from the loop structure (stay in the loop), else
from the successors' `certain`, then `local`. A block with a `call` op gets `local = 1` and
`certain = max(1, certain[succ 0])`.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `likelyadjust(f)`. -/
def likelyadjust (f : Func) : Except String Func := do
  let nb := f.bidLast + 1
  let mut certain : Array Int := Array.replicate nb 0
  let mut loc : Array Int := Array.replicate nb 0
  let (po, f) := f.postorder
  let (nest, f) ← f.loopnest
  let mut f := f
  for b in po do
    let blk := f.getB b
    -- an `if` chain rather than a `match` on the kind: the proof splits it (`likelyadjust_eraseFL`)
    if blk.kind == .Exit then
      loc := loc.set! b 3
      certain := certain.set! b 3
    else if blk.kind == .Ret || blk.kind == .RetJmp then
      loc := loc.set! b 2
      certain := certain.set! b 2
    else if blk.kind == .Defer then
      loc := loc.set! b 1
      certain := certain.set! b (max 1 certain[blk.succs[0]!.b]!)
    else
      if blk.succs.size == 1 then
        certain := certain.set! b certain[blk.succs[0]!.b]!
      else if blk.succs.size == 2 then
        let b0 := blk.succs[0]!.b
        let b1 := blk.succs[1]!.b
        certain := certain.set! b (min certain[b0]! certain[b1]!)
        let l := nest.loopOf b
        let l0 := nest.loopOf b0
        let l1 := nest.loopOf b1
        let mut prediction := blk.likely
        if l.isSome && l0 != l1 then
          if l1.isNone then prediction := .likely
          else if l0.isNone then prediction := .unlikely
          else if l == l0 then prediction := .likely
          else if l == l1 then prediction := .unlikely
        else
          if certain[b1]! > certain[b0]! then prediction := .likely
          else if certain[b0]! > certain[b1]! then prediction := .unlikely
          else if loc[b1]! > loc[b0]! then prediction := .likely
          else if loc[b0]! > loc[b1]! then prediction := .unlikely
        if blk.likely != prediction && blk.likely == .unknown then
          f := f.modB b fun x => { x with likely := prediction }
      for v in blk.values do
        if (f.getV v).op.call then
          loc := loc.set! b 1
          certain := certain.set! b (max 1 certain[blk.succs[0]!.b]!)
          break
  return f

/-- The `likelyadjust` pass. -/
def likelyadjustPass : Pass := Pass.ofFunc fun _ f => likelyadjust f

end GoFV.Opt
