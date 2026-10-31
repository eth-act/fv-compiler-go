import GoFV.SSA.Alloc

/-!
# `mergePoint` (`rewrite.go:998-1046`)

A block among the blocks of `a` that dominates `b` and is dominated by all of them, found by
walking single-predecessor chains backwards from `b` (at most 100 steps in total); `none` when
the walk meets a block with several predecessors or runs out of steps. Like Go (`b.Preds[0]`
of a block without predecessors), walking past the entry block is an error.
-/

namespace GoFV.Rules

open GoFV.SSA

namespace MergePoint

/-- `b.Preds[0].b`, when `b` has at most one predecessor. -/
def step (f : Func) (b : ID) : Except String (Option ID) :=
  let ps := (f.getB b).preds
  if ps.size > 1 then pure none
  else match ps[0]? with
    | some e => pure (some e.b)
    | none => throw s!"mergePoint: b{b} has no predecessors"

/-- Second walk: count the blocks of `a` met (with multiplicity) until all are found. -/
def collect (f : Func) (blocks : Array ID) (r : ID) : Nat → ID → Nat → Except String (Option ID)
  | 0, _, _ => pure none
  | d + 1, b, na => do
    let na := na + blocks.count b
    if na == blocks.size then return some r
    match ← step f b with
    | none => return none
    | some p => collect f blocks r d p na

/-- First walk: find the first block of `a`. -/
def find (f : Func) (blocks : Array ID) : Nat → ID → Except String (Option ID)
  | 0, _ => pure none
  | d + 1, b => do
    if blocks.contains b then return ← collect f blocks b (d + 1) b 0
    match ← step f b with
    | none => return none
    | some p => find f blocks d p

end MergePoint

/-- `mergePoint(b, a...)`. -/
def mergePoint (f : Func) (b : ID) (a : Array ID) : Except String (Option ID) :=
  MergePoint.find f (a.map fun v => (f.getV v).block) 100 b

end GoFV.Rules
