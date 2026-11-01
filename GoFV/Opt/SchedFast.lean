import GoFV.SSA.Sem.Run
import GoFV.Util.PdqSort

/-!
# A checker-only block scheduler over compressed IDs (#147)

`Sem.schedule f b` indexes its tables by value ID, so each call allocates several arrays of
size `maxNodeId`: on big functions this dominates the checked CFG passes, which reschedule a
block per rewrite. `schedFast` renames the block's nodes to their ranks among the node IDs
(`ids`, sorted; binary search), runs `Sem.kahn` and validates its output with `Sem.schedValid`
on the renamed nodes (tables of the block's size), and maps the result back through `ids`.
Arguments that are not nodes map to the sentinel `ids.size`. The renaming is monotone and
injective on the nodes, so the result satisfies `schedule`'s specification
(`GoFV.Proof.SchedFast.schedFast_spec`) and lists the non-pure nodes as `schedule` does
(`schedFast_filter`). `none` when `kahn`'s output fails validation (never on the corpus): no
fallback scheduler, the checker then rejects.
-/

namespace GoFV.Opt.SchedFast

open GoFV.SSA GoFV.SSA.Sem

/-- The index of `a` in the sorted array `ids` (binary search over `[lo, hi)`, `fuel` steps),
else `ids.size`. -/
def bsearch (ids : Array ID) (a : ID) : (fuel lo hi : Nat) → Nat
  | 0, _, _ => ids.size
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if h : mid < ids.size then
        let m := ids[mid]
        if m == a then mid
        else if m < a then bsearch ids a fuel (mid + 1) hi
        else bsearch ids a fuel lo mid
      else ids.size
    else ids.size

/-- `ids` is strictly increasing. -/
def sortedLt (ids : Array ID) : Bool :=
  Nat.all (ids.size - 1) fun i _ => ids.getD i 0 < ids.getD (i + 1) 0

/-- The renaming of `schedFast`: the index in `ids`, `ids.size` if absent. The fuel `ids.size`
suffices (binary search needs `log₂ ids.size + 1` steps) and keeps the kernel from unfolding the
search on symbolic arrays (with a literal fuel, a defeq check of two `rename` terms unfolds an
exponential tree of branches: `(kernel) deterministic timeout`). -/
@[inline] def rename (ids : Array ID) (a : ID) : ID := bsearch ids a ids.size 0 ids.size

/-- A node with its ID and arguments renamed. -/
@[inline] def renameNode (ρ : ID → ID) (n : SNode) : SNode :=
  { n with id := ρ n.id, args := n.args.map ρ }

/-- `schedule`'s evaluation order of the non-`Phi` values of `b` (`kahn`, validated by
`schedValid`), computed over the block's node IDs renamed to `0, …, n - 1`. -/
def schedFast (f : Func) (b : Block) : Option (Array ID) :=
  let vs := schedNodes f b
  let ids := GoFV.Util.PdqSort.sortBy (· < ·) (vs.map (·.id))
  let ws := vs.map (renameNode (rename ids))
  if sortedLt ids && ws.all (·.id < ids.size) then
    ((kahn ws).filter (schedValid ws)).map (·.map (ids.getD · 0))
  else none

end GoFV.Opt.SchedFast
