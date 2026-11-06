import GoFV.Opt.LowerCheck
import GoFV.Proof.Pass.MoveLCheck

/-!
# The `pair` validator (`pairB`, issue #385)

`pair` (`GoFV.Opt.pair`) keeps the CFG and turns two loads of adjacent elements into the
selectors of a pair load (in a block, or the second load in a single-predecessor successor as a
`Copy` of a selector), and two adjacent stores into a pair store and a memory `Copy`.
`pairB tabs tabs' f g` accepts `g` (with `pair`'s tables `tabs'`, which add the pair loads'
tuple types) for `f` (with tables `tabs`) when the tables agree for `f` (`tabsAgreeL`) and the
value-motion validator with `pair`'s cases accepts the pair in `tabs'` (`MoveL.pairMoveB`): each
selector stands for the load of its element, a pair store for the second of its two stores
(`MoveL.relB` with `pr`). Then `g` refines `f` under `runL`
(`GoFV.Proof.MoveL.pair_refinesL`).
-/

namespace GoFV.Opt.PairCheck

open GoFV.SSA

/-- **The `pair` validator** (module doc). -/
def pairB (tabs tabs' : Tables) (f g : Func) : Bool :=
  LowerCheck.tabsAgreeL tabs tabs' f && GoFV.Proof.MoveL.pairMoveB tabs' f g

end GoFV.Opt.PairCheck
