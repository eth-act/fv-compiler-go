import GoFV.Proof.Pass.WBOrder

/-!
# writebarrier: the order of the non-pure nodes of a chain (issue #36)

`np_before`, `np_before_seg`: the order of the non-pure nodes of `B` that `npOK` fixes (ranks
`NpRank`), `held_rank`: the rank of a held non-pure node listed in a segment, `npOf_kept`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- Non-pure nodes of lower rank come first. -/
theorem np_before (S : Setup c b B rs l) {o : Array ID} (ho : schedule c.f B = some o)
    {x y : ID} {qx qy : Nat} (hx : NpRank c b rs x qx) (hy : NpRank c b rs y qy)
    (hxn : npOf c.f B x = true) (hyn : npOf c.f B y = true) (hlt : qx < qy) :
    Order.Before (o.toList.filter (npOf c.f B)) x y := by
  sorry

/-- Kept non-pure nodes of one segment come in the target's schedule order. -/
theorem np_before_seg (S : Setup c b B rs l) {o : Array ID} (ho : schedule c.f B = some o)
    {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {C : Block} (hC : c.g.block? s = some C)
    {oC : Array ID} (hoC : schedule c.g C = some oC) {x y : ID}
    (hxK : c.K.getD x false = true) (hyK : c.K.getD y false = true)
    (hxn : npOf c.f B x = true) (hyn : npOf c.f B y = true)
    (hxy : Order.Before oC.toList x y) :
    Order.Before (o.toList.filter (npOf c.f B)) x y := by
  sorry

/-- A held non-pure node listed in segment `s` has rank `2 s` (kept) or is a store of run
`s - 1` (the run's last store). -/
theorem held_rank (S : Setup c b B rs l) {s x : ID} {k : Nat} (hs : (segsOf b rs)[k]? = some s)
    (hx : x ∈ vals c.g s) (hh : c.held x = true) :
    NpRank c b rs x (2 * k) ∨ ∃ j, k = j + 1 ∧ NpRank c b rs x (2 * j + 1) := by
  sorry

/-- Kept values of `B` and run stores have the same op in `g`'s segment, so the same
non-purity. -/
theorem npOf_kept (S : Setup c b B rs l) {x : ID} (hK : c.K.getD x false = true)
    {k : Nat} {s : ID} (hs : (segsOf b rs)[k]? = some s) {C : Block} (hC : c.g.block? s = some C)
    (hx : x ∈ C.values) : npOf c.g C x = npOf c.f B x := by
  sorry

end Setup

end GoFV.Proof.WB
