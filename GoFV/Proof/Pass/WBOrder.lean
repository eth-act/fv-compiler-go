import GoFV.Proof.Pass.WBStart
import GoFV.Proof.OrderRank
import GoFV.Proof.Merge

/-!
# writebarrier: where the source panics (issue #36)

When the source's block `b` panics at node `r` after the prefix `pre` of its schedule `o`, the
target's chain evaluates before its own panic point only values whose source counterparts are in
`pre`. `pre_of_before`: a non-pure node listed before `r` among the non-pure nodes is in `pre`;
`pre_closed`: `pre` is closed under the in-block arguments of its members; `ord_pre`: a set of
nodes whose non-pure members are in `pre` and whose pure members have their in-block arguments in
the set lies in `pre` (`transfer_pure`). `NpRank`: the order of the non-pure
nodes that `npOK` fixes — the kept ones of segment `s` (rank `2 s`), then the dropped nil check
and the stores of run `s` (rank `2 s + 1`), and within a segment the target's schedule order.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

/-- A node of `B` in a non-pure position of the chain: kept in segment `s` (rank `2 s`), or the
dropped nil check or a store of run `j` (rank `2 j + 1`). -/
def NpRank (c : WBCheck.Ctx) (b : ID) (rs : List Run) (x : ID) (q : Nat) : Prop :=
  (∃ s, q = 2 * s ∧ InSeg c b rs s x ∧ c.K.getD x false = true) ∨
  (∃ j r, q = 2 * j + 1 ∧ rs[j]? = some r ∧ (x ∈ ncsOf c r ∨ x ∈ r.src))

section
variable {f : Func} {B : Block} {o : Array ID} {pre post : List ID} {r : ID}

/-- A node listed before `r` among the non-pure nodes is in the prefix before `r`. -/
theorem pre_of_before (hown : ValuesOwn f B) (hnd : B.values.toList.Nodup)
    (ho : schedule f B = some o) (hsplit : o.toList = pre ++ r :: post) {x : ID}
    (hx : npOf f B x = true) (hr : npOf f B r = true)
    (hb : Order.Before (o.toList.filter (npOf f B)) x r) : x ∈ pre := by
  sorry

/-- The prefix before `r` is closed under in-block arguments. -/
theorem pre_closed (hown : ValuesOwn f B) (hnd : B.values.toList.Nodup)
    (ho : schedule f B = some o) (hsplit : o.toList = pre ++ r :: post) {x a : ID}
    (hx : x ∈ pre) {v : Value} (hv : f.value? x = some v) (ha : a ∈ v.args) (haB : a ∈ B.values)
    (hap : ∀ va, f.value? a = some va → va.op ≠ .Phi) : a ∈ pre := by
  sorry

/-- **The transfer to the prefix.** -/
theorem ord_pre (hown : ValuesOwn f B) (hnd : B.values.toList.Nodup)
    (ho : schedule f B = some o) (hsplit : o.toList = pre ++ r :: post)
    (hr : npOf f B r = true) (A : ID → Prop)
    (hAN : ∀ x, A x → x ∈ B.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi)
    (hnp : ∀ x, A x → npOf f B x = true → x ∈ pre)
    (hcl : ∀ x, A x → npOf f B x = false → ∀ v, f.value? x = some v → ∀ a ∈ v.args,
      a ∈ B.values → (∀ va, f.value? a = some va → va.op ≠ .Phi) → A a) :
    ∀ x, A x → x ∈ pre := by
  sorry

end



end GoFV.Proof.WB
