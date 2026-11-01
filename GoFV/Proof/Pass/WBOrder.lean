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
  have ht := (schedule_spec ho).topo
  have hk : o.toList[pre.length]? = some r := by rw [hsplit]; simp
  obtain ⟨i, j, hij, hi, hj⟩ := (Order.before_filter (npOf f B) hx hr o.toList).1 hb
  rw [Order.idx_unique ht.nodup hj hk] at hij
  rw [hsplit, List.getElem?_append_left hij] at hi
  exact List.mem_of_getElem? hi

/-- The prefix before `r` is closed under in-block arguments. -/
theorem pre_closed (hown : ValuesOwn f B) (hnd : B.values.toList.Nodup)
    (ho : schedule f B = some o) (hsplit : o.toList = pre ++ r :: post) {x a : ID}
    (hx : x ∈ pre) {v : Value} (hv : f.value? x = some v) (ha : a ∈ v.args) (haB : a ∈ B.values)
    (hap : ∀ va, f.value? a = some va → va.op ≠ .Phi) : a ∈ pre := by
  have ht := (schedule_spec ho).topo
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  have hil : i < pre.length := (List.getElem?_eq_some_iff.1 hi).1
  have hio : o.toList[i]? = some x := by rw [hsplit, List.getElem?_append_left hil]; exact hi
  have hxN := (ht.mem x).1 (List.mem_of_getElem? hio)
  obtain ⟨hxB, v', hv', hxp⟩ := (nodeIn_schedNodes hown).1 hxN
  rw [hv] at hv'; cases hv'
  obtain ⟨va, hva, -⟩ := hown a haB
  have haN : NodeIn (schedNodes f B).toList a := (nodeIn_schedNodes hown).2 ⟨haB, va, hva, hap va hva⟩
  obtain ⟨i', hi', hai⟩ := ht.before i x hio a
    (by rw [argsOf_schedNodes hown hnd hxB hv hxp]; exact Array.mem_toList_iff.2 ha) haN
  rw [hsplit, List.getElem?_append_left (Nat.lt_trans hi' hil)] at hai
  exact List.mem_of_getElem? hai

/-- **The transfer to the prefix.** -/
theorem ord_pre (hown : ValuesOwn f B) (hnd : B.values.toList.Nodup)
    (ho : schedule f B = some o) (hsplit : o.toList = pre ++ r :: post)
    (hr : npOf f B r = true) (A : ID → Prop)
    (hAN : ∀ x, A x → x ∈ B.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi)
    (hnp : ∀ x, A x → npOf f B x = true → x ∈ pre)
    (hcl : ∀ x, A x → npOf f B x = false → ∀ v, f.value? x = some v → ∀ a ∈ v.args,
      a ∈ B.values → (∀ va, f.value? a = some va → va.op ≠ .Phi) → A a) :
    ∀ x, A x → x ∈ pre := by
  have hspec := schedule_spec ho
  have hk : o.toList[pre.length]? = some r := by rw [hsplit]; simp
  have htake : o.toList.take pre.length = pre := by rw [hsplit]; simp
  have hnpI := npIn_schedNodes hown hnd
  have hrp : ¬ PureIn (schedNodes f B).toList r := by
    rw [← hnpI] at hr; exact (npIn_iff.1 hr).2
  have key := transfer_pure hspec.topo hspec.pureFirst hk hrp A
    (fun x hx => (nodeIn_schedNodes hown).2 (hAN x hx))
    (fun x hx hpx => by
      rw [htake]
      refine hnp x hx ?_
      rw [← hnpI]
      exact npIn_iff.2 ⟨(nodeIn_schedNodes hown).2 (hAN x hx), hpx⟩)
    (fun x hx hpx a ha haN => by
      obtain ⟨hxB, v, hv, hxp⟩ := hAN x hx
      obtain ⟨haB, va, hva, hap⟩ := (nodeIn_schedNodes hown).1 haN
      have hfalse : npOf f B x = false := by
        rw [← hnpI]
        exact Bool.eq_false_iff.2 fun h => (npIn_iff.1 h).2 hpx
      rw [argsOf_schedNodes hown hnd hxB hv hxp] at ha
      exact hcl x hx hfalse v hv a (Array.mem_toList_iff.1 ha) haB
        fun va' hva' => by rw [hva] at hva'; cases hva'; exact hap)
  intro x hx
  have := key x hx
  rwa [htake] at this

end



end GoFV.Proof.WB
