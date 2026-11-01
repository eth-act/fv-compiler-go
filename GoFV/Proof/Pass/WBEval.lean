import GoFV.Proof.Mixed
import GoFV.Proof.Order

/-!
# Generic evaluation lemmas for the writebarrier proof

`evalAll_Q`: a schedule whose values each evaluate to a value satisfying a register property `Q`
whenever their arguments hold values satisfying `Q` (`LocalQ`) evaluates, and every listed value
(and every value of the accumulator `S`) then holds a value satisfying `Q`. `evalAll_Q_panic`:
a value that panics on every such frame makes the schedule panic after its evaluated prefix.
`transfer_pure`: in a dependency order with pure nodes as early as possible, a set closed under
the arguments of its pure members whose non-pure members precede a root `r` lies before `r`.

Related existing lemmas: `Dead.refOK_of_topo` (a `TopoRem` list is `RefOK` for the arguments
outside it), `stepTerm_same` (terminators of blocks with the same kind, controls and successors
on frames agreeing on the controls), `CopyElim.stepTerm_not_panic`.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem

/-- `x` evaluates, in every frame with the fields of `fr0` whose argument registers satisfy `Q`,
to a value satisfying `Q`. -/
def LocalQ (env : Env) (ctx : Ctx) (fr0 : Frame) (Q : ID → Val → Prop) (x : ID) : Prop :=
  ∀ g : Frame, g = { fr0 with regs := g.regs } →
    (∀ a ∈ argsF ctx.f x, ∃ z, g.regs[a]? = some (some z) ∧ Q a z) →
    ∃ y, stepV env ctx g x = .ok y ∧ Q x y

theorem evalAll_Q {env : Env} {ctx : Ctx} {fr0 : Frame} {Q : ID → Val → Prop} :
    ∀ {o : List ID} {S : ID → Prop} {g : Frame},
      (∀ x ∈ o, LocalQ env ctx fr0 Q x) → RefOK (argsF ctx.f) S o →
      (∀ a, S a → ∃ z, g.regs[a]? = some (some z) ∧ Q a z) →
      g = { fr0 with regs := g.regs } → g.regs.size = ctx.f.valueTab.size →
      ∃ g', evalAll env ctx g o = .ok g' ∧ g' = { fr0 with regs := g'.regs } ∧
        g'.regs.size = g.regs.size ∧
        (∀ a, (S a ∨ a ∈ o) → ∃ z, g'.regs[a]? = some (some z) ∧ Q a z) ∧
        (∀ a, a ∉ o → g'.regs[a]? = g.regs[a]?)
  | [], _, g, _, _, hS, hg, _ =>
    ⟨g, rfl, hg, rfl, fun a ha => ha.elim (hS a) (fun h => absurd h List.not_mem_nil),
      fun _ _ => rfl⟩
  | x :: s, S, g, hl, ⟨hx, hr⟩, hS, hg, hs => by
    obtain ⟨y, hxs, hQy⟩ := hl x List.mem_cons_self g hg fun a ha => hS a (hx a ha)
    have hxlt : x < g.regs.size := by rw [hs]; exact stepV_lt hxs
    rw [evalAll_cons, hxs]
    obtain ⟨g', h1, h2, h3, h4, h5⟩ := evalAll_Q (S := fun a => S a ∨ a = x)
      (g := g.set x y) (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hr
      (fun a ha => by
        by_cases hax : x = a
        · subst hax; exact ⟨y, Frame.set_regs_self hxlt, hQy⟩
        · rw [Frame.set_regs_ne hax]
          exact hS a (ha.resolve_right fun h => hax h.symm))
      (by rw [hg]; rfl) (by simp [Frame.set, hs])
    have hlift : ∀ a, (S a ∨ a ∈ x :: s) → ((S a ∨ a = x) ∨ a ∈ s) := fun a ha => by
      rcases ha with ha | ha
      · exact .inl (.inl ha)
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact .inl (.inr rfl)
        · exact .inr ha
    refine ⟨g', h1, h2, by rw [h3]; simp [Frame.set], fun a ha => h4 a (hlift a ha),
      fun a ha => ?_⟩
    have has : a ∉ s := fun h => ha (List.mem_cons_of_mem _ h)
    have hxa : x ≠ a := fun h => ha (h ▸ List.mem_cons_self)
    rw [h5 a has, Frame.set_regs_ne hxa]

theorem evalAll_Q_panic {env : Env} {ctx : Ctx} {fr0 : Frame} {Q : ID → Val → Prop}
    {pre post : List ID} {r : ID} {S : ID → Prop} {g : Frame} {e : Panic} {m : Mem}
    (hl : ∀ x ∈ pre, LocalQ env ctx fr0 Q x) (href : RefOK (argsF ctx.f) S pre)
    (hS : ∀ a, S a → ∃ z, g.regs[a]? = some (some z) ∧ Q a z)
    (hg : g = { fr0 with regs := g.regs }) (hs : g.regs.size = ctx.f.valueTab.size)
    (hrargs : ∀ a ∈ argsF ctx.f r, S a ∨ a ∈ pre)
    (hr : ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF ctx.f r, ∃ z, g'.regs[a]? = some (some z) ∧ Q a z) →
      stepV env ctx g' r = .panic e m) :
    evalAll env ctx g (pre ++ r :: post) = .panic e m := by
  obtain ⟨g', h1, h2, -, h4, -⟩ := evalAll_Q hl href hS hg hs
  rw [evalAll_append, h1]
  show evalAll env ctx g' (r :: post) = _
  rw [evalAll_cons, hr g' h2 fun a ha => h4 a (hrargs a ha)]

/-- **Transfer of the evaluated prefix** (pure nodes): if `o` is a dependency order with pure
nodes as early as possible, `r = o[k]` is not pure, and `A` is a set of nodes whose non-pure
members are before `r` and whose pure members have all their node arguments in `A`, then all
of `A` is before `r`. -/
theorem transfer_pure {α : Type} {N : α → Prop} {D : α → List α} {pure : α → Prop} {o : List α}
    (ht : Order.Topo N D o) (hp : Order.PureFirst N D pure o) {k : Nat} {r : α}
    (hr : o[k]? = some r) (hrp : ¬ pure r) (A : α → Prop) (hAN : ∀ x, A x → N x)
    (hnp : ∀ x, A x → ¬ pure x → x ∈ o.take k)
    (hcl : ∀ x, A x → pure x → ∀ a ∈ D x, N a → A a) :
    ∀ x, A x → x ∈ o.take k := by
  have key : ∀ i x, o[i]? = some x → A x → i < k := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro x hi hA
      by_cases hpx : pure x
      · refine Nat.lt_of_not_le fun hki => ?_
        have hki' : k < i := by
          rcases Nat.lt_or_eq_of_le hki with h | h
          · exact h
          · subst h; rw [hr] at hi; cases hi; exact absurd hpx hrp
        obtain ⟨a, haD, hNa, i2, hk2, hi2, ha⟩ := hp k i r x hki' hr hi hrp hpx
        exact absurd (ih i2 hi2 a ha (hcl x hA hpx a haD hNa)) (Nat.not_lt.2 hk2)
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hnp x hA hpx)
        rw [List.getElem?_take] at hj
        split at hj
        · rw [Order.idx_unique ht.nodup hi hj]; assumption
        · cases hj
  intro x hA
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ((ht.mem x).2 (hAN x hA))
  exact List.mem_iff_getElem?.2 ⟨i, by rw [List.getElem?_take_of_lt (key i x hi hA)]; exact hi⟩

end GoFV.Proof.WB
