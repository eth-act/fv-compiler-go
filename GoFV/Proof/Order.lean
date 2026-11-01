/-!
# Dependency orders of a block's values

Abstract facts about evaluation orders, independent of the SSA: `Topo N D o` says that the list
`o` contains every node (`N`) exactly once, each after its arguments (`D`) that are nodes;
`PureFirst` is the extra property of the semantics' scheduler that a pure node comes as early
as its arguments allow relative to the non-pure nodes (roots). `transfer` is the key lemma for
passes that change a block's dependencies: if the source order panics at root `r`, every node
the target evaluates before `r` was evaluated by the source before `r` (or is not a source
node), provided the roots are totally ordered by dependency (`chain`) and the target keeps
every dependency of a node on a root (`pres`).
-/

namespace GoFV.Proof.Order

variable {α : Type}

/-- `Dep N D x y`: `y` depends on `x` through arguments that are nodes. -/
inductive Dep (N : α → Prop) (D : α → List α) : α → α → Prop where
  | arg {x y : α} : N x → N y → x ∈ D y → Dep N D x y
  | trans {x y z : α} : Dep N D x y → Dep N D y z → Dep N D x z

/-- `o` is a dependency order of the nodes `N` with arguments `D`. -/
structure Topo (N : α → Prop) (D : α → List α) (o : List α) : Prop where
  nodup : o.Nodup
  mem : ∀ x, x ∈ o ↔ N x
  before : ∀ (j : Nat) x, o[j]? = some x → ∀ a ∈ D x, N a → ∃ i < j, o[i]? = some a

/-- A pure node listed after a non-pure node `y` has an argument (a node) listed at or after
`y`. -/
abbrev PureFirst (N : α → Prop) (D : α → List α) (pure : α → Prop) (o : List α) : Prop :=
  ∀ (k j : Nat) y x, k < j → o[k]? = some y → o[j]? = some x → ¬ pure y → pure x →
    ∃ a ∈ D x, N a ∧ ∃ i : Nat, k ≤ i ∧ i < j ∧ o[i]? = some a

theorem idx_unique {o : List α} (hn : o.Nodup) {i j : Nat} {x : α} (hi : o[i]? = some x)
    (hj : o[j]? = some x) : i = j := by
  have hlt : i < o.length := by
    rcases Nat.lt_or_ge i o.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  exact (hn.getElem?_inj hlt).1 (hi.trans hj.symm)

theorem Dep.right {N : α → Prop} {D : α → List α} {x y : α} : Dep N D x y → N y
  | .arg _ hy _ => hy
  | .trans _ h => Dep.right h

/-- Dependencies go forward in a dependency order. -/
theorem Topo.dep_lt {N : α → Prop} {D : α → List α} {o : List α} (ht : Topo N D o) {x y : α}
    (h : Dep N D x y) : ∀ {i j : Nat}, o[i]? = some x → o[j]? = some y → i < j := by
  induction h with
  | arg hx hy hxy =>
    intro i j hi hj
    obtain ⟨i', hlt, hi'⟩ := ht.before _ _ hj _ hxy hx
    rw [idx_unique ht.nodup hi hi']; exact hlt
  | @trans x y z h1 _ ih1 ih2 =>
    intro i j hi hj
    obtain ⟨m, hm⟩ := List.getElem?_of_mem ((ht.mem y).2 h1.right)
    exact Nat.lt_trans (ih1 hi hm) (ih2 hm hj)

/-- In the source order, a node listed at or after root `r` (other than `r`) depends on `r`:
pure nodes by `PureFirst` (by induction on the distance to `r`), roots by `chain`. -/
theorem dep_of_after {N : α → Prop} {D : α → List α} {pure : α → Prop} {o : List α}
    (hs : Topo N D o) (hk : PureFirst N D pure o) {r : α} {k : Nat} (hr : o[k]? = some r)
    (hrp : ¬ pure r) (chain : ∀ y, N y → ¬ pure y → y ≠ r → Dep N D y r ∨ Dep N D r y) :
    ∀ n i y, i - k = n → k ≤ i → o[i]? = some y → y ≠ r → Dep N D r y := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i y hn hki hiy hyr
    have hNy : N y := (hs.mem y).1 (List.mem_of_getElem? hiy)
    have hki' : k < i := by
      rcases Nat.lt_or_ge k i with h | h
      · exact h
      · have : i = k := Nat.le_antisymm h hki
        subst this; rw [hr] at hiy; cases hiy; exact absurd rfl hyr
    by_cases hpy : pure y
    · obtain ⟨a, haD, hNa, i2, hk2, hi2, ha⟩ := hk k i r y hki' hr hiy hrp hpy
      by_cases har : a = r
      · subst har; exact .arg hNa hNy haD
      · exact .trans (ih (i2 - k) (by omega) i2 a rfl hk2 ha har) (.arg hNa hNy haD)
    · rcases chain y hNy hpy hyr with hd | hd
      · exact absurd (hs.dep_lt hd hiy hr) (by omega)
      · exact hd

/-- The panic transfer: if the source order `o` reaches root `r` at position `k`, every source
node the target order `o'` lists before `r` is listed before `r` by `o`. -/
theorem transfer {N N' : α → Prop} {D D' : α → List α} {pure : α → Prop} {o o' : List α}
    (hs : Topo N D o) (hk : PureFirst N D pure o) (ht : Topo N' D' o')
    {r : α} {k k' : Nat} (hr : o[k]? = some r) (hr' : o'[k']? = some r) (hrp : ¬ pure r)
    (chain : ∀ y, N y → ¬ pure y → y ≠ r → Dep N D y r ∨ Dep N D r y)
    (pres : ∀ y, N y → N' y → Dep N D r y → Dep N' D' r y) :
    ∀ j y, j < k' → o'[j]? = some y → N y → ∃ i < k, o[i]? = some y := by
  intro j y hj hy hNy
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hs.mem y).2 hNy)
  refine ⟨i, ?_, hi⟩
  rcases Nat.lt_or_ge i k with h | h
  · exact h
  · exfalso
    have hyr : y ≠ r := by
      rintro rfl; exact absurd (idx_unique ht.nodup hy hr') (by omega)
    have hd := dep_of_after hs hk hr hrp chain (i - k) i y rfl h hi hyr
    have hN'y : N' y := (ht.mem y).1 (List.mem_of_getElem? hy)
    exact absurd (ht.dep_lt (pres y hNy hN'y hd) hr' hy) (by omega)

end GoFV.Proof.Order
