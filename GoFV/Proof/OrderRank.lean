import GoFV.Proof.Order

/-!
# Canonical order of the non-pure nodes (#96)

`RankFirst`: in a schedule, a non-pure node listed after a non-pure node of greater rank has an
argument listed at or after that node (it was not ready then: the scheduler always picks the
ready non-pure node of least rank). `np_filter_eq`: two orders with `Topo`, `PureFirst` and
`RankFirst` over the same non-pure nodes, with the same dependencies between non-pure nodes
and a rank that totally orders them, list the non-pure nodes in the same sequence. `transfer_rank`: if the
source panics at the non-pure node `r`, everything the target evaluates before `r` the source
evaluated before `r` — the replacement of `Order.transfer` that needs no `chain` fragment and
also covers a panicking `NilCheck`.
-/

namespace GoFV.Proof.Order

variable {α : Type}

/-- `u` is listed before `v` in `o`. -/
def Before (o : List α) (u v : α) : Prop :=
  ∃ i j : Nat, i < j ∧ o[i]? = some u ∧ o[j]? = some v

theorem before_cons {a : α} {l : List α} {u v : α} :
    Before (a :: l) u v ↔ (a = u ∧ v ∈ l) ∨ Before l u v := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
        simp only [List.getElem?_cons_succ] at hj
        exact .inl ⟨hi, List.mem_of_getElem? hj⟩
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at hi hj
        exact .inr ⟨i, j, by omega, hi, hj⟩
  · rintro (⟨rfl, hv⟩ | ⟨i, j, hij, hi, hj⟩)
    · obtain ⟨j, hj⟩ := List.getElem?_of_mem hv
      exact ⟨0, j + 1, by omega, rfl, by simpa using hj⟩
    · exact ⟨i + 1, j + 1, by omega, by simpa using hi, by simpa using hj⟩

theorem before_filter (p : α → Bool) {u v : α} (hu : p u = true) (hv : p v = true) :
    ∀ l : List α, Before (l.filter p) u v ↔ Before l u v
  | [] => by simp [Before]
  | a :: l => by
    have ih := before_filter p hu hv l
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, before_cons, before_cons, ih]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact .inl ⟨h1, (List.mem_filter.1 h2).1⟩
        · exact .inr h
      · rintro (⟨h1, h2⟩ | h)
        · exact .inl ⟨h1, List.mem_filter.2 ⟨h2, hv⟩⟩
        · exact .inr h
    · rw [List.filter_cons_of_neg ha, ih, before_cons]
      constructor
      · exact .inr
      · rintro (⟨rfl, _⟩ | h)
        · exact absurd hu ha
        · exact h

theorem before_of_idx {o : List α} {i j : Nat} {u v : α} (hij : i < j) (hi : o[i]? = some u)
    (hj : o[j]? = some v) : Before o u v := ⟨i, j, hij, hi, hj⟩

/-- In a list without duplicates, `Before` fixes the positions' order. -/
theorem idx_lt_of_before {o : List α} (hn : o.Nodup) {u v : α} (h : Before o u v) {i j : Nat}
    (hi : o[i]? = some u) (hj : o[j]? = some v) : i < j := by
  obtain ⟨i', j', hij, hi', hj'⟩ := h
  rw [idx_unique hn hi hi', idx_unique hn hj hj']
  exact hij

/-- A non-pure node listed after a non-pure node `y` of greater rank (`lt x y`) has an argument
(a node) listed at or after `y`. -/
abbrev RankFirst (N : α → Prop) (D : α → List α) (np : α → Bool) (lt : α → α → Prop)
    (o : List α) : Prop :=
  ∀ (k j : Nat) y x, k < j → o[k]? = some y → o[j]? = some x → np y = true → np x = true →
    lt x y → ∃ a ∈ D x, N a ∧ ∃ i : Nat, k ≤ i ∧ i < j ∧ o[i]? = some a

/-- `RankFirst` transfers to another non-pure predicate and rank that agree on the non-pure
nodes. -/
theorem RankFirst.congr {N : α → Prop} {D : α → List α} {np np' : α → Bool}
    {lt lt' : α → α → Prop} {o : List α} (h : RankFirst N D np lt o)
    (hnp : ∀ x, np' x = np x) (hlt : ∀ x y, np x = true → np y = true → lt' x y → lt x y) :
    RankFirst N D np' lt' o := by
  intro k j y x hkj hy hx hny hnx hl
  rw [hnp] at hny hnx
  exact h k j y x hkj hy hx hny hnx (hlt x y hnx hny hl)

/-- `lt` is a strict total order on the non-pure nodes. -/
structure RankOrder (np : α → Bool) (lt : α → α → Prop) : Prop where
  asymm : ∀ x y, lt x y → ¬ lt y x
  total : ∀ x y, np x = true → np y = true → x ≠ y → lt x y ∨ lt y x

/-- From a node listed at or after the non-pure node at `q`, descending through pure nodes'
arguments (`PureFirst`) reaches a non-pure node listed at or after `q` that it depends on. -/
theorem descend {N : α → Prop} {D : α → List α} {pure : α → Prop} {o : List α}
    (hs : Topo N D o) (hp : PureFirst N D pure o) {q : Nat} {y : α} (hq : o[q]? = some y)
    (hy : ¬ pure y) :
    ∀ (i : Nat) (a : α), q ≤ i → o[i]? = some a →
      ∃ z i', q ≤ i' ∧ o[i']? = some z ∧ ¬ pure z ∧ (z = a ∨ Dep N D z a) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro a hqi ha
    by_cases hpa : pure a
    · have hqi' : q < i := by
        rcases Nat.lt_or_ge q i with h | h
        · exact h
        · have : i = q := Nat.le_antisymm h hqi
          subst this; rw [hq] at ha; cases ha; exact absurd hpa hy
      obtain ⟨b, hb, hNb, i2, hq2, h2i, hib⟩ := hp q i y a hqi' hq ha hy hpa
      obtain ⟨z, i', hqi', hiz, hpz, hzb⟩ := ih i2 h2i b hq2 hib
      have hNa : N a := (hs.mem a).1 (List.mem_of_getElem? ha)
      refine ⟨z, i', hqi', hiz, hpz, .inr ?_⟩
      rcases hzb with rfl | hd
      · exact .arg hNb hNa hb
      · exact .trans hd (.arg hNb hNa hb)
    · exact ⟨a, i, hqi, ha, hpa, .inl rfl⟩

section Unique

variable {N : α → Prop} {D : α → List α} {pure : α → Prop} {np : α → Bool}
  {lt : α → α → Prop} {o : List α}

/-- The `m`-th non-pure node `y` of a schedule is non-pure, its non-pure ancestors come before
it among the non-pure nodes, and every other non-pure node whose non-pure ancestors all come
before it has a greater rank. -/
theorem np_char (hs : Topo N D o) (hp : PureFirst N D pure o) (hr : RankFirst N D np lt o)
    (hnp : ∀ x, np x = true ↔ N x ∧ ¬ pure x) (hord : RankOrder np lt)
    {m : Nat} {y : α} (hy : (o.filter np)[m]? = some y) :
    np y = true ∧
      (∀ z, np z = true → Dep N D z y → z ∈ (o.filter np).take m) ∧
      ∀ x, np x = true → x ∉ (o.filter np).take m → x ≠ y →
        (∀ z, np z = true → Dep N D z x → z ∈ (o.filter np).take m) → lt y x := by
  have hL : (o.filter np).Nodup := hs.nodup.filter _
  have hyL := List.mem_of_getElem? hy
  have hnpy : np y = true := (List.mem_filter.1 hyL).2
  -- an element of the filter before position `m`
  have take_of : ∀ z i, i < m → (o.filter np)[i]? = some z → z ∈ (o.filter np).take m :=
    fun z i him hi => List.mem_of_getElem? (by rw [List.getElem?_take_of_lt him]; exact hi)
  have idx_of_take : ∀ z, z ∈ (o.filter np).take m → ∃ i < m, (o.filter np)[i]? = some z := by
    intro z hz
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hz
    have him : i < m := by
      have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
    exact ⟨i, him, by rw [List.getElem?_take_of_lt him] at hi; exact hi⟩
  -- positions in `o`
  have pos_of : ∀ z, z ∈ o.filter np → ∃ i, o[i]? = some z :=
    fun z hz => List.getElem?_of_mem (List.mem_filter.1 hz).1
  obtain ⟨q, hq⟩ := pos_of y hyL
  refine ⟨hnpy, ?_, ?_⟩
  · intro z hz hd
    have hNz : N z := ((hnp z).1 hz).1
    have hzo : z ∈ o := (hs.mem z).2 hNz
    obtain ⟨iz, hiz⟩ := List.getElem?_of_mem hzo
    have hlt := hs.dep_lt hd hiz hq
    have hb : Before (o.filter np) z y := (before_filter np hz hnpy o).2 ⟨iz, q, hlt, hiz, hq⟩
    obtain ⟨i, j, hij, hi, hj⟩ := hb
    rw [idx_unique hL hj hy] at hij
    exact take_of z i hij hi
  · intro x hx hxS hxy hanc
    have hxo : x ∈ o := (hs.mem x).2 ((hnp x).1 hx).1
    have hxL : x ∈ o.filter np := List.mem_filter.2 ⟨hxo, hx⟩
    obtain ⟨m', hm'⟩ := List.getElem?_of_mem hxL
    have hmm' : m < m' := by
      rcases Nat.lt_or_ge m' m with h | h
      · exact absurd (take_of x m' h hm') hxS
      · rcases Nat.lt_or_ge m m' with h' | h'
        · exact h'
        · have : m' = m := Nat.le_antisymm h' h
          subst this; rw [hy] at hm'; cases hm'; exact absurd rfl hxy
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hxo
    have hqj : q < j := idx_lt_of_before hs.nodup
      ((before_filter np hnpy hx o).1 ⟨m, m', hmm', hy, hm'⟩) hq hj
    rcases hord.total y x hnpy hx (Ne.symm hxy) with h | hlt
    · exact h
    · exfalso
      · obtain ⟨a, ha, hNa, i, hqi, hij, hia⟩ := hr q j y x hqj hq hj hnpy hx hlt
        have hpy : ¬ pure y := ((hnp y).1 hnpy).2
        obtain ⟨z, i', hqi', hiz, hpz, hza⟩ := descend hs hp hq hpy i a hqi hia
        have hNz : N z := (hs.mem z).1 (List.mem_of_getElem? hiz)
        have hnz : np z = true := (hnp z).2 ⟨hNz, hpz⟩
        have hNx : N x := ((hnp x).1 hx).1
        have hdzx : Dep N D z x := by
          rcases hza with rfl | hd
          · exact .arg hNa hNx ha
          · exact .trans hd (.arg hNa hNx ha)
        obtain ⟨i2, hi2m, hi2⟩ := idx_of_take z (hanc z hnz hdzx)
        have hb : Before o z y := (before_filter np hnz hnpy o).1 ⟨i2, m, hi2m, hi2, hy⟩
        have := idx_lt_of_before hs.nodup hb hiz hq
        omega

/-- **The non-pure nodes are scheduled in the same sequence** by any two orders with `Topo`,
`PureFirst` and `RankFirst` over the same non-pure nodes with the same dependencies between
them, when the rank (`lt`) totally orders the non-pure nodes. -/
theorem np_filter_eq {N' : α → Prop} {D' : α → List α} {pure' : α → Prop} {o' : List α}
    (hs : Topo N D o) (hp : PureFirst N D pure o) (hr : RankFirst N D np lt o)
    (hs' : Topo N' D' o') (hp' : PureFirst N' D' pure' o') (hr' : RankFirst N' D' np lt o')
    (hnp : ∀ x, np x = true ↔ N x ∧ ¬ pure x) (hnp' : ∀ x, np x = true ↔ N' x ∧ ¬ pure' x)
    (hord : RankOrder np lt)
    (hdep : ∀ x y, np x = true → np y = true → (Dep N D x y ↔ Dep N' D' x y)) :
    o.filter np = o'.filter np := by
  have hL := hs.nodup.filter np
  have hL' := hs'.nodup.filter np
  have hmem : ∀ x, x ∈ o.filter np ↔ x ∈ o'.filter np := by
    intro x
    rw [List.mem_filter, List.mem_filter, hs.mem, hs'.mem]
    constructor
    · rintro ⟨-, hx⟩; exact ⟨((hnp' x).1 hx).1, hx⟩
    · rintro ⟨-, hx⟩; exact ⟨((hnp x).1 hx).1, hx⟩
  have hlen : (o.filter np).length = (o'.filter np).length :=
    ((List.perm_ext_iff_of_nodup hL hL').2 hmem).length_eq
  have step : ∀ m, (o.filter np).take m = (o'.filter np).take m →
      (o.filter np).take (m + 1) = (o'.filter np).take (m + 1) := by
    intro m hS
    rcases Nat.lt_or_ge m (o.filter np).length with hm | hm
    · have hm' : m < (o'.filter np).length := hlen ▸ hm
      rw [List.take_add_one, List.take_add_one, hS]
      congr 1
      rw [List.getElem?_eq_getElem hm, List.getElem?_eq_getElem hm']
      simp only [Option.toList_some, List.cons.injEq, and_true]
      have hy : (o.filter np)[m]? = some (o.filter np)[m] := List.getElem?_eq_getElem hm
      have hy' : (o'.filter np)[m]? = some (o'.filter np)[m] := List.getElem?_eq_getElem hm'
      obtain ⟨hn1, hb1, hc1⟩ := np_char hs hp hr hnp hord hy
      obtain ⟨hn2, hb2, hc2⟩ := np_char hs' hp' hr' hnp' hord hy'
      have notin : ∀ (L : List α), L.Nodup → ∀ (hm : m < L.length), L[m] ∉ L.take m := by
        intro L hn hm hin
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hin
        have him : i < m := by have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
        rw [List.getElem?_take_of_lt him] at hi
        have := idx_unique hn hi (List.getElem?_eq_getElem hm)
        omega
      refine Classical.byContradiction fun hne => ?_
      have h1 := hc1 (o'.filter np)[m] hn2 (by rw [hS]; exact notin _ hL' hm') (Ne.symm hne)
        (fun z hz hd => by rw [hS]; exact hb2 z hz ((hdep z _ hz hn2).1 hd))
      have h2 := hc2 (o.filter np)[m] hn1 (by rw [← hS]; exact notin _ hL hm) hne
        (fun z hz hd => by rw [← hS]; exact hb1 z hz ((hdep z _ hz hn1).2 hd))
      exact hord.asymm _ _ h1 h2
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega),
        ← List.take_of_length_le (l := o.filter np) hm, ← List.take_of_length_le (l := o'.filter np)
          (by omega : (o'.filter np).length ≤ m)]
      exact hS
  have hall : ∀ m, (o.filter np).take m = (o'.filter np).take m := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => exact step m ih
  rw [← List.take_length (l := o.filter np), hall, hlen, List.take_length]

end Unique

/-- How a source argument `a` of `y` reaches `y` in the target: `a` is a target node `y`
depends on, or `a` is pure and each of its arguments that is a source node reaches `y` (a
pass that replaces a use of a copy by the copy's source keeps `Feeds` through the copy). -/
inductive Feeds (N N' : α → Prop) (D : α → List α) (D' : α → List α) (pure : α → Prop) (y : α) :
    α → Prop where
  | direct {a : α} : N' a → Dep N' D' a y → Feeds N N' D D' pure y a
  | through {a : α} : pure a → (∀ b ∈ D a, N b → Feeds N N' D D' pure y b) →
      Feeds N N' D D' pure y a

/-- **The panic transfer with the canonical rank.** If the source order `o` reaches the non-pure
node `r` at position `k`, every source node the target order `o'` lists before `r` is listed
before `r` by `o` — given that both orders list the non-pure nodes in the same sequence
(`np_filter_eq`) and every argument of a source node the target lists `Feeds` it. -/
theorem transfer_rank {N N' : α → Prop} {D D' : α → List α} {pure : α → Prop} {np : α → Bool}
    {o o' : List α} (hs : Topo N D o) (hk : PureFirst N D pure o) (ht : Topo N' D' o')
    (hnp : ∀ x, np x = true ↔ N x ∧ ¬ pure x) (hseq : o.filter np = o'.filter np)
    {r : α} {k k' : Nat} (hr : o[k]? = some r) (hr' : o'[k']? = some r) (hrp : np r = true)
    (pres : ∀ a y, N a → N y → a ∈ D y → N' y → Feeds N N' D D' pure y a) :
    ∀ j y, j < k' → o'[j]? = some y → N y → ∃ i < k, o[i]? = some y := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro y hj hy hNy
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hs.mem y).2 hNy)
    refine ⟨i, ?_, hi⟩
    rcases Nat.lt_or_ge i k with h | h
    · exact h
    · exfalso
      have hyr : y ≠ r := by
        rintro rfl; exact absurd (idx_unique ht.nodup hy hr') (by omega)
      have hki : k < i := by
        rcases Nat.lt_or_ge k i with h' | h'
        · exact h'
        · have : i = k := Nat.le_antisymm h' h
          subst this; rw [hr] at hi; cases hi; exact absurd rfl hyr
      have hpr : ¬ pure r := ((hnp r).1 hrp).2
      have hN'y : N' y := (ht.mem y).1 (List.mem_of_getElem? hy)
      -- an argument fed into `y` listed at or after `r` in the source is a contradiction
      have feeds : ∀ a, Feeds N N' D D' pure y a → N a → ∀ i2, k ≤ i2 → o[i2]? = some a → False := by
        intro a hf
        induction hf with
        | @direct a hN'a hd =>
          intro hNa i2 hk2 hia
          obtain ⟨ja, hja⟩ := List.getElem?_of_mem ((ht.mem a).2 hN'a)
          have hjaj : ja < j := ht.dep_lt hd hja hy
          obtain ⟨i3, hi3, hai3⟩ := ih ja hjaj a (by omega) hja hNa
          have := idx_unique hs.nodup hia hai3
          omega
        | @through a hpa _ ihb =>
          intro hNa i2 hk2 hia
          have hk2' : k < i2 := by
            rcases Nat.lt_or_ge k i2 with h' | h'
            · exact h'
            · have : i2 = k := Nat.le_antisymm h' hk2
              subst this; rw [hr] at hia; cases hia; exact absurd hpa hpr
          obtain ⟨b, hb, hNb, i4, hk4, _, hib⟩ := hk k i2 r a hk2' hr hia hpr hpa
          exact ihb b hb hNb hNb i4 hk4 hib
      by_cases hpy : pure y
      · obtain ⟨a, ha, hNa, i2, hk2, _, hia⟩ := hk k i r y hki hr hi hpr hpy
        exact feeds a (pres a y hNa hNy ha hN'y) hNa i2 hk2 hia
      · have hny : np y = true := (hnp y).2 ⟨hNy, hpy⟩
        have hb : Before (o'.filter np) y r := (before_filter np hny hrp o').2 ⟨j, k', hj, hy, hr'⟩
        rw [← hseq] at hb
        have := idx_lt_of_before hs.nodup ((before_filter np hny hrp o).1 hb) hi hr
        omega

end GoFV.Proof.Order
