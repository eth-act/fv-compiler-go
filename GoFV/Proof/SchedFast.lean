import GoFV.Opt.SchedFast
import GoFV.Proof.Sched

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedFast` satisfies `schedule`'s specification

`schedFast` (GoFV/Opt/SchedFast.lean) schedules the block's nodes renamed by `ρ := rename ids`
(the index in the sorted node IDs `ids`) and maps the result back through `σ := ids.getD · 0`.
`rename_hit`: a renamed ID inside `ids` is found there, so `σ (ρ a) = a`; the run-time checks
(`ids` strictly increasing, every node found) make `ρ` injective against the nodes and monotone
on them. `spec_transport` carries `SchedSpec` of the renamed block back to the block
(`nodeOf_rename`: the renamed block's node `ρ a` is node `a` renamed). Hence `schedFast_spec`,
and with `schedule_some`/`sched_np_eq`, `schedFast_filter`: `schedule` is defined and lists the
non-pure nodes in the same sequence.
-/

namespace GoFV.Proof.SchedFast

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.SchedFast GoFV.Proof Order

/-! ## The renaming -/

private theorem bsearch_spec (ids : Array ID) (a : ID) : ∀ fuel lo hi,
    bsearch ids a fuel lo hi = ids.size ∨ ids[bsearch ids a fuel lo hi]? = some a
  | 0, _, _ => .inl rfl
  | fuel + 1, lo, hi => by
    simp only [bsearch]
    split
    · split
      · next hm =>
        split
        · next he => exact .inr (by rw [Array.getElem?_eq_getElem hm, beq_iff_eq.1 he])
        · split
          · exact bsearch_spec ids a fuel _ _
          · exact bsearch_spec ids a fuel _ _
      · exact .inl rfl
    · exact .inl rfl

/-- A renamed ID inside `ids` is found there. -/
theorem rename_hit {ids : Array ID} {a : ID} (h : rename ids a < ids.size) :
    ids[rename ids a]? = some a := by
  unfold rename at h ⊢
  rcases bsearch_spec ids a ids.size 0 ids.size with e | e
  · rw [e] at h; exact absurd h (Nat.lt_irrefl _)
  · exact e

private theorem getD_of_getElem? {ids : Array ID} {i a : Nat} (h : ids[i]? = some a) :
    ids.getD i 0 = a := by
  simp [Array.getD_eq_getD_getElem?, h]

private theorem sortedLt_lt {ids : Array ID} (h : sortedLt ids = true) :
    ∀ i j, i < j → j < ids.size → ids.getD i 0 < ids.getD j 0 := by
  unfold sortedLt at h
  rw [nat_all_iff] at h
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    have hs := h j (by omega)
    simp only [decide_eq_true_eq] at hs
    rcases Nat.lt_or_ge i j with hl | hl
    · exact Nat.lt_trans (ih hl (by omega)) hs
    · obtain rfl : i = j := by omega
      exact hs

/-! ## Transport through a renaming -/

section transport

variable {vs : List SNode} {ρ : ID → ID}

private theorem nodup_of_map {l : List ID} (f : ID → ID) (h : (l.map f).Nodup) : l.Nodup :=
  List.Pairwise.of_map f (fun _ _ h e => h (congrArg f e)) h

private theorem find?_congr_mem {p q : SNode → Bool} :
    ∀ {l : List SNode}, (∀ n ∈ l, p n = q n) → l.find? p = l.find? q
  | [], _ => rfl
  | n :: l, h => by
    rw [List.find?_cons, List.find?_cons, h n List.mem_cons_self,
      find?_congr_mem fun m hm => h m (List.mem_cons_of_mem _ hm)]

/-- The renamed block's node `ρ a` is node `a` renamed. -/
theorem nodeOf_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    nodeOf (vs.map (renameNode ρ)) (ρ a) = (nodeOf vs a).map (renameNode ρ) := by
  unfold nodeOf
  rw [List.find?_map]
  have hc : vs.find? ((fun m => m.id == ρ a) ∘ renameNode ρ) = vs.find? (fun m => m.id == a) :=
    find?_congr_mem fun n hn => by
      show (ρ n.id == ρ a) = (n.id == a)
      by_cases e : n.id = a
      · rw [e]; simp
      · have : ρ n.id ≠ ρ a := fun h => e (hρ n hn a h.symm).symm
        rw [beq_false_of_ne this, beq_false_of_ne e]
  rw [hc]

private theorem nodeIn_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    NodeIn (vs.map (renameNode ρ)) (ρ a) ↔ NodeIn vs a := by
  rw [nodeIn_iff, nodeIn_iff, nodeOf_rename hρ]
  cases nodeOf vs a <;> simp

private theorem argsOf_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    argsOf (vs.map (renameNode ρ)) (ρ a) = (argsOf vs a).map ρ := by
  unfold argsOf
  rw [nodeOf_rename hρ]
  cases nodeOf vs a <;> simp [renameNode]

private theorem pureIn_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    PureIn (vs.map (renameNode ρ)) (ρ a) ↔ PureIn vs a := by
  unfold PureIn
  rw [nodeOf_rename hρ]
  cases nodeOf vs a <;> simp [renameNode]

private theorem nilIn_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    NilIn (vs.map (renameNode ρ)) (ρ a) ↔ NilIn vs a := by
  unfold NilIn
  rw [nodeOf_rename hρ]
  cases nodeOf vs a <;> simp [renameNode]

private theorem npIn_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id) (a : ID) :
    npIn (vs.map (renameNode ρ)) (ρ a) = npIn vs a := by
  unfold npIn
  rw [nodeOf_rename hρ]
  cases nodeOf vs a <;> simp [renameNode]

private theorem rankIn_rename (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id)
    (hmono : ∀ n ∈ vs, ∀ m ∈ vs, n.id < m.id → ρ n.id < ρ m.id) {x y : ID}
    (h : rankIn vs x y) : rankIn (vs.map (renameNode ρ)) (ρ x) (ρ y) := by
  obtain ⟨m, n, hm, hn, hlt⟩ := h
  refine ⟨renameNode ρ m, renameNode ρ n, by rw [nodeOf_rename hρ, hm]; rfl,
    by rw [nodeOf_rename hρ, hn]; rfl, ?_⟩
  rw [rankLt_iff] at hlt ⊢
  simp only [renameNode]
  rcases hlt with hlt | ⟨hp, hi⟩
  · exact .inl hlt
  · exact .inr ⟨hp, hmono m (nodeOf_mem hm).1 n (nodeOf_mem hn).1 hi⟩

/-- **`SchedSpec` through a renaming** injective against the nodes and monotone on them. -/
theorem spec_transport (hρ : ∀ n ∈ vs, ∀ a, ρ a = ρ n.id → a = n.id)
    (hmono : ∀ n ∈ vs, ∀ m ∈ vs, n.id < m.id → ρ n.id < ρ m.id) {o : List ID}
    (hS : SchedSpec (vs.map (renameNode ρ)) (o.map ρ)) : SchedSpec vs o := by
  have fwd : ∀ {j : Nat} {x : ID}, o[j]? = some x → (o.map ρ)[j]? = some (ρ x) :=
    fun {j x} h => by rw [List.getElem?_map, h]; rfl
  have back : ∀ (i : Nat) (a : ID), NodeIn vs a → (o.map ρ)[i]? = some (ρ a) → o[i]? = some a := by
    rintro i a ⟨n, hn, rfl⟩ h
    rw [List.getElem?_map] at h
    obtain ⟨b, hb, hbe⟩ := Option.map_eq_some_iff.1 h
    rw [hb, hρ n hn b hbe]
  have hmem : ∀ x, x ∈ o ↔ NodeIn vs x := by
    intro x
    constructor
    · intro hx
      exact (nodeIn_rename hρ x).1 ((hS.topo.mem (ρ x)).1 (List.mem_map_of_mem hx))
    · intro hx
      obtain ⟨y, hy, hye⟩ := List.mem_map.1 ((hS.topo.mem (ρ x)).2 ((nodeIn_rename hρ x).2 hx))
      obtain ⟨n, hn, rfl⟩ := hx
      rwa [← hρ n hn y hye]
  have hargs : ∀ x a', a' ∈ argsOf (vs.map (renameNode ρ)) (ρ x) →
      ∃ a ∈ argsOf vs x, ρ a = a' := fun x a' h => by
    rw [argsOf_rename hρ] at h
    exact List.mem_map.1 h
  refine ⟨?_, ⟨?_, hmem, ?_⟩, ?_, ?_, ?_⟩
  · have := hS.distinct
    rw [List.map_map] at this
    exact nodup_of_map ρ (by simpa [Function.comp_def, renameNode] using this)
  · exact nodup_of_map ρ hS.topo.nodup
  · intro j x hx a ha hNa
    obtain ⟨i, hi, hia⟩ := hS.topo.before j (ρ x) (fwd hx) (ρ a)
      (by rw [argsOf_rename hρ]; exact List.mem_map_of_mem ha) ((nodeIn_rename hρ a).2 hNa)
    exact ⟨i, hi, back i a hNa hia⟩
  · intro k j y x hkj hy hx hpy hpx
    obtain ⟨a', ha', hNa', i, hki, hij, hia⟩ := hS.pureFirst k j (ρ y) (ρ x) hkj (fwd hy) (fwd hx)
      (by rwa [pureIn_rename hρ]) (by rwa [pureIn_rename hρ])
    obtain ⟨a, ha, rfl⟩ := hargs x a' ha'
    have hNa := (nodeIn_rename hρ a).1 hNa'
    exact ⟨a, ha, hNa, i, hki, hij, back i a hNa hia⟩
  · intro k j y x hkj hy hx hpy hpx
    obtain ⟨a', ha', hNa', i, hki, hij, hia⟩ := hS.nilFirst k j (ρ y) (ρ x) hkj (fwd hy) (fwd hx)
      (by rwa [nilIn_rename hρ]) (by rwa [nilIn_rename hρ])
    obtain ⟨a, ha, rfl⟩ := hargs x a' ha'
    have hNa := (nodeIn_rename hρ a).1 hNa'
    exact ⟨a, ha, hNa, i, hki, hij, back i a hNa hia⟩
  · intro k j y x hkj hy hx hpy hpx hr
    obtain ⟨a', ha', hNa', i, hki, hij, hia⟩ := hS.rankFirst k j (ρ y) (ρ x) hkj (fwd hy) (fwd hx)
      (by rwa [npIn_rename hρ]) (by rwa [npIn_rename hρ]) (rankIn_rename hρ hmono hr)
    obtain ⟨a, ha, rfl⟩ := hargs x a' ha'
    have hNa := (nodeIn_rename hρ a).1 hNa'
    exact ⟨a, ha, hNa, i, hki, hij, back i a hNa hia⟩

end transport

/-! ## `schedFast` -/

private theorem rename_inj {ids : Array ID} {a b : ID} (hb : rename ids b < ids.size)
    (he : rename ids a = rename ids b) : a = b := by
  have h1 : ids[rename ids a]? = some a := rename_hit (by rw [he]; exact hb)
  rw [he, rename_hit hb] at h1
  exact (Option.some.inj h1).symm

private theorem rename_mono {ids : Array ID} (hsort : sortedLt ids = true) {a b : ID}
    (ha : rename ids a < ids.size) (hb : rename ids b < ids.size) (hlt : a < b) :
    rename ids a < rename ids b := by
  have e1 : ids.getD (rename ids a) 0 = a := getD_of_getElem? (rename_hit ha)
  have e2 : ids.getD (rename ids b) 0 = b := getD_of_getElem? (rename_hit hb)
  rcases Nat.lt_trichotomy (rename ids a) (rename ids b) with h | h | h
  · exact h
  · exact absurd (rename_inj hb h) (Nat.ne_of_lt hlt)
  · have := sortedLt_lt hsort _ _ h ha
    rw [e1, e2] at this
    exact absurd hlt (Nat.lt_asymm this)

private theorem map_back {ids : Array ID} {ws : List SNode} {o : List ID}
    (hmem : ∀ i ∈ o, ∃ n ∈ ws, n.id = i)
    (hback : ∀ n ∈ ws, rename ids (ids.getD n.id 0) = n.id) :
    (o.map (ids.getD · 0)).map (rename ids) = o := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id o]
  refine List.map_congr_left fun i hi => ?_
  obtain ⟨n, hn, rfl⟩ := hmem i hi
  exact hback n hn

/-- `schedFast`'s result for given `ids`: `schedValid` on the renamed nodes, mapped back. -/
theorem spec_of_ids {vs : Array SNode} {ids : Array ID} (hsort : sortedLt ids = true)
    (hall : ∀ n ∈ vs.toList, rename ids n.id < ids.size) {o : Array ID}
    (hv : schedValid (vs.map (renameNode (rename ids))) o = true) :
    SchedSpec vs.toList (o.map (ids.getD · 0)).toList := by
  have hS : SchedSpec (vs.toList.map (renameNode (rename ids))) o.toList := by
    have := schedValid_spec hv
    rwa [Array.toList_map] at this
  have hback : (o.map (ids.getD · 0)).toList.map (rename ids) = o.toList := by
    rw [Array.toList_map]
    refine map_back (ws := vs.toList.map (renameNode (rename ids)))
      (fun i hi => (hS.topo.mem i).1 hi) fun n' hn' => ?_
    obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hn'
    show rename ids (ids.getD (rename ids n.id) 0) = rename ids n.id
    rw [getD_of_getElem? (rename_hit (hall n hn))]
  refine spec_transport (ρ := rename ids) (fun n hn a he => rename_inj (hall n hn) he)
    (fun n hn m hm hlt => rename_mono hsort (hall n hn) (hall m hm) hlt) ?_
  rw [hback]
  exact hS

/-- **`schedFast` satisfies `schedule`'s specification.** -/
theorem schedFast_spec {f : Func} {B : Block} {o : Array ID} (h : schedFast f B = some o) :
    SchedSpec (schedNodes f B).toList o.toList := by
  unfold schedFast at h
  simp only at h
  split at h
  · next hc =>
    rw [Bool.and_eq_true] at hc
    obtain ⟨o0, ho0, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [Option.filter_eq_some_iff] at ho0
    refine spec_of_ids hc.1 (fun n hn => ?_) ho0.2
    have := Array.all_eq_true_iff_forall_mem.1 hc.2 _
      (Array.mem_map.2 ⟨n, Array.mem_toList_iff.1 hn, rfl⟩)
    exact of_decide_eq_true this
  · cases h

/-- **`schedule` agrees with `schedFast` on the non-pure nodes**: it is defined, and lists the
non-pure nodes (and so every predicate `p` that holds only on non-pure nodes among the block's
nodes) in the same sequence. -/
theorem schedFast_filter {f : Func} {B : Block} {o : Array ID} {p : ID → Bool}
    (hp : ∀ y, p y = true → NodeIn (schedNodes f B).toList y →
      npIn (schedNodes f B).toList y = true)
    (h : schedFast f B = some o) :
    ∃ o', Sem.schedule f B = some o' ∧ o'.toList.filter p = o.toList.filter p := by
  have hS := schedFast_spec h
  obtain ⟨o', ho'⟩ := schedule_some hS.distinct hS.topo
  have hT := schedule_spec ho'
  have hsame : SameNP (schedNodes f B).toList (schedNodes f B).toList := by
    intro x
    refine ⟨rfl, fun hx => ?_⟩
    unfold npIn at hx
    cases hn : nodeOf (schedNodes f B).toList x with
    | none => rw [hn] at hx; cases hx
    | some n => exact ⟨n, n, rfl, rfl, rfl⟩
  have heq := sched_np_eq hS hT hsame fun _ _ _ _ => Iff.rfl
  have key : ∀ l : List ID, (∀ y ∈ l, NodeIn (schedNodes f B).toList y) →
      l.filter p = (l.filter (npIn (schedNodes f B).toList)).filter p := by
    intro l hl
    rw [List.filter_filter]
    refine List.filter_congr fun y hy => ?_
    cases hpy : p y
    · rfl
    · simp [hp y hpy (hl y hy)]
  refine ⟨o', ho', ?_⟩
  rw [key _ fun y hy => (hT.topo.mem y).1 hy, key _ fun y hy => (hS.topo.mem y).1 hy, heq]

end GoFV.Proof.SchedFast
