import GoFV.SSA.Sem.Run
import GoFV.Proof.Order

/-!
# What `schedule` guarantees

`schedule f b = some o` means `o` passed `schedValid`: the IDs of the block's non-`Phi` values
(`schedNodes f b`) are distinct, `o` lists each of them exactly once after its arguments that
are nodes (`Order.Topo`), and pure nodes come as early as their arguments allow relative to
the roots (`Order.PureFirst`). `schedule_spec` states this declaratively; no proof needs Kahn's
algorithm itself.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem Order

/-- The node with ID `x`. -/
def nodeOf (vs : List SNode) (x : ID) : Option SNode := vs.find? (·.id == x)

/-- `x` is a node. -/
def NodeIn (vs : List SNode) (x : ID) : Prop := ∃ n ∈ vs, n.id = x

/-- The arguments of node `x` (none if `x` is not a node). -/
def argsOf (vs : List SNode) (x : ID) : List ID := ((nodeOf vs x).map (·.args.toList)).getD []

/-- `x` is pure (priority 0) or not a node. -/
def PureIn (vs : List SNode) (x : ID) : Prop := ∀ n, nodeOf vs x = some n → n.prio = 0

/-- What a validated schedule `o` of the nodes `vs` satisfies. -/
structure SchedSpec (vs : List SNode) (o : List ID) : Prop where
  distinct : (vs.map (·.id)).Nodup
  topo : Topo (NodeIn vs) (argsOf vs) o
  pureFirst : PureFirst (NodeIn vs) (argsOf vs) (PureIn vs) o

/-! ## The node table -/

theorem le_foldl_max (l : List SNode) (init : ID) :
    init ≤ l.foldl (fun m v => max m v.id) init := by
  induction l generalizing init with
  | nil => exact Nat.le_refl _
  | cons n l ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem id_le_foldl_max {l : List SNode} {n : SNode} (h : n ∈ l) :
    ∀ (init : ID), n.id ≤ l.foldl (fun m v => max m v.id) init := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    intro init
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max l _)
    · exact ih h _

theorem id_lt_maxNodeId {vs : Array SNode} {n : SNode} (h : n ∈ vs.toList) :
    n.id < maxNodeId vs + 1 := by
  unfold maxNodeId
  rw [← Array.foldl_toList]
  exact Nat.lt_succ_of_le (id_le_foldl_max h 0)

theorem idsDistinct_spec : ∀ (l : List SNode) (seen : Array Bool),
    (∀ n ∈ l, n.id < seen.size) → idsDistinct seen l = true →
      (l.map (·.id)).Nodup ∧ ∀ n ∈ l, seen.getD n.id false = false
  | [], _, _, _ => ⟨List.nodup_nil, fun _ h => by cases h⟩
  | n :: l, seen, hs, h => by
    simp only [idsDistinct, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    have hlt : n.id < seen.size := hs n List.mem_cons_self
    obtain ⟨ih1, ih2⟩ := idsDistinct_spec l (seen.set! n.id true)
      (fun m hm => by simpa using hs m (List.mem_cons_of_mem _ hm)) h.2
    have hne : ∀ m ∈ l, m.id ≠ n.id := by
      intro m hm he
      have := ih2 m hm
      rw [he] at this
      simp [Array.getD_eq_getD_getElem?, hlt] at this
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, ih1⟩, fun m hm => ?_⟩
    · obtain ⟨m, hm, he⟩ := List.mem_map.1 hm
      exact hne m hm he
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact h.1
      · have := ih2 m hm
        simpa [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (hne m hm).symm]
          using this

/-- The node table of `schedValid`, by ID, for distinct IDs. -/
theorem nodes_lookup : ∀ (l : List SNode) (t : Array (Option (Array ID × Bool))),
    (l.map (·.id)).Nodup → (∀ n ∈ l, n.id < t.size) → ∀ x,
      (l.foldl (fun t n => t.set! n.id (some (n.args, n.prio == 0))) t)[x]?.join =
        match nodeOf l x with
        | some n => some (n.args, n.prio == 0)
        | none => t[x]?.join
  | [], t, _, _, x => rfl
  | n :: l, t, hd, hs, x => by
    have hd' := List.nodup_cons.1 (by simpa using hd : (n.id :: l.map (·.id)).Nodup)
    rw [List.foldl_cons, nodes_lookup l _ hd'.2 (fun m hm => by
      simpa using hs m (List.mem_cons_of_mem _ hm)) x]
    simp only [nodeOf, List.find?_cons]
    by_cases hx : n.id = x
    · subst hx
      have : l.find? (·.id == n.id) = none := by
        rw [List.find?_eq_none]
        intro m hm he
        exact hd'.1 (List.mem_map.2 ⟨m, hm, by simpa using he⟩)
      simp [this, hs n List.mem_cons_self]
    · have hx' : (n.id == x) = false := by simpa using hx
      simp only [hx', Bool.false_eq_true, ↓reduceIte]
      cases List.find? (fun m => m.id == x) l <;> simp [Array.getElem?_setIfInBounds_ne hx]

/-! ## The walk -/

theorem getD_set_ne {arr : Array Nat} {x a : Nat} {v d : Nat} (h : x ≠ a) :
    (arr.set! x v).getD a d = arr.getD a d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

/-- Pure flag of a node in the table (`true`: pure). -/
def pureFlag (look : ID → Option (Array ID × Bool)) (x : ID) : Bool :=
  match look x with
  | some (_, p) => p
  | none => true

/-- The state of `schedValidAux` after the prefix `P`: positions and the last non-pure node. -/
structure PosInv (look : ID → Option (Array ID × Bool)) (P : List ID) (pos : Array Nat)
    (np m : Nat) : Prop where
  size : pos.size = m
  posIn : ∀ i a, P[i]? = some a → pos.getD a 0 = i + 1
  posOut : ∀ a, a ∉ P → pos.getD a 0 = 0
  np0 : np = 0 → ∀ a ∈ P, pureFlag look a = true
  np1 : ∀ K, np = K + 1 → ∃ y, P[K]? = some y ∧ pureFlag look y = false ∧
    ∀ k y, K < k → P[k]? = some y → pureFlag look y = true

/-- What the walk establishes about `L = P ++ o` beyond position `j0 = |P|`. -/
structure WalkOK (look : ID → Option (Array ID × Bool)) (L : List ID) (j0 : Nat) : Prop where
  nodup : L.Nodup
  nodes : ∀ a ∈ L, look a ≠ none
  topo : ∀ j x args p, j0 ≤ j → L[j]? = some x → look x = some (args, p) →
    ∀ a ∈ args, look a ≠ none → ∃ i < j, L[i]? = some a
  pf : ∀ k j y x args, k < j → j0 ≤ j → L[k]? = some y → L[j]? = some x →
    pureFlag look y = false → look x = some (args, true) →
    ∃ a ∈ args, look a ≠ none ∧ ∃ i, k ≤ i ∧ i < j ∧ L[i]? = some a

theorem getElem?_append_eq {L P : List ID} {x : ID} (h : L = P ++ [x]) : L[P.length]? = some x := by
  subst h; simp

theorem walk_spec {nodes : Array (Option (Array ID × Bool))} {look : ID → Option (Array ID × Bool)}
    {m : Nat} (hlook : ∀ x, nodes[x]?.join = look x) (hm : ∀ x, look x ≠ none → x < m) :
    ∀ (o P : List ID) (pos : Array Nat) (np : Nat), P.Nodup → (∀ a ∈ P, look a ≠ none) →
      PosInv look P pos np m → schedValidAux nodes pos P.length np o = true →
        WalkOK look (P ++ o) P.length := by
  intro o
  induction o with
  | nil =>
    intro P pos np hn hP _ _
    refine ⟨by simpa using hn, by simpa using hP, ?_, ?_⟩
    · intro j x args p hj hx
      rw [List.append_nil, List.getElem?_eq_none hj] at hx; cases hx
    · intro k j y x args _ hj _ hx
      rw [List.append_nil, List.getElem?_eq_none hj] at hx; cases hx
  | cons x o ih =>
    intro P pos np hn hP hinv h
    simp only [schedValidAux, hlook] at h
    split at h
    · next args pu hx =>
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.or_eq_true,
        Option.isNone_iff_eq_none, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
        Array.any_eq_true', decide_eq_true_eq, Option.isSome_iff_ne_none] at h
      obtain ⟨⟨⟨hx0, hargs⟩, hk2⟩, hrest⟩ := h
      have hxP : x ∉ P := fun hm' => by
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hm'
        rw [hinv.posIn i x hi] at hx0; cases hx0
      have hxm : x < m := hm x (by rw [hx]; simp)
      -- the state after `x`
      have hinv' : PosInv look (P ++ [x]) (pos.set! x (P.length + 1))
          (if pu then np else P.length + 1) m := by
        refine ⟨by simp [hinv.size], ?_, ?_, ?_, ?_⟩
        · intro i a hi
          rcases Nat.lt_or_ge i P.length with hlt | hge
          · rw [List.getElem?_append_left hlt] at hi
            have hax : x ≠ a := fun e => hxP (e ▸ List.mem_of_getElem? hi)
            rw [getD_set_ne hax, hinv.posIn i a hi]
          · rw [List.getElem?_append_right hge] at hi
            have : i - P.length = 0 := by
              rcases h' : i - P.length with _ | n
              · rfl
              · rw [h'] at hi; simp at hi
            have hi' : i = P.length := by omega
            subst hi'
            simp at hi; subst hi
            simp [Array.getD_eq_getD_getElem?, hinv.size, hxm]
        · intro a ha
          have hax : x ≠ a := fun e => ha (by simp [e])
          rw [getD_set_ne hax]
          exact hinv.posOut a (fun h => ha (List.mem_append_left _ h))
        · intro hnp a ha
          split at hnp
          · next hpu =>
            rcases List.mem_append.1 ha with ha | ha
            · exact hinv.np0 hnp a ha
            · simp at ha; subst ha; simp [pureFlag, hx, hpu]
          · omega
        · intro K hK
          split at hK
          · next hpu =>
            obtain ⟨y, hy, hyp, hafter⟩ := hinv.np1 K hK
            refine ⟨y, by rw [List.getElem?_append_left (by
              rcases Nat.lt_or_ge K P.length with h | h
              · exact h
              · rw [List.getElem?_eq_none h] at hy; cases hy)]; exact hy, hyp, ?_⟩
            intro k z hk hz
            rcases Nat.lt_or_ge k P.length with hlt | hge
            · rw [List.getElem?_append_left hlt] at hz; exact hafter k z hk hz
            · rw [List.getElem?_append_right hge] at hz
              have : k - P.length = 0 := by
                rcases h' : k - P.length with _ | n
                · rfl
                · rw [h'] at hz; simp at hz
              rw [this] at hz; simp at hz; subst hz; simp [pureFlag, hx, hpu]
          · next hpu =>
            have hK' : K = P.length := by omega
            subst hK'
            refine ⟨x, by simp, by simp [pureFlag, hx]; simpa using hpu, ?_⟩
            intro k z hk hz
            have : (P ++ [x]).length ≤ k := by simp; omega
            rw [List.getElem?_eq_none this] at hz; cases hz
      have hn' : (P ++ [x]).Nodup := by
        rw [List.nodup_append]; exact ⟨hn, by simp, by simp; exact fun a ha e => hxP (e ▸ ha)⟩
      have hP' : ∀ a ∈ P ++ [x], look a ≠ none := by
        intro a ha; rcases List.mem_append.1 ha with ha | ha
        · exact hP a ha
        · simp at ha; subst ha; rw [hx]; simp
      have hW := ih (P ++ [x]) _ _ hn' hP' hinv' (by simpa using hrest)
      have hL : P ++ [x] ++ o = P ++ x :: o := by simp
      rw [hL] at hW
      refine ⟨hW.nodup, hW.nodes, ?_, ?_⟩
      · intro j z args' p hj hz hlz a ha hla
        rcases Nat.lt_or_ge P.length j with hlt | hge
        · exact hW.topo j z args' p (by simp; omega) hz hlz a ha hla
        · have hj : j = P.length := by omega
          subst hj
          simp at hz; subst hz
          rw [hx] at hlz; cases hlz
          have hpa := hargs a ha
          rcases hpa with hna | hpa
          · exact absurd hna hla
          · have : a ∈ P := Classical.byContradiction fun hn => hpa (hinv.posOut a hn)
            obtain ⟨i, hi⟩ := List.getElem?_of_mem this
            have hilt : i < P.length := by
              rcases Nat.lt_or_ge i P.length with h | h
              · exact h
              · rw [List.getElem?_eq_none h] at hi; cases hi
            exact ⟨i, hilt, by rw [List.getElem?_append_left hilt]; exact hi⟩
      · intro k j y z args' hkj hj hy hz hyp hlz
        rcases Nat.lt_or_ge P.length j with hlt | hge
        · exact hW.pf k j y z args' hkj (by simp; omega) hy hz hyp hlz
        · have hj' : j = P.length := by omega
          subst hj'
          simp at hz; subst hz
          rw [hx] at hlz; cases hlz
          have hy' : P[k]? = some y := by rwa [List.getElem?_append_left hkj] at hy
          rcases hk2 with (hk2 | hk2) | hk2
          · simp at hk2
          · -- no non-pure node in P
            exact absurd (hinv.np0 hk2 y (List.mem_of_getElem? hy')) (by simp [hyp])
          · obtain ⟨a, ha, hla, hle⟩ := hk2
            obtain ⟨K, hK⟩ : ∃ K, np = K + 1 := ⟨np - 1, by
              rcases Nat.eq_zero_or_pos np with h0 | h0
              · rw [h0] at hle
                exact absurd (hinv.np0 h0 y (List.mem_of_getElem? hy')) (by simp [hyp])
              · omega⟩
            obtain ⟨_, _, _, hafter⟩ := hinv.np1 K hK
            have hkK : k ≤ K := by
              rcases Nat.lt_or_ge K k with h | h
              · exact absurd (hafter k y h hy') (by simp [hyp])
              · exact h
            have haP : a ∈ P := Classical.byContradiction fun hn => by
              rw [hinv.posOut a hn] at hle; omega
            obtain ⟨i, hi⟩ := List.getElem?_of_mem haP
            have hilt : i < P.length := by
              rcases Nat.lt_or_ge i P.length with h | h
              · exact h
              · rw [List.getElem?_eq_none h] at hi; cases hi
            rw [hinv.posIn i a hi] at hle
            refine ⟨a, ha, hla, i, by omega, hilt, ?_⟩
            rw [List.getElem?_append_left hilt]; exact hi
    · cases h

/-! ## The specification -/

/-- The node table as `schedValid` builds it. -/
def lookOf (vs : List SNode) (x : ID) : Option (Array ID × Bool) :=
  (nodeOf vs x).map fun n => (n.args, n.prio == 0)

theorem nodeOf_mem {vs : List SNode} {x : ID} {n : SNode} (h : nodeOf vs x = some n) :
    n ∈ vs ∧ n.id = x := by
  unfold nodeOf at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem nodeOf_of_mem {vs : List SNode} (hd : (vs.map (·.id)).Nodup) {n : SNode} (h : n ∈ vs) :
    nodeOf vs n.id = some n := by
  induction vs with
  | nil => cases h
  | cons a vs ih =>
    have hd' := List.nodup_cons.1 (by simpa using hd : (a.id :: vs.map (·.id)).Nodup)
    unfold nodeOf
    rw [List.find?_cons]
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have hne : a.id ≠ n.id := fun e => hd'.1 (List.mem_map.2 ⟨n, h, e.symm⟩)
      simp only [show (a.id == n.id) = false by simpa using hne]
      exact ih (by simpa using hd'.2) h

theorem nodeIn_iff {vs : List SNode} {x : ID} : NodeIn vs x ↔ nodeOf vs x ≠ none := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    unfold nodeOf
    intro h
    rw [List.find?_eq_none] at h
    exact h n hn (by simp)
  · intro h
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.1 h
    exact ⟨n, (nodeOf_mem hn).1, (nodeOf_mem hn).2⟩

theorem schedValid_spec {vs : Array SNode} {o : Array ID} (h : schedValid vs o = true) :
    SchedSpec vs.toList o.toList := by
  unfold schedValid at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hd, hsz⟩, hw⟩ := h
  have hlt : ∀ n ∈ vs.toList, n.id < maxNodeId vs + 1 := fun n hn => id_lt_maxNodeId hn
  have hdist := (idsDistinct_spec vs.toList _ (by simpa using hlt) hd).1
  have hlook : ∀ x, (vs.foldl (fun t n => t.set! n.id (some (n.args, n.prio == 0)))
      (Array.replicate (maxNodeId vs + 1) none))[x]?.join = lookOf vs.toList x := by
    intro x
    rw [← Array.foldl_toList, nodes_lookup _ _ hdist (by simpa using hlt) x]
    unfold lookOf
    cases nodeOf vs.toList x with
    | none => simp [Array.getElem?_replicate]; split <;> rfl
    | some n => rfl
  have hm : ∀ x, lookOf vs.toList x ≠ none → x < maxNodeId vs + 1 := by
    intro x hx
    unfold lookOf at hx
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.1 (by simpa using hx)
    obtain ⟨hmem, rfl⟩ := nodeOf_mem hn
    exact hlt n hmem
  have hinv0 : PosInv (lookOf vs.toList) [] (Array.replicate (maxNodeId vs + 1) 0) 0
      (maxNodeId vs + 1) := by
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · intro i a h; cases h
    · intro a _
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    · intro _ a h; cases h
    · intro K h; omega
  have W := walk_spec hlook hm o.toList [] _ 0 List.nodup_nil (fun _ h => by cases h) hinv0 hw
  simp only [List.nil_append, List.length_nil] at W
  have hnode : ∀ a, lookOf vs.toList a ≠ none ↔ NodeIn vs.toList a := by
    intro a; rw [nodeIn_iff]; unfold lookOf; simp
  refine ⟨hdist, ⟨W.nodup, fun x => ⟨fun hx => (hnode x).1 (W.nodes x hx), fun hx => ?_⟩, ?_⟩, ?_⟩
  · -- every node is listed: `o` has as many distinct entries as there are nodes
    refine Classical.byContradiction fun hno => ?_
    have hsub : x :: o.toList ⊆ vs.toList.map (·.id) := by
      intro a ha
      rcases List.mem_cons.1 ha with rfl | ha
      · obtain ⟨n, hn, rfl⟩ := hx; exact List.mem_map.2 ⟨n, hn, rfl⟩
      · obtain ⟨n, hn, rfl⟩ := (hnode a).1 (W.nodes a ha); exact List.mem_map.2 ⟨n, hn, rfl⟩
    have := List.Nodup.length_le_of_subset (List.nodup_cons.2 ⟨hno, W.nodup⟩) hsub
    simp [hsz] at this
    omega
  · intro j x hx a ha hNa
    have hxl : lookOf vs.toList x ≠ none := W.nodes x (List.mem_of_getElem? hx)
    obtain ⟨⟨args, p⟩, hl⟩ := Option.ne_none_iff_exists'.1 hxl
    have ha' : a ∈ args := by
      unfold argsOf at ha; unfold lookOf at hl
      cases hn : nodeOf vs.toList x with
      | none => rw [hn] at hl; cases hl
      | some n => rw [hn] at hl ha; cases hl; simpa using ha
    exact W.topo j x args p (Nat.zero_le _) hx hl a ha' ((hnode a).2 hNa)
  · intro k j y x hkj hy hx hpy hpx
    have hxl : lookOf vs.toList x ≠ none := W.nodes x (List.mem_of_getElem? hx)
    obtain ⟨⟨args, p⟩, hl⟩ := Option.ne_none_iff_exists'.1 hxl
    obtain ⟨n, hn, hnx⟩ : ∃ n, nodeOf vs.toList x = some n ∧ lookOf vs.toList x = some (n.args, n.prio == 0) := by
      unfold lookOf at hl ⊢
      cases hn : nodeOf vs.toList x with
      | none => rw [hn] at hl; cases hl
      | some n => exact ⟨n, rfl, rfl⟩
    have hyfalse : pureFlag (lookOf vs.toList) y = false := by
      unfold PureIn at hpy
      obtain ⟨m, hm, hmp⟩ : ∃ m, nodeOf vs.toList y = some m ∧ m.prio ≠ 0 :=
        Classical.byContradiction fun hc => hpy fun m hm =>
          Classical.byContradiction fun hp => hc ⟨m, hm, hp⟩
      simp [pureFlag, lookOf, hm, hmp]
    have hxp : (n.prio == 0) = true := by simpa using hpx n hn
    rw [hxp] at hnx
    obtain ⟨a, ha, hla, i, hki, hij, hia⟩ :=
      W.pf k j y x n.args hkj (Nat.zero_le _) hy hx hyfalse hnx
    refine ⟨a, ?_, (hnode a).1 hla, i, hki, hij, hia⟩
    unfold argsOf; rw [hn]; simpa using ha

/-- **What `schedule` guarantees.** -/
theorem schedule_spec {f : Func} {b : Block} {o : Array ID} (h : schedule f b = some o) :
    SchedSpec (schedNodes f b).toList o.toList := by
  unfold schedule at h
  rw [Option.filter_eq_some_iff] at h
  exact schedValid_spec h.2

end GoFV.Proof
