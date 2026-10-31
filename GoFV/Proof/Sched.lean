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

/-! ## The fallback scheduler -/

theorem mem_eraseIdx_ids {rem : List SNode} (hd : (rem.map (·.id)).Nodup) {i : Nat}
    (hi : i < rem.length) (n : SNode) : n ∈ rem.eraseIdx i ↔ n ∈ rem ∧ n.id ≠ rem[i].id := by
  rw [List.mem_eraseIdx_iff_getElem]
  constructor
  · rintro ⟨j, hj, hji, rfl⟩
    refine ⟨List.getElem_mem hj, fun he => hji ?_⟩
    have : (rem.map (·.id))[j]'(by simpa using hj) = (rem.map (·.id))[i]'(by simpa using hi) := by
      simpa using he
    exact (hd.getElem_inj).1 this
  · rintro ⟨hn, hne⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
    exact ⟨j, hj, fun e => hne (by subst e; rfl), rfl⟩

theorem argsOf_of_mem {vs : List SNode} (hd : (vs.map (·.id)).Nodup) {n : SNode} (h : n ∈ vs) :
    argsOf vs n.id = n.args.toList := by
  unfold argsOf; rw [nodeOf_of_mem hd h]; rfl

theorem pureIn_of_mem {vs : List SNode} (hd : (vs.map (·.id)).Nodup) {n : SNode} (h : n ∈ vs) :
    PureIn vs n.id ↔ n.prio = 0 := by
  unfold PureIn; rw [nodeOf_of_mem hd h]
  constructor
  · intro hp; exact hp n rfl
  · intro hp m hm; cases hm; exact hp

theorem nodeIn_any {vs : List SNode} {a : ID} : vs.any (·.id == a) = true ↔ NodeIn vs a := by
  simp [NodeIn]

/-- The state of `greedy` after placing `P` (with `rem` left): `np` is 1 + the position of the
last non-pure node placed (0: none), and every pure node left was not ready then. -/
structure GInv (vs : List SNode) (rem : List SNode) (P : List ID) (np : Nat) : Prop where
  remSub : ∀ n ∈ rem, n ∈ vs
  remIds : (rem.map (·.id)).Nodup
  nodup : P.Nodup
  cover : ∀ n ∈ vs, n.id ∈ P ∨ n ∈ rem
  disj : ∀ n ∈ rem, n.id ∉ P
  nodes : ∀ x ∈ P, NodeIn vs x
  topo : ∀ (j : Nat) x, P[j]? = some x → ∀ a ∈ argsOf vs x, NodeIn vs a → ∃ i < j, P[i]? = some a
  pf : PureFirst (NodeIn vs) (argsOf vs) (PureIn vs) P
  np0 : np = 0 → ∀ x ∈ P, PureIn vs x
  np1 : ∀ K, np = K + 1 → (∃ y, P[K]? = some y ∧ ¬ PureIn vs y) ∧
    (∀ k y, K < k → P[k]? = some y → PureIn vs y) ∧
    ∀ n ∈ rem, n.prio = 0 → ∃ a ∈ n.args, NodeIn vs a ∧ a ∉ P.take K

theorem getElem?_concat_self {P : List ID} {x : ID} : (P ++ [x])[P.length]? = some x := by simp

theorem getElem?_concat_lt {P : List ID} {x : ID} {k : Nat} (h : k < P.length) :
    (P ++ [x])[k]? = P[k]? := List.getElem?_append_left h

theorem getElem?_concat_ge {P : List ID} {x : ID} {k : Nat} (h : P.length ≤ k)
    (h' : (P ++ [x])[k]? = some y) : k = P.length ∧ y = x := by
  rw [List.getElem?_append_right h] at h'
  rcases hk : k - P.length with _ | n
  · rw [hk] at h'; simp at h'; exact ⟨by omega, h'.symm⟩
  · rw [hk] at h'; simp at h'

theorem lt_length_of_getElem? {P : List ID} {k : Nat} {y : ID} (h : P[k]? = some y) :
    k < P.length := by
  rcases Nat.lt_or_ge k P.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

/-- Placing a ready node `n` (pure, or non-pure when no pure node is ready) keeps `GInv`. -/
theorem GInv.step {vs rem : List SNode} {P : List ID} {np : Nat}
    (hd : (vs.map (·.id)).Nodup) (hI : GInv vs rem P np) {i : Nat} (hi : i < rem.length)
    (hready : ∀ a ∈ rem[i].args, NodeIn vs a → a ∈ P)
    (hpure : rem[i].prio ≠ 0 → ∀ m ∈ rem, m.prio = 0 → ∃ a ∈ m.args, NodeIn vs a ∧ a ∉ P) :
    GInv vs (rem.eraseIdx i) (P ++ [rem[i].id]) (if rem[i].prio = 0 then np else P.length + 1) := by
  have hn : rem[i] ∈ vs := hI.remSub _ (List.getElem_mem hi)
  have hnP : rem[i].id ∉ P := hI.disj _ (List.getElem_mem hi)
  have hmem := mem_eraseIdx_ids hI.remIds hi
  have hargs := argsOf_of_mem hd hn
  have hpi := pureIn_of_mem hd hn
  refine ⟨fun m hm => hI.remSub m ((hmem m).1 hm).1,
    hI.remIds.sublist ((List.eraseIdx_sublist rem i).map _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.nodup_append]; exact ⟨hI.nodup, by simp, by simp; exact fun a ha e => hnP (e ▸ ha)⟩
  · intro m hm
    rcases hI.cover m hm with h | h
    · exact .inl (List.mem_append_left _ h)
    · by_cases he : m.id = rem[i].id
      · exact .inl (by simp [he])
      · exact .inr ((hmem m).2 ⟨h, he⟩)
  · intro m hm hmP
    obtain ⟨hm1, hm2⟩ := (hmem m).1 hm
    rcases List.mem_append.1 hmP with h | h
    · exact hI.disj m hm1 h
    · simp at h; exact hm2 h
  · intro x hx
    rcases List.mem_append.1 hx with h | h
    · exact hI.nodes x h
    · simp at h; subst h; exact ⟨rem[i], hn, rfl⟩
  · intro j x hx a ha hNa
    rcases Nat.lt_or_ge j P.length with hj | hj
    · rw [getElem?_concat_lt hj] at hx
      obtain ⟨i', hi', h'⟩ := hI.topo j x hx a ha hNa
      exact ⟨i', hi', by rw [getElem?_concat_lt (by omega)]; exact h'⟩
    · obtain ⟨rfl, rfl⟩ := getElem?_concat_ge hj hx
      rw [hargs] at ha
      obtain ⟨i', hi'⟩ := List.getElem?_of_mem (hready a (by simpa using ha) hNa)
      have := lt_length_of_getElem? hi'
      exact ⟨i', this, by rw [getElem?_concat_lt this]; exact hi'⟩
  · intro k j y x hkj hy hx hpy hpx
    rcases Nat.lt_or_ge j P.length with hj | hj
    · rw [getElem?_concat_lt hj] at hx
      rw [getElem?_concat_lt (by omega)] at hy
      obtain ⟨a, ha, hNa, i', hki, hij, h'⟩ := hI.pf k j y x hkj hy hx hpy hpx
      exact ⟨a, ha, hNa, i', hki, hij, by rw [getElem?_concat_lt (by omega)]; exact h'⟩
    · obtain ⟨rfl, rfl⟩ := getElem?_concat_ge hj hx
      rw [getElem?_concat_lt hkj] at hy
      have hp0 : rem[i].prio = 0 := hpi.1 hpx
      -- some non-pure node was placed before: `np = K + 1` with `k ≤ K`
      have hnp : np ≠ 0 := fun h0 => hpy (hI.np0 h0 y (List.mem_of_getElem? hy))
      obtain ⟨K, hK⟩ : ∃ K, np = K + 1 := ⟨np - 1, by omega⟩
      obtain ⟨⟨y', hy', _⟩, hafter, hpend⟩ := hI.np1 K hK
      have hkK : k ≤ K := by
        rcases Nat.lt_or_ge K k with h | h
        · exact absurd (hafter k y h hy) hpy
        · exact h
      obtain ⟨a, ha, hNa, haK⟩ := hpend rem[i] (List.getElem_mem hi) hp0
      obtain ⟨i', hi'⟩ := List.getElem?_of_mem (hready a ha hNa)
      have hlt := lt_length_of_getElem? hi'
      have hKi : K ≤ i' := by
        rcases Nat.lt_or_ge i' K with h | h
        · exact absurd (List.mem_of_getElem? (by rw [List.getElem?_take_of_lt h]; exact hi')) haK
        · exact h
      refine ⟨a, by rw [hargs]; simpa using ha, hNa, i', by omega, hlt, ?_⟩
      rw [getElem?_concat_lt hlt]; exact hi'
  · intro h0 x hx
    split at h0
    · next hp =>
      rcases List.mem_append.1 hx with h | h
      · exact hI.np0 h0 x h
      · simp at h; subst h; exact hpi.2 hp
    · omega
  · intro K hK
    split at hK
    · next hp =>
      obtain ⟨⟨y, hy, hny⟩, hafter, hpend⟩ := hI.np1 K hK
      have hKl := lt_length_of_getElem? hy
      refine ⟨⟨y, by rw [getElem?_concat_lt hKl]; exact hy, hny⟩, ?_, ?_⟩
      · intro k z hk hz
        rcases Nat.lt_or_ge k P.length with h | h
        · rw [getElem?_concat_lt h] at hz; exact hafter k z hk hz
        · obtain ⟨rfl, rfl⟩ := getElem?_concat_ge h hz; exact hpi.2 hp
      · intro m hm hm0
        obtain ⟨a, ha, hNa, haK⟩ := hpend m ((hmem m).1 hm).1 hm0
        refine ⟨a, ha, hNa, ?_⟩
        rwa [List.take_append_of_le_length (by omega)]
    · next hp =>
      have hK' : K = P.length := by omega
      subst hK'
      refine ⟨⟨rem[i].id, getElem?_concat_self, fun h => hp (hpi.1 h)⟩, ?_, ?_⟩
      · intro k z hk hz
        have : (P ++ [rem[i].id]).length ≤ k := by simp; omega
        rw [List.getElem?_eq_none this] at hz; cases hz
      · intro m hm hm0
        obtain ⟨a, ha, hNa, haP⟩ := hpure hp m ((hmem m).1 hm).1 hm0
        exact ⟨a, ha, hNa, by simpa using haP⟩

/-- `greedy` places nodes so that `GInv` holds at the end. -/
theorem greedy_inv {vs : List SNode} (hd : (vs.map (·.id)).Nodup) :
    ∀ (fuel : Nat) (rem : List SNode) (P : List ID) (np : Nat) (o : List ID),
      GInv vs rem P np → greedy vs fuel rem P.reverse = some o →
        ∃ np', GInv vs [] o np' := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem P np o hI h
    cases rem with
    | nil => simp [greedy] at h; subst h; exact ⟨np, hI⟩
    | cons _ _ => simp [greedy] at h
  | succ fuel ih =>
    intro rem P np o hI h
    cases rem with
    | nil => simp [greedy] at h; subst h; exact ⟨np, hI⟩
    | cons r rs =>
      have hready : ∀ (n : SNode), (n.args.all fun a => !(vs.any (·.id == a)) ||
          P.reverse.contains a) = true → ∀ a ∈ n.args, NodeIn vs a → a ∈ P := by
        intro n hn a ha hNa
        rw [Array.all_eq_true'] at hn
        have := hn a ha
        simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
        rcases this with h | h
        · exact absurd (nodeIn_any.2 hNa) (by rw [h]; simp)
        · simpa using h
      simp only [greedy] at h
      split at h
      · next i hi =>
        obtain ⟨hlt, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
        simp only [Bool.and_eq_true, beq_iff_eq] at hpi
        rw [List.getElem?_eq_getElem hlt] at h
        simp only [Option.map_some, Option.getD_some] at h
        have hI' := hI.step hd hlt (hready _ hpi.2) (fun hp => absurd hpi.1 hp)
        rw [if_pos hpi.1] at hI'
        exact ih _ _ _ _ hI' (by simpa using h)
      · next hnone =>
        rw [List.findIdx?_eq_none_iff] at hnone
        split at h
        · next i hi =>
          obtain ⟨hlt, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
          rw [List.getElem?_eq_getElem hlt] at h
          simp only [Option.map_some, Option.getD_some] at h
          have hnp : ∀ m ∈ r :: rs, m.prio = 0 → ∃ a ∈ m.args, NodeIn vs a ∧ a ∉ P := by
            intro m hm hm0
            have h1 := hnone m hm
            rw [hm0] at h1
            simp only [beq_self_eq_true, Bool.true_and] at h1
            refine Classical.byContradiction fun hc => ?_
            have hall : (m.args.all fun a => !(vs.any (·.id == a)) || P.reverse.contains a) =
                true := by
              rw [Array.all_eq_true']
              intro a ha
              by_cases hNa : NodeIn vs a
              · have : a ∈ P := Classical.byContradiction fun haP => hc ⟨a, ha, hNa, haP⟩
                simp [this]
              · have : (vs.any (·.id == a)) = false := by
                  cases h : vs.any (·.id == a) with
                  | false => rfl
                  | true => exact absurd (nodeIn_any.1 h) hNa
                simp [this]
            rw [hall] at h1; cases h1
          have hI' := hI.step hd hlt (hready _ hpi) (fun _ => hnp)
          exact ih _ _ _ _ hI' (by simpa using h)
        · cases h

theorem GInv.start {vs : List SNode} (hd : (vs.map (·.id)).Nodup) : GInv vs vs [] 0 := by
  refine ⟨fun _ h => h, hd, List.nodup_nil, fun _ h => .inr h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro _ _ h; cases h
  · intro _ h; cases h
  · intro j x h; cases h
  · intro k j y x _ h; cases h
  · intro _ x h; cases h
  · intro K h; omega

theorem GInv.done {vs : List SNode} {o : List ID} {np : Nat} (hI : GInv vs [] o np) :
    Topo (NodeIn vs) (argsOf vs) o ∧ PureFirst (NodeIn vs) (argsOf vs) (PureIn vs) o := by
  refine ⟨⟨hI.nodup, fun x => ⟨hI.nodes x, fun ⟨n, hn, hx⟩ => ?_⟩, hI.topo⟩, hI.pf⟩
  rcases hI.cover n hn with h | h
  · exact hx ▸ h
  · cases h

/-- Some node left is ready, when the nodes have a dependency order. -/
theorem GInv.exists_ready {vs rem : List SNode} {P : List ID} {np : Nat}
    (hd : (vs.map (·.id)).Nodup) (hI : GInv vs rem P np) {T : List ID}
    (hT : Topo (NodeIn vs) (argsOf vs) T) {r : SNode} (hr : r ∈ rem) :
    ∃ n ∈ rem, ∀ a ∈ n.args, NodeIn vs a → a ∈ P := by
  have key : ∀ (k : Nat) n, n ∈ rem → T[k]? = some n.id →
      ∃ n ∈ rem, ∀ a ∈ n.args, NodeIn vs a → a ∈ P := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro n hn hk
      by_cases hready : ∀ a ∈ n.args, NodeIn vs a → a ∈ P
      · exact ⟨n, hn, hready⟩
      · obtain ⟨a, ha, hNa, haP⟩ : ∃ a ∈ n.args, NodeIn vs a ∧ a ∉ P :=
          Classical.byContradiction fun hc => hready fun a ha hNa =>
            Classical.byContradiction fun haP => hc ⟨a, ha, hNa, haP⟩
        obtain ⟨m, hm, rfl⟩ := hNa
        have hmr : m ∈ rem := (hI.cover m hm).resolve_left haP
        have hargs := argsOf_of_mem hd (hI.remSub n hn)
        obtain ⟨i, hi, hTi⟩ :=
          hT.before k n.id hk m.id (by rw [hargs]; simpa using ha) ⟨m, hm, rfl⟩
        exact ih i hi m hmr hTi
  obtain ⟨k, hk⟩ := List.getElem?_of_mem ((hT.mem r.id).2 ⟨r, hI.remSub r hr, rfl⟩)
  exact key k r hr hk

theorem ready_of_all {vs : List SNode} {P : List ID} (m : SNode)
    (hm : (m.args.all fun a => !(vs.any (·.id == a)) || P.reverse.contains a) = true) :
    ∀ a ∈ m.args, NodeIn vs a → a ∈ P := by
  intro a ha hNa
  rw [Array.all_eq_true'] at hm
  have := hm a ha
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  rcases this with h | h
  · exact absurd (nodeIn_any.2 hNa) (by rw [h]; simp)
  · simpa using h

theorem all_of_ready {vs : List SNode} {P : List ID} (m : SNode)
    (hm : ∀ a ∈ m.args, NodeIn vs a → a ∈ P) :
    (m.args.all fun a => !(vs.any (·.id == a)) || P.reverse.contains a) = true := by
  rw [Array.all_eq_true']
  intro a ha
  by_cases hNa : NodeIn vs a
  · simp [hm a ha hNa]
  · have : (vs.any (·.id == a)) = false := by
      cases h : vs.any (·.id == a) with
      | false => rfl
      | true => exact absurd (nodeIn_any.1 h) hNa
    simp [this]

theorem greedy_complete {vs : List SNode} (hd : (vs.map (·.id)).Nodup) {T : List ID}
    (hT : Topo (NodeIn vs) (argsOf vs) T) :
    ∀ (fuel : Nat) (rem : List SNode) (P : List ID) (np : Nat), GInv vs rem P np →
      rem.length ≤ fuel → ∃ o, greedy vs fuel rem P.reverse = some o := by
  intro fuel
  induction fuel with
  | zero =>
    intro rem P np _ hl
    cases rem with
    | nil => exact ⟨_, rfl⟩
    | cons _ _ => simp at hl
  | succ fuel ih =>
    intro rem P np hI hl
    cases rem with
    | nil => exact ⟨_, rfl⟩
    | cons r rs =>
      obtain ⟨n, hn, hnr⟩ := hI.exists_ready hd hT List.mem_cons_self
      simp only [greedy]
      split
      · next i hi =>
        obtain ⟨hlt, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
        simp only [Bool.and_eq_true, beq_iff_eq] at hpi
        rw [List.getElem?_eq_getElem hlt]
        have hI' := hI.step hd hlt (ready_of_all _ hpi.2) (fun hp => absurd hpi.1 hp)
        rw [if_pos hpi.1] at hI'
        obtain ⟨o, ho⟩ := ih _ _ _ hI' (by
          rw [List.length_eraseIdx_of_lt hlt]; simp at hl ⊢; omega)
        exact ⟨o, by simpa using ho⟩
      · next hnone =>
        rw [List.findIdx?_eq_none_iff] at hnone
        split
        · next i hi =>
          obtain ⟨hlt, hpi, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
          rw [List.getElem?_eq_getElem hlt]
          have hnp : ∀ m ∈ r :: rs, m.prio = 0 → ∃ a ∈ m.args, NodeIn vs a ∧ a ∉ P := by
            intro m hm hm0
            have h1 := hnone m hm
            rw [hm0] at h1
            simp only [beq_self_eq_true, Bool.true_and] at h1
            refine Classical.byContradiction fun hc => ?_
            rw [all_of_ready m (fun a ha hNa => Classical.byContradiction fun haP =>
              hc ⟨a, ha, hNa, haP⟩)] at h1
            cases h1
          have hI' := hI.step hd hlt (ready_of_all _ hpi) (fun _ => hnp)
          obtain ⟨o, ho⟩ := ih _ _ _ hI' (by
            rw [List.length_eraseIdx_of_lt hlt]; simp at hl ⊢; omega)
          exact ⟨o, by simpa using ho⟩
        · next hnone2 =>
          rw [List.findIdx?_eq_none_iff] at hnone2
          exact absurd (all_of_ready n hnr) (by rw [hnone2 n hn]; simp)

/-- **What `schedule` guarantees.** -/
theorem schedule_spec {f : Func} {b : Block} {o : Array ID} (h : schedule f b = some o) :
    SchedSpec (schedNodes f b).toList o.toList := by
  unfold schedule at h
  simp only at h
  split at h
  · next hd =>
    have hlt : ∀ n ∈ (schedNodes f b).toList, n.id < maxNodeId (schedNodes f b) + 1 :=
      fun n hn => id_lt_maxNodeId hn
    have hdist := (idsDistinct_spec _ _ (by simpa using hlt) hd).1
    split at h
    · next o' ho =>
      cases h
      rw [Option.filter_eq_some_iff] at ho
      exact schedValid_spec ho.2
    · obtain ⟨o', ho', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨np, hI⟩ := greedy_inv hdist _ _ [] 0 o' (GInv.start hdist) ho'
      obtain ⟨ht, hpf⟩ := hI.done
      exact ⟨hdist, by simpa using ht, by simpa using hpf⟩
  · cases h

theorem idsDistinct_of_nodup : ∀ (l : List SNode) (seen : Array Bool),
    (l.map (·.id)).Nodup → (∀ n ∈ l, seen.getD n.id false = false) → idsDistinct seen l = true
  | [], _, _, _ => rfl
  | n :: l, seen, hd, hs => by
    have hd' := List.nodup_cons.1 (by simpa using hd : (n.id :: l.map (·.id)).Nodup)
    simp only [idsDistinct, hs n List.mem_cons_self, Bool.not_false, Bool.true_and]
    refine idsDistinct_of_nodup l _ (by simpa using hd'.2) fun m hm => ?_
    have hne : n.id ≠ m.id := fun e => hd'.1 (List.mem_map.2 ⟨m, hm, e.symm⟩)
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne hne]
      using hs m (List.mem_cons_of_mem _ hm)

/-- `schedule` is defined on every block whose non-`Phi` values have distinct IDs and a
dependency order. -/
theorem schedule_some {f : Func} {b : Block}
    (hd : ((schedNodes f b).toList.map (·.id)).Nodup) {T : List ID}
    (hT : Topo (NodeIn (schedNodes f b).toList) (argsOf (schedNodes f b).toList) T) :
    ∃ o, schedule f b = some o := by
  unfold schedule
  rw [if_pos (idsDistinct_of_nodup _ _ hd fun n _ => by
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]; split <;> rfl)]
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨o, ho⟩ := greedy_complete hd hT (schedNodes f b).size _ [] 0 (GInv.start hd)
      (by simp)
    exact ⟨o.toArray, by simp only [List.reverse_nil] at ho; simp [ho]⟩

end GoFV.Proof
