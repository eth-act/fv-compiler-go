import GoFV.Proof.Pass.DeadRel

/-!
# Deciding `Chained`

`chainedB f B` checks, in every block of `B`, that every two side-effecting roots (priority 2)
are ordered by dependency: it computes the ancestors of each root inside the block
(`ancOf`, a worklist walk over the arguments that are nodes of the block) and checks that of
every two roots one is an ancestor of the other. `chained_of`: it implies `Chained` (the walk
only adds dependencies, `ancW_sound`; whether it finds them all does not matter for soundness).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- `x` is a non-`Phi` value of the block (a node of its schedule, `nodeB_sound`). -/
def nodeB (f : Func) (fb : Block) (x : ID) : Bool :=
  fb.values.contains x && (f.value? x).any (·.op != .Phi)

/-- The arguments of value `x`. -/
def argsV (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

/-- The ancestor walk: `fuel`, the stack, the nodes found so far. -/
def ancW (f : Func) (fb : Block) : Nat → List ID → List ID → List ID
  | 0, _, vis => vis
  | _, [], vis => vis
  | n + 1, y :: st, vis =>
    let new := (argsV f y).filter fun a => nodeB f fb a && !vis.contains a
    ancW f fb n (new ++ st) (new ++ vis)

/-- Nodes of the block that root `r` depends on (found within `|values| + 1` steps per value). -/
def ancOf (f : Func) (fb : Block) (r : ID) : List ID :=
  ancW f fb ((fb.values.size + 1) * (fb.values.size + 1)) [r] []

/-- The priority-2 roots of a block. -/
def roots2 (f : Func) (fb : Block) : List ID :=
  ((schedNodes f fb).toList.filter (·.prio == 2)).map (·.id)

/-- Decides `Chained` (for well-formed `f`, `chained_of`). -/
def chainedB (f : Func) (B : Array ID) : Bool :=
  B.all fun bid =>
    match f.block? bid with
    | none => true
    | some fb =>
      let ancs := (roots2 f fb).map fun r => (r, ancOf f fb r)
      ancs.all fun (y, ay) => ancs.all fun (x, ax) => x == y || ay.contains x || ax.contains y

/-- The nodes of block `fb`'s schedule. -/
abbrev NB (f : Func) (fb : Block) : ID → Prop := NodeIn (schedNodes f fb).toList

/-- Their arguments. -/
abbrev DB (f : Func) (fb : Block) : ID → List ID := argsOf (schedNodes f fb).toList

section
variable {ce : CheckEnv} {f : Func} {bid : ID} {fb : Block}

theorem nodeB_sound (hwf : WF ce f) (hb : bid ∈ f.blocks) (hfb : f.block? bid = some fb)
    {x : ID} (h : nodeB f fb x = true) : NB f fb x := by
  unfold nodeB at h
  simp only [Bool.and_eq_true, Array.contains_iff_mem, Option.any_eq_true, bne_iff_ne,
    ne_eq] at h
  obtain ⟨hx, v, hv, hp⟩ := h
  exact (nodeIn_schedNodes (valuesOwn hwf hb hfb)).2 ⟨hx, v, hv, hp⟩

theorem argsV_node (hwf : WF ce f) (hb : bid ∈ f.blocks) (hfb : f.block? bid = some fb)
    {y : ID} (hy : NB f fb y) : DB f fb y = argsV f y := by
  obtain ⟨hyb, v, hv, hp⟩ := (nodeIn_schedNodes (valuesOwn hwf hb hfb)).1 hy
  show argsOf _ y = _
  rw [argsOf_schedNodes (valuesOwn hwf hb hfb) (hwf.valuesNodup _ _ ⟨hb, hfb⟩) hyb hv hp]
  simp [argsV, hv]

/-- Every node the walk finds is a dependency of `r`. -/
theorem ancW_sound (hwf : WF ce f) (hb : bid ∈ f.blocks) (hfb : f.block? bid = some fb)
    {r : ID} : ∀ (n : Nat) (st vis : List ID),
      (∀ y ∈ st, NB f fb y ∧ (y = r ∨ Order.Dep (NB f fb) (DB f fb) y r)) →
      (∀ a ∈ vis, Order.Dep (NB f fb) (DB f fb) a r) →
      ∀ a ∈ ancW f fb n st vis, Order.Dep (NB f fb) (DB f fb) a r
  | 0, _, _, _, hv => by simpa [ancW] using hv
  | n + 1, [], vis, _, hv => by simpa [ancW] using hv
  | n + 1, y :: st, vis, hs, hv => by
    obtain ⟨hNy, hyr⟩ := hs y List.mem_cons_self
    have hnew : ∀ a ∈ (argsV f y).filter (fun a => nodeB f fb a && !vis.contains a),
        NB f fb a ∧ Order.Dep (NB f fb) (DB f fb) a r := by
      intro a ha
      rw [List.mem_filter, Bool.and_eq_true] at ha
      have hNa := nodeB_sound hwf hb hfb ha.2.1
      have hd : Order.Dep (NB f fb) (DB f fb) a y :=
        .arg hNa hNy (by rw [argsV_node hwf hb hfb hNy]; exact ha.1)
      refine ⟨hNa, ?_⟩
      rcases hyr with rfl | hyr
      · exact hd
      · exact .trans hd hyr
    refine ancW_sound hwf hb hfb n _ _ (fun z hz => ?_) (fun a ha => ?_)
    · rcases List.mem_append.1 hz with hz | hz
      · obtain ⟨h1, h2⟩ := hnew z hz; exact ⟨h1, .inr h2⟩
      · exact hs z (List.mem_cons_of_mem _ hz)
    · rcases List.mem_append.1 ha with ha | ha
      · exact (hnew a ha).2
      · exact hv a ha

theorem ancOf_sound (hwf : WF ce f) (hb : bid ∈ f.blocks) (hfb : f.block? bid = some fb)
    {r : ID} (hr : NB f fb r) {a : ID} (h : a ∈ ancOf f fb r) :
    Order.Dep (NB f fb) (DB f fb) a r :=
  ancW_sound hwf hb hfb _ [r] [] (fun y hy => by
    rw [List.mem_singleton] at hy; subst hy; exact ⟨hr, .inl rfl⟩) (fun _ h => nomatch h) a h

/-- A node that is not of priority ≤ 1 is a priority-2 root. -/
theorem mem_roots2 (hwf : WF ce f) (hb : bid ∈ f.blocks) (hfb : f.block? bid = some fb)
    {x : ID} (hx : NB f fb x) (hn : ¬ NilIn (schedNodes f fb).toList x) : x ∈ roots2 f fb := by
  obtain ⟨n, hn', rfl⟩ := hx
  have hd : ((schedNodes f fb).toList.map (·.id)).Nodup :=
    schedNodes_ids (valuesOwn hwf hb hfb) (hwf.valuesNodup _ _ ⟨hb, hfb⟩)
  unfold NilIn at hn
  rw [nodeOf_of_mem hd hn'] at hn
  have hle : n.prio ≤ 2 := by
    obtain ⟨id, -, v, -, -, rfl⟩ := mem_schedNodes.1 hn'
    simp only [prio]; split <;> (try split) <;> omega
  have : ¬ n.prio ≤ 1 := fun hle1 => hn fun m hm => by cases hm; exact hle1
  exact List.mem_map.2 ⟨n, List.mem_filter.2 ⟨hn', by simp only [beq_iff_eq]; omega⟩, rfl⟩

end

theorem chained_of {ce : CheckEnv} {f : Func} {B : Array ID} (hwf : WF ce f)
    (hB : ∀ bid ∈ B, bid ∈ f.blocks) (h : chainedB f B = true) : Chained f (· ∈ B) := by
  intro bid fb hbB hfb x y hx hy hnx hny hxy
  have hb := hB bid hbB
  unfold chainedB at h
  rw [Array.all_eq_true'] at h
  have h := h bid hbB
  rw [hfb] at h
  simp only [List.all_eq_true, List.mem_map, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem] at h
  have hxr := mem_roots2 hwf hb hfb hx hnx
  have hyr := mem_roots2 hwf hb hfb hy hny
  have := h (y, ancOf f fb y) ⟨y, hyr, rfl⟩ (x, ancOf f fb x) ⟨x, hxr, rfl⟩
  rcases this with (he | hm) | hm
  · exact absurd he hxy
  · exact .inl (ancOf_sound hwf hb hfb hy hm)
  · exact .inr (ancOf_sound hwf hb hfb hx hm)

end GoFV.Proof.Dead
