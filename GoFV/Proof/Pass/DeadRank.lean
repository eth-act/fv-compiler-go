import GoFV.Proof.Pass.DeadBlock

/-!
# Removing dead values keeps the roots' order (#96)

`SubNodes vs vs'`: the nodes `vs'` are some of the nodes `vs`, with the same records (ID,
arguments, priority), closed under arguments. The source order restricted to them is then a
schedule of `vs'` (`schedSpec_restrict`), so by the rank tie-break it lists the non-pure nodes of
`vs'` in the same sequence as any schedule of `vs'` (`sched_transfer`), and a target schedule
reaches before the root `r` only nodes the source reached before `r` (`sched_transfer_sub`, for
any non-pure `r`: a `NilCheck` too). A kept block of `DeadRel` is such a restriction
(`Setup.subNodes`: kept non-`Phi`s keep op and arguments, the arguments of kept values are kept).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof Order

/-- Restricting an order to nodes closed under arguments keeps the waiting property shared by
`PureFirst` and `RankFirst`. -/
theorem waits_filter {α : Type} {N N' : α → Prop} {D D' : α → List α} {P P' : α → α → Prop}
    {o : List α} (hnd : o.Nodup) (p : α → Bool) (hp : ∀ x, p x = true ↔ N' x)
    (hP : ∀ y x, N' y → N' x → P' y x → P y x)
    (hD : ∀ x, N' x → ∀ a ∈ D x, N a → N' a ∧ a ∈ D' x)
    (h : ∀ (k j : Nat) y x, k < j → o[k]? = some y → o[j]? = some x → P y x →
      ∃ a ∈ D x, N a ∧ ∃ i : Nat, k ≤ i ∧ i < j ∧ o[i]? = some a)
    {k j : Nat} {y x : α} (hkj : k < j) (hy : (o.filter p)[k]? = some y)
    (hx : (o.filter p)[j]? = some x) (hyx : P' y x) :
    ∃ a ∈ D' x, N' a ∧ ∃ i : Nat, k ≤ i ∧ i < j ∧ (o.filter p)[i]? = some a := by
  have hndF : (o.filter p).Nodup := hnd.filter _
  have hmy := List.mem_filter.1 (List.mem_of_getElem? hy)
  have hmx := List.mem_filter.1 (List.mem_of_getElem? hx)
  obtain ⟨k0, hk0⟩ := List.getElem?_of_mem hmy.1
  obtain ⟨j0, hj0⟩ := List.getElem?_of_mem hmx.1
  have hkj0 : k0 < j0 :=
    idx_lt_of_before hnd ((before_filter p hmy.2 hmx.2 o).1 ⟨k, j, hkj, hy, hx⟩) hk0 hj0
  obtain ⟨a, ha, hNa, i0, hki0, hij0, hia0⟩ :=
    h k0 j0 y x hkj0 hk0 hj0 (hP y x ((hp y).1 hmy.2) ((hp x).1 hmx.2) hyx)
  obtain ⟨hN'a, ha'⟩ := hD x ((hp x).1 hmx.2) a ha hNa
  have hpa : p a = true := (hp a).2 hN'a
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.mem_filter.2 ⟨List.mem_of_getElem? hia0, hpa⟩)
  refine ⟨a, ha', hN'a, i, ?_,
    idx_lt_of_before hndF ((before_filter p hpa hmx.2 o).2 ⟨i0, j0, hij0, hia0, hj0⟩) hi hx, hi⟩
  rcases Nat.lt_or_ge k0 i0 with hlt | hge
  · exact Nat.le_of_lt
      (idx_lt_of_before hndF ((before_filter p hmy.2 hpa o).2 ⟨k0, i0, hlt, hk0, hia0⟩) hy hi)
  · have he : i0 = k0 := by omega
    rw [he, hk0] at hia0
    cases hia0
    exact Nat.le_of_eq (idx_unique hndF hy hi)

/-- The nodes `vs'` are some of the nodes `vs`, with the same records, closed under arguments. -/
structure SubNodes (vs vs' : List SNode) : Prop where
  distinct : (vs'.map (·.id)).Nodup
  same : ∀ x, NodeIn vs' x → nodeOf vs' x = nodeOf vs x
  closed : ∀ x a, NodeIn vs' x → a ∈ argsOf vs x → NodeIn vs a → NodeIn vs' a

namespace SubNodes

variable {vs vs' : List SNode} (h : SubNodes vs vs') {x : ID}
include h

theorem node (hx : NodeIn vs' x) : NodeIn vs x := by
  have he := h.same x hx
  rw [nodeIn_iff] at hx ⊢; rw [← he]; exact hx

theorem args (hx : NodeIn vs' x) : argsOf vs' x = argsOf vs x := by
  unfold argsOf; rw [h.same x hx]

theorem pure (hx : NodeIn vs' x) : PureIn vs' x ↔ PureIn vs x := by
  unfold PureIn; rw [h.same x hx]

theorem nil (hx : NodeIn vs' x) : NilIn vs' x ↔ NilIn vs x := by
  unfold NilIn; rw [h.same x hx]

theorem np (hx : NodeIn vs' x) : npIn vs' x = npIn vs x := by
  unfold npIn; rw [h.same x hx]

theorem rank {y : ID} (hx : NodeIn vs' x) (hy : NodeIn vs' y) : rankIn vs' x y ↔ rankIn vs x y := by
  unfold rankIn; rw [h.same x hx, h.same y hy]

end SubNodes

/-- **The source schedule restricted to a closed subset of its nodes is a schedule of them.** -/
theorem schedSpec_restrict {vs vs' : List SNode} {o : List ID} (hS : SchedSpec vs o)
    (h : SubNodes vs vs') : SchedSpec vs' (o.filter fun x => vs'.any (·.id == x)) := by
  have hp : ∀ x, (vs'.any (·.id == x)) = true ↔ NodeIn vs' x := fun x => nodeIn_any
  have hD : ∀ x, NodeIn vs' x → ∀ a ∈ argsOf vs x, NodeIn vs a →
      NodeIn vs' a ∧ a ∈ argsOf vs' x :=
    fun x hx a ha hNa => ⟨h.closed x a hx ha hNa, by rw [h.args hx]; exact ha⟩
  have hnd := hS.topo.nodup
  refine ⟨h.distinct, Order.Topo.filter hS.topo _ hp (fun x hx => h.node hx)
    (fun x hx a ha _ => by rw [← h.args hx]; exact ha), ?_, ?_, ?_⟩
  · intro k j y x hkj hy hx hpy hpx
    exact waits_filter (P := fun y x => ¬ PureIn vs y ∧ PureIn vs x)
      (P' := fun y x => ¬ PureIn vs' y ∧ PureIn vs' x) hnd _ hp
      (fun y x hy hx hP => ⟨fun h' => hP.1 ((h.pure hy).2 h'), (h.pure hx).1 hP.2⟩) hD
      (fun k j y x hkj hy hx hP => hS.pureFirst k j y x hkj hy hx hP.1 hP.2) hkj hy hx ⟨hpy, hpx⟩
  · intro k j y x hkj hy hx hpy hpx
    exact waits_filter (P := fun y x => ¬ NilIn vs y ∧ NilIn vs x)
      (P' := fun y x => ¬ NilIn vs' y ∧ NilIn vs' x) hnd _ hp
      (fun y x hy hx hP => ⟨fun h' => hP.1 ((h.nil hy).2 h'), (h.nil hx).1 hP.2⟩) hD
      (fun k j y x hkj hy hx hP => hS.nilFirst k j y x hkj hy hx hP.1 hP.2) hkj hy hx ⟨hpy, hpx⟩
  · intro k j y x hkj hy hx hny hnx hl
    exact waits_filter (P := fun y x => npIn vs y = true ∧ npIn vs x = true ∧ rankIn vs x y)
      (P' := fun y x => npIn vs' y = true ∧ npIn vs' x = true ∧ rankIn vs' x y) hnd _ hp
      (fun y x hy hx hP => ⟨h.np hy ▸ hP.1, h.np hx ▸ hP.2.1, (h.rank hx hy).1 hP.2.2⟩) hD
      (fun k j y x hkj hy hx hP => hS.rankFirst k j y x hkj hy hx hP.1 hP.2.1 hP.2.2) hkj hy hx
      ⟨hny, hnx, hl⟩

theorem sameNP_refl (vs : List SNode) : SameNP vs vs := fun x =>
  ⟨rfl, fun hx => by
    obtain ⟨n, hn⟩ := Option.ne_none_iff_exists'.1 (nodeIn_iff.1 (npIn_iff.1 hx).1)
    exact ⟨n, n, hn, hn, rfl⟩⟩

/-- **The panic transfer when the target keeps a closed subset of the nodes.** If the source
schedule `o` reaches the target's non-pure node `r` at position `k` and the target schedule `o'`
lists it at `k'`, everything `o'` lists before `r`, `o` lists before `r`. -/
theorem sched_transfer_sub {vs vs' : List SNode} {o o' : List ID} (hS : SchedSpec vs o)
    (hT : SchedSpec vs' o') (h : SubNodes vs vs') {r : ID} {k k' : Nat} (hr : o[k]? = some r)
    (hr' : o'[k']? = some r) (hrp : npIn vs' r = true) :
    ∀ j y, j < k' → o'[j]? = some y → ∃ i < k, o[i]? = some y := by
  intro j y hj hy
  have hp : ∀ x, (vs'.any (·.id == x)) = true ↔ NodeIn vs' x := fun x => nodeIn_any
  have hpr := (hp r).2 (npIn_iff.1 hrp).1
  obtain ⟨kK, hkK⟩ := List.getElem?_of_mem
    ((List.mem_filter (p := fun x => vs'.any (·.id == x))).2 ⟨List.mem_of_getElem? hr, hpr⟩)
  have hNy : NodeIn vs' y := (hT.topo.mem y).1 (List.mem_of_getElem? hy)
  obtain ⟨i, hi, hiy⟩ := sched_transfer (schedSpec_restrict hS h) hT (sameNP_refl vs')
    (fun _ _ _ _ => Iff.rfl) hkK hr' hrp (fun a y ha hy hay _ => ⟨ha, .arg ha hy hay⟩)
    j y hj hy hNy
  obtain ⟨i0, hi0⟩ := List.getElem?_of_mem (List.mem_filter.1 (List.mem_of_getElem? hiy)).1
  exact ⟨i0, idx_lt_of_before hS.topo.nodup ((before_filter (fun x => vs'.any (·.id == x))
    ((hp y).2 hNy) hpr o).1 ⟨i, kK, hi, hiy, hkK⟩) hi0 hr, hi0⟩

theorem dep_left {α : Type} {N : α → Prop} {D : α → List α} {x y : α} :
    Order.Dep N D x y → N x
  | .arg hx _ _ => hx
  | .trans h _ => dep_left h

variable {f g : Func} {K : ID → Prop}

/-- **A kept block's nodes are a closed subset of the source block's.** -/
theorem Setup.subNodes (S : Setup f g K) {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) :
    SubNodes (schedNodes f fb).toList (schedNodes g gb).toList := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, hbf, -, -, -⟩ := S.blockFacts hb hgb hfb
  have hbm := S.rel.sub bid hb
  have hownF := valuesOwn hwf hbf hfb
  have hownG := valuesOwn hwg hbm hgb
  have hndF : fb.values.toList.Nodup := hwf.valuesNodup _ _ ⟨hbf, hfb⟩
  have hndG : gb.values.toList.Nodup := hwg.valuesNodup _ _ ⟨hbm, hgb⟩
  refine ⟨schedNodes_ids hownG hndG, fun x hx => ?_, fun x a hx hax hNa => ?_⟩
  · obtain ⟨hxg, gv, hgv, hgn⟩ := (nodeIn_schedNodes hownG).1 hx
    obtain ⟨gv', fv, hgv', hfv, -, -, hxf, -, hph, hsame⟩ := S.value hb hgb hfb hxg
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨hop, -, -, hargs⟩ := hsame hgn
    rw [CopyElim.nodeOf_schedNodes hownG hndG hxg hgv hgn,
      CopyElim.nodeOf_schedNodes hownF hndF hxf hfv (fun h => hgn (hph.2 h)), hop, hargs]
  · have hxS := ((S.nodeT hb hgb hfb).1 hx).2
    exact dep_left (S.depT hb hgb hfb (.arg hNa hxS hax) hx)

end GoFV.Proof.Dead
