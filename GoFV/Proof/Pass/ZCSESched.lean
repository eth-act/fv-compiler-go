import GoFV.Proof.Pass.ZCSESetup

/-!
# zcse: the target block's schedule

`targetSched`: the `EA g` values of the block (argument-free, so first) followed by the source
schedule without them is a dependency order of the target block, so `schedule g gb` is defined.
`depPres`: a target dependency chain follows every source chain from a root with arguments
(such chains run through values with arguments only, which zcse neither moves nor redirects).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom

variable {tabs : Tables} {f g : Func}

/-! ## Dependency orders -/

theorem topoRem_not_mem_drop {D : ID → List ID} :
    ∀ {o : List ID} {j : Nat} {x : ID}, TopoRem D o → o[j]? = some x → ∀ a ∈ D x, a ∉ o.drop j
  | [], _, _, _, h, _, _ => nomatch h
  | y :: o, 0, x, ⟨h1, _⟩, h, a, ha => by cases h; exact h1 a ha
  | _ :: o, j + 1, x, ⟨_, h2⟩, h, a, ha => by
    simpa using topoRem_not_mem_drop (o := o) h2 (by simpa using h) a ha

theorem topo_of_topoRem {N : ID → Prop} {D : ID → List ID} {o : List ID} (hn : o.Nodup)
    (ht : TopoRem D o) (hm : ∀ x, x ∈ o ↔ N x) : Order.Topo N D o := by
  refine ⟨hn, hm, fun j x hj a ha hNa => ?_⟩
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ((hm a).2 hNa)
  refine ⟨i, ?_, hi⟩
  rcases Nat.lt_or_ge i j with h | h
  · exact h
  · exfalso
    apply topoRem_not_mem_drop ht hj a ha
    have hil : i < o.length := (List.getElem?_eq_some_iff.1 hi).1
    rw [List.mem_iff_getElem?]
    exact ⟨i - j, by rw [List.getElem?_drop, Nat.add_sub_cancel' h]; exact hi⟩

theorem topoRem_filter {D D' : ID → List ID} {p : ID → Bool} :
    ∀ {o : List ID}, TopoRem D o → (∀ x ∈ o, ∀ a ∈ D' x, a ∈ D x ∨ p a = false) →
      TopoRem D' (o.filter p)
  | [], _, _ => trivial
  | x :: o, ⟨h1, h2⟩, h => by
    have ih := topoRem_filter (p := p) h2 fun y hy => h y (List.mem_cons_of_mem _ hy)
    rw [List.filter_cons]
    split
    · refine ⟨fun a ha hm => ?_, ih⟩
      rcases h x List.mem_cons_self a ha with had | hp
      · apply h1 a had
        rcases List.mem_cons.1 hm with rfl | hm
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_filter.1 hm).1
      · rcases List.mem_cons.1 hm with rfl | hm
        · rename_i hpx; rw [hpx] at hp; cases hp
        · rw [(List.mem_filter.1 hm).2] at hp; cases hp
    · exact ih

theorem topoRem_append_nil {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, (∀ x ∈ L1, D x = []) → TopoRem D L2 → TopoRem D (L1 ++ L2)
  | [], _, _, h => h
  | x :: L1, L2, hn, h => ⟨by rw [hn x List.mem_cons_self]; nofun,
      topoRem_append_nil (fun y hy => hn y (List.mem_cons_of_mem _ hy)) h⟩

/-! ## The target schedule -/

/-- The block's values that are `EA g`. -/
def eaList (g : Func) (gb : Block) : List ID := gb.values.toList.filter (entryArgless g)

/-- **The target block has a schedule.** -/
theorem targetSched (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {oS : Array ID}
    (hsched : schedule f fb = some oS) : ∃ oT, schedule g gb = some oT := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hownF hndF hsched
  let p : ID → Bool := fun x => !entryArgless g x
  let L := eaList g gb ++ oS.toList.filter p
  have hnode : ∀ x, NodeIn (schedNodes g gb).toList x ↔ x ∈ gb.values ∧
      ∃ v, g.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownG
  have hmem : ∀ x, x ∈ L ↔ NodeIn (schedNodes g gb).toList x := by
    intro x
    rw [S.nodeT hb hfb hgb, nodeIn_schedNodes hownF, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨hx, hea⟩ := List.mem_filter.1 h
        exact .inr ⟨hea, S.ea_block hea hb hgb (Array.mem_toList_iff.1 hx)⟩
      · obtain ⟨hx, hp⟩ := List.mem_filter.1 h
        exact .inl ⟨(omem x).1 hx, by simpa [p] using hp⟩
    · rintro (⟨h, hea⟩ | ⟨hea, rfl⟩)
      · exact .inr (List.mem_filter.2 ⟨(omem x).2 h, by simpa [p] using hea⟩)
      · obtain ⟨gE, hgE, hxE, -⟩ := ea_iff.1 hea
        rw [S.entry, hgb] at hgE; cases hgE
        exact .inl (List.mem_filter.2 ⟨Array.mem_toList_iff.2 hxE, hea⟩)
  have hnd : L.Nodup := by
    refine List.nodup_append.2 ⟨(hndG.filter _), ond.filter _, fun a ha b hb hab => ?_⟩
    subst hab
    have h1 := (List.mem_filter.1 ha).2
    have h2 := (List.mem_filter.1 hb).2
    simp [p, h1] at h2
  have hargs : ∀ x ∈ oS.toList, ∀ a ∈ argsOf (schedNodes g gb).toList x,
      a ∈ argsF f x ∨ p a = false := by
    intro x hx a ha
    obtain ⟨hxb, fv, hfv, hfn⟩ := (omem x).1 hx
    obtain ⟨gv, hgv, -, hop, -, -, -, hsz, hrel⟩ := S.value hfv
    rw [argsF_of hfv]
    by_cases hxg : NodeIn (schedNodes g gb).toList x
    · obtain ⟨hxgb, -⟩ := (hnode x).1 hxg
      rw [argsOf_schedNodes hownG hndG hxgb hgv (by rw [hop]; exact hfn)] at ha
      obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
      have hk' : gv.args[k]? = some a := by simpa using hk
      have hkf : k < fv.args.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hk').1
      obtain ⟨ga, hga, hr⟩ := hrel k fv.args[k] (by simp [hkf])
      rw [hk'] at hga; cases hga
      rcases hr with rfl | ⟨hea, -⟩
      · exact .inl (by simp)
      · exact .inr (by simp [p, hea])
    · unfold argsOf at ha
      rw [nodeIn_iff] at hxg
      simp only [Ne, Decidable.not_not] at hxg
      rw [hxg] at ha; cases ha
  have hT : Order.Topo (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) L := by
    refine topo_of_topoRem hnd (topoRem_append_nil (fun x hx => ?_) (topoRem_filter otopo hargs))
      hmem
    obtain ⟨hx, hea⟩ := List.mem_filter.1 hx
    obtain ⟨-, -, -, v, hv, hva, hvn⟩ := ea_iff.1 hea
    rw [argsOf_schedNodes hownG hndG (Array.mem_toList_iff.1 hx) hv hvn, hva]
  exact schedule_some (schedNodes_ids hownG hndG) hT

/-- A value of `f` with arguments is not `EA g`. -/
theorem not_ea (S : Setup tabs f g) {x : ID} {fv : Value} (hfv : f.value? x = some fv)
    (hne : fv.args ≠ #[]) : ¬ EA g x := by
  intro hea
  obtain ⟨-, -, -, v, hv, hva, -⟩ := ea_iff.1 hea
  obtain ⟨gv, hgv, -, -, -, -, -, hsz, -⟩ := S.value hfv
  rw [hv] at hgv; cases hgv
  rw [hva] at hsz
  exact hne (Array.eq_empty_of_size_eq_zero (by simpa using hsz.symm))

/-- **Target dependencies on a source root with arguments are kept.** -/
theorem depPres (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb) {r : ID}
    (hra : ∀ fv, f.value? r = some fv → fv.args ≠ #[]) :
    ∀ y, Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) r y →
      Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) r y := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  let DT := Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList)
  have key : ∀ x y, Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList)
      x y → (x = r ∨ DT r x) → (∀ fv, f.value? x = some fv → fv.args ≠ #[]) →
      DT r y ∧ ∀ fv, f.value? y = some fv → fv.args ≠ #[] := by
    intro x y hd
    induction hd with
    | @arg x y hx hy hxy =>
      intro hxr hxa
      obtain ⟨hyb, fy, hfy, hyn⟩ := (nodeIn_schedNodes hownF).1 hy
      rw [argsOf_schedNodes hownF hndF hyb hfy hyn] at hxy
      have hya : fy.args ≠ #[] := fun he => by rw [he] at hxy; cases hxy
      have hyA : ∀ fv, f.value? y = some fv → fv.args ≠ #[] := fun fv hfv => by
        rw [hfy] at hfv; cases hfv; exact hya
      obtain ⟨hxb, fx, hfx, hxn⟩ := (nodeIn_schedNodes hownF).1 hx
      obtain ⟨gy, hgy, -, hop, -, -, -, hsz, hrel⟩ := S.value hfy
      obtain ⟨k, hk⟩ := List.getElem?_of_mem hxy
      have hk' : fy.args[k]? = some x := by simpa using hk
      obtain ⟨ga, hga, hr⟩ := hrel k x hk'
      have hgax : ga = x := by
        rcases hr with h | ⟨-, hs⟩
        · exact h
        · obtain ⟨u, -, hu, -, hua, -⟩ := same_iff.1 hs
          rw [hfx] at hu; cases hu
          exact absurd hua (hxa _ hfx)
      subst hgax
      have hxT : NodeIn (schedNodes g gb).toList ga :=
        (S.nodeT hb hfb hgb).2 (.inl ⟨hx, not_ea S hfx (hxa _ hfx)⟩)
      have hyT : NodeIn (schedNodes g gb).toList y :=
        (S.nodeT hb hfb hgb).2 (.inl ⟨hy, not_ea S hfy hya⟩)
      obtain ⟨hygb, -⟩ := (nodeIn_schedNodes hownG).1 hyT
      have hedge : ga ∈ argsOf (schedNodes g gb).toList y := by
        rw [argsOf_schedNodes hownG hndG hygb hgy (by rw [hop]; exact hyn)]
        exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hga)
      refine ⟨?_, hyA⟩
      rcases hxr with rfl | hd
      · exact .arg hxT hyT hedge
      · exact .trans hd (.arg hxT hyT hedge)
    | trans _ _ ih1 ih2 =>
      intro hxr hxa
      obtain ⟨h1, h2⟩ := ih1 hxr hxa
      exact ih2 (.inr h1) h2
  intro y hd
  exact (key r y hd (.inl rfl) hra).1

end GoFV.Proof.ZCSE
