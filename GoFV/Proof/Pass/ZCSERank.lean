import GoFV.Proof.Pass.ZCSESched
import GoFV.Proof.Pass.CopyElimRank

variable [GoFV.SSA.Sem.Addrs]

/-!
# zcse keeps the roots' order (#96)

For a block of `f`, the source and target schedules see the same non-pure nodes with the same
priorities (`sameNP`: zcse moves only pure values, the roots of `g`'s entry being `f`'s,
`rootEntry`), the same dependencies between them (`depPres`; `depBack`: a target chain from a
`Kept` node never passes a redirected argument, as only pure argument-free ones are, `replPure`),
and every argument `a` of a source node `y` `Feeds` it in the target (`feeds`: a kept `a` stays
`y`'s argument; any other is pure and argument-free). `schedTransfer`: so `sched_transfer'`
applies, and a target prefix before a root lists only source nodes the source listed before it.
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom Order

variable {tabs : Tables} {f g : Func}

/-- Non-pure is root. -/
theorem prio_ne_zero {op : Op} : prio op ≠ 0 ↔ isRoot op = true := by
  unfold prio
  by_cases h1 : op.nilCheck = true
  · have h2 : isRoot op = true := by unfold isRoot; simp [h1]
    simp [h1, h2]
  · by_cases h2 : isRoot op = true <;> simp [h1, h2]

/-- The non-pure nodes of a block. -/
theorem npIn_sched {f : Func} {b : Block} (hown : ValuesOwn f b) (hnd : b.values.toList.Nodup)
    {x : ID} : npIn (schedNodes f b).toList x = true ↔
      x ∈ b.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi ∧ prio v.op ≠ 0 := by
  constructor
  · intro h
    obtain ⟨hx, v, hv, hp⟩ := (nodeIn_schedNodes hown).1 (npIn_iff.1 h).1
    refine ⟨hx, v, hv, hp, ?_⟩
    unfold npIn at h
    rw [CopyElim.nodeOf_schedNodes hown hnd hx hv hp] at h
    simpa using h
  · rintro ⟨hx, v, hv, hp, hpr⟩
    unfold npIn
    rw [CopyElim.nodeOf_schedNodes hown hnd hx hv hp]
    simpa using hpr

section

variable (S : Setup tabs f g) {bid : ID} (hb : bid ∈ f.blocks) {fb gb : Block}
  (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
include S hb hfb hgb

/-- **The non-pure nodes of a block and their priorities are the same in the target.** -/
theorem sameNP : SameNP (schedNodes f fb).toList (schedNodes g gb).toList := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG : gb.values.toList.Nodup := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  obtain ⟨gb', hgb', -, -, -, -, -, -, hgf⟩ := S.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  have hST : ∀ x, npIn (schedNodes f fb).toList x = true →
      npIn (schedNodes g gb).toList x = true := by
    intro x h
    obtain ⟨hx, v, hv, hp, hpr⟩ := (npIn_sched hownF hndF).1 h
    have hK : Kept f x := fun fv hfv => by rw [hv] at hfv; cases hfv; exact .inr (prio_ne_zero.1 hpr)
    obtain ⟨hxg, gv, hgv, hgp⟩ := (nodeIn_schedNodes hownG).1
      (nodeT_kept S hb hfb hgb ((nodeIn_schedNodes hownF).2 ⟨hx, v, hv, hp⟩) hK)
    obtain ⟨gv', hgv', -, hop, -⟩ := S.value hv
    rw [hgv] at hgv'; cases hgv'
    exact (npIn_sched hownG hndG).2 ⟨hxg, gv, hgv, hgp, by rw [hop]; exact hpr⟩
  have hTS : ∀ x, npIn (schedNodes g gb).toList x = true →
      npIn (schedNodes f fb).toList x = true := by
    intro x h
    obtain ⟨hxg, gv, hgv, hgp, hpr⟩ := (npIn_sched hownG hndG).1 h
    have hxf : x ∈ fb.values := by
      rcases hgf x hxg with h | hea
      · exact h
      · obtain ⟨fE, hfE, hxE⟩ := S.rel.rootEntry x hea gv hgv (prio_ne_zero.1 hpr)
        have hbe := S.ea_block hea hb hgb hxg
        subst hbe
        rw [hfb] at hfE; cases hfE; exact hxE
    obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hb, hfb⟩ x hxf
    obtain ⟨gv', hgv', -, hop, -⟩ := S.value hfv
    rw [hgv] at hgv'; cases hgv'
    exact (npIn_sched hownF hndF).2 ⟨hxf, fv, hfv, by rw [← hop]; exact hgp,
      by rw [← hop]; exact hpr⟩
  intro x
  refine ⟨Bool.eq_iff_iff.2 ⟨hTS x, hST x⟩, fun h => ?_⟩
  obtain ⟨hx, v, hv, hp, -⟩ := (npIn_sched hownF hndF).1 h
  obtain ⟨hxg, gv, hgv, -, -⟩ := (npIn_sched hownG hndG).1 (hST x h)
  obtain ⟨gv', hgv', -, hop, -⟩ := S.value hv
  rw [hgv] at hgv'; cases hgv'
  refine ⟨_, _, CopyElim.nodeOf_schedNodes hownF hndF hx hv hp,
    CopyElim.nodeOf_schedNodes hownG hndG hxg hgv (by rw [hop]; exact hp), by simp [hop]⟩

/-- **Target dependencies from a kept source node are source dependencies.** -/
theorem depBack {u v : ID}
    (hd : Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) u v) :
    NodeIn (schedNodes f fb).toList u → Kept f u →
      Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) u v ∧
        NodeIn (schedNodes f fb).toList v ∧ Kept f v := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  induction hd with
  | @arg a y ha hy hay =>
    intro haS hak
    obtain ⟨hygb, gy, hgy, hgyn⟩ := (nodeIn_schedNodes hownG).1 hy
    rw [argsOf_schedNodes hownG hndG hygb hgy hgyn] at hay
    have hgya : gy.args ≠ #[] := fun he => by rw [he] at hay; cases hay
    have hyEA : ¬ EA g y := fun hea => by
      obtain ⟨-, -, -, v, hv, hva, -⟩ := ea_iff.1 hea
      rw [hgy] at hv; cases hv; exact hgya hva
    have hyS : NodeIn (schedNodes f fb).toList y :=
      (((S.nodeT hb hfb hgb).1 hy).resolve_right fun h => hyEA h.1).1
    obtain ⟨hyb, fy, hfy, hfyn⟩ := (nodeIn_schedNodes hownF).1 hyS
    obtain ⟨gy', hgy', -, -, -, -, -, hsz, hrel⟩ := S.value hfy
    rw [hgy] at hgy'; cases hgy'
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hay
    have hk' : gy.args[k]? = some a := by simpa using hk
    have hkf : k < fy.args.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hk').1
    have hfk : fy.args[k]? = some fy.args[k] := by simp [hkf]
    obtain ⟨ga, hga, hr⟩ := hrel k fy.args[k] hfk
    rw [hk'] at hga; cases hga
    have hfa : fy.args[k] = a := by
      rcases hr with h | ⟨-, hs⟩
      · exact h.symm
      · refine Classical.byContradiction fun hne => ?_
        obtain ⟨-, w, -, hw, -, -, hwa, -, huw, -⟩ := same_iff.1 hs
        have hroot := S.rel.replPure y fy gy k _ a hfy hgy hfk hk' (Ne.symm hne) w hw
        obtain ⟨-, va, hva, -⟩ := (nodeIn_schedNodes hownF).1 haS
        obtain ⟨w', hw', -, hop, -, -, -, hsz', -⟩ := S.value hva
        rw [hw] at hw'; cases hw'
        rcases hak va hva with h | h
        · exact h (Array.eq_empty_of_size_eq_zero (by rw [← hsz', hwa]; rfl))
        · rw [← hop, hroot] at h; cases h
    refine ⟨.arg haS hyS ?_, hyS, fun fv hfv => ?_⟩
    · rw [argsOf_schedNodes hownF hndF hyb hfy hfyn, ← hfa]; simp
    · rw [hfy] at hfv; cases hfv
      exact .inl fun he => by rw [he] at hkf; cases hkf
  | trans _ _ ih1 ih2 =>
    intro hu hk
    obtain ⟨h1, hw, hwk⟩ := ih1 hu hk
    obtain ⟨h2, hv, hvk⟩ := ih2 hw hwk
    exact ⟨.trans h1 h2, hv, hvk⟩

/-- **Every argument of a source node feeds it in the target**: a kept argument stays the
node's argument; any other is pure and argument-free. -/
theorem feeds {a y : ID} (haN : NodeIn (schedNodes f fb).toList a)
    (hyN : NodeIn (schedNodes f fb).toList y) (hay : a ∈ argsOf (schedNodes f fb).toList y)
    (hyT : NodeIn (schedNodes g gb).toList y) :
    Feeds (NodeIn (schedNodes f fb).toList) (NodeIn (schedNodes g gb).toList)
      (argsOf (schedNodes f fb).toList) (argsOf (schedNodes g gb).toList)
      (PureIn (schedNodes f fb).toList) y a := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hb
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  have hownG := valuesOwn hwg hbg hgb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgb⟩
  obtain ⟨hab, fa, hfa, hfan⟩ := (nodeIn_schedNodes hownF).1 haN
  by_cases hK : Kept f a
  · obtain ⟨hyb, fy, hfy, hfyn⟩ := (nodeIn_schedNodes hownF).1 hyN
    rw [argsOf_schedNodes hownF hndF hyb hfy hfyn] at hay
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hay
    have hk' : fy.args[k]? = some a := by simpa using hk
    obtain ⟨gy, hgy, -, hop, -, -, -, -, hrel⟩ := S.value hfy
    obtain ⟨ga, hga, hr⟩ := hrel k a hk'
    have hga' : ga = a := by
      rcases hr with h | ⟨-, hs⟩
      · exact h
      · refine Classical.byContradiction fun hne => ?_
        obtain ⟨u, w, hu, hw, hua, -, -, -, huw, -⟩ := same_iff.1 hs
        have hroot := S.rel.replPure y fy gy k a ga hfy hgy hk' hga hne w hw
        rw [hfa] at hu; cases hu
        rcases hK _ hfa with h | h
        · exact h hua
        · rw [huw, hroot] at h; cases h
    subst hga'
    have haT := nodeT_kept S hb hfb hgb haN hK
    obtain ⟨hygb, -⟩ := (nodeIn_schedNodes hownG).1 hyT
    refine .direct haT (.arg haT hyT ?_)
    rw [argsOf_schedNodes hownG hndG hygb hgy (by rw [hop]; exact hfyn)]
    exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hga)
  · have hargs : fa.args = #[] := Classical.byContradiction fun h =>
      hK fun fv hfv => by rw [hfa] at hfv; cases hfv; exact .inl h
    have hroot : isRoot fa.op = false := by
      cases h : isRoot fa.op
      · rfl
      · exact absurd (fun fv hfv => by rw [hfa] at hfv; cases hfv; exact .inr h) hK
    refine .through ?_ fun b hb' _ => ?_
    · intro n hn
      rw [CopyElim.nodeOf_schedNodes hownF hndF hab hfa hfan] at hn
      cases hn
      show prio fa.op = 0
      exact Classical.byContradiction fun h => by rw [prio_ne_zero.1 h] at hroot; cases hroot
    · rw [argsOf_schedNodes hownF hndF hab hfa hfan, hargs] at hb'; cases hb'

/-- **A target prefix before a non-pure node lists only source nodes the source lists before
it** (`sched_transfer'`). -/
theorem schedTransfer {oS oT : Array ID} (hso : schedule f fb = some oS)
    (hoT : schedule g gb = some oT) {r : ID} {k k' : Nat} (hk : oS.toList[k]? = some r)
    (hk' : oT.toList[k']? = some r) (hrp : npIn (schedNodes f fb).toList r = true) :
    ∀ j y, j < k' → oT.toList[j]? = some y → NodeIn (schedNodes f fb).toList y →
      ∃ i < k, oS.toList[i]? = some y := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hownF := valuesOwn hwf hb hfb
  have hndF := hwf.valuesNodup _ _ ⟨hb, hfb⟩
  refine sched_transfer' (schedule_spec hso) (schedule_spec hoT) (sameNP S hb hfb hgb)
    (fun x y hx _ => ?_) hk hk' hrp
    (fun a y ha hy hay hyT => feeds S hb hfb hgb ha hy hay hyT)
  obtain ⟨-, v, hv, -, hpr⟩ := (npIn_sched hownF hndF).1 hx
  have hxK : Kept f x := fun fv hfv => by
    rw [hv] at hfv; cases hfv; exact .inr (prio_ne_zero.1 hpr)
  exact ⟨depPres S hb hfb hgb hxK y,
    fun hd => (depBack S hb hfb hgb hd (npIn_iff.1 hx).1 hxK).1⟩

end

end GoFV.Proof.ZCSE
