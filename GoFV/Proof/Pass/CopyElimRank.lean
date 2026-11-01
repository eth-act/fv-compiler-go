import GoFV.Proof.Pass.CopyElimSched

/-!
# copyelim keeps the roots' order (#96)

For a tree block, the source and target schedules see the same non-pure nodes with the same
priorities (`sameNP_copy`), every target dependency between source nodes is a source
dependency (`depBack`: a target edge `a → x` either was a source edge or bypasses a chain of
source copies of `a`; former `Phi`s are never reached, their argument lies outside the block),
and every argument `a` of a source node `y` `Feeds` it in the target (`feedsOf`: `a` itself, or
the source of the copy chain starting at `a`). With `depPres` these are the hypotheses of
`sched_transfer'`.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom Order

variable {tabs : Tables} {f g : Func}

/-- The schedule node of a non-`Phi` value of the block. -/
theorem nodeOf_schedNodes {f : Func} {b : Block} (hown : ValuesOwn f b)
    (hnd : b.values.toList.Nodup) {x : ID} {v : Value} (hx : x ∈ b.values)
    (hv : f.value? x = some v) (hp : v.op ≠ .Phi) :
    nodeOf (schedNodes f b).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hvid⟩ := hown x hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f b).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hp, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids hown hnd) hm
  rw [hvid] at this; exact this

/-- A value that is not a node has no schedule node. -/
theorem nodeOf_none {vs : List SNode} {x : ID} (h : ¬ NodeIn vs x) : nodeOf vs x = none := by
  rw [nodeIn_iff] at h; exact Classical.byContradiction h

theorem prio_copy : prio .Copy = 0 := rfl

section

variable (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
  (hfb : f.block? bid = some fb) {gb : Block} (hgbb : g.block? bid = some gb)
  (hvals : gb.values = fb.values)
include S hbt hfb hgbb hvals

/-- **The non-pure nodes of a tree block and their priorities are the same in the target.** -/
theorem sameNP_copy : SameNP (schedNodes f fb).toList (schedNodes g gb).toList := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hndG' : gb.values.toList.Nodup := hndG
  intro x
  by_cases hx : x ∈ fb.values
  · obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hx
    have hxg : x ∈ gb.values := by rw [hvals]; exact hx
    by_cases hph : fv.op = .Phi
    · have hnS : nodeOf (schedNodes f fb).toList x = none := nodeOf_none fun hn => by
        obtain ⟨-, v, hv, hne⟩ := (nodeIn_schedNodes hownF).1 hn
        rw [hfv] at hv; cases hv; exact hne hph
      have hT : npIn (schedNodes g gb).toList x = false := by
        unfold npIn
        cases hrel with
        | same hop =>
          rw [nodeOf_none fun hn => by
            obtain ⟨-, v, hv, hne⟩ := (nodeIn_schedNodes hownG).1 hn
            rw [hgv] at hv; cases hv; exact hne (hop.trans hph)]
        | phi _ _ hcop =>
          rw [nodeOf_schedNodes hownG hndG' hxg hgv (by rw [hcop]; decide), hcop]; rfl
        | empty hzz => exact absurd hzz hz
      refine ⟨by rw [hT]; unfold npIn; rw [hnS], fun h => ?_⟩
      unfold npIn at h; rw [hnS] at h; cases h
    · have hop : gv.op = fv.op := by
        cases hrel with
        | same hop => exact hop
        | phi _ hp => exact absurd hp hph
        | empty hzz => exact absurd hzz hz
      have hgph : gv.op ≠ .Phi := by rw [hop]; exact hph
      have hnS := nodeOf_schedNodes hownF hndF hx hfv hph
      have hnT := nodeOf_schedNodes hownG hndG' hxg hgv hgph
      refine ⟨by unfold npIn; rw [hnS, hnT, hop], fun _ => ⟨_, _, hnS, hnT, by simp [hop]⟩⟩
  · have hnS : nodeOf (schedNodes f fb).toList x = none := nodeOf_none fun hn =>
      hx ((nodeIn_schedNodes hownF).1 hn).1
    have hnT : nodeOf (schedNodes g gb).toList x = none := nodeOf_none fun hn =>
      hx (by rw [← hvals]; exact ((nodeIn_schedNodes hownG).1 hn).1)
    refine ⟨by unfold npIn; rw [hnS, hnT], fun h => ?_⟩
    unfold npIn at h; rw [hnS] at h; cases h

/-- A source node of the block is a target node. -/
theorem nodeT_of_nodeS {x : ID} (hx : NodeIn (schedNodes f fb).toList x) :
    NodeIn (schedNodes g gb).toList x := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  obtain ⟨hxb, fv, hfv, hne⟩ := (nodeIn_schedNodes (valuesOwn hwf hbt.1 hfb)).1 hx
  obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hxb
  rw [hfv] at hfv'; cases hfv'
  exact (nodeIn_schedNodes (valuesOwn hwg hbg hgbb)).2 ⟨by rw [hvals]; exact hxb, gv, hgv,
    fun hp => hne (valRel_phi hrel hz hp)⟩

end

section

variable (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
  (hfb : f.block? bid = some fb)
  (hpe : ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry)
  {oS : Array ID} (hsched : schedule f fb = some oS)
include S hbt hfb hpe hsched

/-- A target copy of the block, listed in the source schedule, of a value `a` of the block that
is a target node: `a` is a former `Phi`, or the source copy depends on `a`. -/
theorem copyDep :
    ∀ (k : Nat) (y : ID) (gy : Value) (a : ID), oS.toList[k]? = some y → g.value? y = some gy →
      gy.op = .Copy → gy.args = #[a] → a ∈ fb.values →
      (∃ ga, g.value? a = some ga ∧ ga.op ≠ .Phi) →
      a ∈ formerPhis f g fb ∨
        Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) a y := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨-, otopo, omem⟩ := schedule_topo hownF hndF hsched
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro y gy a hk hgy hop hargs hab han
  obtain ⟨hyb, fv, hfv, hnph⟩ := (omem y).1 (List.mem_of_getElem? hk)
  obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hyb
  rw [hfv] at hfv'; cases hfv'
  rw [hgy] at hgv; cases hgv
  obtain ⟨-, fa, hfargs, hra⟩ := copyArg hrel hnph hz hop hargs
  have hyN : NodeIn (schedNodes f fb).toList y := (nodeIn_schedNodes hownF).2 ⟨hyb, fv, hfv, hnph⟩
  have hargsY : argsOf (schedNodes f fb).toList y = [fa] := by
    rw [argsOf_schedNodes hownF hndF hyb hfv hnph, hfargs]
  have hfaU : Anc (make f) (blockOf f fa) bid :=
    uses S.cf hbt.1 hfb hbt.2 hyb hfv hnph (a := fa) (by rw [hfargs]; simp)
  have hfal : Listed f fa :=
    hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hyb, hfv⟩ fa (by rw [hfargs]; simp)
  rcases hra with rfl | ⟨ufa, hufa, hopa, hargsa⟩
  · by_cases hph : ∃ v, f.value? fa = some v ∧ v.op = .Phi
    · exact .inl (mem_formerPhis.2 ⟨hab, hph, han⟩)
    · obtain ⟨v, -, hv, -⟩ := S.value hbt hfb hab
      have haN : NodeIn (schedNodes f fb).toList fa :=
        (nodeIn_schedNodes hownF).2 ⟨hab, v, hv, fun hp => hph ⟨v, hv, hp⟩⟩
      exact .inr (.arg haN hyN (by rw [hargsY]; simp))
  · by_cases hcase : blockOf f fa ≠ bid ∨ ∃ v, f.value? fa = some v ∧ v.op = .Phi
    · exact absurd hab (copyArgOut S hbt hfb hpe hfal hfaU hufa hopa hargsa hcase)
    · have hfab : blockOf f fa = bid := Classical.byContradiction fun hne => hcase (.inl hne)
      obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.used hfal hfaU
      rw [hfab] at hbo; subst hbo
      rw [hfb] at hfb'; cases hfb'
      obtain ⟨vfa, -, hvfa, -⟩ := S.value hbt hfb hx'
      have hfaN' : vfa.op ≠ .Phi := fun hp => hcase (.inr ⟨vfa, hvfa, hp⟩)
      have hfaN : NodeIn (schedNodes f fb).toList fa :=
        (nodeIn_schedNodes hownF).2 ⟨hx', vfa, hvfa, hfaN'⟩
      obtain ⟨j', hj', hjfa⟩ := topoRem_before otopo hk (by rw [argsF_of hfv, hfargs]; simp)
        ((omem fa).2 ⟨hx', vfa, hvfa, hfaN'⟩)
      have hedge : Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) fa y :=
        .arg hfaN hyN (by rw [hargsY]; simp)
      rcases ih j' hj' fa ufa a hjfa hufa hopa hargsa hab han with h | h
      · exact .inl h
      · exact .inr (.trans h hedge)

/-- A target edge `a → x` inside the block: `x` is a source node, and `a` is a former `Phi` or
`x` depends on `a` in the source. -/
theorem edgeBack {gb : Block} (hgbb : g.block? bid = some gb) (hvals : gb.values = fb.values)
    {a x : ID} (ha : NodeIn (schedNodes g gb).toList a) (hx : NodeIn (schedNodes g gb).toList x)
    (hax : a ∈ argsOf (schedNodes g gb).toList x) :
    NodeIn (schedNodes f fb).toList x ∧ (a ∈ formerPhis f g fb ∨
      Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) a x) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  obtain ⟨-, otopo, omem⟩ := schedule_topo hownF hndF hsched
  obtain ⟨hxbG, gv, hgv, hgn⟩ := (nodeIn_schedNodes hownG).1 hx
  have hxb : x ∈ fb.values := by rw [← hvals]; exact hxbG
  obtain ⟨habG, hagn⟩ := (nodeIn_schedNodes hownG).1 ha
  have hab : a ∈ fb.values := by rw [← hvals]; exact habG
  have hagb := blockOf_g S hbt hfb hab
  rw [argsOf_schedNodes hownG hndG hxbG hgv hgn] at hax
  obtain ⟨fv, gv', hfv, hgv', -, -, -, -, hrel, hz⟩ := S.value hbt hfb hxb
  rw [hgv] at hgv'; cases hgv'
  cases hrel with
  | phi w hph hcop hw hr =>
    rw [hw] at hax; simp at hax; subst hax
    exact absurd hagb (S.phiOut hbt (hpe x hxb fv hfv hph) hfb hxb hfv hgv hph hcop hw hr).2
  | empty hzz => exact absurd hzz hz
  | same hop _ _ hsz hargs' =>
    have hnph : fv.op ≠ .Phi := by rw [← hop]; exact hgn
    have hxN : NodeIn (schedNodes f fb).toList x := (nodeIn_schedNodes hownF).2 ⟨hxb, fv, hfv, hnph⟩
    refine ⟨hxN, ?_⟩
    have hargsX := argsOf_schedNodes hownF hndF hxb hfv hnph
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hax
    have hk' : gv.args[k]? = some a := by simpa using hk
    have hkf : k < fv.args.size := by rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hk').1
    obtain ⟨w0, hw0, hr0⟩ := hargs' k fv.args[k] (by simp [hkf])
    rw [hk'] at hw0; cases hw0
    have hfaA : fv.args[k] ∈ argsOf (schedNodes f fb).toList x := by rw [hargsX]; simp
    have hfaU : Anc (make f) (blockOf f fv.args[k]) bid :=
      uses S.cf hbt.1 hfb hbt.2 hxb hfv hnph (Array.getElem_mem hkf)
    have hfal : Listed f fv.args[k] :=
      hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hxb, hfv⟩ _ (Array.getElem_mem hkf)
    rcases hr0 with hfa | ⟨ufa, hufa, hopa, hargsa⟩
    · by_cases hph : ∃ v, f.value? a = some v ∧ v.op = .Phi
      · exact .inl (mem_formerPhis.2 ⟨hab, hph, hagn⟩)
      · obtain ⟨v, -, hv, -⟩ := S.value hbt hfb hab
        have haN : NodeIn (schedNodes f fb).toList a :=
          (nodeIn_schedNodes hownF).2 ⟨hab, v, hv, fun hp => hph ⟨v, hv, hp⟩⟩
        exact .inr (.arg haN hxN (hfa ▸ hfaA))
    · by_cases hcase : blockOf f fv.args[k] ≠ bid ∨ ∃ v, f.value? fv.args[k] = some v ∧ v.op = .Phi
      · exact absurd hab (copyArgOut S hbt hfb hpe hfal hfaU hufa hopa hargsa hcase)
      · have hfab : blockOf f fv.args[k] = bid :=
          Classical.byContradiction fun hne => hcase (.inl hne)
        obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.used hfal hfaU
        rw [hfab] at hbo; subst hbo
        rw [hfb] at hfb'; cases hfb'
        obtain ⟨vfa, -, hvfa, -⟩ := S.value hbt hfb hx'
        have hfaN' : vfa.op ≠ .Phi := fun hp => hcase (.inr ⟨vfa, hvfa, hp⟩)
        have hfaN : NodeIn (schedNodes f fb).toList fv.args[k] :=
          (nodeIn_schedNodes hownF).2 ⟨hx', vfa, hvfa, hfaN'⟩
        obtain ⟨j', hjfa⟩ := List.getElem?_of_mem ((omem _).2 ⟨hx', vfa, hvfa, hfaN'⟩)
        rcases copyDep S hbt hfb hpe hsched j' _ ufa a hjfa hufa hopa hargsa hab hagn with h | h
        · exact .inl h
        · exact .inr (.trans h (.arg hfaN hxN hfaA))

/-- **Target dependencies from a source node are source dependencies.** -/
theorem depBack {gb : Block} (hgbb : g.block? bid = some gb) (hvals : gb.values = fb.values)
    {u v : ID} (hd : Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) u v) :
    NodeIn (schedNodes f fb).toList u →
      Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) u v ∧
        NodeIn (schedNodes f fb).toList v := by
  induction hd with
  | @arg a x ha hx hax =>
    intro haS
    obtain ⟨hxS, h⟩ := edgeBack S hbt hfb hpe hsched hgbb hvals ha hx hax
    refine ⟨?_, hxS⟩
    rcases h with h | h
    · exfalso
      obtain ⟨ce, hwf⟩ := S.wf
      obtain ⟨-, ⟨fv, hfv, hph⟩, -⟩ := mem_formerPhis.1 h
      obtain ⟨-, v, hv, hne⟩ := (nodeIn_schedNodes (valuesOwn hwf hbt.1 hfb)).1 haS
      rw [hfv] at hv; cases hv; exact hne hph
    · exact h
  | trans _ _ ih1 ih2 =>
    intro huS
    obtain ⟨h1, hwS⟩ := ih1 huS
    obtain ⟨h2, hvS⟩ := ih2 hwS
    exact ⟨.trans h1 h2, hvS⟩

omit hpe in
/-- **Every argument of a source node feeds it in the target**: the argument itself, or through
the source copies whose target replacement the target node uses. -/
theorem feedsOf {gb : Block} (hgbb : g.block? bid = some gb) (hvals : gb.values = fb.values)
    {y w : ID} (hyT : NodeIn (schedNodes g gb).toList y)
    (hw : w ∈ argsOf (schedNodes g gb).toList y) :
    ∀ (k : Nat) (a : ID), oS.toList[k]? = some a → ArgRel g a w →
      Feeds (NodeIn (schedNodes f fb).toList) (NodeIn (schedNodes g gb).toList)
        (argsOf (schedNodes f fb).toList) (argsOf (schedNodes g gb).toList)
        (PureIn (schedNodes f fb).toList) y a := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hownF := valuesOwn hwf hbt.1 hfb
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨-, otopo, omem⟩ := schedule_topo hownF hndF hsched
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro a hk hr
  obtain ⟨hab, fv, hfv, hnph⟩ := (omem a).1 (List.mem_of_getElem? hk)
  have haN : NodeIn (schedNodes f fb).toList a := (nodeIn_schedNodes hownF).2 ⟨hab, fv, hfv, hnph⟩
  rcases hr with rfl | ⟨u, hu, hop, hargs⟩
  · have haT := nodeT_of_nodeS S hbt hfb hgbb hvals haN
    exact .direct haT (.arg haT hyT hw)
  · obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hab
    rw [hfv] at hfv'; cases hfv'
    rw [hu] at hgv; cases hgv
    obtain ⟨hcop, fa, hfargs, hra⟩ := copyArg hrel hnph hz hop hargs
    have hpure : PureIn (schedNodes f fb).toList a := by
      intro n hn
      rw [nodeOf_schedNodes hownF hndF hab hfv hnph] at hn
      cases hn; rw [hcop]; rfl
    refine .through hpure fun b hb hbN => ?_
    rw [argsOf_schedNodes hownF hndF hab hfv hnph, hfargs] at hb
    simp at hb; subst hb
    obtain ⟨hbb, vb, hvb, hbn⟩ := (nodeIn_schedNodes hownF).1 hbN
    obtain ⟨j, hj, hjb⟩ := topoRem_before otopo hk (by rw [argsF_of hfv, hfargs]; simp)
      ((omem _).2 ⟨hbb, vb, hvb, hbn⟩)
    exact ih j hj _ hjb hra

end

end GoFV.Proof.CopyElim
