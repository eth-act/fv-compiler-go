import GoFV.Proof.Pass.CopyElimBlock

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim: the target block has a schedule

The target's non-`Phi` values of a tree block are the source's (`oS`) plus the `Phi`s that
became copies (`formerPhis`), and every target dependency inside the block is a source
dependency chain: so `formerPhis ++ oS` is a dependency order of the target block and
`schedule g gb` is defined (`schedule_some`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {tabs : Tables} {f g : Func}

/-- The `Phi`s of the block that are not `Phi`s in `g`. -/
def formerPhis (f g : Func) (b : Block) : List ID :=
  b.values.toList.filter fun z =>
    (f.value? z).any (·.op == .Phi) && (g.value? z).any (·.op != .Phi)

theorem mem_formerPhis {b : Block} {z : ID} :
    z ∈ formerPhis f g b ↔ z ∈ b.values ∧ (∃ fv, f.value? z = some fv ∧ fv.op = .Phi) ∧
      ∃ gv, g.value? z = some gv ∧ gv.op ≠ .Phi := by
  unfold formerPhis
  simp only [List.mem_filter, Array.mem_toList_iff, Bool.and_eq_true, Option.any_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq]

/-- The target value of a non-`Phi` value of a tree block is not a `Phi`; of a `Phi` that stays
a `Phi`, a `Phi`. -/
theorem valRel_phi {fv gv : Value} (hrel : ValRel tabs g fv gv) :
    (gv.op = .Phi → fv.op = .Phi) := by
  intro hg
  cases hrel with
  | same hop => rw [← hop, hg]
  | phi _ hph => exact hph
  | empty _ hop => rw [hop] at hg; cases hg

/-- A copy of `g` that is not a `Phi` of `f` was a copy in `f`, of a related argument. -/
theorem copyArg {fv gv : Value} {w : ID} (hrel : ValRel tabs g fv gv) (hnph : fv.op ≠ .Phi)
    (hop : gv.op = .Copy)
    (hargs : gv.args = #[w]) : fv.op = .Copy ∧ ∃ fa, fv.args = #[fa] ∧ ArgRel g fa w := by
  cases hrel with
  | same hop' _ _ hsz hargs' =>
    refine ⟨by rw [← hop', hop], ?_⟩
    rw [hargs] at hsz
    have h1 : fv.args.size = 1 := by simpa using hsz.symm
    obtain ⟨w0, hw0, hr0⟩ := hargs' 0 fv.args[0] (by simp [h1])
    rw [hargs] at hw0; simp at hw0; subst hw0
    exact ⟨fv.args[0], by
      apply Array.ext; · simp [h1]
      · intro j hj _; simp [h1] at hj; subst hj; simp, hr0⟩
  | phi _ hph => exact absurd hph hnph
  | empty _ hop' => rw [hop] at hop'; cases hop'

/-- The block of a value listed in a tree block, in `g`. -/
theorem blockOf_g (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb) {w : ID} (hw : w ∈ fb.values) : blockOf g w = bid := by
  obtain ⟨-, gv, -, hgv, -, -, hgb, -⟩ := S.value hbt hfb hw
  unfold blockOf; rw [hgv]; exact hgb

/-- An argument of a copy of a tree block, if `f`'s argument is defined elsewhere or is a `Phi`
of the block, is not a value of the block. -/
theorem copyArgOut (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb)
    (hpe : ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry)
    {fa w : ID} {ufa : Value} (hfal : Listed f fa) (hfaU : Anc (make f) (blockOf f fa) bid)
    (hufa : g.value? fa = some ufa) (hopa : ufa.op = .Copy) (hargsa : ufa.args = #[w])
    (hcase : blockOf f fa ≠ bid ∨ ∃ v, f.value? fa = some v ∧ v.op = .Phi) : w ∉ fb.values := by
  intro hw
  have hwb := blockOf_g S hbt hfb hw
  obtain ⟨b', fb', hb', hfb', hx', hbo, hbog⟩ := S.used hfal hfaU
  by_cases hbb : b' = bid
  · subst hbb
    rw [hfb] at hfb'; cases hfb'
    rcases hcase with hcase | ⟨v, hv, hph⟩
    · exact hcase hbo
    · obtain ⟨fv, gv, hfv, hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hx'
      have hvv := Option.some.inj (hfv.symm.trans hv)
      subst hvv
      rw [hufa] at hgv; cases hgv
      obtain ⟨w', hw'a, hr⟩ : ∃ w', ufa.args = #[w'] ∧ ∀ a ∈ fv.args, ArgRel g a w' := by
        cases hrel with
        | same hop' => rw [hopa, hph] at hop'; cases hop'
        | phi w' _ _ ha hr => exact ⟨w', ha, hr⟩
        | empty _ he => rw [hopa] at he; cases he
      rw [hargsa] at hw'a
      have : w = w' := by simpa using hw'a
      subst this
      exact (S.phiOut hbt (hpe _ hx' fv hfv hph) hfb hx' hfv hufa hph hopa hargsa hr).2 hwb
  · obtain ⟨gb', hgbb', -, -, -, -, hvals', -⟩ := S.block hb' hfb'
    have hbt' := S.treeG hb'
    have hU := uses S.cg hbt'.1 hgbb' hbt'.2 (by rw [hvals']; exact hx') hufa
      (by rw [hopa]; decide) (a := w) (by rw [hargsa]; simp)
    rw [S.mk_eq, hwb] at hU
    rw [hbo] at hfaU
    exact hbb (Anc.antisymm S.cp hfaU hU)

/-- An argument of a copy in the source schedule that is a target node is a former `Phi` or
comes earlier in the source schedule. -/
theorem copyBefore (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb)
    (hpe : ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry)
    {oS : Array ID} (hsched : schedule f fb = some oS) :
    ∀ (k : Nat) (y : ID) (gy : Value) (w : ID), oS.toList[k]? = some y → g.value? y = some gy →
      gy.op = .Copy → gy.args = #[w] → w ∈ fb.values →
      (∃ gw, g.value? w = some gw ∧ gw.op ≠ .Phi) →
      w ∈ formerPhis f g fb ∨ ∃ j < k, oS.toList[j]? = some w := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨-, otopo, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
    (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hsched
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro y gy w hk hgy hop hargs hwb hwn
  obtain ⟨hyb, fv, hfv, hnph⟩ := (omem y).1 (List.mem_of_getElem? hk)
  obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hyb
  rw [hfv] at hfv'; cases hfv'
  rw [hgy] at hgv; cases hgv
  obtain ⟨-, fa, hfargs, hra⟩ := copyArg hrel hnph hop hargs
  have hfaU : Anc (make f) (blockOf f fa) bid :=
    uses S.cf hbt.1 hfb hbt.2 hyb hfv hnph (a := fa) (by rw [hfargs]; simp)
  have hfal : Listed f fa :=
    hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hyb, hfv⟩ fa (by rw [hfargs]; simp)
  have hdep : ∀ z, z ∈ fb.values → (∃ v, f.value? z = some v ∧ v.op ≠ .Phi) → z = fa →
      ∃ j < k, oS.toList[j]? = some z := by
    rintro z hzb hzn rfl
    exact topoRem_before otopo hk (by rw [argsF_of hfv, hfargs]; simp) ((omem z).2 ⟨hzb, hzn⟩)
  rcases hra with rfl | ⟨ufa, hufa, hopa, hargsa⟩
  · by_cases hph : ∃ v, f.value? fa = some v ∧ v.op = .Phi
    · exact .inl (mem_formerPhis.2 ⟨hwb, hph, hwn⟩)
    · obtain ⟨v, -, hv, -⟩ := S.value hbt hfb hwb
      exact .inr (hdep fa hwb ⟨v, hv, fun hp => hph ⟨v, hv, hp⟩⟩ rfl)
  · by_cases hcase : blockOf f fa ≠ bid ∨ ∃ v, f.value? fa = some v ∧ v.op = .Phi
    · exact absurd hwb (copyArgOut S hbt hfb hpe hfal hfaU hufa hopa hargsa hcase)
    · have hfab : blockOf f fa = bid := Classical.byContradiction fun hne => hcase (.inl hne)
      obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.used hfal hfaU
      rw [hfab] at hbo; subst hbo
      rw [hfb] at hfb'; cases hfb'
      obtain ⟨vfa, -, hvfa, -⟩ := S.value hbt hfb hx'
      obtain ⟨j', hj', hjfa⟩ := hdep fa hx' ⟨vfa, hvfa, fun hp => hcase (.inr ⟨vfa, hvfa, hp⟩)⟩ rfl
      rcases ih j' hj' fa ufa w hjfa hufa hopa hargsa hwb hwn with h | ⟨j, hj, hjw⟩
      · exact .inl h
      · exact .inr ⟨j, by omega, hjw⟩

/-- **The target block has a schedule.** -/
theorem targetSched (S : Setup tabs f g) {bid : ID} (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb)
    (hpe : ∀ z ∈ fb.values, ∀ fv, f.value? z = some fv → fv.op = .Phi → bid ≠ f.entry)
    {oS : Array ID} (hsched : schedule f fb = some oS) {gb : Block}
    (hgbb : g.block? bid = some gb) (hvals : gb.values = fb.values) :
    ∃ oT, schedule g gb = some oT := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  have hownG := valuesOwn hwg hbg hgbb
  have hndG := hwg.valuesNodup _ _ ⟨hbg, hgbb⟩
  have hndF := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb) hndF hsched
  have hnodeT : ∀ x, NodeIn (schedNodes g gb).toList x ↔
      x ∈ fb.values ∧ ∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi := fun x => by
    rw [nodeIn_schedNodes hownG, hvals]
  -- a target node of the block is a former `Phi` or in the source schedule
  have hsplit : ∀ x, x ∈ fb.values → (∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi) →
      x ∈ formerPhis f g fb ∨ x ∈ oS.toList := by
    intro x hx hgn
    obtain ⟨fv, -, hfv, -⟩ := S.value hbt hfb hx
    by_cases hph : fv.op = .Phi
    · exact .inl (mem_formerPhis.2 ⟨hx, ⟨fv, hfv, hph⟩, hgn⟩)
    · exact .inr ((omem x).2 ⟨hx, fv, hfv, hph⟩)
  have hmemT : ∀ x, x ∈ formerPhis f g fb ++ oS.toList ↔ NodeIn (schedNodes g gb).toList x := by
    intro x
    rw [hnodeT, List.mem_append]
    constructor
    · rintro (h | h)
      · obtain ⟨hx, -, hgn⟩ := mem_formerPhis.1 h; exact ⟨hx, hgn⟩
      · obtain ⟨hx, fv, hfv, hne⟩ := (omem x).1 h
        obtain ⟨fv', gv, hfv', hgv, -, -, -, -, hrel, hz⟩ := S.value hbt hfb hx
        rw [hfv] at hfv'; cases hfv'
        exact ⟨hx, gv, hgv, fun hp => hne (valRel_phi hrel hp)⟩
    · rintro ⟨hx, hgn⟩; exact hsplit x hx hgn
  -- positions in `formerPhis ++ oS`
  have hposF : ∀ a, a ∈ formerPhis f g fb → ∃ i < (formerPhis f g fb).length,
      (formerPhis f g fb ++ oS.toList)[i]? = some a := by
    intro a ha
    obtain ⟨i, hi⟩ := List.getElem?_of_mem ha
    have hil := lt_length_of_getElem? hi
    exact ⟨i, hil, by rw [List.getElem?_append_left hil]; exact hi⟩
  have hposS : ∀ i a, oS.toList[i]? = some a →
      (formerPhis f g fb ++ oS.toList)[(formerPhis f g fb).length + i]? = some a := by
    intro i a hi
    rw [List.getElem?_append_right (by omega)]; simpa using hi
  have hT : Order.Topo (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList)
      (formerPhis f g fb ++ oS.toList) := by
    refine ⟨?_, hmemT, fun j x hj a ha hna => ?_⟩
    · refine List.nodup_append.2 ⟨(hndF.filter _), ond, fun a ha b hb hab => ?_⟩
      subst hab
      obtain ⟨-, ⟨fv, hfv, hph⟩, -⟩ := mem_formerPhis.1 ha
      obtain ⟨-, fv', hfv', hne⟩ := (omem a).1 hb
      rw [hfv] at hfv'; cases hfv'; exact hne hph
    · have hxT := List.mem_of_getElem? hj
      obtain ⟨hxb, gv, hgv, hgn⟩ := (hnodeT x).1 ((hmemT x).1 hxT)
      obtain ⟨hab, -⟩ := (hnodeT a).1 hna
      rw [argsOf_schedNodes hownG hndG (by rw [hvals]; exact hxb) hgv hgn] at ha
      have hagb := blockOf_g S hbt hfb hab
      obtain ⟨fv, gv', hfv, hgv', -, -, -, -, hrel, hz⟩ := S.value hbt hfb hxb
      rw [hgv] at hgv'; cases hgv'
      rcases Nat.lt_or_ge j (formerPhis f g fb).length with hjn | hjn
      · -- a former `Phi`: its argument is outside the block
        rw [List.getElem?_append_left hjn] at hj
        obtain ⟨-, ⟨fv2, hfv2, hph⟩, -⟩ := mem_formerPhis.1 (List.mem_of_getElem? hj)
        rw [hfv] at hfv2; cases hfv2
        cases hrel with
        | same hop => exact absurd (hop.trans hph) hgn
        | phi w _ hcop hw hr =>
          rw [hw] at ha; simp at ha; subst ha
          exact absurd hagb
            (S.phiOut hbt (hpe x hxb fv hfv hph) hfb hxb hfv hgv hph hcop hw hr).2
        | empty hzz => exact absurd hph (hz hzz).not_phi
      · rw [List.getElem?_append_right hjn] at hj
        obtain ⟨-, fv2, hfv2, hnph⟩ := (omem x).1 (List.mem_of_getElem? hj)
        rw [hfv] at hfv2; cases hfv2
        cases hrel with
        | phi _ hph => exact absurd hph hnph
        | empty _ _ hga => rw [hga] at ha; simp at ha
        | same hop _ _ hsz hargs' =>
          obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
          have hk' : gv.args[k]? = some a := by simpa using hk
          have hkf : k < fv.args.size := by
            rw [← hsz]; exact (Array.getElem?_eq_some_iff.1 hk').1
          obtain ⟨w0, hw0, hr0⟩ := hargs' k fv.args[k] (by simp [hkf])
          rw [hk'] at hw0; cases hw0
          have hfaA : fv.args[k] ∈ argsF f x := by rw [argsF_of hfv]; simp
          have hfaU : Anc (make f) (blockOf f fv.args[k]) bid :=
            uses S.cf hbt.1 hfb hbt.2 hxb hfv hnph (Array.getElem_mem hkf)
          have hfal : Listed f fv.args[k] :=
            hwf.argListed _ _ _ _ ⟨⟨hbt.1, hfb⟩, hxb, hfv⟩ _ (Array.getElem_mem hkf)
          rcases hr0 with hfa | ⟨ufa, hufa, hopa, hargsa⟩
          · rcases hsplit a hab ((hnodeT a).1 hna).2 with haF | haS
            · obtain ⟨i, hi, hia⟩ := hposF a haF; exact ⟨i, by omega, hia⟩
            · obtain ⟨i, hi, hia⟩ := topoRem_before otopo hj (hfa ▸ hfaA) haS
              exact ⟨(formerPhis f g fb).length + i, by omega, hposS i a hia⟩
          · by_cases hcase : blockOf f fv.args[k] ≠ bid ∨
                ∃ v, f.value? fv.args[k] = some v ∧ v.op = .Phi
            · exact absurd hab (copyArgOut S hbt hfb hpe hfal hfaU hufa hopa hargsa hcase)
            · have hfab : blockOf f fv.args[k] = bid :=
                Classical.byContradiction fun hne => hcase (.inl hne)
              obtain ⟨b', fb', hb', hfb', hx', hbo, -⟩ := S.used hfal hfaU
              rw [hfab] at hbo; subst hbo
              rw [hfb] at hfb'; cases hfb'
              obtain ⟨vfa, -, hvfa, -⟩ := S.value hbt hfb hx'
              have hfaS : fv.args[k] ∈ oS.toList :=
                (omem _).2 ⟨hx', vfa, hvfa, fun hp => hcase (.inr ⟨vfa, hvfa, hp⟩)⟩
              obtain ⟨j', hj', hjfa⟩ := topoRem_before otopo hj hfaA hfaS
              rcases copyBefore S hbt hfb hpe hsched j' _ ufa a hjfa hufa hopa hargsa hab
                  ((hnodeT a).1 hna).2 with haF | ⟨i, hi, hia⟩
              · obtain ⟨i, hi, hia⟩ := hposF a haF; exact ⟨i, by omega, hia⟩
              · exact ⟨(formerPhis f g fb).length + i, by omega, hposS i a hia⟩
  exact schedule_some (schedNodes_ids hownG hndG) hT

end GoFV.Proof.CopyElim
