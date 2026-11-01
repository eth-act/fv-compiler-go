import GoFV.Proof.Pass.BranchElimNormal

/-!
# branchelim: the merged block before its schedule runs

* The diamond under path dominance: arms and `post` are reachable and their strict dominators
  dominate `dom` (or an arm) (`tree_side`, `tree_post`); a value outside the diamond that a
  value of the diamond reads is defined in a strict dominator of `dom`, so it has a register
  when the run enters `dom` (`anc_region_def`, from lemma (D)).
* `targetPre`: the merged block's `Phi`s are `dom`'s; the target collects them from the same
  arguments, has a schedule, and after the `Phi`s agrees with the source (after `dom`'s `Phi`s)
  outside the arm values and the merged block's schedule.
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

variable {f g : Func} {s : Site}

namespace Setup

variable (S : Setup f g s)
include S

/-- Side `k`'s first block (an arm, or `post`) is reachable, and its strict dominators dominate
`dom`. -/
theorem tree_side (htd : Reachable f s.dom) {k : Nat} {e : Edge} {D : Block}
    (hD : f.block? s.dom = some D) (hk : D.succs[k]? = some e) :
    Reachable f e.b ∧ ∀ a, SDom f a e.b → a ≠ e.b → SDom f a s.dom :=
  S.dom.edge S.domIn hD htd (Array.mem_of_getElem? hk)

/-- Every arm is reachable, and its strict dominators dominate `dom`. -/
theorem tree_arm (htd : Reachable f s.dom) {a : ID}
    (ha : s.arm0 = some a ∨ s.arm1 = some a) :
    Reachable f a ∧ ∀ b, SDom f b a → b ≠ a → SDom f b s.dom := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
  rcases ha with ha | ha
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h, -⟩ | ⟨a', A, ha', he, -⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'
      have := S.tree_side htd hD (k := 0) (e := e0) (by rw [hs]; rfl)
      rwa [he] at this
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h, -⟩ | ⟨a', A, ha', he, -⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'
      have := S.tree_side htd hD (k := 1) (e := e1) (by rw [hs]; rfl)
      rwa [he] at this

/-- `post` is reachable, and its strict dominators dominate `dom` or an arm. -/
theorem tree_post (htd : Reachable f s.dom) :
    Reachable f s.post ∧ ((∀ b, SDom f b s.post → b ≠ s.post → SDom f b s.dom) ∨
      ∃ a, (s.arm0 = some a ∨ s.arm1 = some a) ∧
        ∀ b, SDom f b s.post → b ≠ s.post → SDom f b a) := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, -⟩ := S.diamond
  rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨-, he⟩ | ⟨a, A, ha, -, haIn, hA, -, -, hsu, -⟩
  · have := S.tree_side htd hD (k := 0) (e := e0) (by rw [hs]; rfl)
    rw [he] at this
    exact ⟨this.1, .inl this.2⟩
  · obtain ⟨hta, -⟩ := S.tree_arm htd (.inl ha)
    have h := S.dom.edge haIn hA hta (e := ⟨s.post, s.j0⟩) (by rw [hsu]; simp)
    exact ⟨h.1, .inr ⟨a, .inl ha, h.2⟩⟩

/-- A value outside the diamond read from within it is defined in a strict dominator of `dom`:
it has a register at `dom`'s entry. -/
theorem anc_region_def {env : Env} {tabs : Tables} {frS : Frame}
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {b : ID} (hl : Listed f b) (hout : s.regionVal f b = false) {X : ID}
    (hX : X = s.dom ∨ (s.arm0 = some X ∨ s.arm1 = some X) ∨ X = s.post)
    (hanc : SDom f (blockOf f b) X) : ∃ y, frS.regs[b]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨v, B, hP, hvb, hB, hbB, hbIn⟩ := blockOf_listed hwf hl
  unfold Site.regionVal at hout
  simp only [Bool.or_eq_false_iff] at hout
  obtain ⟨⟨hnd, hna⟩, hnp⟩ := hout
  -- the block of `b` is none of the diamond's blocks
  have hnD : blockOf f b ≠ s.dom := fun h => by
    rw [h] at hB
    have : (valsOf f s.dom).contains b = true := by
      rw [valsOf_eq hB]; exact Array.contains_iff_mem.2 hbB
    rw [this] at hnd; cases hnd
  have hnA : ∀ a, (s.arm0 = some a ∨ s.arm1 = some a) → blockOf f b ≠ a := fun a ha h => by
    rw [h] at hB
    have : s.armVal f b = true := by
      unfold Site.armVal
      rcases ha with ha | ha
      · rw [Bool.or_eq_true]; exact .inl (inArm_iff.2 ⟨a, B, ha, hB, hbB⟩)
      · rw [Bool.or_eq_true]; exact .inr (inArm_iff.2 ⟨a, B, ha, hB, hbB⟩)
    rw [this] at hna; cases hna
  have hnP : blockOf f b ≠ s.post := fun h => by
    rw [h] at hB
    have : s.postVal f b = true := postVal_iff.2 ⟨B, hB, hbB⟩
    rw [this] at hnp; cases hnp
  have hdom : SDom f (blockOf f b) s.dom → ∃ y, frS.regs[b]? = some (some y) := fun h => by
    obtain ⟨y, hy, -⟩ := hdi b v hP (by rw [hvb]; exact ⟨h, hnD⟩)
    exact ⟨y, hy⟩
  have harm : ∀ a, (s.arm0 = some a ∨ s.arm1 = some a) → SDom f (blockOf f b) a →
      ∃ y, frS.regs[b]? = some (some y) := fun a ha h =>
    hdom ((S.tree_arm htd ha).2 _ h (hnA a ha))
  rcases hX with rfl | ha | rfl
  · exact hdom hanc
  · exact harm X ha hanc
  · rcases (S.tree_post htd).2 with h | ⟨a, ha, h⟩
    · exact hdom (h _ hanc hnP)
    · exact harm a ha (h _ hanc hnP)

theorem domInG : s.dom ∈ g.blocks := by
  rw [S.rel.parts.2.2.2.2.2.1]; exact S.domIn

/-- The values of the merged block: a value of `dom`, an arm value or a value of `post`; only
`dom`'s `Phi`s stay `Phi`s. -/
theorem merged_values {D D' : Block} (hD : f.block? s.dom = some D)
    (hD' : g.block? s.dom = some D') {x : ID} (hx : x ∈ D'.values) {gv : Value}
    (hgv : g.value? x = some gv) (hph : gv.op = .Phi) :
    x ∈ D.values ∧ ∃ fv, f.value? x = some fv ∧ fv.op = .Phi ∧ SemEq (some fv) (some gv) ∧
      gv.type = fv.type := by
  obtain ⟨D1, P, D1', hD1, hP, hD1', -, -, -, -, hreg, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hD] at hD1; cases hD1
  rw [hD'] at hD1'; cases hD1'
  have hr := hreg x hx
  unfold Site.regionVal at hr
  -- a value that is not a `Phi` in `f`, or a `post` `Phi`, is not a `Phi` in `g`
  have hnot : ∀ fv, f.value? x = some fv → (fv.op ≠ .Phi ∨ s.postVal f x = true) → False := by
    intro fv hfv hc
    by_cases hp : s.postVal f x = true
    · by_cases hfp : fv.op = .Phi
      · obtain ⟨gv', hgv', -, -, -, -, hop, -⟩ := condSel_of S.rel hfv hp hfp
        rw [hgv] at hgv'; cases hgv'
        rw [hop] at hph; cases hph
      · obtain ⟨gv', hgv', -, hop⟩ := (semEq_of S.rel fun fv' h _ => by
          rw [hfv] at h; cases h; exact hfp).2 fv hfv
        rw [hgv] at hgv'; cases hgv'
        exact hfp (hop ▸ hph)
    · have hfp : fv.op ≠ .Phi := hc.resolve_right hp
      obtain ⟨gv', hgv', -, hop⟩ := (semEq_of S.rel fun _ _ h => absurd h hp).2 fv hfv
      rw [hgv] at hgv'; cases hgv'
      exact hfp (hop ▸ hph)
  have hfv : ∃ fv, f.value? x = some fv := by
    have hsem := (value_spec S.rel x)
    unfold Site.valueOK at hsem
    cases h : f.value? x with
    | some fv => exact ⟨fv, rfl⟩
    | none => rw [h, hgv] at hsem; cases hsem
  obtain ⟨fv, hfv⟩ := hfv
  rcases Bool.or_eq_true_iff.1 hr with hr | hr
  · rcases Bool.or_eq_true_iff.1 hr with hr | hr
    · obtain ⟨D2, hD2, hxD⟩ := domVal_iff.1 hr
      rw [hD] at hD2; cases hD2
      have hnp := (S.dom_not hD hxD).1
      by_cases hfp : fv.op = .Phi
      · obtain ⟨gv', hgv', hty, -⟩ := (semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h).2 fv hfv
        have hsem := (semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h).1
        rw [hfv, hgv] at hsem
        rw [hgv] at hgv'; cases hgv'
        exact ⟨hxD, fv, hfv, hfp, hsem, hty⟩
      · exact (hnot fv hfv (.inl hfp)).elim
    · obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel hr
      rw [hfv] at hv; cases hv
      exact (hnot fv hfv (.inl fun h => by rw [h] at hsafe; simp [specSafeOp] at hsafe)).elim
  · exact (hnot fv hfv (.inr hr)).elim

/-- **The target's `Phi`s and schedule** at the merged block. -/
theorem targetPre {tabs : Tables} {frS frT : Frame} {i : Nat}
    (hs : frS.regs.size = f.valueTab.size)
    (hsz : frT.regs.size = frS.regs.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?) {D : Block}
    (hD : f.block? s.dom = some D) {psS : List (ID × Val)}
    (hpsS : D.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok psS) :
    ∃ D' psT oT, g.block? s.dom = some D' ∧
      D'.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      schedule g D' = some oT ∧ (setPhis psT frT.regs).size = frS.regs.size ∧
      ∀ a, a ∉ oT.toList → s.armVal f a = false →
        (setPhis psT frT.regs)[a]? = (setPhis psS frS.regs)[a]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨D1, P, D', hD1, hP, hD', hid', -, -, -, hreg, hDin, -, -, hsch, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hD] at hD1; cases hD1
  obtain ⟨oT, hoT⟩ := Option.isSome_iff_exists.1 hsch
  have hdg := S.domInG
  have hndF := hwf.valuesNodup s.dom D ⟨S.domIn, hD⟩
  have hndG := hwg.valuesNodup s.dom D' ⟨hdg, hD'⟩
  obtain ⟨-, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hdg hD') hndG hoT
  -- `dom`'s `Phi`s read no arm value
  obtain ⟨huse, -⟩ := uses_spec S.rel S.domIn hD
  obtain ⟨-, -, -, -, -, -, -, hpd, -⟩ := S.diamond
  have hphiArg : ∀ z ∈ D.values, ∀ fv, f.value? z = some fv → ∀ (k : Nat) a, fv.args[k]? = some a →
      s.armVal f a = false := by
    intro z hz fv hfv k a hk
    have hu := huse z hz fv hfv k a hk
    unfold Site.useOK at hu
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
    unfold Site.armVal
    have hda : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → s.dom ≠ a' := fun a' ha' h => by
      obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, h1⟩ := S.diamond
      rcases ha' with ha' | ha'
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨a, A, ha, -, -, -, -, -, -, -, had⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at ha; cases ha; exact had h.symm
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h1 with ⟨h', -⟩ | ⟨a, A, ha, -, -, -, -, -, -, -, had⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at ha; cases ha; exact had h.symm
    obtain ⟨h0, h1⟩ := hu
    have e0 : Site.inArm f s.arm0 a = false := by
      rcases h0 with (h0 | h0) | h0
      · exact h0
      · exact absurd rfl (hda s.dom (.inl h0))
      · exact absurd h0.1.1 (Ne.symm hpd)
    have e1 : Site.inArm f s.arm1 a = false := by
      rcases h1 with (h1 | h1) | h1
      · exact h1
      · exact absurd rfl (hda s.dom (.inr h1))
      · exact absurd h1.1.1 (Ne.symm hpd)
    rw [e0, e1]; rfl
  obtain ⟨psT, hpsT⟩ : ∃ psT, D'.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) =
      .ok psT := by
    refine filterMapM_phi_ok fun z hz => ?_
    rw [Array.mem_toList_iff] at hz
    obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ z hz
    by_cases hgph : gv.op = .Phi
    · obtain ⟨hzD, fv, hfv, hfph, hsem, -⟩ := S.merged_values hD hD' hz hgv hgph
      obtain ⟨a, y, ha, hy, -⟩ := hphiS z hzD fv hfv hfph (by rw [hs]; exact lt_of_value? hfv)
      have hyT : frT.regs[a]? = some (some y) := by rw [hag a (hphiArg z hzD fv hfv i a ha), hy]
      refine ⟨some (z, y.retype ((Ctx.make tabs g).tys[z]?.getD .other)), ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv, hgph, beq_self_eq_true, ite_true,
        show gv.args = fv.args from hsem.2.2.2.2, ha, hyT, Option.join]
      rfl
    · refine ⟨none, ?_⟩
      unfold phiStep
      simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
        show (gv.op == .Phi) = false by simpa using hgph]
      rfl
  obtain ⟨hszT, -, hkeepT, hphiT⟩ := phis_spec hndG hpsT
  refine ⟨D', psT, oT, hD', hpsT, hoT, by rw [hszT, hsz], fun a ha hna => ?_⟩
  by_cases haD' : a ∈ D'.values
  · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ a haD'
    have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
      ha ((omemT a).2 ⟨haD', gv, hgv, hne⟩)
    obtain ⟨haD, fv, hfv, hfph, hsem, hty⟩ := S.merged_values hD hD' haD' hgv hgph
    have hlt : a < frT.regs.size := by rw [hsz, hs]; exact lt_of_value? hfv
    obtain ⟨b1, y1, hb1, hy1, hT⟩ := hphiT a haD' gv hgv hgph hlt
    obtain ⟨b2, y2, hb2, hy2, hS⟩ := hphiS a haD fv hfv hfph (by rw [← hsz]; exact hlt)
    have hb12 : b1 = b2 := by rw [hsem.2.2.2.2, hb2] at hb1; exact (Option.some.inj hb1).symm
    subst hb12
    rw [hag b1 (hphiArg a haD fv hfv i b1 hb2), hy2] at hy1
    have hy12 : y1 = y2 := (Option.some.inj (Option.some.inj hy1)).symm
    subst hy12
    rw [hT, hS, tys_of_value hgv, tys_of_value hfv, hty]
  · have haD : a ∉ D.values := fun h => haD' (hDin a h)
    rw [hkeepT a (.inl haD'), hkeepS a (.inl haD), hag a hna]

end Setup

end GoFV.Proof.BranchElim
