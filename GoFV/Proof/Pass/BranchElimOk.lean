import GoFV.Proof.Pass.BranchElimTarget

/-!
# branchelim: the merged block evaluates as the source's path through the diamond

`merged_ok`: if the source runs `dom` (to frame `G1`, its control choosing side `k`), the side's
arm if any (to `G'`) and `post` (to `G3`), the target's merged block runs to a frame agreeing
with `G3` outside the arm values. Reference evaluation (`evalAll_mix`) against `G3`, with the
other side's arm values free: they are speculation-safe and their arguments are defined (lemma
(D), `anc_region_def`). `post`'s `Phi`s are `CondSelect`s picking, by `dom`'s control, the
argument of the side taken (`evalValue_condSelect`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

theorem evalValue_condSelect {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {p0 p1 c : ID}
    {v0 v1 : Val} {b : Bool} (hop : v.op = .CondSelect) (hargs : v.args = #[p0, p1, c])
    (h0 : fr.regs[p0]? = some (some v0)) (h1 : fr.regs[p1]? = some (some v1))
    (hc : fr.regs[c]? = some (some (.bool b))) :
    evalValue env ctx fr v = .ok ((if b then v0 else v1).retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [hargs]
  simp only [List.mapM_cons, List.mapM_nil, h0, h1, hc, Option.join, Option.bind_some, id, Res.ofOption]
  have hf : frameVal ctx v = none := by unfold frameVal; rw [hop]
  have : evalOp env ctx fr v [v0, v1, .bool b] (ctx.tys[v.id]?.getD .other) =
      .ok (Cmp.condSelect [v0, v1, .bool b]) := by
    unfold evalOp
    split <;> (try (rename_i h; rw [hop] at h; cases h))
    rw [hf]
    simp only [hop]
    rfl
  simp only [bind, Res.bind, pure] at this ⊢
  rw [this]
  cases b <;> rfl

variable {f g : Func} {s : Site}

theorem Taken.ne {k : Nat} {arm arm' : Option ID} {j j' : Nat} (h : Taken s k arm j arm' j')
    (hj : s.j0 ≠ s.j1) : j ≠ j' := by
  rcases h with ⟨-, -, rfl, -, rfl⟩ | ⟨-, -, rfl, -, rfl⟩
  · exact hj
  · exact Ne.symm hj

namespace Setup

variable (S : Setup f g s)
include S

/-- `post`'s `Phi`s read along the side taken no value of the other side's arm. -/
theorem phi_arg_side {k : Nat} {arm arm' : Option ID} {j j' : Nat}
    (htk : Taken s k arm j arm' j') {P : Block} (hP : f.block? s.post = some P) {x : ID}
    (hx : x ∈ P.values) {fv : Value} (hfv : f.value? x = some fv) {a : ID}
    (ha : fv.args[j]? = some a) : Site.inArm f arm' a = false := by
  obtain ⟨huse, -⟩ := uses_spec S.rel S.postIn hP
  obtain ⟨P', hP', -, hj, -⟩ := S.rel.shape
  have hu := huse x hx fv hfv j a ha
  unfold Site.useOK at hu
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
  have hpa : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → a' ≠ s.post := fun a' ha' h => by
    obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
    rcases ha' with ha' | ha'
    · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbp h
    · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbp h
  obtain ⟨h0, h1⟩ := hu
  rcases htk with ⟨-, -, rfl, rfl, -⟩ | ⟨-, -, rfl, rfl, -⟩
  · rcases h1 with (h1 | h1) | h1
    · exact h1
    · exact absurd rfl (hpa s.post (.inr h1))
    · exact absurd h1.2 hj
  · rcases h0 with (h0 | h0) | h0
    · exact h0
    · exact absurd rfl (hpa s.post (.inl h0))
    · exact absurd h0.2 (Ne.symm hj)

/-- The values of the taken side's arm (none if the side is direct). -/
theorem arm_facts {tabs : Tables} {env : Env} {k : Nat} {arm arm' : Option ID} {j j' : Nat}
    (htk : Taken s k arm j arm' j') {G1 G' : Frame} (hs : G1.regs.size = f.valueTab.size)
    (hpath : (arm = none ∧ G' = G1) ∨
      (∃ a A, arm = some a ∧ f.block? a = some A ∧ enterBlock env (Ctx.make tabs f) G1 A 0 = .ok G')) :
    G' = { G1 with regs := G'.regs } ∧ G'.regs.size = G1.regs.size ∧
      (∀ z, Site.inArm f arm z = false → G'.regs[z]? = G1.regs[z]?) ∧
      (∀ x, Site.inArm f arm x = true → ∃ v y, f.value? x = some v ∧ G'.regs[x]? = some (some y) ∧
        evalValue env (Ctx.make tabs f) G' v = .ok y) := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases hpath with ⟨rfl, rfl⟩ | ⟨a, A, rfl, hA, h⟩
  · exact ⟨rfl, rfl, fun _ _ => rfl, fun x hx => by simp [Site.inArm] at hx⟩
  · have haIn : a ∈ f.blocks := S.armIn (by
      rcases htk with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact .inl h.symm
      · exact .inr h.symm)
    obtain ⟨f1, f2, f3, f4, -⟩ := enter_ok_facts hwf haIn hA hs h
    refine ⟨f1, f2, fun z hz => f3 z fun hm => ?_, fun x hx => ?_⟩
    · have : Site.inArm f (some a) z = true := inArm_iff.2 ⟨a, A, rfl, hA, hm⟩
      rw [this] at hz; cases hz
    · obtain ⟨a', A', ha', hA', hxA⟩ := inArm_iff.1 hx
      cases ha'
      rw [hA] at hA'; cases hA'
      have hx' : s.armVal f x = true := by
        unfold Site.armVal
        rcases htk with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · rw [← h, hx]; rfl
        · rw [← h, hx]; simp
      obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel hx'
      obtain ⟨y, hy, hev⟩ := f4 x hxA v hv (fun hp => by rw [hp] at hsafe; simp [specSafeOp] at hsafe)
      exact ⟨v, y, hv, hy, hev⟩

/-- An argument outside the diamond of a merged non-`Phi` is defined at `dom`'s entry. -/
theorem region_arg_def {tabs : Tables} {env : Env} {frS : Frame}
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {x : ID} (hx : s.regionVal f x = true) {gv : Value} (hgv : g.value? x = some gv)
    (hgnp : gv.op ≠ .Phi) {a : ID} (ha : a ∈ gv.args) (hout : s.regionVal f a = false) :
    ∃ y, frS.regs[a]? = some (some y) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hfv : ∃ fv, f.value? x = some fv := by
    have hsem := value_spec S.rel x
    unfold Site.valueOK at hsem
    cases h : f.value? x with
    | some fv => exact ⟨fv, rfl⟩
    | none => rw [h, hgv] at hsem; cases hsem
  obtain ⟨fv, hfv⟩ := hfv
  -- a non-`Phi` of a listed tree block of the diamond
  have hnonphi : ∀ (X : ID) (B : Block), X ∈ f.blocks → f.block? X = some B →
      Reachable f X → x ∈ B.values →
      (∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi) →
      (X = s.dom ∨ (s.arm0 = some X ∨ s.arm1 = some X) ∨ X = s.post) →
      ∃ y, frS.regs[a]? = some (some y) := by
    intro X B hX hB ht hxB hnp hXr
    obtain ⟨hsem, hval⟩ := semEq_of S.rel hnp
    rw [hfv, hgv] at hsem
    obtain ⟨gv', hgv', -, hop⟩ := hval fv hfv
    rw [hgv] at hgv'; cases hgv'
    rw [hsem.2.2.2.2] at ha
    exact S.anc_region_def htd hdi (hwf.argListed X B x fv ⟨⟨hX, hB⟩, hxB, hfv⟩ a ha) hout hXr
      (S.dom.uses hX hB ht hxB hfv (fun h => hgnp (hop ▸ h)) ha)
  unfold Site.regionVal at hx
  rcases Bool.or_eq_true_iff.1 hx with hx | hx
  · rcases Bool.or_eq_true_iff.1 hx with hx | hx
    · obtain ⟨D, hD, hxD⟩ := domVal_iff.1 hx
      exact hnonphi s.dom D S.domIn hD htd hxD
        (fun _ _ h => by rw [(S.dom_not hD hxD).1] at h; cases h) (.inl rfl)
    · have hnp : s.postVal f x = false := Bool.eq_false_iff.2 fun hp' => by
        obtain ⟨P, hP, hxP⟩ := postVal_iff.1 hp'
        have := S.post_not_arm hP hxP; rw [hx] at this; cases this
      unfold Site.armVal at hx
      rcases Bool.or_eq_true_iff.1 hx with hx | hx
      · obtain ⟨a0, A, ha0, hA, hxA⟩ := inArm_iff.1 hx
        exact hnonphi a0 A (S.armIn (.inl ha0)) hA (S.tree_arm htd (.inl ha0)).1 hxA
          (fun _ _ h => by rw [hnp] at h; cases h) (.inr (.inl (.inl ha0)))
      · obtain ⟨a0, A, ha0, hA, hxA⟩ := inArm_iff.1 hx
        exact hnonphi a0 A (S.armIn (.inr ha0)) hA (S.tree_arm htd (.inr ha0)).1 hxA
          (fun _ _ h => by rw [hnp] at h; cases h) (.inr (.inl (.inr ha0)))
  · obtain ⟨P, hP, hxP⟩ := postVal_iff.1 hx
    have htp := (S.tree_post htd).1
    by_cases hph : fv.op = .Phi
    · obtain ⟨gv', hgv', -, -, -, -, -, hargs⟩ := condSel_of S.rel hfv hx hph
      rw [hgv] at hgv'; cases hgv'
      obtain ⟨D, e0, e1, hD, -, hctl, hs, -, h0, h1⟩ := S.diamond
      obtain ⟨hsz2, -⟩ := (post_spec S.rel hP x hxP fv hfv).1 hph
      obtain ⟨P', hP', -, -, hj0, hj1, -⟩ := S.rel.shape
      rw [hP] at hP'; cases hP'
      have hphiArg : ∀ (m : Nat) (em : Edge) (arm : Option ID) (jm : Nat), D.succs[m]? = some em →
          sideOf f s.dom s.post m em = some (arm, jm) → jm < 2 → a = fv.args[jm]! →
          ∃ y, frS.regs[a]? = some (some y) := by
        intro m em arm jm hm hside hjm hae
        have hk : fv.args[jm]? = some a := by
          rw [hae, Array.getElem?_eq_getElem (by omega), getElem!_pos fv.args jm (by omega)]
        obtain ⟨p, hpj, hpb⟩ := S.post_pred hD hm hside hP
        have hX : p.b = s.dom ∨ (s.arm0 = some p.b ∨ s.arm1 = some p.b) ∨ p.b = s.post := by
          rcases hpb with h | h
          · exact .inl h
          · refine .inr (.inl ?_)
            rcases m with _ | _ | m
            · have hem : em = e0 := by rw [hs] at hm; simp at hm; exact hm.symm
              subst hem; rw [h0] at hside; cases hside; exact .inl h
            · have hem : em = e1 := by rw [hs] at hm; simp at hm; exact hm.symm
              subst hem; rw [h1] at hside; cases hside; exact .inr h
            · rw [hs] at hm; simp at hm
        have hpt : Reachable f p.b := by
          rcases hX with h | (h | h) | h
          · rw [h]; exact htd
          · exact (S.tree_arm htd (.inl h)).1
          · exact (S.tree_arm htd (.inr h)).1
          · rw [h]; exact htp
        exact S.anc_region_def htd hdi
          (hwf.argListed s.post P x fv ⟨⟨S.postIn, hP⟩, hxP, hfv⟩ a (Array.mem_of_getElem? hk))
          hout hX (S.dom.phiUse S.postIn hP htp hxP hfv hph hk hpj hpt)
      rw [hargs] at ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with h | h | h
      · exact hphiArg 0 e0 s.arm0 s.j0 (by rw [hs]; rfl) h0 hj0 h
      · exact hphiArg 1 e1 s.arm1 s.j1 (by rw [hs]; rfl) h1 hj1 h
      · subst h
        exact S.anc_region_def htd hdi (hwf.ctrlListed s.dom D ⟨S.domIn, hD⟩ s.c (by rw [hctl]; simp))
          hout (.inl rfl) (S.dom.ctrlUse S.domIn hD htd (by rw [hctl]; simp))
    · exact hnonphi s.post P S.postIn hP htp hxP
        (fun fv' h _ => by rw [hfv] at h; cases h; exact hph) (.inr (.inr rfl))

/-- The merged block's schedule against a source frame `G3` at (or in) `post`: `G3` agrees with
`G'` outside `post`, holds `post`'s `Phi`s, and the values of `post` satisfying `Q` re-evaluate
to their registers. -/
theorem merged_core {tabs : Tables} {env : Env} {frS frT G1 G' G3 : Frame} {i k : Nat}
    {arm arm' : Option ID} {j j' : Nat}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D P : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (h1 : enterBlock env (Ctx.make tabs f) frS D i = .ok G1)
    (htk : Taken s k arm j arm' j')
    (hc : G1.regs[s.c]? = some (some (.bool (k == 0))))
    (hpath : (arm = none ∧ G' = G1) ∨
      (∃ a A, arm = some a ∧ f.block? a = some A ∧ enterBlock env (Ctx.make tabs f) G1 A 0 = .ok G'))
    (hG3 : G3 = { frS with regs := G3.regs }) (hG3s : G3.regs.size = f.valueTab.size)
    (e3o : ∀ z, z ∉ P.values → G3.regs[z]? = G'.regs[z]?)
    (e3p : ∀ x ∈ P.values, ∀ v, f.value? x = some v → v.op = .Phi →
      ∃ a y, v.args[j]? = some a ∧ G'.regs[a]? = some (some y) ∧
        G3.regs[x]? = some (some (y.retype ((Ctx.make tabs f).tys[x]?.getD .other))))
    (Q : ID → Prop)
    (e3v : ∀ x ∈ P.values, ∀ v, f.value? x = some v → v.op ≠ .Phi → Q x →
      ∃ y, G3.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G3 v = .ok y) :
    ∃ D' psT oT, g.block? s.dom = some D' ∧ D'.id = s.dom ∧
      D'.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      schedule g D' = some oT ∧ oT.toList.Nodup ∧ TopoRem (argsF (Ctx.make tabs g).f) oT.toList ∧
      (∀ x, x ∈ oT.toList ↔ x ∈ D'.values ∧ ∃ gv, g.value? x = some gv ∧ gv.op ≠ .Phi) ∧
      (∀ x ∈ P.values, x ∈ oT.toList) ∧
      ({ frT with regs := setPhis psT frT.regs } : Frame) = { G3 with regs := setPhis psT frT.regs } ∧
      (setPhis psT frT.regs).size = G3.regs.size ∧
      G3.regs.size = (Ctx.make tabs g).f.valueTab.size ∧
      (∀ a, a ∉ oT.toList → s.armVal f a = false → (setPhis psT frT.regs)[a]? = G3.regs[a]?) ∧
      (∀ a, a ∉ oT.toList → (∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x) →
        ∃ z, (setPhis psT frT.regs)[a]? = some (some z)) ∧
      (∀ x ∈ oT.toList, (∀ fv, f.value? x = some fv → x ∈ P.values → fv.op ≠ .Phi → Q x) →
        MixOK env (Ctx.make tabs g) G3 (fun z => Site.inArm f arm' z = true) [x]) ∧
      (∀ x, s.armVal f x = true → x ∈ oT.toList) ∧
      (∀ x, Site.inArm f arm' x = true → s.armVal f x = true) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, hgsz, -⟩ := S.rel.parts.2.2
  obtain ⟨-, hown, -⟩ := S.rel.parts.2.2
  -- the source's path
  obtain ⟨e1f, e1s, e1o, e1v, e1p⟩ := enter_ok_facts hwf S.domIn hD hs h1
  obtain ⟨eaf, eas, eao, eav⟩ := S.arm_facts htk (by rw [e1s, hs]) hpath
  -- the target's `Phi`s and schedule
  obtain ⟨psS, hpsS⟩ := phis_of_enter (f := f) h1
  obtain ⟨D', psT, oT, hD', hpsT, hoT, hszT, hagT⟩ := S.targetPre hs hsz hag hD hpsS
  obtain ⟨D1, P1, D1', hD1, hP1, hD1', hid', -, -, -, hreg, hDin, hPin, harmin, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hD] at hD1; cases hD1
  rw [hP] at hP1; cases hP1
  rw [hD'] at hD1'; cases hD1'
  have hdg := S.domInG
  have hndG := hwg.valuesNodup s.dom D' ⟨hdg, hD'⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo (valuesOwn hwg hdg hD') hndG hoT
  have hndF := hwf.valuesNodup s.dom D ⟨S.domIn, hD⟩
  obtain ⟨-, -, hkeepS, hphiS⟩ := phis_spec hndF hpsS
  -- membership facts
  have hnotP : ∀ z ∈ D.values, s.postVal f z = false := fun z hz => (S.dom_not hD hz).1
  have hnotA : ∀ z ∈ D.values, s.armVal f z = false := fun z hz => (S.dom_not hD hz).2
  have hPnotA : ∀ z ∈ P.values, s.armVal f z = false := fun z hz => S.post_not_arm hP hz
  have hinArm : ∀ z, Site.inArm f arm z = true ∨ Site.inArm f arm' z = true → s.armVal f z = true := by
    intro z hz
    unfold Site.armVal
    rcases htk with ⟨-, h, -, h', -⟩ | ⟨-, h, -, h', -⟩
    · rcases hz with hz | hz
      · rw [← h, hz]; rfl
      · rw [← h', hz]; simp
    · rcases hz with hz | hz
      · rw [← h, hz]; simp
      · rw [← h', hz]; rfl
  have hArmEither : ∀ z, s.armVal f z = true → Site.inArm f arm z = true ∨ Site.inArm f arm' z = true := by
    intro z hz
    unfold Site.armVal at hz
    rcases htk with ⟨-, h, -, h', -⟩ | ⟨-, h, -, h', -⟩
    · rw [← h, ← h'] at hz; exact Bool.or_eq_true_iff.1 hz
    · rw [← h, ← h'] at hz; exact (Bool.or_eq_true_iff.1 hz).symm
  have hPin' : ∀ z, s.postVal f z = true → z ∈ P.values := fun z hz => by
    obtain ⟨P2, hP2, hz⟩ := postVal_iff.1 hz
    rw [hP] at hP2; cases hP2; exact hz
  -- registers of `G3` outside `post` and the arm
  have g3_out : ∀ z, z ∉ P.values → Site.inArm f arm z = false → G3.regs[z]? = G1.regs[z]? :=
    fun z hz ha => by rw [e3o z hz, eao z ha]
  -- every value of `post` and every arm value is a node of the target's schedule
  have hPnode : ∀ z ∈ P.values, z ∈ oT.toList := by
    intro z hz
    obtain ⟨fv, hfv, -⟩ := hwf.valueId s.post P ⟨S.postIn, hP⟩ z hz
    have hzp : s.postVal f z = true := postVal_iff.2 ⟨P, hP, hz⟩
    refine (omemT z).2 ⟨hPin z hz, ?_⟩
    by_cases hph : fv.op = .Phi
    · obtain ⟨gv, hgv, -, -, -, -, hop, -⟩ := condSel_of S.rel hfv hzp hph
      exact ⟨gv, hgv, by rw [hop]; simp⟩
    · obtain ⟨gv, hgv, -, hop⟩ := (semEq_of S.rel fun fv' h _ => by
        rw [hfv] at h; cases h; exact hph).2 fv hfv
      exact ⟨gv, hgv, by rw [hop]; exact hph⟩
  have hAnode : ∀ z, s.armVal f z = true → z ∈ oT.toList := by
    intro z hz
    obtain ⟨fv, hfv, hsafe, -⟩ := armVal_spec S.rel hz
    have hnp : s.postVal f z = false := Bool.eq_false_iff.2 fun hp' => by
      have := S.post_not_arm hP (hPin' z hp'); rw [hz] at this; cases this
    obtain ⟨gv, hgv, -, hop⟩ := (semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h).2 fv hfv
    refine (omemT z).2 ⟨harmin z hz, gv, hgv, ?_⟩
    rw [hop]; intro h; rw [h] at hsafe; simp [specSafeOp] at hsafe
  -- the target after its `Phi`s agrees with `G3` outside its schedule
  have hT0 : ∀ a, a ∉ oT.toList → s.armVal f a = false →
      (setPhis psT frT.regs)[a]? = G3.regs[a]? := by
    intro a ha hna
    rw [hagT a ha hna]
    have haP : a ∉ P.values := fun h => ha (hPnode a h)
    have haA : Site.inArm f arm a = false := Bool.eq_false_iff.2 fun h =>
      by rw [hinArm a (.inl h)] at hna; cases hna
    rw [g3_out a haP haA]
    by_cases haD : a ∈ D.values
    · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ a (hDin a haD)
      have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
        ha ((omemT a).2 ⟨hDin a haD, gv, hgv, hne⟩)
      obtain ⟨-, fv, hfv, hfph, -, -⟩ := S.merged_values hD hD' (hDin a haD) hgv hgph
      have hlt : a < frS.regs.size := by rw [hs]; exact lt_of_value? hfv
      obtain ⟨b1, y1, hb1, hy1, hS1⟩ := hphiS a haD fv hfv hfph hlt
      obtain ⟨b2, y2, hb2, hy2, hS2⟩ := e1p a haD fv hfv hfph
      rw [hb1] at hb2; cases hb2
      rw [hy1] at hy2; cases hy2
      rw [hS1, hS2]
    · rw [hkeepS a (.inl haD), e1o a haD]
  -- the other side's arm values are free
  let F : ID → Prop := fun x => Site.inArm f arm' x = true
  have hFarm : ∀ x, F x → s.armVal f x = true := fun x hx => hinArm x (.inr hx)
  have hnF : ∀ x, s.armVal f x = false → ¬ F x := fun x hx hF => by rw [hFarm x hF] at hx; cases hx
  have hctxT : (Ctx.make tabs g).params = (Ctx.make tabs f).params := params_eq hown
  have htys : ∀ x fv gv, f.value? x = some fv → g.value? x = some gv → gv.type = fv.type →
      (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := fun x fv gv hfv hgv hty => by
    rw [tys_of_value hfv, tys_of_value hgv, hty]
  have hval : ∀ x gv, g.value? x = some gv → ∃ fv, f.value? x = some fv := fun x gv hgv => by
    have hsem := value_spec S.rel x
    unfold Site.valueOK at hsem
    cases h : f.value? x with
    | some fv => exact ⟨fv, rfl⟩
    | none => rw [h, hgv] at hsem; cases hsem
  -- an unchanged value, evaluated where its arguments agree with a source frame `Gs` of the
  -- activation, yields the source's result there
  have hsame : ∀ x fv gv (Gs g' : Frame) y, f.value? x = some fv → g.value? x = some gv →
      x ∈ D'.values → (∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi) →
      Gs = { G3 with regs := Gs.regs } → g' = { G3 with regs := g'.regs } →
      (∀ a ∈ fv.args, g'.regs[a]? = Gs.regs[a]?) → evalValue env (Ctx.make tabs f) Gs fv = .ok y →
      stepV env (Ctx.make tabs g) g' x = .ok y := by
    intro x fv gv Gs g' y hfv hgv hxD hc hGs hg' hag' hev
    obtain ⟨hsem, hv⟩ := semEq_of S.rel hc
    rw [hfv, hgv] at hsem
    obtain ⟨gv', hgv', hty, -⟩ := hv fv hfv
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨gv'', hgv'', hgid, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ x hxD
    rw [hgv] at hgv''; cases hgv''
    have hfid : fv.id = x := hsem.1 ▸ hgid
    rw [stepV_eq hgv]
    exact (evalValue_ctx_congr (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g) hsem
      (frame_same hg' hGs) hag' (by rw [hfid]; exact htys x fv gv hfv hgv hty) rfl hctxT
      rfl).trans hev
  have hG1 : G1 = { G3 with regs := G1.regs } := frame_same e1f hG3
  have hG' : G' = { G3 with regs := G'.regs } := frame_same (by rw [eaf, e1f]) hG3
  have hnotPv : ∀ z, s.postVal f z = false → z ∉ P.values := fun z hz hm => by
    rw [postVal_iff.2 ⟨P, hP, hm⟩] at hz; cases hz
  have hnotArmv : ∀ z, s.armVal f z = false → Site.inArm f arm z = false := fun z hz =>
    Bool.eq_false_iff.2 fun h => by rw [hinArm z (.inl h)] at hz; cases hz
  have hargsT : ∀ x gv, g.value? x = some gv → ∀ a ∈ gv.args, a ∈ argsF (Ctx.make tabs g).f x :=
    fun x gv hgv a ha => by
      rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]; exact Array.mem_toList_iff.2 ha
  have hPnp : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → a' ≠ s.post := fun a' ha' h => by
    obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, h1⟩ := S.diamond
    rcases ha' with ha' | ha'
    · rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbp h
    · rcases S.side_facts hD2 (by rw [hs2]; rfl) h1 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbp h
  have hDnp : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → a' ≠ s.dom := fun a' ha' h => by
    obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, h1⟩ := S.diamond
    rcases ha' with ha' | ha'
    · rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, -, hbd⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbd h
    · rcases S.side_facts hD2 (by rw [hs2]; rfl) h1 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, -, hbd⟩
      · rw [h'] at ha'; cases ha'
      · rw [ha'] at hb; cases hb; exact hbd h
  -- arguments of the values of `dom` and of `post`'s non-`Phi`s are no arm values
  have hnoArm : ∀ bid B, bid ∈ f.blocks → f.block? bid = some B → (bid = s.dom ∨ bid = s.post) →
      ∀ x ∈ B.values, ∀ fv, f.value? x = some fv → fv.op ≠ .Phi → ∀ a ∈ fv.args,
        s.armVal f a = false := by
    intro bid B hb hB hbr x hx fv hfv hnp a ha
    obtain ⟨k', hk'⟩ := Array.mem_iff_getElem?.1 ha
    have hu := (uses_spec S.rel hb hB).1 x hx fv hfv k' a hk'
    unfold Site.useOK at hu
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
    obtain ⟨h0, h1⟩ := hu
    have hna : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → bid ≠ a' := fun a' ha' h => by
      rcases hbr with rfl | rfl
      · exact hDnp a' ha' h.symm
      · exact hPnp a' ha' h.symm
    have e0 : Site.inArm f s.arm0 a = false := by
      rcases h0 with (h0 | h0) | h0
      · exact h0
      · exact absurd rfl (hna bid (.inl h0))
      · exact absurd h0.1.2 hnp
    have e1 : Site.inArm f s.arm1 a = false := by
      rcases h1 with (h1 | h1) | h1
      · exact h1
      · exact absurd rfl (hna bid (.inr h1))
      · exact absurd h1.1.2 hnp
    unfold Site.armVal; rw [e0, e1]; rfl
  have hctlNA : s.armVal f s.c = false :=
    (uses_spec S.rel S.domIn hD).2 s.c (by
      obtain ⟨D2, -, -, hD2, -, hctl, -⟩ := S.diamond
      rw [hD] at hD2; cases hD2; rw [hctl]; simp)
  have hshape := S.rel.shape
  obtain ⟨-, -, -, hj, -, -, -, haok0, haok1, -⟩ := hshape
  have harmOK : s.armOK f arm arm' = true := by
    rcases htk with ⟨-, h, -, h', -⟩ | ⟨-, h, -, h', -⟩
    · rw [h, h']; exact haok0
    · rw [h, h']; exact haok1
  -- `MixOK`
  have hmix : ∀ x ∈ oT.toList, (∀ fv, f.value? x = some fv → x ∈ P.values → fv.op ≠ .Phi → Q x) →
      MixOK env (Ctx.make tabs g) G3 F [x] := by
    intro x hx hQx z hz
    rw [List.mem_singleton] at hz
    rw [hz]
    obtain ⟨hxD', gv, hgv, hgnp⟩ := (omemT x).1 hx
    obtain ⟨fv, hfv⟩ := hval x gv hgv
    have hr := hreg x hxD'
    refine ⟨fun hnFx => ?_, fun hFx g' hg' hdef => ?_⟩
    · unfold Site.regionVal at hr
      rcases Bool.or_eq_true_iff.1 hr with hr | hr
      · rcases Bool.or_eq_true_iff.1 hr with hr | hr
        · -- a value of `dom`
          obtain ⟨D2, hD2, hxD⟩ := domVal_iff.1 hr
          rw [hD] at hD2; cases hD2
          have hnp := hnotP x hxD
          have hc : ∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi :=
            fun _ _ h => by rw [hnp] at h; cases h
          obtain ⟨hsem, hv⟩ := semEq_of S.rel hc
          rw [hfv, hgv] at hsem
          obtain ⟨gv', hgv', -, hop⟩ := hv fv hfv
          rw [hgv] at hgv'; cases hgv'
          have hfnp : fv.op ≠ .Phi := fun h => hgnp (hop ▸ h)
          obtain ⟨y, hy, hev⟩ := e1v x hxD fv hfv hfnp
          refine ⟨y, by rw [g3_out x (hnotPv x hnp) (hnotArmv x (hnotA x hxD)), hy],
            fun g' hg' hag' _ => hsame x fv gv G1 g' y hfv hgv hxD' hc hG1 hg' (fun a ha => ?_) hev⟩
          have hna := hnoArm s.dom D S.domIn hD (.inl rfl) x hxD fv hfv hfnp a ha
          have hnpa : s.postVal f a = false := (dom_spec S.rel hD).1 x hxD fv hfv hfnp a ha
          rw [hag' a (hargsT x gv hgv a (hsem.2.2.2.2 ▸ ha)) (hnF a hna),
            g3_out a (hnotPv a hnpa) (hnotArmv a hna)]
        · -- a value of the taken side's arm
          have hxa : Site.inArm f arm x = true := (hArmEither x hr).resolve_right hnFx
          have hnp : s.postVal f x = false := Bool.eq_false_iff.2 fun hp' => by
            have := S.post_not_arm hP (hPin' x hp'); rw [hr] at this; cases this
          have hc : ∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi :=
            fun _ _ h => by rw [hnp] at h; cases h
          obtain ⟨hsem, -⟩ := semEq_of S.rel hc
          rw [hfv, hgv] at hsem
          obtain ⟨v, y, hv, hy, hev⟩ := eav x hxa
          rw [hfv] at hv; cases hv
          obtain ⟨v', hv', -, hargs⟩ := armOK_spec harmOK hxa
          rw [hfv] at hv'; cases hv'
          refine ⟨y, by rw [e3o x (hnotPv x hnp), hy],
            fun g' hg' hag' _ => hsame x fv gv G' g' y hfv hgv hxD' hc hG' hg' (fun a ha => ?_) hev⟩
          obtain ⟨hnpa, hnoa⟩ := hargs a ha
          rw [hag' a (hargsT x gv hgv a (hsem.2.2.2.2 ▸ ha)) (fun h => by rw [h] at hnoa; cases hnoa),
            e3o a (hnotPv a hnpa)]
      · -- a value of `post`
        obtain ⟨P2, hP2, hxP⟩ := postVal_iff.1 hr
        rw [hP] at hP2; cases hP2
        by_cases hph : fv.op = .Phi
        · obtain ⟨a', y0, ha', hy0, hx3⟩ := e3p x hxP fv hfv hph
          obtain ⟨gv', hgv', hgid', hgty, -, -, hgop, hgargs⟩ := condSel_of S.rel hfv hr hph
          rw [hgv] at hgv'; cases hgv'
          obtain ⟨gv'', hgv'', hgid, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ x hxD'
          rw [hgv] at hgv''; cases hgv''
          refine ⟨_, hx3, fun g' hg' hag' hdef => ?_⟩
          have hmem : ∀ a ∈ gv.args, ∃ z, g'.regs[a]? = some (some z) := fun a ha =>
            hdef a (hargsT x gv hgv a ha)
          obtain ⟨v0, hv0⟩ := hmem fv.args[s.j0]! (by rw [hgargs]; simp)
          obtain ⟨v1, hv1⟩ := hmem fv.args[s.j1]! (by rw [hgargs]; simp)
          have hcv : g'.regs[s.c]? = some (some (.bool (k == 0))) := by
            rw [hag' s.c (hargsT x gv hgv s.c (by rw [hgargs]; simp)) (hnF s.c hctlNA),
              g3_out s.c (hnotPv s.c (dom_spec S.rel hD).2) (hnotArmv s.c hctlNA), hc]
          rw [stepV_eq hgv, evalValue_condSelect hgop hgargs hv0 hv1 hcv, hgid,
            htys x fv gv hfv hgv hgty]
          -- the side taken
          have hpost : ∀ a, fv.args[j]? = some a → g'.regs[a]? = G'.regs[a]? := by
            intro a ha
            have hnoa := S.phi_arg_side htk hP hxP hfv ha
            have hget : fv.args[j]! = a := by
              have hlt := (Array.getElem?_eq_some_iff.1 ha).1
              rw [getElem!_pos fv.args j hlt]; exact (Array.getElem?_eq_some_iff.1 ha).2
            rw [hag' a (hargsT x gv hgv a (by
                rw [hgargs]
                rcases htk with ⟨-, -, rfl, -, -⟩ | ⟨-, -, rfl, -, -⟩
                · rw [← hget]; simp
                · rw [← hget]; simp))
              (fun h => by rw [h] at hnoa; cases hnoa),
              e3o a (hnotPv a (((post_spec S.rel hP x hxP fv hfv).1 hph).2 a
                (Array.mem_of_getElem? ha)))]
          have hjv : g'.regs[fv.args[j]!]? = some (some y0) := by
            have hlt : j < fv.args.size := (Array.getElem?_eq_some_iff.1 ha').1
            rw [getElem!_pos fv.args j hlt]
            rw [Array.getElem?_eq_getElem hlt] at ha'
            cases ha'
            rw [hpost _ (Array.getElem?_eq_getElem hlt), hy0]
          rcases htk with ⟨rfl, -, rfl, -, -⟩ | ⟨rfl, -, rfl, -, -⟩
          · rw [hjv] at hv0; cases hv0; rfl
          · rw [hjv] at hv1; cases hv1; rfl
        · obtain ⟨y, hy, hev⟩ := e3v x hxP fv hfv hph (hQx fv hfv hxP hph)
          have hc : ∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi :=
            fun fv' h _ => by rw [hfv] at h; cases h; exact hph
          obtain ⟨hsem, -⟩ := semEq_of S.rel hc
          rw [hfv, hgv] at hsem
          refine ⟨y, hy, fun g' hg' hag' _ => hsame x fv gv G3 g' y hfv hgv hxD' hc rfl hg'
            (fun a ha => hag' a (hargsT x gv hgv a (hsem.2.2.2.2 ▸ ha))
              (hnF a (hnoArm s.post P S.postIn hP (.inr rfl) x hxP fv hfv hph a ha))) hev⟩
    · -- a value of the other side's arm: speculation-safe
      have hxarm := hFarm x hFx
      obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel hxarm
      rw [hfv] at hv; cases hv
      have hnp : s.postVal f x = false := Bool.eq_false_iff.2 fun hp' => by
        have := S.post_not_arm hP (hPin' x hp'); rw [hxarm] at this; cases this
      obtain ⟨hsem, -⟩ := semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h
      rw [hfv, hgv] at hsem
      rw [stepV_eq hgv]
      exact evalValue_specSafe (by rw [hsem.2.1]; exact hsafe)
        fun a ha => hdef a (hargsT x gv hgv a ha)
  have hnoarmS : ∀ a, a ∉ oT.toList → s.armVal f a = false := fun a ha =>
    Bool.eq_false_iff.2 fun h => ha (hAnode a h)
  have hSd : ∀ a, a ∉ oT.toList → (∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x) →
      ∃ z, (setPhis psT frT.regs)[a]? = some (some z) := by
    rintro a hna ⟨x, hx, hax⟩
    have hnarm := hnoarmS a hna
    rw [hT0 a hna hnarm]
    have haP : a ∉ P.values := fun h => hna (hPnode a h)
    rw [g3_out a haP (hnotArmv a hnarm)]
    by_cases haD : a ∈ D.values
    · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ a (hDin a haD)
      have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
        hna ((omemT a).2 ⟨hDin a haD, gv, hgv, hne⟩)
      obtain ⟨-, fv, hfv, hfph, -, -⟩ := S.merged_values hD hD' (hDin a haD) hgv hgph
      obtain ⟨-, y, -, -, hy⟩ := e1p a haD fv hfv hfph
      exact ⟨_, hy⟩
    · rw [e1o a haD]
      obtain ⟨hxD', gv, hgv, hgnp⟩ := (omemT x).1 hx
      have hout : s.regionVal f a = false := by
        have hd : (valsOf f s.dom).contains a = false := Bool.eq_false_iff.2 fun h => haD (by
          obtain ⟨D2, hD2, h2⟩ := domVal_iff.1 h; rw [hD] at hD2; cases hD2; exact h2)
        have hpv : s.postVal f a = false := Bool.eq_false_iff.2 fun h => haP (hPin' a h)
        unfold Site.regionVal
        rw [hnarm, hd, hpv]; rfl
      exact S.region_arg_def htd hdi (hreg x hxD') hgv hgnp
        (by rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv] at hax
            exact Array.mem_toList_iff.1 hax) hout
  exact ⟨D', psT, oT, hD', hid', hpsT, hoT, ondT, otopoT, omemT, hPnode, with_regs_same hfr hG3 _,
    by rw [hszT, hG3s, hs], by rw [hG3s, ← hgsz]; rfl, hT0, hSd, hmix, hAnode, hFarm⟩

/-- **The merged block runs as the source's path.** -/
theorem merged_ok {tabs : Tables} {env : Env} {frS frT G1 G' G3 : Frame} {i k : Nat}
    {arm arm' : Option ID} {j j' : Nat}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D P : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (h1 : enterBlock env (Ctx.make tabs f) frS D i = .ok G1)
    (htk : Taken s k arm j arm' j')
    (hc : G1.regs[s.c]? = some (some (.bool (k == 0))))
    (hpath : (arm = none ∧ G' = G1) ∨
      (∃ a A, arm = some a ∧ f.block? a = some A ∧ enterBlock env (Ctx.make tabs f) G1 A 0 = .ok G'))
    (h3 : enterBlock env (Ctx.make tabs f) G' P j = .ok G3) :
    ∃ D' GT, g.block? s.dom = some D' ∧ enterBlock env (Ctx.make tabs g) frT D' i = .ok GT ∧
      GT = { G3 with regs := GT.regs } ∧ GT.regs.size = G3.regs.size ∧
      ∀ a, s.armVal f a = false → GT.regs[a]? = G3.regs[a]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨e1f, e1s, -, -, -⟩ := enter_ok_facts hwf S.domIn hD hs h1
  obtain ⟨eaf, eas, -, -⟩ := S.arm_facts htk (by rw [e1s, hs]) hpath
  obtain ⟨e3f, e3s, e3o, e3v, e3p⟩ := enter_ok_facts hwf S.postIn hP (by rw [eas, e1s, hs]) h3
  obtain ⟨D', psT, oT, hD', hid', hpsT, hoT, -, otopoT, -, -, hg0, hsz0, hGs, hT0, hSd, hmix,
      hAnode, hFarm⟩ := S.merged_core hfr hsz hs hag htd hdi hD hP h1 htk hc hpath
    (by rw [e3f, eaf, e1f]) (by rw [e3s, eas, e1s, hs]) e3o e3p (fun _ => True)
    (fun x hx v hv hp _ => e3v x hx v hv hp)
  have hnoarmS : ∀ a, a ∉ oT.toList → s.armVal f a = false := fun a ha =>
    Bool.eq_false_iff.2 fun h => ha (hAnode a h)
  have hnF : ∀ a, s.armVal f a = false → ¬ Site.inArm f arm' a = true := fun a ha hF => by
    rw [hFarm a hF] at ha; cases ha
  obtain ⟨GT, hev, hGT, hGTs, h4, -, h6⟩ := evalAll_mix (F := fun z => Site.inArm f arm' z = true)
    hGs (mixOK_of_single fun x hx => hmix x hx fun _ _ _ _ => trivial)
    (S := fun a => a ∉ oT.toList ∧ ∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x)
    (Dead.refOK_of_topo otopoT fun x hx a ha hna => ⟨hna, x, hx, ha⟩)
    (fun a ha _ => hT0 a ha.1 (hnoarmS a ha.1)) (fun a ha => hSd a ha.1 ha.2) hg0 hsz0
  refine ⟨D', GT, hD', ?_, hGT, hGTs, fun a ha => ?_⟩
  · rw [enterBlock_eq, hpsT]
    change (Res.ofOption _ ((Ctx.make tabs g).sched[D'.id]?).join).bind _ = _
    rw [hid', sched_of_block hD', hoT]
    exact hev
  · by_cases haT : a ∈ oT.toList
    · exact h4 a (.inr haT) (hnF a ha)
    · rw [h6 a haT]; exact hT0 a haT ha

end Setup

end GoFV.Proof.BranchElim
