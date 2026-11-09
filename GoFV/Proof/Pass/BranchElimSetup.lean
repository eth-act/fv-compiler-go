import GoFV.Proof.Pass.BranchElimRel
import GoFV.Proof.Enter
import GoFV.Proof.Mixed
import GoFV.Proof.SimIH

variable [GoFV.SSA.Sem.Addrs]

/-!
# branchelim: the setting of one checked rewrite

`Base f g s`: `f` is well formed and `g` is `f` with the diamond `s` merged (`DRel`).
`Setup f g s` adds that `g` is well formed and `f`'s uses are dominated on paths (`Dom.UseDom`,
so path dominance `SDom f` is a dominance relation: `Setup.dom`). Consequences of `Base` used by
the simulation and the preservation proofs: the blocks of the diamond are listed and distinct,
their values are disjoint, a run enters an arm or `post` only from the diamond, and the two
functions' contexts agree on unchanged values.
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

/-- See the module doc. -/
structure Base (f g : Func) (s : Site) : Prop where
  wf : ∃ ce, WF ce f
  rel : DRel f g s

/-- See the module doc. -/
structure Setup (f g : Func) (s : Site) : Prop extends Base f g s where
  wg : ∃ ce, WF ce g
  cf : UseDom f

/-- Side `k` of the diamond is taken: its arm and `post`'s predecessor index, and the other
side's. -/
def Taken (s : Site) (k : Nat) (arm : Option ID) (j : Nat) (arm' : Option ID) (j' : Nat) : Prop :=
  (k = 0 ∧ arm = s.arm0 ∧ j = s.j0 ∧ arm' = s.arm1 ∧ j' = s.j1) ∨
  (k = 1 ∧ arm = s.arm1 ∧ j = s.j1 ∧ arm' = s.arm0 ∧ j' = s.j0)

variable {f g : Func} {s : Site}

theorem params_eq {tabs : Tables} (h : g.ownAux = f.ownAux) :
    (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, h]

theorem Setup.dom (S : Setup f g s) : DomRel f (Reachable f) (SDom f) := S.cf.domRel

namespace Base

variable (S : Base f g s)
include S

theorem domIn : s.dom ∈ f.blocks := S.rel.parts.2.1

/-- The diamond's blocks in `f`. -/
theorem diamond :
    ∃ D e0 e1, f.block? s.dom = some D ∧ D.kind = .If ∧ D.controls = #[s.c] ∧
      D.succs = #[e0, e1] ∧ s.post ≠ s.dom ∧
      sideOf f s.dom s.post 0 e0 = some (s.arm0, s.j0) ∧
      sideOf f s.dom s.post 1 e1 = some (s.arm1, s.j1) := by
  obtain ⟨-, -, D, e0, e1, hD, hk, hc, hs, hpd, h0, h1⟩ := site_spec S.rel.site
  exact ⟨D, e0, e1, hD, hk, hc, hs, hpd, h0, h1⟩

/-- Facts of a side: its edge's target is listed; through an arm, the arm is a listed `Plain`
block entered only from `dom` (at index 0) and continuing to `post` along `j`. -/
theorem side_facts {k : Nat} {e : Edge} {arm : Option ID} {j : Nat} {D : Block}
    (hD : f.block? s.dom = some D) (hk : D.succs[k]? = some e)
    (hside : sideOf f s.dom s.post k e = some (arm, j)) :
    (arm = none ∧ e = ⟨s.post, j⟩) ∨
    (∃ a A, arm = some a ∧ e = ⟨a, 0⟩ ∧ a ∈ f.blocks ∧ f.block? a = some A ∧ A.kind = .Plain ∧
      A.preds = #[⟨s.dom, k⟩] ∧ A.succs = #[⟨s.post, j⟩] ∧ a ≠ s.post ∧ a ≠ s.dom) := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases sideOf_spec hside with h | ⟨a, A, ha, heb, hA, hAk, hpr, hsu, hap, had⟩
  · exact .inl h
  · obtain ⟨hl, c, hc, hci⟩ := hwf.succLink s.dom D ⟨S.domIn, hD⟩ k e hk
    rw [heb, hA] at hc; cases hc
    rw [hpr] at hci
    have hi : e.i = 0 := by
      rcases Nat.lt_or_ge e.i 1 with h | h
      · omega
      · rw [Array.getElem?_eq_none (by simpa using h)] at hci; cases hci
    refine .inr ⟨a, A, ha, by cases e; simp_all, heb ▸ hl, hA, hAk, hpr, hsu, hap, had⟩

/-- `post` is listed. -/
theorem postIn : s.post ∈ f.blocks := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, -⟩ := S.diamond
  rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨-, rfl⟩ | ⟨a, A, -, rfl, haIn, hA, -, -, hsu, -⟩
  · exact (hwf.succLink s.dom D ⟨S.domIn, hD⟩ 0 _ (by rw [hs]; rfl)).1
  · exact (hwf.succLink a A ⟨haIn, hA⟩ 0 ⟨s.post, s.j0⟩ (by rw [hsu]; rfl)).1

/-- `post`'s predecessor along side `k` is `dom` (direct) or the side's arm. -/
theorem post_pred {k : Nat} {e : Edge} {arm : Option ID} {j : Nat} {D P : Block}
    (hD : f.block? s.dom = some D) (hk : D.succs[k]? = some e)
    (hside : sideOf f s.dom s.post k e = some (arm, j)) (hP : f.block? s.post = some P) :
    ∃ p, P.preds[j]? = some p ∧ (p.b = s.dom ∨ arm = some p.b) := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases S.side_facts hD hk hside with ⟨-, rfl⟩ | ⟨a, A, ha, rfl, haIn, hA, -, -, hsu, -⟩
  · obtain ⟨-, c, hc, hci⟩ := hwf.succLink s.dom D ⟨S.domIn, hD⟩ k _ hk
    rw [hP] at hc; cases hc
    exact ⟨_, hci, .inl rfl⟩
  · obtain ⟨-, c, hc, hci⟩ := hwf.succLink a A ⟨haIn, hA⟩ 0 ⟨s.post, j⟩ (by rw [hsu]; rfl)
    rw [hP] at hc; cases hc
    exact ⟨_, hci, .inr ha⟩

/-- Every predecessor of `post` is `dom` or an arm. -/
theorem post_preds {P : Block} (hP : f.block? s.post = some P) {i : Nat} {p : Edge}
    (hp : P.preds[i]? = some p) : p.b = s.dom ∨ s.arm0 = some p.b ∨ s.arm1 = some p.b := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
  obtain ⟨P', hP', hsz, hj, hj0, hj1, -⟩ := S.rel.shape
  rw [hP] at hP'; cases hP'
  obtain ⟨p0, hp0, hb0⟩ := S.post_pred hD (by rw [hs]; rfl) h0 hP
  obtain ⟨p1, hp1, hb1⟩ := S.post_pred hD (by rw [hs]; rfl) h1 hP
  have hi : i < 2 := by
    rcases Nat.lt_or_ge i P.preds.size with h | h
    · omega
    · rw [Array.getElem?_eq_none h] at hp; cases hp
  have : i = s.j0 ∨ i = s.j1 := by omega
  rcases this with rfl | rfl
  · rw [hp0] at hp; cases hp
    rcases hb0 with h | h
    · exact .inl h
    · exact .inr (.inl h)
  · rw [hp1] at hp; cases hp
    rcases hb1 with h | h
    · exact .inl h
    · exact .inr (.inr h)

/-- The run enters an arm or `post` only from the diamond: a successor of a listed block
other than `dom` and the arms is neither. -/
theorem succ_normal {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B)
    (hbd : b ≠ s.dom) (ha0 : s.arm0 ≠ some b) (ha1 : s.arm1 ≠ some b) {e : Edge}
    (he : e ∈ B.succs) : e.b ≠ s.post ∧ s.arm0 ≠ some e.b ∧ s.arm1 ≠ some e.b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, c, hc, hci⟩ := hwf.succLink b B ⟨hb, hB⟩ k e hk
  have harm : ∀ a, (s.arm0 = some a ∨ s.arm1 = some a) → e.b ≠ a := by
    intro a ha hea
    obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
    have key : ∀ (k' : Nat) (e' : Edge) (arm : Option ID) (j : Nat), D.succs[k']? = some e' →
        sideOf f s.dom s.post k' e' = some (arm, j) → arm = some a → False := by
      intro k' e' arm j hk' hside harm'
      rcases S.side_facts hD hk' hside with ⟨h', -⟩ | ⟨a', A, ha', -, -, hA, -, hpr, -⟩
      · rw [h'] at harm'; cases harm'
      · rw [harm'] at ha'; cases ha'
        rw [hea, hA] at hc; cases hc
        rw [hpr] at hci
        have : e.i = 0 := by
          rcases Nat.lt_or_ge e.i 1 with h | h
          · omega
          · rw [Array.getElem?_eq_none (by simpa using h)] at hci; cases hci
        rw [this] at hci
        simp at hci
        exact hbd hci.1.symm
    rcases ha with ha | ha
    · exact key 0 e0 s.arm0 s.j0 (by rw [hs]; rfl) h0 ha
    · exact key 1 e1 s.arm1 s.j1 (by rw [hs]; rfl) h1 ha
  refine ⟨fun hep => ?_, fun h => harm e.b (.inl h) rfl, fun h => harm e.b (.inr h) rfl⟩
  rw [hep] at hc
  rcases S.post_preds hc hci with h | h | h
  · exact hbd h
  · exact ha0 h
  · exact ha1 h

/-- Arms are listed. -/
theorem armIn {a : ID} (ha : s.arm0 = some a ∨ s.arm1 = some a) : a ∈ f.blocks := by
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
  rcases ha with ha | ha
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h, -⟩ | ⟨a', A, ha', -, hIn, -⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'; exact hIn
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h, -⟩ | ⟨a', A, ha', -, hIn, -⟩
    · rw [h] at ha; cases ha
    · rw [ha] at ha'; cases ha'; exact hIn

/-- A value of a listed block that is an arm value is listed in that arm. -/
theorem armVal_block {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B)
    {x : ID} (hx : x ∈ B.values) (ha : s.armVal f x = true) :
    s.arm0 = some b ∨ s.arm1 = some b := by
  obtain ⟨ce, hwf⟩ := S.wf
  unfold Site.armVal at ha
  rcases Bool.or_eq_true_iff.1 ha with ha | ha
  · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 ha
    have := hwf.valueOnce b B a A ⟨hb, hB⟩ ⟨S.armIn (.inl ha), hA⟩ x hx hxA
    exact .inl (this ▸ ha)
  · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 ha
    have := hwf.valueOnce b B a A ⟨hb, hB⟩ ⟨S.armIn (.inr ha), hA⟩ x hx hxA
    exact .inr (this ▸ ha)

/-- A value of a listed block that is a `post` value is listed in `post`. -/
theorem postVal_block {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B)
    {x : ID} (hx : x ∈ B.values) (hp : s.postVal f x = true) : b = s.post := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨P, hP, hxP⟩ := postVal_iff.1 hp
  exact hwf.valueOnce b B s.post P ⟨hb, hB⟩ ⟨S.postIn, hP⟩ x hx hxP

/-- Values of `dom` are not values of `post` or an arm. -/
theorem dom_not {D : Block} (hD : f.block? s.dom = some D) {x : ID} (hx : x ∈ D.values) :
    s.postVal f x = false ∧ s.armVal f x = false := by
  obtain ⟨-, -, -, -, -, -, -, hpd, -⟩ := S.diamond
  refine ⟨Bool.eq_false_iff.2 fun hp => hpd (S.postVal_block S.domIn hD hx hp).symm,
    Bool.eq_false_iff.2 fun ha => ?_⟩
  obtain ⟨D', e0, e1, hD', -, -, hs, -, h0, h1⟩ := S.diamond
  rw [hD] at hD'; cases hD'
  rcases S.armVal_block S.domIn hD hx ha with h | h
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h', -⟩ | ⟨a, A, ha', -, -, -, -, -, -, -, had⟩
    · rw [h'] at h; cases h
    · rw [h] at ha'; cases ha'; exact had rfl
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h', -⟩ | ⟨a, A, ha', -, -, -, -, -, -, -, had⟩
    · rw [h'] at h; cases h
    · rw [h] at ha'; cases ha'; exact had rfl

/-- Values of `post` are not arm values. -/
theorem post_not_arm {P : Block} (hP : f.block? s.post = some P) {x : ID} (hx : x ∈ P.values) :
    s.armVal f x = false := by
  refine Bool.eq_false_iff.2 fun ha => ?_
  obtain ⟨D, e0, e1, hD, -, -, hs, -, h0, h1⟩ := S.diamond
  rcases S.armVal_block S.postIn hP hx ha with h | h
  · rcases S.side_facts hD (by rw [hs]; rfl) h0 with ⟨h', -⟩ | ⟨a, A, ha', -, -, -, -, -, -, hap, -⟩
    · rw [h'] at h; cases h
    · rw [h] at ha'; cases ha'; exact hap rfl
  · rcases S.side_facts hD (by rw [hs]; rfl) h1 with ⟨h', -⟩ | ⟨a, A, ha', -, -, -, -, -, -, hap, -⟩
    · rw [h'] at h; cases h
    · rw [h] at ha'; cases ha'; exact hap rfl

/-- The two contexts agree on the values of `f` other than `post`'s `Phi`s. -/
theorem ctxAgree {tabs : Tables} {l : List ID}
    (hl : ∀ x ∈ l, ∀ fv, f.value? x = some fv → s.postVal f x = true → fv.op ≠ .Phi)
    (hid : ∀ x ∈ l, ∀ fv, f.value? x = some fv → fv.id = x) :
    CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) l := by
  obtain ⟨-, hown, -⟩ := S.rel.parts.2.2
  refine ⟨fun x hx => (semEq_of S.rel (hl x hx)).1, fun x hx v hv => ?_, rfl,
    params_eq hown, rfl⟩
  change f.value? x = some v at hv
  obtain ⟨gv, hgv, hty, -⟩ := (semEq_of S.rel (hl x hx)).2 v hv
  rw [hid x hx v hv, tys_of_value hv, tys_of_value hgv, hty]

end Base

end GoFV.Proof.BranchElim
