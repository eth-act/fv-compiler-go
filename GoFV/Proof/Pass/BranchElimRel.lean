import GoFV.Opt.BranchElimCheck
import GoFV.Proof.Pass.DeadChain
import GoFV.Proof.Speculate
import GoFV.Proof.Agree

/-!
# branchelim: what the step checker establishes

`DRel f g s`: `site? f s.dom s.post = some s` and `s.relB f g` (`GoFV.Opt.BranchElimCheck`).
This module unfolds the checker into the facts the simulation uses: the diamond's shape
(`site_spec`, `sideOf_spec`, `post_shape`), the conditions on arm, `dom` and `post` values,
the merged block of `g`, and the unchanged values and blocks.
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof

/-- One checked branchelim rewrite. -/
structure DRel (f g : Func) (s : Site) : Prop where
  site : site? f s.dom s.post = some s
  rel : s.relB f g = true

theorem valsOf_eq {f : Func} {b : ID} {B : Block} (h : f.block? b = some B) : valsOf f b = B.values := by
  simp [valsOf, h]

theorem inArm_iff {f : Func} {a? : Option ID} {x : ID} :
    Site.inArm f a? x = true ↔ ∃ a A, a? = some a ∧ f.block? a = some A ∧ x ∈ A.values := by
  unfold Site.inArm valsOf
  cases a? with
  | none => simp
  | some a =>
    cases h : f.block? a with
    | none => simp [h]
    | some A => simp [h, Array.contains_iff_mem]

theorem postVal_iff {s : Site} {f : Func} {x : ID} :
    s.postVal f x = true ↔ ∃ P, f.block? s.post = some P ∧ x ∈ P.values := by
  unfold Site.postVal valsOf
  cases h : f.block? s.post with
  | none => simp [h]
  | some P => simp [h, Array.contains_iff_mem]

theorem domVal_iff {s : Site} {f : Func} {x : ID} :
    (valsOf f s.dom).contains x = true ↔ ∃ D, f.block? s.dom = some D ∧ x ∈ D.values := by
  unfold valsOf
  cases h : f.block? s.dom with
  | none => simp [h]
  | some D => simp [h, Array.contains_iff_mem]

/-- The site of a diamond. -/
theorem site_spec {f : Func} {dom post : ID} {s : Site} (h : site? f dom post = some s) :
    s.dom = dom ∧ s.post = post ∧ ∃ D e0 e1, f.block? dom = some D ∧ D.kind = .If ∧
      D.controls = #[s.c] ∧ D.succs = #[e0, e1] ∧ post ≠ dom ∧
      sideOf f dom post 0 e0 = some (s.arm0, s.j0) ∧ sideOf f dom post 1 e1 = some (s.arm1, s.j1) := by
  unfold site? at h
  cases hD : f.block? dom with
  | none => rw [hD] at h; cases h
  | some D =>
    rw [hD] at h
    simp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
      obtain ⟨⟨⟨hk, hcs⟩, hss⟩, hpd⟩ := hc
      split at h
      · rename_i a0 j0 a1 j1 h0 h1
        cases h
        have hsucc : D.succs = #[D.succs[0]!, D.succs[1]!] := by
          apply Array.ext
          · simp [hss]
          · intro i h1 h2
            simp only [hss] at h1
            have : i = 0 ∨ i = 1 := by omega
            rcases this with rfl | rfl <;> simp [getElem!_pos, hss]
        have hctl : D.controls = #[D.controls[0]!] := by
          apply Array.ext
          · simp [hcs]
          · intro i h1 h2
            simp only [hcs] at h1
            have : i = 0 := by omega
            subst this; simp [getElem!_pos, hcs]
        exact ⟨rfl, rfl, D, _, _, rfl, hk, hctl, hsucc, hpd, h0, h1⟩
      · cases h
    · cases h

/-- A side of the diamond: the edge enters `post` directly, or a `Plain` arm whose only
predecessor is `dom` along successor `k` and whose only successor is `post`. -/
theorem sideOf_spec {f : Func} {dom post : ID} {k : Nat} {e : Edge} {a? : Option ID} {j : Nat}
    (h : sideOf f dom post k e = some (a?, j)) :
    (a? = none ∧ e = ⟨post, j⟩) ∨
    (∃ a A, a? = some a ∧ e.b = a ∧ f.block? a = some A ∧ A.kind = .Plain ∧
      A.preds = #[⟨dom, k⟩] ∧ A.succs = #[⟨post, j⟩] ∧ a ≠ post ∧ a ≠ dom) := by
  unfold sideOf at h
  split at h
  · rename_i hp
    cases h
    exact .inl ⟨rfl, by cases e; simp_all⟩
  · rename_i hp
    split at h
    · rename_i A hA
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨⟨hk, hpr⟩, hss⟩, hsb⟩, hnd⟩ := hc
        have hs0 : A.succs = #[⟨post, (A.succs[0]?.map (·.i)).getD 0⟩] := by
          have h0 : 0 < A.succs.size := by omega
          apply Array.ext
          · simp [hss]
          · intro i h1 h2
            simp only [hss] at h1
            have : i = 0 := by omega
            subst this
            have hb : A.succs[0].b = post := by
              simpa [Array.getElem?_eq_getElem h0] using hsb
            simp [Array.getElem?_eq_getElem h0, ← hb]
        refine .inr ⟨e.b, A, rfl, rfl, hA, hk, hpr, hs0, by simpa using hp, hnd⟩
      · cases h
    · cases h

section
variable {f g : Func} {s : Site}

theorem DRel.parts (h : DRel f g s) :
    s.shapeOK f = true ∧ s.dom ∈ f.blocks ∧ g.entry = f.entry ∧ g.ownAux = f.ownAux ∧
      g.valueTab.size = f.valueTab.size ∧ g.blocks = f.blocks ∧ s.mergedOK f g = true ∧
      (∀ x, x < f.valueTab.size → s.valueOK f g x = true) ∧ (∀ b ∈ f.blocks, s.blockOK f g b = true) := by
  have := h.rel
  simp only [Site.relB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true', Array.contains_iff_mem] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h0⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := this
  exact ⟨h1, h0, h2, h3, h4, h5, h6, h7, h8⟩

theorem DRel.shape (h : DRel f g s) :
    ∃ P, f.block? s.post = some P ∧ P.preds.size = 2 ∧ s.j0 ≠ s.j1 ∧ s.j0 < 2 ∧ s.j1 < 2 ∧
      (∀ a b, s.arm0 = some a → s.arm1 = some b → a ≠ b) ∧
      s.armOK f s.arm0 s.arm1 = true ∧ s.armOK f s.arm1 s.arm0 = true ∧ s.usesOK f = true ∧
      s.domOK f = true ∧ s.postOK f = true := by
  have h1 := h.parts.1
  unfold Site.shapeOK at h1
  cases hP : f.block? s.post with
  | none => rw [hP] at h1; cases h1
  | some P =>
    rw [hP] at h1
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hj⟩, hj0⟩, hj1⟩, harms⟩, ha0⟩, ha1⟩, hu⟩, hd⟩, hpo⟩ := h1
    refine ⟨P, rfl, hp, hj, hj0, hj1, (fun a b h0 h1 => ?_), ha0, ha1, hu, hd, hpo⟩
    rw [h0, h1] at harms
    simpa using harms

/-- The values of an arm. -/
theorem armOK_spec {own other : Option ID} (h : s.armOK f own other = true) {x : ID}
    (hx : Site.inArm f own x = true) :
    ∃ v, f.value? x = some v ∧ specSafeOp v.op = true ∧
      ∀ a ∈ v.args, s.postVal f a = false ∧ Site.inArm f other a = false := by
  obtain ⟨a, A, rfl, hA, hxA⟩ := inArm_iff.1 hx
  unfold Site.armOK at h
  simp only at h
  rw [valsOf_eq hA] at h
  have := (Array.all_eq_true'.1 h) x hxA
  cases hv : f.value? x with
  | none => rw [hv] at this; cases this
  | some v =>
    rw [hv] at this
    simp only [Bool.and_eq_true, Site.armArgsOK, Array.all_eq_true', Bool.not_eq_true'] at this
    exact ⟨v, rfl, this.1, fun a ha => this.2 a ha⟩

/-- An arm value (either side). -/
theorem armVal_spec (h : DRel f g s) {x : ID} (hx : s.armVal f x = true) :
    ∃ v, f.value? x = some v ∧ specSafeOp v.op = true ∧ ∀ a ∈ v.args, s.postVal f a = false := by
  obtain ⟨-, -, -, -, -, -, -, ha0, ha1, -⟩ := h.shape
  unfold Site.armVal at hx
  rcases Bool.or_eq_true_iff.1 hx with hx | hx
  · obtain ⟨v, hv, hs, ha⟩ := armOK_spec ha0 hx
    exact ⟨v, hv, hs, fun a h => (ha a h).1⟩
  · obtain ⟨v, hv, hs, ha⟩ := armOK_spec ha1 hx
    exact ⟨v, hv, hs, fun a h => (ha a h).1⟩

/-- Uses of arm values. -/
theorem uses_spec (h : DRel f g s) {bid : ID} (hb : bid ∈ f.blocks) {B : Block}
    (hB : f.block? bid = some B) :
    (∀ y ∈ B.values, ∀ yv, f.value? y = some yv → ∀ (k : Nat) a, yv.args[k]? = some a →
      s.useOK f bid yv k a = true) ∧ ∀ c ∈ B.controls, s.armVal f c = false := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hu, -⟩ := h.shape
  unfold Site.usesOK at hu
  have := (Array.all_eq_true'.1 hu) bid hb
  rw [hB] at this
  simp only [Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at this
  refine ⟨fun y hy yv hyv k a hk => ?_, this.2⟩
  have h1 := this.1 y hy
  rw [hyv] at h1
  simp only [List.all_eq_true, List.mem_range] at h1
  have hk' : k < yv.args.size := by
    rcases Nat.lt_or_ge k yv.args.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hk; cases hk
  have := h1 k hk'
  rwa [getElem!_pos yv.args k hk', show yv.args[k] = a from by
    rw [Array.getElem?_eq_getElem hk'] at hk; exact Option.some.inj hk] at this

/-- `dom`'s non-`Phi` values and control read nothing of `post`. -/
theorem dom_spec (h : DRel f g s) {D : Block} (hD : f.block? s.dom = some D) :
    (∀ x ∈ D.values, ∀ v, f.value? x = some v → v.op ≠ .Phi → ∀ a ∈ v.args, s.postVal f a = false) ∧
      s.postVal f s.c = false := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hd, -⟩ := h.shape
  unfold Site.domOK at hd
  rw [valsOf_eq hD] at hd
  simp only [Bool.and_eq_true, Array.all_eq_true', Bool.not_eq_true'] at hd
  refine ⟨fun x hx v hv hp a ha => ?_, hd.2⟩
  have := hd.1 x hx
  rw [hv] at this
  simp only [Bool.or_eq_true, beq_iff_eq, hp, false_or, Array.all_eq_true',
    Bool.not_eq_true'] at this
  exact this a ha

/-- `post`'s `Phi`s have two arguments, none of `post`; its other values are no parameter
reads. -/
theorem post_spec (h : DRel f g s) {P : Block} (hP : f.block? s.post = some P) :
    ∀ x ∈ P.values, ∀ v, f.value? x = some v →
      (v.op = .Phi → v.args.size = 2 ∧ ∀ a ∈ v.args, s.postVal f a = false) ∧
      (v.op ≠ .Phi → v.op ≠ .Arg ∧ v.op ≠ .ArgIntReg) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpo⟩ := h.shape
  unfold Site.postOK at hpo
  rw [valsOf_eq hP] at hpo
  intro x hx v hv
  have := (Array.all_eq_true'.1 hpo) x hx
  rw [hv] at this
  simp only at this
  by_cases hp : v.op = .Phi
  · simp only [hp, beq_self_eq_true, ite_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
      Bool.not_eq_true'] at this
    exact ⟨fun _ => this, fun h' => absurd hp h'⟩
  · simp only [show (v.op == .Phi) = false by simpa using hp, Bool.false_eq_true, ite_false,
      Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    exact ⟨fun h' => absurd h' hp, fun _ => this⟩

/-- The merged block of `g`. -/
theorem merged_spec (h : DRel f g s) :
    ∃ D P D', f.block? s.dom = some D ∧ f.block? s.post = some P ∧ g.block? s.dom = some D' ∧
      D'.id = s.dom ∧ D'.kind = P.kind ∧ D'.controls = P.controls ∧ D'.succs = P.succs ∧
      (∀ x ∈ D'.values, s.regionVal f x = true) ∧ (∀ x ∈ D.values, x ∈ D'.values) ∧
      (∀ x ∈ P.values, x ∈ D'.values) ∧ (∀ x, s.armVal f x = true → x ∈ D'.values) ∧
      (schedule g D').isSome ∧ chainedB g #[s.dom] = true ∧ chainedB f #[s.dom, s.post] = true := by
  have hm := h.parts.2.2.2.2.2.2.1
  unfold Site.mergedOK at hm
  cases hD : f.block? s.dom with
  | none => rw [hD] at hm; cases hm
  | some D =>
  cases hP : f.block? s.post with
  | none => rw [hD, hP] at hm; cases hm
  | some P =>
  cases hD' : g.block? s.dom with
  | none => rw [hD, hP, hD'] at hm; cases hm
  | some D' =>
  rw [hD, hP, hD'] at hm
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Array.contains_iff_mem] at hm
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hid, hk⟩, hc⟩, hsu⟩, hreg⟩, hDin⟩, hPin⟩, ha0⟩, ha1⟩, hsch⟩, hcg⟩, hcf⟩ := hm
  refine ⟨D, P, D', rfl, rfl, rfl, hid, hk, hc, hsu, hreg, hDin, hPin, fun x hx => ?_, hsch, hcg, hcf⟩
  unfold Site.armVal at hx
  rcases Bool.or_eq_true_iff.1 hx with hx | hx
  · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 hx
    rw [ha] at ha0
    simp only [valsOf_eq hA, Array.all_eq_true', Array.contains_iff_mem] at ha0
    exact ha0 x hxA
  · obtain ⟨a, A, ha, hA, hxA⟩ := inArm_iff.1 hx
    rw [ha] at ha1
    simp only [valsOf_eq hA, Array.all_eq_true', Array.contains_iff_mem] at ha1
    exact ha1 x hxA

/-- Every value of `f` and `g` (the tables have the same size). -/
theorem value_spec (h : DRel f g s) (x : ID) : s.valueOK f g x = true := by
  obtain ⟨-, -, -, -, hsz, -, -, hv, -⟩ := h.parts
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hv x hx
  · unfold Site.valueOK
    have h1 : f.value? x = none := by simp [Func.value?, Array.getElem?_eq_none hx]
    have h2 : g.value? x = none := by simp [Func.value?, Array.getElem?_eq_none (hsz ▸ hx)]
    rw [h1, h2]

/-- A value other than `post`'s `Phi`s is unchanged in what evaluation reads. -/
theorem semEq_of (h : DRel f g s) {x : ID}
    (hx : ∀ fv, f.value? x = some fv → s.postVal f x = true → fv.op ≠ .Phi) :
    SemEq (f.value? x) (g.value? x) ∧
      ∀ fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.type = fv.type ∧ gv.op = fv.op := by
  have hv := value_spec h x
  unfold Site.valueOK at hv
  cases hf : f.value? x with
  | none =>
    rw [hf] at hv
    cases hg : g.value? x with
    | none => exact ⟨trivial, fun _ h => nomatch h⟩
    | some _ => rw [hg] at hv; cases hv
  | some fv =>
    rw [hf] at hv
    cases hg : g.value? x with
    | none => rw [hg] at hv; cases hv
    | some gv =>
      rw [hg] at hv
      have hnc : (s.postVal f x && fv.op == .Phi) = false := by
        cases hp : s.postVal f x with
        | false => rfl
        | true => simpa using hx fv hf hp
      simp only [hnc, Bool.false_eq_true, ite_false, Bool.and_eq_true, beq_iff_eq] at hv
      obtain ⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop, hargs⟩ := hv
      exact ⟨⟨hid, hop, haux, hai, hargs⟩, fun fv' h' => by
        cases h'; exact ⟨gv, rfl, hty, hop⟩⟩

/-- `post`'s `Phi`s became `CondSelect`s. -/
theorem condSel_of (h : DRel f g s) {x : ID} {fv : Value} (hfv : f.value? x = some fv)
    (hp : s.postVal f x = true) (hph : fv.op = .Phi) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.op = .CondSelect ∧
      gv.args = #[fv.args[s.j0]!, fv.args[s.j1]!, s.c] := by
  have hv := value_spec h x
  unfold Site.valueOK at hv
  rw [hfv] at hv
  cases hg : g.value? x with
  | none => rw [hg] at hv; cases hv
  | some gv =>
    rw [hg] at hv
    simp only [hp, hph, beq_self_eq_true, Bool.and_self, ite_true, Bool.and_eq_true,
      beq_iff_eq] at hv
    obtain ⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop, hargs⟩ := hv
    exact ⟨gv, rfl, hid, hty, haux, hai, hop, hargs⟩

/-- A block outside the diamond is unchanged. -/
theorem block_spec (h : DRel f g s) {bid : ID} (hb : bid ∈ f.blocks) (hr : s.regionBlock bid = false) :
    ∃ fb gb, f.block? bid = some fb ∧ g.block? bid = some gb ∧ BlockAgree fb gb := by
  have := h.parts.2.2.2.2.2.2.2.2 bid hb
  unfold Site.blockOK at this
  rw [hr, Bool.false_or] at this
  cases hf : f.block? bid with
  | none => rw [hf] at this; cases this
  | some fb =>
  cases hg : g.block? bid with
  | none => rw [hf, hg] at this; cases this
  | some gb =>
  rw [hf, hg] at this
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨⟨hid, hv⟩, hk⟩, hc⟩, hs⟩ := this
  exact ⟨fb, gb, rfl, rfl, ⟨hid, hv, hk, hc, hs⟩⟩

end

end GoFV.Proof.BranchElim
