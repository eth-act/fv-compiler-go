import GoFV.Opt.ShortCircuitCheck
import GoFV.Proof.Checked
import GoFV.Proof.Pass.ZCSERel

/-!
# short circuit, step 1: the relation `cpaOK` establishes

`CRel tabs f g` (`cpaOK_sound`): `g` has `f`'s blocks, entry and control-flow graph; its entry
block is `f`'s with new values `news` appended, each a `ConstBool` without arguments; every
other block is unchanged; every value of `f` is unchanged but for its use count and arguments,
and a changed argument is justified (`Just`): an argument of a `Phi` along an edge out of an
`If` on that argument, replaced by a `ConstBool` of the entry holding the control's value on
that edge (`ConstOK`).
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof

/-- `c` is a `ConstBool` of `g`'s entry without arguments, of the boolean shape, holding `d`. -/
def ConstOK (tabs : Tables) (g : Func) (c : ID) (d : Bool) : Prop :=
  c ∈ (valsOf g g.entry) ∧ ∃ w, g.value? c = some w ∧ w.op = .ConstBool ∧ w.args = #[] ∧
    w.id = c ∧ w.block = g.entry ∧ (w.auxInt != 0) = d ∧ tabs.ty w.type = .bool

/-- Argument `k` of `Phi` `fv` of `f` was `fa`, the control of the `If` predecessor along edge
`k`, and became the constant `ga` it holds on that edge. -/
def Just (tabs : Tables) (f g : Func) (fv : Value) (k : Nat) (fa ga : ID) : Prop :=
  fv.op = .Phi ∧ ∃ Y e P, f.block? fv.block = some Y ∧ Y.preds[k]? = some e ∧
    f.block? e.b = some P ∧ P.kind = .If ∧ P.controls[0]? = some fa ∧
    ConstOK tabs g ga (e.i == 0)

/-- A new value: a `ConstBool` of the entry without arguments, with a `Bool` auxint. -/
def NewC (f g : Func) (x : ID) : Prop :=
  f.value? x = none ∧ ∃ w, g.value? x = some w ∧ w.op = .ConstBool ∧ w.args = #[] ∧ w.id = x ∧
    w.block = g.entry ∧ (w.auxInt = 0 ∨ w.auxInt = 1)

/-- The declarative form of `cpaOK`. -/
structure CRel (tabs : Tables) (f g : Func) : Prop where
  blocks : g.blocks = f.blocks
  entry : g.entry = f.entry
  ownAux : g.ownAux = f.ownAux
  bidLast : g.bidLast = f.bidLast
  vsize : g.valueTab.size = f.valueTab.size
  bsize : g.blockTab.size = f.blockTab.size
  other : ∀ y, y ≠ f.entry → g.block? y = f.block? y
  entryB : ∃ fE news, f.block? f.entry = some fE ∧
    g.block? f.entry = some { fE with values := fE.values ++ news } ∧ news.toList.Nodup ∧
    ∀ x ∈ news, NewC f g x
  safe : ∀ gE, g.block? g.entry = some gE → ∀ x ∈ gE.values, ∀ w, g.value? x = some w →
    ZCSE.argless w = true → ZCSE.safe tabs (ZCSE.params tabs g) w = true
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧
    { gv with args := fv.args, uses := fv.uses } = fv ∧ gv.args.size = fv.args.size ∧
    ∀ (k : Nat) (fa : ID), fv.args[k]? = some fa → ∃ ga, gv.args[k]? = some ga ∧
      (ga = fa ∨ Just tabs f g fv k fa ga)

theorem constB_sound {tabs : Tables} {g : Func} {c : ID} {d : Bool}
    (h : constB tabs g c d = true) : ConstOK tabs g c d := by
  unfold constB at h
  rw [Bool.and_eq_true, Array.contains_iff_mem] at h
  obtain ⟨hm, h⟩ := h
  refine ⟨hm, ?_⟩
  cases hw : g.value? c with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨w, rfl, h1, h2, h3, h4, h5, ?_⟩
    revert h6; cases tabs.ty w.type <;> simp

theorem argOK_sound {tabs : Tables} {f g : Func} {fv : Value} {k : Nat} {fa ga : ID}
    (h : argOK tabs f g fv k fa ga = true) : ga = fa ∨ Just tabs f g fv k fa ga := by
  unfold argOK at h
  rw [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inl h.symm
  · right
    rw [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hphi, h⟩ := h
    refine ⟨hphi, ?_⟩
    cases hY : f.block? fv.block with
    | none => simp only [hY] at h; cases h
    | some Y =>
      simp only [hY] at h
      cases he : Y.preds[k]? with
      | none => simp only [he] at h; cases h
      | some e =>
        simp only [he] at h
        cases hP : f.block? e.b with
        | none => simp only [hP] at h; cases h
        | some P =>
          simp only [hP, Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨Y, e, P, by simp [hY], by simp [he], by simp [hP], h.1.1, h.1.2, constB_sound h.2⟩

theorem cpaValOK_sound {tabs : Tables} {f g : Func} {x : ID} {fv : Value}
    (h : cpaValOK tabs f g x = true) (hf : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧
      { gv with args := fv.args, uses := fv.uses } = fv ∧ gv.args.size = fv.args.size ∧
      ∀ (k : Nat) (fa : ID), fv.args[k]? = some fa → ∃ ga, gv.args[k]? = some ga ∧
        (ga = fa ∨ Just tabs f g fv k fa ga) := by
  unfold cpaValOK at h
  rw [hf] at h
  cases hg : g.value? x with
  | none => rw [hg] at h; cases h
  | some gv =>
    rw [hg] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨gv, rfl, h1, h2, fun k fa hfa => ?_⟩
    have hk : k < fv.args.size := (Array.getElem?_eq_some_iff.1 hfa).1
    have hk' : k < gv.args.size := h2 ▸ hk
    refine ⟨gv.args[k], by simp [hk'], ?_⟩
    have := argOK_sound (h3 k hk)
    rw [getElem!_pos fv.args k hk, getElem!_pos gv.args k hk',
      (Array.getElem?_eq_some_iff.1 hfa).2] at this
    exact this

theorem newConstOK_sound {f g : Func} {x : ID} (h : newConstOK f g x = true) : NewC f g x := by
  unfold newConstOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h0, h⟩ := h
  refine ⟨by simpa using h0, ?_⟩
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff, Bool.or_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨w, rfl, h1, h2, h3, h4, h5⟩

theorem extract_split {a b : Array ID} (h : a.extract 0 b.size = b) :
    a = b ++ a.extract b.size := by
  have hle : b.size ≤ a.size := by
    have := congrArg Array.size h
    simp only [Array.size_extract] at this
    omega
  have e : a.extract 0 b.size ++ a.extract b.size a.size = a.extract 0 a.size := by
    rw [Array.extract_append_extract]; simp [hle]
  rw [h] at e
  rw [e]; simp

/-- **The checker is sound.** -/
theorem cpaOK_sound {tabs : Tables} {f g : Func} (h : cpaOK tabs f g = true) : CRel tabs f g := by
  unfold cpaOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hbl, hen⟩, how⟩, hbid⟩, hvs⟩, htab⟩, hE⟩, hval⟩ := h
  obtain ⟨hbs, htab⟩ := tabEq_spec htab
  have hother : ∀ y, y ≠ f.entry → g.block? y = f.block? y := fun y hy => by
    unfold Func.block?
    rw [htab y (by simpa using hy)]
  refine ⟨hbl, hen, how, hbid, hvs, hbs, hother, ?_, ?_, ?_⟩
  · revert hE
    cases hfE : f.block? f.entry with
    | none => intro h; cases h
    | some fE =>
      rw [hen]
      cases hgE : g.block? f.entry with
      | none => intro h; cases h
      | some gE =>
        intro h
        simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
        refine ⟨fE, gE.values.extract fE.values.size, rfl, ?_, h4, fun x hx => newConstOK_sound (h3 x hx)⟩
        rw [← extract_split h2, ← h1]
  · intro gE hgE x hx w hw ha
    revert hE
    rw [hen] at hgE ⊢
    rw [hgE]
    cases f.block? f.entry with
    | none => intro h; cases h
    | some fE =>
      intro h
      simp only [Bool.and_eq_true, Array.all_eq_true'] at h
      have := h.2 x hx
      rw [hw] at this
      simpa [ha] using this
  · intro x fv hfv
    have hx : x < f.valueTab.size := ZCSE.lt_of_value? hfv
    have := nat_all_spec hval x hx
    simp only [withPtrEq] at this
    exact cpaValOK_sound this hfv

end GoFV.Proof.ShortCirc
