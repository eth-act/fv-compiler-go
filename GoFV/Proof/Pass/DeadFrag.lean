import GoFV.Proof.Pass.DeadRel

/-!
# Deciding `DeadRel` and `NoNil`

`deadRelB f g` decides `DeadRel f g` (`deadRelB_sound`); `noNilB` decides `NoNil`
(`noNil_of`). `Chained` is decided by `chainedB` (`GoFV.Proof.Pass.DeadChain`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

def panickingB (op : Op) : Bool :=
  op == .PanicBounds || op == .StaticLECall || op == .StaticCall || op == .NilCheck

theorem panickingB_false {op : Op} (h : panickingB op = false) : ¬ Panicking op := by
  unfold panickingB at h; unfold Panicking
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne] at h
  rintro (h' | h' | h' | h') <;> simp_all

def kindRelB (fk gk : BlockKind) : Bool := gk == fk || (fk == .First && gk == .Plain)

theorem kindRelB_sound {fk gk : BlockKind} (h : kindRelB fk gk = true) : KindRel fk gk := by
  unfold kindRelB at h; unfold KindRel
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] using h

def phiArgsB (f g : Func) (c : ID) (iS iT : Nat) : Bool :=
  match g.block? c with
  | none => true
  | some gc => gc.values.all fun x =>
    match g.value? x with
    | some gv => gv.op != .Phi || (f.value? x).any (fun fv => gv.args[iT]? == fv.args[iS]?)
    | none => true

theorem phiArgsB_sound {f g : Func} {c : ID} {iS iT : Nat} (h : phiArgsB f g c iS iT = true) :
    PhiArgs f g c iS iT := by
  intro gc hgc x hx gv hgv hph
  unfold phiArgsB at h
  rw [hgc, Array.all_eq_true'] at h
  have := h x hx
  rw [hgv] at this
  simp only [hph, bne_self_eq_false, Bool.false_or, Option.any_eq_true, beq_iff_eq] at this
  exact this

/-- The checks of one kept block `bid` (`gb` in `g`, `fb` in `f`). -/
def blockB (f g : Func) (bid : ID) (gb fb : Block) : Bool :=
  f.blocks.contains bid && kindRelB fb.kind gb.kind && gb.controls == fb.controls &&
  gb.values.all (fb.values.contains ·) &&
  (List.range fb.succs.size).all (fun k => (fb.kind == .First && k != 0) ||
    match fb.succs[k]?, gb.succs[k]? with
    | some e, some e' => e'.b == e.b && phiArgsB f g e.b e.i e'.i
    | _, _ => false) &&
  gb.values.all (fun x =>
    match g.value? x, f.value? x with
    | some gv, some fv => gv.type == fv.type && ((gv.op == .Phi) == (fv.op == .Phi)) &&
        (gv.op == .Phi || (gv.op == fv.op && gv.aux == fv.aux && decide (gv.auxInt = fv.auxInt) &&
          gv.args == fv.args))
    | some _, none => false
    | none, _ => true) &&
  fb.values.all (fun x => gb.values.contains x ||
    match f.value? x with
    | some fv => !panickingB fv.op
    | none => true)

/-- Decides `DeadRel`. -/
def deadRelB (f g : Func) : Bool :=
  g.entry == f.entry && g.ownAux == f.ownAux && g.valueTab.size == f.valueTab.size &&
  g.blocks.all fun bid =>
    match g.block? bid, f.block? bid with
    | some gb, some fb => blockB f g bid gb fb
    | some _, none => false
    | none, _ => false

theorem deadRelB_blocks {f g : Func} (h : deadRelB f g = true) :
    ∀ bid ∈ g.blocks, bid ∈ f.blocks := by
  intro bid hb
  unfold deadRelB at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  have := h.2 bid hb
  split at this
  · unfold blockB at this
    simp only [Bool.and_eq_true] at this
    simpa using this.1.1.1.1.1.1
  · cases this
  · cases this

theorem deadRelB_sound {f g : Func} (h : deadRelB f g = true) : DeadRel f g := by
  unfold deadRelB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨he, ho⟩, hv⟩, hb⟩ := h
  -- the block checks, for a kept block
  have hB : ∀ bid ∈ g.blocks, ∀ gb, g.block? bid = some gb →
      ∃ fb, f.block? bid = some fb ∧ blockB f g bid gb fb = true := by
    intro bid hm gb hgb
    have := hb bid hm
    rw [hgb] at this
    cases hfb : f.block? bid with
    | none => rw [hfb] at this; cases this
    | some fb => rw [hfb] at this; exact ⟨fb, rfl, this⟩
  have hparts : ∀ {bid gb fb}, blockB f g bid gb fb = true →
      bid ∈ f.blocks ∧ KindRel fb.kind gb.kind ∧ gb.controls = fb.controls ∧
      (∀ x ∈ gb.values, x ∈ fb.values) ∧
      (∀ k < fb.succs.size, (fb.kind = .First ∧ k ≠ 0) ∨
        ∃ e e', fb.succs[k]? = some e ∧ gb.succs[k]? = some e' ∧ e'.b = e.b ∧
          PhiArgs f g e.b e.i e'.i) ∧
      (∀ x ∈ gb.values, ∀ gv, g.value? x = some gv → ∃ fv, f.value? x = some fv ∧
        gv.type = fv.type ∧ (gv.op = .Phi ↔ fv.op = .Phi) ∧
        (gv.op ≠ .Phi → gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
          gv.args = fv.args)) ∧
      (∀ x ∈ fb.values, x ∉ gb.values → ∀ fv, f.value? x = some fv → ¬ Panicking fv.op) := by
    intro bid gb fb h
    unfold blockB at h
    simp only [Bool.and_eq_true, Array.all_eq_true', List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
    refine ⟨by simpa using h1, kindRelB_sound h2, by simpa using h3,
      fun x hx => by simpa using h4 x hx, fun k hk => ?_, fun x hx gv hgv => ?_,
      fun x hx hn fv hfv => ?_⟩
    · have := h5 k hk
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
      rcases this with h | h
      · exact .inl h
      · right
        split at h
        · rename_i e e' he he'
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨e, e', he, he', h.1, phiArgsB_sound h.2⟩
        · cases h
    · have := h6 x hx
      rw [hgv] at this
      cases hfv : f.value? x with
      | none => rw [hfv] at this; cases this
      | some fv =>
        rw [hfv] at this
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
        obtain ⟨⟨hty, hph⟩, hs⟩ := this
        refine ⟨fv, rfl, hty, ?_, fun hn => ?_⟩
        · constructor
          · intro hp; rw [hp] at hph; simpa using hph.symm
          · intro hp; rw [hp] at hph; simpa using hph
        · rcases hs with hs | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
          · exact absurd hs hn
          · exact ⟨h1, h2, h3, h4⟩
    · have := h7 x hx
      simp only [Bool.or_eq_true, hfv] at this
      rcases this with h | h
      · exact absurd (by simpa using h) hn
      · exact panickingB_false (by simpa using h)
  refine ⟨he, ho, hv, fun bid hm gb hgb => ?_, fun bid hm gb fb hgb hfb k e he hf => ?_,
    fun bid hm gb hgb x hx gv hgv => ?_, fun bid hm gb fb hgb hfb => ?_⟩
  · obtain ⟨fb, hfb, hB'⟩ := hB bid hm gb hgb
    obtain ⟨p1, p2, p3, p4, -⟩ := hparts hB'
    exact ⟨fb, hfb, p1, p2, p3, p4⟩
  · obtain ⟨fb', hfb', hB'⟩ := hB bid hm gb hgb
    rw [hfb] at hfb'; cases hfb'
    obtain ⟨-, -, -, -, p5, -⟩ := hparts hB'
    have hk : k < fb.succs.size := (Array.getElem?_eq_some_iff.1 he).1
    rcases p5 k hk with ⟨hF, hk0⟩ | ⟨e1, e', he1, he', hb', hP⟩
    · exact absurd (hf hF) hk0
    · rw [he] at he1; cases he1
      exact ⟨e', he', hb', hP⟩
  · obtain ⟨fb, -, hB'⟩ := hB bid hm gb hgb
    exact (hparts hB').2.2.2.2.2.1 x hx gv hgv
  · obtain ⟨fb', hfb', hB'⟩ := hB bid hm gb hgb
    rw [hfb] at hfb'; cases hfb'
    exact (hparts hB').2.2.2.2.2.2

/-- Decides `NoNil`. -/
def noNilB (f : Func) : Bool :=
  f.valueTab.all fun o => match o with
    | some v => v.op != .NilCheck
    | none => true

theorem noNil_of {f : Func} (h : noNilB f = true) : NoNil f := by
  intro x fv hfv hop
  unfold noNilB at h
  rw [Array.all_eq_true'] at h
  unfold Func.value? at hfv
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at hfv; cases hfv
  | some o =>
    rw [hx] at hfv
    have := h o (Array.mem_of_getElem? hx)
    cases o with
    | none => cases hfv
    | some v =>
      simp only [Option.join] at hfv
      cases hfv
      simp [hop] at this

end GoFV.Proof.Dead
