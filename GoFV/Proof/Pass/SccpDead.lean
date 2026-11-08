import GoFV.Opt.SccpCheck
import GoFV.Proof.Pass.DeadSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# sccp's removed edges: `deadOK` gives deadcode's `DeadRel` (issue #32)

`deadOK_spec`: if `Sccp.deadOK h g` accepts, `g` keeps all of `h`'s blocks, values and the edges a
run can take (`Dead.DeadRel h g (· ∈ g.blocks)`), so `g` refines `h` when both are well formed
(`Dead.refines_of_deadRel`). sccp's intermediate function `h` has a `First` block wherever
`replaceConst` rewires an `If` or `JumpTable` to `Plain`; its successors but 0 are the edges
`removeEdge` drops (in sccp's second intermediate function, where `Phi`s only lose arguments).
-/

namespace GoFV.Proof.Sccp

open GoFV.SSA GoFV.Opt GoFV.Opt.Sccp GoFV.Proof GoFV.Proof.Dead

theorem phiArgsOK_spec {h g : Func} {c : ID} {iS iT : Nat} (H : phiArgsOK h g c iS iT = true) :
    PhiArgs h g c iS iT := by
  intro gc hgc x hx gv hgv hph
  unfold phiArgsOK at H
  rw [hgc] at H
  have := (Array.all_eq_true_iff_forall_mem.1 H) x hx
  simp only [hgv, hph, bne_self_eq_false, Bool.false_or] at this
  cases hhv : h.value? x with
  | none => rw [hhv] at this; cases this
  | some hv =>
    rw [hhv] at this
    exact ⟨hv, rfl, by simpa using this⟩

theorem valueOK_spec {h g : Func} {x : ID} (H : valueOK h g x = true) {gv : Value}
    (hgv : g.value? x = some gv) :
    ∃ fv, h.value? x = some fv ∧ gv.type = fv.type ∧ (gv.op = .Phi ↔ fv.op = .Phi) ∧
      (gv.op ≠ .Phi → gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
        gv.args = fv.args) := by
  unfold valueOK at H
  rw [hgv] at H
  cases hhv : h.value? x with
  | none => rw [hhv] at H; cases H
  | some hv =>
    rw [hhv] at H
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at H
    obtain ⟨⟨hty, hph⟩, hrest⟩ := H
    refine ⟨hv, rfl, hty, ?_, fun hne => ?_⟩
    · constructor
      · intro h1; rw [h1] at hph; simp at hph; exact hph
      · intro h1; rw [h1] at hph; simpa using hph
    · rcases hrest with h1 | ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      · exact absurd h1 hne
      · exact ⟨h1, h2, h3, h4⟩

theorem deadBlockOK_spec {h g : Func} {hb gb : Block} (H : deadBlockOK h g hb gb = true) :
    KindRel hb.kind gb.kind ∧ gb.controls = hb.controls ∧ (∀ x ∈ gb.values, x ∈ hb.values) ∧
    (∀ (k : Nat) (e : Edge), hb.succs[k]? = some e → (hb.kind = .First → k = 0) →
      ∃ e', gb.succs[k]? = some e' ∧ e'.b = e.b ∧ e.b ∈ g.blocks ∧ PhiArgs h g e.b e.i e'.i) ∧
    (∀ x ∈ gb.values, valueOK h g x = true) ∧
    (∀ x ∈ hb.values, x ∉ gb.values → ∀ fv, h.value? x = some fv → ¬ Panicking fv.op) := by
  unfold deadBlockOK at H
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.all_eq_true',
    Array.contains_iff_mem, List.all_eq_true, List.mem_range] at H
  obtain ⟨⟨⟨⟨⟨hk, hc⟩, hv⟩, he⟩, hval⟩, hdrop⟩ := H
  refine ⟨?_, hc, hv, fun k e hke hF => ?_, hval, fun x hx hng fv hfv hp => ?_⟩
  · rcases hk with hk | ⟨h1, h2⟩
    · exact .inl hk
    · exact .inr ⟨h1, h2⟩
  · have hlt : k < hb.succs.size := (Array.getElem?_eq_some_iff.1 hke).1
    rcases he k hlt with ⟨hF', hk0⟩ | h1
    · exact absurd (hF hF') (by simpa using hk0)
    · rw [hke] at h1
      cases hge : gb.succs[k]? with
      | none => rw [hge] at h1; cases h1
      | some e' =>
        rw [hge] at h1
        simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem] at h1
        obtain ⟨⟨h2, h3⟩, h4⟩ := h1
        exact ⟨e', rfl, h2, h3, phiArgsOK_spec h4⟩
  · rcases hdrop x hx with h1 | h1
    · exact hng h1
    · rw [hfv] at h1
      simp only [Option.all_some, Bool.not_eq_true', Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        at h1
      rcases hp with hp | hp
      · rw [hp] at h1; cases h1.1
      · exact h1.2 hp

/-- **`deadOK` gives `DeadRel`.** -/
theorem deadOK_spec {h g : Func} (H : deadOK h g = true) : DeadRel h g (· ∈ g.blocks) := by
  unfold deadOK at H
  simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem, List.all_eq_true,
    List.mem_range, Array.all_eq_true'] at H
  obtain ⟨⟨⟨⟨⟨hen, hown⟩, hsz⟩, hentry⟩, hvb⟩, hbl⟩ := H
  have hblk : ∀ bid ∈ g.blocks, ∀ gb, g.block? bid = some gb →
      ∃ hb, h.block? bid = some hb ∧ bid ∈ h.blocks ∧ deadBlockOK h g hb gb = true := by
    intro bid hb gb hgb
    have := hbl bid hb
    rw [hgb] at this
    cases hhb : h.block? bid with
    | none => rw [hhb] at this; cases this
    | some fb =>
      rw [hhb] at this
      simp only [Bool.and_eq_true, Array.contains_iff_mem] at this
      exact ⟨fb, rfl, this.1, this.2⟩
  refine ⟨hen, hown, hsz, hentry, fun _ h => h, fun x gv fv hgv hfv => ?_, ?_, ?_, ?_, ?_⟩
  · have := hvb x (lt_of_value? hgv)
    rw [hgv, hfv] at this
    simpa using this
  · intro bid hb gb hgb
    obtain ⟨fb, hfb, hbm, hd⟩ := hblk bid hb gb hgb
    obtain ⟨hk, hc, hv, -⟩ := deadBlockOK_spec hd
    exact ⟨fb, hfb, hbm, hk, hc, hv⟩
  · intro bid hb gb fb hgb hfb k e hke hF
    obtain ⟨fb', hfb', -, hd⟩ := hblk bid hb gb hgb
    rw [hfb] at hfb'; cases hfb'
    exact (deadBlockOK_spec hd).2.2.2.1 k e hke hF
  · intro bid hb gb hgb x hx gv hgv
    obtain ⟨fb, -, -, hd⟩ := hblk bid hb gb hgb
    exact valueOK_spec ((deadBlockOK_spec hd).2.2.2.2.1 x hx) hgv
  · intro bid hb gb fb hgb hfb
    obtain ⟨fb', hfb', -, hd⟩ := hblk bid hb gb hgb
    rw [hfb] at hfb'; cases hfb'
    exact (deadBlockOK_spec hd).2.2.2.2.2

end GoFV.Proof.Sccp
