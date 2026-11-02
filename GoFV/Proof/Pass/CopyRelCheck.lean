import GoFV.Opt.CopyRelCheck
import GoFV.Proof.Pass.CopyElimSim

/-!
# `Phi`s turned copies: `copyOK` gives copyelim's `CopyRel` (issues #32, #69)

`copyOK_spec`: if `CopyCheck.copyOK tabs k g` accepts, `g` is related to `k` by copyelim's static
relation (`CopyElim.CopyRel tabs k g`: a `Phi` of `k` that `phielimValue` turned into `Copy w`
(sccp's `removeEdge`, `applyRewrite`) has only arguments `w` or copies of `w`; every other value
is unchanged) and `k` is in copyelim's fragment `EmptyFrag`, so `g` refines `k` when both pass
`check` (`CopyElim.refines_of_rel`).
-/

namespace GoFV.Proof.CopyRelCheck

open GoFV.SSA GoFV.Opt GoFV.Opt.CopyCheck GoFV.Proof.CopyElim

theorem copyValueOK_spec {tabs : Tables} {k g : Func} {x : ID}
    (H : copyValueOK tabs k g x = true) :
    (∀ kv, k.value? x = some kv → ∃ gv, g.value? x = some gv ∧ gv.block = kv.block ∧
      gv.type = kv.type ∧ zeroSizeAggregate tabs kv.type ≠ .ok true ∧ ValRel tabs g kv gv) ∧
    (∀ gv w, g.value? x = some gv → gv.op = .Copy → gv.args = #[w] →
      ∃ wv, g.value? w = some wv ∧ RetypeInto (tabs.ty wv.type) (tabs.ty gv.type)) := by
  unfold copyValueOK at H
  rw [Bool.and_eq_true] at H
  obtain ⟨H1, H2⟩ := H
  constructor
  · intro kv hkv
    rw [hkv] at H1
    cases hgv : g.value? x with
    | none => rw [hgv] at H1; cases H1
    | some gv =>
      rw [hgv] at H1
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at H1
      obtain ⟨⟨⟨hb, hty⟩, hz⟩, hrel⟩ := H1
      refine ⟨gv, rfl, hb, hty, fun h => by simp [h] at hz, ?_⟩
      rcases hrel with ⟨⟨⟨hop, hax⟩, hai⟩, hargs⟩ | ⟨⟨⟨hph, hcp⟩, h1⟩, hall⟩
      · exact .same hop hax hai (by rw [hargs])
          (fun j a ha => ⟨a, by rw [hargs]; exact ha, .inl rfl⟩)
      · refine .phi _ hph hcp h1 (fun a ha => ?_)
        have := (Array.all_eq_true_iff_forall_mem.1 hall) a ha
        unfold copyArg at this
        simp only [Bool.or_eq_true, beq_iff_eq, Option.any_eq_true, Bool.and_eq_true] at this
        rcases this with h | ⟨u, hu, hop, hargs⟩
        · exact .inl h
        · exact .inr ⟨u, hu, hop, hargs⟩
  · intro gv w hgv hop hargs
    rw [hgv] at H2
    simp only [Option.all_some, Bool.or_eq_true, bne_iff_ne, ne_eq] at H2
    have hsz : gv.args.size = 1 := by rw [hargs]; rfl
    have h0 : gv.args[0]! = w := by rw [hargs]; rfl
    rcases H2 with (h | h) | h
    · exact absurd hop h
    · exact absurd hsz h
    · rw [h0] at h
      obtain ⟨wv, hwv, hr⟩ := (Option.any_eq_true _ _).1 h
      exact ⟨wv, hwv, (retypeEqB_sound hr).into⟩

/-- **`copyOK` gives `CopyRel` and `EmptyFrag`.** -/
theorem copyOK_spec {tabs : Tables} {k g : Func} (H : copyOK tabs k g = true) :
    CopyRel tabs k g ∧ EmptyFrag tabs k := by
  unfold copyOK at H
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at H
  obtain ⟨⟨⟨hcfg, hown⟩, hsz⟩, hbl⟩ := H
  have hblk : ∀ bid ∈ k.blocks, ∀ kb, k.block? bid = some kb →
      ∃ gb, g.block? bid = some gb ∧ gb.kind = kb.kind ∧ gb.values = kb.values ∧
        gb.controls = kb.controls ∧ ∀ x ∈ kb.values, copyValueOK tabs k g x = true := by
    intro bid hb kb hkb
    have := hbl bid hb
    rw [hkb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at this
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
      exact ⟨gb, rfl, h1, h2, h3, h4⟩
  refine ⟨⟨hcfg, hown, hsz, ?_, ?_, ?_⟩, ⟨?_⟩⟩
  · intro bid hb _ kb hkb
    obtain ⟨gb, hgb, h1, h2, h3, -⟩ := hblk bid hb kb hkb
    exact ⟨gb, hgb, h1, h2, by rw [h3], fun j c hc => ⟨c, by rw [h3]; exact hc, .inl rfl⟩⟩
  · intro bid hb _ kb hkb x hx kv hkv
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    obtain ⟨gv, hgv, hbk, hty, -, hrel⟩ := (copyValueOK_spec (h4 x hx)).1 kv hkv
    exact ⟨gv, hgv, hbk, hty, hrel⟩
  · intro bid hb _ kb hkb x hx gv w hgv hop hargs
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    exact (copyValueOK_spec (h4 x hx)).2 gv w hgv hop hargs
  · intro bid hb _ kb hkb x hx kv hkv hz'
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    obtain ⟨-, -, -, -, hz, -⟩ := (copyValueOK_spec (h4 x hx)).1 kv hkv
    exact absurd hz' hz

end GoFV.Proof.CopyRelCheck
