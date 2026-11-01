import GoFV.Opt.DecPhiElim
import GoFV.Proof.Pass.CopyElimSim

/-!
# decompose builtin's phi eliminations: `phRelOK` gives copyelim's `CopyRel` (issue #17)

`phRelOK_spec`: if `DecPhiElim.phRelOK tabs h g` accepts, `g` is related to `h` by copyelim's
static relation (`CopyElim.CopyRel tabs h g`: a `Phi` of `h` that is `Copy w` in `g` has only
arguments `w` or copies of `w`; every other value keeps its op, aux and auxint, with arguments
the same or the argument of a copy of `g`) and `h` is in copyelim's fragment `EmptyFrag`, so
`g` refines `h` when both pass `check` (`CopyElim.refines_of_rel`).
-/

namespace GoFV.Proof.DecPhiElim

open GoFV.SSA GoFV.Opt GoFV.Opt.DecPhiElim GoFV.Proof.CopyElim

theorem phArg_spec {g : Func} {a a' : ID} (h : phArg g a a' = true) : ArgRel g a a' := by
  unfold phArg at h
  simp only [Bool.or_eq_true, beq_iff_eq, Option.any_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨u, hu, hop, hargs⟩
  · exact .inl h
  · exact .inr ⟨u, hu, hop, hargs⟩

theorem phArgs_spec {g : Func} : ∀ {as bs : List ID}, phArgs g as bs = true →
    as.length = bs.length ∧
      ∀ (k : Nat) (a : ID), as[k]? = some a → ∃ w, bs[k]? = some w ∧ ArgRel g a w
  | [], [], _ => ⟨rfl, fun k a h => by simp at h⟩
  | a :: as, b :: bs, h => by
    simp only [phArgs, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hl, ih⟩ := phArgs_spec h2
    refine ⟨by simp [hl], fun k x hx => ?_⟩
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact ⟨b, rfl, phArg_spec h1⟩
    | succ k => exact ih k x (by simpa using hx)
  | [], _ :: _, h | _ :: _, [], h => by simp [phArgs] at h

/-- `phArgs` of two argument arrays. -/
theorem phArgs_arr {g : Func} {as bs : Array ID} (h : phArgs g as.toList bs.toList = true) :
    bs.size = as.size ∧
      ∀ (k : Nat) (a : ID), as[k]? = some a → ∃ w, bs[k]? = some w ∧ ArgRel g a w := by
  obtain ⟨hl, hr⟩ := phArgs_spec h
  refine ⟨by simpa using hl.symm, fun k a ha => ?_⟩
  obtain ⟨w, hw, hrel⟩ := hr k a (by rw [Array.getElem?_toList]; exact ha)
  exact ⟨w, by rw [Array.getElem?_toList] at hw; exact hw, hrel⟩

theorem phValueOK_spec {tabs : Tables} {h g : Func} {x : ID}
    (H : phValueOK tabs h g x = true) :
    (∀ kv, h.value? x = some kv → ∃ gv, g.value? x = some gv ∧ gv.block = kv.block ∧
      gv.type = kv.type ∧ zeroSizeAggregate tabs kv.type ≠ .ok true ∧ ValRel tabs g kv gv) ∧
    (∀ gv w, g.value? x = some gv → gv.op = .Copy → gv.args = #[w] →
      ∃ wv, g.value? w = some wv ∧ RetypeEq (tabs.ty wv.type) (tabs.ty gv.type)) := by
  unfold phValueOK at H
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
      · obtain ⟨hsz, hr⟩ := phArgs_arr hargs
        exact .same hop hax hai hsz hr
      · exact .phi _ hph hcp h1 (fun a ha => phArg_spec ((Array.all_eq_true_iff_forall_mem.1 hall) a ha))
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
      exact ⟨wv, hwv, retypeEqB_sound hr⟩

/-- **`phRelOK` gives `CopyRel` and `EmptyFrag`.** -/
theorem phRelOK_spec {tabs : Tables} {h g : Func} (H : phRelOK tabs h g = true) :
    CopyRel tabs h g ∧ EmptyFrag tabs h := by
  unfold phRelOK at H
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at H
  obtain ⟨⟨⟨hcfg, hown⟩, hsz⟩, hbl⟩ := H
  have hblk : ∀ bid ∈ h.blocks, ∀ kb, h.block? bid = some kb →
      ∃ gb, g.block? bid = some gb ∧ gb.kind = kb.kind ∧ gb.values = kb.values ∧
        phArgs g kb.controls.toList gb.controls.toList = true ∧
        ∀ x ∈ kb.values, phValueOK tabs h g x = true := by
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
    obtain ⟨hcs, hc⟩ := phArgs_arr h3
    exact ⟨gb, hgb, h1, h2, hcs, hc⟩
  · intro bid hb _ kb hkb x hx kv hkv
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    obtain ⟨gv, hgv, hbk, hty, -, hrel⟩ := (phValueOK_spec (h4 x hx)).1 kv hkv
    exact ⟨gv, hgv, hbk, hty, hrel⟩
  · intro bid hb _ kb hkb x hx gv w hgv hop hargs
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    exact (phValueOK_spec (h4 x hx)).2 gv w hgv hop hargs
  · intro bid hb _ kb hkb x hx kv hkv
    obtain ⟨-, -, -, -, -, h4⟩ := hblk bid hb kb hkb
    obtain ⟨-, -, -, -, hz, -⟩ := (phValueOK_spec (h4 x hx)).1 kv hkv
    exact hz

end GoFV.Proof.DecPhiElim
