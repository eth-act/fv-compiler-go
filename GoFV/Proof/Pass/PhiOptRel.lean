import GoFV.Opt.PhiOptCheck
import GoFV.Proof.WF

variable [GoFV.SSA.Sem.Addrs]

/-!
# phiopt's output relation

`PRel tabs f g`, the declarative form of the checker `GoFV.Opt.PhiOpt.prel` (`prel_sound`):
`g` has `f`'s control-flow graph, block kinds and controls; its blocks hold `f`'s values and
new values (no table entry in `f`, `newOK`); every value of `f` keeps its ID, type and block,
and its op, aux, auxint and arguments unless it is a rewritten `Phi` (`rewriteOK`).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.Opt GoFV.Opt.PhiOpt

/-- The declarative output relation. -/
structure PRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : f.valueTab.size ≤ g.valueTab.size
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.controls = fb.controls ∧ (∀ x ∈ fb.values, x ∈ gb.values) ∧
    (∀ x ∈ gb.values, x ∈ fb.values ∨ (f.value? x = none ∧ newOK f g bid x = true))
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧
    gv.type = fv.type ∧ gv.block = fv.block ∧
    ((gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.args = fv.args) ∨
      rewriteOK tabs f g fv gv = true)

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

/-- **The checker is sound.** -/
theorem prel_sound {tabs : Tables} {f g : Func} (h : prel tabs f g = true) : PRel tabs f g := by
  unfold prel at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Array.all_eq_true',
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hblk⟩, hval⟩ := h
  refine ⟨hcfg, hown, hsz, fun bid hb fb hfb => ?_, fun x fv hfv => ?_⟩
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.or_eq_true,
        Array.contains_iff_mem, Option.isNone_iff_eq_none] at this
      obtain ⟨⟨⟨hk, hc⟩, h1⟩, h2⟩ := this
      exact ⟨gb, rfl, hk, hc, h1, h2⟩
  · have := hval x (lt_of_value? hfv)
    unfold valueOK at this
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
      obtain ⟨⟨⟨hid, hty⟩, hbl⟩, hr⟩ := this
      refine ⟨gv, rfl, hid, hty, hbl, ?_⟩
      rcases hr with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | h
      · exact .inl ⟨h1, h2, h3, h4⟩
      · exact .inr h

end GoFV.Proof.PhiOpt
