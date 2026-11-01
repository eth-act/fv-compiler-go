import GoFV.Opt.ZCSE
import GoFV.Proof.WF

/-!
# zcse's output relation

`ZRel tabs f g`, the declarative form of the checker `GoFV.Opt.ZCSE.zrel` (`zrel_sound`): `g`
has `f`'s control-flow graph, block kinds and controls; its blocks hold `f`'s values except
for argument-free values of `g`'s entry (`EA g`, zcse's representatives), which may come from
other blocks; every value keeps its ID, op, aux, auxint and type, and each argument is kept or
replaced by an `EA g` value with the same op, aux, auxint and type (`Same`) that is not a root
(`replPure`); `EA g` values evaluate in every frame (`safe`), and the roots among them are values
of `f`'s entry (`rootEntry`).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.Opt GoFV.Opt.ZCSE

/-- `x` is an argument-free value of `g`'s entry block. -/
abbrev EA (g : Func) (x : ID) : Prop := entryArgless g x = true

/-- `fa` of `f` and `ga` of `g` are argument-free with the same op, aux, auxint and type. -/
abbrev Same (f g : Func) (fa ga : ID) : Prop := sameArgless f g fa ga = true

theorem argless_iff {v : Value} : argless v = true ↔ v.args = #[] ∧ v.op ≠ .Phi := by
  simp [argless, Array.isEmpty_iff]

theorem ea_iff {g : Func} {x : ID} :
    EA g x ↔ ∃ gE, g.block? g.entry = some gE ∧ x ∈ gE.values ∧
      ∃ v, g.value? x = some v ∧ v.args = #[] ∧ v.op ≠ .Phi := by
  unfold EA entryArgless
  cases hE : g.block? g.entry with
  | none => simp
  | some gE =>
    cases hv : g.value? x with
    | none => simp
    | some v => simp [argless_iff]

theorem same_iff {f g : Func} {fa ga : ID} :
    Same f g fa ga ↔ ∃ u w, f.value? fa = some u ∧ g.value? ga = some w ∧ u.args = #[] ∧
      u.op ≠ .Phi ∧ w.args = #[] ∧ w.op ≠ .Phi ∧ u.op = w.op ∧ u.aux = w.aux ∧
      u.auxInt = w.auxInt ∧ u.type = w.type := by
  unfold Same sameArgless
  cases hu : f.value? fa with
  | none => simp
  | some u =>
    cases hw : g.value? ga with
    | none => simp
    | some w => simp [argless_iff, and_assoc]

/-- The declarative output relation. -/
structure ZRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  vsize : g.valueTab.size = f.valueTab.size
  block : ∀ bid ∈ f.blocks, ∀ fb, f.block? bid = some fb → ∃ gb, g.block? bid = some gb ∧
    gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
    (∀ x ∈ fb.values, x ∈ gb.values ∨ EA g x) ∧ (∀ x ∈ gb.values, x ∈ fb.values ∨ EA g x)
  safe : ∀ x, EA g x → ∃ v, g.value? x = some v ∧ safe tabs (params tabs g) v = true
  rootEntry : ∀ x, EA g x → ∀ v, g.value? x = some v → Sem.isRoot v.op = true →
    ∃ fE, f.block? f.entry = some fE ∧ x ∈ fE.values
  value : ∀ x fv, f.value? x = some fv → ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧
    gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ gv.type = fv.type ∧
    gv.args.size = fv.args.size ∧ ∀ (k : Nat) (fa : ID), fv.args[k]? = some fa →
      ∃ ga, gv.args[k]? = some ga ∧ (ga = fa ∨ EA g ga ∧ Same f g fa ga)
  replPure : ∀ x fv gv (k : Nat) fa ga, f.value? x = some fv → g.value? x = some gv →
    fv.args[k]? = some fa → gv.args[k]? = some ga → ga ≠ fa →
    ∀ w, g.value? ga = some w → Sem.isRoot w.op = false

theorem lt_of_value? {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    x < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge x f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

/-- **The checker is sound.** -/
theorem zrel_sound {tabs : Tables} {f g : Func} (h : zrel tabs f g = true) : ZRel tabs f g := by
  unfold zrel at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hblk⟩, hsafe⟩, hval⟩ := h
  refine ⟨hcfg, hown, hsz, fun bid hb fb hfb => ?_, fun x hx => ?_, fun x hx v hv hr => ?_,
    fun x fv hfv => ?_, fun x fv gv k fa ga hfv hgv hfa hga hne w hw => ?_⟩
  · have := hblk bid hb
    unfold blockOK at this
    rw [hfb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.or_eq_true,
        Array.contains_iff_mem] at this
      obtain ⟨⟨⟨hk, hc⟩, h1⟩, h2⟩ := this
      exact ⟨gb, rfl, hk, hc, h1, h2⟩
  · obtain ⟨gE, hgE, hxE, -⟩ := ea_iff.1 hx
    have := hsafe x (by rw [hgE]; exact hxE)
    rw [hx] at this
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Option.any_eq_true] at this
    exact this.1
  · obtain ⟨gE, hgE, hxE, -⟩ := ea_iff.1 hx
    have := hsafe x (by rw [hgE]; exact hxE)
    rw [hx] at this
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
    have h2 := this.2
    unfold rootStays notRoot at h2
    rw [hv] at h2
    simp only [Option.any_some, hr, Bool.not_true, Bool.false_or] at h2
    cases hfE : f.block? f.entry with
    | none => rw [hfE] at h2; cases h2
    | some fE => rw [hfE] at h2; exact ⟨fE, rfl, by simpa using h2⟩
  · have := hval x (lt_of_value? hfv)
    unfold valueOK at this
    rw [hfv] at this
    cases hgv : g.value? x with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Bool.or_eq_true] at this
      obtain ⟨⟨⟨⟨⟨⟨hid, hop⟩, hax⟩, hai⟩, hty⟩, hsz'⟩, hargs⟩ := this
      refine ⟨gv, rfl, hid, hop, hax, hai, hty, hsz', fun k fa hfa => ?_⟩
      have hk : k < fv.args.size := (Array.getElem?_eq_some_iff.1 hfa).1
      have hk' : k < gv.args.size := hsz' ▸ hk
      have hfa' : fv.args[k]! = fa := by
        rw [getElem!_pos fv.args k hk]; exact (Array.getElem?_eq_some_iff.1 hfa).2
      refine ⟨gv.args[k], by simp [hk'], ?_⟩
      rcases hargs k hk with h1 | ⟨⟨h2, h3⟩, -⟩
      · left; rw [← hfa', h1, getElem!_pos gv.args k hk']
      · right
        rw [getElem!_pos gv.args k hk'] at h2 h3
        rw [hfa'] at h3
        exact ⟨h2, h3⟩
  · have := hval x (lt_of_value? hfv)
    unfold valueOK at this
    rw [hfv, hgv] at this
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Bool.or_eq_true] at this
    have hk : k < fv.args.size := (Array.getElem?_eq_some_iff.1 hfa).1
    have hk' : k < gv.args.size := (Array.getElem?_eq_some_iff.1 hga).1
    have e1 : fv.args[k]! = fa := by
      rw [getElem!_pos fv.args k hk]; exact (Array.getElem?_eq_some_iff.1 hfa).2
    have e2 : gv.args[k]! = ga := by
      rw [getElem!_pos gv.args k hk']; exact (Array.getElem?_eq_some_iff.1 hga).2
    rcases this.2 k hk with h1 | ⟨-, h3⟩
    · exact absurd (by rw [← e1, ← e2, h1]) hne
    · rw [e2] at h3
      unfold notRoot at h3
      rw [hw] at h3
      simpa using h3

end GoFV.Proof.ZCSE
