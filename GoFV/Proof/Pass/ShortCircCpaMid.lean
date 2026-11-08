import GoFV.Proof.Pass.ShortCircCpaWF
import GoFV.Proof.Pass.ZCSESetup

variable [GoFV.SSA.Sem.Addrs]

/-!
# short circuit, step 1: the result and its intermediate are extensions; zcse's relation

`CRel.ext_g`, `CRel.ext_mid`: the result `g` and `mid f g` extend `f` (`Ext`). `CRel.zrel_mid`:
`mid f g` (`f` with the new constants in its entry) is related to `f` by zcse's relation
`ZCSE.ZRel`, so it refines `f` by `ZCSE.refines_of_rel`.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

variable {tabs : Tables} {f g : Func}

theorem value_fields {fv gv : Value} (h : { gv with args := fv.args, uses := fv.uses } = fv) :
    gv.id = fv.id ∧ gv.op = fv.op ∧ gv.block = fv.block ∧ gv.auxInt = fv.auxInt ∧
      gv.aux = fv.aux ∧ gv.type = fv.type ∧ gv.pos = fv.pos := by
  exact ⟨by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h]⟩

theorem value_eta {fv gv : Value} (h : { gv with args := fv.args, uses := fv.uses } = fv) :
    { gv with args := fv.args } = { fv with uses := gv.uses } := by
  rw [← h]

theorem args_eq_of {a b : Array ID} (hs : a.size = b.size)
    (h : ∀ (k : Nat) (x : ID), b[k]? = some x → a[k]? = some x) : a = b := by
  apply Array.ext hs
  intro k h1 h2
  have := h k b[k] (by simp [h2])
  rw [Array.getElem?_eq_getElem h1] at this
  exact Option.some.inj this

theorem blockTab_get {h : Func} {y : ID} (hy : y < h.blockTab.size) :
    h.blockTab[y] = h.block? y := by
  unfold Func.block?; rw [Array.getElem?_eq_getElem hy]; cases h.blockTab[y] <;> rfl

namespace CRel

variable (C : CRel tabs f g)
include C

theorem block_adj {fE : Block} {news : Array ID} (hfE : f.block? f.entry = some fE)
    (hgE : g.block? f.entry = some { fE with values := fE.values ++ news }) (y : ID) :
    g.block? y = (f.block? y).map (adj f news y) := by
  by_cases hy : y = f.entry
  · subst hy; rw [hgE, hfE]; simp [adj]
  · rw [C.other y hy]
    cases f.block? y <;> simp [adj, hy]

/-- The value of `f` in `g`, as `Ext` states it. -/
theorem ext_value {fE : Block} {news : Array ID} (hfE : f.block? f.entry = some fE)
    (hgE : g.block? f.entry = some { fE with values := fE.values ++ news })
    (x : ID) (fv : Value) (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.op = fv.op ∧ gv.block = fv.block ∧
      gv.auxInt = fv.auxInt ∧ gv.args.size = fv.args.size ∧ (fv.op ≠ .Phi → gv.args = fv.args) ∧
      ∀ (k : Nat) (a : ID), gv.args[k]? = some a → fv.args[k]? = some a ∨ a ∈ fE.values ++ news := by
  obtain ⟨gv, hgv, heq, hsz, hargs⟩ := C.value x fv hfv
  obtain ⟨h1, h2, h3, h4, -⟩ := value_fields heq
  refine ⟨gv, hgv, h1, h2, h3, h4, hsz, fun hph => args_eq_of hsz fun k a hk => ?_,
    fun k a hk => ?_⟩
  · obtain ⟨ga, hga, hor⟩ := hargs k a hk
    rcases hor with rfl | ⟨hp, -⟩
    · exact hga
    · exact absurd hp hph
  · have hk' : k < fv.args.size := hsz ▸ (Array.getElem?_eq_some_iff.1 hk).1
    obtain ⟨ga, hga, hor⟩ := hargs k fv.args[k] (by simp [hk'])
    rw [hk] at hga; cases hga
    rcases hor with h | ⟨-, -, -, -, -, -, -, -, -, hc, -⟩
    · left; rw [h]; simp [hk']
    · right
      have := hc
      rw [valsOf_eq (by rw [C.entry]; exact hgE)] at this
      exact this

theorem ext_g : ∃ fE news, Ext f g fE news := by
  obtain ⟨fE, news, hfE, hgE, hnd, hnew⟩ := C.entryB
  refine ⟨fE, news, C.blocks, C.entry, C.block_adj hfE hgE, hfE, hnd, fun x hx => ?_,
    C.ext_value hfE hgE⟩
  obtain ⟨h0, w, hw, h1, h2, h3, h4, h5⟩ := hnew x hx
  exact ⟨h0, w, hw, h1, h2, h3, by rw [h4, C.entry], h5⟩

theorem mid_of_f {x : ID} {fv : Value} (hfv : f.value? x = some fv) :
    ∃ gv, g.value? x = some gv ∧ (mid f g).value? x = some { fv with uses := gv.uses } ∧
      { gv with args := fv.args, uses := fv.uses } = fv := by
  obtain ⟨gv, hgv, heq, -⟩ := C.value x fv hfv
  refine ⟨gv, hgv, ?_, heq⟩
  rw [mid_value, hgv, hfv]
  simp only [value_eta heq]

theorem mid_of_none {x : ID} (hfv : f.value? x = none) : (mid f g).value? x = g.value? x := by
  rw [mid_value, hfv]
  cases g.value? x <;> rfl

theorem ext_mid : ∃ fE news, Ext f (mid f g) fE news := by
  obtain ⟨fE, news, hfE, hgE, hnd, hnew⟩ := C.entryB
  refine ⟨fE, news, C.blocks, C.entry, fun y => by rw [mid_block]; exact C.block_adj hfE hgE y,
    hfE, hnd, fun x hx => ?_, fun x fv hfv => ?_⟩
  · obtain ⟨h0, w, hw, h1, h2, h3, h4, h5⟩ := hnew x hx
    exact ⟨h0, w, by rw [C.mid_of_none h0]; exact hw, h1, h2, h3, by rw [h4, C.entry], h5⟩
  · obtain ⟨gv, -, hm, -⟩ := C.mid_of_f hfv
    exact ⟨_, hm, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun k a hk => .inl hk⟩

theorem cfg_mid : DomCert.cfgView (mid f g) = DomCert.cfgView f := by
  obtain ⟨fE, news, hfE, hgE, -⟩ := C.entryB
  have hb := C.block_adj hfE hgE
  unfold DomCert.cfgView
  simp only [mid, C.entry, C.bidLast, C.blocks]
  congr 1
  apply Array.ext (by simp [C.bsize])
  intro y h1 h2
  simp only [Array.getElem_map]
  have hy1 : y < g.blockTab.size := by simpa using h1
  have hy2 : y < f.blockTab.size := by simpa using h2
  rw [blockTab_get hy1, blockTab_get hy2, hb y]
  cases f.block? y with
  | none => rfl
  | some b =>
    simp only [Option.map_some]
    obtain ⟨h1, h2, h3, -⟩ := adj_fields (f := f) (news := news) (y := y) (b := b)
    rw [h1, h2, h3]

theorem ea_mid {x : ID} (hx : ZCSE.EA (mid f g) x) :
    ∃ gE, g.block? g.entry = some gE ∧ x ∈ gE.values ∧ ∃ v, g.value? x = some v ∧
      (mid f g).value? x = some v ∧ v.args = #[] ∧ v.op ≠ .Phi := by
  obtain ⟨gE, hgE, hxE, v, hv, hva, hvn⟩ := ZCSE.ea_iff.1 hx
  refine ⟨gE, hgE, hxE, ?_⟩
  cases hfv : f.value? x with
  | none => rw [C.mid_of_none hfv] at hv; exact ⟨v, hv, by rw [C.mid_of_none hfv]; exact hv, hva, hvn⟩
  | some fv =>
    obtain ⟨gv, hgv, hm, heq⟩ := C.mid_of_f hfv
    rw [hm] at hv; cases hv
    have hfa : fv.args = #[] := hva
    obtain ⟨gv', hgv', -, hsz, -⟩ := C.value x fv hfv
    rw [hgv] at hgv'; cases hgv'
    have hga : gv.args = #[] := Array.eq_empty_of_size_eq_zero (by rw [hsz, hfa]; rfl)
    have : { fv with uses := gv.uses } = gv := by
      rw [← value_eta heq, hfa, ← hga]
    exact ⟨gv, hgv, by rw [hm, this], hga, by rw [← this]; exact hvn⟩

/-- **`mid f g` is zcse's relation of `f`**: the constants are added to the entry. -/
theorem zrel_mid : ZCSE.ZRel tabs f (mid f g) where
  cfg := C.cfg_mid
  ownAux := C.ownAux
  vsize := by simp [mid, C.vsize]
  block := fun bid _ fb hfb => by
    obtain ⟨fE, news, hfE, hgE, -, hnew⟩ := C.entryB
    refine ⟨adj f news bid fb, by rw [mid_block, C.block_adj hfE hgE, hfb]; rfl,
      adj_fields.2.2.2.1, adj_fields.2.2.2.2, fun x hx => .inl (adj_values_sup hx), fun x hx => ?_⟩
    rcases adj_values hx with h | ⟨rfl, hn⟩
    · exact .inl h
    · right
      obtain ⟨h0, w, hw, hop, hargs, -⟩ := hnew x hn
      refine ZCSE.ea_iff.2 ⟨_, by rw [mid_block, show (mid f g).entry = f.entry from C.entry,
        C.block_adj hfE hgE, hfE]; rfl, ?_, w, by rw [C.mid_of_none h0]; exact hw, hargs,
        by rw [hop]; decide⟩
      unfold adj; simp only [ite_true]; exact Array.mem_append_right _ hn
  safe := fun x hx => by
    obtain ⟨gE, hgE, hxE, v, hv, hm, hva, hvn⟩ := C.ea_mid hx
    exact ⟨v, hm, C.safe gE hgE x hxE v hv (ZCSE.argless_iff.2 ⟨hva, hvn⟩)⟩
  rootEntry := fun x hx v hv hr => by
    obtain ⟨gE, hgE, hxE, v', hv', hm, -⟩ := C.ea_mid hx
    rw [hm] at hv; cases hv
    obtain ⟨fE, news, hfE, hgE', -, hnew⟩ := C.entryB
    rw [C.entry, hgE'] at hgE; cases hgE
    refine ⟨fE, hfE, ?_⟩
    rcases Array.mem_append.1 hxE with h | h
    · exact h
    · obtain ⟨-, w, hw, hop, -⟩ := hnew x h
      rw [hv'] at hw; cases hw
      rw [hop] at hr; exact absurd hr (by decide)
  value := fun x fv hfv => by
    obtain ⟨gv, -, hm, -⟩ := C.mid_of_f hfv
    exact ⟨_, hm, rfl, rfl, rfl, rfl, rfl, rfl, fun k fa hk => ⟨fa, hk, .inl rfl⟩⟩
  replPure := fun x fv gv k fa ga hfv hgv hfa hga hne => by
    obtain ⟨gv', -, hm, -⟩ := C.mid_of_f hfv
    rw [hm] at hgv; cases hgv
    rw [hfa] at hga; cases hga
    exact absurd rfl hne

end CRel

end GoFV.Proof.ShortCirc
