import GoFV.Proof.ProveCheck.Facts
import GoFV.Proof.AtomSimOK

/-!
# The checked relation `proveRel`, declaratively (issue #24)

`proveRel_spec`: what `ProveCheck.proveRel tabs f g` guarantees (`RelSpec`): the atoms and
terminators of the atom simulation, every block a dominator-tree block, the path facts
(`FactsSpec`), the `Phi` invariants (`InvSpec`), and per listed value of `f` its block,
definition (`sameDef`) or a justified rewrite (`valueOK`), per block its terminator or a
justified branch removal (`branchOK`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck
  GoFV.Proof GoFV.Proof.Dom

/-- The `Phi` invariants hold on every incoming edge, assuming them all. -/
def InvSpec (tabs : Tables) (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) : Prop :=
  ∀ z w r, (z, w, r) ∈ inv → ∃ zv, f.value? z = some zv ∧ zv.op = .Phi ∧ intAt tabs zv w = true ∧
    ∀ a fs, (a, fs) ∈ phiEdges f C F z → (∃ av, f.value? a = some av ∧ intAt tabs av w = true) ∧
      (rng f.value? tabs { facts := fs, inv } rngFuel w a).sub r = true

/-- One listed value of `f`: kept, or rewritten justifiably under its block's assumptions. -/
def ValSpec (tabs : Tables) (f g : Func) (A : Asm) (gb : Block) (x : ID) : Prop :=
  x ∈ gb.values ∧ ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ gv.block = fv.block ∧
    (sameDef fv gv = true ∨ valueOK f.value? tabs A fv gv = true)

/-- `proveRel` as propositions. -/
structure RelSpec (tabs : Tables) (f g : Func) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) : Prop where
  atoms : atomsOK f g = true
  closedF : closedOK f = true
  closedG : closedOK g = true
  tree : ∀ b ∈ f.blocks, (make f).inTree b = true
  hF : FactsSpec f (make f) F
  hinv : InvSpec tabs f (make f) F inv
  blocks : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
    (fb.kind = gb.kind ∧ fb.controls = gb.controls ∧ fb.succs = gb.succs ∨
      branchOK f.value? tabs { facts := factsAt F b, inv } fb gb = true) ∧
    ∀ x ∈ fb.values, ValSpec tabs f g { facts := factsAt F b, inv } gb x

theorem invOK_spec {tabs : Tables} {f : Func} {C : DomCert.Cert} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} (h : invOK f tabs C F inv inv = true) :
    InvSpec tabs f C F inv := by
  intro z w r hz
  unfold invOK at h
  rw [List.all_eq_true] at h
  have := h _ hz
  simp only [Bool.and_eq_true, List.all_eq_true] at this
  obtain ⟨hp, he⟩ := this
  cases hzv : f.value? z with
  | none => rw [hzv] at hp; cases hp
  | some zv =>
    rw [hzv] at hp
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hp
    refine ⟨zv, rfl, hp.1, hp.2, fun a fs hm => ?_⟩
    have := he (a, fs) hm
    simp only [Bool.and_eq_true] at this
    obtain ⟨h1, h2⟩ := this
    cases hav : f.value? a with
    | none => rw [hav] at h1; cases h1
    | some av => rw [hav] at h1; exact ⟨⟨av, rfl, by simpa using h1⟩, h2⟩

theorem valuesOK_spec {tabs : Tables} {f g : Func} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} (h : valuesOK tabs f g F inv = true) :
    ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
      (fb.kind = gb.kind ∧ fb.controls = gb.controls ∧ fb.succs = gb.succs ∨
        branchOK f.value? tabs { facts := factsAt F b, inv } fb gb = true) ∧
      ∀ x ∈ fb.values, ValSpec tabs f g { facts := factsAt F b, inv } gb x := by
  intro b hb fb hfb
  unfold valuesOK at h
  rw [Array.all_eq_true'] at h
  have := h b hb
  rw [hfb] at this
  cases hgb : g.block? b with
  | none => rw [hgb] at this; cases this
  | some gb =>
    rw [hgb] at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.all_eq_true'] at this
    obtain ⟨hk, hv⟩ := this
    refine ⟨gb, rfl, ?_, fun x hx => ?_⟩
    · rcases hk with ⟨⟨h1, h2⟩, h3⟩ | h4
      · exact .inl ⟨h1, h2, h3⟩
      · exact .inr h4
    · have := hv x hx
      simp only [Bool.and_eq_true, Array.contains_iff_mem] at this
      obtain ⟨hxg, hd⟩ := this
      cases hfv : f.value? x with
      | none => rw [hfv] at hd; cases hd
      | some fv =>
        cases hgv : g.value? x with
        | none => rw [hfv, hgv] at hd; cases hd
        | some gv =>
          rw [hfv, hgv] at hd
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hd
          exact ⟨hxg, fv, gv, hfv, hgv, hd.1, hd.2⟩

theorem proveRel_spec {tabs : Tables} {f g : Func} (h : proveRel tabs f g = true) :
    RelSpec tabs f g (asmOf f tabs).2.1 (asmOf f tabs).2.2 := by
  unfold proveRel at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨ha, hcf⟩, hcg⟩, ht⟩, hfacts⟩, hinv⟩, hvals⟩ := h
  exact { atoms := ha, closedF := hcf, closedG := hcg,
          tree := fun b hb => (Array.all_eq_true'.1 ht) b hb,
          hF := factsOK_spec hfacts, hinv := invOK_spec hinv, blocks := valuesOK_spec hvals }

/-- A `Phi`'s incoming edge from a tree block is among `phiEdges`. -/
theorem mem_phiEdges {f : Func} {C : DomCert.Cert} {F : Array (List (ID × Bool))} {z h : ID}
    {zv : Value} {hb pb : Block} {i : Nat} {e : Edge} {a : ID}
    (hz : f.value? z = some zv) (hzb : zv.block = h) (hhb : f.block? h = some hb)
    (hzm : z ∈ hb.values) (he : hb.preds[i]? = some e) (ha : zv.args[i]? = some a)
    (ht : C.inTree e.b = true) (hpb : f.block? e.b = some pb) :
    (a, ownFact pb e.i ++ factsAt F e.b) ∈ phiEdges f C F z := by
  have hpl : placed? f z = some h := by
    unfold placed?; rw [hz]; simp only [← hzb] at hhb ⊢; rw [hhb]; simp [hzm]
  unfold phiEdges
  rw [hpl, hz]
  simp only [hhb]
  refine List.mem_filterMap.2 ⟨i, List.mem_range.2 (Array.getElem?_eq_some_iff.1 he).1, ?_⟩
  rw [he, ha]
  simp [ht, hpb]

end GoFV.Proof.ProveCheck
