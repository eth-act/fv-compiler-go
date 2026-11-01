import GoFV.Proof.ProveCheck.Facts
import GoFV.Proof.AtomSimOK

/-!
# The checked relation `proveRel`, declaratively (issue #24)

`proveRel_spec`: what `ProveCheck.proveRel tabs f g` guarantees (`RelSpec`): the atoms and
terminators of the atom simulation, every block a dominator-tree block, the path facts
(`FactsSpec`), the `Phi` invariants (`InvSpec`), the relations (`RelsSpec`), and per listed
value of `f` its block, definition justified (`defOK`: kept, a value rewrite `valueOK`,
arguments folded to constants), per block its terminator or a justified branch removal
(`branchOK`).
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

/-- The relations' table, as propositions: each block's are usable there (`relHere`) and
include its tree parent's; along every edge of a tree block the successor's hold after its
`Phi`s (`relEdgeOK`). -/
structure RelsSpec (tabs : Tables) (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) : Prop where
  here : ∀ p ∈ f.blocks, C.inTree p = true → ∀ r ∈ relsAt RB p, relHere f tabs C p r = true
  up : ∀ p ∈ f.blocks, C.inTree p = true → p ≠ f.entry →
    ∀ r ∈ relsAt RB (C.up p), r ∈ relsAt RB p
  edge : ∀ p ∈ f.blocks, C.inTree p = true → ∀ pb, f.block? p = some pb → ∀ k e,
    pb.succs[k]? = some e → ∃ eb, f.block? e.b = some eb ∧
      ∀ r ∈ relsAt RB e.b, relEdgeOK f tabs F inv RB p pb k e eb r = true

/-- One listed value of `f` (listed in `fb`): its definition justified under its block's
assumptions (`defOK`). -/
def ValSpec (tabs : Tables) (f g : Func) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) (A : Asm)
    (fb gb : Block) (x : ID) : Prop :=
  x ∈ gb.values ∧ ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ gv.block = fv.block ∧
    defOK f.value? tabs F inv RB A g fb fv gv = true

/-- `proveRel` as propositions. -/
structure RelSpec (tabs : Tables) (f g : Func) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) : Prop where
  atoms : atomsOK f g = true
  closedF : closedOK f = true
  closedG : closedOK g = true
  tree : ∀ b ∈ f.blocks, (make f).inTree b = true
  hF : FactsSpec f (make f) F
  hinv : InvSpec tabs f (make f) F inv
  hrels : RelsSpec tabs f (make f) F inv RB
  blocks : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
    (fb.kind = gb.kind ∧ fb.controls = gb.controls ∧ fb.succs = gb.succs ∨
      branchOK f.value? tabs (asmAt F inv RB b) fb gb = true) ∧
    ∀ x ∈ fb.values, ValSpec tabs f g F inv RB (asmAt F inv RB b) fb gb x

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

theorem relsOK_spec {tabs : Tables} {f : Func} {C : DomCert.Cert} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} {RB : Array (List (ID × ID × Width × Int))}
    (h : relsOK f tabs C F inv RB = true) : RelsSpec tabs f C F inv RB := by
  unfold relsOK at h
  rw [Array.all_eq_true'] at h
  have key : ∀ p ∈ f.blocks, C.inTree p = true → ∃ pb, f.block? p = some pb ∧
      (relsAt RB p).all (relHere f tabs C p) = true ∧
      (p == f.entry || (relsAt RB (C.up p)).all fun r => (relsAt RB p).contains r) = true ∧
      (List.range pb.succs.size).all (fun k =>
        match pb.succs[k]? with
        | none => false
        | some e =>
          match f.block? e.b with
          | none => false
          | some eb => (relsAt RB e.b).all (relEdgeOK f tabs F inv RB p pb k e eb)) = true := by
    intro p hp ht
    have := h p hp
    simp only [ht, Bool.not_true, Bool.false_or] at this
    cases hpb : f.block? p with
    | none => rw [hpb] at this; cases this
    | some pb =>
      rw [hpb] at this
      simp only [Bool.and_eq_true] at this
      exact ⟨pb, rfl, this.1.1, this.1.2, this.2⟩
  refine ⟨fun p hp ht r hr => ?_, fun p hp ht hne r hr => ?_, fun p hp ht pb hpb k e hk => ?_⟩
  · obtain ⟨pb, -, h1, -, -⟩ := key p hp ht
    exact List.all_eq_true.1 h1 r hr
  · obtain ⟨pb, -, -, h2, -⟩ := key p hp ht
    simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, List.all_eq_true,
      List.contains_iff_mem] at h2
    exact h2 r hr
  · obtain ⟨pb', hpb', -, -, h3⟩ := key p hp ht
    rw [hpb] at hpb'; cases hpb'
    have hk' : k < pb.succs.size := (Array.getElem?_eq_some_iff.1 hk).1
    have := List.all_eq_true.1 h3 k (List.mem_range.2 hk')
    rw [hk] at this
    simp only at this
    cases heb : f.block? e.b with
    | none => rw [heb] at this; cases this
    | some eb =>
      rw [heb] at this
      exact ⟨eb, rfl, fun r hr => List.all_eq_true.1 this r hr⟩

/-- What `relEdgeOK` says: the relation's `Phi` is the successor's, with an argument along the
edge whose difference to `y` is decided; or it is not, and the source block has the
relation. -/
theorem relEdgeOK_spec {tabs : Tables} {f : Func} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} {RB : Array (List (ID × ID × Width × Int))} {p : ID}
    {pb : Block} {k : Nat} {e : Edge} {eb : Block} {z y : ID} {w : Width} {c : Int}
    (h : relEdgeOK f tabs F inv RB p pb k e eb (z, y, w, c) = true) :
    (z ∈ eb.values ∧ ∃ zv a av, f.value? z = some zv ∧ zv.args[e.i]? = some a ∧
      f.value? a = some av ∧ intAt tabs av w = true ∧
      diffDecides f.value? tabs (edgeAsm F inv RB p pb k y w) linFuel a y w c = true) ∨
    (z ∉ eb.values ∧ (z, y, w, c) ∈ relsAt RB p) := by
  unfold relEdgeOK at h
  dsimp only at h
  split at h
  · rename_i hz
    left
    refine ⟨Array.contains_iff_mem.1 hz, ?_⟩
    cases hzv : f.value? z with
    | none => rw [hzv] at h; cases h
    | some zv =>
      rw [hzv] at h
      simp only [Option.any_some] at h
      cases ha : zv.args[e.i]? with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        simp only [Bool.and_eq_true] at h
        obtain ⟨h1, h2⟩ := h
        cases hav : f.value? a with
        | none => rw [hav] at h1; cases h1
        | some av =>
          rw [hav] at h1
          exact ⟨zv, a, av, rfl, ha, hav, by simpa using h1, h2⟩
  · rename_i hz
    exact .inr ⟨fun hm => hz (Array.contains_iff_mem.2 hm), List.contains_iff_mem.1 h⟩

theorem valuesOK_spec {tabs : Tables} {f g : Func} {F : Array (List (ID × Bool))}
    {inv : List (ID × Width × Rng)} {RB : Array (List (ID × ID × Width × Int))}
    (h : valuesOK tabs f g F inv RB = true) :
    ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
      (fb.kind = gb.kind ∧ fb.controls = gb.controls ∧ fb.succs = gb.succs ∨
        branchOK f.value? tabs (asmAt F inv RB b) fb gb = true) ∧
      ∀ x ∈ fb.values, ValSpec tabs f g F inv RB (asmAt F inv RB b) fb gb x := by
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
          simp only [Bool.and_eq_true, beq_iff_eq] at hd
          exact ⟨hxg, fv, gv, hfv, hgv, hd.1, hd.2⟩

theorem proveRel_spec {tabs : Tables} {f g : Func} (h : proveRel tabs f g = true) :
    RelSpec tabs f g (asmOf f tabs).2.1 (asmOf f tabs).2.2.1 (asmOf f tabs).2.2.2 := by
  unfold proveRel at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ha, hcf⟩, hcg⟩, ht⟩, hfacts⟩, hinv⟩, hrels⟩, hvals⟩ := h
  exact { atoms := ha, closedF := hcf, closedG := hcg,
          tree := fun b hb => (Array.all_eq_true'.1 ht) b hb,
          hF := factsOK_spec hfacts, hinv := invOK_spec hinv, hrels := relsOK_spec hrels,
          blocks := valuesOK_spec hvals }

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
