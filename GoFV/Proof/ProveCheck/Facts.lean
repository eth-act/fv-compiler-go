import GoFV.Proof.ProveCheck.DecideSound
import GoFV.Proof.DomCert
import GoFV.Proof.Avail

/-!
# The path facts, declaratively (issue #24)

`factsOK_spec`: what `ProveCheck.factsOK` guarantees about the facts table `F` (`FactsSpec`);
`facts_anc`: the facts of a block include those of its dominator-tree ancestors.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck
  GoFV.Proof GoFV.Proof.Dom

/-- The path facts' table, as propositions. -/
structure FactsSpec (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool))) : Prop where
  entry : factsAt F f.entry = []
  entryIn : f.entry ∈ f.blocks
  entryTree : C.inTree f.entry = true
  fact : ∀ p ∈ f.blocks, C.inTree p = true → ∀ pb, f.block? p = some pb → ∀ c v,
    (c, v) ∈ factsAt F p → factOK f C p pb c = true
  up : ∀ p ∈ f.blocks, C.inTree p = true → p ≠ f.entry →
    C.up p ∈ f.blocks ∧ ∀ q ∈ factsAt F (C.up p), q ∈ factsAt F p
  succ : ∀ p ∈ f.blocks, C.inTree p = true → ∀ pb, f.block? p = some pb → ∀ k e,
    pb.succs[k]? = some e → e.b ∈ f.blocks ∧ C.inTree e.b = true ∧
      ∀ q ∈ factsAt F e.b, q ∈ factsAt F p ∨ q ∈ ownFact pb k

theorem factsOK_spec {f : Func} {C : DomCert.Cert} {F : Array (List (ID × Bool))}
    (h : factsOK f C F = true) : FactsSpec f C F := by
  unfold factsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem, Array.all_eq_true'] at h
  obtain ⟨⟨⟨he, hin⟩, ht⟩, hall⟩ := h
  refine ⟨he, hin, ht, fun p hp hpt pb hpb c v hcv => ?_, fun p hp hpt hne => ?_,
    fun p hp hpt pb hpb k e hk => ?_⟩
  · have := hall p hp
    simp only [hpt, Bool.not_true, Bool.false_or, hpb, Bool.and_eq_true, List.all_eq_true] at this
    exact this.1.1 (c, v) hcv
  · have := hall p hp
    simp only [hpt, Bool.not_true, Bool.false_or] at this
    cases hpb : f.block? p with
    | none => rw [hpb] at this; cases this
    | some pb =>
      rw [hpb] at this
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, hne, false_or,
        Array.contains_iff_mem, List.all_eq_true, List.contains_iff_mem] at this
      exact ⟨this.1.2.1, this.1.2.2⟩
  · have := hall p hp
    simp only [hpt, Bool.not_true, Bool.false_or, hpb, Bool.and_eq_true, List.all_eq_true,
      List.mem_range] at this
    have hk' : k < pb.succs.size := (Array.getElem?_eq_some_iff.1 hk).1
    have := this.2 k hk'
    rw [hk] at this
    simp only [Bool.and_eq_true, Array.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

/-- What `placed?` says. -/
theorem placed?_spec {f : Func} {c e : ID} (h : placed? f c = some e) :
    ∃ cv blk, f.value? c = some cv ∧ cv.block = e ∧ f.block? e = some blk ∧ c ∈ blk.values := by
  unfold placed? at h
  cases hc : f.value? c with
  | none => simp [hc] at h
  | some cv =>
    simp only [hc] at h
    by_cases hb : (f.block? cv.block).any (·.values.contains c) = true
    · rw [if_pos hb] at h; cases h
      cases hblk : f.block? cv.block with
      | none => rw [hblk] at hb; cases hb
      | some blk =>
        rw [hblk] at hb
        simp only [Option.any_some, Array.contains_iff_mem] at hb
        exact ⟨cv, blk, rfl, rfl, rfl, hb⟩
    · rw [if_neg hb] at h; cases h

/-- A usable fact of tree block `p`: a term placed in a strict ancestor, not listed in `p`. -/
theorem factOK_spec {f : Func} {p : ID} {pb : Block} {c : ID}
    (h : factOK f (make f) p pb c = true) (hp : parentsOK (make f) f.entry = true) :
    c ∉ pb.values ∧ ∃ cv, Placed f c cv ∧ cv.block ≠ p ∧ Anc (make f) cv.block p ∧
      termOp cv.op = true := by
  unfold factOK at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Array.contains_iff_mem] at h
  obtain ⟨hn, h⟩ := h
  refine ⟨fun hm => by simp [hm] at hn, ?_⟩
  cases hpl : placed? f c with
  | none => rw [hpl] at h; cases h
  | some e =>
    cases hc : f.value? c with
    | none => rw [hpl, hc] at h; cases h
    | some cv =>
      rw [hpl, hc] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.contains_iff_mem] at h
      obtain ⟨⟨⟨hne, hanc⟩, ht⟩, hin⟩ := h
      obtain ⟨cv', blk, hcv', hb, hblk, hcb⟩ := placed?_spec hpl
      rw [hc] at hcv'; cases hcv'
      subst hb
      exact ⟨cv, ⟨hc, hin, blk, hblk, hcb⟩, hne, (anc_iff hp).1 hanc, ht⟩

/-- **The facts of a block include those of its ancestors.** -/
theorem facts_anc {f : Func} {F : Array (List (ID × Bool))} (hF : FactsSpec f (make f) F)
    (hp : parentsOK (make f) f.entry = true) :
    ∀ k b n, b ∈ f.blocks → (make f).depthOf b = some n → k ≤ n →
      ∀ q ∈ factsAt F ((make f).walk k b), q ∈ factsAt F b
  | 0, _, _, _, _, _, q, hq => hq
  | k + 1, b, n, hb, hd, hk, q, hq => by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hne : b ≠ f.entry := fun e => by
      subst e; rw [entry_depth hp] at hd; cases hd
    have ht : (make f).inTree b = true := by simp [Cert.inTree, hd]
    obtain ⟨hup, hsub⟩ := hF.up b hb ht hne
    have hdu := ((parent_spec hp hd).2 m rfl).2
    rw [walk_succ] at hq
    exact hsub q (facts_anc hF hp k _ m hup hdu (by omega) q hq)

theorem facts_of_anc {f : Func} {F : Array (List (ID × Bool))} (hF : FactsSpec f (make f) F)
    (hp : parentsOK (make f) f.entry = true) {a b : ID} (h : Anc (make f) a b) (hb : b ∈ f.blocks) :
    ∀ q ∈ factsAt F a, q ∈ factsAt F b := by
  obtain ⟨n, k, hd, hk, rfl⟩ := h
  exact facts_anc hF hp k b n hb hd hk

end GoFV.Proof.ProveCheck
