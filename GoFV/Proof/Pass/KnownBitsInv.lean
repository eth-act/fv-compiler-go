import GoFV.Proof.Pass.KnownBitsShift
import GoFV.Proof.AtomSim

/-!
# The source-side invariant of known bits (issue #26)

`kbOK_spec`: what known bits' checker establishes, as propositions. `kbInv`: the invariant
`AtomSim.SrcInv` of a run of the source: every register `a` has the bits its final entry
`E[a]` claims (`Gam`), on blocks of `R`. It holds at the entry (registers `poison`) and is kept by
each step: a term by the post-fixpoint condition and the transfer functions' soundness
(`tk_sound`, `shift_sound`), an atom (nothing claimed but its shape's), and an edge (its target is
in `R` by `reachOK`; each `Phi` claims no more than its argument on that live edge).
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.KnownBits GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

/-- What `kbOK` checks. -/
structure KbFacts (tabs : Tables) (f g : Func) (E : Array (Int64 × Int64)) (R : Array Bool) :
    Prop where
  atoms : atomsOK f g = true
  cf : closedOK f = true
  cg : closedOK g = true
  blocks : blocksOK f g = true
  reach : reachOK f R = true
  fix : ∀ x < f.valueTab.size, fixOK tabs f R E x = true
  rep : ∀ x < f.valueTab.size, repOK tabs f g E x = true

theorem kbOK_spec {tabs : Tables} {f g : Func} {E : Array (Int64 × Int64)} {R : Array Bool}
    (h : kbOK tabs f g E R = true) : KbFacts tabs f g E R := by
  unfold kbOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, fun x hx => (h6 x hx).1, fun x hx => (h6 x hx).2⟩

/-! ## Terminators and reachability -/

theorem succ_idx {b : Block} {k : Nat} {e : Edge} (h : Sem.succ b k = .ok (.goto e)) :
    b.succs[k]? = some e := by
  unfold Sem.succ at h
  cases hk : b.succs[k]? with
  | none => rw [hk] at h; cases h
  | some e' => rw [hk] at h; cases h; rfl

/-- A terminator's successor, and `First` takes its first one. -/
theorem stepTerm_goto_idx {fr : Frame} {b : Block} {e : Edge}
    (h : stepTerm fr b = .ok (.goto e)) : ∃ k, b.succs[k]? = some e ∧ (b.kind = .First → k = 0) := by
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact ⟨0, succ_idx h, fun _ => rfl⟩
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first
            | (cases h; done)
            | exact ⟨_, succ_idx h, fun h' => by cases h'⟩
            | (split at h <;> first
              | (cases h; done)
              | exact ⟨_, succ_idx h, fun h' => by cases h'⟩
              | (split at h <;> cases h))
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

theorem reachOK_succ {f : Func} {R : Array Bool} (h : reachOK f R = true) {p : ID} {pb : Block}
    (hp : p ∈ f.blocks) (hpb : f.block? p = some pb) (hR : R.getD p false = true) {k : Nat}
    {e : Edge} (hk : pb.succs[k]? = some e) (hF : pb.kind = .First → k = 0) :
    R.getD e.b false = true := by
  unfold reachOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  have := h.2 p hp
  simp only [hR, Bool.not_true, Bool.false_or, hpb, List.all_eq_true, List.mem_range] at this
  have hlt : k < pb.succs.size := (Array.getElem?_eq_some_iff.1 hk).1
  have h2 := this k hlt
  rw [getElem!_pos pb.succs k hlt, (Array.getElem?_eq_some_iff.1 hk).2] at h2
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h2
  rcases h2 with ⟨h3, h4⟩ | h3
  · exact absurd (hF h3) h4
  · exact h3

/-! ## The invariant -/

section
variable {tabs : Tables} {f g : Func} {E : Array (Int64 × Int64)} {R : Array Bool} {ce : CheckEnv}
  (hwf : WF ce f) (K : KbFacts tabs f g E R)
include hwf K

theorem argE_eq {v : Value} {i : Nat} (hi : i < v.args.size) : argE E v i = ent E v.args[i] := by
  simp [argE, hi]

/-- A term node keeps the invariant. -/
theorem kb_term {x : ID} {v : Value} (hv : f.value? x = some v) (ht : termOp v.op = true)
    (ρ : ID → Val) (hρ : ∀ a ∈ v.args, Gam (ent E a) (ρ a)) :
    Gam (ent E x) ((evalPure v.op (tabs.ty v.type) v.auxInt v.aux (v.args.toList.map ρ)).retype
      (tabs.ty v.type)) := by
  have hfix := K.fix x (lt_of_value? hv)
  have hph : v.op ≠ .Phi := fun h => by rw [h, termOp_phi] at ht; cases ht
  simp only [fixOK, hv, beq_iff_eq, hph, ite_false, ht, Bool.not_true, Bool.false_eq_true]
    at hfix
  have hl : ∀ i (h : i < (v.args.toList.map ρ).length), i < 2 →
      Gam (if i = 0 then argE E v 0 else argE E v 1) (v.args.toList.map ρ)[i] := by
    intro i h hi2
    have hi : i < v.args.size := by simpa using h
    simp only [List.getElem_map, Array.getElem_toList]
    have := hρ _ (Array.getElem_mem hi)
    rcases Nat.lt_or_ge i 1 with h0 | h1
    · obtain rfl : i = 0 := by omega
      simpa [argE_eq hwf K hi] using this
    · obtain rfl : i = 1 := by omega
      simpa [argE_eq hwf K hi] using this
  cases hk : kind v.op with
  | none =>
    rw [hk] at hfix
    exact gam_any _ hfix _
  | some k =>
    rw [hk] at hfix
    obtain ⟨hsem, hvalid⟩ := kind_spec hk (tabs.ty v.type) v.auxInt v.aux (v.args.toList.map ρ)
    rw [hsem]
    cases k with
    | shift s w a => exact shift_sound s w a v.auxInt _ _ hl hfix
    | _ =>
      first
      | exact (norm_retype (tk_sound (fun _ _ _ h => by cases h) hvalid _ (ent_masked _ _)
          (ent_masked _ _) _ hl) _).incl hfix

/-- An atom keeps the invariant. -/
theorem kb_atom {x : ID} {v : Value} (hv : f.value? x = some v) (ht : termOp v.op = false)
    (hph : v.op ≠ .Phi) (y : Val) : Gam (ent E x) (y.retype (tabs.ty v.type)) := by
  have hfix := K.fix x (lt_of_value? hv)
  simp only [fixOK, hv, beq_iff_eq, hph, ite_false, ht, Bool.not_false, ite_true] at hfix
  exact gam_any _ hfix y

/-- An edge the source takes from a block of `R` is live. -/
theorem kb_live {p : ID} {pb : Block} (hp : p ∈ f.blocks) (hpb : f.block? p = some pb)
    (hR : R.getD p false = true) {k : Nat} {e : Edge} (hk : pb.succs[k]? = some e)
    (hF : pb.kind = .First → k = 0) :
    e.b ∈ f.blocks ∧ R.getD e.b false = true ∧ liveIn f R e.b e.i = true := by
  obtain ⟨hmem, c, hc, hpred⟩ := hwf.succLink p pb ⟨hp, hpb⟩ k e hk
  refine ⟨hmem, reachOK_succ K.reach hp hpb hR hk hF, ?_⟩
  unfold liveIn
  simp only [Bool.or_eq_true]
  right
  simp only [hc, Option.bind_some, hpred, hR, hpb, Bool.true_and, bne_iff_ne, ne_eq,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  by_cases hfk : pb.kind = .First
  · exact .inr (hF hfk)
  · exact .inl hfk

/-- The `Phi`s of a live edge keep the invariant. -/
theorem kb_phis {fr : Frame} {b : ID} {i : Nat} (hb : b ∈ f.blocks)
    (hlive : liveIn f R b i = true) (hinv : ∀ a, Gam (ent E a) (rv fr a)) :
    PhisP tabs f (fun _ a y => Gam (ent E a) y) fr b i := by
  intro bb hbb z hz v hv hph a ha
  have hfix := K.fix z (lt_of_value? hv)
  obtain ⟨v', hv', -, hvb⟩ := hwf.valueId b bb ⟨hb, hbb⟩ z hz
  rw [hv] at hv'; cases hv'
  simp only [fixOK, hv, hph, beq_self_eq_true, ite_true, List.all_eq_true, List.mem_range] at hfix
  have hi : i < v.args.size := (Array.getElem?_eq_some_iff.1 ha).1
  have h1 := hfix i hi
  rw [hvb, hlive, getElem!_pos v.args i hi, (Array.getElem?_eq_some_iff.1 ha).2] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  exact (norm_retype (hinv a).lo _).incl h1

end

/-- **The source-side invariant of known bits**: every register has the bits its entry claims,
while the source runs a block of `R`. -/
def kbInv {tabs : Tables} {f g : Func} {E : Array (Int64 × Int64)} {R : Array Bool}
    {ce : CheckEnv} (hwf : WF ce f) (K : KbFacts tabs f g E R) : SrcInv tabs f where
  P _ a y := Gam (ent E a) y
  L b _ := b ∈ f.blocks ∧ R.getD b false = true
  start := by
    have h := K.reach
    unfold reachOK at h
    simp only [Bool.and_eq_true] at h
    exact ⟨⟨hwf.entry, h.1⟩, fun _ => Gam.poison _⟩
  poisonAtom _ _ _ := Gam.poison _
  edge p _ pb fr e _ hpb hL hinv _ _ _ hst := by
    obtain ⟨k, hk, hF⟩ := stepTerm_goto_idx hst
    obtain ⟨hm, hR, hl⟩ := kb_live hwf K hL.1 hpb hL.2 hk hF
    exact ⟨⟨hm, hR⟩, hinv, kb_phis hwf K hm hl hinv⟩
  term _ _ _ x _ v hv ht ρ hρ := kb_term hwf K hv ht ρ hρ
  atom _ _ _ x _ v hv ht hph y := kb_atom hwf K hv ht hph y

@[simp] theorem kbInv_P {tabs : Tables} {f g : Func} {E : Array (Int64 × Int64)} {R : Array Bool}
    {ce : CheckEnv} (hwf : WF ce f) (K : KbFacts tabs f g E R) (b a : ID) (y : Val) :
    (kbInv hwf K).P b a y = Gam (ent E a) y := rfl

end GoFV.Proof.KnownBits
