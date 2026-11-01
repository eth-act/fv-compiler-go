import GoFV.Proof.ProveCheck.Spec
import GoFV.Proof.AtomSimSet
import GoFV.Proof.Merge

/-!
# The source-side invariant of prove's validator (issue #24)

`proveInv`: while the source runs block `b`, every register `a` holds a value `y` that is
fixed by `retype` at `a`'s shape, is `.bool v` for every path fact `(a, v)` of `b`, and lies
in `r` for every `Phi` invariant `(a, w, r)` (`PInv`). It holds at the entry (no facts), is
kept by evaluating values (a block's own values are never its facts, `Phi`s are never terms),
and along each edge: the target's facts are the source block's plus the branch just taken, and
each `Phi`'s new value lies in its invariant's range because the range analysis is sound
(`rng_sound`) under the source block's facts (`InvSpec`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck
  GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Term GoFV.Proof.AtomSim

/-- The invariant at block `b` of register `a` holding `y`. -/
def PInv (tabs : Tables) (f : Func) (F : Array (List (ID × Bool))) (inv : List (ID × Width × Rng))
    (b a : ID) (y : Val) : Prop :=
  y.retype (shape f.value? tabs a) = y ∧
  (b ∈ f.blocks → ∀ v, (a, v) ∈ factsAt F b → y = .bool v) ∧
  (∀ w r, (a, w, r) ∈ inv → ∀ yv : BitVec w.bits, y = .int w yv → r.Mem yv)

section
variable {tabs : Tables} {f g : Func} {ce : CheckEnv} {F : Array (List (ID × Bool))}
  {inv : List (ID × Width × Rng)}

theorem shape_of {x : ID} {v : Value} (h : f.value? x = some v) :
    shape f.value? tabs x = tabs.ty v.type := by simp [shape, h]

/-- A fact of a block of `f` is not one of its values. -/
theorem fact_not_mem (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) {x : ID} (hx : x ∈ bb.values) {v : Bool}
    (hf : (x, v) ∈ factsAt F b) : False :=
  (factOK_spec (hR.hF.fact b hb (hR.tree b hb) bb hbb x v hf) hc.parents).1 hx

/-- A fact is a term placed in a strict ancestor. -/
theorem fact_placed (hc : CertOK f) (hR : RelSpec tabs f g F inv) {b : ID} {bb : Block}
    (hb : b ∈ f.blocks) (hbb : f.block? b = some bb) {x : ID} {v : Bool}
    (hf : (x, v) ∈ factsAt F b) :
    ∃ cv, Placed f x cv ∧ cv.block ≠ b ∧ Anc (make f) cv.block b ∧ termOp cv.op = true :=
  (factOK_spec (hR.hF.fact b hb (hR.tree b hb) bb hbb x v hf) hc.parents).2

theorem inv_phi (hR : RelSpec tabs f g F inv) {z : ID} {w : Width} {r : Rng}
    (hz : (z, w, r) ∈ inv) : ∃ zv, f.value? z = some zv ∧ zv.op = .Phi :=
  let ⟨zv, h1, h2, _⟩ := hR.hinv z w r hz; ⟨zv, h1, h2⟩

/-- The edge taken by a terminator, and its own fact. -/
theorem edge_taken {fr : Frame} {pb : Block} {e : Edge} (h : stepTerm fr pb = .ok (.goto e)) :
    ∃ k, pb.succs[k]? = some e ∧ ∀ c v, (c, v) ∈ ownFact pb k → fr.regs[c]? = some (some (.bool v)) := by
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 (GoFV.Proof.stepTerm_goto_mem h)
  unfold ownFact
  by_cases hkind : pb.kind = .If
  · simp only [hkind, beq_self_eq_true, ite_true]
    rcases hl : pb.controls.toList with _ | ⟨c, _ | ⟨c', l⟩⟩
    · exact ⟨k, hk, fun _ _ hm => by simp at hm⟩
    · have hc : pb.controls = #[c] := by
        apply Array.ext'; rw [hl]
      obtain ⟨b, e', hreg, he', hn⟩ := GoFV.Proof.stepTerm_if hkind hc h
      cases hn
      refine ⟨if b then 0 else 1, he', fun c0 v hm => ?_⟩
      simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      cases b <;> simpa using hreg
    · exact ⟨k, hk, fun _ _ hm => by simp at hm⟩
  · have : (pb.kind == .If) = false := by simpa using hkind
    simp only [this, Bool.false_eq_true, ite_false]
    exact ⟨k, hk, fun _ _ hm => by simp at hm⟩

/-- **The invariant.** -/
def proveInv (hwf : WF ce f) (hc : CertOK f) (hR : RelSpec tabs f g F inv) : SrcInv tabs f where
  P := PInv tabs f F inv
  L b _ := b ∈ f.blocks
  start := ⟨hwf.entry, fun a => ⟨retype_poison' _, fun _ v (hv : (a, v) ∈ factsAt F f.entry) => (by
    rw [hR.hF.entry] at hv; cases hv), fun _ _ _ _ h => (by cases h)⟩⟩
  poisonAtom b a hat := ⟨retype_poison' _, fun hb v hv => by
      obtain ⟨bb, hbb, -⟩ := hwf.blockId b hb
      obtain ⟨cv, hp, -, -, ht⟩ := fact_placed hc hR hb hbb hv
      exact absurd ⟨cv, hp.1, ht⟩ hat,
    fun _ _ _ _ h => by cases h⟩
  term b bb hbb x hx v hv ht ρ _ := by
    refine ⟨by rw [shape_of hv, Val.retype_idem], fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hx hf).elim,
      fun w r hz => ?_⟩
    obtain ⟨zv, hzv, hph⟩ := inv_phi hR hz
    rw [hv] at hzv; cases hzv
    rw [hph, termOp_phi] at ht; cases ht
  atom b bb hbb x hx v hv _ hnp y := by
    refine ⟨by rw [shape_of hv, Val.retype_idem], fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hx hf).elim,
      fun w r hz => ?_⟩
    obtain ⟨zv, hzv, hph⟩ := inv_phi hR hz
    rw [hv] at hzv; cases hzv
    exact absurd hph hnp
  edge p ip pb fr e V hpb hp hP hD hAnc hPhi hst := by
    obtain ⟨k, hk, hown⟩ := edge_taken hst
    have hpt := hR.tree p hp
    obtain ⟨heb, -, hsub⟩ := hR.hF.succ p hp hpt pb hpb k e hk
    -- the source block's facts and the branch taken, at the end of `p`
    have hfacts : ∀ c v, ((c, v) ∈ factsAt F p ∨ (c, v) ∈ ownFact pb k) → rv fr c = .bool v ∧ V c := by
      intro c v hcv
      rcases hcv with hcv | hcv
      · refine ⟨(hP c).2.1 hp v hcv, hAnc c ?_⟩
        obtain ⟨cv, hpl, -, hanc, -⟩ := fact_placed hc hR hp hpb hcv
        exact ⟨cv, hpl, hanc⟩
      · refine ⟨rv_of (hown c v hcv), hAnc c ?_⟩
        have hcm : c ∈ pb.controls := by
          unfold ownFact at hcv
          split at hcv
          · split at hcv
            · rename_i c0 hl
              simp only [List.mem_singleton, Prod.mk.injEq] at hcv
              obtain ⟨rfl, -⟩ := hcv
              rw [← Array.mem_toList_iff, hl]; exact List.mem_singleton_self _
            · cases hcv
          · cases hcv
        obtain ⟨cv, hpl, hbo⟩ := placed_of_listed hwf (hwf.ctrlListed p pb ⟨hp, hpb⟩ c hcm)
        refine ⟨cv, hpl, ?_⟩
        rw [← hbo]
        exact ctrlUse hc hp hpb (by simpa [Cert.inTree] using hpt) hcm
    refine ⟨heb, fun a => ⟨(hP a).1, fun _ v hv => (hfacts a v (hsub _ hv)).1, (hP a).2.2⟩, ?_⟩
    intro bb hbb z hz v hv hph a ha
    refine ⟨by rw [shape_of hv, Val.retype_idem], fun hb v' hf => (fact_not_mem hwf hc hR hb hbb hz hf).elim,
      fun w r hzi yv hyv => ?_⟩
    obtain ⟨zv, hzv, -, hzw, hedges⟩ := hR.hinv z w r hzi
    rw [hv] at hzv; cases hzv
    have hty : tabs.ty v.type = .int w := width_some (by simpa [intAt] using hzw)
    -- the incoming edge is one of `phiEdges`
    obtain ⟨-, cb, hcb, hpred⟩ := hwf.succLink p pb ⟨hp, hpb⟩ k e hk
    rw [hbb] at hcb
    rw [← Option.some.inj hcb] at hpred
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId e.b bb ⟨heb, hbb⟩ z hz
    rw [hv] at hv'; cases hv'
    have hm := mem_phiEdges (F := F) (C := make f) hv hvb hbb hz hpred ha hpt hpb
    obtain ⟨⟨av, hav, haw⟩, hsubr⟩ := hedges a _ hm
    have hshA : shape f.value? tabs a = .int w := by
      rw [shape_of hav]; exact width_some (by simpa [intAt] using haw)
    have hra : rv fr a = .int w yv := by
      have := (hP a).1
      rw [hshA] at this
      rw [← this]; rw [hty] at hyv; exact hyv
    -- the assumptions of the edge hold of the frame
    have hA : AsmHolds f.value? tabs (rv fr) { facts := ownFact pb k ++ factsAt F p, inv } := by
      refine ⟨fun c v hcv => ?_, fun z' w' r' hz' n yv' hd => ?_, fun a' _ _ => (hP a').1⟩
      · have hcv' : (c, v) ∈ factsAt F p ∨ (c, v) ∈ ownFact pb k := by
          rcases List.mem_append.1 hcv with h | h
          · exact .inr h
          · exact .inl h
        obtain ⟨hcr, hcV⟩ := hfacts c v hcv'
        obtain ⟨N, hN⟩ := (hD c hcV).2 (rv fr) fun _ _ _ => rfl
        exact ⟨N, fun n hn => (hN n hn).trans hcr⟩
      · obtain ⟨zv', hzv', hph'⟩ := inv_phi hR hz'
        have hat : ¬ IsTerm f.value? z' := fun ⟨u, hu, ht⟩ => by
          rw [hzv'] at hu; cases hu; rw [hph', termOp_phi] at ht; cases ht
        cases n with
        | zero => simp [den] at hd
        | succ n =>
          rw [den_succ_atom hat] at hd
          exact (hP z').2.2 w' r' hz' yv' hd
    obtain ⟨N, hN⟩ := (hD a (hPhi bb hbb z hz v hv hph a ha)).2 (rv fr) fun _ _ _ => rfl
    have hden : den f.value? tabs (rv fr) N a = .int w yv := (hN N (Nat.le_refl N)).trans hra
    exact Rng.mem_of_sub hsubr (rng_sound hA rngFuel w a N yv hden)

end

end GoFV.Proof.ProveCheck
