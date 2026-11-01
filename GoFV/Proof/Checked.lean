import GoFV.Opt.Checked

/-!
# Soundness of the shared checker pieces (`GoFV.Opt.Checked`)
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

theorem checkOK_sound {ce : CheckEnv} {f : Func} (h : checkOK ce f = true) :
    check ce f = .ok () := by
  unfold checkOK at h
  split at h
  · rename_i h'; exact h'
  · cases h

theorem valsOf_eq {f : Func} {b : ID} {B : Block} (h : f.block? b = some B) :
    valsOf f b = B.values := by
  unfold valsOf; rw [h]; rfl

theorem tabEq_spec {α : Type} [DecidableEq α] {a b : Array α} {skip : Nat → Bool}
    (h : tabEq a b skip = true) : a.size = b.size ∧ ∀ i, skip i = false → b[i]? = a[i]? := by
  unfold tabEq at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · have := h.2 i (List.mem_range.2 hlt)
    rw [hi, Bool.false_or, decide_eq_true_eq] at this
    exact this.symm
  · rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (h.1 ▸ hge)]

end GoFV.Proof
