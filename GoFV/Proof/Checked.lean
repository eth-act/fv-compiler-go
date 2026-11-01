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

theorem nat_all_spec {n : Nat} {f : (i : Nat) → i < n → Bool} (h : Nat.all n f = true) :
    ∀ i (hi : i < n), f i hi = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true] at h
    intro i hi
    rcases Nat.lt_or_ge i n with hl | hl
    · exact ih h.1 i hl
    · obtain rfl : i = n := by omega
      exact h.2

theorem tabEq_spec {α : Type} [DecidableEq α] [Inhabited α] {a b : Array α} {skip : Nat → Bool}
    (h : tabEq a b skip = true) : a.size = b.size ∧ ∀ i, skip i = false → b[i]? = a[i]? := by
  simp only [tabEq, withPtrEq] at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1, fun i hi => ?_⟩
  rcases Nat.lt_or_ge i a.size with hlt | hge
  · have := nat_all_spec h.2 i hlt
    rw [hi, Bool.false_or, decide_eq_true_eq] at this
    rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem (h.1 ▸ hlt)]
    rw [getElem!_pos a i hlt, getElem!_pos b i (h.1 ▸ hlt)] at this
    exact congrArg some this.symm
  · rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (h.1 ▸ hge)]

end GoFV.Proof
