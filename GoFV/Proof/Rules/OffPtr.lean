import GoFV.Proof.Rules.Tactic
import GoFV.Proof.PtrAddr
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `OffPtr` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules whose top op is in the `OffPtr` family
(`docs/proofs/rules.md`). The pointer arguments have word shapes by `Pat.argsOK` (hypothesis
`hat` of `rule_unfold`: a pointer shape or the 64-bit integer shape, which have the values and
the retyping of `.ptr none`, `wordShape_ptr`), so a leaf is `poison`, an integer word or a pointer
(`val_of_hasTy_ptr`). Offsets add (`ptr_add_add`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:964`: `(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])` -/
theorem r_generic_964_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_964 := by
  rule_unfold
  obtain ⟨h0, h1⟩ := hat
  obtain ⟨hr0, -⟩ := wordShape_ptr h0
  obtain ⟨-, hh1⟩ := wordShape_ptr h1
  rw [hh1] at hlt
  simp only [hr0] at hty ⊢
  rcases val_of_hasTy_ptr hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · exact Refines.poison _
  · by_cases hw : ((Ptr.ofAddr x).add (BitVec.ofInt 64 (e.auxInt [0]).toInt)).inWindow = true
    · have h1 : PtrOps.wordRes x (BitVec.ofInt 64 (e.auxInt [0]).toInt) =
          .int .w64 (x + BitVec.ofInt 64 (e.auxInt [0]).toInt) := by
        unfold PtrOps.wordRes; rw [if_pos hw]
      simp only [PtrOps.offPtr] at hty ⊢
      rw [h1] at hty ⊢
      have hr : ∀ z, Val.retype (.ptr none) (.int .w64 z) = .int .w64 z := fun _ => rfl
      simp only [hr, PtrOps.offPtr] at hty ⊢
      rw [PtrOps.wordRes_wordRes hw] at hty ⊢
      rw [ofInt_int64_ofInt (by decide), ofInt_wrapInt_true (by decide), BitVec.ofInt_add]
      rw [BitVec.add_comm (BitVec.ofInt 64 (e.auxInt [0]).toInt)] at hty ⊢
      exact refines_retype_of_hasTy hty
    · have h1 : PtrOps.wordRes x (BitVec.ofInt 64 (e.auxInt [0]).toInt) = .poison := by
        unfold PtrOps.wordRes; rw [if_neg hw]
      simp only [PtrOps.offPtr] at hty ⊢
      rw [h1]
      exact Refines.poison _
  · have hi : ∀ k : Int64, PtrOps.offPtr k [.ptr p] = PtrOps.ptrRes (p.add (BitVec.ofInt 64 k.toInt)) :=
      fun _ => rfl
    rw [← Val.retype_of_hasTy hty]
    rw [hi, retype_ptrRes_ptr, offPtr_ptrRes, hi]
    rw [ofInt_int64_ofInt (by decide), ofInt_wrapInt_true (by decide), BitVec.ofInt_add,
      BitVec.add_comm]
    exact ptrRes_two_steps p _ _ _

/-- `generic.rules:965`: `(OffPtr p [0]) && v.Type.Compare(p.Type) == types.CMPeq => p` -/
theorem r_generic_965_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_965 := by
  rule_unfold
  obtain ⟨-, hh0⟩ := wordShape_ptr hat
  simp only [DV.int.injEq] at hc
  rw [hh0] at hlt
  rcases val_of_hasTy_ptr hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl]
  · exact Refines.poison _
  · simp only [PtrOps.offPtr, hc, PtrOps.wordRes]
    have : x + BitVec.ofInt 64 (0 : Int) = x := by simp
    rw [this]
    split
    · exact Refines.refl _
    · exact Refines.poison _
  · simp only [PtrOps.offPtr, hc]
    have : p.add (BitVec.ofInt 64 0) = p := by simp [Ptr.add]
    rw [this]
    rw [hl] at hlt
    have hcv : p.convertible = false := by simpa [Val.hasTy] using hlt
    have h := ptrRes_refines p
    rwa [Ptr.word_of_not_convertible hcv] at h

end GoFV.Proof.Rules
