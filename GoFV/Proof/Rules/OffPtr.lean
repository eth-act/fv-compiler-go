import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `OffPtr` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules whose top op is in the `OffPtr` family
(`docs/proofs/rules.md`). The pointer arguments have pointer shapes by `Pat.argsOK` (hypothesis
`hat` of `rule_unfold`), so a leaf is `poison` or a pointer (`val_of_hasTy_ptr`). Offsets add
(`ptr_add_add`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:964`: `(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])` -/
theorem r_generic_964_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_964 := by
  rule_unfold
  obtain ⟨⟨el0, h0⟩, ⟨el1, h1⟩⟩ := hat
  rw [h1] at hlt
  rw [h0] at hty ⊢
  rcases val_of_hasTy_ptr hlt with hl | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · exact Refines.poison _
  · simp only [PtrOps.offPtr, Val.retype] at hty ⊢
    rw [ofInt_int64_ofInt (by decide), ofInt_wrapInt_true (by decide), BitVec.ofInt_add,
      BitVec.add_comm, ← ptr_add_add]
    exact refines_retype_of_hasTy hty

/-- `generic.rules:965`: `(OffPtr p [0]) && v.Type.Compare(p.Type) == types.CMPeq => p` -/
theorem r_generic_965_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_965 := by
  rule_unfold
  obtain ⟨el0, h0⟩ := hat
  simp only [DV.int.injEq] at hc
  rw [h0] at hlt
  rcases val_of_hasTy_ptr hlt with hl | ⟨p, hl⟩ <;> rw [hl]
  · exact Refines.poison _
  · simp [PtrOps.offPtr, hc, Ptr.add]
    exact Refines.refl _

end GoFV.Proof.Rules
