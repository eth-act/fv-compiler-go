import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Rule lemmas: `AddPtr` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules whose top op is in the `AddPtr` family
(`docs/proofs/rules.md`). By `Pat.argsOK` the pointer is pointer-typed and the offset a 64-bit
integer: a `Const32` offset is `poison` after `retype` (`:127` holds trivially).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:126`: `(AddPtr <t> x (Const64 [c])) => (OffPtr <t> x [c])` -/
theorem r_generic_126_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_126 := by
  rule_unfold
  obtain ⟨⟨el0, h0⟩, h1⟩ := hat
  simp only [Nat.reduceAdd] at h1
  rw [h0] at hlt
  rw [h1] at hty ⊢
  rcases val_of_hasTy_ptr hlt with hl | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · exact Refines.poison _
  · simp [PtrOps.addPtr, PtrOps.offPtr, Conv.const, Val.retype, asOffset] at hty ⊢
    exact refines_retype_of_hasTy hty

/-- `generic.rules:127`: `(AddPtr <t> x (Const32 [c])) => (OffPtr <t> x [int64(c)])` -/
theorem r_generic_127_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_127 := by
  rule_unfold
  obtain ⟨⟨el0, h0⟩, h1⟩ := hat
  simp only [Nat.reduceAdd] at h1
  rw [h1]
  have hw : ¬ Width.w64.bits ≤ Width.w32.bits := by decide
  simp only [Conv.const, Val.retype, hw, ite_false]
  rcases e.leaf [0] with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    first | exact Refines.poison _ | (rename_i w _; cases w <;> exact Refines.poison _)

end GoFV.Proof.Rules
