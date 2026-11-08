import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `AddPtr` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules whose top op is in the `AddPtr` family
(`docs/proofs/rules.md`). By `Pat.argsOK` the pointer is pointer-typed and the offset a 64-bit
integer. `:127` (a `Const32` offset) is vacuous under `Pat.argsOK` on a 64-bit target (no
instance, so no lemma).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:126`: `(AddPtr <t> x (Const64 [c])) => (OffPtr <t> x [c])` -/
theorem r_generic_126_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_126 := by
  rule_unfold
  obtain ⟨⟨⟨el0, h0⟩, -⟩, h1⟩ := hat
  simp only [Nat.reduceAdd] at h1
  rw [h0] at hlt
  rw [h1] at hty ⊢
  rcases val_of_hasTy_ptr hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · exact Refines.poison _
  all_goals
    simp [PtrOps.addPtr, PtrOps.offPtr, Conv.const, Val.retype, asOffset] at hty ⊢
    exact refines_retype_of_hasTy hty

end GoFV.Proof.Rules
