import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `EqPtr`/`NeqPtr` against `ConstNil`

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules comparing a pointer with the nil
pointer (`docs/proofs/rules.md`). By `Pat.argsOK` both arguments are pointer words (a pointer
or a 64-bit integer, `uintptr` itabs), so the nil constant reads as the nil pointer
(`null_word`) and the other argument is `poison`, an integer or a pointer
(`val_of_hasTy_word`); pointer equality compares block and offset (#156), so equality with nil
is `Ptr.isNil` (`null_eq`; an integer address is nil iff it is 0, `ofAddr_isNil`), which
`IsNonNil` negates. A pointer word equals itself (`ptr_eq_self`; `generic.rules:1646`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:1684`: `(NeqPtr (ConstNil) p) => (IsNonNil p)` -/
theorem r_generic_1684_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1684 := by
  rule_unfold
  obtain ⟨h0, h1⟩ := hat
  have hn := null_word h0
  generalize Val.retype (e.ty [0]) (Val.ptr Ptr.null) = n at hn hty ⊢
  rcases val_of_hasTy_word h1 hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · simp only [PtrOps.eqPtr, hn]; simp only [Val.asPtrWord]; exact Refines.poison _
  all_goals
    simp only [PtrOps.eqPtr, hn] at hty ⊢
    simp only [Val.asPtrWord, PtrOps.isNonNil, null_eq, ofAddr_isNil,
      Bool.bne_true, not_beq_bne] at hty ⊢
    exact refines_retype_of_hasTy hty

/-- `generic.rules:1683`: `(EqPtr (ConstNil) p) => (Not (IsNonNil p))` -/
theorem r_generic_1683_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1683 := by
  rule_unfold
  obtain ⟨h0, h1⟩ := hat
  have hn := null_word h0
  generalize Val.retype (e.ty [0]) (Val.ptr Ptr.null) = n at hn hty ⊢
  rcases val_of_hasTy_word h1 hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · simp only [PtrOps.eqPtr, hn]; simp only [Val.asPtrWord]; exact Refines.poison _
  all_goals
    simp only [PtrOps.eqPtr, hn] at hty ⊢
    simp only [Val.asPtrWord, PtrOps.isNonNil, null_eq, ofAddr_isNil,
      Cmp.not, bool1, Val.retype, Val.asBool, Bool.bne_false] at hty ⊢
    try simp only [bne, Bool.not_not] at hty ⊢
    exact refines_retype_of_hasTy hty

theorem ptr_eq_self (p : Ptr) : p.eq p = true := by
  simp [Ptr.eq]

/-- `generic.rules:1646`: `(EqPtr x x) => (ConstBool [true])` -/
theorem r_generic_1646_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1646 := by
  rule_unfold
  rw [hc] at hty ⊢
  have hb : PtrOps.eqPtr false [e.leaf [0], e.leaf [0]] = .poison ∨
      PtrOps.eqPtr false [e.leaf [0], e.leaf [0]] = .bool true := by
    rcases val_of_hasTy_word hat.1 hlt.1 with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] <;>
      simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]
  rcases hb with hb | hb <;> rw [hb] at hty ⊢
  · exact Refines.poison _
  · exact refines_retype_of_hasTy hty

/-- `generic.rules:1646` at a heap pointer. -/
theorem inst_r_generic_1646 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1646
    (PEnv.ofLists [([0], .ptr ⟨.heap 0, 8⟩), ([1], .ptr ⟨.heap 0, 8⟩)] [([], .bool)] (.ptr none) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1646]
  rule_eval
  simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]

end GoFV.Proof.Rules
