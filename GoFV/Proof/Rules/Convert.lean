import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.PtrAddr

/-!
# Rule lemmas: `Convert` round trips (`generic.rules:1072`, issue #290)

`(Convert (Convert ptr mem) mem) => ptr`. With `Pat.argsOK` both `Convert`s go between a pointer
and a 64-bit integer (`convArgOk`), so the round trip is pointer → integer → pointer or
integer → pointer → integer. Both word shapes have the same values (`Val.hasTy_ptr_eq_i64`): a
64-bit integer, which both `Convert`s keep (a pointer that converts to an integer is held as its
address, `Ptr.word`), or a pointer that does not convert to an integer, which the
pointer → integer `Convert` turns into `poison`.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA.Sem

section

variable [GoFV.SSA.Sem.Addrs]

/-- A pointer that does not convert to an integer converts to `poison`. -/
private theorem convert_i64_nc {p : Ptr} (hc : p.convertible = false) (m : Val) :
    PtrOps.convert (.int .w64) [.ptr p, m] = .poison := by
  show (match p.convertible, p.addr? with | true, some a => Val.int .w64 a | _, _ => Val.poison) = _
  rw [hc]

/-- `generic.rules:1072`: `(Convert (Convert ptr mem) mem) => ptr`. -/
theorem r_generic_1072_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1072 := by
  rule_unfold
  obtain ⟨⟨h00, -⟩, -⟩ := hlt
  obtain ⟨h0, h1⟩ := hat
  revert h0 h1
  cases hT : e.ty [] with
  | ptr el =>
    intro h0 h1
    simp only [isInt64Ty_iff] at h0
    rw [h0] at h1 ⊢
    simp only [isPtrTy_iff] at h1
    obtain ⟨el', h1⟩ := h1
    rw [h1] at h00
    rcases val_of_hasTy_word (.inl ⟨el', rfl⟩) h00 with h | ⟨x, h⟩ | ⟨p, h⟩ <;> rw [h]
    · exact .poison _
    · simp only [PtrOps.convert, Val.retype]
      exact .int _ _
    · rw [h] at h00
      simp only [Val.hasTy] at h00
      rw [convert_i64_nc (Ptr.not_convertible_of_held h00)]
      exact .poison _
  | int w =>
    cases w with
    | w64 =>
      intro h0 h1
      simp only [isPtrTy_iff] at h0
      obtain ⟨el, h0⟩ := h0
      rw [h0] at h1 ⊢
      simp only [isInt64Ty_iff] at h1
      rw [h1] at h00
      rcases val_of_hasTy_word (.inr rfl) h00 with h | ⟨x, h⟩ | ⟨p, h⟩ <;> rw [h]
      · exact .poison _
      · simp only [PtrOps.convert, Val.retype]
        exact .int _ _
      · rw [h] at h00
        simp only [Val.hasTy] at h00
        have hi : Val.retype (.ptr el) (PtrOps.convert (.ptr el) [.ptr p, e.leaf [1, 0]]) = .ptr p :=
          Ptr.word_of_held h00
        rw [hi, convert_i64_nc (Ptr.not_convertible_of_held h00)]
        exact .poison _
    | _ => intro h0; simp at h0
  | _ => intro h0; simp at h0

end

open scoped GoFV.SSA.Sem.Fixed

/-- `generic.rules:1072` at `uintptr` on an integer `x = 2^40 + 8` (the heap pointer
`⟨heap 0, 8⟩` in between): the matched value is `x` again. -/
theorem inst_r_generic_1072 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1072
    (PEnv.ofLists [([0, 0], .i64 (2 ^ 40 + 8))]
      [([], .int .w64), ([0], .ptr none), ([1, 0], .mem), ([1], .mem)] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1072]
  rule_eval
  simp [PtrOps.convert, Val.retype]

/-- `generic.rules:1072` at `unsafe.Pointer` on the integer word `2^40 + 8` (the heap pointer
`⟨heap 0, 8⟩` held as its address): the matched value is that word again. -/
theorem inst_r_generic_1072_ptr : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1072
    (PEnv.ofLists [([0, 0], .i64 (2 ^ 40 + 8))]
      [([], .ptr none), ([0], .int .w64), ([1, 0], .mem), ([1], .mem)] (.ptr none) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1072]
  rule_eval
  simp [PtrOps.convert, Val.retype]

end GoFV.Proof.Rules
