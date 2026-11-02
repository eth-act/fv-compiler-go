import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.PtrAddr
import GoFV.Rules.Guarded

/-!
# Rule lemmas: `Convert` round trips (`generic.rules:1072`, issue #290)

`(Convert (Convert ptr mem) mem) => ptr`, proven at an integer type only
(`GoFV.Rules.Guarded.r_generic_1072`, condition `!v.Type.IsPtrShaped()`). With `Pat.argsOK` both
`Convert`s go between a pointer and a 64-bit integer (`convArgOk`), so the round trip is
integer → pointer → integer. Integer → pointer is the identity (§3.3), so an integer leaf comes
back unchanged; an address-less pointer in an integer register (`Val.hasTy`) does not convert,
so the matched value is `poison`. The pointer round trip (`v` pointer-shaped) is not a
refinement: a convertible pointer `p` gives the integer word `addr p` in the source and `p` in
the target (docs/proofs/rules.md "Findings").
-/

namespace GoFV.Proof.Rules

open GoFV.SSA.Sem

/-- `generic.rules:1072`: `(Convert (Convert ptr mem) mem) => ptr` at an integer type
(`!v.Type.IsPtrShaped()`). -/
theorem r_generic_1072_sound : Rule.Sound GoFV.Rules.Guarded.r_generic_1072 := by
  rule_unfold
  obtain ⟨⟨h00, -⟩, -⟩ := hlt
  obtain ⟨h0, h1⟩ := hat
  revert h0 h1 hcond
  cases hT : e.ty [] with
  | ptr el => intro hcond; simp [kindDV, kindE] at hcond
  | int w =>
    cases w with
    | w64 =>
      intro _ h0 h1
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
        simp only [Val.hasTy, Option.isNone_iff_eq_none] at h00
        simp only [PtrOps.convert, Val.retype, h00]
        cases p.convertible <;> exact .poison _
    | _ => intro _ h0; simp at h0
  | _ => intro _ h0; simp at h0

/-- `generic.rules:1072` at `uintptr` on an integer `x = 2^40 + 8` (the heap pointer
`⟨heap 0, 8⟩` in between): the matched value is `x` again. -/
theorem inst_r_generic_1072 : Rule.Inst GoFV.Rules.Guarded.r_generic_1072
    (PEnv.ofLists [([0, 0], .i64 (2 ^ 40 + 8))]
      [([], .int .w64), ([0], .ptr none), ([1, 0], .mem), ([1], .mem)] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Guarded.r_generic_1072]
  rule_eval
  simp [PtrOps.convert, Val.retype, kindDV, kindE]

end GoFV.Proof.Rules
