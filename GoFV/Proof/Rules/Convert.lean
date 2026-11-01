import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.PtrAddr
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemmas: `Convert` round trips (`generic.rules:1072`)

`(Convert (Convert ptr mem) mem) => ptr`. With `Pat.argsOK` both `Convert`s go between a pointer
and a 64-bit integer (`convArgOk`), in opposite directions. Pointer → integer → pointer:
`Ptr.ofAddr_addr` (a convertible pointer comes back). Integer → pointer → integer:
`Ptr.addr?_ofAddr` (the pointer at an address has that address); an address-less pointer in an
integer register (`Val.hasTy`) does not convert, so the matched value is `poison`.
-/

namespace GoFV.SSA.Sem

/-- The pointer `Ptr.ofAddr` gives at an address has that address. -/
theorem Ptr.addr?_ofAddr (x : BitVec 64) : (Ptr.ofAddr x).addr? = some x := by
  have hx := x.isLt
  unfold Ptr.ofAddr
  dsimp only
  split
  · simp [Ptr.addr?, Blk.base?]
  · split
    · rename_i h1 h2
      simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have : (x.toNat / 2 ^ 40 - 1 + 1) * 2 ^ 40 + x.toNat % 2 ^ 40 = x.toNat := by omega
      omega
    · rename_i h1 h2
      split
      · rename_i hk
        simp only [beq_iff_eq] at hk
        simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      · simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega

end GoFV.SSA.Sem

namespace GoFV.Proof.Rules

open GoFV.SSA.Sem

/-- `generic.rules:1072`: `(Convert (Convert ptr mem) mem) => ptr` -/
theorem r_generic_1072_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1072 := by
  rule_unfold
  obtain ⟨⟨h00, -⟩, -⟩ := hlt
  obtain ⟨h0, h1⟩ := hat
  revert h0 h1
  cases hT : e.ty [] with
  | ptr el =>
    intro h0 h1
    simp only [convArgOk, isInt64Ty_iff] at h0
    rw [h0] at h1 ⊢
    simp only [convArgOk, isPtrTy_iff] at h1
    obtain ⟨el', h1⟩ := h1
    rw [h1] at h00
    rcases val_of_hasTy_ptr h00 with h | ⟨p, h⟩ <;> rw [h]
    · exact .poison _
    · simp only [PtrOps.convert]
      cases hc : p.convertible <;> cases ha : p.addr? <;>
        simp only [Val.retype, Width.bits, Nat.le_refl, ite_true, BitVec.setWidth_eq]
      · exact .poison _
      · exact .poison _
      · exact .poison _
      · rw [Ptr.ofAddr_addr hc ha]; exact .ptr _
  | int w =>
    cases w with
    | w64 =>
      intro h0 h1
      simp only [convArgOk, isPtrTy_iff] at h0
      obtain ⟨el, h0⟩ := h0
      rw [h0] at h1 ⊢
      simp only [convArgOk, isInt64Ty_iff] at h1
      rw [h1] at h00
      rcases val_of_hasTy_word (.inr rfl) h00 with h | ⟨x, h⟩ | ⟨p, h⟩ <;> rw [h]
      · exact .poison _
      · simp only [PtrOps.convert, Val.retype, Ptr.addr?_ofAddr]
        cases (Ptr.ofAddr x).convertible
        · exact .poison _
        · exact .int _ _
      · rw [h] at h00
        simp only [Val.hasTy, Option.isNone_iff_eq_none] at h00
        simp only [PtrOps.convert, Val.retype, h00]
        cases p.convertible <;> exact .poison _
    | _ => intro h0; simp [convArgOk] at h0
  | _ => intro h0; simp [convArgOk] at h0

/-- `generic.rules:1072` on an integer `x = 2^40 + 8` (heap pointer `⟨heap 0, 8⟩` in between). -/
theorem inst_r_generic_1072 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1072
    (PEnv.ofLists [([0, 0], .i64 (2 ^ 40 + 8))]
      [([], .int .w64), ([0], .ptr none), ([1, 0], .mem), ([1], .mem)] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1072]
  rule_eval
  simp only [PtrOps.convert, Val.retype, Ptr.addr?_ofAddr,
    show (Ptr.ofAddr (2#64 ^ 40 + 8#64)).convertible = true from rfl]
  simp

end GoFV.Proof.Rules
