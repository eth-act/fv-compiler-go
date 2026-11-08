import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values09

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `PtrIndex` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules whose top op is in the `PtrIndex` family
(`docs/proofs/rules.md`). The pointer arguments have pointer shapes by `Pat.argsOK` (hypothesis
`hat` of `rule_unfold`), so a leaf is `poison` or a pointer (`val_of_hasTy_ptr`). The element size
`t.Elem().Size()` is the one of the pointer shape (`methodE`), the index a 64-bit integer.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:970`: `(PtrIndex <t> ptr idx) && config.PtrSize == 8 => (AddPtr ptr (Mul64 <typ.Int> idx (Const64 <typ.Int> [t.Elem().Size()])))` -/
theorem r_generic_970_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_970 := by
  rule_unfold
  obtain ⟨⟨el0, h0⟩, h1⟩ := hat
  simp only [Nat.reduceAdd] at h1
  rw [h0, h1] at hlt
  obtain ⟨hl0, hl1⟩ := hlt
  rcases val_of_hasTy_ptr hl0 with hp | ⟨y, hp⟩ | ⟨p, hp⟩ <;> rw [hp] at hty ⊢
  · exact Refines.poison _
  · -- an integer word: integer-word arithmetic on both sides
    rcases val_of_hasTy_int64 hl1 with hx | ⟨x, hx⟩ | ⟨q, hx, -⟩ <;> rw [hx] at hty ⊢
    · simp [PtrOps.ptrIndex, asOffset]; exact Refines.poison _
    · rcases hT : e.ty [] with _ | _ | _ | _ | _ | (_ | k) | _ | _ | _ | _ <;>
        simp [PtrOps.ptrIndex, hT, asOffset] at hty ⊢ <;> try exact Refines.poison _
      have hk : BitVec.ofInt Width.w64.bits ((k : Int).bmod Int64.size) = BitVec.ofNat 64 k := by
        have hs : Int64.size = 2 ^ 64 := rfl
        rw [hs, ofInt_bmod_of_le (w := Width.w64.bits) (k := 64) (by decide), BitVec.ofInt_natCast]
      suffices key : ∀ M, M = Val.int .w64 (x * BitVec.ofNat 64 k) →
          Refines (PtrOps.wordRes y (x * BitVec.ofNat 64 k))
            (Val.retype (Ty.ptr (some k)) (PtrOps.addPtr [Val.int .w64 y, M])) by
        apply key
        simp [Sem.Int.mul, int2, Conv.const, Val.retype, Val.asInt, strctField]
        rw [hk]
      rintro M rfl
      have hse : (x * BitVec.ofNat 64 k).signExtend 64 = x * BitVec.ofNat 64 k := by simp
      simp only [PtrOps.addPtr, asOffset, hse, PtrOps.wordRes]
      split
      · exact Refines.refl _
      · exact Refines.poison _
    · simp [PtrOps.ptrIndex, asOffset]; exact Refines.poison _
  rcases val_of_hasTy_int64 hl1 with hx | ⟨x, hx⟩ | ⟨q, hx, -⟩ <;> rw [hx] at hty ⊢
  · simp [PtrOps.ptrIndex, asOffset]; exact Refines.poison _
  · rcases hT : e.ty [] with _ | _ | _ | _ | _ | (_ | k) | _ | _ | _ | _ <;>
      simp [PtrOps.ptrIndex, hT, asOffset] at hty ⊢ <;> try exact Refines.poison _
    have hk : BitVec.ofInt Width.w64.bits ((k : Int).bmod Int64.size) = BitVec.ofNat 64 k := by
      have hs : Int64.size = 2 ^ 64 := rfl
      rw [hs, ofInt_bmod_of_le (w := Width.w64.bits) (k := 64) (by decide), BitVec.ofInt_natCast]
    suffices key : ∀ M, M = Val.int .w64 (x * BitVec.ofNat 64 k) →
        Refines (PtrOps.ptrRes (p.add (x * BitVec.ofNat 64 k)))
          (Val.retype (Ty.ptr (some k)) (PtrOps.addPtr [Val.ptr p, M])) by
      apply key
      simp [Sem.Int.mul, int2, Conv.const, Val.retype, Val.asInt, strctField]
      rw [hk]
    rintro M rfl
    have hse : (x * BitVec.ofNat 64 k).signExtend 64 = x * BitVec.ofNat 64 k := by simp
    simp only [PtrOps.addPtr, asOffset, hse, retype_ptrRes_ptr]
    exact Refines.refl _
  · simp [PtrOps.ptrIndex, asOffset]; exact Refines.poison _

end GoFV.Proof.Rules
