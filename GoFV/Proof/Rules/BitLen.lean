import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values01

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `BitLen` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`BitLen` family (`docs/proofs/rules.md`).

The `PtrSize == 4` forms (`:65`–`:68`) have a false condition on the 64-bit target. The
`PtrSize == 8` forms (`:61`–`:64`, issue #69) fold `BitLen<w>` of a constant `x` to `Const64
[bits.Len<w>(x)]`: the op is `w - clz x` at the result's width, and `bits.Len` (`bitsLen`) of
`x.toNat` is `w - clz x` (`bitsLen_toNat`: `Nat.log2` of a nonzero `x` lies between the bounds
`BitVec.two_pow_sub_clz_le_toNat_of_ne_zero` and `BitVec.toNat_lt_two_pow_sub_clz`), at most 64,
so its 64-bit constant retyped to the result's width is the same number (`bitLen_ref`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `bits.Len` of a bit vector's value: its width minus its leading zeros. -/
private theorem bitsLen_toNat {w : Nat} (x : BitVec w) : bitsLen x.toNat = w - x.clz.toNat := by
  by_cases hx : x = 0#w
  · subst hx
    have h := (BitVec.clz_eq_iff_eq_zero (x := 0#w)).2 rfl
    rw [h]
    simp [bitsLen]
  · have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | h
      · exact absurd (BitVec.eq_of_toNat_eq (by have := x.isLt; simp at this ⊢; omega)) hx
      · exact h
    have hlt := BitVec.clz_lt_iff_ne_zero.2 hx
    have hc : x.clz.toNat < w := by
      rw [BitVec.lt_def, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt Nat.lt_two_pow_self] at hlt
      exact hlt
    have h1 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero hw hx
    have h2 := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have hn : x.toNat ≠ 0 := fun h => hx (BitVec.eq_of_toNat_eq (by simpa using h))
    have hl : Nat.log2 x.toNat = w - 1 - x.clz.toNat :=
      (Nat.log2_eq_iff hn).2 ⟨h1, by
        rw [show w - 1 - x.clz.toNat + 1 = w - x.clz.toNat by omega]; exact h2⟩
    simp only [bitsLen, hl, hn, ite_false]
    omega

private theorem wrapInt_false_toNat (w : Nat) (y : Int) :
    (wrapInt w false y).toNat = (BitVec.ofInt w y).toNat := by
  rw [BitVec.toNat_ofInt, wrapInt_false, Int.natCast_pow]; rfl

/-- A count `k ≤ 64` as the op's result and as the rule's 64-bit constant retyped. -/
private theorem bitLen_ref' {w k : Nat} (hk : k ≤ w) (hw : w ≤ 64) (t : Ty) :
    Refines (match (match t with | .int w' => some w' | _ => none) with
        | some rw => Val.int rw (BitVec.ofNat (match rw with
            | Width.w8 => 8 | Width.w16 => 16 | Width.w32 => 32 | Width.w64 => 64) k)
        | none => Val.poison)
      (Val.retype t (Val.i64 (BitVec.ofInt 64 (wrapInt 64 true (k : Int))))) := by
  have hb : wrapInt 64 true (k : Int) = k := by
    have h64 : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by decide
    rw [wrapInt_true, Int.bmod_eq_emod_of_lt (by rw [h64]; omega), h64]
    omega
  rw [hb]
  cases t <;> try exact Refines.poison _
  rename_i rw
  have hs : ∀ n, n ≤ 64 → BitVec.setWidth n (BitVec.ofInt 64 (k : Int)) = BitVec.ofNat n k := by
    intro n hn
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.ofInt_natCast]
    rw [Nat.mod_eq_of_lt (a := k) (by omega)]
  cases rw <;> simp only [Val.retype, Width.bits] <;>
    rw [ite_eq_left (by decide), hs _ (by decide)] <;> exact Refines.int _ _

private theorem bitLen_ref {w : Nat} (x : BitVec w) (hw : w ≤ 64) (t : Ty) :
    Refines (match (match t with | .int w' => some w' | _ => none) with
        | some rw => Val.int rw (BitVec.ofNat (match rw with
            | Width.w8 => 8 | Width.w16 => 16 | Width.w32 => 32 | Width.w64 => 64) (w - x.clz.toNat))
        | none => Val.poison)
      (Val.retype t (Val.i64 (BitVec.ofInt 64 (wrapInt 64 true ((w - x.clz.toNat : Nat) : Int))))) :=
  bitLen_ref' (Nat.sub_le _ _) hw t

/-- `rule_auto`'s case split, then `bitLen_ref`. -/
local macro "bitlen_auto" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  rw [wrapInt_false_toNat, bitsLen_toNat]
  exact bitLen_ref _ (by decide) _))

/-- `generic.rules:61`: `(BitLen64 (Const64 [c])) && config.PtrSize == 8 => (Const64 [int64(bits.Len64(uint64(c)))])` -/
theorem r_generic_61_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_61 := by bitlen_auto

/-- `generic.rules:62`: `(BitLen32 (Const32 [c])) && config.PtrSize == 8 => (Const64 [int64(bits.Len32(uint32(c)))])` -/
theorem r_generic_62_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_62 := by bitlen_auto

/-- `generic.rules:63`: `(BitLen16 (Const16 [c])) && config.PtrSize == 8 => (Const64 [int64(bits.Len16(uint16(c)))])` -/
theorem r_generic_63_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_63 := by bitlen_auto

/-- `generic.rules:64`: `(BitLen8 (Const8 [c])) && config.PtrSize == 8 => (Const64 [int64(bits.Len8(uint8(c)))])` -/
theorem r_generic_64_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_64 := by bitlen_auto

/-- `generic.rules:67`: `(BitLen16 (Const16 [c])) && config.PtrSize == 4 => (Const32 [int32(bits.Len16(uint16(c)))])` -/
theorem r_generic_67_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_67 := by rule_auto

/-- `generic.rules:66`: `(BitLen32 (Const32 [c])) && config.PtrSize == 4 => (Const32 [int32(bits.Len32(uint32(c)))])` -/
theorem r_generic_66_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_66 := by rule_auto

/-- `generic.rules:65`: `(BitLen64 (Const64 [c])) && config.PtrSize == 4 => (Const32 [int32(bits.Len64(uint64(c)))])` -/
theorem r_generic_65_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_65 := by rule_auto

/-- `generic.rules:68`: `(BitLen8 (Const8 [c])) && config.PtrSize == 4 => (Const32 [int32(bits.Len8(uint8(c)))])` -/
theorem r_generic_68_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_68 := by rule_auto

/-- `generic.rules:62` at `BitLen32 (Const32 [5])` (the result `Const64 [3]`). -/
theorem inst_r_generic_62 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_62
    (PEnv.ofLists [] [([], .int .w64), ([0], .int .w32)] (.int .w64) [([0], 5)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_62]
  rule_eval

/-- `generic.rules:61` at `BitLen64 (Const64 [-1])` (the result `Const64 [64]`). -/
theorem inst_r_generic_61 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_61
    (PEnv.ofLists [] [([], .int .w64), ([0], .int .w64)] (.int .w64) [([0], -1)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_61]
  rule_eval

end GoFV.Proof.Rules
