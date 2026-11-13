import GoFV.Proof.Rules.DivmodS2
import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Divmod.Values00

/-!
# Unsigned division of a nonnegative dividend by `smagic` (`divmod.rules:136–148`, #69)

`(Div<N>u <t> x (Const<N> [c])) && t.IsSigned() && smagicOK<N>(c)` divides by the signed magic
number of `c`, which is exact for a nonnegative dividend only (`divmod.rules` "Case 4: unsigned
divide where x < 1<<(N-1)"). Go's prove pass builds a signed-typed `Div<N>u` only after it has
shown the dividend nonnegative; under the semantics `t.IsSigned()` is an oracle atom, so the rule
is false at a negative `x` (rules.md "Findings"). `nonNegLeaves` names the dividend, `FrameOK`
makes it a nonnegative integer or `poison` (the rewrite validator decides it with `nonNegD`,
`RewriteCheck.nonNegLeavesD`), and the four lemmas hold under `Rule.SoundT`
(`Rule.soundT_of_soundNN`).

`udiv_magic_nat`: for `x < 2^(n-1)`, `⌊x*m / 2^(n+s)⌋ = ⌊x/c⌋` (`sdiv_magic_int` at a
nonnegative `x`); `udiv_smagic_hmul` (`:144`, `:148`: `Hmul<N>u x m >> s`) and `udiv_smagic_wide`
(`:136`, `:140`: `(SignExt x * m) >> (N + s)` in a register of twice the width) are its
`BitVec` forms. The condition's `t.IsSigned()` is reduced to an oracle boolean
(`methodE_isSigned`) before `divs_smagic` reads `smagicOK<N>(c)` out of it.
-/

namespace GoFV.Proof.Rules.DivmodS

variable [GoFV.SSA.Sem.Addrs]

open GoFV.Rules GoFV.Rules.Magic

/-- Unsigned division by the signed magic number of a dividend below `2^(n-1)`:
`⌊x*M / 2^(n+S)⌋ = ⌊x/c⌋` (`sdiv_magic_int` at a nonnegative `x`). -/
theorem udiv_magic_nat {n S M : Nat} {c : Int} (hn : 2 ≤ n) (h : SSpec n c S M) {X : Nat}
    (hX : X < 2 ^ (n - 1)) : X * M / 2 ^ (n + S) = X / c.toNat := by
  obtain ⟨-, hS2, hS3, hS4, -, -, hMC1, hMC2⟩ := h
  have hC0 : 0 < c.toNat := Nat.lt_of_le_of_lt (Nat.zero_le _) hS3
  have hP := two_pow_int_pos (n - 1)
  have key := sdiv_magic_int (n := n) (S := S) (M := M) (C := c.toNat) (x := (X : Int))
    (by omega) hC0 hMC1 hMC2 (Nat.le_of_lt hS4) (by omega) (by exact_mod_cast hX)
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), Int.sub_zero, ← Int.ofNat_tdiv] at key
  exact_mod_cast key

omit [GoFV.SSA.Sem.Addrs] in
/-- A bit vector with a clear sign bit is below `2^(n-1)`. -/
theorem toNat_lt_of_msb {n : Nat} {x : BitVec n} (hx : x.msb = false) (hn : 1 ≤ n) :
    x.toNat < 2 ^ (n - 1) := by
  have h := BitVec.msb_eq_false_iff_two_mul_lt.1 hx
  have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← Nat.pow_succ']; exact congrArg (2 ^ ·) (by omega)
  omega

omit [GoFV.SSA.Sem.Addrs] in
/-- The divisor of `SSpec` read at `n` bits is `c`. -/
theorem toNat_ofInt_c {n S M : Nat} {c : Int} (h : SSpec n c S M) :
    (BitVec.ofInt n c).toNat = c.toNat := by
  obtain ⟨-, hS2, hS3, hS4, -, -, -, -⟩ := h
  have h1 : 2 ^ (S + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt (by omega) (by omega)]

/-- `Div32u`/`Div64u` by `smagic` of a nonnegative dividend (`divmod.rules:144/148`):
`Hmul x m >> s`, unsigned. -/
theorem udiv_smagic_hmul {n S M : Nat} {c : Int} (hn : 2 ≤ n) (h : SSpec n c S M)
    (x : BitVec n) (hx : x.msb = false) {a : Nat} (ha : a = S) :
    x / BitVec.ofInt n c =
      BitVec.extractLsb' n n (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) (BitVec.ofNat n M))
        >>> a := by
  subst ha
  have hX := toNat_lt_of_msb hx (by omega)
  have hM2 := h.hM2
  have key := udiv_magic_nat hn h hX
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofInt_c h, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hM2]
  have h2n : 2 ^ (2 * n) = 2 ^ (n - 1) * 2 ^ n * 2 := by
    rw [← Nat.pow_add, ← Nat.pow_succ]; exact congrArg (2 ^ ·) (by omega)
  have hxn : x.toNat < 2 ^ (2 * n) := by
    have := x.isLt; have : 2 ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hXM : x.toNat * M < 2 ^ (2 * n) := by
    rw [h2n]
    calc x.toNat * M < 2 ^ (n - 1) * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt hX hM2
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by decide)
  have hM2n : M < 2 ^ (2 * n) := by
    have : 2 ^ n ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hq : x.toNat * M / 2 ^ n < 2 ^ n := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add]
    calc x.toNat * M < 2 ^ (n - 1) * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt hX hM2
      _ ≤ 2 ^ (n + n) := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.mod_eq_of_lt hM2n, Nat.mod_eq_of_lt hxn, Nat.mod_eq_of_lt hXM]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt hq, Nat.div_div_eq_div_mul, ← Nat.pow_add, key]

/-- `Div16u`/`Div32u` by `smagic` of a nonnegative dividend in a wider register
(`divmod.rules:136/140`): `(SignExt x * m) >> (n + s)`, unsigned, truncated to `n` bits. -/
theorem udiv_smagic_wide {n W S M : Nat} {c : Int} (hn : 2 ≤ n) (hW : 2 * n ≤ W)
    (h : SSpec n c S M) (x : BitVec n) (hx : x.msb = false) {a : Nat} (ha : a = n + S) :
    x / BitVec.ofInt n c = BitVec.setWidth n ((BitVec.signExtend W x * BitVec.ofNat W M) >>> a) := by
  subst ha
  have hX := toNat_lt_of_msb hx (by omega)
  have hM2 := h.hM2
  have key := udiv_magic_nat hn h hX
  have hnW : 2 ^ n ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) (by omega)
  have hXM : x.toNat * M < 2 ^ W :=
    calc x.toNat * M < 2 ^ (n - 1) * 2 ^ n := Nat.mul_lt_mul_of_lt_of_lt hX hM2
      _ ≤ 2 ^ W := by rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hq : x.toNat / c.toNat < 2 ^ n :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, toNat_ofInt_c h, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.signExtend_eq_setWidth_of_msb_false hx, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt hnW),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hM2 hnW), Nat.mod_eq_of_lt hXM, Nat.shiftRight_eq_div_pow,
    key, Nat.mod_eq_of_lt hq]

/-- Close a nonnegative-dividend `smagic` goal: the wide form (`:136/140`) or the `Hmul` form
(`:144/148`); `hx` is the dividend's clear sign bit (`nonNegLeaves`). -/
macro "divu_smagic" : tactic => `(tactic| first
  | exact GoFV.Proof.Rules.DivmodS.udiv_smagic_wide (by decide) (by decide)
      ‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _› _ (by simpa using ‹(!_) = true›)
      (by have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS2; bv_omega)
  | exact GoFV.Proof.Rules.DivmodS.udiv_smagic_hmul (by decide)
      ‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _› _ (by simpa using ‹(!_) = true›)
      (by have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS2; bv_omega))

end GoFV.Proof.Rules.DivmodS

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Rules.Generated.Divmod

/-- `t.IsSigned()` is not modelled (`methodE`): the oracle answers it. -/
theorem methodE_isSigned (dy : DV) : methodE dy "IsSigned" [] = none := rfl

attribute [local rule_unfold_ds ↓] methodE_isSigned

section

variable [GoFV.SSA.Sem.Addrs]

set_option hygiene false in
/-- `Rule.SoundNN` of a `divmod.rules:136–148` rule: unfold, read the dividend's sign bit
(`nonNegLeaves`), `smagicOK` out of the condition, and close by `divu_smagic`. -/
local macro "divu_nn" : tactic => `(tactic| (
  rule_unfold
  intro hnl _
  have hx := hnl [0] (by simp [nonNegLeaves])
  clear hnl
  (try simp only [binE_land_bool, rule_unfold_s] at hcond)
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals (try (simp only [GoFV.SSA.Sem.Val.retype] at *; rule_norm))
  all_goals divu_smagic))

/-- `divmod.rules:136`: `(Div16u <t> x (Const16 [c])) && t.IsSigned() && smagicOK16(c) => (Rsh32Ux64 <t> (Mul32 <typ.UInt32> (SignExt16to32 x) (Const32 <typ.UInt32> [int32(smagic16(c).m)])) (Const64 <typ.UInt64> [16 + smagic16(c).s]))` -/
theorem r_divmod_136_sound : Rule.SoundT r_divmod_136 :=
  Rule.soundT_of_soundNN (by divu_nn) rfl

/-- `divmod.rules:140`: `(Div32u <t> x (Const32 [c])) && t.IsSigned() && smagicOK32(c) && config.RegSize == 8 => (Rsh64Ux64 <t> (Mul64 <typ.UInt64> (SignExt32to64 x) (Const64 <typ.UInt64> [int64(smagic32(c).m)])) (Const64 <typ.UInt64> [32 + smagic32(c).s]))` -/
theorem r_divmod_140_sound : Rule.SoundT r_divmod_140 :=
  Rule.soundT_of_soundNN (by divu_nn) rfl

/-- `divmod.rules:144`: `(Div32u <t> x (Const32 [c])) && t.IsSigned() && smagicOK32(c) && config.RegSize == 4 => (Rsh32Ux64 <t> (Hmul32u <typ.UInt32> x (Const32 <typ.UInt32> [int32(smagic32(c).m)])) (Const64 <typ.UInt64> [smagic32(c).s]))` -/
theorem r_divmod_144_sound : Rule.SoundT r_divmod_144 :=
  Rule.soundT_of_soundNN (by divu_nn) rfl

/-- `divmod.rules:148`: `(Div64u <t> x (Const64 [c])) && t.IsSigned() && smagicOK64(c) => (Rsh64Ux64 <t> (Hmul64u <typ.UInt64> x (Const64 <typ.UInt64> [int64(smagic64(c).m)])) (Const64 <typ.UInt64> [smagic64(c).s]))` -/
theorem r_divmod_148_sound : Rule.SoundT r_divmod_148 :=
  Rule.soundT_of_soundNN (by divu_nn) rfl

end

/-! ## Non-vacuity -/

open scoped GoFV.SSA.Sem.Fixed

set_option hygiene false in
/-- `Rule.InstT` of a `divmod.rules:136–148` rule at `x = 100`, `c = 7`: the built nodes have no
frame helpers, the dividend is nonnegative (`nonNegLeaves`), the oracle answers `t.IsSigned()`
(and `config.RegSize == …`) `true`. -/
local macro "divu_inst" r:ident : tactic => `(tactic| (
  refine ⟨Oracle.const_boolTyped true, ?_, ?_⟩
  · refine ⟨fun n hn => ?_, by simp [$r:ident, emptyStrVars], by simp [$r:ident, samePtrVars],
      by simp [$r:ident, numElem1Vars], by simp [$r:ident, size0Vars],
      by simp [$r:ident, sameLeaves], fun p hp => ?_, by simp [$r:ident, nonNegAuxs]⟩
    · simp only [$r:ident, Result.nodes, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a b h hb <;>
        simp only [reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
        simp [strDataVar?, lenVar?, auxVar?, shiftAmt?] at hb
    · simp [$r:ident, nonNegLeaves] at hp
      subst hp
      decide
  · simp [$r:ident, Pat.rawT, Pat.densT, Pat.denT, sigmaT, Pat.bindsT, Pat.bindssT, opVal]
    rule_eval
    all_goals (simp [sigmaT, Pat.bindsT, Pat.bindssT, List.lookup, auxIntDV]; try rule_eval)
    all_goals simp [show Magic.smagicOK 7 = true by decide]))

/-- `divmod.rules:136` at `100 / 7`, `int16`. -/
theorem inst_r_divmod_136 : Rule.InstT r_divmod_136 {}
    (PEnv.ofLists [([0], .i16 100)] [] (.int .w16) [([1], 7)]) (Oracle.const true) := by
  divu_inst r_divmod_136

/-- `divmod.rules:140` at `100 / 7`, `int32`. -/
theorem inst_r_divmod_140 : Rule.InstT r_divmod_140 {}
    (PEnv.ofLists [([0], .i32 100)] [] (.int .w32) [([1], 7)]) (Oracle.const true) := by
  divu_inst r_divmod_140

/-- `divmod.rules:144` at `100 / 7`, `int32`. -/
theorem inst_r_divmod_144 : Rule.InstT r_divmod_144 {}
    (PEnv.ofLists [([0], .i32 100)] [] (.int .w32) [([1], 7)]) (Oracle.const true) := by
  divu_inst r_divmod_144

/-- `divmod.rules:148` at `100 / 7`, `int64`. -/
theorem inst_r_divmod_148 : Rule.InstT r_divmod_148 {}
    (PEnv.ofLists [([0], .i64 100)] [] (.int .w64) [([1], 7)]) (Oracle.const true) := by
  divu_inst r_divmod_148

end GoFV.Proof.Rules
