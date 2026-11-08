import GoFV.Proof.Low.Rules.ConstFold

/-!
# Lowering rule lemmas: bit-field peepholes (`ARM64.rules:1641-1765`, `1853-1855`)

`UBFX`/`UBFIZ`/`SBFX`/`SBFIZ` of an `ARM64BitField` auxint `width | lsb<<8` (`Arm64.bf`) built by
`armBFAuxInt`, which the rule denotation computes in range and leaves to the oracle otherwise
(`callH`). Every rule here rewrites an op of an op of `x` into one op of `x`: the outer op reads
the low bits of the inner result that `retypeL` keeps (`refines_op1_inner`: the whole register for
the right shifts and the bit fields, the result's low bits for `SLLconst`/`ANDconst`, the source
width for an extension), and the composed op is the new one bit by bit (`bf_bits`: the
`getLsbD` of each op, then `bf_close` splits the index conditions and closes each case by
`omega`). The auxints the rules read are in Go's range (`hrng`, `Pat.rangeL`: shift amounts below
64, bit fields `bfOK`), so the result's `armBFAuxInt` is in range and `bf_ofInt` decodes it. A
mask condition `isARM64BFMask(…)` names the mask's width (`bfMaskW`, `bf_mask`), whose bits
`bf_mask_getLsbD` gives. `(ANDconst [0xff…] x) => (MOV{B,H,W}Ureg x)`: the same op.
-/

namespace GoFV.Proof.Low.Rules.Bitfield

open GoFV.Proof.Rules in
#helper_name_lemmas "armBFAuxInt" "isARM64BFMask" "arm64BFWidth"

end GoFV.Proof.Low.Rules.Bitfield

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-! ## Auxint arithmetic -/

private theorem bf_wrap64 {v : Int} (h1 : -2 ^ 63 ≤ v) (h2 : v < 2 ^ 63) : wrapInt 64 true v = v := by
  simp only [wrapInt, ite_true]; rw [Int.bmod_eq_of_le] <;> omega

private theorem bf_emod (a b : Int) : a.emod b = a % b := rfl

/-- The bit field `width | lsb<<8` built in range. -/
private theorem bf_ofInt {l w : Int} (h0 : 0 ≤ l) (h1 : l ≤ 63) (h2 : 1 ≤ w) (h3 : l + w ≤ 64) :
    Arm64.bf (Int64.ofInt (w + l * 256)) = (l.toNat, w.toNat) := by
  have hb : (Int64.ofInt (w + l * 256)).toInt = w + l * 256 :=
    Int64.toInt_ofInt_of_le (by omega) (by omega)
  simp only [Arm64.bf, hb, Prod.mk.injEq]
  constructor <;> omega

/-! ## Bits -/

private theorem bf_getLsbD_mask (w i : Nat) :
    (Arm64.mask w).getLsbD i = (decide (i < 64) && decide (i < w)) := by
  simp only [Arm64.mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]

private theorem bf_getLsbD_sext {w : Nat} (i : Nat) (x : BitVec 64) (h1 : 1 ≤ w) (h2 : w ≤ 64) :
    (Arm64.sext w x).getLsbD i =
      (decide (i < 64) && if i < w then x.getLsbD i else x.getLsbD (w - 1)) := by
  by_cases hi : i < 64
  · simp only [Arm64.sext, show w ≠ 0 by omega, ite_false, Arm64.mask,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, BitVec.msb_shiftLeft, BitVec.getMsbD]
    by_cases hin : i < w
    · have e1 : 64 - w + i - (64 - w) = i := by omega
      simp [hin, hi, e1, show 64 - w + i < 64 by omega, show ¬ 64 ≤ i by omega,
        show ¬ 64 - w + i < 64 - w by omega]
    · have e2 : 64 - 1 - (64 - w) = w - 1 := by omega
      simp [hin, hi, e2, show ¬ 64 - w + i < 64 by omega, show ¬ 64 ≤ i by omega,
        show w - 1 < w by omega, show 64 - w < 64 by omega, show w - 1 < 64 by omega]
  · simp [hi, BitVec.getLsbD_of_ge (Arm64.sext w x) i (by omega)]

private theorem bf_getLsbD_rl {s : Nat} (i : Nat) (x : BitVec 64) (hs : s < 64) :
    (Arm64.Shift.rl.apply x s).getLsbD i = x.getLsbD (s + i) := by
  simp only [Arm64.Shift.apply, Nat.mod_eq_of_lt hs, BitVec.getLsbD_ushiftRight]

private theorem bf_getLsbD_ll {s : Nat} (i : Nat) (x : BitVec 64) (hs : s < 64) :
    (Arm64.Shift.ll.apply x s).getLsbD i =
      (decide (i < 64) && decide (s ≤ i) && x.getLsbD (i - s)) := by
  simp only [Arm64.Shift.apply, Nat.mod_eq_of_lt hs, BitVec.getLsbD_shiftLeft]
  by_cases h : i < s
  · simp [h, show ¬ s ≤ i by omega]
  · simp [h, show s ≤ i by omega]

private theorem bf_getLsbD_ra {s : Nat} (i : Nat) (x : BitVec 64) (hs : s < 64) :
    (Arm64.Shift.ra.apply x s).getLsbD i =
      (decide (i < 64) && if s + i < 64 then x.getLsbD (s + i) else x.getLsbD 63) := by
  simp only [Arm64.Shift.apply, Nat.mod_eq_of_lt hs, BitVec.getLsbD_sshiftRight,
    BitVec.msb_eq_getLsbD_last]
  by_cases hi : i < 64
  · simp [hi, show ¬ 64 ≤ i by omega]
  · simp [hi, show 64 ≤ i by omega]

private theorem bf_getLsbD_ext_false {w : Nat} (i : Nat) (x : BitVec 64) :
    (Arm64.ext false w x).getLsbD i = (decide (i < 64) && decide (i < w) && x.getLsbD i) := by
  simp only [Arm64.ext, Bool.false_eq_true, ite_false, BitVec.getLsbD_and, bf_getLsbD_mask]
  exact Bool.and_comm _ _

private theorem bf_getLsbD_ext_true {w : Nat} (i : Nat) (x : BitVec 64) (h1 : 1 ≤ w) (h2 : w ≤ 64) :
    (Arm64.ext true w x).getLsbD i =
      (decide (i < 64) && if i < w then x.getLsbD i else x.getLsbD (w - 1)) := by
  simp only [Arm64.ext, ite_true, bf_getLsbD_sext i x h1 h2]

private theorem bf_getLsbD_ubfx {k : Int64} {l w : Nat} (i : Nat) (x : BitVec 64) (hk : Arm64.bf k = (l, w)) :
    (Arm64.ubfx k x).getLsbD i = (decide (i < 64) && decide (i < w) && x.getLsbD (l + i)) := by
  simp only [Arm64.ubfx, hk, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, bf_getLsbD_mask]
  exact Bool.and_comm _ _

private theorem bf_getLsbD_ubfiz {k : Int64} {l w : Nat} (i : Nat) (x : BitVec 64)
    (hk : Arm64.bf k = (l, w)) :
    (Arm64.ubfiz k x).getLsbD i =
      (decide (i < 64) && decide (l ≤ i) && decide (i - l < w) && x.getLsbD (i - l)) := by
  simp only [Arm64.ubfiz, hk, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, bf_getLsbD_mask]
  by_cases h : i < l
  · simp [h, show ¬ l ≤ i by omega]
  · by_cases hi : i < 64
    · simp only [h, hi, show l ≤ i by omega, show i - l < 64 by omega, decide_true, decide_false,
        Bool.not_false, Bool.true_and]
      exact Bool.and_comm _ _
    · simp [hi]

private theorem bf_getLsbD_sbfx {k : Int64} {l w : Nat} (i : Nat) (x : BitVec 64) (hk : Arm64.bf k = (l, w))
    (h1 : 1 ≤ w) (h2 : w ≤ 64) :
    (Arm64.sbfx k x).getLsbD i =
      (decide (i < 64) && if i < w then x.getLsbD (l + i) else x.getLsbD (l + (w - 1))) := by
  simp only [Arm64.sbfx, hk, bf_getLsbD_sext i _ h1 h2, BitVec.getLsbD_ushiftRight]

private theorem bf_getLsbD_sbfiz {k : Int64} {l w : Nat} (i : Nat) (x : BitVec 64)
    (hk : Arm64.bf k = (l, w)) (h1 : 1 ≤ w) (h2 : w ≤ 64) :
    (Arm64.sbfiz k x).getLsbD i =
      (decide (i < 64) && decide (l ≤ i) &&
        if i - l < w then x.getLsbD (i - l) else x.getLsbD (w - 1)) := by
  simp only [Arm64.sbfiz, hk, BitVec.getLsbD_shiftLeft]
  by_cases h : i < l
  · simp [h, show ¬ l ≤ i by omega]
  · by_cases hi : i < 64
    · rw [bf_getLsbD_sext (i - l) _ h1 h2]
      simp [h, hi, show l ≤ i by omega, show i - l < 64 by omega]
    · simp [hi]

private theorem bf_getLsbD_ubfx_of {l w : Int} (h0 : 0 ≤ l) (h1 : l ≤ 63) (h2 : 1 ≤ w) (h3 : l + w ≤ 64)
    (i : Nat) (x : BitVec 64) :
    (Arm64.ubfx (Int64.ofInt (w + l * 256)) x).getLsbD i =
      (decide (i < 64) && decide (i < w.toNat) && x.getLsbD (l.toNat + i)) :=
  bf_getLsbD_ubfx i x (bf_ofInt h0 h1 h2 h3)

private theorem bf_getLsbD_ubfiz_of {l w : Int} (h0 : 0 ≤ l) (h1 : l ≤ 63) (h2 : 1 ≤ w) (h3 : l + w ≤ 64)
    (i : Nat) (x : BitVec 64) :
    (Arm64.ubfiz (Int64.ofInt (w + l * 256)) x).getLsbD i =
      (decide (i < 64) && decide (l.toNat ≤ i) && decide (i - l.toNat < w.toNat) &&
        x.getLsbD (i - l.toNat)) :=
  bf_getLsbD_ubfiz i x (bf_ofInt h0 h1 h2 h3)

private theorem bf_getLsbD_sbfx_of {l w : Int} (h0 : 0 ≤ l) (h1 : l ≤ 63) (h2 : 1 ≤ w) (h3 : l + w ≤ 64)
    (i : Nat) (x : BitVec 64) :
    (Arm64.sbfx (Int64.ofInt (w + l * 256)) x).getLsbD i =
      (decide (i < 64) &&
        if i < w.toNat then x.getLsbD (l.toNat + i) else x.getLsbD (l.toNat + (w.toNat - 1))) :=
  bf_getLsbD_sbfx i x (bf_ofInt h0 h1 h2 h3) (by omega) (by omega)

private theorem bf_getLsbD_sbfiz_of {l w : Int} (h0 : 0 ≤ l) (h1 : l ≤ 63) (h2 : 1 ≤ w) (h3 : l + w ≤ 64)
    (i : Nat) (x : BitVec 64) :
    (Arm64.sbfiz (Int64.ofInt (w + l * 256)) x).getLsbD i =
      (decide (i < 64) && decide (l.toNat ≤ i) &&
        if i - l.toNat < w.toNat then x.getLsbD (i - l.toNat) else x.getLsbD (w.toNat - 1)) :=
  bf_getLsbD_sbfiz i x (bf_ofInt h0 h1 h2 h3) (by omega) (by omega)

private theorem bf_getLsbD_ubfx_k (k : Int64) (i : Nat) (x : BitVec 64) :
    (Arm64.ubfx k x).getLsbD i = (decide (i < 64) && decide (i < k.toInt.toNat % 256) &&
      x.getLsbD (k.toInt.toNat / 256 + i)) :=
  bf_getLsbD_ubfx i x rfl

private theorem bf_getLsbD_ubfiz_k (k : Int64) (i : Nat) (x : BitVec 64) :
    (Arm64.ubfiz k x).getLsbD i = (decide (i < 64) && decide (k.toInt.toNat / 256 ≤ i) &&
      decide (i - k.toInt.toNat / 256 < k.toInt.toNat % 256) &&
      x.getLsbD (i - k.toInt.toNat / 256)) :=
  bf_getLsbD_ubfiz i x rfl

private theorem bf_getLsbD_sbfx_k (k : Int64) (i : Nat) (x : BitVec 64) (h1 : 1 ≤ k.toInt.toNat % 256)
    (h2 : k.toInt.toNat % 256 ≤ 64) :
    (Arm64.sbfx k x).getLsbD i = (decide (i < 64) &&
      if i < k.toInt.toNat % 256 then x.getLsbD (k.toInt.toNat / 256 + i)
      else x.getLsbD (k.toInt.toNat / 256 + (k.toInt.toNat % 256 - 1))) :=
  bf_getLsbD_sbfx i x rfl h1 h2

private theorem bf_getLsbD_sbfiz_k (k : Int64) (i : Nat) (x : BitVec 64) (h1 : 1 ≤ k.toInt.toNat % 256)
    (h2 : k.toInt.toNat % 256 ≤ 64) :
    (Arm64.sbfiz k x).getLsbD i = (decide (i < 64) && decide (k.toInt.toNat / 256 ≤ i) &&
      if i - k.toInt.toNat / 256 < k.toInt.toNat % 256 then x.getLsbD (i - k.toInt.toNat / 256)
      else x.getLsbD (k.toInt.toNat % 256 - 1)) :=
  bf_getLsbD_sbfiz i x rfl h1 h2

/-- A left shift's low `m` bits read its operand's low `m` bits only. -/
private theorem bf_ll_low {m s : Nat} (a b : BitVec 64) (h : a.setWidth m = b.setWidth m) :
    (Arm64.Shift.ll.apply a s).setWidth m = (Arm64.Shift.ll.apply b s).setWidth m := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hb : ∀ q, q < m → a.getLsbD q = b.getLsbD q := fun q hq => by
    have := congrArg (fun y : BitVec m => y.getLsbD q) h
    simpa [BitVec.getLsbD_setWidth, hq] using this
  simp only [BitVec.getLsbD_setWidth, Arm64.Shift.apply, BitVec.getLsbD_shiftLeft]
  by_cases hq : j < s % 64
  · simp [hq]
  · rw [hb (j - s % 64) (by omega)]

private theorem armReadW_sll (T : Ty) : armReadW .ARM64SLLconst T 0 = lowW T := by cases T <;> rfl

/-- The bits of a mask whose part above `r` is `2^k - 1` (`bfMaskW`). -/
private theorem bf_mask_getLsbD {m r : Int} {k : Nat} (h : bfMaskW m r = some k) (i : Nat)
    (hi : r.toNat ≤ i) :
    (BitVec.ofInt 64 m).getLsbD i = (decide (i < 64) && decide (i - r.toNat < k)) := by
  unfold bfMaskW at h
  split at h
  · dsimp only at h
    split at h
    · rename_i hc
      obtain ⟨_, hn1, _⟩ := hc
      cases h
      by_cases h64 : i < 64
      · rw [← BitVec.testBit_toNat, BitVec.toNat_ofInt]
        have h2 : (m % ((2 ^ 64 : Nat) : Int)).toNat = (m.emod (2 ^ 64)).toNat := by norm_cast
        rw [h2]
        have hn := Nat.eq_sub_of_add_eq hn1
        have hd := Nat.testBit_div_two_pow (n := r.toNat) (m.emod (2 ^ 64)).toNat (i - r.toNat)
        rw [show i - r.toNat + r.toNat = i by omega, hn, Nat.testBit_two_pow_sub_one] at hd
        rw [← hd]
        simp [h64]
      · simp [h64, BitVec.getLsbD_of_ge (BitVec.ofInt 64 m) i (by omega)]
    · cases h
  · cases h

/-- The width a mask names (`bfMaskW`) is in `[1, 62]`. -/
private theorem bf_mask_width {m r : Int} {k : Nat} (h : bfMaskW m r = some k) :
    1 ≤ k ∧ k ≤ 62 ∧ 0 ≤ r ∧ r < 64 := by
  unfold bfMaskW at h
  split at h
  · rename_i hr
    dsimp only at h
    split at h
    · rename_i hc
      obtain ⟨hn0, hn1, hk⟩ := hc
      cases h
      refine ⟨?_, hk, hr.1, hr.2⟩
      rcases Nat.eq_zero_or_pos (Nat.log2 ((m.emod (2 ^ 64)).toNat / 2 ^ r.toNat + 1)) with h0 | h0
      · rw [h0] at hn1; omega
      · exact h0
    · cases h
  · cases h

private theorem bf_decide_ite (p : Prop) [Decidable p] : decide p = if p then true else false := by
  by_cases h : p <;> simp [h]

/-- Close a per-bit goal: every condition split, each case by `omega` on the indices. -/
syntax "bf_close" (" [" term "]")? : tactic
macro_rules
  | `(tactic| bf_close) => `(tactic| bf_close [Int.toNat_natCast])
  | `(tactic| bf_close [$h]) => `(tactic| (
    try simp only [bf_decide_ite] at *
    repeat' split
    all_goals (try simp (disch := omega) only [$h:term, bf_decide_ite])
    all_goals (repeat' split)
    all_goals (try simp only [Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
      Bool.not_true, Bool.not_false, Bool.and_self])
    all_goals first
      | rfl
      | (exfalso; omega)
      | (congr 1; omega)
      | (simp (disch := omega) only [BitVec.getLsbD_of_ge]; done)))

set_option hygiene false in
/-- The auxint ranges (`hrng`) and the condition (`hcond`) as integer facts, `wrapInt` of the
in-range auxint arithmetic dropped, and the result's `armBFAuxInt` in range. -/
macro "bf_prep" : tactic => `(tactic| (
  simp (config := { decide := true }) only [Pat.rangeL, Pat.rangeLs, auxRangeL, bfOK,
    Bool.and_eq_true, decide_eq_true_eq, and_true, ite_true, ite_false, Bool.or_eq_true,
    beq_iff_eq] at hrng
  simp only [Arm64.amt, decide_eq_true_eq, bf_emod, Int64.ofInt_toInt] at *
  have hb0 := Int64.toInt_lt (e.auxInt [])
  have hb1 := Int64.le_toInt (e.auxInt [])
  have hb2 := Int64.toInt_lt (e.auxInt [0])
  have hb3 := Int64.le_toInt (e.auxInt [0])
  try simp (disch := omega) only [Int.emod_eq_of_lt] at *
  try simp (disch := omega) only [bf_wrap64] at *
  try simp (disch := omega) only [ite_eq_left]))

/-- The composed op's bits (`bf_getLsbD_*`, and a mask's by `bf_mask_getLsbD`), then `bf_close`. -/
syntax "bf_bits" (" [" term "]")? : tactic
macro_rules
  | `(tactic| bf_bits) => `(tactic| bf_bits [Int.toNat_natCast])
  | `(tactic| bf_bits [$h]) => `(tactic| (
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp (disch := omega) only [Int.toNat_natCast, bf_getLsbD_rl, bf_getLsbD_ll, bf_getLsbD_ra,
      bf_getLsbD_ext_false, bf_getLsbD_ext_true, bf_getLsbD_ubfx_of, bf_getLsbD_ubfiz_of,
      bf_getLsbD_sbfx_of, bf_getLsbD_sbfiz_of, BitVec.getLsbD_and, $h:term]
    try simp (disch := omega) only [bf_getLsbD_ubfx_k, bf_getLsbD_ubfiz_k, bf_getLsbD_sbfx_k,
      bf_getLsbD_sbfiz_k, bf_getLsbD_rl, bf_getLsbD_ll, bf_getLsbD_ra, bf_getLsbD_ext_false,
      bf_getLsbD_ext_true, BitVec.getLsbD_and, $h:term]
    bf_close [$h]))

set_option hygiene false in
/-- An outer op reading the whole register (`SRLconst`, `SRAconst`, `UBFX`): the composed op. -/
macro "bf_in64" : tactic => `(tactic| (
  refine refines_op1_inner (n := 64) (by decide) (by decide)
    (by simpa only [armReadW] using harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_eq] at h; rw [h]) ?_ _
  intro x))

set_option hygiene false in
/-- An outer `SLLconst`, reading its result's low bits: the composed op. -/
macro "bf_insll" : tactic => `(tactic| (
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2 (armReadW_sll _ ▸ harg.1) _ _ _
    (fun a b h => bf_ll_low a b h) ?_ _
  intro x))

set_option hygiene false in
/-- An outer `ANDconst`, reading its result's low bits: the composed op. -/
macro "bf_inand" : tactic => `(tactic| (
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64ANDconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_and, h]) ?_ _
  intro x))

set_option hygiene false in
/-- An outer extension `MOV{B,H,W}{,U}reg`, reading its source width: the composed op. -/
macro "bf_inext " s:term:max n:num : tactic => `(tactic| (
  refine refines_op1_inner (n := $n) (by decide) (by decide)
    (by simpa only [armReadW] using harg.1) _ _ _
    (fun a b h => by rw [ext_low $s (by decide) a, ext_low $s (by decide) b, h]) ?_ _
  intro x))

macro "bf_r64" : tactic => `(tactic| (bf_in64; bf_bits))
macro "bf_rsll" : tactic => `(tactic| (bf_insll; bf_bits))
macro "bf_rand" : tactic => `(tactic| (bf_inand; bf_bits))
macro "bf_rext " s:term:max n:num : tactic => `(tactic| (bf_inext $s $n; bf_bits))

set_option hygiene false in
/-- A condition `isARM64BFMask(…)` on the mask `bfMaskW m r` (`hcond`): the mask's width `k`
(`hm`, `hw`), the result's `arm64BFWidth` that width. -/
macro "bf_mask " m:term:max r:term:max : tactic => `(tactic| (
  cases hm : bfMaskW $m $r
  · simp only [hm] at hcond; cases hcond
  rename_i k
  simp only [hm, callH, DV.bool.injEq, decide_eq_true_eq] at hcond ⊢
  have hw := bf_mask_width hm
  bf_prep))

/-! ## Rules -/

/-- `ARM64.rules:1641`: `(SRAconst [rc] (SLLconst [lc] x)) && lc > rc => (SBFIZ [armBFAuxInt(lc-rc, 64-lc)] x)` -/
theorem r_ARM64_1641_sound : ArmRule.Checked r_ARM64_1641 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1643`: `(MOVWreg (SLLconst [lc] x)) && lc < 32 => (SBFIZ [armBFAuxInt(lc, 32-lc)] x)` -/
theorem r_ARM64_1643_sound : ArmRule.Checked r_ARM64_1643 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 32

/-- `ARM64.rules:1644`: `(MOVHreg (SLLconst [lc] x)) && lc < 16 => (SBFIZ [armBFAuxInt(lc, 16-lc)] x)` -/
theorem r_ARM64_1644_sound : ArmRule.Checked r_ARM64_1644 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 16

/-- `ARM64.rules:1645`: `(MOVBreg (SLLconst [lc] x)) && lc < 8 => (SBFIZ [armBFAuxInt(lc, 8-lc)] x)` -/
theorem r_ARM64_1645_sound : ArmRule.Checked r_ARM64_1645 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 8

/-- `ARM64.rules:1647`: `(SLLconst [lc] (MOVWreg x)) => (SBFIZ [armBFAuxInt(lc, min(32, 64-lc))] x)` -/
theorem r_ARM64_1647_sound : ArmRule.Checked r_ARM64_1647 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1648`: `(SLLconst [lc] (MOVHreg x)) => (SBFIZ [armBFAuxInt(lc, min(16, 64-lc))] x)` -/
theorem r_ARM64_1648_sound : ArmRule.Checked r_ARM64_1648 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1649`: `(SLLconst [lc] (MOVBreg x)) => (SBFIZ [armBFAuxInt(lc, min(8, 64-lc))] x)` -/
theorem r_ARM64_1649_sound : ArmRule.Checked r_ARM64_1649 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1653`: `(SRAconst [rc] (SLLconst [lc] x)) && lc <= rc => (SBFX [armBFAuxInt(rc-lc, 64-rc)] x)` -/
theorem r_ARM64_1653_sound : ArmRule.Checked r_ARM64_1653 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1655`: `(SRAconst [rc] (MOVWreg x)) && rc < 32 => (SBFX [armBFAuxInt(rc, 32-rc)] x)` -/
theorem r_ARM64_1655_sound : ArmRule.Checked r_ARM64_1655 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1656`: `(SRAconst [rc] (MOVHreg x)) && rc < 16 => (SBFX [armBFAuxInt(rc, 16-rc)] x)` -/
theorem r_ARM64_1656_sound : ArmRule.Checked r_ARM64_1656 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1657`: `(SRAconst [rc] (MOVBreg x)) && rc < 8 => (SBFX [armBFAuxInt(rc, 8-rc)] x)` -/
theorem r_ARM64_1657_sound : ArmRule.Checked r_ARM64_1657 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1659`: `(MOVWreg (SBFX [bfc] x)) && bfc.width() <= 32 => (SBFX [bfc] x)` -/
theorem r_ARM64_1659_sound : ArmRule.Checked r_ARM64_1659 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 32

/-- `ARM64.rules:1660`: `(MOVHreg (SBFX [bfc] x)) && bfc.width() <= 16 => (SBFX [bfc] x)` -/
theorem r_ARM64_1660_sound : ArmRule.Checked r_ARM64_1660 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 16

/-- `ARM64.rules:1661`: `(MOVBreg (SBFX [bfc] x)) && bfc.width() <= 8 => (SBFX [bfc] x)` -/
theorem r_ARM64_1661_sound : ArmRule.Checked r_ARM64_1661 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext true 8

/-- `ARM64.rules:1681`: `(SRLconst [rc] (SLLconst [lc] x)) && lc > rc => (UBFIZ [armBFAuxInt(lc-rc, 64-lc)] x)` -/
theorem r_ARM64_1681_sound : ArmRule.Checked r_ARM64_1681 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1683`: `(SLLconst [lc] (MOVWUreg x)) => (UBFIZ [armBFAuxInt(lc, min(32, 64-lc))] x)` -/
theorem r_ARM64_1683_sound : ArmRule.Checked r_ARM64_1683 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1684`: `(SLLconst [lc] (MOVHUreg x)) => (UBFIZ [armBFAuxInt(lc, min(16, 64-lc))] x)` -/
theorem r_ARM64_1684_sound : ArmRule.Checked r_ARM64_1684 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1685`: `(SLLconst [lc] (MOVBUreg x)) => (UBFIZ [armBFAuxInt(lc, min(8, 64-lc))] x)` -/
theorem r_ARM64_1685_sound : ArmRule.Checked r_ARM64_1685 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1687`: `(MOVWUreg (SLLconst [lc] x)) && lc < 32 => (UBFIZ [armBFAuxInt(lc, 32-lc)] x)` -/
theorem r_ARM64_1687_sound : ArmRule.Checked r_ARM64_1687 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 32

/-- `ARM64.rules:1688`: `(MOVHUreg (SLLconst [lc] x)) && lc < 16 => (UBFIZ [armBFAuxInt(lc, 16-lc)] x)` -/
theorem r_ARM64_1688_sound : ArmRule.Checked r_ARM64_1688 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 16

/-- `ARM64.rules:1689`: `(MOVBUreg (SLLconst [lc] x)) && lc < 8 => (UBFIZ [armBFAuxInt(lc, 8-lc)] x)` -/
theorem r_ARM64_1689_sound : ArmRule.Checked r_ARM64_1689 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 8

/-- `ARM64.rules:1701`: `(SRLconst [rc] (SLLconst [lc] x)) && lc < rc => (UBFX [armBFAuxInt(rc-lc, 64-rc)] x)` -/
theorem r_ARM64_1701_sound : ArmRule.Checked r_ARM64_1701 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1703`: `(SRLconst [rc] (MOVWUreg x)) && rc < 32 => (UBFX [armBFAuxInt(rc, 32-rc)] x)` -/
theorem r_ARM64_1703_sound : ArmRule.Checked r_ARM64_1703 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1704`: `(SRLconst [rc] (MOVHUreg x)) && rc < 16 => (UBFX [armBFAuxInt(rc, 16-rc)] x)` -/
theorem r_ARM64_1704_sound : ArmRule.Checked r_ARM64_1704 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1705`: `(SRLconst [rc] (MOVBUreg x)) && rc < 8 => (UBFX [armBFAuxInt(rc, 8-rc)] x)` -/
theorem r_ARM64_1705_sound : ArmRule.Checked r_ARM64_1705 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1707`: `(MOVWUreg (SRLconst [rc] x)) && rc < 32 => (UBFX [armBFAuxInt(rc, 32)] x)` -/
theorem r_ARM64_1707_sound : ArmRule.Checked r_ARM64_1707 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 32

/-- `ARM64.rules:1708`: `(MOVHUreg (SRLconst [rc] x)) && rc < 16 => (UBFX [armBFAuxInt(rc, 16)] x)` -/
theorem r_ARM64_1708_sound : ArmRule.Checked r_ARM64_1708 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 16

/-- `ARM64.rules:1709`: `(MOVBUreg (SRLconst [rc] x)) && rc < 8 => (UBFX [armBFAuxInt(rc, 8)] x)` -/
theorem r_ARM64_1709_sound : ArmRule.Checked r_ARM64_1709 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 8

/-- `ARM64.rules:1723`: `(MOVWUreg (UBFX [bfc] x)) && bfc.width() <= 32 => (UBFX [bfc] x)` -/
theorem r_ARM64_1723_sound : ArmRule.Checked r_ARM64_1723 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 32

/-- `ARM64.rules:1724`: `(MOVHUreg (UBFX [bfc] x)) && bfc.width() <= 16 => (UBFX [bfc] x)` -/
theorem r_ARM64_1724_sound : ArmRule.Checked r_ARM64_1724 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 16

/-- `ARM64.rules:1725`: `(MOVBUreg (UBFX [bfc] x)) && bfc.width() <= 8 => (UBFX [bfc] x)` -/
theorem r_ARM64_1725_sound : ArmRule.Checked r_ARM64_1725 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rext false 8

/-- `ARM64.rules:1731`: `(UBFX [bfc] e:(MOVWUreg x)) && e.Uses == 1 && bfc.lsb() < 32 => (UBFX [armBFAuxInt(bfc.lsb(), min(bfc.width(), 32-bfc.lsb()))] x)` -/
theorem r_ARM64_1731_sound : ArmRule.Checked r_ARM64_1731 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1735`: `(UBFX [bfc] e:(MOVHUreg x)) && e.Uses == 1 && bfc.lsb() < 16 => (UBFX [armBFAuxInt(bfc.lsb(), min(bfc.width(), 16-bfc.lsb()))] x)` -/
theorem r_ARM64_1735_sound : ArmRule.Checked r_ARM64_1735 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1739`: `(UBFX [bfc] e:(MOVBUreg x)) && e.Uses == 1 && bfc.lsb() < 8 => (UBFX [armBFAuxInt(bfc.lsb(), min(bfc.width(), 8-bfc.lsb()))] x)` -/
theorem r_ARM64_1739_sound : ArmRule.Checked r_ARM64_1739 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1743`: `(SRLconst [sc] (UBFX [bfc] x)) && sc < bfc.width() => (UBFX [armBFAuxInt(bfc.lsb()+sc, bfc.width()-sc)] x)` -/
theorem r_ARM64_1743_sound : ArmRule.Checked r_ARM64_1743 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1713`: `(ANDconst [ac] (SRLconst [sc] x)) && isARM64BFMask(sc, ac, 0) => (UBFX [armBFAuxInt(sc, arm64BFWidth(ac, 0))] x)` -/
theorem r_ARM64_1713_sound : ArmRule.Checked r_ARM64_1713 := by
  left; arm_unfold; arm_norm; bf_mask (e.auxInt []).toInt 0; bf_inand; bf_bits [bf_mask_getLsbD hm]

/-- `ARM64.rules:1718`: `(ANDconst [c] (UBFX [bfc] x)) && isARM64BFMask(0, c, 0) => (UBFX [armBFAuxInt(bfc.lsb(), min(bfc.width(), arm64BFWidth(c, 0)))] x)` -/
theorem r_ARM64_1718_sound : ArmRule.Checked r_ARM64_1718 := by
  left; arm_unfold; arm_norm; bf_mask (e.auxInt []).toInt 0; bf_inand; bf_bits [bf_mask_getLsbD hm]

/-- `ARM64.rules:1697`: `(ANDconst [ac] (SLLconst [sc] x)) && isARM64BFMask(sc, ac, sc) => (UBFIZ [armBFAuxInt(sc, arm64BFWidth(ac, sc))] x)` -/
theorem r_ARM64_1697_sound : ArmRule.Checked r_ARM64_1697 := by
  left; arm_unfold; arm_norm; bf_mask (e.auxInt []).toInt (e.auxInt [0]).toInt; bf_inand
  bf_bits [bf_mask_getLsbD hm]

/-- `ARM64.rules:1716`: `(SRLconst [sc] (ANDconst [ac] x)) && isARM64BFMask(sc, ac, sc) => (UBFX [armBFAuxInt(sc, arm64BFWidth(ac, sc))] x)` -/
theorem r_ARM64_1716_sound : ArmRule.Checked r_ARM64_1716 := by
  left; arm_unfold; arm_norm; bf_mask (e.auxInt [0]).toInt (e.auxInt []).toInt; bf_in64
  bf_bits [bf_mask_getLsbD hm]

/-- `ARM64.rules:1694`: `(SLLconst [sc] (ANDconst [ac] x)) && isARM64BFMask(sc, ac, 0) => (UBFIZ [armBFAuxInt(sc, arm64BFWidth(ac, 0))] x)` -/
theorem r_ARM64_1694_sound : ArmRule.Checked r_ARM64_1694 := by
  left; arm_unfold; arm_norm; bf_mask (e.auxInt [0]).toInt 0; bf_insll; bf_bits [bf_mask_getLsbD hm]

/-- `ARM64.rules:1665`: `(SRAconst [sc] (SBFIZ [bfc] x)) && sc < bfc.lsb() => (SBFIZ [armBFAuxInt(bfc.lsb()-sc, bfc.width())] x)` -/
theorem r_ARM64_1665_sound : ArmRule.Checked r_ARM64_1665 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1668`: `(SRAconst [sc] (SBFIZ [bfc] x)) && sc >= bfc.lsb() && sc < bfc.lsb()+bfc.width() => (SBFX [armBFAuxInt(sc-bfc.lsb(), bfc.lsb()+bfc.width()-sc)] x)` -/
theorem r_ARM64_1668_sound : ArmRule.Checked r_ARM64_1668 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1672`: `(SBFX [bfc] s:(SLLconst [sc] x)) && s.Uses == 1 && sc <= bfc.lsb() => (SBFX [armBFAuxInt(bfc.lsb() - sc, bfc.width())] x)` -/
theorem r_ARM64_1672_sound : ArmRule.Checked r_ARM64_1672 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1677`: `(SBFX [bfc] s:(SLLconst [sc] x)) && s.Uses == 1 && sc > bfc.lsb() && sc < bfc.lsb()+bfc.width() => (SBFIZ [armBFAuxInt(sc - bfc.lsb(), bfc.width() - (sc-bfc.lsb()))] x)` -/
theorem r_ARM64_1677_sound : ArmRule.Checked r_ARM64_1677 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1745`: `(UBFX [bfc] (SRLconst [sc] x)) && sc+bfc.width()+bfc.lsb() < 64 => (UBFX [armBFAuxInt(bfc.lsb()+sc, bfc.width())] x)` -/
theorem r_ARM64_1745_sound : ArmRule.Checked r_ARM64_1745 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1747`: `(SLLconst [sc] (UBFIZ [bfc] x)) && sc+bfc.width()+bfc.lsb() < 64 => (UBFIZ [armBFAuxInt(bfc.lsb()+sc, bfc.width())] x)` -/
theorem r_ARM64_1747_sound : ArmRule.Checked r_ARM64_1747 := by
  left; arm_unfold; arm_norm; bf_prep; bf_rsll

/-- `ARM64.rules:1749`: `(UBFIZ [bfc] (SLLconst [sc] x)) && sc < bfc.width() => (UBFIZ [armBFAuxInt(bfc.lsb()+sc, bfc.width()-sc)] x)` -/
theorem r_ARM64_1749_sound : ArmRule.Checked r_ARM64_1749 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1754`: `(SRLconst [sc] (UBFIZ [bfc] x)) && sc < bfc.lsb() => (UBFIZ [armBFAuxInt(bfc.lsb()-sc, bfc.width())] x)` -/
theorem r_ARM64_1754_sound : ArmRule.Checked r_ARM64_1754 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1757`: `(SRLconst [sc] (UBFIZ [bfc] x)) && sc > bfc.lsb() && sc < bfc.lsb()+bfc.width() => (UBFX [armBFAuxInt(sc-bfc.lsb(), bfc.lsb()+bfc.width()-sc)] x)` -/
theorem r_ARM64_1757_sound : ArmRule.Checked r_ARM64_1757 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1762`: `(UBFX [bfc] (SLLconst [sc] x)) && sc < bfc.lsb() => (UBFX [armBFAuxInt(bfc.lsb()-sc, bfc.width())] x)` -/
theorem r_ARM64_1762_sound : ArmRule.Checked r_ARM64_1762 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1765`: `(UBFX [bfc] (SLLconst [sc] x)) && sc > bfc.lsb() && sc < bfc.lsb()+bfc.width() => (UBFIZ [armBFAuxInt(sc-bfc.lsb(), bfc.lsb()+bfc.width()-sc)] x)` -/
theorem r_ARM64_1765_sound : ArmRule.Checked r_ARM64_1765 := by
  left; arm_unfold; arm_norm; bf_prep; bf_r64

/-- `ARM64.rules:1853`: `(ANDconst [0xffffffff] x) => (MOVWUreg x)` -/
theorem r_ARM64_1853_sound : ArmRule.Checked r_ARM64_1853 := by
  left; arm_unfold; arm_norm
  simp only [DV.int.injEq] at hc
  have hf : (fun x => x &&& BitVec.ofInt 64 (e.auxInt []).toInt) = Arm64.ext false 32 := by
    funext x; rw [hc]; rfl
  rw [hf]; exact Refines.refl _

/-- `ARM64.rules:1854`: `(ANDconst [0xffff ] x) => (MOVHUreg x)` -/
theorem r_ARM64_1854_sound : ArmRule.Checked r_ARM64_1854 := by
  left; arm_unfold; arm_norm
  simp only [DV.int.injEq] at hc
  have hf : (fun x => x &&& BitVec.ofInt 64 (e.auxInt []).toInt) = Arm64.ext false 16 := by
    funext x; rw [hc]; rfl
  rw [hf]; exact Refines.refl _

/-- `ARM64.rules:1855`: `(ANDconst [0xff ] x) => (MOVBUreg x)` -/
theorem r_ARM64_1855_sound : ArmRule.Checked r_ARM64_1855 := by
  left; arm_unfold; arm_norm
  simp only [DV.int.injEq] at hc
  have hf : (fun x => x &&& BitVec.ofInt 64 (e.auxInt []).toInt) = Arm64.ext false 8 := by
    funext x; rw [hc]; rfl
  rw [hf]; exact Refines.refl _

end GoFV.Proof.Low.Rules
