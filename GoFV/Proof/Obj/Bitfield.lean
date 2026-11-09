import GoFV.Proof.Obj.Basic

variable [GoFV.SSA.Sem.Addrs]

/-!
# The bitfield moves the assembler encodes shifts, field extracts and extensions as

`progSym` (`GoFV/Asm/CheckObj.lean`) describes a P0 constant shift, `UBFX`/`SBFX`/`UBFIZ` and the
`MOV{B,BU,H,HU,W}` register extensions by the bitfield move (`UBFM`/`SBFM`) the assembler encodes
them as; here each equals what `progEffect` computes (`dp2Op` of a constant amount, `ubfx`,
`sbfx`, `ubfiz`, `sext`, `maskN`), for every operand.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Arm64.ProgOp
open GoFV.SSA.Sem.Arm64 (sext ubfx sbfx ubfiz)

/-- The datasize in bits. -/
abbrev wOf (sf : Bool) : Nat := if sf then 64 else 32

/-- `DecodeBitMasks` of a 64-bit bitfield move: `wmask = ROR(ones(imms+1), immr)`,
`tmask = ones(d+1)`, `d = (imms - immr) mod 64`. -/
private theorem bfT_dbm64 (imms immr : BitVec 6) :
    decodeBitMasks 64 true imms immr false =
      some ((BitVec.ofNat 64 (2 ^ (imms.toNat + 1) - 1)).rotateRight immr.toNat,
        BitVec.ofNat 64 (2 ^ ((imms.toNat + 64 - immr.toNat) % 64 + 1) - 1)) := by
  have hs := imms.isLt
  have hr := immr.isLt
  have h1 : highestSetBit (BitVec.ofBool true ++ ~~~imms) = some 6 := by
    simp only [highestSetBit, List.find?, BitVec.getLsbD_append]
    simp
  have h2 : imms.toNat % 64 = imms.toNat := Nat.mod_eq_of_lt hs
  have h3 : immr.toNat % 64 = immr.toNat := Nat.mod_eq_of_lt hr
  unfold decodeBitMasks
  rw [h1]
  simp [h2, h3, replicateTo, BitVec.ofNat_toNat, -BitVec.toNat_rotateRight]

/-- `bfT_dbm64` at 32 bits (`imms`, `immr` below 32). -/
private theorem bfT_dbm32 (imms immr : BitVec 6) (hs : imms.toNat < 32) (hr : immr.toNat < 32) :
    decodeBitMasks 32 false imms immr false =
      some ((BitVec.ofNat 32 (2 ^ (imms.toNat + 1) - 1)).rotateRight immr.toNat,
        BitVec.ofNat 32 (2 ^ ((imms.toNat + 32 - immr.toNat) % 32 + 1) - 1)) := by
  have h5 : imms[5] = false := by
    rw [← BitVec.getLsbD_eq_getElem]
    simp only [BitVec.getLsbD]; exact Nat.testBit_lt_two_pow (by omega)
  have h1 : highestSetBit (BitVec.ofBool false ++ ~~~imms) = some 5 := by
    simp only [highestSetBit, List.find?, BitVec.getLsbD_append]
    simp [h5]
  have h2 : imms.toNat % 32 = imms.toNat := Nat.mod_eq_of_lt hs
  have h3 : immr.toNat % 32 = immr.toNat := Nat.mod_eq_of_lt hr
  unfold decodeBitMasks
  rw [h1]
  simp [h2, h3, replicateTo, BitVec.ofNat_toNat, -BitVec.toNat_rotateRight]

/-- Bit `i` of a rotation. -/
private theorem bfT_rot {n : Nat} (y : BitVec n) (r i : Nat) (hr : r < n) (hi : i < n) :
    (y.rotateRight r).getLsbD i = y.getLsbD ((i + r) % n) := by
  rw [BitVec.getLsbD_rotateRight, Nat.mod_eq_of_lt hr]
  by_cases h : i + r < n
  · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)), Nat.mod_eq_of_lt h, Nat.add_comm]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), Nat.mod_eq_sub_mod (by omega),
      Nat.mod_eq_of_lt (by omega)]
    simp only [hi, decide_true, Bool.true_and]
    congr 1; omega

/-- Bit `i` of `UBFM`/`SBFM` (zero destination). -/
private theorem bfT_bit (sf : Bool) (opc : BitVec 2) (hopc : opc ≠ 1) (immr imms : BitVec 6)
    (hr : immr.toNat < wOf sf) (hs : imms.toNat < wOf sf) (x : BitVec 64) (i : Nat) :
    (bitfieldMove sf opc immr imms 0 x).getLsbD i =
      (decide (i < wOf sf) &&
        if i ≤ (imms.toNat + wOf sf - immr.toNat) % wOf sf then
          decide ((i + immr.toNat) % wOf sf ≤ imms.toNat) && x.getLsbD ((i + immr.toNat) % wOf sf)
        else decide (opc = 0) && x.getLsbD imms.toNat) := by
  have h1 : (opc != 1) = true := by simpa using hopc
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hr hs ⊢
    simp only [bitfieldMove, sized, bfT_dbm32 imms immr hs hr, h1, Bool.false_eq_true, ↓reduceIte,
      BitVec.getLsbD_setWidth]
    by_cases hi : i < 32
    · have hr' := bfT_rot (BitVec.setWidth 32 x) _ _ hr hi
      have hw := bfT_rot (BitVec.ofNat 32 (2 ^ (imms.toNat + 1) - 1)) _ _ hr hi
      have hm1 : (-1 : BitVec 32) = BitVec.allOnes 32 := BitVec.neg_one_eq_allOnes
      have hz : ∀ j, (0 : BitVec 32).getLsbD j = false := fun _ => BitVec.getLsbD_zero
      have hlt : (i + immr.toNat) % 32 < 32 := Nat.mod_lt _ (by decide)
      have hi64 : i < 64 := by omega
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hz, hr', hw,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, BitVec.getLsbD_setWidth, hi, hlt, hs,
        hi64, decide_true, Bool.true_and, Nat.lt_add_one_iff]
      by_cases ho : opc = 0
      · cases hx : x.getLsbD imms.toNat <;>
          simp only [ho, Bool.false_eq_true, ↓reduceIte, hm1, BitVec.getLsbD_allOnes, hz, hi,
            decide_true, Bool.true_and] <;>
          by_cases h₁ : i ≤ (imms.toNat + 32 - immr.toNat) % 32 <;>
          by_cases h₂ : (i + immr.toNat) % 32 ≤ imms.toNat <;> simp [h₁, h₂]
      · simp only [ho, ↓reduceIte, hz, decide_false, Bool.false_and]
        by_cases h₁ : i ≤ (imms.toNat + 32 - immr.toNat) % 32 <;>
          by_cases h₂ : (i + immr.toNat) % 32 ≤ imms.toNat <;> simp [h₁, h₂]
    · simp [hi, BitVec.getLsbD_of_ge _ i (Nat.le_of_not_lt hi)]
  · simp only [wOf, ↓reduceIte] at hr hs ⊢
    simp only [bitfieldMove, sized, bfT_dbm64 imms immr, h1, ↓reduceIte, BitVec.setWidth_eq]
    by_cases hi : i < 64
    · have hr' := bfT_rot x _ _ hr hi
      have hw := bfT_rot (BitVec.ofNat 64 (2 ^ (imms.toNat + 1) - 1)) _ _ hr hi
      have hm1 : (-1 : BitVec 64) = BitVec.allOnes 64 := BitVec.neg_one_eq_allOnes
      have hz : ∀ j, (0 : BitVec 64).getLsbD j = false := fun _ => BitVec.getLsbD_zero
      have hlt : (i + immr.toNat) % 64 < 64 := Nat.mod_lt _ (by decide)
      simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, hz, hr', hw,
        BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, hi, hlt,
        decide_true, Bool.true_and, Nat.lt_add_one_iff]
      by_cases ho : opc = 0
      · cases hx : x.getLsbD imms.toNat <;>
          simp only [ho, Bool.false_eq_true, ↓reduceIte, hm1, BitVec.getLsbD_allOnes, hz, hi,
            decide_true, Bool.true_and] <;>
          by_cases h₁ : i ≤ (imms.toNat + 64 - immr.toNat) % 64 <;>
          by_cases h₂ : (i + immr.toNat) % 64 ≤ imms.toNat <;> simp [h₁, h₂]
      · simp only [ho, ↓reduceIte, hz, decide_false, Bool.false_and]
        by_cases h₁ : i ≤ (imms.toNat + 64 - immr.toNat) % 64 <;>
          by_cases h₂ : (i + immr.toNat) % 64 ≤ imms.toNat <;> simp [h₁, h₂]
    · simp [hi, BitVec.getLsbD_of_ge _ i (Nat.le_of_not_lt hi)]

private theorem bfT_dt {p : Prop} [Decidable p] (h : p) : decide p = true := decide_eq_true h
private theorem bfT_df {p : Prop} [Decidable p] (h : ¬p) : decide p = false := decide_eq_false h
private theorem bfT_it {p : Prop} [Decidable p] {α : Sort _} (a b : α) (h : p) :
    (if p then a else b) = a := by simp [h]
private theorem bfT_if {p : Prop} [Decidable p] {α : Sort _} (a b : α) (h : ¬p) :
    (if p then a else b) = b := by simp [h]
private theorem bfT_d0 : decide ((0 : BitVec 2) = 0) = true := rfl
private theorem bfT_d2 : decide ((2 : BitVec 2) = 0) = false := rfl

/-- Decide the linear `decide`s and `if`s by `omega` and simplify the Boolean connectives. -/
local macro "bfT_simp" : tactic =>
  `(tactic| simp (disch := omega) only [bfT_dt, bfT_df, bfT_it, bfT_if, Bool.true_and,
    Bool.false_and, Bool.and_true, Bool.not_true, Bool.not_false, Bool.and_false, bfT_d0, bfT_d2,
    ite_self, decide_true, decide_false])

/-- `bfT_bit` at 32 bits, the immediates given as numbers. -/
private theorem bfT_bit32 (opc : BitVec 2) (hopc : opc ≠ 1) (immr imms : BitVec 6) (r s : Nat)
    (hr : immr.toNat = r) (hs : imms.toNat = s) (hr' : r < 32) (hs' : s < 32) (x : BitVec 64)
    (i : Nat) :
    (bitfieldMove false opc immr imms 0 x).getLsbD i =
      (decide (i < 32) &&
        if i ≤ (s + 32 - r) % 32 then decide ((i + r) % 32 ≤ s) && x.getLsbD ((i + r) % 32)
        else decide (opc = 0) && x.getLsbD s) := by
  subst hr hs
  exact bfT_bit false opc hopc immr imms hr' hs' x i

private theorem bfT_bit64 (opc : BitVec 2) (hopc : opc ≠ 1) (immr imms : BitVec 6) (r s : Nat)
    (hr : immr.toNat = r) (hs : imms.toNat = s) (x : BitVec 64) (i : Nat) :
    (bitfieldMove true opc immr imms 0 x).getLsbD i =
      (decide (i < 64) &&
        if i ≤ (s + 64 - r) % 64 then decide ((i + r) % 64 ≤ s) && x.getLsbD ((i + r) % 64)
        else decide (opc = 0) && x.getLsbD s) := by
  subst hr hs
  exact bfT_bit true opc hopc immr imms immr.isLt imms.isLt x i

private theorem bfT_bf (lsb width : Nat) (hl : lsb ≤ 64) (hw : width ≤ 64) :
    GoFV.SSA.Sem.Arm64.bf (Int64.ofNat (lsb * 256 + width)) = (lsb, width) := by
  simp only [GoFV.SSA.Sem.Arm64.bf,
    Int64.toInt_ofNat_of_lt (show lsb * 256 + width < 2 ^ 63 by omega),
    Int.toNat_natCast]
  congr 1 <;> omega

/-- Bit `i` of `sext w y`. -/
private theorem bfT_sext_bit (w : Nat) (hw : 0 < w ∧ w ≤ 64) (y : BitVec 64) (i : Nat)
    (hi : i < 64) :
    (sext w y).getLsbD i = if i < w then y.getLsbD i else y.getLsbD (w - 1) := by
  simp only [sext, show w ≠ 0 by omega, ↓reduceIte, BitVec.getLsbD_sshiftRight,
    BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, Nat.reduceSub]
  by_cases hiw : i < w
  · have e : 64 - w + i - (64 - w) = i := by omega
    rw [e]; bfT_simp
  · have e : 63 - (64 - w) = w - 1 := by omega
    rw [e]; bfT_simp

theorem lsl_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 8 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 ((wOf sf - k) % wOf sf)) (BitVec.ofNat 6 (wOf sf - 1 - k)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h8 : (8 : BitVec 6).toNat = 8 := rfl
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    rw [bfT_bit32 2 (by decide) _ _ ((32 - k) % 32) (32 - 1 - k)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
      (by omega) (by omega)]
    have hk32 : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hkm : k % 32 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, Bool.false_eq_true, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq, h8, hk32, hkm,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft]
    by_cases hi32 : i < 32
    · by_cases hki : k ≤ i
      · rw [show (i + (32 - k) % 32) % 32 = i - k by omega]; bfT_simp
      · bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hk ⊢
    rw [bfT_bit64 2 (by decide) _ _ ((64 - k) % 64) (64 - 1 - k)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)]
    have hk64 : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; omega
    have hkm : k % 64 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, ↓reduceIte, BitVec.setWidth_eq,
      h8, hk64, hkm,
      BitVec.getLsbD_shiftLeft]
    by_cases hki : k ≤ i
    · rw [show (i + (64 - k) % 64) % 64 = i - k by omega]; bfT_simp
    · bfT_simp

theorem lsr_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 9 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h9 : (9 : BitVec 6).toNat = 9 := rfl
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    rw [bfT_bit32 2 (by decide) _ _ k (32 - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat])
      (by omega) (by omega)]
    have hk32 : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hkm : k % 32 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, Bool.false_eq_true, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq, h9, hk32, hkm,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
    by_cases hi32 : i + k < 32
    · rw [show (i + k) % 32 = k + i by omega]; bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hk ⊢
    rw [bfT_bit64 2 (by decide) _ _ k (64 - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat])]
    have hk64 : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; omega
    have hkm : k % 64 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, ↓reduceIte, BitVec.setWidth_eq,
      h9, hk64, hkm,
      BitVec.getLsbD_ushiftRight]
    by_cases hi64 : i + k < 64
    · rw [show (i + k) % 64 = k + i by omega]; bfT_simp
    · rw [BitVec.getLsbD_of_ge x (k + i) (by omega)]; bfT_simp

theorem asr_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 10 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 0 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h10 : (10 : BitVec 6).toNat = 10 := rfl
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hk ⊢
    rw [bfT_bit32 0 (by decide) _ _ k (32 - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat])
      (by omega) (by omega)]
    have hk32 : ((BitVec.ofNat 64 k).setWidth 32).toNat = k := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    have hkm : k % 32 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, Bool.false_eq_true, ↓reduceIte,
      BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide), BitVec.setWidth_eq, h10, hk32, hkm,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last,
      Nat.reduceSub]
    by_cases hi32 : i < 32
    · by_cases hik : k + i < 32
      · rw [show (i + k) % 32 = k + i by omega]; bfT_simp
      · bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hk ⊢
    rw [bfT_bit64 0 (by decide) _ _ k (64 - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat])]
    have hk64 : (BitVec.ofNat 64 k).toNat = k := by simp only [BitVec.toNat_ofNat]; omega
    have hkm : k % 64 = k := Nat.mod_eq_of_lt hk.2
    simp only [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply, trunc, ↓reduceIte, BitVec.setWidth_eq,
      h10, hk64, hkm,
      BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last, Nat.reduceSub]
    by_cases hik : k + i < 64
    · rw [show (i + k) % 64 = k + i by omega]; bfT_simp
    · bfT_simp

theorem ubfx_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (ubfx (Int64.ofNat (lsb * 256 + width)) (trunc sf x)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    rw [bfT_bit32 2 (by decide) _ _ lsb (lsb + width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
      (by omega) (by omega)]
    simp only [trunc, Bool.false_eq_true, ↓reduceIte, ubfx, bfT_bf lsb width (by omega) (by omega),
      GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hiw : i < width
    · rw [show (i + lsb) % 32 = lsb + i by omega]; bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hb ⊢
    rw [bfT_bit64 2 (by decide) _ _ lsb (lsb + width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)]
    simp only [trunc, ↓reduceIte, ubfx, bfT_bf lsb width (by omega) (by omega),
      GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_and,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hiw : i < width
    · rw [show (i + lsb) % 64 = lsb + i by omega]; bfT_simp
    · bfT_simp

theorem sbfx_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (sbfx (Int64.ofNat (lsb * 256 + width)) (trunc sf x)) =
      bitfieldMove sf 0 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    rw [bfT_bit32 0 (by decide) _ _ lsb (lsb + width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
      (by omega) (by omega)]
    simp only [trunc, Bool.false_eq_true, ↓reduceIte, sbfx, bfT_bf lsb width (by omega) (by omega),
      BitVec.getLsbD_setWidth]
    rw [bfT_sext_bit width ⟨hw, by omega⟩ _ i hi]
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
    by_cases hi32 : i < 32
    · by_cases hiw : i < width
      · rw [show (i + lsb) % 32 = lsb + i by omega]; bfT_simp
      · rw [show lsb + (width - 1) = lsb + width - 1 by omega]; bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hb ⊢
    rw [bfT_bit64 0 (by decide) _ _ lsb (lsb + width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)]
    simp only [trunc, ↓reduceIte, sbfx, bfT_bf lsb width (by omega) (by omega)]
    rw [bfT_sext_bit width ⟨hw, by omega⟩ _ i hi]
    simp only [BitVec.getLsbD_ushiftRight]
    by_cases hiw : i < width
    · rw [show (i + lsb) % 64 = lsb + i by omega]; bfT_simp
    · rw [show lsb + (width - 1) = lsb + width - 1 by omega]; bfT_simp

theorem ubfiz_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (ubfiz (Int64.ofNat (lsb * 256 + width)) x) =
      bitfieldMove sf 2 (BitVec.ofNat 6 ((wOf sf - lsb) % wOf sf)) (BitVec.ofNat 6 (width - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases sf
  · simp only [wOf, Bool.false_eq_true, ↓reduceIte] at hb ⊢
    rw [bfT_bit32 2 (by decide) _ _ ((32 - lsb) % 32) (width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)
      (by omega) (by omega)]
    simp only [trunc, Bool.false_eq_true, ↓reduceIte, ubfiz, bfT_bf lsb width (by omega) (by omega),
      GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_setWidth, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hi32 : i < 32
    · by_cases h1 : lsb ≤ i
      · by_cases h2 : i < lsb + width
        · rw [show (i + (32 - lsb) % 32) % 32 = i - lsb by omega]; bfT_simp
        · bfT_simp
      · bfT_simp
    · bfT_simp
  · simp only [wOf, ↓reduceIte] at hb ⊢
    rw [bfT_bit64 2 (by decide) _ _ ((64 - lsb) % 64) (width - 1)
      (by simp only [BitVec.toNat_ofNat]; omega) (by simp only [BitVec.toNat_ofNat]; omega)]
    simp only [trunc, ↓reduceIte, ubfiz, bfT_bf lsb width (by omega) (by omega),
      GoFV.SSA.Sem.Arm64.mask, BitVec.getLsbD_and,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases h1 : lsb ≤ i
    · by_cases h2 : i < lsb + width
      · rw [show (i + (64 - lsb) % 64) % 64 = i - lsb by omega]; bfT_simp
      · bfT_simp
    · bfT_simp

/-- `MOVB`/`MOVH`/`MOVW` between registers: `SBFM Xd, Xn, #0, #(8n − 1)`. -/
theorem sext_bfm (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) (x : BitVec 64) :
    sextTo64 n x = bitfieldMove true 0 0 (BitVec.ofNat 6 (8 * n - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bfT_bit64 0 (by decide) _ _ 0 (8 * n - 1) rfl (by simp only [BitVec.toNat_ofNat]; omega)]
  simp only [sextTo64]
  rw [bfT_sext_bit (8 * n) ⟨by omega, by omega⟩ _ i hi]
  by_cases hin : i < 8 * n
  · rw [show (i + 0) % 64 = i by omega]; bfT_simp
  · bfT_simp

/-- `MOVBU`/`MOVHU` between registers: `UBFM Xd, Xn, #0, #(8n − 1)`. -/
theorem zext_bfm (n : Nat) (hn : n = 1 ∨ n = 2) (x : BitVec 64) :
    maskN n x = bitfieldMove true 2 0 (BitVec.ofNat 6 (8 * n - 1)) 0 x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [bfT_bit64 2 (by decide) _ _ 0 (8 * n - 1) rfl (by simp only [BitVec.toNat_ofNat]; omega)]
  have h8 : (n == 8) = false := by rcases hn with rfl | rfl <;> rfl
  simp only [maskN, h8, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hin : i < 8 * n
  · rw [show (i + 0) % 64 = i by omega]; bfT_simp
  · bfT_simp

/-- `MOVWU` between registers: `ORR Wd, WZR, Wn`. -/
theorem zext32 (x : BitVec 64) : maskN 4 x = trunc false x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h8 : (4 == 8) = false := rfl
  simp only [maskN, h8, Bool.false_eq_true, ↓reduceIte, trunc, BitVec.getLsbD_and,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, BitVec.getLsbD_setWidth, Nat.reduceMul]
  by_cases hi32 : i < 32
  · bfT_simp
  · bfT_simp

end GoFV.Proof.Obj
