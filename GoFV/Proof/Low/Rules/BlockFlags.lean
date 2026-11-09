import GoFV.Proof.Low.Rules.Peep
import GoFV.Proof.Rules.DivisibleInv

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: block rules on flags with a variable control (`ARM64.rules:556`, `621-624`, `644-647`, `1332-1341`)

Block rules of lowered code that branch on a rule variable (#385):

* `(GE|LT (CMPconst [0] x))` as `(TBZ|TBNZ [63] x)`, `(GE|LT (CMPWconst [0] x))` as `(TBZ|TBNZ
  [31] x)`: the flags of `x - 0` have `V` clear and `N` the sign bit (`subFlags_zero`), so `GE`
  and `LT` read the sign bit; a pointer without an address leaves `N` unknown (`reg_of_cmp0`).
* `(EQ|NE (TSTconst [c] x)) && oneBit(c)` as `(TBZ|TBNZ [ntz64(c)] x)`, and the `TSTWconst` forms
  on `int64(uint32(c))`: `c` is the single bit `ntz64(c)` (`oneBit_twoPow`, `oneBit_twoPow32`),
  whose `AND` with the register is zero iff the bit is clear (`and_twoPow_eq_zero`).
* `(K (InvertFlags cmp))` as `(K' cmp)` for the integer kinds: `K` on the flags of the swapped
  compare is `K'` on `cmp`, whatever `cmp` (`invertFlags_cond`).
* `(TB(Z|NZ) [0] (XORconst [1] x))` as `(TB(NZ|Z) [0] x)`: bit 0 of the `XORconst`'s register,
  read back at its shape, is bit 0 of `x`'s register flipped (`xor1_bit0`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- The flags of `x - 0`: `N` the sign bit, `Z` whether `x` is zero, `C` set, `V` clear. -/
theorem subFlags_zero {n : Nat} (hn : 0 < n) (r : BitVec n) :
    (Arm64.subFlags r 0).2 = ⟨r.msb, r == 0, true, false⟩ := by
  have h : BitVec.ofNat n (r.toNat + (~~~(0 : BitVec n)).toNat + 1) = r := by
    apply BitVec.eq_of_toNat_eq
    have := r.isLt
    have h0 : (0 : BitVec n).toNat = 0 := by simp
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0]
    rw [show r.toNat + (2 ^ n - 1 - 0) + 1 = r.toNat + 2 ^ n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt this]
  have hnot : (~~~(0 : BitVec n)).toNat = 2 ^ n - 1 := by simp
  have hint : (~~~(0 : BitVec n)).toInt = -1 := by
    rw [show ~~~(0 : BitVec n) = BitVec.allOnes n by simp]
    simp [BitVec.toInt_allOnes, hn]
  have := Nat.two_pow_pos n
  simp only [Arm64.subFlags, addWithCarry, ite_true]
  rw [h]
  simp only [hnot, hint]
  congr 1
  · simp only [bne_iff_ne, ne_eq]; omega
  · have : r.toInt + -1 + 1 = r.toInt := by omega
    simp [this]

/-- A condition that reads the `N` bit (`GE`, `LT`): undefined when it is unknown. -/
def readsN (c : Cond) : Prop := ∀ z, c.eval none (some z) none none = none

/-- A defined condition on the flags of `CMPconst [0] x` that reads `N`: `x` has a register. -/
theorem reg_of_cmp0 {x : Val} {c : Cond} {b : Bool} (hc : readsN c)
    (h : c.onVal (Arm64.cmp x (.int .w64 0)) = some b) :
    ∃ r, Arm64.reg x = some r ∧ c.onVal (Arm64.subFlags r 0).2.toVal = some b := by
  have h0 : Arm64.reg (.int .w64 (0 : BitVec 64)) = some 0 := rfl
  cases hx : Arm64.reg x with
  | some r =>
    refine ⟨r, rfl, ?_⟩
    have hc' : Arm64.cmp x (.int .w64 0) = Arm64.cmpRes (Arm64.subFlags r 0) := by
      unfold Arm64.cmp; rw [hx, h0]
    rwa [hc', onVal_cmpRes] at h
  | none =>
    cases x with
    | ptr p =>
      have hc' : Arm64.cmp (.ptr p) (.int .w64 0) =
          .agg [.poison, .bool false, .poison, .poison, .poison] := by
        unfold Arm64.cmp; simp only [Arm64.reg] at hx; simp only [Arm64.reg, hx]; rfl
      rw [hc'] at h
      simp only [Cond.onVal, Val.flagBit] at h
      rw [hc] at h; cases h
    | _ => simp_all [Arm64.cmp, Arm64.reg, Cond.onVal]

/-- A defined condition on the flags of `CMPWconst [0] x`: `x` has a register. -/
theorem reg_of_cmpw0 {x : Val} {c : Cond} {b : Bool}
    (h : c.onVal (Arm64.cmp1w (fun r => Arm64.subFlags r 0) [x]) = some b) :
    ∃ r, Arm64.reg x = some r ∧ c.onVal (Arm64.subFlags (r.setWidth 32) 0).2.toVal = some b := by
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 h
  cases hx : Arm64.reg x with
  | none => simp [Arm64.reg32, hx] at hr
  | some R =>
    simp only [Arm64.reg32, hx, Option.map_some, Option.some.injEq] at hr
    exact ⟨R, rfl, hr ▸ h⟩

private theorem ge_n {n : Nat} (hn : 0 < n) {r : BitVec n} {b : Bool}
    (h : Cond.ge.onVal (Arm64.subFlags r 0).2.toVal = some b) : (!r.msb) = b := by
  simp only [subFlags_zero hn, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit] at h
  cases hm : r.msb <;> simp_all

private theorem lt_n {n : Nat} (hn : 0 < n) {r : BitVec n} {b : Bool}
    (h : Cond.lt.onVal (Arm64.subFlags r 0).2.toVal = some b) : r.msb = b := by
  simp only [subFlags_zero hn, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit] at h
  cases hm : r.msb <;> simp_all

private theorem readsN_ge : readsN .ge := fun _ => rfl
private theorem readsN_lt : readsN .lt := fun _ => rfl

private theorem msb64 (r : BitVec 64) : r.msb = r.getLsbD 63 := BitVec.msb_eq_getLsbD_last r

private theorem msb32 (r : BitVec 64) : (r.setWidth 32).msb = r.getLsbD 31 := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_setWidth]; rfl

/-- `ARM64.rules:645`: `(GE (CMPconst [0] x) yes no) => (TBZ [63] x yes no)` -/
theorem r_ARM64_645_sound : BlockRuleL.Sound r_ARM64_645 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc, show BitVec.ofInt 64 0 = 0 from rfl] at hbr
  simp only [brVal, show BlockKind.ARM64GE.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg_of_cmp0 readsN_ge (Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr)
  rw [hr, Option.map_some, ← ge_n (by decide) h, msb64]; rfl

/-- `ARM64.rules:647`: `(LT (CMPconst [0] x) yes no) => (TBNZ [63] x yes no)` -/
theorem r_ARM64_647_sound : BlockRuleL.Sound r_ARM64_647 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc, show BitVec.ofInt 64 0 = 0 from rfl] at hbr
  simp only [brVal, show BlockKind.ARM64LT.isArm64 = true from rfl,
    show BlockKind.ARM64TBNZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg_of_cmp0 readsN_lt (Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr)
  rw [hr, Option.map_some, ← lt_n (by decide) h, msb64]; rfl

/-- `ARM64.rules:644`: `(GE (CMPWconst [0] x) yes no) => (TBZ [31] x yes no)` -/
theorem r_ARM64_644_sound : BlockRuleL.Sound r_ARM64_644 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [imm32_of_zero hc] at hbr
  simp only [brVal, show BlockKind.ARM64GE.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  rw [hr, Option.map_some, ← ge_n (by decide) h, msb32]; rfl

/-- `ARM64.rules:646`: `(LT (CMPWconst [0] x) yes no) => (TBNZ [31] x yes no)` -/
theorem r_ARM64_646_sound : BlockRuleL.Sound r_ARM64_646 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [imm32_of_zero hc] at hbr
  simp only [brVal, show BlockKind.ARM64LT.isArm64 = true from rfl,
    show BlockKind.ARM64TBNZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  rw [hr, Option.map_some, ← lt_n (by decide) h, msb32]; rfl

theorem ofFlagBit_cases (o : Option Bool) : Val.ofFlagBit o = .poison ∨ ∃ b, Val.ofFlagBit o = .bool b := by
  cases o with
  | none => exact .inl rfl
  | some b => exact .inr ⟨b, rfl⟩

/-- `InvertFlags`' result read at any shape refines it. -/
theorem retypeL_invertFlags_ref (T : Ty) (f : Val) :
    Refines ((invertFlags f).retypeL T) (invertFlags f) := by
  unfold invertFlags
  split
  · exact retypeL_agg5_ref T (ofFlagBit_cases _) (ofFlagBit_cases _) (ofFlagBit_cases _)
      (ofFlagBit_cases _) (ofFlagBit_cases _)
  · rw [retypeL_poison]; exact .poison _

set_option hygiene false in
/-- `(K (InvertFlags cmp)) => (K' cmp)`: `K` on `InvertFlags cmp` is `K'` on `cmp`
(`invertFlags_cond`). -/
local macro "arm_invflags" : tactic => `(tactic| (
  arm_bunfold; arm_norm
  simp (config := { decide := true }) only [brVal, Arm64.taken, ite_true, Bool.bne_false]
    at hbr ⊢
  exact invertFlags_cond rfl (Mono.onVal_of (retypeL_invertFlags_ref _ _) hbr)))

/-- `ARM64.rules:1332`: `(LT (InvertFlags cmp) yes no) => (GT cmp yes no)` -/
theorem r_ARM64_1332_sound : BlockRuleL.Sound r_ARM64_1332 := by arm_invflags

/-- `ARM64.rules:1333`: `(GT (InvertFlags cmp) yes no) => (LT cmp yes no)` -/
theorem r_ARM64_1333_sound : BlockRuleL.Sound r_ARM64_1333 := by arm_invflags

/-- `ARM64.rules:1334`: `(LE (InvertFlags cmp) yes no) => (GE cmp yes no)` -/
theorem r_ARM64_1334_sound : BlockRuleL.Sound r_ARM64_1334 := by arm_invflags

/-- `ARM64.rules:1335`: `(GE (InvertFlags cmp) yes no) => (LE cmp yes no)` -/
theorem r_ARM64_1335_sound : BlockRuleL.Sound r_ARM64_1335 := by arm_invflags

/-- `ARM64.rules:1336`: `(ULT (InvertFlags cmp) yes no) => (UGT cmp yes no)` -/
theorem r_ARM64_1336_sound : BlockRuleL.Sound r_ARM64_1336 := by arm_invflags

/-- `ARM64.rules:1337`: `(UGT (InvertFlags cmp) yes no) => (ULT cmp yes no)` -/
theorem r_ARM64_1337_sound : BlockRuleL.Sound r_ARM64_1337 := by arm_invflags

/-- `ARM64.rules:1338`: `(ULE (InvertFlags cmp) yes no) => (UGE cmp yes no)` -/
theorem r_ARM64_1338_sound : BlockRuleL.Sound r_ARM64_1338 := by arm_invflags

/-- `ARM64.rules:1339`: `(UGE (InvertFlags cmp) yes no) => (ULE cmp yes no)` -/
theorem r_ARM64_1339_sound : BlockRuleL.Sound r_ARM64_1339 := by arm_invflags

/-- `ARM64.rules:1340`: `(EQ (InvertFlags cmp) yes no) => (EQ cmp yes no)` -/
theorem r_ARM64_1340_sound : BlockRuleL.Sound r_ARM64_1340 := by arm_invflags

/-- `ARM64.rules:1341`: `(NE (InvertFlags cmp) yes no) => (NE cmp yes no)` -/
theorem r_ARM64_1341_sound : BlockRuleL.Sound r_ARM64_1341 := by arm_invflags

/-- `oneBit(c)` at `int64` (`ARM64.rules:621-624`'s condition): `c`'s pattern is the single bit
`ntz64(c)`. -/
theorem oneBit_twoPow {c : Int} (h1 : wrapInt 64 true (andPred GoTy.int64 c) = 0)
    (h2 : BitVec.ofInt 64 c ≠ 0) :
    trailingZeros (c.emod (2 ^ 64)).toNat 64 < 64 ∧
      BitVec.ofInt 64 c = BitVec.twoPow 64 (trailingZeros (c.emod (2 ^ 64)).toNat 64) := by
  have hC : BitVec.ofInt 64 c &&& (BitVec.ofInt 64 c - 1#64) = 0 := by
    have := congrArg (BitVec.ofInt 64) h1
    rw [ofInt_wrapInt_true (Nat.le_refl 64), andPred] at this
    simp only [bitwise, show GoTy.int64.intInfo? = some (64, true) from rfl,
      Option.getD_some] at this
    rw [ofInt_wrapInt_true (Nat.le_refl 64), BitVec.ofInt_natCast, BitVec.ofNat_and,
      ofNat_pat64 (Nat.le_refl 64), ofNat_pat64 (Nat.le_refl 64), ofInt_sub'] at this
    simpa using this
  have hN : (BitVec.ofInt 64 c).toNat = (c.emod (2 ^ 64)).toNat := by
    rw [BitVec.toNat_ofInt]; rfl
  generalize hb : BitVec.ofInt 64 c = b at hC h2 hN
  have hpos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h2
    · exact h
  have h1' : (1#64).toNat = 1 := rfl
  have hn : b.toNat &&& (b.toNat - 1) = 0 := by
    have := congrArg BitVec.toNat hC
    rw [BitVec.toNat_and, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1']; omega), h1'] at this
    simpa using this
  have hp := pow2_of_and_pred hpos hn
  have hlt := b.isLt
  have hj : bitsLen b.toNat - 1 < 64 := by
    false_or_by_contra
    rename_i hk
    have : 2 ^ 64 ≤ 2 ^ (bitsLen b.toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  generalize bitsLen b.toNat - 1 = j at hp hj
  have ht : trailingZeros (2 ^ j) 64 = j := by
    obtain ⟨hs, hodd⟩ := Divisible.trailingZeros_spec (2 ^ j) (Nat.two_pow_pos j)
      (by rw [← hp]; exact hlt)
    generalize trailingZeros (2 ^ j) 64 = t at hs hodd
    rcases Nat.lt_trichotomy t j with h | h | h
    · rw [Nat.pow_div (Nat.le_of_lt h) (by decide)] at hodd
      obtain ⟨d, hd⟩ : ∃ d, j - t = d + 1 := ⟨j - t - 1, by omega⟩
      rw [hd, Nat.pow_succ] at hodd; simp at hodd
    · exact h
    · rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide) h)] at hodd; cases hodd
  rw [← hN, hp, ht]
  refine ⟨hj, BitVec.eq_of_toNat_eq ?_⟩
  rw [BitVec.toNat_twoPow, hp, Nat.mod_eq_of_lt (hp ▸ hlt)]

/-- The bit index `ntz64(c)` as the `TBZ`/`TBNZ` auxint. -/
theorem tbAux {k : Nat} (hk : k < 64) : (Int64.ofInt (wrapInt 64 true (k : Int))).toInt.toNat = k := by
  have : wrapInt 64 true (k : Int) = k := by
    simp only [wrapInt, ite_true]
    rw [Int.bmod_eq_of_le] <;> omega
  rw [this, Int64.toInt_ofInt, Int.bmod_eq_of_le] <;> simp [Int64.size] <;> omega

/-- The `Z` flag of `TST` with a single bit: the bit is clear. -/
theorem and_twoPow_eq_zero {k : Nat} (hk : k < 64) (r : BitVec 64) :
    (r &&& BitVec.twoPow 64 k == 0) = !r.getLsbD k := by
  have h0 : BitVec.twoPow 64 k ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
    simp at this
  rw [BitVec.and_twoPow]
  split <;> simp_all

/-- A 64-bit flags result read at any shape refines it. -/
theorem retypeL_flags1_ref (T : Ty) (f : BitVec 64 → Flags) (a : Val) :
    Refines ((Arm64.flags1 f [a]).retypeL T) (Arm64.flags1 f [a]) := by
  have hb : ∀ x : Bool, Val.bool x = .poison ∨ ∃ b, Val.bool x = .bool b := fun x => .inr ⟨x, rfl⟩
  cases h : Arm64.reg a <;> simp only [Arm64.flags1, h]
  · rw [retypeL_poison]; exact .poison _
  · exact retypeL_agg5_ref T (hb _) (hb _) (hb _) (hb _) (.inl rfl)

/-- `EQ`/`NE` on the flags of `TSTconst [c] x`: `x` has a register, whose `Z` decides. -/
theorem reg_of_tst {x : Val} {c : Cond} {C : BitVec 64} {b : Bool}
    (h : c.onVal (Arm64.flags1 (fun r => logicFlags (r &&& C)) [x]) = some b) :
    ∃ r, Arm64.reg x = some r ∧ c.onVal (logicFlags (r &&& C)).toVal = some b := by
  cases hx : Arm64.reg x <;> simp only [Arm64.flags1, hx] at h
  · simp [Cond.onVal] at h
  · exact ⟨_, rfl, h⟩

private theorem ofInt_toInt64 (x : Int64) : BitVec.ofInt 64 x.toInt = x.toBitVec := by
  rw [← Int64.toInt_toBitVec, BitVec.ofInt_toInt]

private theorem ofInt_ne_zero64 {x : Int64} (h : ¬x.toInt = 0) : BitVec.ofInt 64 x.toInt ≠ 0 := by
  rw [ofInt_toInt64]; intro h0; apply h; rw [← Int64.toInt_toBitVec, h0]; rfl

/-- `oneBit(int64(uint32(c)))` (`ARM64.rules:623-624`'s condition): the low word of `c` is the
single bit `ntz64(int64(uint32(c)))`, below 32. -/
theorem oneBit_twoPow32 {c : Int64}
    (h1 : wrapInt 64 true (andPred GoTy.int64
      (wrapInt 64 true (wrapInt 32 false (wrapInt 32 true c.toInt)))) = 0)
    (h2 : ¬wrapInt 64 true (wrapInt 32 false (wrapInt 32 true c.toInt)) = 0) :
    trailingZeros ((wrapInt 64 true (wrapInt 32 false (wrapInt 32 true c.toInt))).emod
      (2 ^ 64)).toNat 64 < 32 ∧
    Arm64.imm32 c = BitVec.twoPow 32 (trailingZeros ((wrapInt 64 true (wrapInt 32 false
      (wrapInt 32 true c.toInt))).emod (2 ^ 64)).toNat 64) := by
  have hu : wrapInt 32 false (wrapInt 32 true c.toInt) = c.toInt % 2 ^ 32 := by
    simp only [wrapInt, ite_true, Bool.false_eq_true, ite_false]; exact Int.bmod_emod
  rw [hu] at h1 h2 ⊢
  have h0 : 0 ≤ c.toInt % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hl : c.toInt % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  have hw : wrapInt 64 true (c.toInt % 2 ^ 32) = c.toInt % 2 ^ 32 := by
    simp only [wrapInt, ite_true]; rw [Int.bmod_eq_of_le] <;> omega
  rw [hw] at h1 h2 ⊢
  have hn : (BitVec.ofInt 64 (c.toInt % 2 ^ 32)).toNat = (c.toInt % 2 ^ 32).toNat := by
    rw [BitVec.toNat_ofInt, Int.emod_eq_of_lt h0 (Int.lt_trans hl (by decide))]
  have hne : BitVec.ofInt 64 (c.toInt % 2 ^ 32) ≠ 0 := by
    intro h; apply h2
    have := congrArg BitVec.toNat h
    rw [hn] at this
    change _ = 0 at this
    have := Int.toNat_eq_zero.mp this
    omega
  obtain ⟨hk, hC⟩ := oneBit_twoPow h1 hne
  generalize trailingZeros ((c.toInt % 2 ^ 32).emod (2 ^ 64)).toNat 64 = k at hk hC ⊢
  have hp : (c.toInt % 2 ^ 32).toNat = 2 ^ k := by
    rw [← hn, hC, BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)]
  have hk32 : k < 32 := by
    false_or_by_contra
    rename_i hk'
    have : 2 ^ 32 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  refine ⟨hk32, BitVec.eq_of_toNat_eq ?_⟩
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk32), ← hp,
    Arm64.imm32, BitVec.toNat_ofInt]
  rfl

/-- `ARM64.rules:621`: `(EQ (TSTconst [c] x) yes no) && oneBit(c) => (TBZ [int64(ntz64(c))] x yes no)` -/
theorem r_ARM64_621_sound : BlockRuleL.Sound r_ARM64_621 := by
  arm_bunfold; arm_norm
  dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond
  simp only [sigmaL, Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper, rule_unfold_s] at hcond
  obtain ⟨hk, hC⟩ := oneBit_twoPow hcond.1 (ofInt_ne_zero64 hcond.2)
  generalize trailingZeros _ 64 = k at hk hC ⊢
  rw [hC] at hbr
  simp only [brVal, show BlockKind.ARM64EQ.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false, tbAux hk]
  obtain ⟨r, hr, h⟩ := reg_of_tst (Mono.onVal_of (retypeL_flags1_ref _ _ _) hbr)
  simp only [logicFlags, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.some.injEq,
    and_twoPow_eq_zero hk] at h
  rw [hr, Option.map_some, h]

/-- `ARM64.rules:622`: `(NE (TSTconst [c] x) yes no) && oneBit(c) => (TBNZ [int64(ntz64(c))] x yes no)` -/
theorem r_ARM64_622_sound : BlockRuleL.Sound r_ARM64_622 := by
  arm_bunfold; arm_norm
  dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond
  simp only [sigmaL, Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper, rule_unfold_s] at hcond
  obtain ⟨hk, hC⟩ := oneBit_twoPow hcond.1 (ofInt_ne_zero64 hcond.2)
  generalize trailingZeros _ 64 = k at hk hC ⊢
  rw [hC] at hbr
  simp only [brVal, show BlockKind.ARM64NE.isArm64 = true from rfl,
    show BlockKind.ARM64TBNZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false, tbAux hk]
  obtain ⟨r, hr, h⟩ := reg_of_tst (Mono.onVal_of (retypeL_flags1_ref _ _ _) hbr)
  simp only [logicFlags, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.map_some,
    Option.some.injEq, and_twoPow_eq_zero hk, Bool.not_not] at h
  rw [hr, Option.map_some, h]

/-- `EQ`/`NE` on the flags of `TSTWconst [c] x`: `x` has a register, whose low word's `Z` decides. -/
theorem reg_of_tstw {x : Val} {c : Cond} {C : BitVec 32} {b : Bool}
    (h : c.onVal (Arm64.flags1w (fun r => logicFlags (r &&& C)) [x]) = some b) :
    ∃ r, Arm64.reg x = some r ∧ c.onVal (logicFlags (r.setWidth 32 &&& C)).toVal = some b := by
  cases hx : Arm64.reg x <;> simp only [Arm64.flags1w, Arm64.reg32, hx, Option.map_none,
    Option.map_some] at h
  · simp [Cond.onVal] at h
  · exact ⟨_, rfl, h⟩

/-- The `Z` flag of `TSTW` with a single bit of the low word: the register's bit is clear. -/
theorem and_twoPow32_eq_zero {k : Nat} (hk : k < 32) (r : BitVec 64) :
    (r.setWidth 32 &&& BitVec.twoPow 32 k == 0) = !r.getLsbD k := by
  have h0 : BitVec.twoPow 32 k ≠ 0 := by
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
    simp at this
  rw [BitVec.and_twoPow, BitVec.getLsbD_setWidth]
  simp only [hk, decide_true, Bool.true_and]
  split <;> simp_all

/-- `ARM64.rules:623`: `(EQ (TSTWconst [c] x) yes no) && oneBit(int64(uint32(c))) => (TBZ [int64(ntz64(int64(uint32(c))))] x yes no)` -/
theorem r_ARM64_623_sound : BlockRuleL.Sound r_ARM64_623 := by
  arm_bunfold; arm_norm
  dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond
  simp only [sigmaL, Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper, rule_unfold_s] at hcond
  obtain ⟨hk, hC⟩ := oneBit_twoPow32 hcond.1 hcond.2
  generalize trailingZeros _ 64 = k at hk hC ⊢
  rw [hC] at hbr
  simp only [brVal, show BlockKind.ARM64EQ.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false, tbAux (by omega)]
  obtain ⟨r, hr, h⟩ := reg_of_tstw (Mono.onVal_of (retypeL_flags1w_ref _ _ _) hbr)
  simp only [logicFlags, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.some.injEq,
    and_twoPow32_eq_zero hk] at h
  rw [hr, Option.map_some, h]

/-- `ARM64.rules:624`: `(NE (TSTWconst [c] x) yes no) && oneBit(int64(uint32(c))) => (TBNZ [int64(ntz64(int64(uint32(c))))] x yes no)` -/
theorem r_ARM64_624_sound : BlockRuleL.Sound r_ARM64_624 := by
  arm_bunfold; arm_norm
  dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at hcond
  simp only [sigmaL, Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper, rule_unfold_s] at hcond
  obtain ⟨hk, hC⟩ := oneBit_twoPow32 hcond.1 hcond.2
  generalize trailingZeros _ 64 = k at hk hC ⊢
  rw [hC] at hbr
  simp only [brVal, show BlockKind.ARM64NE.isArm64 = true from rfl,
    show BlockKind.ARM64TBNZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false, tbAux (by omega)]
  obtain ⟨r, hr, h⟩ := reg_of_tstw (Mono.onVal_of (retypeL_flags1w_ref _ _ _) hbr)
  simp only [logicFlags, Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.map_some,
    Option.some.injEq, and_twoPow32_eq_zero hk, Bool.not_not] at h
  rw [hr, Option.map_some, h]

/-- Bit 0 of a register result read back at its shape is bit 0 of the result. -/
private theorem reg_retypeL_res_bit0 (T : Ty) (y : BitVec 64) {z : BitVec 64}
    (h : Arm64.reg ((Arm64.res T y).retypeL T) = some z) : z.getLsbD 0 = y.getLsbD 0 := by
  cases T with
  | int w =>
    cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Arm64.reg, Width.bits] at h <;>
      subst h <;> simp
  | bool =>
    simp only [Arm64.res, Val.retypeL, Val.widen, Val.retype, Arm64.reg] at h
    cases hb : y.getLsbD 0 <;> simp_all <;> (subst_vars; decide)
  | _ => simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Arm64.reg]

/-- A test `f` of bit 0 of `XORconst [1] x` is the test of bit 0 of `x` flipped. -/
private theorem xor1_bit0 (T : Ty) (x : Val) (f : Bool → Bool) (b : Bool)
    (h : (Arm64.reg ((Arm64.op1 T (fun y => y ^^^ BitVec.ofInt 64 1) [x]).retypeL T)).map
      (fun y => f (y.getLsbD 0)) = some b) :
    (Arm64.reg x).map (fun y => f (!y.getLsbD 0)) = some b := by
  cases hx : Arm64.reg x with
  | none =>
    rw [show Arm64.op1 T (fun y => y ^^^ BitVec.ofInt 64 1) [x] = .poison by simp only [Arm64.op1, hx],
      retypeL_poison] at h
    simp only [show Arm64.reg .poison = none from rfl, Option.map_none] at h
    cases h
  | some r =>
    simp only [Arm64.op1, hx] at h
    cases hz : Arm64.reg ((Arm64.res T (r ^^^ BitVec.ofInt 64 1)).retypeL T) with
    | none => rw [hz] at h; cases h
    | some z =>
      rw [hz, Option.map_some, Option.some.injEq] at h
      have hz0 := reg_retypeL_res_bit0 T _ hz
      rw [BitVec.getLsbD_xor, show (BitVec.ofInt 64 1).getLsbD 0 = true by decide,
        Bool.xor_true] at hz0
      rw [Option.map_some, ← h, hz0]

/-- `ARM64.rules:556`: `(TB(Z|NZ) [0] (XORconst [1] x) yes no) => (TB(NZ|Z) [0] x yes no)` -/
theorem r_ARM64_556_sound : BlockRuleL.Sound r_ARM64_556 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc] at hbr
  simp only [brVal, show BlockKind.ARM64TBNZ.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken, hb,
    show (Int64.ofInt 0).toInt.toNat = 0 from rfl, Int.toNat_zero, Bool.bne_false] at hbr ⊢
  exact xor1_bit0 _ _ id b hbr

/-- `ARM64.rules:556`: `(TB(Z|NZ) [0] (XORconst [1] x) yes no) => (TB(NZ|Z) [0] x yes no)` -/
theorem r_ARM64_556_2_sound : BlockRuleL.Sound r_ARM64_556_2 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc] at hbr
  simp only [brVal, show BlockKind.ARM64TBNZ.isArm64 = true from rfl,
    show BlockKind.ARM64TBZ.isArm64 = true from rfl, ite_true, Arm64.taken, hb,
    show (Int64.ofInt 0).toInt.toNat = 0 from rfl, Int.toNat_zero, Bool.bne_false] at hbr ⊢
  have := xor1_bit0 _ _ (!·) b hbr
  simpa only [Bool.not_not] using this

end GoFV.Proof.Low.Rules
