import GoFV.Proof.Low.Rules.Peep

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: extensions and masks of constants and masks (`ARM64.rules:1241-1260`)

Peepholes of lowered code (#385):

* `(MOV{B,H,W}{,U}reg (MOVDconst [c])) => (MOVDconst [int64({u,}int{8,16,32}(c))])` and
  `(MOVDreg (MOVDconst [c])) => (MOVDconst [c])`: the extension reads the low bits of the
  constant's register, which every shape holding them keeps (`retypeL_res_reg`), and extends
  them as the folded constant does (`refines_ext_const`; `MOVDreg` is `poison` in the semantics).
* `(ANDconst [c] (MOV{W,H,B}Ureg x)) => (ANDconst [c&(1<<n-1)] x)`, `(MOV{W,H,B}Ureg (ANDconst [c]
  x)) => (ANDconst [c&(1<<n-1)] x)`, `(ANDconst [c] (ANDconst [d] x)) => (ANDconst [c&d] x)` and
  `(XORconst [c] (XORconst [d] x)) => (XORconst [c^d] x)`: the outer op reads the low bits of the
  inner result at its shape, which agree with the inner op's register on them (`retypeL_res_reg`),
  and depend only on them (`refines_op1_inner`); composed, the two ops are the folded one.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- The bits a bitwise op with an immediate reads: those `retypeL` keeps at its shape. -/
theorem armReadW_lowC (o : Op) (T : Ty) (i : Nat)
    (ho : o = .ARM64ANDconst ∨ o = .ARM64ORconst ∨ o = .ARM64XORconst) :
    armReadW o T i = lowW T := by
  rcases ho with rfl | rfl | rfl <;> cases T <;> rfl

/-- An extension reads the low `n` bits of its register only. -/
theorem ext_low (s : Bool) {n : Nat} (hn : n ≤ 64) (y : BitVec 64) :
    Arm64.ext s n y = Arm64.ext s n ((y.setWidth n).setWidth 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases s
  · simp only [Arm64.ext, Arm64.mask, Bool.false_eq_true, ite_false, BitVec.getLsbD_and,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    by_cases hin : i < n <;> simp [hin, hi]
  · by_cases h0 : n = 0
    · subst h0; simp [Arm64.ext, Arm64.sext]
    simp only [Arm64.ext, Arm64.sext, Arm64.mask, ite_true, h0, ite_false,
      BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
      BitVec.msb_shiftLeft, BitVec.getMsbD]
    by_cases h1 : 64 - n + i < 64 <;> simp [h1, hi]
    all_goals (cases decide (i < n) <;> cases decide (63 - (64 - n) < n) <;>
      cases decide (63 - (64 - n) < 64) <;> simp)

/-- An extension of a constant register read at a shape holding the extended bits: `poison`, or
the extension of the constant, the folded constant. -/
theorem refines_ext_const (s : Bool) {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 64) {T T0 : Ty}
    (h : n ≤ argWidth T0) (c : Int) :
    Refines ((Arm64.op1 T (Arm64.ext s n) [(Arm64.res T0 (BitVec.ofInt 64 c)).retypeL T0]).retypeL T)
      ((Arm64.res T (BitVec.ofInt 64 (wrapInt n s c))).retypeL T) := by
  rcases retypeL_res_reg h1 hn h (BitVec.ofInt 64 c) with hp | ⟨y, hy, hyk⟩
  · rw [hp]; simp only [Arm64.op1, show Arm64.reg .poison = none from rfl, retypeL_poison]
    exact .poison _
  · simp only [Arm64.op1, hy]
    rw [ext_low s hn, hyk, setWidth_ofInt_of_ge hn]
    cases s
    · rw [ext_false_setWidth n _ hn, setWidth_ofInt_of_le hn]; exact Refines.refl _
    · rw [ext_true_setWidth n _ (by omega) hn, signExtend_ofInt hn]; exact Refines.refl _

/-- **An op of an op's result** read at a shape holding the `n` low bits the outer op `g` reads:
`poison`, or the composed op `h` (`g ∘ f` on those bits). -/
theorem refines_op1_inner {n : Nat} (h1 : 1 ≤ n) (hn : n ≤ 64) {T T0 : Ty} (h : n ≤ argWidth T0)
    (f g k : BitVec 64 → BitVec 64)
    (hg : ∀ a b : BitVec 64, a.setWidth n = b.setWidth n →
      (g a).setWidth (lowW T) = (g b).setWidth (lowW T))
    (hk : ∀ x, g (f x) = k x) (x : Val) :
    Refines ((Arm64.op1 T g [(Arm64.op1 T0 f [x]).retypeL T0]).retypeL T)
      ((Arm64.op1 T k [x]).retypeL T) := by
  cases hx : Arm64.reg x with
  | none =>
    simp only [Arm64.op1, hx, retypeL_poison, show Arm64.reg .poison = none from rfl]
    exact .poison _
  | some x' =>
    simp only [Arm64.op1, hx]
    rcases retypeL_res_reg h1 hn h (f x') with hp | ⟨y, hy, hyk⟩
    · rw [hp]; simp only [show Arm64.reg .poison = none from rfl, retypeL_poison]
      exact .poison _
    · simp only [hy]
      rw [retypeL_res_low T (hg _ _ hyk), hk]; exact Refines.refl _

/-- `ARM64.rules:1254`: `(MOVBreg (MOVDconst [c])) => (MOVDconst [int64(int8(c))])` -/
theorem r_ARM64_1254_sound : ArmRule.Checked r_ARM64_1254 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const true (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1255`: `(MOVBUreg (MOVDconst [c])) => (MOVDconst [int64(uint8(c))])` -/
theorem r_ARM64_1255_sound : ArmRule.Checked r_ARM64_1255 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const false (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1256`: `(MOVHreg (MOVDconst [c])) => (MOVDconst [int64(int16(c))])` -/
theorem r_ARM64_1256_sound : ArmRule.Checked r_ARM64_1256 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const true (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1257`: `(MOVHUreg (MOVDconst [c])) => (MOVDconst [int64(uint16(c))])` -/
theorem r_ARM64_1257_sound : ArmRule.Checked r_ARM64_1257 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const false (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1258`: `(MOVWreg (MOVDconst [c])) => (MOVDconst [int64(int32(c))])` -/
theorem r_ARM64_1258_sound : ArmRule.Checked r_ARM64_1258 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const true (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1259`: `(MOVWUreg (MOVDconst [c])) => (MOVDconst [int64(uint32(c))])` -/
theorem r_ARM64_1259_sound : ArmRule.Checked r_ARM64_1259 := by
  left; arm_unfold; arm_norm
  exact refines_ext_const false (by decide) (by decide) (by simpa only [armReadW] using harg) _

/-- `ARM64.rules:1260`: `(MOVDreg (MOVDconst [c])) => (MOVDconst [c])` (`MOVDreg` is `poison`) -/
theorem r_ARM64_1260_sound : ArmRule.Checked r_ARM64_1260 := by
  left; arm_unfold; arm_norm
  rw [retypeL_poison]; exact .poison _

/-- The masks of the rules' `c&(1<<n-1)`. -/
private theorem mask_ofInt (n : Nat) (hn : n ≤ 64 := by decide) :
    Arm64.mask n = BitVec.ofInt 64 (2 ^ n - 1 : Nat) := by
  simp only [Arm64.mask, BitVec.ofInt_natCast]

/-- The constant arithmetic of a folded constant, pushed into `BitVec` (`rule_arith`). -/
macro "cf_norm" : tactic => `(tactic| (
  simp (disch := decide) only [show (GoTy.int64.intInfo?.getD (64, true)) = (64, true) from rfl,
    rule_arith, Arm64.ext, Bool.false_eq_true, ite_false]))

private theorem and_mask (x c : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    x &&& Arm64.mask n &&& c = x &&& (c &&& BitVec.ofInt 64 (2 ^ n - 1 : Nat)) := by
  rw [BitVec.and_assoc, BitVec.and_comm (Arm64.mask n), mask_ofInt n hn]

private theorem mask_and (x c : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    x &&& c &&& Arm64.mask n = x &&& (c &&& BitVec.ofInt 64 (2 ^ n - 1 : Nat)) := by
  rw [BitVec.and_assoc, mask_ofInt n hn]

private theorem ext_false_low {n : Nat} (hn : n ≤ 64) {T : Ty} (a b : BitVec 64)
    (h : a.setWidth n = b.setWidth n) :
    (Arm64.ext false n a).setWidth (lowW T) = (Arm64.ext false n b).setWidth (lowW T) := by
  rw [ext_low false hn a, ext_low false hn b, h]

/-- `ARM64.rules:1242`: `(ANDconst [c] (MOVWUreg x)) => (ANDconst [c&(1<<32-1)] x)` -/
theorem r_ARM64_1242_sound : ArmRule.Checked r_ARM64_1242 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64ANDconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_and, h]) ?_ _
  intro x; cf_norm
  exact and_mask x _ 32 (by decide)

/-- `ARM64.rules:1243`: `(ANDconst [c] (MOVHUreg x)) => (ANDconst [c&(1<<16-1)] x)` -/
theorem r_ARM64_1243_sound : ArmRule.Checked r_ARM64_1243 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64ANDconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_and, h]) ?_ _
  intro x; cf_norm
  exact and_mask x _ 16 (by decide)

/-- `ARM64.rules:1244`: `(ANDconst [c] (MOVBUreg x)) => (ANDconst [c&(1<<8-1)] x)` -/
theorem r_ARM64_1244_sound : ArmRule.Checked r_ARM64_1244 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64ANDconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_and, h]) ?_ _
  intro x; cf_norm
  exact and_mask x _ 8 (by decide)

/-- `ARM64.rules:1245`: `(MOVWUreg (ANDconst [c] x)) => (ANDconst [c&(1<<32-1)] x)` -/
theorem r_ARM64_1245_sound : ArmRule.Checked r_ARM64_1245 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (n := 32) (by decide) (by decide)
    (by simpa only [armReadW] using harg.1) _ _ _ (ext_false_low (by decide)) ?_ _
  intro x; cf_norm
  exact mask_and x _ 32 (by decide)

/-- `ARM64.rules:1246`: `(MOVHUreg (ANDconst [c] x)) => (ANDconst [c&(1<<16-1)] x)` -/
theorem r_ARM64_1246_sound : ArmRule.Checked r_ARM64_1246 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (n := 16) (by decide) (by decide)
    (by simpa only [armReadW] using harg.1) _ _ _ (ext_false_low (by decide)) ?_ _
  intro x; cf_norm
  exact mask_and x _ 16 (by decide)

/-- `ARM64.rules:1247`: `(MOVBUreg (ANDconst [c] x)) => (ANDconst [c&(1<<8-1)] x)` -/
theorem r_ARM64_1247_sound : ArmRule.Checked r_ARM64_1247 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (n := 8) (by decide) (by decide)
    (by simpa only [armReadW] using harg.1) _ _ _ (ext_false_low (by decide)) ?_ _
  intro x; cf_norm
  exact mask_and x _ 8 (by decide)

/-- `ARM64.rules:1241`: `(ANDconst [c] (ANDconst [d] x)) => (ANDconst [c&d] x)` -/
theorem r_ARM64_1241_sound : ArmRule.Checked r_ARM64_1241 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64ANDconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_and, h]) ?_ _
  intro x; cf_norm
  ac_rfl

/-- `ARM64.rules:1251`: `(XORconst [c] (XORconst [d] x)) => (XORconst [c^d] x)` -/
theorem r_ARM64_1251_sound : ArmRule.Checked r_ARM64_1251 := by
  left; arm_unfold; arm_norm
  refine refines_op1_inner (lowW_pos _).1 (lowW_pos _).2
    (armReadW_lowC .ARM64XORconst _ 0 (by simp) ▸ harg.1) _ _ _
    (fun a b h => by simp only [BitVec.setWidth_xor, h]) ?_ _
  intro x; cf_norm
  ac_rfl

end GoFV.Proof.Low.Rules
