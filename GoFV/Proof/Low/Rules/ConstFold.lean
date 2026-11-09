import GoFV.Proof.Low.Rules.Peep

/-!
# Lowering rule lemmas: extensions and masks of constants and masks, constant folds (`ARM64.rules:1211-1216`, `1241-1260`)

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
* `(ADDconst [c] (ADDconst [d] x)) => (ADDconst [c+d] x)` and the `ADDconst`/`SUBconst` mixes
  (1212, 1213, 1215, 1216): a pointer `x` is held as one at a word shape, so both results are
  word-shaped (`Pat.argsOKLs`); it moves by `d` inside its block (`Ptr.held_of_blk`), then by
  `c`, which is the move by `c+d`, or the first move leaves its window and the source is
  `poison`; any other `x` adds as a register (`refines_addP_addP`). `(ADDconst [c] (MOVDconst
  [d])) => (MOVDconst [c+d])` and `(SUBconst [c] (MOVDconst [d])) => (MOVDconst [d-c])` (1211,
  1214) add to the constant's register (`refines_addP_const`).
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

private theorem cf_addP_nonptr (T : Ty) {x : Val} (hx : ∀ p, x ≠ .ptr p) (k : BitVec 64) :
    Arm64.addP T x k = Arm64.op1 T (fun a => a + k) [x] := by
  unfold Arm64.addP; split
  · simp_all
  · rfl

private theorem cf_add_low (n : Nat) (a a' b : BitVec 64) (h : a.setWidth n = a'.setWidth n) :
    (a + b).setWidth n = (a' + b).setWidth n := by
  by_cases hn : n ≤ 64
  · rw [BitVec.setWidth_add _ _ hn, BitVec.setWidth_add _ _ hn, h]
  · have ha : a = a' := by
      have := congrArg (BitVec.setWidth 64) h
      rwa [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_eq, BitVec.setWidth_eq] at this
    rw [ha]

/-- A register result (or `poison`) read back at its shape is not a pointer. -/
private theorem cf_op1_not_ptr (T : Ty) (f : BitVec 64 → BitVec 64) (x : Val) (q : Ptr) :
    (Arm64.op1 T f [x]).retypeL T ≠ .ptr q := by
  cases hx : Arm64.reg x with
  | none => simp [Arm64.op1, hx, retypeL_poison]
  | some r =>
    simp only [Arm64.op1, hx]
    cases T with
    | int w => cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
    | _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype]

private theorem cf_res_not_ptr (T : Ty) (k : BitVec 64) (q : Ptr) :
    (Arm64.res T k).retypeL T ≠ .ptr q := by
  cases T with
  | int w => cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
  | _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype]

/-- A pointer held as one, read at a word shape, is itself. -/
private theorem cf_retypeL_held {T : Ty} (hT : wordShape T = true) {q : Ptr} (hq : q.held = true) :
    (Val.ptr q).retypeL T = .ptr q := by
  cases T with
  | int w => cases w <;> simp_all [wordShape, Val.retypeL, Val.widen, Val.retype, Ptr.word_of_held hq]
  | ptr e => simp [Val.retypeL, Val.widen, Val.retype, Ptr.word_of_held hq]
  | _ => simp [wordShape] at hT

private theorem cf_wordShape_of_ptr {T : Ty} {p : Ptr} (h : (Val.ptr p).hasTy T = true) :
    wordShape T = true := by
  cases T with
  | int w => cases w <;> simp_all [Val.hasTy, wordShape]
  | _ => simp_all [Val.hasTy, wordShape]

/-- `ADDconst [b]` of `ADDconst [a] x` as `ADDconst [a+b] x`: a pointer `x` (held as one, at a
word shape, so both results are word-shaped by the provenance clauses `hs0`, `hs`) moves by `a`
inside its block, then by `b`, or the first move leaves its window and the result is `poison`; any
other `x` adds as a register, and the low bits of the sum are the low bits of the sums. -/
theorem refines_addP_addP {T T0 T1 : Ty} (hw : lowW T ≤ argWidth T0)
    (hs0 : (!wordShape T1) = true ∨ wordShape T0 = true)
    (hs : (!wordShape T0) = true ∨ wordShape T = true) {x : Val} (hx : x.hasTy T1 = true)
    (a b : BitVec 64) :
    Refines ((Arm64.addP T ((Arm64.addP T0 x a).retypeL T0) b).retypeL T)
      ((Arm64.addP T x (a + b)).retypeL T) := by
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    have hph := Ptr.held_of_hasTy hx
    have hT1 := cf_wordShape_of_ptr hx
    have hT0 : wordShape T0 = true := by simpa [hT1] using hs0
    show Refines ((Arm64.addP T ((PtrOps.ptrRes (p.add a)).retypeL T0) b).retypeL T)
      ((PtrOps.ptrRes (p.add (a + b))).retypeL T)
    unfold PtrOps.ptrRes
    by_cases hwin : (p.add a).inWindow = true
    · have hq : (p.add a).held = true := Ptr.held_of_blk (p := p) (q := p.add a) rfl hph hwin
      rw [if_pos hwin, Ptr.word_of_held hq, cf_retypeL_held hT0 hq]
      have he : (p.add a).add b = p.add (a + b) := by simp [Ptr.add, BitVec.add_assoc]
      show Refines ((PtrOps.ptrRes ((p.add a).add b)).retypeL T) _
      rw [he]; exact Refines.refl _
    · rw [if_neg hwin, retypeL_poison]
      show Refines (Val.retypeL T .poison) _
      rw [retypeL_poison]; exact .poison _
  · have hp' : ∀ p, x ≠ .ptr p := fun p h => hp ⟨p, h⟩
    rw [cf_addP_nonptr T0 hp', cf_addP_nonptr T (cf_op1_not_ptr T0 _ x), cf_addP_nonptr T hp']
    exact refines_op1_inner (lowW_pos _).1 (lowW_pos _).2 hw _ _ _
      (fun u v h => cf_add_low _ u v b h) (fun y => BitVec.add_assoc y a b) x

/-- `ADDconst [b]` of a constant register: the constant plus `b`, as far as the low bits go. -/
theorem refines_addP_const {T T0 : Ty} (hw : lowW T ≤ argWidth T0) (r b : BitVec 64) :
    Refines ((Arm64.addP T ((Arm64.res T0 r).retypeL T0) b).retypeL T)
      ((Arm64.res T (r + b)).retypeL T) := by
  rcases retypeL_res_reg (lowW_pos T).1 (lowW_pos T).2 hw r with h | ⟨y, hy, hyr⟩
  · rw [h]
    show Refines (Val.retypeL T .poison) _
    rw [retypeL_poison]; exact .poison _
  · rw [cf_addP_nonptr T (cf_res_not_ptr T0 r)]
    simp only [Arm64.op1, hy]
    rw [retypeL_res_low T (cf_add_low _ y r b hyr)]
    exact Refines.refl _

private theorem armReadW_addc (T : Ty) : armReadW .ARM64ADDconst T 0 = lowW T := by cases T <;> rfl
private theorem armReadW_subc (T : Ty) : armReadW .ARM64SUBconst T 0 = lowW T := by cases T <;> rfl

/-- `ARM64.rules:1211`: `(ADDconst [c] (MOVDconst [d])) => (MOVDconst [c+d])` -/
theorem r_ARM64_1211_sound : ArmRule.Checked r_ARM64_1211 := by
  left; arm_unfold; arm_norm
  rw [BitVec.ofInt_add, BitVec.add_comm]
  exact refines_addP_const (armReadW_addc _ ▸ harg.1) _ _

/-- `ARM64.rules:1212`: `(ADDconst [c] (ADDconst [d] x)) => (ADDconst [c+d] x)` -/
theorem r_ARM64_1212_sound : ArmRule.Checked r_ARM64_1212 := by
  left; arm_unfold; arm_norm
  rw [BitVec.ofInt_add, BitVec.add_comm]
  exact refines_addP_addP (armReadW_addc _ ▸ harg.1.1) harg.2.2 harg.1.2 hty _ _

/-- `ARM64.rules:1213`: `(ADDconst [c] (SUBconst [d] x)) => (ADDconst [c-d] x)` -/
theorem r_ARM64_1213_sound : ArmRule.Checked r_ARM64_1213 := by
  left; arm_unfold; arm_norm
  rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
  exact refines_addP_addP (armReadW_addc _ ▸ harg.1.1) harg.2.2 harg.1.2 hty _ _

/-- `ARM64.rules:1214`: `(SUBconst [c] (MOVDconst [d])) => (MOVDconst [d-c])` -/
theorem r_ARM64_1214_sound : ArmRule.Checked r_ARM64_1214 := by
  left; arm_unfold; arm_norm
  rw [BitVec.sub_eq_add_neg]
  exact refines_addP_const (armReadW_subc _ ▸ harg.1) _ _

/-- `ARM64.rules:1215`: `(SUBconst [c] (SUBconst [d] x)) => (ADDconst [-c-d] x)` -/
theorem r_ARM64_1215_sound : ArmRule.Checked r_ARM64_1215 := by
  left; arm_unfold; arm_norm
  rw [BitVec.ofInt_neg, BitVec.sub_eq_add_neg, BitVec.add_comm]
  exact refines_addP_addP (armReadW_subc _ ▸ harg.1.1) harg.2.2 harg.1.2 hty _ _

/-- `ARM64.rules:1216`: `(SUBconst [c] (ADDconst [d] x)) => (ADDconst [-c+d] x)` -/
theorem r_ARM64_1216_sound : ArmRule.Checked r_ARM64_1216 := by
  left; arm_unfold; arm_norm
  rw [show BitVec.ofInt 64 (wrapInt 64 true (-(e.auxInt []).toInt) + (e.auxInt [0]).toInt) =
      BitVec.ofInt 64 (e.auxInt [0]).toInt + -BitVec.ofInt 64 (e.auxInt []).toInt by
    rw [BitVec.ofInt_add, ofInt_wrapInt_true (Nat.le_refl 64), BitVec.ofInt_neg, BitVec.add_comm]]
  exact refines_addP_addP (armReadW_subc _ ▸ harg.1.1) harg.2.2 harg.1.2 hty _ _

end GoFV.Proof.Low.Rules
