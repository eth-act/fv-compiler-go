import GoFV.Proof.Low.Rules.Flags
import GoFV.Proof.Low.Rules.Tactic
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: integer comparisons (`ARM64.rules:239-293`, `451-452`)

`(Eq64 x y) => (Equal (CMP x y))` and the `Neq`/`Less`/`Leq` (signed and unsigned) forms of all
widths: 32- and 64-bit operands compare by `CMPW`/`CMP` directly, 8- and 16-bit ones after a
`ZeroExt`/`SignExt` to 32 bits, which keeps `==`, `<ᵤ`, `≤ᵤ` (`zext_*`) and `<ₛ`, `≤ₛ`
(`sext_*`). The flags of `SUBS` read by the condition are Phase 1's comparison
(`Flags.cond_sub`), and `CSET` at the boolean shape is the condition (`refines_cset_bool`).
`IsInBounds`/`IsSliceInBounds` are `LessThanU`/`LessEqualU` of `CMP` on an index of any width
(`refines_inBounds`).

False under the semantics, so not proven: `EqPtr`/`NeqPtr` (243, 251; `x` the 64-bit address of
the frame variable `local 0 1`, `y` the pointer `temp 0 1 + 0`: `EqPtr` is `false`, `CMP` sees
equal addresses) and `IsNonNil` (450; a non-convertible pointer `heap 0 + (2^64 - 2^40)` has
address 0: non-nil, while `CMPconst [0]` sets `Z`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

theorem asInt_cases (w : Width) (v : Val) : v.asInt w = none ∨ ∃ x, v = .int w x := by
  cases v with
  | int w' y =>
    by_cases hw : w' = w
    · subst hw; exact .inr ⟨y, rfl⟩
    · exact .inl (by simp [Val.asInt, hw])
  | _ => exact .inl rfl

@[simp] theorem retypeL_flags_toVal (f : Flags) : f.toVal.retypeL Ty.flags = f.toVal := rfl

theorem cmp_int (w w' : Width) (x : BitVec w.bits) (y : BitVec w'.bits) :
    Arm64.cmp (.int w x) (.int w' y) = (Arm64.subFlags (x.setWidth 64) (y.setWidth 64)).2.toVal :=
  rfl

theorem flags2w_int (f : BitVec 32 → BitVec 32 → Flags) (w w' : Width) (x : BitVec w.bits)
    (y : BitVec w'.bits) :
    Arm64.flags2w f [.int w x, .int w' y] = (f (x.setWidth 32) (y.setWidth 32)).toVal := by
  simp only [Arm64.flags2w, Arm64.reg32, Arm64.reg, Option.map_some,
    BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide)]

@[simp] theorem setWidth_w64 (x : BitVec Width.w64.bits) : x.setWidth 64 = x := BitVec.setWidth_eq x
@[simp] theorem setWidth_w32 (x : BitVec Width.w32.bits) : x.setWidth 32 = x := BitVec.setWidth_eq x

theorem zext_beq {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.setWidth m == y.setWidth m) = (x == y) := by
  have hx := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  have hy := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h)
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, ← BitVec.toNat_inj, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt hy]

theorem zext_bne {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.setWidth m != y.setWidth m) = (x != y) := by
  simp only [bne, zext_beq x y h]

theorem zext_ult {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.setWidth m).ult (y.setWidth m) = x.ult y := by
  have hx := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  have hy := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h)
  simp only [BitVec.ult, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem zext_ule {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.setWidth m).ule (y.setWidth m) = x.ule y := by
  have hx := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)
  have hy := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by decide) h)
  simp only [BitVec.ule, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem sext_slt {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.signExtend m).slt (y.signExtend m) = x.slt y := by
  simp only [BitVec.slt, BitVec.toInt_signExtend_of_le h]

theorem sext_sle {n m : Nat} (x y : BitVec n) (h : n ≤ m) :
    (x.signExtend m).sle (y.signExtend m) = x.sle y := by
  simp only [BitVec.sle, BitVec.toInt_signExtend_of_le h]

/-- `CSET` of a condition at the boolean shape: the condition. -/
theorem refines_cset_bool {op : Op} {c : Cond} (hop : Cond.ofOp op = some c) {fv : Val}
    {b : Bool} (h : c.onVal fv = some b) :
    Refines ((Val.bool b).retypeL .bool) ((Arm64.cset .bool op [fv]).retypeL .bool) := by
  simp only [Arm64.cset, hop, Option.bind_some, h]
  cases b <;> exact Refines.refl _

/-- `IsInBounds`/`IsSliceInBounds` (`slice`) as `LessThanU`/`LessEqualU` of `CMP`: an index of
any width against a length of its width compares as their zero-extended registers. -/
theorem refines_inBounds (slice : Bool) {op : Op} {c : Cond} (hop : Cond.ofOp op = some c)
    (hc : ∀ x y : BitVec 64, c.onVal (Arm64.subFlags x y).2.toVal =
      some (if slice then x.ule y else x.ult y)) (a b : Val) :
    Refines ((Cmp.inBounds slice [a, b]).retypeL .bool)
      ((Arm64.cset .bool op [(Arm64.cmp a b).retypeL Ty.flags]).retypeL .bool) := by
  cases a with
  | int w i =>
    rcases asInt_cases w b with hb | ⟨n, rfl⟩
    · simp only [Cmp.inBounds, hb, retypeL_poison]; exact .poison _
    · simp only [Cmp.inBounds, Val.asInt_int]
      split
      · rw [retypeL_poison]; exact .poison _
      · rw [cmp_int, retypeL_flags_toVal]
        refine refines_cset_bool hop ?_
        have hw : w.bits ≤ 64 := by cases w <;> decide
        rw [hc]
        cases slice <;> simp only [ite_true, ite_false, Bool.false_eq_true, zext_ult _ _ hw,
          zext_ule _ _ hw]
  | _ => simp only [Cmp.inBounds, retypeL_poison]; exact .poison _

set_option hygiene false in
/-- Case split on two integer leaves of width `w`: `poison` unless both are `w`-bit integers. -/
macro "arm_leaves " w:term : tactic => `(tactic| (
  rcases asInt_cases $w (e.leaf [0]) with h0 | ⟨x, h0⟩ <;>
    rcases asInt_cases $w (e.leaf [1]) with h1 | ⟨y, h1⟩ <;>
    simp only [h0, h1, Val.asInt_int, Option.elim, retypeL_poison, retypeL_int_self] <;>
    try exact .poison _))

/-- Close `CSET [cc] (CMP/CMPW …)` against Phase 1's comparison of the leaves. -/
macro "arm_cmp" : tactic => `(tactic| (
  simp only [cmp_int, flags2w_int, retypeL_flags_toVal, setWidth_w64, setWidth_w32]
  refine refines_cset_bool rfl ?_
  first
    | rw [(cond_sub _ _ (sub_lt64 _ _)).1] | rw [(cond_sub _ _ (sub_lt64 _ _)).2.1]
    | rw [(cond_sub _ _ (sub_lt64 _ _)).2.2.1] | rw [(cond_sub _ _ (sub_lt64 _ _)).2.2.2.1]
    | rw [(cond_sub _ _ (sub_lt64 _ _)).2.2.2.2.1] | rw [(cond_sub _ _ (sub_lt64 _ _)).2.2.2.2.2]
    | rw [(cond_sub _ _ (sub_lt32 _ _)).1] | rw [(cond_sub _ _ (sub_lt32 _ _)).2.1]
    | rw [(cond_sub _ _ (sub_lt32 _ _)).2.2.1] | rw [(cond_sub _ _ (sub_lt32 _ _)).2.2.2.1]
    | rw [(cond_sub _ _ (sub_lt32 _ _)).2.2.2.2.1] | rw [(cond_sub _ _ (sub_lt32 _ _)).2.2.2.2.2]
  try simp (disch := decide) only [zext_beq, zext_bne, zext_ult, zext_ule, sext_slt, sext_sle]))

/-- `ARM64.rules:239`: `(Eq8 x y) => (Equal (CMPW (ZeroExt8to32 x) (ZeroExt8to32 y)))` -/
theorem r_ARM64_239_sound : ArmRule.Checked r_ARM64_239 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:240`: `(Eq16 x y) => (Equal (CMPW (ZeroExt16to32 x) (ZeroExt16to32 y)))` -/
theorem r_ARM64_240_sound : ArmRule.Checked r_ARM64_240 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:241`: `(Eq32 x y) => (Equal (CMPW x y))` -/
theorem r_ARM64_241_sound : ArmRule.Checked r_ARM64_241 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:242`: `(Eq64 x y) => (Equal (CMP x y))` -/
theorem r_ARM64_242_sound : ArmRule.Checked r_ARM64_242 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:247`: `(Neq8 x y) => (NotEqual (CMPW (ZeroExt8to32 x) (ZeroExt8to32 y)))` -/
theorem r_ARM64_247_sound : ArmRule.Checked r_ARM64_247 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:248`: `(Neq16 x y) => (NotEqual (CMPW (ZeroExt16to32 x) (ZeroExt16to32 y)))` -/
theorem r_ARM64_248_sound : ArmRule.Checked r_ARM64_248 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:249`: `(Neq32 x y) => (NotEqual (CMPW x y))` -/
theorem r_ARM64_249_sound : ArmRule.Checked r_ARM64_249 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:250`: `(Neq64 x y) => (NotEqual (CMP x y))` -/
theorem r_ARM64_250_sound : ArmRule.Checked r_ARM64_250 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:254`: `(Less8 x y) => (LessThan (CMPW (SignExt8to32 x) (SignExt8to32 y)))` -/
theorem r_ARM64_254_2_sound : ArmRule.Checked r_ARM64_254_2 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:254`: `(Less16 x y) => (LessThan (CMPW (SignExt16to32 x) (SignExt16to32 y)))` -/
theorem r_ARM64_254_sound : ArmRule.Checked r_ARM64_254 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:255`: `(Less32 x y) => (LessThan (CMPW x y))` -/
theorem r_ARM64_255_sound : ArmRule.Checked r_ARM64_255 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:256`: `(Less64 x y) => (LessThan (CMP x y))` -/
theorem r_ARM64_256_sound : ArmRule.Checked r_ARM64_256 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:276`: `(Less8U x y) => (LessThanU (CMPW (ZeroExt8to32 x) (ZeroExt8to32 y)))` -/
theorem r_ARM64_276_sound : ArmRule.Checked r_ARM64_276 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:277`: `(Less16U x y) => (LessThanU (CMPW (ZeroExt16to32 x) (ZeroExt16to32 y)))` -/
theorem r_ARM64_277_sound : ArmRule.Checked r_ARM64_277 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:278`: `(Less32U x y) => (LessThanU (CMPW x y))` -/
theorem r_ARM64_278_sound : ArmRule.Checked r_ARM64_278 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:279`: `(Less64U x y) => (LessThanU (CMP x y))` -/
theorem r_ARM64_279_sound : ArmRule.Checked r_ARM64_279 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:281`: `(Leq8 x y) => (LessEqual (CMPW (SignExt8to32 x) (SignExt8to32 y)))` -/
theorem r_ARM64_281_sound : ArmRule.Checked r_ARM64_281 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:282`: `(Leq16 x y) => (LessEqual (CMPW (SignExt16to32 x) (SignExt16to32 y)))` -/
theorem r_ARM64_282_sound : ArmRule.Checked r_ARM64_282 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:283`: `(Leq32 x y) => (LessEqual (CMPW x y))` -/
theorem r_ARM64_283_sound : ArmRule.Checked r_ARM64_283 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:284`: `(Leq64 x y) => (LessEqual (CMP x y))` -/
theorem r_ARM64_284_sound : ArmRule.Checked r_ARM64_284 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:290`: `(Leq8U x y) => (LessEqualU (CMPW (ZeroExt8to32 x) (ZeroExt8to32 y)))` -/
theorem r_ARM64_290_sound : ArmRule.Checked r_ARM64_290 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w8
  all_goals arm_cmp

/-- `ARM64.rules:291`: `(Leq16U x y) => (LessEqualU (CMPW (ZeroExt16to32 x) (ZeroExt16to32 y)))` -/
theorem r_ARM64_291_sound : ArmRule.Checked r_ARM64_291 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w16
  all_goals arm_cmp

/-- `ARM64.rules:292`: `(Leq32U x y) => (LessEqualU (CMPW x y))` -/
theorem r_ARM64_292_sound : ArmRule.Checked r_ARM64_292 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w32
  all_goals arm_cmp

/-- `ARM64.rules:293`: `(Leq64U x y) => (LessEqualU (CMP x y))` -/
theorem r_ARM64_293_sound : ArmRule.Checked r_ARM64_293 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  all_goals arm_leaves .w64
  all_goals arm_cmp

/-- `ARM64.rules:451`: `(IsInBounds idx len) => (LessThanU (CMP idx len))` -/
theorem r_ARM64_451_sound : ArmRule.Checked r_ARM64_451 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_inBounds false rfl (fun x y => (cond_sub x y (sub_lt64 x y)).2.2.2.2.1) _ _

/-- `ARM64.rules:452`: `(IsSliceInBounds idx len) => (LessEqualU (CMP idx len))` -/
theorem r_ARM64_452_sound : ArmRule.Checked r_ARM64_452 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_inBounds true rfl (fun x y => (cond_sub x y (sub_lt64 x y)).2.2.2.2.2) _ _

end GoFV.Proof.Low.Rules
