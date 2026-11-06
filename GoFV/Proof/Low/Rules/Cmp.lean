import GoFV.Proof.Low.Rules.Flags
import GoFV.Proof.Low.Rules.Tactic
import GoFV.Proof.PtrAddr
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: integer and pointer comparisons (`ARM64.rules:239-293`, `450-452`)

`(Eq64 x y) => (Equal (CMP x y))` and the `Neq`/`Less`/`Leq` (signed and unsigned) forms of all
widths: 32- and 64-bit operands compare by `CMPW`/`CMP` directly, 8- and 16-bit ones after a
`ZeroExt`/`SignExt` to 32 bits, which keeps `==`, `<ᵤ`, `≤ᵤ` (`zext_*`) and `<ₛ`, `≤ₛ`
(`sext_*`). The flags of `SUBS` read by the condition are Phase 1's comparison
(`Flags.cond_sub`), and `CSET` at the boolean shape is the condition (`refines_cset_bool`).
`IsInBounds`/`IsSliceInBounds` are `LessThanU`/`LessEqualU` of `CMP` on an index of any width
(`refines_inBounds`).

`EqPtr`/`NeqPtr` (243, 251) and `IsNonNil` (450): a pointer's register is its address `a` only
when it is the pointer `Ptr.ofAddr a` (`Arm64.ptrReg`, `ptrReg_eq_some`), and Phase 1 reads an
integer word `x` as `Ptr.ofAddr x`, so `CMP` of two registers is pointer equality
(`Ptr.ofAddr_eq_ofAddr`); a pointer without a register is no word's pointer and `CMP` compares it
by provenance (`cmp_z_ptr`). Before that gate both were false: the frame variable `local 0 1` and
the frame temporary `temp 0 1` share an address, and `heap 0 + (2^64 - 2^40)` has address 0.
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

@[simp] theorem retypeL_cmpRes {n : Nat} (p : BitVec n × Flags) :
    (Arm64.cmpRes p).retypeL Ty.flags = Arm64.cmpRes p := rfl

@[simp] theorem onVal_cmpRes (c : Cond) {n : Nat} (p : BitVec n × Flags) :
    c.onVal (Arm64.cmpRes p) = c.onVal p.2.toVal := rfl

theorem cmp_int (w w' : Width) (x : BitVec w.bits) (y : BitVec w'.bits) :
    Arm64.cmp (.int w x) (.int w' y) = Arm64.cmpRes (Arm64.subFlags (x.setWidth 64) (y.setWidth 64)) :=
  rfl

theorem cmp2w_int (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (w w' : Width) (x : BitVec w.bits)
    (y : BitVec w'.bits) :
    Arm64.cmp2w f [.int w x, .int w' y] = Arm64.cmpRes (f (x.setWidth 32) (y.setWidth 32)) := by
  simp only [Arm64.cmp2w, Arm64.reg32, Arm64.reg, Option.map_some,
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
      · rw [cmp_int, retypeL_cmpRes]
        refine refines_cset_bool hop ?_
        rw [onVal_cmpRes]
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
  simp only [cmp_int, cmp2w_int, retypeL_cmpRes, setWidth_w64, setWidth_w32]
  refine refines_cset_bool rfl ?_
  rw [onVal_cmpRes]
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

/-! ## Pointer compares -/

/-- A pointer's register is `a` exactly when it is the pointer at `a`. -/
theorem ptrReg_eq_some {p : Ptr} {a : BitVec 64} :
    Arm64.ptrReg p = some a ↔ Ptr.ofAddr a = p := by
  unfold Arm64.ptrReg
  constructor
  · intro h
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h
  · rintro rfl
    rw [Ptr.addr?_ofAddr]
    simp

/-- A pointer without a register is the pointer at no address. -/
theorem ofAddr_ne_of_ptrReg {p : Ptr} (h : Arm64.ptrReg p = none) (a : BitVec 64) :
    Ptr.ofAddr a ≠ p := fun he => by
  have := ptrReg_eq_some.2 he
  rw [h] at this; cases this

private theorem asPtrWord_cases {v : Val} {p : Ptr} (hv : v.asPtrWord = some p) :
    (∃ x, v = .int .w64 x ∧ Ptr.ofAddr x = p) ∨ v = .ptr p := by
  cases v with
  | ptr p' => simp only [Val.asPtrWord, Option.some.injEq] at hv; exact .inr (hv ▸ rfl)
  | int w x =>
    cases w <;> simp only [Val.asPtrWord, Option.some.injEq, reduceCtorEq] at hv
    exact .inl ⟨x, rfl, hv⟩
  | _ => simp only [Val.asPtrWord, reduceCtorEq] at hv

private theorem z_sub64 (x y : BitVec 64) :
    Cond.eq.onVal (Arm64.cmpRes (Arm64.subFlags x y)) = some (x == y) := by
  rw [onVal_cmpRes, (cond_sub x y (sub_lt64 x y)).1]

private theorem z_none :
    Cond.eq.onVal (Val.agg [.poison, .bool false, .poison, .poison, .poison]) = some false := rfl

/-- `CMP`'s result is flags-shaped. -/
@[simp] theorem retypeL_cmp (a b : Val) : (Arm64.cmp a b).retypeL Ty.flags = Arm64.cmp a b := by
  unfold Arm64.cmp
  split
  · rfl
  · split <;> (try split) <;> rfl

/-- The `Z` flag of `CMP a b` on two pointer words is Phase 1's pointer equality (`EqPtr`):
pointers with registers are the pointers at those registers (`ptrReg_eq_some`), and a pointer
without one is no integer word's pointer and compares by provenance. -/
theorem cmp_z_ptr {a b : Val} {p q : Ptr} (ha : a.asPtrWord = some p)
    (hb : b.asPtrWord = some q) :
    Cond.eq.onVal (Arm64.cmp a b) = some (p.eq q) := by
  have hne : ∀ {r : Ptr}, Arm64.ptrReg r = none → ∀ x, (Ptr.ofAddr x).eq r = false ∧
      r.eq (Ptr.ofAddr x) = false := fun {r} hr x => by
    have h := ofAddr_ne_of_ptrReg hr x
    constructor
    · cases he : (Ptr.ofAddr x).eq r
      · rfl
      · exact absurd ((Ptr.eq_iff _ _).1 he) h
    · cases he : r.eq (Ptr.ofAddr x)
      · rfl
      · exact absurd ((Ptr.eq_iff _ _).1 he).symm h
  rcases asPtrWord_cases ha with ⟨x, rfl, rfl⟩ | rfl <;>
    rcases asPtrWord_cases hb with ⟨y, rfl, rfl⟩ | rfl
  · rw [cmp_int, setWidth_w64, setWidth_w64, z_sub64, Ptr.ofAddr_eq_ofAddr]
  · cases hq : Arm64.ptrReg q with
    | none =>
      simp only [Arm64.cmp, Arm64.reg, hq, Option.isSome_some, ite_true]
      rw [z_none, (hne hq x).1]
    | some y =>
      obtain rfl := ptrReg_eq_some.1 hq
      simp only [Arm64.cmp, Arm64.reg, hq, setWidth_w64]
      rw [z_sub64, Ptr.ofAddr_eq_ofAddr]
  · cases hp : Arm64.ptrReg p with
    | none =>
      simp only [Arm64.cmp, Arm64.reg, hp, Option.isSome_some, ite_true]
      rw [z_none, (hne hp y).2]
    | some x =>
      obtain rfl := ptrReg_eq_some.1 hp
      simp only [Arm64.cmp, Arm64.reg, hp, setWidth_w64]
      rw [z_sub64, Ptr.ofAddr_eq_ofAddr]
  · cases hp : Arm64.ptrReg p <;> cases hq : Arm64.ptrReg q
    rotate_left 3
    · rename_i x y
      obtain rfl := ptrReg_eq_some.1 hp
      obtain rfl := ptrReg_eq_some.1 hq
      simp only [Arm64.cmp, Arm64.reg, hp, hq]
      rw [z_sub64, Ptr.ofAddr_eq_ofAddr]
    all_goals
      simp only [Arm64.cmp, Arm64.reg, hp, hq]
      obtain ⟨bp, op⟩ := p; obtain ⟨bq, oq⟩ := q
      by_cases hb : bp = bq
      · subst hb
        simp only [beq_self_eq_true, ite_true, z_sub64, Ptr.eq, Bool.true_and]
      · have hb' : (bp == bq) = false := by simp [hb]
        simp only [hb', ite_false, Bool.false_eq_true, z_none, Ptr.eq, Bool.false_and]

/-- `Z` of `CMPconst [0] p`: whether `p` is nil. -/
theorem cmp_z_ptr_zero (p : Ptr) : Cond.eq.onVal (Arm64.cmp (.ptr p) (.int .w64 0)) = some p.isNil := by
  have hz : (Val.int .w64 (0 : BitVec 64)).asPtrWord = some Ptr.null := rfl
  rw [cmp_z_ptr rfl hz]
  obtain ⟨b, o⟩ := p
  simp [Ptr.eq, Ptr.isNil, Ptr.null]

theorem onVal_ne_eq (f : Val) : Cond.ne.onVal f = (Cond.eq.onVal f).map (!·) := by
  unfold Cond.onVal; split <;> rfl

/-- `EqPtr`/`NeqPtr` (`neg`) as `Equal`/`NotEqual` of `CMP` (`ARM64.rules:243`, `251`). -/
theorem refines_eqPtr (neg : Bool) {op : Op} {c : Cond} (hop : Cond.ofOp op = some c)
    (hc : ∀ f, c.onVal f = (Cond.eq.onVal f).map (· != neg)) (a b : Val) :
    Refines ((PtrOps.eqPtr neg [a, b]).retypeL .bool)
      ((Arm64.cset .bool op [(Arm64.cmp a b).retypeL Ty.flags]).retypeL .bool) := by
  cases ha : a.asPtrWord with
  | none => simp only [PtrOps.eqPtr, ha, retypeL_poison]; exact .poison _
  | some p =>
    cases hb : b.asPtrWord with
    | none => simp only [PtrOps.eqPtr, ha, hb, retypeL_poison]; exact .poison _
    | some q =>
      simp only [PtrOps.eqPtr, ha, hb]
      refine refines_cset_bool hop ?_
      rw [hc, retypeL_cmp, cmp_z_ptr ha hb]; rfl

/-- `ARM64.rules:243`: `(EqPtr x y) => (Equal (CMP x y))` -/
theorem r_ARM64_243_sound : ArmRule.Checked r_ARM64_243 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_eqPtr false rfl (fun f => by cases Cond.eq.onVal f <;> simp) _ _

/-- `ARM64.rules:251`: `(NeqPtr x y) => (NotEqual (CMP x y))` -/
theorem r_ARM64_251_sound : ArmRule.Checked r_ARM64_251 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  exact refines_eqPtr true rfl (fun f => by rw [onVal_ne_eq]; cases Cond.eq.onVal f <;> simp) _ _

/-- `ARM64.rules:450`: `(IsNonNil ptr) => (NotEqual (CMPconst [0] ptr))` -/
theorem r_ARM64_450_sound : ArmRule.Checked r_ARM64_450 := by
  left
  arm_unfold
  all_goals arm_shape
  all_goals arm_norm
  have h0 : BitVec.ofInt 64 0 = 0 := rfl
  rw [h0]
  cases ha : e.leaf [0] with
  | int w x =>
    simp only [PtrOps.isNonNil]
    rw [cmp_int, setWidth_w64, retypeL_cmpRes]
    refine refines_cset_bool rfl ?_
    have hw : w.bits ≤ 64 := by cases w <;> decide
    rw [onVal_ne_eq, show (0 : BitVec 64) = (0 : BitVec w.bits).setWidth 64 by simp, z_sub64,
      Option.map_some, zext_beq x 0 hw]
    rfl
  | ptr p =>
    simp only [PtrOps.isNonNil]
    refine refines_cset_bool rfl ?_
    rw [retypeL_cmp, onVal_ne_eq, cmp_z_ptr_zero]
    rfl
  | _ => simp only [PtrOps.isNonNil, retypeL_poison]; exact .poison _

end GoFV.Proof.Low.Rules
