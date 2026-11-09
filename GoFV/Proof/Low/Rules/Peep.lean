import GoFV.Proof.Low.Rules.Cmp
import GoFV.Proof.Low.ArmMonoFam

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: constant operands and compares with zero (`ARM64.rules:600-601`, `970-1000`)

Peepholes of lowered code (#385):

* `(CMP x (MOVDconst [c]))`, `(CMPW x (MOVDconst [c]))` and the shifts `(SLL|SRL|SRA x (MOVDconst
  [c]))` take the constant as an immediate. The constant's register is read at its node's shape;
  every shape whose register the op reads whole (`armReadW`: 64 bits; 32 for `CMPW`) holds the
  constant or `poison` (`retypeL_res_wide`, `retypeL_res_w32`), so the result is the immediate
  form's or `poison`. A shift takes its amount modulo 64, which `[c&63]` is (`amt63`); `CMPW` reads
  the low word, which `int32(c)` is (`imm32_wrap`).
* `(AND|OR|XOR x (MOVDconst [c]))` (both argument orders) take the constant as an immediate: the
  result is read at its low `lowW` bits, which only the constant's low bits at its own shape decide
  (`retypeL_res_low`, `retypeL_res_reg`, `refines_bitop_const`).
* `(ADD x (MOVDconst [c]))` (both argument orders) as `(ADDconst [c] x)`: a pointer operand
  (`Arm64.add`'s provenance case) holds a word shape, so the validator's provenance clause
  (`Pat.argsOKLs`) makes the result a word, whose constant operand is read whole
  (`retypeL_res_wide`); any other operand adds as a register, as the bitwise ops do
  (`refines_add_const`). `(SUB x (MOVDconst [c]))` as `(SUBconst [c] x)` likewise, moving a pointer
  by `-c` (`refines_sub_const`).
* `(ADDconst [c] y) && c < 0 => (SUBconst [-c] y)`: subtracting `-c` is adding `c` modulo `2^64`.
* `(EQ|NE (CMPconst [0] x))` as `(Z|NZ x)`, `(EQ|NE (CMPWconst [0] x))` as `(ZW|NZW x)`: the flags
  of a compare read at any shape refine the flags (`retypeL_cmp_ref`), whose `Z` bit is whether the
  register is zero (`subFlags_zero_z`); a pointer without an address compares unequal to 0 and is
  not nil, a nil pointer has address 0 (`isZero_of_cmp0`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- A 64-bit constant register read at a shape with a whole register: the constant, or `poison`. -/
theorem retypeL_res_wide {T : Ty} (h : 64 ≤ argWidth T) (k : BitVec 64) :
    (Arm64.res T k).retypeL T = .int .w64 k ∨ (Arm64.res T k).retypeL T = .poison := by
  cases T with
  | int w => cases w <;> simp_all [argWidth, Width.bits, Arm64.res, Val.retypeL, Val.widen, Val.retype]
  | ptr e => exact .inl rfl
  | agg fs n => exact .inr rfl
  | _ => simp [argWidth] at h

private theorem cmp_poison_right (a : Val) : Arm64.cmp a .poison = .poison := by
  cases a <;> simp [Arm64.cmp, Arm64.reg]

private theorem op2_const (T : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (a : Val) (k : BitVec 64) :
    Arm64.op2 T f [a, .int .w64 k] = Arm64.op1 T (fun x => f x k) [a] := by
  have hk : Arm64.reg (.int .w64 k) = some k := by simp [Arm64.reg]
  cases h : Arm64.reg a <;> simp only [Arm64.op2, Arm64.op1, h, hk]

private theorem op2_poison (T : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (a : Val) :
    Arm64.op2 T f [a, .poison] = .poison := by
  have hk : Arm64.reg .poison = none := rfl
  cases h : Arm64.reg a <;> simp only [Arm64.op2, h, hk]

private theorem cmp2w_poison (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (a : Val) :
    Arm64.cmp2w f [a, .poison] = .poison := by
  have hk : Arm64.reg32 .poison = none := rfl
  cases h : Arm64.reg32 a <;> simp only [Arm64.cmp2w, h, hk]

private theorem amt63 (c : Int) :
    Arm64.amt (Int64.ofInt (wrapInt 64 true ((pat64 c &&& pat64 63 : Nat) : Int))) =
      (BitVec.ofInt 64 c).toNat % 64 := by
  have hp : pat64 c = (BitVec.ofInt 64 c).toNat := by
    simp only [pat64, BitVec.toNat_ofInt]; rfl
  have h63 : pat64 63 = 2 ^ 6 - 1 := by decide
  rw [h63, Nat.and_two_pow_sub_one_eq_mod, ← hp]
  have hm : pat64 c % 2 ^ 6 < 64 := Nat.mod_lt _ (by decide)
  generalize pat64 c % 2 ^ 6 = m at hm ⊢
  simp only [Arm64.amt, wrapInt, ite_true]
  have : ((m : Int)).bmod (2 ^ 64) = m := by
    rw [Int.bmod_eq_of_le] <;> omega
  rw [this, Int64.toInt_ofInt_of_le (by omega) (by omega)]
  omega

/-- `ARM64.rules:1000`: `(ADDconst [c] y) && c < 0 => (SUBconst [-c] y)` -/
theorem r_ARM64_1000_sound : ArmRule.Checked r_ARM64_1000 := by
  left; arm_unfold; arm_norm
  rw [BitVec.ofInt_neg, BitVec.neg_neg]; exact Refines.refl _

/-- `ARM64.rules:990`: `(CMP x (MOVDconst [c])) => (CMPconst [c] x)` -/
theorem r_ARM64_990_sound : ArmRule.Checked r_ARM64_990 := by
  left; arm_unfold; arm_norm
  rcases retypeL_res_wide harg.2 (BitVec.ofInt 64 (e.auxInt [1]).toInt) with h | h <;> rw [h]
  · exact Refines.refl _
  · rw [cmp_poison_right, retypeL_poison]; exact .poison _

/-- `ARM64.rules:983`: `(SLL x (MOVDconst [c])) => (SLLconst x [c&63])` -/
theorem r_ARM64_983_sound : ArmRule.Checked r_ARM64_983 := by
  left; arm_unfold; arm_norm
  rcases retypeL_res_wide harg.2 (BitVec.ofInt 64 (e.auxInt [1]).toInt) with h | h <;> rw [h]
  · rw [op2_const]
    simp only [show (GoTy.int64.intInfo?.getD (64, true)) = (64, true) from rfl, amt63,
      Arm64.Shift.apply, Nat.mod_mod]
    exact Refines.refl _
  · rw [op2_poison, retypeL_poison]; exact .poison _

/-- `ARM64.rules:984`: `(SRL x (MOVDconst [c])) => (SRLconst x [c&63])` -/
theorem r_ARM64_984_sound : ArmRule.Checked r_ARM64_984 := by
  left; arm_unfold; arm_norm
  rcases retypeL_res_wide harg.2 (BitVec.ofInt 64 (e.auxInt [1]).toInt) with h | h <;> rw [h]
  · rw [op2_const]
    simp only [show (GoTy.int64.intInfo?.getD (64, true)) = (64, true) from rfl, amt63,
      Arm64.Shift.apply, Nat.mod_mod]
    exact Refines.refl _
  · rw [op2_poison, retypeL_poison]; exact .poison _

/-- `ARM64.rules:985`: `(SRA x (MOVDconst [c])) => (SRAconst x [c&63])` -/
theorem r_ARM64_985_sound : ArmRule.Checked r_ARM64_985 := by
  left; arm_unfold; arm_norm
  rcases retypeL_res_wide harg.2 (BitVec.ofInt 64 (e.auxInt [1]).toInt) with h | h <;> rw [h]
  · rw [op2_const]
    simp only [show (GoTy.int64.intInfo?.getD (64, true)) = (64, true) from rfl, amt63,
      Arm64.Shift.apply, Nat.mod_mod]
    exact Refines.refl _
  · rw [op2_poison, retypeL_poison]; exact .poison _

theorem imm32_wrap (c : Int) : Arm64.imm32 (Int64.ofInt (wrapInt 32 true c)) = BitVec.ofInt 32 c := by
  simp only [Arm64.imm32, wrapInt, ite_true]
  have h1 := Int.le_bmod (x := c) (m := 2 ^ 32) (by decide)
  have h2 := Int.bmod_lt (x := c) (m := 2 ^ 32) (by decide)
  rw [Int64.toInt_ofInt_of_le (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt]
  rw [Int.bmod_emod]

/-- A 64-bit constant register read at a shape with at least 32 bits: its low word, or `poison`. -/
theorem retypeL_res_w32 {T : Ty} (h : 32 ≤ argWidth T) (k : BitVec 64) :
    Arm64.reg32 ((Arm64.res T k).retypeL T) = some (k.setWidth 32) ∨
      (Arm64.res T k).retypeL T = .poison := by
  cases T with
  | int w => cases w <;> simp_all [argWidth, Width.bits, Arm64.res, Val.retypeL, Val.widen,
      Val.retype, Arm64.reg32, Arm64.reg]
  | ptr e => exact .inl rfl
  | agg fs n => exact .inr rfl
  | _ => simp [argWidth] at h

private theorem cmp2w_reg (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (a b : Val)
    {k : BitVec 32} (hb : Arm64.reg32 b = some k) :
    Arm64.cmp2w f [a, b] = Arm64.cmp1w (fun x => f x k) [a] := by
  cases h : Arm64.reg32 a <;> simp only [Arm64.cmp2w, Arm64.cmp1w, h, hb]

/-- `ARM64.rules:992`: `(CMPW x (MOVDconst [c])) => (CMPWconst [int32(c)] x)` -/
theorem r_ARM64_992_sound : ArmRule.Checked r_ARM64_992 := by
  left; arm_unfold; arm_norm
  rcases retypeL_res_w32 harg.2 (BitVec.ofInt 64 (e.auxInt [1]).toInt) with h | h
  · rw [cmp2w_reg _ _ _ h, imm32_wrap, setWidth_ofInt_le (by decide)]
    exact Refines.refl _
  · rw [h, cmp2w_poison, retypeL_poison]; exact .poison _

theorem retype_bit_ref (t : Ty) {a : Val} (ha : a = .poison ∨ ∃ b, a = .bool b) :
    Refines (a.retype t) a := by
  rcases ha with rfl | ⟨b, rfl⟩
  · cases t <;> exact .poison _
  · cases t <;> first | exact Refines.refl _ | exact .poison _

theorem retypeL_agg5_ref (T : Ty) {a0 a1 a2 a3 a4 : Val}
    (h0 : a0 = .poison ∨ ∃ b, a0 = .bool b) (h1 : a1 = .poison ∨ ∃ b, a1 = .bool b)
    (h2 : a2 = .poison ∨ ∃ b, a2 = .bool b) (h3 : a3 = .poison ∨ ∃ b, a3 = .bool b)
    (h4 : a4 = .poison ∨ ∃ b, a4 = .bool b) :
    Refines ((Val.agg [a0, a1, a2, a3, a4]).retypeL T) (.agg [a0, a1, a2, a3, a4]) := by
  have hw : (Val.agg [a0, a1, a2, a3, a4]).widen T = .agg [a0, a1, a2, a3, a4] := by
    cases T <;> rfl
  rw [Val.retypeL, hw]
  cases T with
  | agg fs n =>
    rcases fs with _ | ⟨⟨_, t0⟩, _ | ⟨⟨_, t1⟩, _ | ⟨⟨_, t2⟩, _ | ⟨⟨_, t3⟩, _ | ⟨⟨_, t4⟩, _ | ⟨_, _⟩⟩⟩⟩⟩⟩
    all_goals first
      | exact .poison _
      | exact .agg (.cons (retype_bit_ref t0 h0) (.cons (retype_bit_ref t1 h1)
          (.cons (retype_bit_ref t2 h2) (.cons (retype_bit_ref t3 h3)
            (.cons (retype_bit_ref t4 h4) .nil)))))
  | _ => exact .poison _

/-- A comparison's flags read at any shape refine the flags. -/
theorem retypeL_cmp_ref (T : Ty) (a b : Val) : Refines ((Arm64.cmp a b).retypeL T) (Arm64.cmp a b) := by
  have hp : ∀ v, v = Val.poison → Refines (v.retypeL T) v := fun v h => by
    subst h; rw [retypeL_poison]; exact .poison _
  have hb : ∀ x : Bool, Val.bool x = .poison ∨ ∃ b, Val.bool x = .bool b := fun x => .inr ⟨x, rfl⟩
  have hq : Val.poison = .poison ∨ ∃ b, Val.poison = .bool b := .inl rfl
  unfold Arm64.cmp
  split
  · exact retypeL_agg5_ref T (hb _) (hb _) (hb _) (hb _) (hb _)
  · split
    · split
      · exact retypeL_agg5_ref T (hb _) (hb _) (hb _) (hb _) (hb _)
      · exact retypeL_agg5_ref T hq (hb _) hq hq hq
    · split
      · exact retypeL_agg5_ref T hq (hb _) hq hq hq
      · exact hp _ rfl
    · split
      · exact retypeL_agg5_ref T hq (hb _) hq hq hq
      · exact hp _ rfl
    · exact hp _ rfl

theorem subFlags_zero_z {n : Nat} (r : BitVec n) : (Arm64.subFlags r 0).2.z = (r == 0) := by
  have h : BitVec.ofNat n (r.toNat + (~~~(0 : BitVec n)).toNat + 1) = r := by
    apply BitVec.eq_of_toNat_eq
    have := r.isLt
    have h2 : (2 : Nat) ^ n > 0 := Nat.two_pow_pos n
    have h0 : (0 : BitVec n).toNat = 0 := by simp
    simp only [BitVec.toNat_ofNat, BitVec.toNat_not, h0]
    rw [show r.toNat + (2 ^ n - 1 - 0) + 1 = r.toNat + 2 ^ n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt this]
  simp only [Arm64.subFlags, addWithCarry, ite_true, h]

private theorem isZero_of_cmp0 {x : Val} {b : Bool}
    (h : Cond.eq.onVal (Arm64.cmp x (.int .w64 0)) = some b) : Arm64.isZero x = some b := by
  have h0 : Arm64.reg (.int .w64 (0 : BitVec 64)) = some 0 := rfl
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    rw [cmp_z_ptr_zero, Option.some.injEq] at h
    subst h; rfl
  · have hz : Arm64.isZero x = (Arm64.reg x).map (· == 0) := by
      cases x <;> first | rfl | exact absurd ⟨_, rfl⟩ hp
    rw [hz]
    cases hx : Arm64.reg x with
    | some r =>
      have hc : Arm64.cmp x (.int .w64 0) = Arm64.cmpRes (Arm64.subFlags r 0) := by
        unfold Arm64.cmp; rw [hx, h0]
      rw [hc, onVal_cmpRes] at h
      simp only [Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.some.injEq,
        subFlags_zero_z] at h
      subst h
      rfl
    | none => cases x <;> simp_all [Arm64.cmp, Arm64.reg, Cond.onVal]

private theorem ofInt64_zero : BitVec.ofInt 64 0 = 0 := rfl

/-- `ARM64.rules:600`: `(EQ (CMPconst [0] x) yes no) => (Z x yes no)` -/
theorem r_ARM64_600_sound : BlockRuleL.Sound r_ARM64_600 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc, ofInt64_zero] at hbr
  simp only [brVal, show BlockKind.ARM64EQ.isArm64 = true from rfl,
    show BlockKind.ARM64Z.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  exact isZero_of_cmp0 (Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr)

private theorem onVal_ne (v : Val) : Cond.ne.onVal v = (Cond.eq.onVal v).map (!·) := by
  unfold Cond.onVal; split <;> rfl

/-- `ARM64.rules:600`: `(NE (CMPconst [0] x) yes no) => (NZ x yes no)` -/
theorem r_ARM64_600_2_sound : BlockRuleL.Sound r_ARM64_600_2 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [hc, ofInt64_zero] at hbr
  simp only [brVal, show BlockKind.ARM64NE.isArm64 = true from rfl,
    show BlockKind.ARM64NZ.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  have h1 := Mono.onVal_of (retypeL_cmp_ref _ _ _) hbr
  rw [onVal_ne] at h1
  cases h2 : Cond.eq.onVal (Arm64.cmp (e.leaf [0]) (Val.int Width.w64 0)) with
  | none => rw [h2] at h1; cases h1
  | some z =>
    rw [h2] at h1; cases h1
    rw [isZero_of_cmp0 h2]; rfl

theorem retypeL_flags1w_ref (T : Ty) (f : BitVec 32 → Flags) (a : Val) :
    Refines ((Arm64.flags1w f [a]).retypeL T) (Arm64.flags1w f [a]) := by
  have hb : ∀ x : Bool, Val.bool x = .poison ∨ ∃ b, Val.bool x = .bool b := fun x => .inr ⟨x, rfl⟩
  cases h : Arm64.reg32 a <;> simp only [Arm64.flags1w, h]
  · rw [retypeL_poison]; exact .poison _
  · exact retypeL_agg5_ref T (hb _) (hb _) (hb _) (hb _) (.inl rfl)

theorem retypeL_cmp1w_ref (T : Ty) (f : BitVec 32 → BitVec 32 × Flags) (a : Val) :
    Refines ((Arm64.cmp1w f [a]).retypeL T) (Arm64.cmp1w f [a]) := by
  have hb : ∀ x : Bool, Val.bool x = .poison ∨ ∃ b, Val.bool x = .bool b := fun x => .inr ⟨x, rfl⟩
  cases h : Arm64.reg32 a <;> simp only [Arm64.cmp1w, h]
  · rw [retypeL_poison]; exact .poison _
  · exact retypeL_agg5_ref T (hb _) (hb _) (hb _) (hb _) (hb _)

theorem reg32_of_cmpw0 {x : Val} {c : Cond} {b : Bool}
    (h : c.onVal (Arm64.cmp1w (fun r => Arm64.subFlags r 0) [x]) = some b) :
    ∃ r, Arm64.reg32 x = some r ∧ c.onVal (Arm64.subFlags r 0).snd.toVal = some b := by
  cases hr : Arm64.reg32 x <;> simp only [Arm64.cmp1w, hr] at h
  · simp [Cond.onVal] at h
  · exact ⟨_, rfl, h⟩

theorem imm32_of_zero {k : Int64} (h : wrapInt 32 true k.toInt = 0) : Arm64.imm32 k = 0 := by
  simp only [wrapInt, ite_true] at h
  have he := Int.bmod_emod (x := k.toInt) (m := 2 ^ 32)
  rw [h] at he
  apply BitVec.eq_of_toNat_eq
  simp only [Arm64.imm32, BitVec.toNat_ofInt, ← he]
  rfl

/-- `ARM64.rules:601`: `(EQ (CMPWconst [0] x) yes no) => (ZW x yes no)` -/
theorem r_ARM64_601_sound : BlockRuleL.Sound r_ARM64_601 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [imm32_of_zero hc] at hbr
  simp only [brVal, show BlockKind.ARM64EQ.isArm64 = true from rfl,
    show BlockKind.ARM64ZW.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  simp only [Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.some.injEq,
    subFlags_zero_z] at h
  rw [hr, ← h]; rfl

/-- `ARM64.rules:601`: `(NE (CMPWconst [0] x) yes no) => (NZW x yes no)` -/
theorem r_ARM64_601_2_sound : BlockRuleL.Sound r_ARM64_601_2 := by
  arm_bunfold; arm_norm
  simp only [DV.int.injEq] at hc
  rw [imm32_of_zero hc] at hbr
  simp only [brVal, show BlockKind.ARM64NE.isArm64 = true from rfl,
    show BlockKind.ARM64NZW.isArm64 = true from rfl, ite_true, Arm64.taken] at hbr ⊢
  rw [Bool.bne_false]
  obtain ⟨r, hr, h⟩ := reg32_of_cmpw0 (Mono.onVal_of (retypeL_cmp1w_ref _ _ _) hbr)
  simp only [Flags.toVal, Cond.onVal, Cond.eval, Val.flagBit, Option.map_some, Option.some.injEq,
    subFlags_zero_z] at h
  rw [hr, ← h]; simp [bne]

/-- The low bits of a register `retypeL` keeps at shape `T` (`armReadW` of a low-bit op). -/
def lowW : Ty → Nat
  | .int w => w.bits
  | .bool => 1
  | _ => 64

theorem armReadW_low (o : Op) (T : Ty) (i : Nat)
    (ho : o = .ARM64AND ∨ o = .ARM64OR ∨ o = .ARM64XOR) : armReadW o T i = lowW T := by
  rcases ho with rfl | rfl | rfl <;> cases T <;> rfl

/-- `retypeL` of a register result reads its low `lowW` bits. -/
theorem retypeL_res_low (T : Ty) {r r' : BitVec 64}
    (h : r.setWidth (lowW T) = r'.setWidth (lowW T)) :
    (Arm64.res T r).retypeL T = (Arm64.res T r').retypeL T := by
  cases T with
  | int w =>
    simp only [lowW] at h
    cases w <;> simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
  | bool =>
    simp only [lowW] at h
    have : r.getLsbD 0 = r'.getLsbD 0 := by
      have h1 := congrArg (fun x : BitVec 1 => x.getLsbD 0) h
      simpa using h1
    simp only [Arm64.res, this]
  | _ => simp only [lowW, BitVec.setWidth_eq] at h; rw [h]

/-- A constant register read at a shape holding at least `n` low bits: `poison`, or a register
with the constant's low `n` bits. -/
theorem retypeL_res_reg {T : Ty} {n : Nat} (hn : 1 ≤ n) (hn' : n ≤ 64) (h : n ≤ argWidth T)
    (k : BitVec 64) : (Arm64.res T k).retypeL T = .poison ∨
      ∃ y, Arm64.reg ((Arm64.res T k).retypeL T) = some y ∧ y.setWidth n = k.setWidth n := by
  cases T with
  | int w =>
    right
    simp only [argWidth] at h
    cases w <;> simp only [Width.bits] at h <;>
      refine ⟨_, rfl, ?_⟩ <;>
      simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits,
        BitVec.setWidth_setWidth_of_le _ h]
  | bool =>
    right
    simp only [argWidth] at h
    have : n = 1 := by omega
    subst this
    refine ⟨_, rfl, ?_⟩
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have : i = 0 := by omega
    subst this
    cases hb : k.getLsbD 0 <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, hb] <;>
      simpa using hb
  | ptr e => right; exact ⟨k, rfl, rfl⟩
  | agg fs m => left; rfl
  | _ => simp [argWidth] at h; omega

theorem lowW_pos (T : Ty) : 1 ≤ lowW T ∧ lowW T ≤ 64 := by
  cases T with
  | int w => cases w <;> decide
  | _ => simp [lowW]

/-- A bitwise op with a constant operand, as its immediate form. -/
private theorem refines_bitop_const {T T1 : Ty} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hfl : ∀ n (a b b' : BitVec 64), b.setWidth n = b'.setWidth n →
      (f a b).setWidth n = (f a b').setWidth n)
    (hw : lowW T ≤ argWidth T1) (x : Val) (k : BitVec 64) :
    Refines ((Arm64.op2 T f [x, (Arm64.res T1 k).retypeL T1]).retypeL T)
      ((Arm64.op1 T (fun a => f a k) [x]).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  rcases retypeL_res_reg h1 h2 hw k with h | ⟨y, hy, hyk⟩
  · rw [h]
    cases hx : Arm64.reg x <;> simp only [Arm64.op2, hx, show Arm64.reg .poison = none from rfl,
      retypeL_poison] <;> exact .poison _
  · cases hx : Arm64.reg x with
    | none => simp only [Arm64.op2, Arm64.op1, hx, hy, retypeL_poison]; exact .poison _
    | some r =>
      simp only [Arm64.op2, Arm64.op1, hx, hy]
      rw [retypeL_res_low T (hfl _ r y k hyk)]
      exact Refines.refl _

private theorem op2_comm (T : Ty) {f : BitVec 64 → BitVec 64 → BitVec 64} (hc : ∀ a b, f a b = f b a)
    (a b : Val) : Arm64.op2 T f [a, b] = Arm64.op2 T f [b, a] := by
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b <;> simp only [Arm64.op2, ha, hb, hc]

private theorem armReadW_add (T : Ty) (i : Nat) : armReadW .ARM64ADD T i = lowW T := by
  cases T <;> rfl

/-- A constant register read at its node's shape is not a pointer. -/
private theorem retypeL_res_not_ptr (T : Ty) (k : BitVec 64) (q : Ptr) :
    (Arm64.res T k).retypeL T ≠ .ptr q := by
  cases T with
  | int w => cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
  | _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype]

private theorem add_comm2 (T : Ty) (a b : Val) : Arm64.add T [a, b] = Arm64.add T [b, a] := by
  cases a <;> cases b <;> (delta Arm64.add; dsimp only) <;>
    first | rfl | exact op2_comm T (fun x y => BitVec.add_comm x y) _ _

private theorem add_nonptr (T : Ty) {x c : Val} (hx : ∀ p, x ≠ .ptr p) (hc : ∀ q, c ≠ .ptr q) :
    Arm64.add T [x, c] = Arm64.op2 T (· + ·) [x, c] := by
  unfold Arm64.add; split <;> simp_all

private theorem addP_nonptr (T : Ty) {x : Val} (hx : ∀ p, x ≠ .ptr p) (k : BitVec 64) :
    Arm64.addP T x k = Arm64.op1 T (fun a => a + k) [x] := by
  unfold Arm64.addP; split
  · simp_all
  · rfl

private theorem setWidth_add_congr (n : Nat) (a b b' : BitVec 64)
    (h : b.setWidth n = b'.setWidth n) : (a + b).setWidth n = (a + b').setWidth n := by
  by_cases hn : n ≤ 64
  · rw [BitVec.setWidth_add _ _ hn, BitVec.setWidth_add _ _ hn, h]
  · have hb : b = b' := by
      have := congrArg (BitVec.setWidth 64) h
      rwa [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_eq, BitVec.setWidth_eq] at this
    rw [hb]

/-- `ADD` with a constant operand, as `ADDconst`: a pointer operand (at a word shape, `Val.hasTy`)
needs a word result (`hs`, `Pat.argsOKLs`'s provenance clause), whose constant operand is read
whole (`retypeL_res_wide`); any other operand adds as a register, whose result keeps the low bits
only the constant's low bits decide (`refines_bitop_const`). -/
private theorem refines_add_const {T T0 T1 : Ty} (hw : lowW T ≤ argWidth T1)
    (hs : (!wordShape T0) = true ∨ wordShape T = true) {x : Val} (hx : x.hasTy T0 = true)
    (k : BitVec 64) :
    Refines ((Arm64.add T [x, (Arm64.res T1 k).retypeL T1]).retypeL T)
      ((Arm64.addP T x k).retypeL T) := by
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    have hT0 : wordShape T0 = true := by
      cases T0 with
      | int w => cases w <;> simp_all [Val.hasTy, wordShape]
      | _ => simp_all [Val.hasTy, wordShape]
    have hT : wordShape T = true := by simpa [hT0] using hs
    have h64 : lowW T = 64 := by
      cases T with
      | int w => cases w <;> simp_all [wordShape, lowW, Width.bits]
      | _ => simp_all [wordShape, lowW]
    rcases retypeL_res_wide (h64 ▸ hw) k with h | h
    · rw [h]; simp only [Arm64.add, Arm64.reg, BitVec.setWidth_eq, Arm64.addP]; exact Refines.refl _
    · rw [h]; simp only [Arm64.add, Arm64.reg, retypeL_poison]; exact .poison _
  · have hp' : ∀ p, x ≠ .ptr p := fun p h => hp ⟨p, h⟩
    rw [add_nonptr T hp' (retypeL_res_not_ptr T1 k), addP_nonptr T hp']
    exact refines_bitop_const (· + ·) setWidth_add_congr hw x k

/-- `ARM64.rules:970`: `(ADD x (MOVDconst <t> [c])) && !t.IsPtr() => (ADDconst [c] x)` -/
theorem r_ARM64_970_sound : ArmRule.Checked r_ARM64_970 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_add_const (armReadW_add _ 1 ▸ harg.2.1) harg.1.2 hty _
  · rw [add_comm2]
    exact refines_add_const (armReadW_add _ 0 ▸ harg.1.1) harg.2.2 hty _

/-- `ARM64.rules:972`: `(AND x (MOVDconst [c])) => (ANDconst [c] x)` -/
theorem r_ARM64_972_sound : ArmRule.Checked r_ARM64_972 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_and, h])
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2) _ _
  · rw [op2_comm _ (fun a b => BitVec.and_comm a b)]
    exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_and, h])
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1) _ _

/-- `ARM64.rules:973`: `(OR x (MOVDconst [c])) => (ORconst [c] x)` -/
theorem r_ARM64_973_sound : ArmRule.Checked r_ARM64_973 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_or, h])
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2) _ _
  · rw [op2_comm _ (fun a b => BitVec.or_comm a b)]
    exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_or, h])
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1) _ _

/-- `ARM64.rules:974`: `(XOR x (MOVDconst [c])) => (XORconst [c] x)` -/
theorem r_ARM64_974_sound : ArmRule.Checked r_ARM64_974 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_xor, h])
      (armReadW_low .ARM64XOR _ 1 (by simp) ▸ harg.2) _ _
  · rw [op2_comm _ (fun a b => BitVec.xor_comm a b)]
    exact refines_bitop_const _ (fun n a b b' h => by simp only [BitVec.setWidth_xor, h])
      (armReadW_low .ARM64XOR _ 0 (by simp) ▸ harg.1) _ _

private theorem armReadW_sub (T : Ty) (i : Nat) : armReadW .ARM64SUB T i = lowW T := by
  cases T <;> rfl

private theorem sub_nonptr (T : Ty) {x c : Val} (hx : ∀ p, x ≠ .ptr p) :
    Arm64.sub T [x, c] = Arm64.op2 T (· - ·) [x, c] := by
  unfold Arm64.sub; split <;> simp_all

private theorem setWidth_sub_congr (n : Nat) (a b b' : BitVec 64)
    (h : b.setWidth n = b'.setWidth n) : (a - b).setWidth n = (a - b').setWidth n := by
  by_cases hn : n ≤ 64
  · rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hn,
      BitVec.setWidth_add _ _ hn, BitVec.setWidth_neg_of_le hn, BitVec.setWidth_neg_of_le hn, h]
  · have hb : b = b' := by
      have := congrArg (BitVec.setWidth 64) h
      rwa [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_setWidth_of_le _ (by omega),
        BitVec.setWidth_eq, BitVec.setWidth_eq] at this
    rw [hb]

/-- `SUB` with a constant operand, as `SUBconst` (`ADDconst` of the negated constant): as
`refines_add_const`, a pointer operand needs a word result whose constant is read whole, and both
sides move the pointer by `-k`; any other operand subtracts as a register. -/
private theorem refines_sub_const {T T0 T1 : Ty} (hw : lowW T ≤ argWidth T1)
    (hs : (!wordShape T0) = true ∨ wordShape T = true) {x : Val} (hx : x.hasTy T0 = true)
    (k : BitVec 64) :
    Refines ((Arm64.sub T [x, (Arm64.res T1 k).retypeL T1]).retypeL T)
      ((Arm64.addP T x (-k)).retypeL T) := by
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    have hT0 : wordShape T0 = true := by
      cases T0 with
      | int w => cases w <;> simp_all [Val.hasTy, wordShape]
      | _ => simp_all [Val.hasTy, wordShape]
    have hT : wordShape T = true := by simpa [hT0] using hs
    have h64 : lowW T = 64 := by
      cases T with
      | int w => cases w <;> simp_all [wordShape, lowW, Width.bits]
      | _ => simp_all [wordShape, lowW]
    rcases retypeL_res_wide (h64 ▸ hw) k with h | h
    · rw [h]; simp only [Arm64.sub, Arm64.reg, BitVec.setWidth_eq, Arm64.addP]; exact Refines.refl _
    · rw [h]; simp only [Arm64.sub, Arm64.reg, retypeL_poison]; exact .poison _
  · have hp' : ∀ p, x ≠ .ptr p := fun p h => hp ⟨p, h⟩
    rw [sub_nonptr T hp', addP_nonptr T hp']
    have hf : (fun a : BitVec 64 => a + -k) = (fun a => a - k) := by
      funext a; exact (BitVec.sub_eq_add_neg a k).symm
    rw [hf]
    exact refines_bitop_const (· - ·) setWidth_sub_congr hw x k

/-- `ARM64.rules:971`: `(SUB x (MOVDconst [c])) => (SUBconst [c] x)` -/
theorem r_ARM64_971_sound : ArmRule.Checked r_ARM64_971 := by
  left; arm_unfold; arm_norm
  exact refines_sub_const (armReadW_sub _ 1 ▸ harg.2.1) harg.1.2 hty _

end GoFV.Proof.Low.Rules
