import GoFV.Proof.Low.Rules.Kit
import GoFV.Rules.Generated.ARM64

/-!
# Lowering rule lemmas: ellipsis rules on integer ops (`ARM64.rules:5-50`, `108-110`, `191-211`)

`ArmRule.SetOp` of `(o ...) => (o' ...)` with `o` a generic integer op and `o'` its arm64 op
(`Copy` for the truncations): 64-bit arithmetic, `Mul32`/`MULW`, the bitwise ops and the zero
and 64-bit sign extensions compute the zero-extended register of the generic result, sound at
every shape (`setOpSound_int1`, `setOpSound_int2`); narrow arithmetic, the narrow sign
extensions and the truncations agree on the low bits, at the op's own shape (`setOpSound_top1`,
`setOpSound_top2`, the `topOKL` premise). The byte swaps compute the zero-extended register too:
`REV`/`REVW` reverse the bytes as `Bswap64`/`Bswap32`, `REV16W` of a zero-extended halfword
swaps its two bytes as `Bswap16` (`rev16_setWidth`, `bswap16_eq`). `(AddPtr ...) => (ADD ...)`
is sound on a 64-bit integer index (`SetOpSoundT`, which the validator checks, `setArgsOK`):
`AddPtr` sign-extends its index, `ADD` reads the register.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low GoFV.Opt.LowerTerm
open GoFV.Rules.Generated.ARM64

private theorem s_Add16_ARM64ADD : SetOpSound .Add16 .ARM64ADD :=
  setOpSound_top2 .w16 (· + ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Add32_ARM64ADD : SetOpSound .Add32 .ARM64ADD :=
  setOpSound_top2 .w32 (· + ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Add64_ARM64ADD : SetOpSound .Add64 .ARM64ADD :=
  setOpSound_int2 .w64 (· + ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Add8_ARM64ADD : SetOpSound .Add8 .ARM64ADD :=
  setOpSound_top2 .w8 (· + ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Sub16_ARM64SUB : SetOpSound .Sub16 .ARM64SUB :=
  setOpSound_top2 .w16 (· - ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Sub32_ARM64SUB : SetOpSound .Sub32 .ARM64SUB :=
  setOpSound_top2 .w32 (· - ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Sub64_ARM64SUB : SetOpSound .Sub64 .ARM64SUB :=
  setOpSound_int2 .w64 (· - ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Sub8_ARM64SUB : SetOpSound .Sub8 .ARM64SUB :=
  setOpSound_top2 .w8 (· - ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Mul64_ARM64MUL : SetOpSound .Mul64 .ARM64MUL :=
  setOpSound_int2 .w64 (· * ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Mul16_ARM64MULW : SetOpSound .Mul16 .ARM64MULW :=
  setOpSound_top2 .w16 (· * ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Mul32_ARM64MULW : SetOpSound .Mul32 .ARM64MULW :=
  setOpSound_int2 .w32 (· * ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Mul8_ARM64MULW : SetOpSound .Mul8 .ARM64MULW :=
  setOpSound_top2 .w8 (· * ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_And16_ARM64AND : SetOpSound .And16 .ARM64AND :=
  setOpSound_int2 .w16 (· &&& ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Or16_ARM64OR : SetOpSound .Or16 .ARM64OR :=
  setOpSound_int2 .w16 (· ||| ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Xor16_ARM64XOR : SetOpSound .Xor16 .ARM64XOR :=
  setOpSound_int2 .w16 (· ^^^ ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_And32_ARM64AND : SetOpSound .And32 .ARM64AND :=
  setOpSound_int2 .w32 (· &&& ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Or32_ARM64OR : SetOpSound .Or32 .ARM64OR :=
  setOpSound_int2 .w32 (· ||| ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Xor32_ARM64XOR : SetOpSound .Xor32 .ARM64XOR :=
  setOpSound_int2 .w32 (· ^^^ ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_And64_ARM64AND : SetOpSound .And64 .ARM64AND :=
  setOpSound_int2 .w64 (· &&& ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Or64_ARM64OR : SetOpSound .Or64 .ARM64OR :=
  setOpSound_int2 .w64 (· ||| ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Xor64_ARM64XOR : SetOpSound .Xor64 .ARM64XOR :=
  setOpSound_int2 .w64 (· ^^^ ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_And8_ARM64AND : SetOpSound .And8 .ARM64AND :=
  setOpSound_int2 .w8 (· &&& ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Or8_ARM64OR : SetOpSound .Or8 .ARM64OR :=
  setOpSound_int2 .w8 (· ||| ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Xor8_ARM64XOR : SetOpSound .Xor8 .ARM64XOR :=
  setOpSound_int2 .w8 (· ^^^ ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Neg16_ARM64NEG : SetOpSound .Neg16 .ARM64NEG :=
  setOpSound_top1 .w16 .w16 (- ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Com16_ARM64MVN : SetOpSound .Com16 .ARM64MVN :=
  setOpSound_top1 .w16 .w16 (~~~ ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Neg32_ARM64NEG : SetOpSound .Neg32 .ARM64NEG :=
  setOpSound_top1 .w32 .w32 (- ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Com32_ARM64MVN : SetOpSound .Com32 .ARM64MVN :=
  setOpSound_top1 .w32 .w32 (~~~ ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Neg64_ARM64NEG : SetOpSound .Neg64 .ARM64NEG :=
  setOpSound_int1 .w64 .w64 (- ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Com64_ARM64MVN : SetOpSound .Com64 .ARM64MVN :=
  setOpSound_int1 .w64 .w64 (~~~ ·) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Neg8_ARM64NEG : SetOpSound .Neg8 .ARM64NEG :=
  setOpSound_top1 .w8 .w8 (- ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Com8_ARM64MVN : SetOpSound .Com8 .ARM64MVN :=
  setOpSound_top1 .w8 .w8 (~~~ ·) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc16to8_Copy : SetOpSound .Trunc16to8 .Copy :=
  setOpSound_top1 .w16 .w8 (·.setWidth 8) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc32to8_Copy : SetOpSound .Trunc32to8 .Copy :=
  setOpSound_top1 .w32 .w8 (·.setWidth 8) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc32to16_Copy : SetOpSound .Trunc32to16 .Copy :=
  setOpSound_top1 .w32 .w16 (·.setWidth 16) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc64to8_Copy : SetOpSound .Trunc64to8 .Copy :=
  setOpSound_top1 .w64 .w8 (·.setWidth 8) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc64to16_Copy : SetOpSound .Trunc64to16 .Copy :=
  setOpSound_top1 .w64 .w16 (·.setWidth 16) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Trunc64to32_Copy : SetOpSound .Trunc64to32 .Copy :=
  setOpSound_top1 .w64 .w32 (·.setWidth 32) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt8to16_ARM64MOVBUreg : SetOpSound .ZeroExt8to16 .ARM64MOVBUreg :=
  setOpSound_int1 .w8 .w16 (·.setWidth 16) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt8to32_ARM64MOVBUreg : SetOpSound .ZeroExt8to32 .ARM64MOVBUreg :=
  setOpSound_int1 .w8 .w32 (·.setWidth 32) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt16to32_ARM64MOVHUreg : SetOpSound .ZeroExt16to32 .ARM64MOVHUreg :=
  setOpSound_int1 .w16 .w32 (·.setWidth 32) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt8to64_ARM64MOVBUreg : SetOpSound .ZeroExt8to64 .ARM64MOVBUreg :=
  setOpSound_int1 .w8 .w64 (·.setWidth 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt16to64_ARM64MOVHUreg : SetOpSound .ZeroExt16to64 .ARM64MOVHUreg :=
  setOpSound_int1 .w16 .w64 (·.setWidth 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_ZeroExt32to64_ARM64MOVWUreg : SetOpSound .ZeroExt32to64 .ARM64MOVWUreg :=
  setOpSound_int1 .w32 .w64 (·.setWidth 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt8to16_ARM64MOVBreg : SetOpSound .SignExt8to16 .ARM64MOVBreg :=
  setOpSound_top1 .w8 .w16 (·.signExtend 16) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt8to32_ARM64MOVBreg : SetOpSound .SignExt8to32 .ARM64MOVBreg :=
  setOpSound_top1 .w8 .w32 (·.signExtend 32) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt16to32_ARM64MOVHreg : SetOpSound .SignExt16to32 .ARM64MOVHreg :=
  setOpSound_top1 .w16 .w32 (·.signExtend 32) (by arm_top) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt8to64_ARM64MOVBreg : SetOpSound .SignExt8to64 .ARM64MOVBreg :=
  setOpSound_int1 .w8 .w64 (·.signExtend 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt16to64_ARM64MOVHreg : SetOpSound .SignExt16to64 .ARM64MOVHreg :=
  setOpSound_int1 .w16 .w64 (·.signExtend 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_SignExt32to64_ARM64MOVWreg : SetOpSound .SignExt32to64 .ARM64MOVWreg :=
  setOpSound_int1 .w32 .w64 (·.signExtend 64) (fun _ _ _ _ _ => rfl) (by arm_reg)

private theorem s_Bswap64_ARM64REV : SetOpSound .Bswap64 .ARM64REV :=
  setOpSound_int1 .w64 .w64 (fun x => BitVec.ofNat 64 (Int.bswapNat 8 x.toNat))
    (fun _ _ _ _ _ => rfl) (by arm_reg <;> rfl)

private theorem s_Bswap32_ARM64REVW : SetOpSound .Bswap32 .ARM64REVW :=
  setOpSound_int1 .w32 .w32 (fun x => BitVec.ofNat 32 (Int.bswapNat 4 x.toNat))
    (fun _ _ _ _ _ => rfl) (by arm_reg <;> rfl)

/-- `Bswap16` of `x`: its two bytes swapped. -/
theorem bswap16_eq (x : BitVec 16) :
    BitVec.ofNat 16 (Int.bswapNat 2 x.toNat) = (x <<< 8) + (x >>> 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Int.bswapNat, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_zero,
    Nat.mul_one, Nat.add_zero, show (2 : Nat) ^ 8 = 256 from rfl, show (2 : Nat) ^ 16 = 65536 from rfl]
  have h1 := x.isLt
  have h2 : x.toNat / 256 < 256 := by omega
  have h3 : x.toNat * 256 % 65536 = x.toNat % 256 * 256 := by omega
  rw [Nat.mod_eq_of_lt h2, h3]

private theorem shl8_add_shr8 (x : BitVec 16) : (x <<< 8) + (x >>> 8) = (x <<< 8) ||| (x >>> 8) := by
  apply BitVec.add_eq_or_of_and_eq_zero
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_zero]
  by_cases h : i < 8
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x (8 + i) (by omega)]

/-- `REV16W` of a zero-extended halfword: its two bytes swapped, zero-extended. -/
theorem rev16_setWidth (x : BitVec 16) :
    Arm64.rev16 (x.setWidth 32) = ((x <<< 8) + (x >>> 8)).setWidth 32 := by
  rw [shl8_add_shr8]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm64.rev16, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat]
  iterate 32 (rcases i with _ | i; · simp (config := { decide := true }))
  omega

private theorem s_Bswap16_ARM64REV16W : SetOpSound .Bswap16 .ARM64REV16W :=
  setOpSound_int1 .w16 .w16 (fun x => BitVec.ofNat 16 (Int.bswapNat 2 x.toNat))
    (fun _ _ _ _ _ => rfl) (by
      intro tabs ty ai ax x
      show Arm64.op1w ty Arm64.rev16 [.int .w16 x] = _
      simp only [Arm64.op1w, Arm64.reg32, Arm64.reg, Arm64.res32, Option.map]
      rw [BitVec.setWidth_setWidth_of_le _ (by decide), rev16_setWidth, bswap16_eq]
      congr 1)

/-- `ARM64.rules:5`: `(Add16 ...) => (ADD ...)` -/
theorem r_ARM64_5_sound : ArmRule.Checked r_ARM64_5 :=
  checked_setOp .Add16 .ARM64ADD rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Add16_ARM64ADD

/-- `ARM64.rules:5`: `(Add32 ...) => (ADD ...)` -/
theorem r_ARM64_5_2_sound : ArmRule.Checked r_ARM64_5_2 :=
  checked_setOp .Add32 .ARM64ADD rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Add32_ARM64ADD

/-- `ARM64.rules:5`: `(Add64 ...) => (ADD ...)` -/
theorem r_ARM64_5_3_sound : ArmRule.Checked r_ARM64_5_3 :=
  checked_setOp .Add64 .ARM64ADD rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Add64_ARM64ADD

/-- `ARM64.rules:5`: `(Add8 ...) => (ADD ...)` -/
theorem r_ARM64_5_4_sound : ArmRule.Checked r_ARM64_5_4 :=
  checked_setOp .Add8 .ARM64ADD rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Add8_ARM64ADD

/-- `AddPtr p i` at a pointer shape (`topOKL`) with `i` a 64-bit integer (`setArgW64`) is `ADD p i`:
`PtrOps.addPtr` sign-extends the index, which at 64 bits is its register; a pointer moves under
the window rule on both sides (`PtrOps.ptrRes`); an integer word adds as an integer, which
`PtrOps.wordRes` makes `poison` outside the window; any other base or index is `poison`. -/
private theorem s_AddPtr_ARM64ADD : SetOpSoundT .AddPtr .ARM64ADD := by
  intro tabs ty ai ax args htop hw
  obtain ⟨e, rfl⟩ : ∃ e, ty = .ptr e := by
    revert htop
    cases ty <;> simp [topOKL, GoFV.Opt.RewriteCheck.topOK, GoFV.Opt.RewriteCheck.natShape,
      GoFV.Opt.RewriteCheck.ptrTop, GoFV.Opt.RewriteCheck.constTop, GoFV.Opt.RewriteCheck.frameTop,
      atomicLoadOp] <;>
      first | exact ⟨rfl, rfl⟩ | exact ⟨rfl, rfl, rfl⟩ | decide | (rename_i w; cases w <;> decide)
  rw [opValL_gen rfl rfl, opValL_arm rfl rfl rfl]
  show Sem.Refines ((PtrOps.addPtr args).retypeL (.ptr e)) ((Arm64.add (.ptr e) args).retypeL (.ptr e))
  rcases args with _ | ⟨a, _ | ⟨i, _ | ⟨c, rest⟩⟩⟩
  · exact .poison _
  · cases a <;> first | exact .poison _ | (rename_i w _; cases w <;> exact .poison _)
  · have hi := hw 1 i rfl rfl
    cases i with
    | int w k =>
      obtain rfl : w = .w64 := by cases w <;> simp_all [Val.hasTy]
      cases a with
      | ptr p =>
        simp only [PtrOps.addPtr, asOffset, BitVec.signExtend_eq, Arm64.add, Arm64.reg,
          BitVec.setWidth_eq]
        exact Refines.refl _
      | int w x =>
        cases w
        all_goals try exact .poison _
        simp only [PtrOps.addPtr, asOffset, BitVec.signExtend_eq, PtrOps.wordRes, Arm64.add,
          Arm64.op2, Arm64.reg, BitVec.setWidth_eq, Arm64.res]
        split
        · exact Refines.refl _
        · exact .poison _
      | _ => exact .poison _
    | ptr q => cases a <;> first | exact .poison _ | (rename_i w _; cases w <;> exact .poison _)
    | poison => cases a <;> first | exact .poison _ | (rename_i w _; cases w <;> exact .poison _)
    | _ => simp [Val.hasTy] at hi
  · cases a <;> first | exact .poison _ | (rename_i w _; cases w <;> exact .poison _)

/-- `ARM64.rules:5`: `(AddPtr ...) => (ADD ...)` -/
theorem r_ARM64_5_5_sound : ArmRule.Checked r_ARM64_5_5 :=
  checked_setOpT .AddPtr .ARM64ADD rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_arm _ rfl rfl rfl) s_AddPtr_ARM64ADD

/-- `ARM64.rules:8`: `(Sub16 ...) => (SUB ...)` -/
theorem r_ARM64_8_sound : ArmRule.Checked r_ARM64_8 :=
  checked_setOp .Sub16 .ARM64SUB rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Sub16_ARM64SUB

/-- `ARM64.rules:8`: `(Sub32 ...) => (SUB ...)` -/
theorem r_ARM64_8_2_sound : ArmRule.Checked r_ARM64_8_2 :=
  checked_setOp .Sub32 .ARM64SUB rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Sub32_ARM64SUB

/-- `ARM64.rules:8`: `(Sub64 ...) => (SUB ...)` -/
theorem r_ARM64_8_3_sound : ArmRule.Checked r_ARM64_8_3 :=
  checked_setOp .Sub64 .ARM64SUB rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Sub64_ARM64SUB

/-- `ARM64.rules:8`: `(Sub8 ...) => (SUB ...)` -/
theorem r_ARM64_8_4_sound : ArmRule.Checked r_ARM64_8_4 :=
  checked_setOp .Sub8 .ARM64SUB rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Sub8_ARM64SUB

/-- `ARM64.rules:11`: `(Mul64 ...) => (MUL ...)` -/
theorem r_ARM64_11_sound : ArmRule.Checked r_ARM64_11 :=
  checked_setOp .Mul64 .ARM64MUL rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Mul64_ARM64MUL

/-- `ARM64.rules:12`: `(Mul16 ...) => (MULW ...)` -/
theorem r_ARM64_12_sound : ArmRule.Checked r_ARM64_12 :=
  checked_setOp .Mul16 .ARM64MULW rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Mul16_ARM64MULW

/-- `ARM64.rules:12`: `(Mul32 ...) => (MULW ...)` -/
theorem r_ARM64_12_2_sound : ArmRule.Checked r_ARM64_12_2 :=
  checked_setOp .Mul32 .ARM64MULW rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Mul32_ARM64MULW

/-- `ARM64.rules:12`: `(Mul8 ...) => (MULW ...)` -/
theorem r_ARM64_12_3_sound : ArmRule.Checked r_ARM64_12_3 :=
  checked_setOp .Mul8 .ARM64MULW rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Mul8_ARM64MULW

/-- `ARM64.rules:43`: `(And16 ...) => (AND ...)` -/
theorem r_ARM64_43_sound : ArmRule.Checked r_ARM64_43 :=
  checked_setOp .And16 .ARM64AND rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_And16_ARM64AND

/-- `ARM64.rules:44`: `(Or16 ...) => (OR ...)` -/
theorem r_ARM64_44_sound : ArmRule.Checked r_ARM64_44 :=
  checked_setOp .Or16 .ARM64OR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Or16_ARM64OR

/-- `ARM64.rules:45`: `(Xor16 ...) => (XOR ...)` -/
theorem r_ARM64_45_sound : ArmRule.Checked r_ARM64_45 :=
  checked_setOp .Xor16 .ARM64XOR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Xor16_ARM64XOR

/-- `ARM64.rules:43`: `(And32 ...) => (AND ...)` -/
theorem r_ARM64_43_2_sound : ArmRule.Checked r_ARM64_43_2 :=
  checked_setOp .And32 .ARM64AND rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_And32_ARM64AND

/-- `ARM64.rules:44`: `(Or32 ...) => (OR ...)` -/
theorem r_ARM64_44_2_sound : ArmRule.Checked r_ARM64_44_2 :=
  checked_setOp .Or32 .ARM64OR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Or32_ARM64OR

/-- `ARM64.rules:45`: `(Xor32 ...) => (XOR ...)` -/
theorem r_ARM64_45_2_sound : ArmRule.Checked r_ARM64_45_2 :=
  checked_setOp .Xor32 .ARM64XOR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Xor32_ARM64XOR

/-- `ARM64.rules:43`: `(And64 ...) => (AND ...)` -/
theorem r_ARM64_43_3_sound : ArmRule.Checked r_ARM64_43_3 :=
  checked_setOp .And64 .ARM64AND rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_And64_ARM64AND

/-- `ARM64.rules:44`: `(Or64 ...) => (OR ...)` -/
theorem r_ARM64_44_3_sound : ArmRule.Checked r_ARM64_44_3 :=
  checked_setOp .Or64 .ARM64OR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Or64_ARM64OR

/-- `ARM64.rules:45`: `(Xor64 ...) => (XOR ...)` -/
theorem r_ARM64_45_3_sound : ArmRule.Checked r_ARM64_45_3 :=
  checked_setOp .Xor64 .ARM64XOR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Xor64_ARM64XOR

/-- `ARM64.rules:43`: `(And8 ...) => (AND ...)` -/
theorem r_ARM64_43_4_sound : ArmRule.Checked r_ARM64_43_4 :=
  checked_setOp .And8 .ARM64AND rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_And8_ARM64AND

/-- `ARM64.rules:44`: `(Or8 ...) => (OR ...)` -/
theorem r_ARM64_44_4_sound : ArmRule.Checked r_ARM64_44_4 :=
  checked_setOp .Or8 .ARM64OR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Or8_ARM64OR

/-- `ARM64.rules:45`: `(Xor8 ...) => (XOR ...)` -/
theorem r_ARM64_45_4_sound : ArmRule.Checked r_ARM64_45_4 :=
  checked_setOp .Xor8 .ARM64XOR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Xor8_ARM64XOR

/-- `ARM64.rules:48`: `(Neg16 ...) => (NEG ...)` -/
theorem r_ARM64_48_sound : ArmRule.Checked r_ARM64_48 :=
  checked_setOp .Neg16 .ARM64NEG rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Neg16_ARM64NEG

/-- `ARM64.rules:50`: `(Com16 ...) => (MVN ...)` -/
theorem r_ARM64_50_sound : ArmRule.Checked r_ARM64_50 :=
  checked_setOp .Com16 .ARM64MVN rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Com16_ARM64MVN

/-- `ARM64.rules:48`: `(Neg32 ...) => (NEG ...)` -/
theorem r_ARM64_48_2_sound : ArmRule.Checked r_ARM64_48_2 :=
  checked_setOp .Neg32 .ARM64NEG rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Neg32_ARM64NEG

/-- `ARM64.rules:50`: `(Com32 ...) => (MVN ...)` -/
theorem r_ARM64_50_2_sound : ArmRule.Checked r_ARM64_50_2 :=
  checked_setOp .Com32 .ARM64MVN rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Com32_ARM64MVN

/-- `ARM64.rules:48`: `(Neg64 ...) => (NEG ...)` -/
theorem r_ARM64_48_3_sound : ArmRule.Checked r_ARM64_48_3 :=
  checked_setOp .Neg64 .ARM64NEG rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Neg64_ARM64NEG

/-- `ARM64.rules:50`: `(Com64 ...) => (MVN ...)` -/
theorem r_ARM64_50_3_sound : ArmRule.Checked r_ARM64_50_3 :=
  checked_setOp .Com64 .ARM64MVN rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Com64_ARM64MVN

/-- `ARM64.rules:48`: `(Neg8 ...) => (NEG ...)` -/
theorem r_ARM64_48_4_sound : ArmRule.Checked r_ARM64_48_4 :=
  checked_setOp .Neg8 .ARM64NEG rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Neg8_ARM64NEG

/-- `ARM64.rules:50`: `(Com8 ...) => (MVN ...)` -/
theorem r_ARM64_50_4_sound : ArmRule.Checked r_ARM64_50_4 :=
  checked_setOp .Com8 .ARM64MVN rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Com8_ARM64MVN

/-- `CvtBoolToUint8` as `Copy` at its own shape `int8` (`topOKL`): the boolean's register read at
8 bits (`Val.widen`) is its 0/1 byte; any other argument makes `CvtBoolToUint8` `poison`. -/
private theorem s_CvtBoolToUint8_Copy : SetOpSound .CvtBoolToUint8 .Copy := by
  intro tabs ty ai ax args ht
  obtain rfl : ty = .int .w8 :=
    (show ∀ ty, topOKL .CvtBoolToUint8 ty = true → ty = .int .w8 by arm_top) ty ht
  have h1 : opValL tabs .CvtBoolToUint8 (.int .w8) ai ax args = Conv.boolToUint8 args := rfl
  rw [h1]
  by_cases hb : ∃ b, args = [.bool b]
  · obtain ⟨b, rfl⟩ := hb
    rw [show opValL tabs .Copy (.int .w8) ai ax [.bool b] = .bool b from rfl]
    cases b <;> exact Refines.refl _
  · have hp : Conv.boolToUint8 args = .poison := by
      match args, hb with
      | [a], hb => cases a <;> first | rfl | exact absurd ⟨_, rfl⟩ hb
      | [], _ => rfl
      | _ :: _ :: _, _ => rfl
    rw [hp, retypeL_poison]; exact .poison _

/-- `ARM64.rules:233`: `(CvtBoolToUint8 ...) => (Copy ...)` -/
theorem r_ARM64_233_sound : ArmRule.Checked r_ARM64_233 :=
  checked_setOp .CvtBoolToUint8 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_generic _ rfl rfl) s_CvtBoolToUint8_Copy

/-- `ARM64.rules:191`: `(Trunc16to8 ...) => (Copy ...)` -/
theorem r_ARM64_191_sound : ArmRule.Checked r_ARM64_191 :=
  checked_setOp .Trunc16to8 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc16to8_Copy

/-- `ARM64.rules:192`: `(Trunc32to8 ...) => (Copy ...)` -/
theorem r_ARM64_192_sound : ArmRule.Checked r_ARM64_192 :=
  checked_setOp .Trunc32to8 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc32to8_Copy

/-- `ARM64.rules:193`: `(Trunc32to16 ...) => (Copy ...)` -/
theorem r_ARM64_193_sound : ArmRule.Checked r_ARM64_193 :=
  checked_setOp .Trunc32to16 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc32to16_Copy

/-- `ARM64.rules:194`: `(Trunc64to8 ...) => (Copy ...)` -/
theorem r_ARM64_194_sound : ArmRule.Checked r_ARM64_194 :=
  checked_setOp .Trunc64to8 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc64to8_Copy

/-- `ARM64.rules:195`: `(Trunc64to16 ...) => (Copy ...)` -/
theorem r_ARM64_195_sound : ArmRule.Checked r_ARM64_195 :=
  checked_setOp .Trunc64to16 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc64to16_Copy

/-- `ARM64.rules:196`: `(Trunc64to32 ...) => (Copy ...)` -/
theorem r_ARM64_196_sound : ArmRule.Checked r_ARM64_196 :=
  checked_setOp .Trunc64to32 .Copy rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_generic _ rfl rfl)
    s_Trunc64to32_Copy

/-- `ARM64.rules:199`: `(ZeroExt8to16 ...) => (MOVBUreg ...)` -/
theorem r_ARM64_199_sound : ArmRule.Checked r_ARM64_199 :=
  checked_setOp .ZeroExt8to16 .ARM64MOVBUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt8to16_ARM64MOVBUreg

/-- `ARM64.rules:200`: `(ZeroExt8to32 ...) => (MOVBUreg ...)` -/
theorem r_ARM64_200_sound : ArmRule.Checked r_ARM64_200 :=
  checked_setOp .ZeroExt8to32 .ARM64MOVBUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt8to32_ARM64MOVBUreg

/-- `ARM64.rules:201`: `(ZeroExt16to32 ...) => (MOVHUreg ...)` -/
theorem r_ARM64_201_sound : ArmRule.Checked r_ARM64_201 :=
  checked_setOp .ZeroExt16to32 .ARM64MOVHUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt16to32_ARM64MOVHUreg

/-- `ARM64.rules:202`: `(ZeroExt8to64 ...) => (MOVBUreg ...)` -/
theorem r_ARM64_202_sound : ArmRule.Checked r_ARM64_202 :=
  checked_setOp .ZeroExt8to64 .ARM64MOVBUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt8to64_ARM64MOVBUreg

/-- `ARM64.rules:203`: `(ZeroExt16to64 ...) => (MOVHUreg ...)` -/
theorem r_ARM64_203_sound : ArmRule.Checked r_ARM64_203 :=
  checked_setOp .ZeroExt16to64 .ARM64MOVHUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt16to64_ARM64MOVHUreg

/-- `ARM64.rules:204`: `(ZeroExt32to64 ...) => (MOVWUreg ...)` -/
theorem r_ARM64_204_sound : ArmRule.Checked r_ARM64_204 :=
  checked_setOp .ZeroExt32to64 .ARM64MOVWUreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_ZeroExt32to64_ARM64MOVWUreg

/-- `ARM64.rules:206`: `(SignExt8to16 ...) => (MOVBreg ...)` -/
theorem r_ARM64_206_sound : ArmRule.Checked r_ARM64_206 :=
  checked_setOp .SignExt8to16 .ARM64MOVBreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt8to16_ARM64MOVBreg

/-- `ARM64.rules:207`: `(SignExt8to32 ...) => (MOVBreg ...)` -/
theorem r_ARM64_207_sound : ArmRule.Checked r_ARM64_207 :=
  checked_setOp .SignExt8to32 .ARM64MOVBreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt8to32_ARM64MOVBreg

/-- `ARM64.rules:208`: `(SignExt16to32 ...) => (MOVHreg ...)` -/
theorem r_ARM64_208_sound : ArmRule.Checked r_ARM64_208 :=
  checked_setOp .SignExt16to32 .ARM64MOVHreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt16to32_ARM64MOVHreg

/-- `ARM64.rules:209`: `(SignExt8to64 ...) => (MOVBreg ...)` -/
theorem r_ARM64_209_sound : ArmRule.Checked r_ARM64_209 :=
  checked_setOp .SignExt8to64 .ARM64MOVBreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt8to64_ARM64MOVBreg

/-- `ARM64.rules:210`: `(SignExt16to64 ...) => (MOVHreg ...)` -/
theorem r_ARM64_210_sound : ArmRule.Checked r_ARM64_210 :=
  checked_setOp .SignExt16to64 .ARM64MOVHreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt16to64_ARM64MOVHreg

/-- `ARM64.rules:211`: `(SignExt32to64 ...) => (MOVWreg ...)` -/
theorem r_ARM64_211_sound : ArmRule.Checked r_ARM64_211 :=
  checked_setOp .SignExt32to64 .ARM64MOVWreg rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_SignExt32to64_ARM64MOVWreg

/-- `ARM64.rules:108`: `(Bswap64 ...) => (REV ...)` -/
theorem r_ARM64_108_sound : ArmRule.Checked r_ARM64_108 :=
  checked_setOp .Bswap64 .ARM64REV rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Bswap64_ARM64REV

/-- `ARM64.rules:109`: `(Bswap32 ...) => (REVW ...)` -/
theorem r_ARM64_109_sound : ArmRule.Checked r_ARM64_109 :=
  checked_setOp .Bswap32 .ARM64REVW rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_Bswap32_ARM64REVW

/-- `ARM64.rules:110`: `(Bswap16 ...) => (REV16W ...)` -/
theorem r_ARM64_110_sound : ArmRule.Checked r_ARM64_110 :=
  checked_setOp .Bswap16 .ARM64REV16W rfl rfl rfl rfl (termVL_generic _ rfl rfl)
    (termVL_arm _ rfl rfl rfl) s_Bswap16_ARM64REV16W

end GoFV.Proof.Low.Rules
