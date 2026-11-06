import GoFV.Proof.Low.Rules.BlockFlags

/-!
# Lowering rule lemmas: `InvertFlags` (`ARM64.rules:991`, `993`, `1003`, `1374-1383`)

`InvertFlags f` is the flags of the compare with swapped operands (`Sem.invertFlags`, from the
fifth flags component `g`, the sign of the negated difference, which only `InvertFlags` reads):

* `(CMP x y) && canonLessThan(x,y) => (InvertFlags (CMP y x))` (`1003`, and `CMPW`), `(CMP
  (MOVDconst [c]) x) => (InvertFlags (CMPconst [c] x))` (`991`, and `CMPW`, `993`): `InvertFlags`
  of the swapped compare is the compare itself, value for value (`invertFlags_cmp`,
  `invertFlags_cmp2w`, both from `invertFlags_sub`).
* `(Equal (InvertFlags x)) => (Equal x)`, `(LessThan (InvertFlags x)) => (GreaterThan x)`, … on
  the integer conditions (`1374-1383`): the condition on `InvertFlags x` is the swapped one on `x`,
  whatever `x` (`invertFlags_cond`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- A 64-bit compare's flags are at the flags shape. -/
theorem retypeL_flags_cmp (a b : Val) : (Arm64.cmp a b).retypeL Ty.flags = Arm64.cmp a b := by
  unfold Arm64.cmp
  split
  · rfl
  · split
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · rfl

/-- A 32-bit compare's flags are at the flags shape. -/
theorem retypeL_flags_cmp2w (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (as : List Val) :
    (Arm64.cmp2w f as).retypeL Ty.flags = Arm64.cmp2w f as := by
  unfold Arm64.cmp2w
  split
  · split <;> rfl
  · rfl

/-- A 32-bit compare with an immediate: its flags are at the flags shape. -/
theorem retypeL_flags_cmp1w (f : BitVec 32 → BitVec 32 × Flags) (as : List Val) :
    (Arm64.cmp1w f as).retypeL Ty.flags = Arm64.cmp1w f as := by
  unfold Arm64.cmp1w
  split
  · split <;> rfl
  · rfl

theorem invertFlags_poison : invertFlags .poison = .poison := rfl

/-- **`InvertFlags (CMP b a)` is `CMP a b`**, on registers and on pointers alike. -/
theorem invertFlags_cmp (a b : Val) : invertFlags (Arm64.cmp b a) = Arm64.cmp a b := by
  have key : ∀ x y : BitVec 64, invertFlags (Arm64.cmpRes (Arm64.subFlags y x)) =
      Arm64.cmpRes (Arm64.subFlags x y) := fun x y =>
    invertFlags_sub x y (sub_lt64 x y) (sub_lt64 y x)
  have hp : invertFlags (.agg [.poison, .bool false, .poison, .poison, .poison]) =
      .agg [.poison, .bool false, .poison, .poison, .poison] := rfl
  have hP := invertFlags_poison
  unfold Arm64.cmp
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b
  case some.some x y => exact key x y
  all_goals
    cases a <;> cases b <;> simp only [Arm64.reg] at ha hb <;> simp_all
  all_goals (try split) <;> (try split) <;> simp_all

/-- **`InvertFlags (CMPW b a)` is `CMPW a b`.** -/
theorem invertFlags_cmp2w (a b : Val) :
    invertFlags (Arm64.cmp2w (fun x y => Arm64.subFlags x y) [b, a]) =
      Arm64.cmp2w (fun x y => Arm64.subFlags x y) [a, b] := by
  simp only [Arm64.cmp2w]
  cases ha : Arm64.reg32 a <;> cases hb : Arm64.reg32 b
  case some.some x y => exact invertFlags_sub x y (sub_lt32 x y) (sub_lt32 y x)
  all_goals rfl

/-- `InvertFlags (CMPWconst [k] a)` is `CMPW b a` for `b` a register holding `k`. -/
theorem invertFlags_cmp1w {k : BitVec 32} (a b : Val) (hb : Arm64.reg32 b = some k) :
    invertFlags (Arm64.cmp1w (fun x => Arm64.subFlags x k) [a]) =
      Arm64.cmp2w (fun x y => Arm64.subFlags x y) [b, a] := by
  simp only [Arm64.cmp1w, Arm64.cmp2w, hb]
  cases ha : Arm64.reg32 a
  · rfl
  · exact invertFlags_sub _ _ (sub_lt32 _ _) (sub_lt32 _ _)

theorem cmp_poison_left (b : Val) : Arm64.cmp .poison b = .poison := by
  cases b <;> simp [Arm64.cmp, Arm64.reg]

theorem cmp2w_poison_left (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (b : Val) :
    Arm64.cmp2w f [.poison, b] = .poison := by
  simp [Arm64.cmp2w, Arm64.reg32, Arm64.reg]

/-- `CSET` of an integer condition on `InvertFlags f` is `CSET` of the swapped condition on `f`. -/
theorem refines_cset_invert {op op' : Op} {c c' : Cond} (hop : Cond.ofOp op = some c)
    (hop' : Cond.ofOp op' = some c') (hs : c.swapInt = some c') (T T0 : Ty) (f : Val) :
    Refines ((Arm64.cset T op [(invertFlags f).retypeL T0]).retypeL T)
      ((Arm64.cset T op' [f]).retypeL T) := by
  simp only [Arm64.cset, hop, hop', Option.bind_some]
  cases h : c.onVal ((invertFlags f).retypeL T0) with
  | none => rw [retypeL_poison]; exact .poison _
  | some b =>
    rw [invertFlags_cond hs (Mono.onVal_of (retypeL_invertFlags_ref _ _) h)]
    exact Refines.refl _

/-- `ARM64.rules:1003`: `(CMP x y) && canonLessThan(x,y) => (InvertFlags (CMP y x))` -/
theorem r_ARM64_1003_sound : ArmRule.Checked r_ARM64_1003 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp, invertFlags_cmp]; exact Refines.refl _

/-- `ARM64.rules:1003`: `(CMPW x y) && canonLessThan(x,y) => (InvertFlags (CMPW y x))` -/
theorem r_ARM64_1003_2_sound : ArmRule.Checked r_ARM64_1003_2 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp2w, invertFlags_cmp2w]; exact Refines.refl _

/-- `ARM64.rules:991`: `(CMP (MOVDconst [c]) x) => (InvertFlags (CMPconst [c] x))` -/
theorem r_ARM64_991_sound : ArmRule.Checked r_ARM64_991 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp, invertFlags_cmp]
  rcases retypeL_res_wide harg.1 (BitVec.ofInt 64 (e.auxInt [0]).toInt) with h | h <;> rw [h]
  · exact Refines.refl _
  · rw [cmp_poison_left, retypeL_poison]; exact .poison _

/-- `ARM64.rules:993`: `(CMPW (MOVDconst [c]) x) => (InvertFlags (CMPWconst [int32(c)] x))` -/
theorem r_ARM64_993_sound : ArmRule.Checked r_ARM64_993 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp1w]
  rcases retypeL_res_w32 harg.1 (BitVec.ofInt 64 (e.auxInt [0]).toInt) with h | h
  · rw [setWidth_ofInt_le (by decide)] at h
    rw [imm32_wrap, invertFlags_cmp1w _ _ h]
    exact Refines.refl _
  · rw [h, cmp2w_poison_left, retypeL_poison]; exact .poison _

/-- `ARM64.rules:1374`: `(Equal (InvertFlags x)) => (Equal x)` -/
theorem r_ARM64_1374_sound : ArmRule.Checked r_ARM64_1374 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1375`: `(NotEqual (InvertFlags x)) => (NotEqual x)` -/
theorem r_ARM64_1375_sound : ArmRule.Checked r_ARM64_1375 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1376`: `(LessThan (InvertFlags x)) => (GreaterThan x)` -/
theorem r_ARM64_1376_sound : ArmRule.Checked r_ARM64_1376 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1377`: `(LessThanU (InvertFlags x)) => (GreaterThanU x)` -/
theorem r_ARM64_1377_sound : ArmRule.Checked r_ARM64_1377 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1378`: `(GreaterThan (InvertFlags x)) => (LessThan x)` -/
theorem r_ARM64_1378_sound : ArmRule.Checked r_ARM64_1378 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1379`: `(GreaterThanU (InvertFlags x)) => (LessThanU x)` -/
theorem r_ARM64_1379_sound : ArmRule.Checked r_ARM64_1379 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1380`: `(LessEqual (InvertFlags x)) => (GreaterEqual x)` -/
theorem r_ARM64_1380_sound : ArmRule.Checked r_ARM64_1380 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1381`: `(LessEqualU (InvertFlags x)) => (GreaterEqualU x)` -/
theorem r_ARM64_1381_sound : ArmRule.Checked r_ARM64_1381 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1382`: `(GreaterEqual (InvertFlags x)) => (LessEqual x)` -/
theorem r_ARM64_1382_sound : ArmRule.Checked r_ARM64_1382 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1383`: `(GreaterEqualU (InvertFlags x)) => (LessEqualU x)` -/
theorem r_ARM64_1383_sound : ArmRule.Checked r_ARM64_1383 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

end GoFV.Proof.Low.Rules
