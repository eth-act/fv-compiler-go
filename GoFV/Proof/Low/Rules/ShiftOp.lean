import GoFV.Proof.Low.Rules.Peep

/-!
# Lowering rule lemmas: shifted and inverted operands of bitwise ops (`ARM64.rules:1179-1182`, `1439-1449`)

Peepholes of lowered code (#385) that fold an operand's producer into a bitwise op:

* `(AND|OR|XOR x0 x1:(SLLconst|SRLconst|SRAconst|RORconst [c] y)) && clobberIfDead(x1) =>
  (ANDshift..|ORshift..|XORshift.. x0 y [c])` (1439-1449, both argument orders) and
  `(AND|XOR|OR x (MVN y)) => (BIC|EON|ORN x y)` (1179-1181): the result is read at its low `lowW`
  bits, which only the low `lowW` bits of the folded operand decide; the operand's register read
  at its own shape keeps at least those bits (`armReadW` of the bitwise op, `harg`), so the folded
  form computes the same low bits from the producer's input (`refines_op2_op1`).
* `(MVN (XOR x y)) => (EON x y)` (1182): likewise for the inverted result (`refines_op1_op2`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

private theorem op2_poison_r (T : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (x : Val) :
    Arm64.op2 T f [x, .poison] = .poison := by
  cases hx : Arm64.reg x <;> simp only [Arm64.op2, hx, show Arm64.reg .poison = none from rfl]

private theorem op2_swap (T : Ty) {f : BitVec 64 → BitVec 64 → BitVec 64}
    (hc : ∀ a b, f a b = f b a) (a b : Val) : Arm64.op2 T f [a, b] = Arm64.op2 T f [b, a] := by
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b <;> simp only [Arm64.op2, ha, hb, hc]

/-- A binary op on `x` and an operand `g y` (computed at shape `T1`, read back there): the op on
`x` and `y` with `g` folded in, as far as the low `lowW T` bits of the result go. -/
theorem refines_op2_op1 {T T1 : Ty} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (g : BitVec 64 → BitVec 64)
    (hfl : ∀ a b b', b.setWidth (lowW T) = b'.setWidth (lowW T) →
      (f a b).setWidth (lowW T) = (f a b').setWidth (lowW T))
    (hw : lowW T ≤ argWidth T1) (x y : Val) :
    Refines ((Arm64.op2 T f [x, (Arm64.op1 T1 g [y]).retypeL T1]).retypeL T)
      ((Arm64.op2 T (fun a b => f a (g b)) [x, y]).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  cases hy : Arm64.reg y with
  | none =>
    have : Arm64.op1 T1 g [y] = .poison := by simp only [Arm64.op1, hy]
    rw [this, retypeL_poison, op2_poison_r, retypeL_poison]; exact .poison _
  | some v =>
    have : Arm64.op1 T1 g [y] = Arm64.res T1 (g v) := by simp only [Arm64.op1, hy]
    rw [this]
    rcases retypeL_res_reg h1 h2 hw (g v) with h | ⟨z, hz, hzk⟩
    · rw [h, op2_poison_r, retypeL_poison]; exact .poison _
    · cases hx : Arm64.reg x with
      | none => simp only [Arm64.op2, hx, retypeL_poison]; exact .poison _
      | some u =>
        simp only [Arm64.op2, hx, hy, hz]
        rw [retypeL_res_low T (hfl u z (g v) hzk)]
        exact Refines.refl _

/-- `refines_op2_op1` with the folded operand first (a commutative op). -/
theorem refines_op2_op1_swap {T T1 : Ty} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (g : BitVec 64 → BitVec 64) (hc : ∀ a b, f a b = f b a)
    (hfl : ∀ a b b', b.setWidth (lowW T) = b'.setWidth (lowW T) →
      (f a b).setWidth (lowW T) = (f a b').setWidth (lowW T))
    (hw : lowW T ≤ argWidth T1) (x y : Val) :
    Refines ((Arm64.op2 T f [(Arm64.op1 T1 g [y]).retypeL T1, x]).retypeL T)
      ((Arm64.op2 T (fun a b => f a (g b)) [x, y]).retypeL T) := by
  rw [op2_swap T hc]
  exact refines_op2_op1 f g hfl hw x y

/-- A unary op on a binary op's result (computed at shape `T1`, read back there): the composite
on the operands, as far as the low `lowW T` bits of the result go. -/
theorem refines_op1_op2 {T T1 : Ty} (h : BitVec 64 → BitVec 64)
    (f : BitVec 64 → BitVec 64 → BitVec 64)
    (hfl : ∀ b b', b.setWidth (lowW T) = b'.setWidth (lowW T) →
      (h b).setWidth (lowW T) = (h b').setWidth (lowW T))
    (hw : lowW T ≤ argWidth T1) (x y : Val) :
    Refines ((Arm64.op1 T h [(Arm64.op2 T1 f [x, y]).retypeL T1]).retypeL T)
      ((Arm64.op2 T (fun a b => h (f a b)) [x, y]).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  cases hx : Arm64.reg x with
  | none =>
    have : Arm64.op2 T1 f [x, y] = .poison := by simp only [Arm64.op2, hx]
    rw [this, retypeL_poison]
    simp only [Arm64.op1, show Arm64.reg .poison = none from rfl, retypeL_poison]
    exact .poison _
  | some u =>
    cases hy : Arm64.reg y with
    | none =>
      have : Arm64.op2 T1 f [x, y] = .poison := by simp only [Arm64.op2, hx, hy]
      rw [this, retypeL_poison]
      simp only [Arm64.op1, show Arm64.reg .poison = none from rfl, retypeL_poison]
      exact .poison _
    | some v =>
      have : Arm64.op2 T1 f [x, y] = Arm64.res T1 (f u v) := by simp only [Arm64.op2, hx, hy]
      rw [this]
      rcases retypeL_res_reg h1 h2 hw (f u v) with e | ⟨z, hz, hzk⟩
      · rw [e]
        simp only [Arm64.op1, show Arm64.reg .poison = none from rfl, retypeL_poison]
        exact .poison _
      · simp only [Arm64.op1, Arm64.op2, hx, hy, hz]
        rw [retypeL_res_low T (hfl z (f u v) hzk)]
        exact Refines.refl _

private theorem and_low (n : Nat) (a b b' : BitVec 64) (h : b.setWidth n = b'.setWidth n) :
    (a &&& b).setWidth n = (a &&& b').setWidth n := by simp only [BitVec.setWidth_and, h]

private theorem or_low (n : Nat) (a b b' : BitVec 64) (h : b.setWidth n = b'.setWidth n) :
    (a ||| b).setWidth n = (a ||| b').setWidth n := by simp only [BitVec.setWidth_or, h]

private theorem xor_low (n : Nat) (a b b' : BitVec 64) (h : b.setWidth n = b'.setWidth n) :
    (a ^^^ b).setWidth n = (a ^^^ b').setWidth n := by simp only [BitVec.setWidth_xor, h]

private theorem not_low (n : Nat) (b b' : BitVec 64) (h : b.setWidth n = b'.setWidth n) :
    (~~~b).setWidth n = (~~~b').setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have e := congrArg (fun v : BitVec n => v.getLsbD i) h
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] at e
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_not, hi, decide_true, Bool.true_and, e]

/-- The shifted-register forms with the auxint read back from the rule's `Int64`. -/
private theorem opSh_eq (T : Ty) (sh : Arm64.Shift) (k : Int64)
    (f : BitVec 64 → BitVec 64 → BitVec 64) (args : List Val) :
    Arm64.opSh T sh (Int64.ofInt k.toInt) f args =
      Arm64.op2 T (fun a b => f a (sh.apply b (Arm64.amt k))) args := by
  simp only [Arm64.opSh, Arm64.shifted, Int64.ofInt_toInt]

/-- `ARM64.rules:1439`: `(AND x0 x1:(SLLconst [c] y)) && clobberIfDead(x1) => (ANDshiftLL x0 y [c])` -/
theorem r_ARM64_1439_sound : ArmRule.Checked r_ARM64_1439 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.and_comm (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1440`: `(AND x0 x1:(SRLconst [c] y)) && clobberIfDead(x1) => (ANDshiftRL x0 y [c])` -/
theorem r_ARM64_1440_sound : ArmRule.Checked r_ARM64_1440 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.and_comm (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1441`: `(AND x0 x1:(SRAconst [c] y)) && clobberIfDead(x1) => (ANDshiftRA x0 y [c])` -/
theorem r_ARM64_1441_sound : ArmRule.Checked r_ARM64_1441 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.and_comm (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1442`: `(AND x0 x1:(RORconst [c] y)) && clobberIfDead(x1) => (ANDshiftRO x0 y [c])` -/
theorem r_ARM64_1442_sound : ArmRule.Checked r_ARM64_1442 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.and_comm (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1443`: `(OR x0 x1:(SLLconst [c] y)) && clobberIfDead(x1) => (ORshiftLL x0 y [c])` -/
theorem r_ARM64_1443_sound : ArmRule.Checked r_ARM64_1443 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.or_comm (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1444`: `(OR x0 x1:(SRLconst [c] y)) && clobberIfDead(x1) => (ORshiftRL x0 y [c])` -/
theorem r_ARM64_1444_sound : ArmRule.Checked r_ARM64_1444 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.or_comm (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1445`: `(OR x0 x1:(SRAconst [c] y)) && clobberIfDead(x1) => (ORshiftRA x0 y [c])` -/
theorem r_ARM64_1445_sound : ArmRule.Checked r_ARM64_1445 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.or_comm (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1446`: `(OR x0 x1:(RORconst [c] y)) && clobberIfDead(x1) => (ORshiftRO x0 y [c])` -/
theorem r_ARM64_1446_sound : ArmRule.Checked r_ARM64_1446 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.or_comm (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1447`: `(XOR x0 x1:(SLLconst [c] y)) && clobberIfDead(x1) => (XORshiftLL x0 y [c])` -/
theorem r_ARM64_1447_sound : ArmRule.Checked r_ARM64_1447 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.xor_comm (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1448`: `(XOR x0 x1:(SRLconst [c] y)) && clobberIfDead(x1) => (XORshiftRL x0 y [c])` -/
theorem r_ARM64_1448_sound : ArmRule.Checked r_ARM64_1448 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.xor_comm (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1449`: `(XOR x0 x1:(SRAconst [c] y)) && clobberIfDead(x1) => (XORshiftRA x0 y [c])` -/
theorem r_ARM64_1449_sound : ArmRule.Checked r_ARM64_1449 := by
  left; arm_unfold
  all_goals arm_norm
  all_goals simp only [opSh_eq]
  · exact refines_op2_op1 _ _ (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.xor_comm (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1179`: `(AND x (MVN y)) => (BIC x y)` -/
theorem r_ARM64_1179_sound : ArmRule.Checked r_ARM64_1179 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_op2_op1 _ _ (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.and_comm (fun a b b' h => and_low _ a b b' h)
      (armReadW_low .ARM64AND _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1180`: `(XOR x (MVN y)) => (EON x y)` -/
theorem r_ARM64_1180_sound : ArmRule.Checked r_ARM64_1180 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_op2_op1 _ _ (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.xor_comm (fun a b b' h => xor_low _ a b b' h)
      (armReadW_low .ARM64XOR _ 0 (by simp) ▸ harg.1.1) _ _

/-- `ARM64.rules:1181`: `(OR x (MVN y)) => (ORN x y)` -/
theorem r_ARM64_1181_sound : ArmRule.Checked r_ARM64_1181 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_op2_op1 _ _ (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 1 (by simp) ▸ harg.2.1) _ _
  · exact refines_op2_op1_swap _ _ BitVec.or_comm (fun a b b' h => or_low _ a b b' h)
      (armReadW_low .ARM64OR _ 0 (by simp) ▸ harg.1.1) _ _

private theorem armReadW_mvn (T : Ty) : armReadW .ARM64MVN T 0 = lowW T := by
  cases T <;> rfl

private theorem eon_eq : (fun a b : BitVec 64 => a ^^^ ~~~b) = fun a b => ~~~(a ^^^ b) := by
  funext a b; rw [BitVec.not_xor_right]

/-- `ARM64.rules:1182`: `(MVN (XOR x y)) => (EON x y)` -/
theorem r_ARM64_1182_sound : ArmRule.Checked r_ARM64_1182 := by
  left; arm_unfold
  arm_norm
  rw [eon_eq]
  exact refines_op1_op2 _ _ (fun b b' h => not_low _ b b' h) (armReadW_mvn _ ▸ harg.1) _ _

end GoFV.Proof.Low.Rules
