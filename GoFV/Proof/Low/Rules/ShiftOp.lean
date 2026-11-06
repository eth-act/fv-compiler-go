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

/-! ## `ADD`/`SUB` with a shifted operand -/

private theorem add_low {n : Nat} (hn : n ≤ 64) (a b b' : BitVec 64)
    (h : b.setWidth n = b'.setWidth n) : (a + b).setWidth n = (a + b').setWidth n := by
  rw [BitVec.setWidth_add _ _ hn, BitVec.setWidth_add _ _ hn, h]

private theorem sub_low {n : Nat} (hn : n ≤ 64) (a b b' : BitVec 64)
    (h : b.setWidth n = b'.setWidth n) : (a - b).setWidth n = (a - b').setWidth n := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ hn,
    BitVec.setWidth_add _ _ hn, BitVec.setWidth_neg_of_le hn, BitVec.setWidth_neg_of_le hn, h]

/-- A register result read at its shape is never a pointer. -/
private theorem retypeL_res_nonptr (T : Ty) (r : BitVec 64) (p : Ptr) :
    (Arm64.res T r).retypeL T ≠ .ptr p := by
  intro h
  cases T with
  | int w => rw [retypeL_res_int] at h; cases h
  | bool => cases h
  | ptr el => cases h
  | _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype] at h

private theorem retypeL_op1_nonptr (T : Ty) (g : BitVec 64 → BitVec 64) (y : Val) (p : Ptr) :
    (Arm64.op1 T g [y]).retypeL T ≠ .ptr p := by
  cases hy : Arm64.reg y <;> simp only [Arm64.op1, hy, retypeL_poison, ne_eq, reduceCtorEq,
    not_false_eq_true, retypeL_res_nonptr]

private theorem retypeL_op2w_nonptr (T : Ty) (g : BitVec 32 → BitVec 32 → BitVec 32) (a b : Val)
    (p : Ptr) : (Arm64.op2w T g [a, b]).retypeL T ≠ .ptr p := by
  cases ha : Arm64.reg32 a <;> cases hb : Arm64.reg32 b <;>
    simp only [Arm64.op2w, Arm64.res32, ha, hb, retypeL_poison, ne_eq, reduceCtorEq,
      not_false_eq_true, retypeL_res_nonptr]

private theorem add_nonptr (T : Ty) {x v : Val} (hx : ∀ p, x ≠ .ptr p) (hv : ∀ p, v ≠ .ptr p) :
    Arm64.add T [x, v] = Arm64.op2 T (· + ·) [x, v] := by
  cases x <;> cases v <;> first | rfl | exact absurd rfl (hx _) | exact absurd rfl (hv _)

private theorem sub_nonptr (T : Ty) {x v : Val} (hx : ∀ p, x ≠ .ptr p) :
    Arm64.sub T [x, v] = Arm64.op2 T (· - ·) [x, v] := by
  cases x <;> first | rfl | exact absurd rfl (hx _)

private theorem addP_nonptr (T : Ty) {x : Val} (hx : ∀ p, x ≠ .ptr p) (k : BitVec 64) :
    Arm64.addP T x k = match Arm64.reg x with
      | some a => Arm64.res T (a + k)
      | none => .poison := by
  cases x <;> first | rfl | exact absurd rfl (hx _)

private theorem addSh_nonptr (T : Ty) (sh : Arm64.Shift) (k : Int64) {x : Val}
    (hx : ∀ p, x ≠ .ptr p) (y : Val) :
    Arm64.addSh T sh k [x, y] = Arm64.op2 T (fun a b => a + sh.apply b (Arm64.amt k)) [x, y] := by
  cases hy : Arm64.reg y <;> cases hr : Arm64.reg x <;>
    simp only [Arm64.addSh, Arm64.op2, Arm64.shifted, hy, hr, addP_nonptr T hx]

private theorem subSh_nonptr (T : Ty) (sh : Arm64.Shift) (k : Int64) {x : Val}
    (hx : ∀ p, x ≠ .ptr p) (y : Val) :
    Arm64.subSh T sh k [x, y] = Arm64.op2 T (fun a b => a - sh.apply b (Arm64.amt k)) [x, y] := by
  cases hy : Arm64.reg y <;> cases hr : Arm64.reg x <;>
    simp only [Arm64.subSh, Arm64.op2, Arm64.shifted, hy, hr, addP_nonptr T hx,
      BitVec.sub_eq_add_neg]

/-- A pointer of shape `T0` (`hasTy`): `T0` is a word shape. -/
private theorem wordShape_of_ptr {p : Ptr} {T0 : Ty} (h : (Val.ptr p).hasTy T0 = true) :
    wordShape T0 = true := by
  cases T0 with
  | int w => cases w <;> simp_all [Val.hasTy, wordShape]
  | ptr _ => rfl
  | _ => simp [Val.hasTy] at h

private theorem lowW_word {T : Ty} (h : wordShape T = true) : lowW T = 64 := by
  cases T with
  | int w => cases w <;> simp_all [wordShape, lowW, Width.bits]
  | ptr _ => rfl
  | _ => simp [wordShape] at h

/-- `ADD x (g y)` (the shifted operand computed at shape `T1`) as `ADDshift x y` (`Arm64.addSh`):
a pointer `x` has a word shape `T0`, so the result has a word shape (`hp`, the validator's
provenance clause) and the operand is read whole; otherwise only the low `lowW T` bits count. -/
theorem refines_addSh {T T0 T1 : Ty} (sh : Arm64.Shift) (k : Int64)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (x y : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.add T [x, (Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1]).retypeL T)
      ((Arm64.addSh T sh (Int64.ofInt k.toInt) [x, y]).retypeL T) := by
  rw [Int64.ofInt_toInt]
  by_cases hxp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hxp
    have hT : wordShape T = true := by
      have := wordShape_of_ptr hx
      rcases hp with h | h
      · simp [this] at h
      · exact h
    have h64 : 64 ≤ argWidth T1 := lowW_word hT ▸ hw
    cases hy : Arm64.reg y with
    | none =>
      simp only [Arm64.op1, Arm64.addSh, hy, retypeL_poison]
      simp only [Arm64.add, show Arm64.reg .poison = none from rfl, retypeL_poison]
      exact .poison _
    | some v =>
      simp only [Arm64.op1, hy]
      rcases retypeL_res_wide h64 (sh.apply v (Arm64.amt k)) with h | h <;> rw [h]
      · simp only [Arm64.addSh, Arm64.addP, Arm64.shifted, hy]
        simp only [Arm64.add, Arm64.reg, BitVec.setWidth_eq]
        exact Refines.refl _
      · simp only [Arm64.add, show Arm64.reg .poison = none from rfl, retypeL_poison]
        exact .poison _
  · have hx' : ∀ p, x ≠ .ptr p := fun p h => hxp ⟨p, h⟩
    rw [add_nonptr T hx' (retypeL_op1_nonptr T1 _ y), addSh_nonptr T sh k hx']
    exact refines_op2_op1 (· + ·) _ (fun a b b' h => add_low (lowW_pos T).2 a b b' h) hw x y

/-- `refines_addSh` with the shifted operand first. -/
theorem refines_addSh_swap {T T0 T1 : Ty} (sh : Arm64.Shift) (k : Int64)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (x y : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.add T [(Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1, x]).retypeL T)
      ((Arm64.addSh T sh (Int64.ofInt k.toInt) [x, y]).retypeL T) := by
  have hc : Arm64.add T [(Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1, x] =
      Arm64.add T [x, (Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1] := by
    have hv := retypeL_op1_nonptr T1 (fun b => sh.apply b (Arm64.amt k)) y
    generalize (Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1 = v at hv ⊢
    cases x with
    | ptr p => cases v <;> first | rfl | exact absurd rfl (hv _)
    | _ =>
      rw [add_nonptr T (fun p h => by cases h) hv, add_nonptr T hv (fun p h => by cases h)]
      exact op2_swap T (fun a b => BitVec.add_comm a b) _ _
  rw [hc]
  exact refines_addSh sh k hw hp x y hx

/-- `SUB x (g y)` as `SUBshift x y` (`Arm64.subSh`), as `refines_addSh`. -/
theorem refines_subSh {T T0 T1 : Ty} (sh : Arm64.Shift) (k : Int64)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (x y : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.sub T [x, (Arm64.op1 T1 (fun b => sh.apply b (Arm64.amt k)) [y]).retypeL T1]).retypeL T)
      ((Arm64.subSh T sh (Int64.ofInt k.toInt) [x, y]).retypeL T) := by
  rw [Int64.ofInt_toInt]
  by_cases hxp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hxp
    have hT : wordShape T = true := by
      have := wordShape_of_ptr hx
      rcases hp with h | h
      · simp [this] at h
      · exact h
    have h64 : 64 ≤ argWidth T1 := lowW_word hT ▸ hw
    cases hy : Arm64.reg y with
    | none =>
      simp only [Arm64.op1, Arm64.subSh, hy, retypeL_poison]
      simp only [Arm64.sub, show Arm64.reg .poison = none from rfl, retypeL_poison]
      exact .poison _
    | some v =>
      simp only [Arm64.op1, hy]
      rcases retypeL_res_wide h64 (sh.apply v (Arm64.amt k)) with h | h <;> rw [h]
      · simp only [Arm64.subSh, Arm64.addP, Arm64.shifted, hy]
        simp only [Arm64.sub, Arm64.reg, BitVec.setWidth_eq]
        exact Refines.refl _
      · simp only [Arm64.sub, show Arm64.reg .poison = none from rfl, retypeL_poison]
        exact .poison _
  · have hx' : ∀ p, x ≠ .ptr p := fun p h => hxp ⟨p, h⟩
    rw [sub_nonptr T hx', subSh_nonptr T sh k hx']
    exact refines_op2_op1 (· - ·) _ (fun a b b' h => sub_low (lowW_pos T).2 a b b' h) hw x y

private theorem armReadW_addSub (o : Op) (T : Ty) (i : Nat)
    (ho : o = .ARM64ADD ∨ o = .ARM64SUB) : armReadW o T i = lowW T := by
  rcases ho with rfl | rfl <;> cases T <;> rfl

/-- `ARM64.rules:1433`: `(ADD x0 x1:(SLLconst [c] y)) && clobberIfDead(x1) => (ADDshiftLL x0 y [c])` -/
theorem r_ARM64_1433_sound : ArmRule.Checked r_ARM64_1433 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_addSh .ll _ (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2
      _ _ hty.1
  · exact refines_addSh_swap .ll _ (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1)
      harg.2.2 _ _ hty.2

/-- `ARM64.rules:1434`: `(ADD x0 x1:(SRLconst [c] y)) && clobberIfDead(x1) => (ADDshiftRL x0 y [c])` -/
theorem r_ARM64_1434_sound : ArmRule.Checked r_ARM64_1434 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_addSh .rl _ (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2
      _ _ hty.1
  · exact refines_addSh_swap .rl _ (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1)
      harg.2.2 _ _ hty.2

/-- `ARM64.rules:1435`: `(ADD x0 x1:(SRAconst [c] y)) && clobberIfDead(x1) => (ADDshiftRA x0 y [c])` -/
theorem r_ARM64_1435_sound : ArmRule.Checked r_ARM64_1435 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_addSh .ra _ (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2
      _ _ hty.1
  · exact refines_addSh_swap .ra _ (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1)
      harg.2.2 _ _ hty.2

/-- `ARM64.rules:1436`: `(SUB x0 x1:(SLLconst [c] y)) && clobberIfDead(x1) => (SUBshiftLL x0 y [c])` -/
theorem r_ARM64_1436_sound : ArmRule.Checked r_ARM64_1436 := by
  left; arm_unfold; arm_norm
  exact refines_subSh .ll _ (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2
    _ _ hty.1

/-- `ARM64.rules:1437`: `(SUB x0 x1:(SRLconst [c] y)) && clobberIfDead(x1) => (SUBshiftRL x0 y [c])` -/
theorem r_ARM64_1437_sound : ArmRule.Checked r_ARM64_1437 := by
  left; arm_unfold; arm_norm
  exact refines_subSh .rl _ (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2
    _ _ hty.1

/-- `ARM64.rules:1438`: `(SUB x0 x1:(SRAconst [c] y)) && clobberIfDead(x1) => (SUBshiftRA x0 y [c])` -/
theorem r_ARM64_1438_sound : ArmRule.Checked r_ARM64_1438 := by
  left; arm_unfold; arm_norm
  exact refines_subSh .ra _ (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2
    _ _ hty.1

/-! ## `MADDW`/`MSUBW` -/

/-- A value of shape `T0` where the validator's provenance clause holds at a non-word result
shape: not a pointer. -/
private theorem nonptr_of_shape {T T0 : Ty} {x : Val} (hT : wordShape T = false)
    (hp : (!wordShape T0) = true ∨ wordShape T = true) (hx : x.hasTy T0 = true) :
    ∀ p, x ≠ .ptr p := by
  rintro p rfl
  have := wordShape_of_ptr hx
  rcases hp with h | h <;> simp_all

/-- A register result at a non-word shape whose low bits are not at most 32: `poison`. -/
private theorem retypeL_res_wideOther {T : Ty} (hT : wordShape T = false) (hl : ¬ lowW T ≤ 32)
    (r : BitVec 64) : (Arm64.res T r).retypeL T = .poison := by
  cases T with
  | int w => cases w <;> simp_all [wordShape, lowW, Width.bits]
  | bool => simp [lowW] at hl
  | ptr _ => simp [wordShape] at hT
  | _ => rfl

private theorem op2_res_cases (T : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (args : List Val) :
    Arm64.op2 T f args = .poison ∨ ∃ r, Arm64.op2 T f args = Arm64.res T r := by
  unfold Arm64.op2
  split
  · split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- `ADD x (MULW a b)` (or `SUB`, `hs`) at a shape of at most 32 bits as `MADDW x a b`
(`MSUBW`): the low bits of the 64-bit sum of the 32-bit product are the 32-bit sum's; at a
non-word shape `x` is not a pointer (`hp`), and any other non-word shape reads `poison`. -/
private theorem refines_op2_mulw {T T1 : Ty} (f : BitVec 64 → BitVec 64 → BitVec 64)
    (f32 : BitVec 32 → BitVec 32 → BitVec 32)
    (hf : ∀ n, n ≤ 32 → ∀ (u z : BitVec 64) (m : BitVec 32), z.setWidth n = m.setWidth n →
      (f u z).setWidth n = (f32 (u.setWidth 32) m).setWidth n)
    (hT : wordShape T = false) (hw : lowW T ≤ argWidth T1) (x a b : Val) :
    Refines ((Arm64.op2 T f [x, (Arm64.op2w T1 (· * ·) [a, b]).retypeL T1]).retypeL T)
      ((Arm64.op3w T (fun u v w => f32 u (v * w)) [x, a, b]).retypeL T) := by
  by_cases hl : lowW T ≤ 32
  · obtain ⟨h1, h2⟩ := lowW_pos T
    cases ha : Arm64.reg32 a with
    | none =>
      have : Arm64.op2w T1 (· * ·) [a, b] = .poison := by simp only [Arm64.op2w, ha]
      rw [this, retypeL_poison, op2_poison_r, retypeL_poison]; exact .poison _
    | some va =>
      cases hb : Arm64.reg32 b with
      | none =>
        have : Arm64.op2w T1 (· * ·) [a, b] = .poison := by simp only [Arm64.op2w, ha, hb]
        rw [this, retypeL_poison, op2_poison_r, retypeL_poison]; exact .poison _
      | some vb =>
        have : Arm64.op2w T1 (· * ·) [a, b] = Arm64.res T1 ((va * vb).setWidth 64) := by
          simp only [Arm64.op2w, Arm64.res32, ha, hb]
        rw [this]
        rcases retypeL_res_reg h1 h2 hw ((va * vb).setWidth 64) with h | ⟨z, hz, hzk⟩
        · rw [h, op2_poison_r, retypeL_poison]; exact .poison _
        · cases hx : Arm64.reg x with
          | none => simp only [Arm64.op2, hx, retypeL_poison]; exact .poison _
          | some u =>
            have hx32 : Arm64.reg32 x = some (u.setWidth 32) := by
              simp only [Arm64.reg32, hx, Option.map_some]
            simp only [Arm64.op2, Arm64.op3w, Arm64.res32, hx, hx32, ha, hb, hz]
            apply Eq.subst (motive := fun v => Refines v _) (retypeL_res_low T _).symm
            · exact Refines.refl _
            · rw [hf _ hl u z (va * vb) (by rw [hzk, BitVec.setWidth_setWidth_of_le _ (by omega)]),
                BitVec.setWidth_setWidth_of_le _ (by omega)]
  · rcases op2_res_cases T f [x, (Arm64.op2w T1 (· * ·) [a, b]).retypeL T1] with h | ⟨r, h⟩ <;>
      rw [h]
    · rw [retypeL_poison]; exact .poison _
    · rw [retypeL_res_wideOther hT hl]; exact .poison _

private theorem add32_low (n : Nat) (hn : n ≤ 32) (u z : BitVec 64) (m : BitVec 32)
    (h : z.setWidth n = m.setWidth n) :
    (u + z).setWidth n = (u.setWidth 32 + m).setWidth n := by
  rw [BitVec.setWidth_add _ _ (by omega), BitVec.setWidth_add _ _ hn, h,
    BitVec.setWidth_setWidth_of_le _ hn]

private theorem sub32_low (n : Nat) (hn : n ≤ 32) (u z : BitVec 64) (m : BitVec 32)
    (h : z.setWidth n = m.setWidth n) :
    (u - z).setWidth n = (u.setWidth 32 - m).setWidth n := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.setWidth_add _ _ (by omega),
    BitVec.setWidth_add _ _ hn, BitVec.setWidth_neg_of_le (by omega), BitVec.setWidth_neg_of_le hn,
    h, BitVec.setWidth_setWidth_of_le _ hn]

/-- `ADD x (MULW a b)` at a non-word shape as `MADDW x a b` (`refines_op2_mulw`). -/
theorem refines_maddw {T T0 T1 : Ty} (hT : wordShape T = false) (hw : lowW T ≤ argWidth T1)
    (hp : (!wordShape T0) = true ∨ wordShape T = true) (x a b : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.add T [x, (Arm64.op2w T1 (· * ·) [a, b]).retypeL T1]).retypeL T)
      ((Arm64.op3w T (fun u v w => u + v * w) [x, a, b]).retypeL T) := by
  rw [add_nonptr T (nonptr_of_shape hT hp hx) (retypeL_op2w_nonptr T1 _ a b)]
  exact refines_op2_mulw (· + ·) (· + ·) add32_low hT hw x a b

/-- `refines_maddw` with the product first. -/
theorem refines_maddw_swap {T T0 T1 : Ty} (hT : wordShape T = false) (hw : lowW T ≤ argWidth T1)
    (hp : (!wordShape T0) = true ∨ wordShape T = true) (x a b : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.add T [(Arm64.op2w T1 (· * ·) [a, b]).retypeL T1, x]).retypeL T)
      ((Arm64.op3w T (fun u v w => u + v * w) [x, a, b]).retypeL T) := by
  rw [add_nonptr T (retypeL_op2w_nonptr T1 _ a b) (nonptr_of_shape hT hp hx),
    op2_swap T (fun u v => BitVec.add_comm u v)]
  exact refines_op2_mulw (· + ·) (· + ·) add32_low hT hw x a b

/-- `SUB x (MULW a b)` at a non-word shape as `MSUBW x a b` (`refines_op2_mulw`). -/
theorem refines_msubw {T T0 T1 : Ty} (hT : wordShape T = false) (hw : lowW T ≤ argWidth T1)
    (hp : (!wordShape T0) = true ∨ wordShape T = true) (x a b : Val) (hx : x.hasTy T0 = true) :
    Refines ((Arm64.sub T [x, (Arm64.op2w T1 (· * ·) [a, b]).retypeL T1]).retypeL T)
      ((Arm64.op3w T (fun u v w => u - v * w) [x, a, b]).retypeL T) := by
  rw [sub_nonptr T (nonptr_of_shape hT hp hx)]
  exact refines_op2_mulw (· - ·) (· - ·) sub32_low hT hw x a b

/-- `ARM64.rules:1017`: `(ADD a l:(MULW x y)) && v.Type.Size() <= 4 && l.Uses==1 && clobber(l) => (MADDW a x y)` -/
theorem r_ARM64_1017_sound : ArmRule.Checked r_ARM64_1017 := by
  left; arm_unfold
  all_goals arm_norm
  · arm_shape
    all_goals first
      | (simp [binE] at hcond; done)
      | exact refines_maddw rfl (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2
          _ _ _ hty.1
  · arm_shape
    all_goals first
      | (simp [binE] at hcond; done)
      | exact refines_maddw_swap rfl (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1)
          harg.2.2 _ _ _ hty.2

/-- `ARM64.rules:1018`: `(SUB a l:(MULW x y)) && v.Type.Size() <= 4 && l.Uses==1 && clobber(l) => (MSUBW a x y)` -/
theorem r_ARM64_1018_sound : ArmRule.Checked r_ARM64_1018 := by
  left; arm_unfold; arm_norm
  arm_shape
  all_goals first
    | (simp [binE] at hcond; done)
    | exact refines_msubw rfl (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2
        _ _ _ hty.1

end GoFV.Proof.Low.Rules
