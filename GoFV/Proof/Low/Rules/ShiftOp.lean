import GoFV.Proof.Low.Rules.Peep

variable [GoFV.SSA.Sem.Addrs]

/-!
# Lowering rule lemmas: folded operand producers (`ARM64.rules:1012-1018`, `1179-1184`, `1433-1449`, `1635`)

Peepholes of lowered code (#385) that fold an operand's producer into its consumer:

* `(AND|OR|XOR x0 x1:(SLLconst|SRLconst|SRAconst|RORconst [c] y)) && clobberIfDead(x1) =>
  (ANDshift..|ORshift..|XORshift.. x0 y [c])` (1439-1449, both argument orders) and
  `(AND|XOR|OR x (MVN y)) => (BIC|EON|ORN x y)` (1179-1181): the result is read at its low `lowW`
  bits, which only the low `lowW` bits of the folded operand decide; the operand's register read
  at its own shape keeps at least those bits (`armReadW` of the bitwise op, `harg`), so the folded
  form computes the same low bits from the producer's input (`refines_op2_op1`).
* `(MVN (XOR x y)) => (EON x y)` (1182): likewise for the inverted result (`refines_op1_op2`).
* `(ADD|SUB x0 x1:(SLLconst|SRLconst|SRAconst [c] y)) && clobberIfDead(x1) => (ADDshift..|SUBshift..
  x0 y [c])` (1433-1438): a pointer `x0` has a word shape, so by the validator's provenance clause
  (`Pat.argsOKLs`) the result has one and the shifted operand is read whole (`retypeL_res_wide`):
  both sides move the pointer by the same amount (`PtrOps.ptrRes`); any other `x0` adds as a
  register, low bits as above (`refines_addSh`, `refines_subSh`).
* `(ADD|SUB a l:(MULW x y)) && v.Type.Size() <= 4 && … => (MADDW|MSUBW a x y)` (1017, 1018): the
  condition rules out the word shapes, so `a` is no pointer (provenance clause); at most 32 low
  bits are read, which the 32-bit `MADDW` computes, and any other non-word shape is `poison`
  (`refines_op2_mulw`).
* `(ADD a l:(MUL x y)) && … => (MADD a x y)`, `(SUB a (MUL x y)) => (MSUB a x y)` and the `MNEG`
  forms (1012-1015): `MADD`/`MSUB` move a pointer `a` by `±x·y` as `ADD`/`SUB` do (`Arm64.madd`,
  `addP`); a pointer `a` makes the result word-shaped (provenance clause) and the product is read
  whole, any other `a` adds as a register, low bits as above (`refines_madd`).
* `(NEG (SUB x y)) => (SUB y x)` (1183) and `(NEG (NEG x)) => x` (1184): registers negate and
  subtract as words, low bits as above (`refines_op1_op2`). A pointer at a word shape is held as
  a pointer (`Ptr.held`: it does not convert, and it lies inside its window, since Phase 1 makes
  a pointer outside it `poison`, #385), has no register (`Ptr.convertible` is the `Ptr.ofAddr`
  round trip), and neither has any pointer `SUB` moves it to inside its window
  (`Ptr.held_of_blk`), so `NEG` of it is `poison` (`refines_neg_sub`, `refines_neg_neg`).

False under the semantics (docs/proofs/rules.md, Findings; counterexamples evaluated with
`#eval`), so not proven: 1197 (`x = heap (2^22) + 0`, `y = z = 2^41`: the target's `ADD x z`
leaves the window); 1198 (`x = y = temp 0 1 + 0`, `z = 2^24`: the target's `x - (y + z)` moves
`x` through an intermediate outside its window).
Not provable: 1701/1703 (`UBFX [armBFAuxInt(…)]`): `armBFAuxInt` is not a modelled helper
(`Helper.ofName`), so the result's auxint is the oracle's.
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

/-! ## `NEG` of `SUB` and of `NEG` (1183, 1184) -/

/-- A pointer that does not convert has no register (`Ptr.convertible_ofAddr`: every pointer
`Ptr.ofAddr` gives converts). -/
private theorem ptrReg_none {p : Ptr} (h : p.convertible = false) : Arm64.ptrReg p = none := by
  unfold Arm64.ptrReg
  split
  · split
    · rename_i he; rw [← he, Ptr.convertible_ofAddr] at h; cases h
    · rfl
  · rfl

/-- A pointer held as a pointer, read at any shape, has no register. -/
private theorem reg_retypeL_held (T : Ty) {q : Ptr} (hq : q.held = true) :
    Arm64.reg ((Val.ptr q).retypeL T) = none := by
  have hr : Arm64.reg (.ptr q) = none := ptrReg_none (Ptr.not_convertible_of_held hq)
  cases T with
  | int w =>
    cases w <;> simp only [Val.retypeL, Val.widen, Val.retype, Ptr.word_of_held hq, hr] <;> rfl
  | ptr _ => simp only [Val.retypeL, Val.widen, Val.retype, Ptr.word_of_held hq, hr]
  | _ => rfl

private theorem neg_low {n : Nat} (hn : n ≤ 64) (b b' : BitVec 64)
    (h : b.setWidth n = b'.setWidth n) : (-b).setWidth n = (-b').setWidth n := by
  rw [BitVec.setWidth_neg_of_le hn, BitVec.setWidth_neg_of_le hn, h]

/-- `NEG` of a register result (computed at shape `T1`, read back there): the negated register,
as far as the low `lowW T` bits go. -/
private theorem refines_neg_res {T T1 : Ty} (hw : lowW T ≤ argWidth T1) (r : BitVec 64) :
    Refines ((Arm64.op1 T (- ·) [(Arm64.res T1 r).retypeL T1]).retypeL T)
      ((Arm64.res T (-r)).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  rcases retypeL_res_reg h1 h2 hw r with e | ⟨z, hz, hzk⟩
  · rw [e]
    simp only [Arm64.op1, show Arm64.reg .poison = none from rfl, retypeL_poison]
    exact .poison _
  · simp only [Arm64.op1, hz]
    rw [retypeL_res_low T (neg_low h2 z r hzk)]
    exact Refines.refl _

private theorem neg_sub' (a b : BitVec 64) : -(a - b) = b - a := by
  rw [BitVec.neg_sub, BitVec.add_comm, ← BitVec.sub_eq_add_neg]

/-- `NEG (SUB x y)` as `SUB y x` (`ARM64.rules:1183`). Two operands with registers subtract as
registers, and the negated difference is the swapped one, as far as the low `lowW T` bits go
(`refines_op1_op2`). A pointer operand has no register: by its shape it is held as a pointer
(`Ptr.held`: it does not convert and lies inside its window, F1+F2 of #385), and so is every
pointer `SUB` moves it to inside its window (`Ptr.held_of_blk`), so `NEG` of it is `poison`.
Two pointers subtract by address or, in one block, by offset, symmetrically. -/
theorem refines_neg_sub {T T0 T1 T2 : Ty} (hw : lowW T ≤ argWidth T1) (x y : Val)
    (hx : x.hasTy T0 = true) (hy : y.hasTy T2 = true) :
    Refines ((Arm64.op1 T (- ·) [(Arm64.sub T1 [x, y]).retypeL T1]).retypeL T)
      ((Arm64.sub T [y, x]).retypeL T) := by
  have hpois : ∀ v, Refines ((Arm64.op1 T (- ·) [Val.retypeL T1 .poison]).retypeL T) v := fun v => by
    simp only [retypeL_poison, Arm64.op1, show Arm64.reg .poison = none from rfl]
    exact .poison _
  by_cases hxp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hxp
    have hp := Ptr.held_of_hasTy hx
    by_cases hyp : ∃ q, y = .ptr q
    · obtain ⟨q, rfl⟩ := hyp
      cases hpa : p.addr? <;> cases hqa : q.addr? <;> simp only [Arm64.sub, hpa, hqa]
      · by_cases hb : p.blk = q.blk
        · simp only [hb, beq_self_eq_true, ite_true]
          have h := refines_neg_res (T := T) hw (p.off - q.off)
          rwa [neg_sub'] at h
        · simp only [hb, Ne.symm hb, beq_iff_eq, ite_false]
          exact hpois _
      · by_cases hb : p.blk = q.blk
        · simp only [hb, beq_self_eq_true, ite_true]
          have h := refines_neg_res (T := T) hw (p.off - q.off)
          rwa [neg_sub'] at h
        · simp only [hb, Ne.symm hb, beq_iff_eq, ite_false]
          exact hpois _
      · by_cases hb : p.blk = q.blk
        · simp only [hb, beq_self_eq_true, ite_true]
          have h := refines_neg_res (T := T) hw (p.off - q.off)
          rwa [neg_sub'] at h
        · simp only [hb, Ne.symm hb, beq_iff_eq, ite_false]
          exact hpois _
      · rename_i a b
        have h := refines_neg_res (T := T) hw (a - b)
        rwa [neg_sub'] at h
    · -- `SUB p i` moves `p` inside its block: a held pointer or `poison`
      have hs : Arm64.sub T1 [.ptr p, y] = match Arm64.reg y with
          | some k => PtrOps.ptrRes (p.add (-k))
          | none => .poison := by
        cases y <;> first | rfl | exact absurd ⟨_, rfl⟩ hyp
      rw [hs]
      cases Arm64.reg y with
      | none => exact hpois _
      | some k =>
        simp only [PtrOps.ptrRes]
        split
        · rename_i hw'
          have hq : (p.add (-k)).held = true :=
            Ptr.held_of_blk (p := p) (q := p.add (-k)) rfl hp hw'
          rw [Ptr.word_of_held hq]
          simp only [Arm64.op1, reg_retypeL_held T1 hq, retypeL_poison]
          exact .poison _
        · exact hpois _
  · have hx' : ∀ p, x ≠ .ptr p := fun p h => hxp ⟨p, h⟩
    rw [sub_nonptr T1 hx']
    by_cases hyp : ∃ q, y = .ptr q
    · obtain ⟨q, rfl⟩ := hyp
      have hr : Arm64.reg (.ptr q) = none :=
        ptrReg_none (Ptr.not_convertible_of_held (Ptr.held_of_hasTy hy))
      rw [show Arm64.op2 T1 (· - ·) [x, .ptr q] = .poison by
        cases hxr : Arm64.reg x <;> simp only [Arm64.op2, hxr, hr]]
      exact hpois _
    · have hy' : ∀ q, y ≠ .ptr q := fun q h => hyp ⟨q, h⟩
      rw [sub_nonptr T hy']
      have he : Arm64.op2 T (· - ·) [y, x] = Arm64.op2 T (fun a b => -(a - b)) [x, y] := by
        cases hxr : Arm64.reg x <;> cases hyr : Arm64.reg y <;>
          simp only [Arm64.op2, hxr, hyr, neg_sub']
      rw [he]
      exact refines_op1_op2 (- ·) (· - ·) (fun b b' h => neg_low (lowW_pos T).2 b b' h) hw x y

/-- A register read back at the shape of the value it holds is the value. -/
private theorem retypeL_res_self {T : Ty} {x : Val} (hx : x.hasTy T = true) {v : BitVec 64}
    (hr : Arm64.reg x = some v) : (Arm64.res T v).retypeL T = x := by
  cases x with
  | int w a =>
    cases T with
    | int w' =>
      simp only [Val.hasTy, beq_iff_eq] at hx
      subst hx
      simp only [Arm64.reg, Option.some.injEq] at hr
      subst hr
      cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
    | ptr e =>
      cases w <;> simp [Val.hasTy] at hx
      simp only [Arm64.reg, Option.some.injEq] at hr
      subst hr
      simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
    | _ => simp [Val.hasTy] at hx
  | bool b =>
    cases T <;> simp [Val.hasTy] at hx
    simp only [Arm64.reg, Option.some.injEq] at hr
    subst hr
    cases b <;> rfl
  | ptr p =>
    have : Arm64.reg (.ptr p) = none :=
      ptrReg_none (Ptr.not_convertible_of_held (Ptr.held_of_hasTy hx))
    rw [this] at hr; cases hr
  | _ => cases hr

/-- `NEG (NEG x)` as `x` (`ARM64.rules:1184`) at a shape of `x` (`hT`): a register negated twice
is itself, as far as the low `lowW T` bits go, and read back at `x`'s shape it is `x`; a pointer
`x` is held as a pointer (its shape), has no register, and `NEG` of it is `poison`. -/
theorem refines_neg_neg {T T1 : Ty} (hw : lowW T ≤ argWidth T1) (x : Val)
    (hx : x.hasTy T = true) :
    Refines ((Arm64.op1 T (- ·) [(Arm64.op1 T1 (- ·) [x]).retypeL T1]).retypeL T) x := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  cases hr : Arm64.reg x with
  | none =>
    simp only [Arm64.op1, hr, retypeL_poison, show Arm64.reg .poison = none from rfl]
    exact .poison _
  | some v =>
    simp only [Arm64.op1, hr]
    rcases retypeL_res_reg h1 h2 hw (-v) with e | ⟨z, hz, hzk⟩
    · rw [e]
      simp only [show Arm64.reg .poison = none from rfl, retypeL_poison]
      exact .poison _
    · simp only [hz]
      rw [retypeL_res_low T (show (-z).setWidth (lowW T) = v.setWidth (lowW T) by
        rw [neg_low h2 z (-v) hzk, BitVec.neg_neg]), retypeL_res_self hx hr]
      exact Refines.refl _

/-- `NEG` reads its argument at the low `lowW` bits of its shape. -/
theorem armReadW_neg (T : Ty) : armReadW .ARM64NEG T 0 = lowW T := by
  cases T <;> rfl

/-- `ARM64.rules:1183`: `(NEG (SUB x y)) => (SUB y x)` -/
theorem r_ARM64_1183_sound : ArmRule.Checked r_ARM64_1183 := by
  left; arm_unfold; arm_norm
  exact refines_neg_sub (armReadW_neg _ ▸ harg.1) _ _ hty.1 hty.2

/-! ## `ADD` of a sign-masked shifted operand (1635) -/

private theorem add_poison_r (T : Ty) (x : Val) : Arm64.add T [x, .poison] = .poison := by
  cases x <;> rfl

private theorem op2_none_r (T : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64) (a : Val) {b : Val}
    (hb : Arm64.reg b = none) : Arm64.op2 T f [a, b] = .poison := by
  cases ha : Arm64.reg a <;> simp only [Arm64.op2, ha, hb]

/-- A register result at the shape of a value with a register whose shape holds 64 bits (a word
shape): the 64-bit integer. -/
private theorem retypeL_res_of_reg {T : Ty} {y : Val} {v : BitVec 64} (h : 64 ≤ argWidth T)
    (hy : y.hasTy T = true) (hr : Arm64.reg y = some v) (r : BitVec 64) :
    (Arm64.res T r).retypeL T = .int .w64 r := by
  cases T with
  | int w => cases w <;> simp_all [argWidth, Width.bits, Arm64.res, Val.retypeL, Val.widen, Val.retype]
  | ptr _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype]
  | agg _ _ => cases y <;> simp_all [Val.hasTy, Arm64.reg]
  | _ => simp_all [argWidth]

/-- The sign mask `z >> 63`: all ones or zero. -/
private theorem sra63_eq (z : BitVec 64) :
    z.sshiftRight 63 = if z.msb then BitVec.allOnes 64 else 0#64 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_sshiftRight]
  rcases Nat.lt_or_ge i 1 with h | h
  · obtain rfl : i = 0 := by omega
    rw [BitVec.msb_eq_getLsbD_last]
    by_cases hb : z.getLsbD 63 <;> simp [hb, BitVec.getLsbD_eq_getElem] at * <;> simp [hb]
  · by_cases hb : z.msb <;>
      simp only [hb, show ¬ 63 + i < 64 by omega, dite_false, ite_true, ite_false,
        BitVec.getElem_allOnes, BitVec.getElem_zero, Bool.false_eq_true]

/-- The sign mask `z >> 63` commutes with a left shift of the other operand. -/
private theorem sra63_and_shl (z y : BitVec 64) (j : Nat) :
    z.sshiftRight 63 &&& y <<< j = (y &&& z.sshiftRight 63) <<< j := by
  rw [sra63_eq]
  split <;> simp only [BitVec.allOnes_and, BitVec.and_allOnes, BitVec.zero_and, BitVec.and_zero,
    BitVec.zero_shiftLeft]

/-- `ADD x (ANDshiftLL (SRAconst [63] z) y [k])` (the `AND` computed at shape `T1`, the sign mask at
`T2`) as `ADDshiftLL x (ANDshiftRA y z [63]) [k]` (the `AND` at `y`'s shape `T3`): the mask is all
ones or zero, so it commutes with the shift (`sra63_and_shl`); both mask producers read whole
registers (`h2`, `h3`); a pointer `x` has a word shape, so the result has one (`hp`, the
validator's provenance clause) and the operand is read whole; otherwise only the low `lowW T` bits
count. -/
theorem refines_add_andSh {T T0 T1 T2 T3 : Ty} (k c : Int64) (hc : c.toInt = 63)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (h2 : 64 ≤ argWidth T2) (h3 : 64 ≤ argWidth T3) (x y z : Val) (hx : x.hasTy T0 = true)
    (hy : y.hasTy T3 = true) :
    Refines ((Arm64.add T [x, (Arm64.opSh T1 .ll k (fun a b => a &&& b)
        [(Arm64.op1 T2 (fun a => Arm64.Shift.ra.apply a (Arm64.amt c)) [z]).retypeL T2, y]).retypeL T1]).retypeL T)
      ((Arm64.addSh T .ll (Int64.ofInt k.toInt) [x, (Arm64.opSh T3 .ra (Int64.ofInt 63)
        (fun a b => a &&& b) [y, z]).retypeL T3]).retypeL T) := by
  rw [Int64.ofInt_toInt]
  have hamt : Arm64.amt c = 63 := by simp [Arm64.amt, hc]
  have hamt' : Arm64.amt (Int64.ofInt 63) = 63 := by decide
  have hsp : ∀ t, Refines ((Arm64.add T [x, Val.poison.retypeL T1]).retypeL T) t := fun t => by
    rw [retypeL_poison, add_poison_r, retypeL_poison]; exact .poison _
  have hreg : ∀ v : BitVec 64, Arm64.reg (.int .w64 v) = some v := fun v => by
    simp [Arm64.reg]
  have h64n : Width.w64.bits = 64 := rfl
  have hpl : ∀ (T' : Ty) (f : BitVec 64 → BitVec 64 → BitVec 64),
      Arm64.op2 T' f [.poison, y] = .poison := fun T' f => by
    cases hy' : Arm64.reg y <;> simp only [Arm64.op2, hy', show Arm64.reg .poison = none from rfl]
  cases hz : Arm64.reg z with
  | none =>
    simp only [Arm64.op1, hz, retypeL_poison, Arm64.opSh, hpl, add_poison_r]
    exact .poison _
  | some zv =>
    cases hyr : Arm64.reg y with
    | none =>
      simp only [Arm64.opSh, op2_none_r _ _ _ hyr]
      exact hsp _
    | some yv =>
      have hN : (Arm64.opSh T3 .ra (Int64.ofInt 63) (fun a b => a &&& b) [y, z]).retypeL T3 =
          .int .w64 (yv &&& zv.sshiftRight 63) := by
        simp only [Arm64.opSh, Arm64.op2, Arm64.shifted, hyr, hz, hamt', Arm64.Shift.apply,
          Nat.reduceMod]
        exact retypeL_res_of_reg h3 hy hyr _
      rw [hN]
      simp only [Arm64.op1, hz, hamt]
      rcases retypeL_res_wide h2 (Arm64.Shift.ra.apply zv 63) with hS | hS <;> rw [hS]
      · have hm : Arm64.opSh T1 .ll k (fun a b => a &&& b)
            [.int .w64 (Arm64.Shift.ra.apply zv 63), y] =
            Arm64.op1 T1 (fun b => Arm64.Shift.ll.apply b (Arm64.amt k))
              [.int .w64 (yv &&& zv.sshiftRight 63)] := by
          simp only [Arm64.opSh, Arm64.op2, Arm64.op1, Arm64.shifted, hreg, hyr,
            Arm64.Shift.apply, h64n, Nat.reduceMod]
          rw [sra63_and_shl]
        rw [hm]
        by_cases hxp : ∃ p, x = .ptr p
        · obtain ⟨p, rfl⟩ := hxp
          have hT : wordShape T = true := by
            have := wordShape_of_ptr hx
            rcases hp with h | h
            · simp [this] at h
            · exact h
          have h64 : 64 ≤ argWidth T1 := lowW_word hT ▸ hw
          simp only [Arm64.op1, hreg]
          rcases retypeL_res_wide h64
            (Arm64.Shift.ll.apply (yv &&& zv.sshiftRight 63) (Arm64.amt k)) with h | h <;> rw [h]
          · simp only [Arm64.add, Arm64.addSh, Arm64.addP, Arm64.shifted, hreg]
            exact Refines.refl _
          · rw [add_poison_r, retypeL_poison]; exact .poison _
        · have hx' : ∀ p, x ≠ .ptr p := fun p h => hxp ⟨p, h⟩
          rw [add_nonptr T hx' (retypeL_op1_nonptr T1 _ _), addSh_nonptr T .ll k hx']
          exact refines_op2_op1 (· + ·) _ (fun a b b' h => add_low (lowW_pos T).2 a b b' h) hw x _
      · simp only [Arm64.opSh, hpl]
        exact hsp _

private theorem armReadW_andSh (T : Ty) (i : Nat) : armReadW .ARM64ANDshiftLL T i = 64 := by
  cases T <;> rfl

private theorem armReadW_sra (T : Ty) (i : Nat) : armReadW .ARM64SRAconst T i = 64 := by
  cases T <;> rfl

private theorem retypeL_opSh_nonptr (T : Ty) (sh : Arm64.Shift) (k : Int64)
    (g : BitVec 64 → BitVec 64 → BitVec 64) (a b : Val) (p : Ptr) :
    (Arm64.opSh T sh k g [a, b]).retypeL T ≠ .ptr p := by
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b <;>
    simp only [Arm64.opSh, Arm64.op2, ha, hb, retypeL_poison, ne_eq, reduceCtorEq,
      not_false_eq_true, retypeL_res_nonptr]

/-- `ADD` of an operand that is no pointer, in either order. -/
private theorem add_comm_nonptr (T : Ty) {v : Val} (hv : ∀ p, v ≠ .ptr p) (x : Val) :
    Arm64.add T [v, x] = Arm64.add T [x, v] := by
  cases x with
  | ptr p => cases v <;> first | rfl | exact absurd rfl (hv _)
  | _ =>
    rw [add_nonptr T hv (fun p h => by cases h), add_nonptr T (fun p h => by cases h) hv]
    exact op2_swap T (fun a b => BitVec.add_comm a b) _ _

/-- `ARM64.rules:1635`: `(ADD x0 x1:(ANDshiftLL x2:(SRAconst [63] z) y [sl])) && x1.Uses == 1 && x2.Uses == 1 => (ADDshiftLL x0 (ANDshiftRA <y.Type> y z [63]) [sl])` -/
theorem r_ARM64_1635_sound : ArmRule.Checked r_ARM64_1635 := by
  left; arm_unfold
  all_goals arm_norm
  · have hc' : (e.auxInt [0, 1]).toInt = 63 := by injection hc
    exact refines_add_andSh _ _ hc' (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1)
      harg.1.2 (armReadW_andSh _ 0 ▸ harg.2.2.1.1) (armReadW_andSh _ 1 ▸ harg.2.2.2) _ _ _ hty.1
      hty.2.2
  · have hc' : (e.auxInt [0, 0]).toInt = 63 := by injection hc
    rw [add_comm_nonptr _ (retypeL_opSh_nonptr _ _ _ _ _ _)]
    exact refines_add_andSh _ _ hc' (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1)
      harg.2.2 (armReadW_andSh _ 0 ▸ harg.1.2.1.1) (armReadW_andSh _ 1 ▸ harg.1.2.2) _ _ _ hty.2
      hty.1.2

/-! ## `MADD`/`MSUB` (1012-1015) -/

/-- `ADD a (g x y)` or `SUB a (g x y)` (`op`; `s` the sign of the product's register in the sum;
the product computed at shape `T1`) as `MADD`/`MSUB a x y` (`Arm64.madd`): a pointer `a` has a
word shape `T0`, so the result has one (`hp`, the validator's provenance clause) and the product
is read whole: both sides move `a` by the same amount (`addP`); otherwise only the low `lowW T`
bits of the sum count. -/
theorem refines_madd {T T0 T1 : Ty} (op : Val → Val → Val) (s : BitVec 64 → BitVec 64)
    (hop : ∀ p r, op (.ptr p) (.int .w64 r) = PtrOps.ptrRes (p.add (s r)))
    (hop2 : ∀ a b, (∀ p, a ≠ .ptr p) → (∀ p, b ≠ .ptr p) →
      op a b = Arm64.op2 T (fun u v => u + s v) [a, b])
    (hpo : ∀ a, op a .poison = .poison)
    (hsl : ∀ n, n ≤ 64 → ∀ b b' : BitVec 64, b.setWidth n = b'.setWidth n →
      (s b).setWidth n = (s b').setWidth n)
    (g : BitVec 64 → BitVec 64 → BitVec 64) (neg : Bool)
    (hg : ∀ u v, s (g u v) = if neg then -(u * v) else u * v)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (a x y : Val) (ha : a.hasTy T0 = true) :
    Refines ((op a ((Arm64.op2 T1 g [x, y]).retypeL T1)).retypeL T)
      ((Arm64.madd T neg [a, x, y]).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  cases hx : Arm64.reg x with
  | none =>
    simp only [Arm64.op2, hx, retypeL_poison, hpo]; exact .poison _
  | some u =>
    cases hy : Arm64.reg y with
    | none =>
      simp only [Arm64.op2, hx, hy, retypeL_poison, hpo]; exact .poison _
    | some v =>
      simp only [Arm64.op2, Arm64.madd, hx, hy, ← hg]
      by_cases hap : ∃ p, a = .ptr p
      · obtain ⟨p, rfl⟩ := hap
        have hT : wordShape T = true := by
          have := wordShape_of_ptr ha
          rcases hp with h | h
          · simp [this] at h
          · exact h
        have h64 : 64 ≤ argWidth T1 := lowW_word hT ▸ hw
        rcases retypeL_res_wide h64 (g u v) with h | h <;> rw [h]
        · rw [hop]; exact Refines.refl _
        · rw [hpo, retypeL_poison]; exact .poison _
      · have ha' : ∀ p, a ≠ .ptr p := fun p h => hap ⟨p, h⟩
        rw [hop2 _ _ ha' (retypeL_res_nonptr T1 _)]
        rcases retypeL_res_reg h1 h2 hw (g u v) with h | ⟨z, hz, hzk⟩
        · rw [h, op2_poison_r, retypeL_poison]; exact .poison _
        · rw [addP_nonptr T ha']
          cases hra : Arm64.reg a with
          | none => simp only [Arm64.op2, hra, retypeL_poison]; exact .poison _
          | some r =>
            simp only [Arm64.op2, hra, hz]
            rw [retypeL_res_low T (show (r + s z).setWidth (lowW T) = (r + s (g u v)).setWidth (lowW T)
              from by rw [BitVec.setWidth_add _ _ h2, BitVec.setWidth_add _ _ h2, hsl _ h2 _ _ hzk])]
            exact Refines.refl _

/-- `refines_madd` for `ADD a (g x y)`. -/
theorem refines_madd_add {T T0 T1 : Ty} (g : BitVec 64 → BitVec 64 → BitVec 64) (neg : Bool)
    (hg : ∀ u v, g u v = if neg then -(u * v) else u * v)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (a x y : Val) (ha : a.hasTy T0 = true) :
    Refines ((Arm64.add T [a, (Arm64.op2 T1 g [x, y]).retypeL T1]).retypeL T)
      ((Arm64.madd T neg [a, x, y]).retypeL T) :=
  refines_madd (fun a b => Arm64.add T [a, b]) id
    (fun p r => by simp only [Arm64.add, Arm64.reg, BitVec.setWidth_eq, id])
    (fun _ _ ha hb => add_nonptr T ha hb) (add_poison_r T) (fun _ _ _ _ h => h) g neg hg hw hp
    a x y ha

/-- `refines_madd` for `SUB a (g x y)`. -/
theorem refines_madd_sub {T T0 T1 : Ty} (g : BitVec 64 → BitVec 64 → BitVec 64) (neg : Bool)
    (hg : ∀ u v, -(g u v) = if neg then -(u * v) else u * v)
    (hw : lowW T ≤ argWidth T1) (hp : (!wordShape T0) = true ∨ wordShape T = true)
    (a x y : Val) (ha : a.hasTy T0 = true) :
    Refines ((Arm64.sub T [a, (Arm64.op2 T1 g [x, y]).retypeL T1]).retypeL T)
      ((Arm64.madd T neg [a, x, y]).retypeL T) :=
  refines_madd (fun a b => Arm64.sub T [a, b]) (- ·)
    (fun p r => by simp only [Arm64.sub, Arm64.reg, BitVec.setWidth_eq])
    (fun _ _ ha _ => by rw [sub_nonptr T ha]; simp only [BitVec.sub_eq_add_neg])
    (fun a => by cases a <;> rfl)
    (fun _ hn _ _ h => by rw [BitVec.setWidth_neg_of_le hn, BitVec.setWidth_neg_of_le hn, h])
    g neg hg hw hp a x y ha

private theorem retypeL_op2_nonptr (T : Ty) (g : BitVec 64 → BitVec 64 → BitVec 64) (a b : Val)
    (p : Ptr) : (Arm64.op2 T g [a, b]).retypeL T ≠ .ptr p := by
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b <;>
    simp only [Arm64.op2, ha, hb, retypeL_poison, ne_eq, reduceCtorEq, not_false_eq_true,
      retypeL_res_nonptr]

/-- `ARM64.rules:1012`: `(ADD a l:(MUL x y)) && l.Uses==1 && clobber(l) => (MADD a x y)` -/
theorem r_ARM64_1012_sound : ArmRule.Checked r_ARM64_1012 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_madd_add _ false (fun _ _ => rfl)
      (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2 _ _ _ hty.1
  · rw [add_comm_nonptr _ (retypeL_op2_nonptr _ _ _ _)]
    exact refines_madd_add _ false (fun _ _ => rfl)
      (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1) harg.2.2 _ _ _ hty.2

/-- `ARM64.rules:1013`: `(SUB a l:(MUL x y)) && l.Uses==1 && clobber(l) => (MSUB a x y)` -/
theorem r_ARM64_1013_sound : ArmRule.Checked r_ARM64_1013 := by
  left; arm_unfold; arm_norm
  exact refines_madd_sub _ true (fun _ _ => rfl)
    (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2 _ _ _ hty.1

/-- `ARM64.rules:1014`: `(ADD a l:(MNEG x y)) && l.Uses==1 && clobber(l) => (MSUB a x y)` -/
theorem r_ARM64_1014_sound : ArmRule.Checked r_ARM64_1014 := by
  left; arm_unfold
  all_goals arm_norm
  · exact refines_madd_add _ true (fun _ _ => rfl)
      (armReadW_addSub .ARM64ADD _ 1 (.inl rfl) ▸ harg.2.1.1) harg.1.2 _ _ _ hty.1
  · rw [add_comm_nonptr _ (retypeL_op2_nonptr _ _ _ _)]
    exact refines_madd_add _ true (fun _ _ => rfl)
      (armReadW_addSub .ARM64ADD _ 0 (.inl rfl) ▸ harg.1.1.1) harg.2.2 _ _ _ hty.2

/-- `ARM64.rules:1015`: `(SUB a l:(MNEG x y)) && l.Uses==1 && clobber(l) => (MADD a x y)` -/
theorem r_ARM64_1015_sound : ArmRule.Checked r_ARM64_1015 := by
  left; arm_unfold; arm_norm
  exact refines_madd_sub _ false (fun _ _ => BitVec.neg_neg)
    (armReadW_addSub .ARM64SUB _ 1 (.inr rfl) ▸ harg.2.1.1) harg.1.2 _ _ _ hty.1

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
