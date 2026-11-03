import GoFV.Proof.Low.RuleL
import GoFV.Proof.Rules.Tactic

/-!
# Lemma kit for the lowering rule lemmas (issue #385)

The facts the rule lemmas of `GoFV/Proof/Low/Rules/*` share:

* `retypeL` of an arm64 register result (`Arm64.res`) against the generic value it stands for:
  a register holding the zero-extension of a `w`-bit integer is that integer at every shape
  (`refines_res_zext`);
* `SetOpSound` of an ellipsis rule whose generic op is a `w`-bit integer op (`GoFV.SSA.Sem.int1`,
  `GoFV.SSA.Sem.int2`) and whose arm64 op computes the zero-extension of its result on zero-extended
  arguments (`setOpSound_int1`, `setOpSound_int2`), or which computes the same value
  (`setOpSound_same`);
* the term facts of `ArmRule.SetOp` (`termVL_generic`, `termVL_arm`) and the three shapes of
  `ArmRule.Checked` (`checked_setOp`, `checked_rename`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low GoFV.Opt.LowerTerm

/-! ## `opValL` at an op -/

/-- `opValL` of an arm64 op other than `MOVDaddr`: `Arm64.evalPure`. -/
theorem opValL_arm {o : Op} (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false)
    (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  simp only [opValL, hg, hm, Bool.false_eq_true, ite_false]

/-- `opValL` of a generic op other than `Addr`/`ConstString`: `evalPure`. -/
theorem opValL_gen {o : Op} (hg : o.generic = true) (hf : frameOp o = false)
    (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = evalPure o ty ai ax args := by
  simp only [opValL, hg, ite_true, opVal_pure hf]

/-- `Arm64.evalPure op …` at a constructor `op`: its family's definition. -/
dsimproc reduceArmEvalPure (Arm64.evalPure _ _ _ _ _) := fun e => do
  -- `Arm64.evalPure` has an implicit universe-polymorphic `AuxRef` argument first
  unless e.isAppOfArity ``GoFV.SSA.Sem.Arm64.evalPure 6 do return .continue
  unless (e.getArg! 1).isConst do return .continue
  match ← reduceAtOp e with
  | some e' => return .done e'
  | none => return .continue

/-! ## Shapes of register results -/

@[simp] theorem retypeL_poison (t : Ty) : Val.poison.retypeL t = .poison := by
  cases t <;> rfl

/-- A register holding the zero-extension of a `w`-bit integer `r` is `r` at every shape. -/
theorem refines_res_zext (ty : Ty) (w : Width) (r : BitVec w.bits) :
    Refines ((Val.int w r).retypeL ty) ((Arm64.res ty (r.setWidth 64)).retypeL ty) := by
  cases ty with
  | bool => simp only [Val.retypeL, Arm64.res, Val.widen, Val.retype]; exact .poison _
  | int w' =>
    have h : Val.retypeL (.int w') (Val.int w r) =
        Val.retypeL (.int w') (Val.int .w64 (r.setWidth 64)) := by
      cases w <;> cases w' <;>
        simp (config := { decide := true }) [Val.retypeL, Val.widen, Val.retype,
          BitVec.setWidth_setWidth_of_le]
    rw [h]; exact Refines.refl _
  | ptr e =>
    have h : Val.retypeL (.ptr e) (Val.int w r) =
        Val.retypeL (.ptr e) (Val.int .w64 (r.setWidth 64)) := by
      cases w <;> simp (config := { decide := true }) [Val.retypeL, Val.widen, Val.retype]
    rw [h]; exact Refines.refl _
  | _ => simp only [Val.retypeL, Arm64.res, Val.widen, Val.retype]; exact .poison _

/-- `refines_res_zext` at 64 bits. -/
theorem refines_res64 (ty : Ty) (r : BitVec 64) :
    Refines ((Val.int .w64 r).retypeL ty) ((Arm64.res ty r).retypeL ty) := by
  have h := refines_res_zext ty .w64 r
  simpa only [Width.bits, BitVec.setWidth_eq] using h


/-! ## Extensions of registers -/

/-- `MOV{B,H,W}Ureg` of a zero-extended `n`-bit integer: unchanged. -/
theorem ext_false_setWidth (n : Nat) (x : BitVec n) (_h : n ≤ 64) :
    Arm64.ext false n (x.setWidth 64) = x.setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm64.ext, Arm64.mask, Bool.false_eq_true, ite_false, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases hin : i < n
  · simp [hin, hi]
  · simp [hin, BitVec.getLsbD_of_ge x i (by omega)]

/-- `MOV{B,H,W}reg` of a zero-extended `n`-bit integer: its sign extension. -/
theorem ext_true_setWidth (n : Nat) (x : BitVec n) (h0 : 0 < n) (h : n ≤ 64) :
    Arm64.ext true n (x.setWidth 64) = x.signExtend 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Arm64.ext, Arm64.sext, Arm64.mask, ite_true, Nat.pos_iff_ne_zero.mp h0, ite_false,
    BitVec.getLsbD_sshiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one,
    BitVec.getLsbD_signExtend, BitVec.msb_shiftLeft, BitVec.getMsbD]
  have e1 : 64 - n + i - (64 - n) = i := by omega
  have e2 : 64 - 1 - (64 - n) = n - 1 := by omega
  rw [e1, e2, BitVec.msb_eq_getLsbD_last]
  by_cases hin : i < n
  · have h1 : 64 - n + i < 64 := by omega
    simp [hin, h1, hi, show ¬ 64 ≤ i by omega, show ¬ 64 - n + i < 64 - n by omega]
  · have h1 : ¬ 64 - n + i < 64 := by omega
    simp [hin, h1, hi, show n - 1 < n by omega, show ¬ 64 ≤ i by omega,
      show 64 - n < 64 by omega, show n - 1 < 64 by omega]

/-- The low `m` bits of a sign extension to `k ≥ m` bits: the sign extension to `m` bits. -/
theorem setWidth_signExtend_le {n m k : Nat} (x : BitVec n) (h : m ≤ k) :
    (x.signExtend k).setWidth m = x.signExtend m := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, show i < k by omega]

theorem ext_false_setWidth' (n : Nat) (x : BitVec n) (h : n ≤ 64 := by decide) :
    Arm64.ext false n (x.setWidth 64) = x.setWidth 64 := ext_false_setWidth n x h

theorem ext_true_setWidth' (n : Nat) (x : BitVec n) (h0 : 0 < n := by decide)
    (h : n ≤ 64 := by decide) :
    Arm64.ext true n (x.setWidth 64) = x.signExtend 64 := ext_true_setWidth n x h0 h

/-! ## Argument cases -/

theorem int1_cases (w : Width) (f : BitVec w.bits → Val) (args : List Val) :
    GoFV.SSA.Sem.int1 w f args = .poison ∨ ∃ x, args = [.int w x] ∧ GoFV.SSA.Sem.int1 w f args = f x := by
  match args with
  | [a] =>
    cases a with
    | int w' x =>
      by_cases h : w' = w
      · subst h; exact .inr ⟨x, rfl, by simp [GoFV.SSA.Sem.int1]⟩
      · exact .inl (by simp [GoFV.SSA.Sem.int1, Val.asInt, h])
    | _ => exact .inl rfl
  | [] => exact .inl rfl
  | _ :: _ :: _ => exact .inl rfl

theorem int2_cases (w : Width) (f : BitVec w.bits → BitVec w.bits → Val) (args : List Val) :
    GoFV.SSA.Sem.int2 w f args = .poison ∨
      ∃ x y, args = [.int w x, .int w y] ∧ GoFV.SSA.Sem.int2 w f args = f x y := by
  match args with
  | [a, b] =>
    cases a with
    | int w' x =>
      cases b with
      | int w'' y =>
        by_cases h : w' = w
        · subst h
          by_cases h' : w'' = w'
          · subst h'; exact .inr ⟨x, y, rfl, by simp [GoFV.SSA.Sem.int2]⟩
          · exact .inl (by simp [GoFV.SSA.Sem.int2, Val.asInt, h'])
        · exact .inl (by simp [GoFV.SSA.Sem.int2, Val.asInt, h])
      | _ =>
        exact .inl (by simp only [GoFV.SSA.Sem.int2, Val.asInt]; split <;> simp_all)
    | _ => exact .inl rfl
  | [] => exact .inl rfl
  | [_] => exact .inl rfl
  | _ :: _ :: _ :: _ => exact .inl rfl

/-! ## Ellipsis rules on integer ops -/

/-- `SetOpSound` of a unary `w`-bit op (result of width `w'`) whose arm64 op computes the
zero-extended result: sound at every shape. -/
theorem setOpSound_int1 {o o' : Op} (w w' : Width) (f : BitVec w.bits → BitVec w'.bits)
    (h1 : ∀ tabs ty ai ax args,
      opValL tabs o ty ai ax args = GoFV.SSA.Sem.int1 w (fun x => .int w' (f x)) args)
    (h2 : ∀ tabs ty ai ax x,
      opValL tabs o' ty ai ax [.int w x] = Arm64.res ty ((f x).setWidth 64)) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  rw [h1]
  rcases int1_cases w (fun x => .int w' (f x)) args with h | ⟨x, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  · rw [h, h2]; exact refines_res_zext ty w' (f x)

/-- `SetOpSound` of a binary `w`-bit op whose arm64 op computes the zero-extended result:
sound at every shape. -/
theorem setOpSound_int2 {o o' : Op} (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits)
    (h1 : ∀ tabs ty ai ax args,
      opValL tabs o ty ai ax args = GoFV.SSA.Sem.int2 w (fun x y => .int w (f x y)) args)
    (h2 : ∀ tabs ty ai ax x y,
      opValL tabs o' ty ai ax [.int w x, .int w y] = Arm64.res ty ((f x y).setWidth 64)) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  rw [h1]
  rcases int2_cases w (fun x y => .int w (f x y)) args with h | ⟨x, y, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  · rw [h, h2]; exact refines_res_zext ty w (f x y)

@[simp] theorem retypeL_int_self (w : Width) (x : BitVec w.bits) :
    (Val.int w x).retypeL (.int w) = .int w x := by
  cases w <;> simp [Val.retypeL, Val.widen, Val.retype]

/-- `SetOpSound` of a unary `w`-bit op of result width `w'` at its own shape `.int w'` (the only
one `topOKL` admits, `htop`): the arm64 result read at `w'` bits. -/
theorem setOpSound_top1 {o o' : Op} (w w' : Width) (f : BitVec w.bits → BitVec w'.bits)
    (htop : ∀ ty, topOKL o ty = true → ty = .int w')
    (h1 : ∀ tabs ty ai ax args,
      opValL tabs o ty ai ax args = GoFV.SSA.Sem.int1 w (fun x => .int w' (f x)) args)
    (h2 : ∀ tabs ai ax x,
      (opValL tabs o' (.int w') ai ax [.int w x]).retypeL (.int w') = .int w' (f x)) :
    SetOpSound o o' := by
  intro tabs ty ai ax args ht
  obtain rfl := htop ty ht
  rw [h1]
  rcases int1_cases w (fun x => .int w' (f x)) args with h | ⟨x, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  · rw [h, h2, retypeL_int_self]; exact Refines.refl _

/-- `SetOpSound` of a binary `w`-bit op at its own shape `.int w` (`htop`). -/
theorem setOpSound_top2 {o o' : Op} (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits)
    (htop : ∀ ty, topOKL o ty = true → ty = .int w)
    (h1 : ∀ tabs ty ai ax args,
      opValL tabs o ty ai ax args = GoFV.SSA.Sem.int2 w (fun x y => .int w (f x y)) args)
    (h2 : ∀ tabs ai ax x y,
      (opValL tabs o' (.int w) ai ax [.int w x, .int w y]).retypeL (.int w) = .int w (f x y)) :
    SetOpSound o o' := by
  intro tabs ty ai ax args ht
  obtain rfl := htop ty ht
  rw [h1]
  rcases int2_cases w (fun x y => .int w (f x y)) args with h | ⟨x, y, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  · rw [h, h2, retypeL_int_self]; exact Refines.refl _

/-- `SetOpSound` of two ops with the same value. -/
theorem setOpSound_same {o o' : Op}
    (h : ∀ tabs ty ai ax args, opValL tabs o ty ai ax args = opValL tabs o' ty ai ax args) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  rw [h]; exact Refines.refl _

/-- The register of an integer at shape `.int w`: its low `w` bits. -/
@[simp] theorem retypeL_res_int (w : Width) (r : BitVec 64) :
    (Arm64.res (.int w) r).retypeL (.int w) = .int w (r.setWidth w.bits) := by
  cases w <;> rfl

/-- An integer read at a narrower (or its own) integer shape: its low bits. -/
theorem retypeL_int_int (w w' : Width) (x : BitVec w.bits) (h : w'.bits ≤ w.bits) :
    (Val.int w x).retypeL (.int w') = .int w' (x.setWidth w'.bits) := by
  cases w <;> cases w' <;> first | rfl | (exfalso; revert h; decide)

/-- The arm64 side of an ellipsis rule on integers: `opValL` of an arm64 op, its family, the
registers of integer arguments. -/
macro "arm_reg" : tactic => `(tactic| (
  intros
  simp (disch := decide) only [opValL_arm, opValL_gen, reduceArmEvalPure, reduceEvalPure,
    Arm64.add, Arm64.sub, Arm64.op1, Arm64.op2, Arm64.op1w, Arm64.op2w, Arm64.res32, Arm64.reg,
    Arm64.reg32, Option.map_some, BitVec.setWidth_eq, BitVec.setWidth_and, BitVec.setWidth_or,
    BitVec.setWidth_xor, retypeL_res_int, BitVec.setWidth_setWidth_of_le, BitVec.sub_eq_add_neg,
    BitVec.setWidth_add, BitVec.setWidth_mul, BitVec.setWidth_neg_of_le, BitVec.setWidth_not,
    BitVec.setWidth_setWidth, ext_false_setWidth', ext_true_setWidth', setWidth_signExtend_le,
    retypeL_int_int, Width.bits]))

/-- `topOKL o ty` at an integer op of width `w` forces `ty = .int w`. -/
macro "arm_top" : tactic => `(tactic| (
  intro ty h
  cases ty with
  | int w' => cases w' <;> first | rfl | exact absurd h Bool.false_ne_true
  | _ => exact absurd h Bool.false_ne_true))

/-! ## Term facts and the shapes of `ArmRule.Checked` -/

theorem termVL_generic (o : Op) (hg : o.generic = true)
    (ht : GoFV.Opt.RewriteCheck.termOp o = true) :
    ∀ tabs (v : Value), v.op = o → termVL tabs v = true := by
  intro tabs v hv
  simp only [termVL, hv, hg, ht, ite_true]

theorem termVL_arm (o : Op) (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false)
    (ht : (armTerm o && !actOp o && !isRoot o) = true) :
    ∀ tabs (v : Value), v.op = o → termVL tabs v = true := by
  intro tabs v hv
  simp only [termVL, hv, hg, hm, Bool.false_eq_true, ite_false, ht]

/-- An ellipsis rule `(o ...) => (o' ...)` on terms with `SetOpSound o o'`. -/
theorem checked_setOp {r : Rule} (o o' : Op) (hp : ellipsisOn o r.pat = true)
    (hr : r.result = .setOp o') (hc : r.cond = none) (hb : r.block = none)
    (h1 : ∀ tabs (v : Value), v.op = o → termVL tabs v = true)
    (h2 : ∀ tabs (v : Value), v.op = o' → termVL tabs v = true) (hs : SetOpSound o o') :
    ArmRule.Checked r :=
  .inr (.inl ⟨o, o', hp, hr, hc, hb, h1, h2, hs⟩)

/-- An atom rename `(o ...) => (o' ...)`. -/
theorem checked_rename {r : Rule} (o o' : Op) (hp : ellipsisOn o r.pat = true)
    (hr : r.result = .setOp o') (hc : r.cond = none) (hb : r.block = none)
    (hn : renameOp o o' = true) : ArmRule.Checked r :=
  .inr (.inr ⟨o, o', hp, hr, hc, hb, hn⟩)

end GoFV.Proof.Low.Rules
