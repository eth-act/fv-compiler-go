import GoFV.Proof.Low.RuleL
import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Low.Rules.Attr

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

/-- `opValL` of an arm64 op other than `MOVDaddr` and the integer loads: `Arm64.evalPure`. -/
theorem opValL_arm {o : Op} (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false)
    (hl : ldOp? o = none) (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]

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

/-! ## Arm64 families (`arm_sem`) -/

attribute [arm_sem] Arm64.imm Arm64.addK Arm64.res32 Arm64.reg32 Option.map_some
  BitVec.setWidth_eq

/-- `opValL` of `Addr`: the global the symbol names. -/
@[arm_sem] theorem opValL_addr (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs .Addr ty ai ax args = addrVal tabs ax := by
  simp only [opValL, show Op.generic .Addr = true from rfl, ite_true, opVal_addr]

/-- `opValL` of `MOVDaddr`: `movAddr`. -/
@[arm_sem] theorem opValL_movDaddr (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs .ARM64MOVDaddr ty ai ax args = movAddr tabs ai ax args := by
  simp only [opValL, show Op.generic .ARM64MOVDaddr = false from rfl, Bool.false_eq_true,
    ite_false, beq_self_eq_true, ite_true]

/-- `Addr {sym}` as `MOVDaddr {sym} base`: the same global. -/
theorem refines_addr_movAddr (T : Ty) (tabs : Tables) (ax : Option AuxRef) (base : Val) :
    Refines ((addrVal tabs ax).retypeL T) ((movAddr tabs 0 ax [base]).retypeL T) := by
  cases ax with
  | none => simp only [addrVal, Option.bind_none, retypeL_poison]; exact .poison _
  | some n =>
    simp only [addrVal, Option.bind_some, movAddr, symPtr]
    rcases hx : tabs.aux? n with _ | ⟨fmt, k⟩
    · rw [retypeL_poison]; exact .poison _
    · cases k with
      | sym name =>
        have : PtrOps.ptrRes ⟨.global name.toStringLossy, BitVec.ofInt 64 (0 : Int64).toInt⟩ =
            .ptr ⟨.global name.toStringLossy, 0⟩ := rfl
        simp only [Option.elim, this]
        exact Refines.refl _
      | _ => rw [retypeL_poison]; exact .poison _

/-- The low `n` bits of a 64-bit immediate. -/
@[arm_sem] theorem setWidth_ofInt_le {n m : Nat} (h : n ≤ m) (x : Int) :
    (BitVec.ofInt m x).setWidth n = BitVec.ofInt n x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  have h2 : ((2 ^ n : Nat) : Int) ∣ ((2 ^ m : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 h)
  have hm : (0 : Int) < ((2 ^ m : Nat) : Int) := by
    have := Nat.two_pow_pos m; omega
  have hn : (0 : Int) < ((2 ^ n : Nat) : Int) := by
    have := Nat.two_pow_pos n; omega
  have hy := Int.emod_nonneg x (Int.ne_of_gt hm)
  have hy' := Int.emod_nonneg x (Int.ne_of_gt hn)
  have key : (((x % ((2 ^ m : Nat) : Int)).toNat % 2 ^ n : Nat) : Int) =
      (((x % ((2 ^ n : Nat) : Int)).toNat : Nat) : Int) := by
    rw [Int.natCast_emod, Int.toNat_of_nonneg hy, Int.toNat_of_nonneg hy']
    exact Int.emod_emod_of_dvd x h2
  exact_mod_cast key

/-- A narrow constant: the register holding its low bits at its own shape. -/
theorem refines_top_int (w : Width) (x : BitVec w.bits) (r : BitVec 64)
    (h : r.setWidth w.bits = x) :
    Refines ((Val.int w x).retypeL (.int w)) ((Arm64.res (.int w) r).retypeL (.int w)) := by
  rw [retypeL_int_self, retypeL_res_int, h]; exact Refines.refl _

/-- `OffPtr [k] v` as `ADDconst [k] v` at a pointer shape. -/
theorem refines_offPtr (el : Option Nat) (k : Int64) (v : Val) :
    Refines ((PtrOps.offPtr k [v]).retypeL (.ptr el))
      ((Arm64.addK (.ptr el) (BitVec.ofInt 64 k.toInt) [v]).retypeL (.ptr el)) := by
  cases v with
  | ptr q => exact Refines.refl _
  | int w x =>
    cases w with
    | w64 =>
      simp only [PtrOps.offPtr, PtrOps.wordRes, Arm64.addK, Arm64.addP, Arm64.reg, Arm64.res,
        BitVec.setWidth_eq]
      split
      · exact Refines.refl _
      · rw [retypeL_poison]; exact .poison _
    | _ => rw [show PtrOps.offPtr k [.int _ x] = .poison from rfl, retypeL_poison]; exact .poison _
  | _ => rw [show PtrOps.offPtr k [_] = .poison from rfl, retypeL_poison]; exact .poison _

/-- `ADDconst [0] v` at `v`'s own shape is `v` (or `poison`). -/
theorem refines_addP_zero (T : Ty) (v : Val) (h : v.hasTy T = true) :
    Refines ((Arm64.addP T v 0).retypeL T) v := by
  have hz : ∀ y : BitVec 64, y + 0 = y := fun y => by simp
  cases v with
  | poison =>
    rw [show Arm64.addP T .poison 0 = .poison from rfl, retypeL_poison]; exact .poison _
  | ptr q =>
    have hc : q.convertible = false := by
      cases T <;> (try (rename_i w; cases w)) <;> simp_all [Val.hasTy]
    have hw : q.word = .ptr q := by simp [Ptr.word, hc]
    have hq : ({ blk := q.blk, off := q.off } : Ptr) = q := rfl
    simp only [Arm64.addP, PtrOps.ptrRes, Ptr.add, hz, hq]
    split
    · rw [hw]
      cases T with
      | ptr el => show Refines q.word _; rw [hw]; exact Refines.refl _
      | int w =>
        cases w <;> simp [Val.hasTy] at h
        show Refines q.word _; rw [hw]; exact Refines.refl _
      | _ => simp [Val.hasTy] at h
    · rw [retypeL_poison]; exact .poison _
  | int w x =>
    cases T with
    | int w' =>
      have : w = w' := by simpa [Val.hasTy] using h
      subst this
      simp only [Arm64.addP, Arm64.reg, hz]
      rw [retypeL_res_int, BitVec.setWidth_setWidth_of_le _ (by cases w <;> decide),
        BitVec.setWidth_eq]
      exact Refines.refl _
    | ptr el =>
      cases w <;> simp [Val.hasTy] at h
      simp only [Arm64.addP, Arm64.reg, Arm64.res, hz, BitVec.setWidth_eq]
      exact Refines.refl _
    | _ => simp [Val.hasTy] at h
  | bool b =>
    cases T <;> simp [Val.hasTy] at h
    cases b <;> exact Refines.refl _
  | _ => rw [show Arm64.addP T _ 0 = .poison from rfl, retypeL_poison]; exact .poison _

/-! ## Block controls -/

/-- Bit 0 of a register result read back at its shape: bit 0 of the register. -/
theorem reg_res_retypeL (T : Ty) (r x : BitVec 64)
    (h : Arm64.reg ((Arm64.res T r).retypeL T) = some x) : x.getLsbD 0 = r.getLsbD 0 := by
  cases T with
  | int w =>
    rw [retypeL_res_int] at h
    simp only [Arm64.reg, Option.some.injEq] at h
    subst h
    cases w <;> simp
  | bool =>
    have e : (Arm64.res .bool r).retypeL .bool = .bool (r.getLsbD 0) := rfl
    rw [e] at h
    simp only [Arm64.reg, Option.some.injEq] at h
    subst h
    cases r.getLsbD 0 <;> simp
  | ptr el =>
    have e : (Arm64.res (.ptr el) r).retypeL (.ptr el) = .int .w64 r := rfl
    rw [e] at h
    simp only [Arm64.reg, Option.some.injEq, BitVec.setWidth_eq] at h
    subst h; rfl
  | _ => exact absurd h (by simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Arm64.reg])

/-- `TBNZ [0]` on a `CSET` (`Equal`, `NotEqual`, …) of flags `f`: the condition on `f`. -/
theorem tbnz_cset {T : Ty} {op : Op} {f : Val} {ai : Int64} {b : Bool} (hai : ai.toInt = 0)
    (h : brVal .ARM64TBNZ ai ((Arm64.cset T op [f]).retypeL T) = some b) :
    (Cond.ofOp op).bind (·.onVal f) = some b := by
  have e : ∀ v, brVal .ARM64TBNZ ai v = (Arm64.reg v).map (fun x => x.getLsbD ai.toInt.toNat) :=
    fun _ => rfl
  rw [e, hai] at h
  rcases hcond : (Cond.ofOp op).bind (·.onVal f) with _ | c
  · have : Arm64.cset T op [f] = .poison := by simp only [Arm64.cset, hcond]
    rw [this, retypeL_poison] at h
    simp [Arm64.reg] at h
  · have : Arm64.cset T op [f] = Arm64.res T (if c then 1 else 0) := by
      simp only [Arm64.cset, hcond]
    rw [this] at h
    rcases ho : Arm64.reg ((Arm64.res T (if c = true then 1 else 0)).retypeL T) with _ | x <;>
      rw [ho] at h
    · simp at h
    · have := reg_res_retypeL T _ x ho
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      simp only [Int.toNat_zero, this]; cases c <;> rfl

/-- `If` on a `CSET` of flags `f`: the condition on `f`. -/
theorem if_cset {T : Ty} {op : Op} {f : Val} {ai : Int64} {b : Bool}
    (h : brVal .If ai ((Arm64.cset T op [f]).retypeL T) = some b) :
    (Cond.ofOp op).bind (·.onVal f) = some b := by
  have e : ∀ v, brVal .If ai v = (match v with | .bool b => some b | _ => none) := fun _ => rfl
  rw [e] at h
  rcases hcond : (Cond.ofOp op).bind (·.onVal f) with _ | c
  · have : Arm64.cset T op [f] = .poison := by simp only [Arm64.cset, hcond]
    rw [this, retypeL_poison] at h
    simp at h
  · have : Arm64.cset T op [f] = Arm64.res T (if c then 1 else 0) := by
      simp only [Arm64.cset, hcond]
    rw [this] at h
    cases T with
    | bool =>
      have e : (Arm64.res .bool (if c = true then 1 else 0)).retypeL .bool = .bool c := by
        cases c <;> rfl
      rw [e] at h; simpa using h
    | int w => rw [retypeL_res_int] at h; simp at h
    | _ => exact absurd h (by simp [Arm64.res, Val.retypeL, Val.widen, Val.retype])

/-- `If` on a boolean as `TBNZ [0]`. -/
theorem tbnz_of_if {v : Val} {ai ai' : Int64} {b : Bool} (hai : ai'.toInt = 0)
    (h : brVal .If ai v = some b) : brVal .ARM64TBNZ ai' v = some b := by
  have e : ∀ v, brVal .If ai v = (match v with | .bool b => some b | _ => none) := fun _ => rfl
  have e' : ∀ v, brVal .ARM64TBNZ ai' v =
      (Arm64.reg v).map (fun x => x.getLsbD ai'.toInt.toNat) := fun _ => rfl
  rw [e] at h
  rw [e', hai]
  cases v with
  | bool c =>
    simp only [Option.some.injEq] at h; subst h
    cases c <;> rfl
  | _ => simp at h

/-- `NZ` on a `CSET` of flags `f`: the condition on `f`. -/
theorem nz_cset {T : Ty} {op : Op} {f : Val} {ai : Int64} {b : Bool}
    (h : brVal .ARM64NZ ai ((Arm64.cset T op [f]).retypeL T) = some b) :
    (Cond.ofOp op).bind (·.onVal f) = some b := by
  have e : ∀ v, brVal .ARM64NZ ai v = (Arm64.isZero v).map (!·) := fun _ => rfl
  rw [e] at h
  rcases hcond : (Cond.ofOp op).bind (·.onVal f) with _ | c
  · have : Arm64.cset T op [f] = .poison := by simp only [Arm64.cset, hcond]
    rw [this, retypeL_poison] at h
    simp [Arm64.isZero, Arm64.reg] at h
  · have : Arm64.cset T op [f] = Arm64.res T (if c then 1 else 0) := by
      simp only [Arm64.cset, hcond]
    rw [this] at h
    cases T with
    | bool =>
      have e : (Arm64.res .bool (if c = true then 1 else 0)).retypeL .bool = .bool c := by
        cases c <;> rfl
      rw [e] at h; cases c <;> simpa [Arm64.isZero, Arm64.reg] using h
    | int w =>
      rw [retypeL_res_int] at h
      cases w <;> cases c <;>
        simpa (config := { decide := true }) [Arm64.isZero, Arm64.reg, Width.bits] using h
    | ptr el =>
      have e : (Arm64.res (.ptr el) (if c = true then 1 else 0)).retypeL (.ptr el) =
          .int .w64 (if c = true then 1 else 0) := rfl
      rw [e] at h; cases c <;>
        simpa (config := { decide := true }) [Arm64.isZero, Arm64.reg, Width.bits] using h
    | _ => exact absurd h (by simp [Arm64.res, Val.retypeL, Val.widen, Val.retype,
        Arm64.isZero, Arm64.reg])

/-- The arm64 flags kinds as their condition on the control. -/
theorem brVal_cond {k : BlockKind} {op : Op} {f : Val} {b : Bool} (ai : Int64)
    (hk : ∀ ai v, brVal k ai v = (Cond.ofOp op).bind (·.onVal v))
    (h : (Cond.ofOp op).bind (·.onVal f) = some b) : brVal k ai f = some (b != false) := by
  rw [hk, h, Bool.bne_false]

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
  have hact : actOp o = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht; exact ht.1.2
  have hl : ldOp? o = none := ldOp?_of_act hact
  simp only [termVL, hv, hg, hm, hl, ldarOp_of_act hact, Option.isSome_none, Bool.false_eq_true,
    ite_false, ht]

theorem termVL_ldar (o : Op) (hd : ldarOp o = true) :
    ∀ tabs (v : Value), v.op = o → termVL tabs v = true := by
  intro tabs v hv
  have hg : o.generic = false := by rcases ldarOp_cases hd with rfl | rfl | rfl <;> rfl
  have hm : (o == .ARM64MOVDaddr) = false := by rcases ldarOp_cases hd with rfl | rfl | rfl <;> rfl
  simp only [termVL, hv, hg, hm, ldOp?_of_ldar hd, hd, Option.isSome_none, Bool.false_eq_true,
    ite_false, ite_true]

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
  .inr (.inr (.inl ⟨o, o', hp, hr, hc, hb, hn⟩))

/-- A rule on a store (`ArmRule.Mem`). -/
theorem checked_store {r : Rule} {n ty ai ax ar args c}
    (hp : r.pat = .op .Store n ty ai ax ar args c) : ArmRule.Checked r :=
  .inr (.inr (.inr ⟨.Store, n, ty, ai, ax, ar, args, c, hp, .inl rfl⟩))

/-- A rule on a frame address (`ArmRule.Mem`). -/
theorem checked_localAddr {r : Rule} {n ty ai ax ar args c}
    (hp : r.pat = .op .LocalAddr n ty ai ax ar args c) : ArmRule.Checked r :=
  .inr (.inr (.inr ⟨.LocalAddr, n, ty, ai, ax, ar, args, c, hp, .inr (.inl rfl)⟩))

/-- A rule on an arm64 store (`ArmRule.Mem`). -/
theorem checked_armStore {r : Rule} {o n ty ai ax ar args c}
    (hp : r.pat = .op o n ty ai ax ar args c) (ho : (stSize o).isSome = true) :
    ArmRule.Checked r :=
  .inr (.inr (.inr ⟨o, n, ty, ai, ax, ar, args, c, hp, .inr (.inr (.inl ho))⟩))

/-- A rule on a lowered bounds panic (`ArmRule.Mem`, `pbAtom`). -/
theorem checked_pb {r : Rule} {o n ty ai ax ar args c}
    (hp : r.pat = .op o n ty ai ax ar args c) (ho : pbAtom o = true) :
    ArmRule.Checked r :=
  .inr (.inr (.inr ⟨o, n, ty, ai, ax, ar, args, c, hp, .inr (.inr (.inr (.inl ho)))⟩))

/-- A rule on a `Zero` (`ArmRule.Mem`). -/
theorem checked_zero {r : Rule} {n ty ai ax ar args c}
    (hp : r.pat = .op .Zero n ty ai ax ar args c) : ArmRule.Checked r :=
  .inr (.inr (.inr ⟨.Zero, n, ty, ai, ax, ar, args, c, hp, .inr (.inr (.inr (.inr rfl)))⟩))

end GoFV.Proof.Low.Rules
