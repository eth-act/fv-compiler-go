import GoFV.Proof.Pass.CSEComm
import GoFV.Proof.Pass.CSEOp
import GoFV.Proof.EvalL
import GoFV.Opt.LoweredCSECheck
import GoFV.Proof.EvalOpLDispatch

/-!
# lowered cse: facts about `evalOpL` at single ops

`runL` evaluates an op with `evalOpL` (mode `faulting = false`):

* `evalOpL_tail`: an arm64 op outside `CSEL.arm64Act` is `Arm64.evalPure` (or `atomicRoot`, for
  a root);
* `evalOpL_swap`: a commutative op ignores the order of its first two arguments (the generic ones
  by Phase 1's `evalOp_swap`, the arm64 ones family by family, `armEvalPure_swap`; `ADD` of two
  pointers adds their addresses);
* `evalOpL_ok_id`: two values with the same op (in `CSEL.substOp`), aux, auxint and first
  argument's producer give the same result on the same arguments when both evaluate;
* `evalOpL_total`: a non-root value other than `Arg`/`ArgIntReg` evaluates.

`Op` is split by `cases` once per lemma, the cases outside the lemma closed by evaluating a
`Bool` predicate on the constructor (never `simp` on an op variable, LEARNINGS).
-/

namespace GoFV.Proof.CSEL

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-! ## Families -/

theorem op2_swap {ty : Ty} {g : BitVec 64 → BitVec 64 → BitVec 64} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.op2 ty g (b :: a :: rest) = Arm64.op2 ty g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.op2; dsimp only
    cases Arm64.reg b <;> cases Arm64.reg a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem op2w_swap {ty : Ty} {g : BitVec 32 → BitVec 32 → BitVec 32} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.op2w ty g (b :: a :: rest) = Arm64.op2w ty g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.op2w; dsimp only
    cases Arm64.reg32 b <;> cases Arm64.reg32 a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem flags2_swap {g : BitVec 64 → BitVec 64 → Flags} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.flags2 g (b :: a :: rest) = Arm64.flags2 g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.flags2; dsimp only
    cases Arm64.reg b <;> cases Arm64.reg a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem flags2w_swap {g : BitVec 32 → BitVec 32 → Flags} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.flags2w g (b :: a :: rest) = Arm64.flags2w g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.flags2w; dsimp only
    cases Arm64.reg32 b <;> cases Arm64.reg32 a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem cmp2_swap {g : BitVec 64 → BitVec 64 → BitVec 64 × Flags} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.cmp2 g (b :: a :: rest) = Arm64.cmp2 g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.cmp2; dsimp only
    cases Arm64.reg b <;> cases Arm64.reg a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem cmpP_swap {g : BitVec 64 → BitVec 64 → BitVec 64 × Flags} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.cmpP g (b :: a :: rest) = Arm64.cmpP g (a :: b :: rest) := by
  cases rest with
  | nil =>
    unfold Arm64.cmpP; dsimp only
    cases ha : Arm64.reg a <;> cases hb : Arm64.reg b <;> dsimp only <;>
      (cases a <;> cases b <;> simp_all [Arm64.reg, hg])
  | cons _ _ => rfl

theorem cmp2w_swap {g : BitVec 32 → BitVec 32 → BitVec 32 × Flags} (hg : ∀ x y, g x y = g y x)
    (a b : Val) (rest : List Val) :
    Arm64.cmp2w g (b :: a :: rest) = Arm64.cmp2w g (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.cmp2w; dsimp only
    cases Arm64.reg32 b <;> cases Arm64.reg32 a <;> dsimp only <;> first | rfl | exact congrArg _ (hg _ _)
  | cons _ _ => rfl

theorem addWithCarry_comm {n : Nat} (x y : BitVec n) (c : Bool) :
    addWithCarry x y c = addWithCarry y x c := by
  unfold addWithCarry
  rw [Nat.add_comm x.toNat, Int.add_comm x.toInt]

theorem adds_swap (ty : Ty) (a b : Val) (rest : List Val) :
    Arm64.adds ty (b :: a :: rest) = Arm64.adds ty (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta Arm64.adds; dsimp only
    cases Arm64.reg b <;> cases Arm64.reg a <;>
      dsimp only <;> first | rfl | exact congrArg _ (addWithCarry_comm _ _ _)
  | cons _ _ => rfl

theorem adcs_swap (ty : Ty) (a b : Val) (rest : List Val) :
    Arm64.adcs ty (b :: a :: rest) = Arm64.adcs ty (a :: b :: rest) := by
  match rest with
  | [c] =>
    delta Arm64.adcs; dsimp only
    cases Arm64.reg b <;> cases Arm64.reg a <;> cases Arm64.carry c <;>
      dsimp only <;> first | rfl | exact congrArg _ (addWithCarry_comm _ _ _)
  | [] => rfl
  | _ :: _ :: _ => rfl

theorem add_swap (ty : Ty) (a b : Val) (rest : List Val) :
    Arm64.add ty (b :: a :: rest) = Arm64.add ty (a :: b :: rest) := by
  cases rest with
  | nil =>
    cases a <;> cases b <;> (delta Arm64.add; dsimp only) <;>
      first | rfl | exact op2_swap (fun x y => BitVec.add_comm x y) _ _ []
  | cons _ _ => cases a <;> cases b <;> rfl

theorem fbin_swap (w : Width)
    {g : (f : GoFV.IEEE.Fmt) → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f}
    (hg : ∀ f x y, g f x y = g f y x) (a b : Val) (rest : List Val) :
    FOps.bin g w (b :: a :: rest) = FOps.bin g w (a :: b :: rest) := by
  cases w with
  | w32 => exact CSE.int2_swap (w := .w32) (fun x y => congrArg _ (hg .b32 x y)) a b rest
  | w64 => exact CSE.int2_swap (w := .w64) (fun x y => congrArg _ (hg .b64 x y)) a b rest
  | _ => rfl

theorem fadd_swap (w : Width) (a b : Val) (rest : List Val) :
    Arm64.fop w FOps.add (b :: a :: rest) = Arm64.fop w FOps.add (a :: b :: rest) := by
  delta Arm64.fop FOps.add
  simp only [List.map_cons]
  exact fbin_swap w (fun _ x y => FOps.ordered_comm _ x y) _ _ _

theorem fmul_swap (w : Width) (a b : Val) (rest : List Val) :
    Arm64.fop w FOps.mul (b :: a :: rest) = Arm64.fop w FOps.mul (a :: b :: rest) := by
  delta Arm64.fop FOps.mul
  simp only [List.map_cons]
  exact fbin_swap w (fun _ x y => FOps.ordered_comm _ x y) _ _ _

theorem fnmul_swap (w : Width) (a b : Val) (rest : List Val) :
    Arm64.fnmul w (b :: a :: rest) = Arm64.fnmul w (a :: b :: rest) := by
  delta Arm64.fnmul; rw [fmul_swap]

/-! ## `Arm64.evalPure` and `evalOpL` -/

/-- **The commutative arm64 ops are symmetric** in their first two arguments (a commutative
generic op is `poison` in `Arm64.evalPure`). -/
theorem armEvalPure_swap {op : Op} {ty : Ty} {k : Int64} {aux : Option AuxRef} {a b : Val}
    {rest : List Val} (h : op.commutative = true) :
    Arm64.evalPure op ty k aux (b :: a :: rest) = Arm64.evalPure op ty k aux (a :: b :: rest) := by
  cases op
  all_goals first | exact absurd h Bool.false_ne_true | skip
  case ARM64ADD => exact add_swap ty a b rest
  case ARM64ADDSflags => exact adds_swap ty a b rest
  case ARM64ADCSflags => exact adcs_swap ty a b rest
  case ARM64MUL => exact op2_swap (fun x y => BitVec.mul_comm x y) a b rest
  case ARM64MULW => exact op2w_swap (fun x y => BitVec.mul_comm x y) a b rest
  case ARM64MNEG => exact op2_swap (fun x y => by rw [BitVec.mul_comm x]) a b rest
  case ARM64MNEGW => exact op2w_swap (fun x y => by rw [BitVec.mul_comm x]) a b rest
  case ARM64MULH =>
    exact op2_swap (fun x y => by delta Arm64.smulh; rw [BitVec.mul_comm (x.signExtend _)]) a b rest
  case ARM64UMULH =>
    exact op2_swap (fun x y => by delta Arm64.umulh; rw [BitVec.mul_comm (x.setWidth _)]) a b rest
  case ARM64MULL =>
    exact op2_swap (fun x y => by delta Arm64.smull; rw [BitVec.mul_comm]) a b rest
  case ARM64UMULL =>
    exact op2_swap (fun x y => by delta Arm64.umull; rw [BitVec.mul_comm]) a b rest
  case ARM64AND => exact op2_swap (fun x y => BitVec.and_comm x y) a b rest
  case ARM64OR => exact op2_swap (fun x y => BitVec.or_comm x y) a b rest
  case ARM64XOR => exact op2_swap (fun x y => BitVec.xor_comm x y) a b rest
  case ARM64CMN =>
    exact cmpP_swap (fun x y => addWithCarry_comm x y false) a b rest
  case ARM64CMNW =>
    exact cmp2w_swap (fun x y => addWithCarry_comm x y false) a b rest
  case ARM64TST => exact flags2_swap (fun x y => by rw [BitVec.and_comm x]) a b rest
  case ARM64TSTW => exact flags2w_swap (fun x y => by rw [BitVec.and_comm x]) a b rest
  case ARM64FADDS => exact fadd_swap .w32 a b rest
  case ARM64FADDD => exact fadd_swap .w64 a b rest
  case ARM64FMULS => exact fmul_swap .w32 a b rest
  case ARM64FMULD => exact fmul_swap .w64 a b rest
  case ARM64FNMULS => exact fnmul_swap .w32 a b rest
  case ARM64FNMULD => exact fnmul_swap .w64 a b rest
  -- the generic commutative ops: `poison`
  all_goals rfl

/-- A commutative op is not a root and not evaluated with the activation. -/
theorem comm_plain {op : Op} (h : op.commutative = true) :
    isRoot op = false ∧ CSEL.arm64Act op = false := by
  cases op <;> first | exact absurd h Bool.false_ne_true | exact ⟨by decide, rfl⟩

/-- `CSEL.arm64Act` is `LowerTerm.actOp` (`evalOpL_eq`): the same 91 ops. -/
private theorem arm64Act_eq_actOp (op : Op) :
    GoFV.Opt.CSEL.arm64Act op = GoFV.Opt.LowerTerm.actOp op := by
  cases op <;> rfl

/-- An arm64 op outside `CSEL.arm64Act` is `Arm64.evalPure` (`atomicRoot` for a root). -/
theorem evalOpL_tail {fl : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (ha : CSEL.arm64Act v.op = false) :
    evalOpL fl env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  exact evalOpL_of_not_actOp hg (by rw [← arm64Act_eq_actOp]; exact ha)

/-- **Swapping the first two arguments of a commutative op keeps its lowered result.** -/
theorem evalOpL_swap {fl : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {a b : Val}
    {rest : List Val} {ty : Ty} (h : v.op.commutative = true) :
    evalOpL fl env ctx fr v (b :: a :: rest) ty = evalOpL fl env ctx fr v (a :: b :: rest) ty := by
  cases hg : v.op.generic
  · obtain ⟨hr, ha⟩ := comm_plain h
    rw [evalOpL_tail hg ha, evalOpL_tail hg ha, hr]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [armEvalPure_swap h]
  · rw [evalOpL_generic _ _ _ _ _ _ hg, evalOpL_generic _ _ _ _ _ _ hg]
    exact CSE.evalOp_swap h

/-! ## ID independence -/

/-- The activation ops of `CSEL.actOK` do not read the value's ID. -/
theorem arm64Op_id {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} (i : ID)
    (h : CSEL.actOK u.op = true) (argv : List Val) (ty : Ty) :
    arm64Op false env ctx fr { u with id := i } argv ty = arm64Op false env ctx fr u argv ty := by
  obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := u
  dsimp only at h ⊢
  cases op <;> first | exact absurd h Bool.false_ne_true | rfl

/-- An arm64 op of `CSEL.arm64Act` is `arm64Op`. -/
theorem evalOpL_act {fl : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (ha : CSEL.arm64Act v.op = true) :
    evalOpL fl env ctx fr v argv ty = arm64Op fl env ctx fr v argv ty := by
  exact evalOpL_of_actOp hg (by rw [← arm64Act_eq_actOp]; exact ha)

theorem isRoot_of_substOp {op : Op} (hs : CSEL.substOp op = true)
    (hn : op ≠ .ARM64LoweredNilCheck) (hm : op ≠ .ARM64LoweredMemEq) : isRoot op = false := by
  simp only [CSEL.substOp, Bool.or_eq_true, beq_iff_eq, hn, hm, false_or, Bool.and_eq_true,
    Bool.not_eq_true'] at hs
  exact hs.1

/-- `LoweredMemEq` is `memEq` of its arguments. -/
theorem arm64Op_memEq {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .ARM64LoweredMemEq) :
    arm64Op false env ctx fr v argv ty = .ok (memEq argv) := by
  obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := v
  dsimp only at hop
  subst hop
  rfl

/-- A `LoweredNilCheck` that evaluates returns its first argument (Phase 1's `NilCheck`). -/
theorem arm64Op_nilCheck_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {r : Val} (hop : v.op = .ARM64LoweredNilCheck)
    (h : arm64Op false env ctx fr v argv ty = .ok r) : ∃ rest, argv = r :: rest := by
  have e : arm64Op false env ctx fr v argv ty =
      evalOp env ctx fr { v with op := .NilCheck } argv ty := by
    obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := v
    dsimp only at hop
    subst hop
    rfl
  rw [e] at h
  exact CSE.evalOp_nilCheck_ok rfl h

/-- **Two values of a `CSEL.substOp` op with the same aux, auxint and first argument's producer
that both evaluate on the same arguments give the same result**: the ID occurs only in `stuck`
messages, a `LoweredNilCheck` returns its pointer. -/
theorem evalOpL_ok_id {env : Env} {ctx : Ctx} {fr : Frame} {u v : Value} {argv : List Val}
    {ty : Ty} {r1 r2 : Val} (hop : v.op = u.op) (hax : v.aux = u.aux) (hai : v.auxInt = u.auxInt)
    (hsx : sxOf ctx.f v = sxOf ctx.f u) (hs : CSEL.substOp u.op = true)
    (h1 : evalOpL false env ctx fr u argv ty = .ok r1)
    (h2 : evalOpL false env ctx fr v argv ty = .ok r2) : r1 = r2 := by
  by_cases hn : u.op = .ARM64LoweredNilCheck
  · have hg : u.op.generic = false := by rw [hn]; rfl
    have ha : CSEL.arm64Act u.op = true := by rw [hn]; rfl
    rw [evalOpL_act hg ha] at h1
    rw [evalOpL_act (hop ▸ hg) (hop ▸ ha)] at h2
    obtain ⟨rest1, e1⟩ := arm64Op_nilCheck_ok hn h1
    obtain ⟨rest2, e2⟩ := arm64Op_nilCheck_ok (hop.trans hn) h2
    rw [e1] at e2; cases e2; rfl
  by_cases hm : u.op = .ARM64LoweredMemEq
  · have hg : u.op.generic = false := by rw [hm]; rfl
    have ha : CSEL.arm64Act u.op = true := by rw [hm]; rfl
    rw [evalOpL_act hg ha, arm64Op_memEq hm] at h1
    rw [evalOpL_act (hop ▸ hg) (hop ▸ ha), arm64Op_memEq (hop.trans hm)] at h2
    exact Res.ok.inj (h1.symm.trans h2)
  have hr := isRoot_of_substOp hs hn hm
  cases hg : u.op.generic
  · cases ha : CSEL.arm64Act u.op
    · rw [evalOpL_tail hg ha, hr] at h1
      rw [evalOpL_tail (hop ▸ hg) (hop ▸ ha), hop, hr, hax, hai] at h2
      exact Res.ok.inj (h1.symm.trans h2)
    · have hok : CSEL.actOK u.op = true := by
        simp only [CSEL.substOp, Bool.or_eq_true, beq_iff_eq, hn, hm, false_or, hg, ha, hr,
          Bool.not_false, Bool.true_and, Bool.false_or, Bool.not_true] at hs
        exact hs
      have e : evalOpL false env ctx fr v argv ty =
          evalOpL false env ctx fr { u with id := v.id } argv ty :=
        evalOpL_congr (by rw [hop]) hax hai rfl rfl rfl rfl (by rw [hsx]; rfl)
      rw [e, evalOpL_act (v := { u with id := v.id }) hg ha, arm64Op_id _ hok] at h2
      rw [evalOpL_act hg ha] at h1
      exact Res.ok.inj (h1.symm.trans h2)
  · rw [evalOpL_generic _ _ _ _ _ _ hg] at h1
    rw [evalOpL_generic _ _ _ _ _ _ (hop ▸ hg)] at h2
    exact CSE.evalOp_ok_id hop hax hai hr h1 h2

/-! ## Totality -/

/-- The non-root activation ops evaluate. -/
theorem arm64Op_total {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ha : CSEL.arm64Act v.op = true) (hr : isRoot v.op = false) :
    ∃ r, arm64Op false env ctx fr v argv ty = .ok r := by
  exact arm64Op_total_of_actOp (by rw [← arm64Act_eq_actOp]; exact ha) hr

/-- **A non-root lowered value evaluates**, unless it is `Arg`/`ArgIntReg` (a parameter
lookup). -/
theorem evalOpL_total {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hr : isRoot v.op = false) (ha : v.op ≠ .Arg) (hb : v.op ≠ .ArgIntReg) :
    ∃ r, evalOpL false env ctx fr v argv ty = .ok r := by
  cases hg : v.op.generic
  · cases hact : CSEL.arm64Act v.op
    · rw [evalOpL_tail hg hact, hr]; exact ⟨_, rfl⟩
    · rw [evalOpL_act hg hact]; exact arm64Op_total hact hr
  · rw [evalOpL_generic _ _ _ _ _ _ hg]
    exact CSE.evalOp_total hr ha hb

end GoFV.Proof.CSEL
