import GoFV.SSA.Sem.Run

/-!
# cse: commutative ops ignore the order of their first two arguments

`evalOp_swap`: for an op with `Op.commutative` (the ops cse may compare with their first two
arguments swapped, `CSE.swappable`), swapping the first two evaluated arguments does not change
the result. All 55 such ops reach `evalPure`; the float ops and `Add32carry`,
`Add32withcarry`, `Add32carrywithcarry` are `poison` there (later phases), the others are
symmetric in their first two arguments family by family (`int2_swap`, `bool2_swap`,
`eqPtr_swap`, `memEq_swap`, `addcarry_swap`).

The 446-constructor `Op` is split once per lemma by `cases`, the non-commutative cases closed
by evaluating `Op.commutative` on the constructor, the others by naming their family (never
`simp` on an op variable, LEARNINGS). Definitions are opened by `delta` + `dsimp only`, so this
module realizes no equation lemmas of `Sem` definitions.

`GoFV.Proof.Rules.Comm` proves the phase-P1 part for the rule interpreter (`int2_comm`, …);
it is not imported here: it sits behind `import Lean` and the rule tables.
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem

/-! ## Families -/

theorem int2_swap {w : Width} {f : BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y, f x y = f y x) (a b : Val) (rest : List Val) :
    int2 w f (b :: a :: rest) = int2 w f (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta int2; dsimp only
    cases b.asInt w <;> cases a.asInt w <;> first | rfl | exact hf _ _
  | cons _ _ => rfl

theorem bool2_swap {f : Bool → Bool → Bool} (hf : ∀ x y, f x y = f y x) (a b : Val)
    (rest : List Val) : bool2 f (b :: a :: rest) = bool2 f (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta bool2; dsimp only
    cases b.asBool <;> cases a.asBool <;> first | rfl | exact congrArg Val.bool (hf _ _)
  | cons _ _ => rfl

theorem Ptr.eq_comm (p q : Ptr) : p.eq q = q.eq p := by
  delta Ptr.eq
  by_cases hb : p.blk = q.blk
  · rw [beq_iff_eq.2 hb, beq_iff_eq.2 hb.symm]
    exact BEq.comm
  · rw [beq_eq_false_iff_ne.2 hb, beq_eq_false_iff_ne.2 (Ne.symm hb)]
    cases p.addr? <;> cases q.addr? <;> first | rfl | exact BEq.comm

theorem eqPtr_swap (neg : Bool) (a b : Val) (rest : List Val) :
    PtrOps.eqPtr neg (b :: a :: rest) = PtrOps.eqPtr neg (a :: b :: rest) := by
  cases rest with
  | nil =>
    delta PtrOps.eqPtr; dsimp only
    cases b.asPtrWord <;> cases a.asPtrWord <;>
      first | rfl | exact congrArg (fun t => Val.bool (t != neg)) (Ptr.eq_comm _ _)
  | cons _ _ => rfl

theorem memEq_swap (a b : Val) (rest : List Val) :
    memEq (b :: a :: rest) = memEq (a :: b :: rest) := by
  cases b <;> cases a <;> try rfl
  rename_i q p
  rcases rest with _ | ⟨c, rest⟩
  · rfl
  cases c <;> try rfl
  rename_i n
  rcases rest with _ | ⟨d, rest⟩
  · rfl
  cases d <;> try rfl
  rename_i m
  rcases rest with _ | ⟨e, rest⟩
  · delta memEq; dsimp only
    cases m.read p n.toNat <;> cases m.read q n.toNat <;>
      first | rfl | simp only [Bool.or_comm, BEq.comm]
  · rfl

theorem addcarry_swap (a b : Val) (rest : List Val) :
    Sem.Int.addcarry (b :: a :: rest) = Sem.Int.addcarry (a :: b :: rest) := by
  match rest with
  | [c] =>
    delta Sem.Int.addcarry int3; dsimp only
    cases b.asInt .w64 <;> cases a.asInt .w64 <;> cases c.asInt .w64 <;>
      first | rfl | (dsimp only; rw [Nat.add_comm (BitVec.toNat _) (BitVec.toNat _)])
  | [] => rfl
  | _ :: _ :: _ => rfl

/-! ## Integer and boolean families -/

theorem add_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.add w (b :: a :: rest) = Sem.Int.add w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.add_comm x]) a b rest

theorem mul_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.mul w (b :: a :: rest) = Sem.Int.mul w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.mul_comm x]) a b rest

theorem and_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.and w (b :: a :: rest) = Sem.Int.and w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.and_comm x]) a b rest

theorem or_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.or w (b :: a :: rest) = Sem.Int.or w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.or_comm x]) a b rest

theorem xor_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.xor w (b :: a :: rest) = Sem.Int.xor w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.xor_comm x]) a b rest

theorem hmul_swap (w : Width) (signed : Bool) (a b : Val) (rest : List Val) :
    Sem.Int.hmul w signed (b :: a :: rest) = Sem.Int.hmul w signed (a :: b :: rest) :=
  int2_swap (fun x _ => by
    dsimp only; rw [BitVec.mul_comm (x.signExtend _), BitVec.mul_comm (x.setWidth _)]) a b rest

theorem mulhilo_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.mulhilo w (b :: a :: rest) = Sem.Int.mulhilo w (a :: b :: rest) :=
  int2_swap (fun x _ => by dsimp only; rw [BitVec.mul_comm (x.setWidth _)]) a b rest

theorem mulover_swap (w : Width) (a b : Val) (rest : List Val) :
    Sem.Int.mulover w (b :: a :: rest) = Sem.Int.mulover w (a :: b :: rest) :=
  int2_swap (fun x _ => by rw [BitVec.mul_comm x, Nat.mul_comm x.toNat]) a b rest

theorem eq_swap (w : Width) (a b : Val) (rest : List Val) :
    Cmp.eq w (b :: a :: rest) = Cmp.eq w (a :: b :: rest) :=
  int2_swap (fun _ _ => congrArg Val.bool BEq.comm) a b rest

theorem neq_swap (w : Width) (a b : Val) (rest : List Val) :
    Cmp.neq w (b :: a :: rest) = Cmp.neq w (a :: b :: rest) :=
  int2_swap (fun _ _ => congrArg Val.bool bne_comm) a b rest

theorem andB_swap (a b : Val) (rest : List Val) :
    Cmp.andB (b :: a :: rest) = Cmp.andB (a :: b :: rest) :=
  bool2_swap Bool.and_comm a b rest

theorem orB_swap (a b : Val) (rest : List Val) :
    Cmp.orB (b :: a :: rest) = Cmp.orB (a :: b :: rest) :=
  bool2_swap Bool.or_comm a b rest

theorem eqB_swap (a b : Val) (rest : List Val) :
    Cmp.eqB (b :: a :: rest) = Cmp.eqB (a :: b :: rest) :=
  bool2_swap (fun _ _ => BEq.comm) a b rest

theorem neqB_swap (a b : Val) (rest : List Val) :
    Cmp.neqB (b :: a :: rest) = Cmp.neqB (a :: b :: rest) :=
  bool2_swap (fun _ _ => bne_comm) a b rest

/-! ## `evalPure` and `evalOp` -/

theorem evalPure_swap {op : Op} {ty : Ty} {auxInt : Int64} {aux : Option AuxRef} {a b : Val}
    {rest : List Val} (h : op.commutative = true) :
    evalPure op ty auxInt aux (b :: a :: rest) = evalPure op ty auxInt aux (a :: b :: rest) := by
  cases op
  all_goals first | exact absurd h Bool.false_ne_true | skip
  case Add8 => exact add_swap .w8 a b rest
  case Add16 => exact add_swap .w16 a b rest
  case Add32 => exact add_swap .w32 a b rest
  case Add64 => exact add_swap .w64 a b rest
  case Mul8 => exact mul_swap .w8 a b rest
  case Mul16 => exact mul_swap .w16 a b rest
  case Mul32 => exact mul_swap .w32 a b rest
  case Mul64 => exact mul_swap .w64 a b rest
  case Hmul32 => exact hmul_swap .w32 true a b rest
  case Hmul32u => exact hmul_swap .w32 false a b rest
  case Hmul64 => exact hmul_swap .w64 true a b rest
  case Hmul64u => exact hmul_swap .w64 false a b rest
  case Mul32uhilo => exact mulhilo_swap .w32 a b rest
  case Mul64uhilo => exact mulhilo_swap .w64 a b rest
  case Mul32uover => exact mulover_swap .w32 a b rest
  case Mul64uover => exact mulover_swap .w64 a b rest
  case And8 => exact and_swap .w8 a b rest
  case And16 => exact and_swap .w16 a b rest
  case And32 => exact and_swap .w32 a b rest
  case And64 => exact and_swap .w64 a b rest
  case Or8 => exact or_swap .w8 a b rest
  case Or16 => exact or_swap .w16 a b rest
  case Or32 => exact or_swap .w32 a b rest
  case Or64 => exact or_swap .w64 a b rest
  case Xor8 => exact xor_swap .w8 a b rest
  case Xor16 => exact xor_swap .w16 a b rest
  case Xor32 => exact xor_swap .w32 a b rest
  case Xor64 => exact xor_swap .w64 a b rest
  case Eq8 => exact eq_swap .w8 a b rest
  case Eq16 => exact eq_swap .w16 a b rest
  case Eq32 => exact eq_swap .w32 a b rest
  case Eq64 => exact eq_swap .w64 a b rest
  case Neq8 => exact neq_swap .w8 a b rest
  case Neq16 => exact neq_swap .w16 a b rest
  case Neq32 => exact neq_swap .w32 a b rest
  case Neq64 => exact neq_swap .w64 a b rest
  case EqPtr => exact eqPtr_swap false a b rest
  case NeqPtr => exact eqPtr_swap true a b rest
  case AndB => exact andB_swap a b rest
  case OrB => exact orB_swap a b rest
  case EqB => exact eqB_swap a b rest
  case NeqB => exact neqB_swap a b rest
  case Add64carry => exact addcarry_swap a b rest
  case MemEq => exact memEq_swap a b rest
  -- `poison` in phases P1/P2: floats and the 32-bit carry chain.
  all_goals rfl

/-- A commutative op is evaluated by `evalPure` (unless `frameVal` or `isRoot` decides). -/
theorem evalOp_pure {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {args : List Val} {ty : Ty}
    (h : v.op.commutative = true) :
    evalOp env ctx fr v args ty =
      match frameVal ctx v with
      | some x => pure x
      | none =>
        if isRoot v.op then .stuck s!"v{v.id}: {v.op.name} is not in phases P1/P2"
        else pure (evalPure v.op ty v.auxInt v.aux args) := by
  delta evalOp
  generalize v.op = op at h ⊢
  cases op <;> first | exact absurd h Bool.false_ne_true | rfl

/-- Swapping the first two evaluated arguments of a commutative op keeps its result. -/
theorem evalOp_swap {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {a b : Val}
    {rest : List Val} {ty : Ty} (h : v.op.commutative = true) :
    evalOp env ctx fr v (b :: a :: rest) ty = evalOp env ctx fr v (a :: b :: rest) ty := by
  rw [evalOp_pure h, evalOp_pure h, evalPure_swap h]

/-! ## Non-vacuity -/

/-- A value of op `op` (the other fields are irrelevant to `evalOp` here). -/
private def valueOf (op : Op) : Value := { (default : Value) with op }

/-- Non-vacuity: `Add64` is commutative, `2 + 1 = 3` evaluates and `evalOp_swap` gives
`1 + 2 = 3`. -/
theorem evalOp_swap_witness (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) :
    evalOp env ctx fr (valueOf .Add64) [.i64 2, .i64 1] ty = .ok (.i64 3) ∧
    evalOp env ctx fr (valueOf .Add64) [.i64 1, .i64 2] ty = .ok (.i64 3) := by
  have h : evalOp env ctx fr (valueOf .Add64) [.i64 2, .i64 1] ty = .ok (.i64 3) := by rfl
  exact ⟨h, (evalOp_swap (v := valueOf .Add64) (a := .i64 2) (b := .i64 1) (rest := [])
    rfl).trans h⟩

/-- The hypothesis matters: `Sub64` is not commutative and `2 - 1 ≠ 1 - 2`. -/
theorem evalOp_swap_sub64 (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) :
    evalOp env ctx fr (valueOf .Sub64) [.i64 2, .i64 1] ty ≠
      evalOp env ctx fr (valueOf .Sub64) [.i64 1, .i64 2] ty := by
  have h1 : evalOp env ctx fr (valueOf .Sub64) [.i64 2, .i64 1] ty = .ok (.i64 1) := by rfl
  have h2 : evalOp env ctx fr (valueOf .Sub64) [.i64 1, .i64 2] ty = .ok (.i64 (-1)) := by rfl
  rw [h1, h2]
  intro h
  have := congrArg (fun r : Res Val => match r with | .ok (.int _ x) => x.toNat | _ => 0) h
  exact absurd this (by decide)

end GoFV.Proof.CSE
