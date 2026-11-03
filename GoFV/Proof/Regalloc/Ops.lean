import GoFV.Proof.Regalloc.Match

/-!
# Regalloc checker soundness: the ops the checker reasons about

What `evalOpL` gives for the ops whose results the checker relates beyond "same op, same
arguments": frame constants (`kOp`: activation-only values, never `stuck` or a panic, read of the
value only its op, aux and auxint), pure arm64 ops (`Arm64.evalPure`, no ID), selectors
(`selRes`: one component of the tuple), `MOVDreg`/`MOVDnop` (`movdRes`, `movdLoc`),
`MakeResult`, `Copy`, `KeepAlive`, `VarLive`.
-/

-- Parallel elaboration (-j4) wrote this module's constants in a different order on every build
-- (3 builds, 3 hashes), so importers missed the shared cache (#1; LEARNINGS.md).
set_option Elab.async false

namespace GoFV.Proof.RA

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RegallocCheck

/-- A selector's result: component `i` of its one argument. -/
def selRes (i : Nat) : List Val → Val
  | [x] => comp (some i) x
  | _ => .poison

/-- `MOVDreg`/`MOVDnop` with sign extension `sx` (`arm64Op`, `movdLoc`). -/
def movdRes (sx : Bool) (argv : List Val) (ty : Ty) : Val :=
  match argv with
  | [a] =>
    match a with
    | .int _ x => Arm64.res ty (if sx then x.signExtend 64 else x.setWidth 64)
    | a => Arm64.regVal ty a
  | _ => .poison

/-- An op that faults on no nil argument accesses nothing `nilFaults` checks. -/
theorem nilFaults_none {fa : Bool} {ctx : Ctx} {v : Value} {argv : List Val}
    (h0 : v.op.faultOnNilArg0 = false) (h1 : v.op.faultOnNilArg1 = false) :
    nilFaults fa ctx v argv = none := by
  have hacc : nilAccesses ctx v argv = [] := by
    unfold nilAccesses
    simp [h0, h1]
  unfold nilFaults
  rw [hacc]
  split
  · rfl
  · split <;> simp

theorem kOp_cases {op : Op} (h : kOp op = true) :
    op = .ARM64MOVDconst ∨ op = .ARM64FMOVSconst ∨ op = .ARM64FMOVDconst ∨
      op = .ARM64LoweredGetCallerPC ∨ op = .ARM64MOVDaddr ∨ op = .ARM64ZERO ∨ op = .SP ∨
      op = .SB := by
  unfold kOp at h
  split at h <;> simp_all

/-- A frame constant's op (`kOp`), evaluated. -/
def kRes (ctx : Ctx) (v : Value) (argv : List Val) (ty : Ty) : Val :=
  match v.op with
  | .SP => .ptr ⟨.outargs ctx.act, 0⟩
  | .SB => evalPure .SB ty v.auxInt v.aux argv
  | .ARM64MOVDaddr => match argv with
    | [a] => (symAddr ctx v a).elim .poison PtrOps.ptrRes
    | _ => .poison
  | op => Arm64.evalPure op ty v.auxInt v.aux argv

theorem evalOpL_kop_eq {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hk : kOp v.op = true) :
    evalOpL fa env ctx fr v argv ty = .ok (kRes ctx v argv ty) := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := v
  dsimp only at hk
  rcases kOp_cases hk with h | h | h | h | h | h | h | h <;> subst h
  all_goals first
    | (rw [evalOpL_pure (by decide)]; rfl)
    | (simp only [evalOpL, evalOp, frameVal, kRes, show Op.generic .SP = true from by decide,
        show Op.generic .SB = true from by decide, show isRoot .SB = false from by decide,
        ite_true, Bool.false_eq_true, ite_false]; rfl)
    | skip
  simp only [evalOpL, show Op.generic .ARM64MOVDaddr = false from by decide, Bool.false_eq_true,
    ite_false]
  unfold arm64Op
  have hnf : ∀ w : Value, w.op = .ARM64MOVDaddr → nilFaults fa ctx w argv = none := by
    intro w hw
    exact nilFaults_none (by rw [hw]; decide) (by rw [hw]; decide)
  rw [hnf _ rfl]
  simp only [kRes]
  match argv with
  | [] => rfl
  | [a] => rfl
  | _ :: _ :: _ => rfl

theorem kRes_congr {ctx ctx' : Ctx} {v v' : Value} {argv : List Val} {ty : Ty}
    (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt)
    (htabs : ctx'.tabs = ctx.tabs) (hact : ctx'.act = ctx.act) :
    kRes ctx' v' argv ty = kRes ctx v argv ty := by
  unfold kRes symAddr
  rw [hop, haux, hai, htabs, hact]

/-- A frame constant's op reads of the value its op, aux and auxint only, of the context its
tables and activation, and is never `stuck` or a panic. -/
theorem evalOpL_kop {fa : Bool} {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value}
    {argv : List Val} {ty : Ty} (hk : kOp v.op = true) (hop : v'.op = v.op)
    (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt) (htabs : ctx'.tabs = ctx.tabs)
    (hact : ctx'.act = ctx.act) :
    evalOpL fa env ctx' fr' v' argv ty = evalOpL fa env ctx fr v argv ty := by
  rw [evalOpL_kop_eq hk, evalOpL_kop_eq (hop ▸ hk), kRes_congr hop haux hai htabs hact]

theorem evalOpL_pure {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hp : pureArm64 v.op = true) :
    evalOpL fa env ctx fr v argv ty = .ok (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  have hg : v.op.generic = false := by
    unfold pureArm64 at hp; revert hp; cases v.op.generic <;> simp
  have hr : isRoot v.op = false := by
    unfold pureArm64 at hp; revert hp; cases isRoot v.op <;> simp
  unfold evalOpL
  simp only [hg, Bool.false_eq_true, ite_false]
  split
  all_goals first
    | (rename_i h; rw [h] at hp; exact absurd hp (by decide))
    | (rename_i op _; simp only [hr]; rfl)

theorem evalOpL_sel {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {i : Nat} (hs : selIndex v = some i) :
    evalOpL fa env ctx fr v argv ty = .ok (selRes i argv) := by
  have hsel : ∀ (j : Nat) (argv : List Val), Tuple.select j argv = selRes j argv := by
    intro j argv
    match argv with
    | [] => rfl
    | [x] => cases x <;> rfl
    | x :: _ :: _ => cases x <;> rfl
  unfold selIndex at hs
  split at hs
  · rename_i h
    cases hs
    unfold evalOpL
    rw [h]
    simp only [show Op.generic .Select0 = true from by decide, ite_true]
    unfold evalOp
    rw [h]
    simp only [frameVal, h, show isRoot .Select0 = false from by decide, Bool.false_eq_true,
      ite_false]
    exact congrArg _ (hsel 0 argv)
  · rename_i h
    cases hs
    unfold evalOpL
    rw [h]
    simp only [show Op.generic .Select1 = true from by decide, ite_true]
    unfold evalOp
    rw [h]
    simp only [frameVal, h, show isRoot .Select1 = false from by decide, Bool.false_eq_true,
      ite_false]
    exact congrArg _ (hsel 1 argv)
  · rename_i h
    split at hs
    · cases hs
    · rename_i hn
      cases hs
      unfold evalOpL
      rw [h]
      simp only [show Op.generic .SelectN = true from by decide, ite_true]
      unfold evalOp
      rw [h]
      simp only [frameVal, h, show isRoot .SelectN = false from by decide, Bool.false_eq_true,
        ite_false]
      show Res.ok (Tuple.selectN v.auxInt argv) = _
      match argv with
      | [] => rfl
      | [x] => cases x <;> simp [Tuple.selectN, selRes, comp, hn]
      | x :: _ :: _ => cases x <;> rfl
  · cases hs

theorem evalOpL_movd {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hm : v.op = .ARM64MOVDreg ∨ v.op = .ARM64MOVDnop) :
    evalOpL fa env ctx fr v argv ty =
      .ok (movdRes (((v.args[0]?.bind ctx.f.value?).map
        (Arm64.signExtendsIn ctx.f.value?)).getD false) argv ty) := by
  have hnf : ∀ (fa : Bool) (ctx : Ctx) (argv : List Val), nilFaults fa ctx v argv = none := by
    intro fa ctx argv
    rcases hm with h | h <;> exact nilFaults_none (by rw [h]; decide) (by rw [h]; decide)
  unfold evalOpL
  rcases hm with h | h
  · rw [h]
    simp only [show Op.generic .ARM64MOVDreg = false from by decide, Bool.false_eq_true, ite_false]
    unfold arm64Op
    simp only [hnf, h]
    unfold movdRes
    match argv with
    | [] => rfl
    | [a] => cases a <;> rfl
    | _ :: _ :: _ => rfl
  · rw [h]
    simp only [show Op.generic .ARM64MOVDnop = false from by decide, Bool.false_eq_true, ite_false]
    unfold arm64Op
    simp only [hnf, h]
    unfold movdRes
    match argv with
    | [] => rfl
    | [a] => cases a <;> rfl
    | _ :: _ :: _ => rfl

theorem movdLoc_eq (lc : LocCtx) (v : Value) (argv : List Val) (ty : Ty) :
    movdLoc lc v argv ty =
      movdRes ((v.args[0]?.map (lc.signOf lc.ctx.f.valueTab.size)).getD false) argv ty := by
  unfold movdLoc movdRes
  match argv with
  | [] => rfl
  | [a] => cases a <;> rfl
  | _ :: _ :: _ => rfl

theorem evalOpL_makeResult {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hm : v.op = .MakeResult) :
    evalOpL fa env ctx fr v argv ty = .ok (.tuple argv) := by
  unfold evalOpL
  rw [hm]
  simp only [show Op.generic .MakeResult = true from by decide, ite_true]
  unfold evalOp
  rw [hm]
  simp only [frameVal, hm, show isRoot .MakeResult = false from by decide, Bool.false_eq_true,
    ite_false]
  rfl

theorem evalOpL_copy {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {x : Val} {ty : Ty} (hm : v.op = .Copy) :
    evalOpL fa env ctx fr v [x] ty = .ok x := by
  unfold evalOpL
  rw [hm]
  simp only [show Op.generic .Copy = true from by decide, ite_true]
  unfold evalOp
  rw [hm]
  simp only [frameVal, hm, show isRoot .Copy = false from by decide, Bool.false_eq_true,
    ite_false]
  rfl

theorem evalOpL_keepAlive {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {y : Val} (hm : v.op = .KeepAlive)
    (h : evalOpL fa env ctx fr v argv ty = .ok y) : ∃ x m, argv = [x, .mem m] ∧ y = .mem m := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := v
  dsimp only at hm
  subst hm
  simp only [evalOpL, evalOp, memRoot, show Op.generic .KeepAlive = true from by decide, ite_true] at h
  split at h
  all_goals first
    | contradiction
    | (cases h; exact ⟨_, _, rfl, rfl⟩)
    | (split at h <;> cases h)

theorem evalOpL_keepAlive_panic {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {e : Panic} {m : Mem} (hm : v.op = .KeepAlive) :
    evalOpL fa env ctx fr v argv ty ≠ .panic e m := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := v
  dsimp only at hm
  subst hm
  intro h
  simp only [evalOpL, evalOp, memRoot, show Op.generic .KeepAlive = true from by decide, ite_true] at h
  split at h
  all_goals first
    | contradiction
    | cases h
    | (split at h <;> cases h)

theorem evalOpL_varLive {fa : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {m : Mem}
    {ty : Ty} (hm : v.op = .VarLive) : evalOpL fa env ctx fr v [.mem m] ty = .ok (.mem m) := by
  obtain ⟨id, op, t, ai, ax, pos, us, args, blk⟩ := v
  dsimp only at hm
  subst hm
  simp [evalOpL, evalOp, memRoot, show Op.generic .KeepAlive = true from by decide, show Op.generic .VarLive = true from by decide]

end GoFV.Proof.RA
