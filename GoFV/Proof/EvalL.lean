import GoFV.Proof.SimL
import GoFV.Proof.Frame
import GoFV.Proof.Eval

/-!
# Evaluating a lowered value (`evalValueL`): locality, congruence, panics

`GoFV.Proof.Frame` and `GoFV.Proof.Eval` for `runL`'s value evaluation: a value reads the
registers of its arguments only (`evalValueL_regs`, `evalValueL_congr`); it reads of itself its
op, aux, auxint and ID, of the context the tables, parameters, activation and shapes, and of the
function only whether its first argument sign-extends (`MOVDreg`/`MOVDnop`, `Arm64.signExtendsIn`:
`evalOpL_congr`, `evalValueL_eq_of_args`); one that does not get stuck has its arguments
(`evalValueL_args_def`); only calls, nil checks and, when memory ops fault, arm64 ops panic
(`PanickingL`, `evalValueL_panic_op`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- What the evaluation of `v` reads of the function `f` beyond `v`: whether its first argument
sign-extends. -/
def sxOf (f : Func) (v : Value) : Option Bool :=
  (v.args[0]?.bind f.value?).map (Arm64.signExtendsIn f.value?)

theorem evalOpL_frame (faulting : Bool) (env : Env) (ctx : Ctx) (fr : Frame)
    (r : Array (Option Val)) (v : Value) (argv : List Val) (ty : Ty) :
    evalOpL faulting env ctx { fr with regs := r } v argv ty = evalOpL faulting env ctx fr v argv ty :=
  rfl

/-- A lowered value's evaluation reads the registers of its arguments only. -/
theorem evalValueL_regs {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame}
    {r r' : Array (Option Val)} {v : Value} (h : ∀ a ∈ v.args, r[a]? = r'[a]?) :
    evalValueL md env ctx { fr with regs := r } v = evalValueL md env ctx { fr with regs := r' } v := by
  unfold evalValueL
  simp only [evalOpL_frame]
  congr 1
  exact mapM_congr' _ fun a ha => by rw [h a (Array.mem_toList_iff.1 ha)]

/-- Two frames of one activation whose registers agree on `v`'s arguments evaluate `v` alike. -/
theorem evalValueL_congr {md : LMode} {env : Env} {ctx : Ctx} {fr g : Frame} {v : Value}
    (hg : g = { fr with regs := g.regs }) (h : ∀ a ∈ v.args, fr.regs[a]? = g.regs[a]?) :
    evalValueL md env ctx fr v = evalValueL md env ctx g v := by
  rw [hg]
  exact evalValueL_regs (fr := fr) (r := fr.regs) (r' := g.regs) h

/-- `evalOpL` reads of the value its op, aux, auxint and ID, of the context the tables, the
parameters and the activation, and of the function whether the first argument sign-extends. -/
theorem evalOpL_congr {faulting : Bool} {env : Env} {ctx ctx' : Ctx} {fr : Frame} {v v' : Value}
    {argv : List Val} {ty : Ty} (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id) (htabs : ctx'.tabs = ctx.tabs)
    (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hsx : sxOf ctx'.f v' = sxOf ctx.f v) :
    evalOpL faulting env ctx' fr v' argv ty = evalOpL faulting env ctx fr v argv ty := by
  unfold evalOpL
  rw [hop]
  split
  · exact evalOp_congr hop haux hai hid htabs hpar hact
  · obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
    obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
    dsimp only at htabs hpar hact hsx
    subst htabs hpar hact
    unfold sxOf at hsx
    unfold arm64Op nilFaults nilAccesses wildNil symAddr frameVal memRoot callOp callTarget
      atomicRoot Atomic.barrier
      Atomic.prefetch Atomic.rmwRoot Atomic.casRoot Atomic.rmw Atomic.cas Atomic.unmodelled
    simp only [hop, haux, hai, hid, hsx]

theorem evalValueL_eq_of_args {md : LMode} {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame}
    {v v' : Value} (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt)
    (hid : v'.id = v.id) (hsz : v'.args.size = v.args.size)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a →
      ∃ a' y, v'.args[k]? = some a' ∧ fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y))
    (hfr : fr' = { fr with regs := fr'.regs }) (hty : ctx'.tys[v.id]? = ctx.tys[v.id]?)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hsx : sxOf ctx'.f v' = sxOf ctx.f v) :
    evalValueL md env ctx' fr' v' = evalValueL md env ctx fr v := by
  unfold evalValueL
  rw [mapM_ofOption_eq (l := v'.args.toList) (l' := v.args.toList)
    (m := fun a => s!"v{v'.id}: argument v{a} has no value")
    (m' := fun a => s!"v{v.id}: argument v{a} has no value")
    (r := fun a => (fr'.regs[a]?).join) (r' := fun a => (fr.regs[a]?).join) (by simp [hsz])
    (fun k a' ha' => by
      have hk : k < v.args.size := by
        have := (List.getElem?_eq_some_iff.1 ha').1; simp at this; omega
      obtain ⟨a'', y, h1, h2, h3⟩ := hargs k v.args[k] (by simp [hk])
      rw [Array.getElem?_toList] at ha'
      rw [ha'] at h1; cases h1
      exact ⟨v.args[k], y, by simp [hk], by simp [h3], by simp [h2]⟩)]
  rw [hid, hty, hfr]
  simp only [evalOpL_frame, evalOpL_congr hop haux hai hid htabs hpar hact hsx]

/-- A lowered value that evaluates (or panics) has all its arguments' registers. -/
theorem evalValueL_args_def {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValueL md env ctx fr v ≠ .stuck msg) :
    ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z) := by
  intro a ha
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | ok L =>
    obtain ⟨z, hz⟩ := mapM_ofOption_def hm a (Array.mem_toList_iff.2 ha)
    cases hr : fr.regs[a]? with
    | none => rw [hr] at hz; cases hz
    | some o => rw [hr] at hz; cases o with
      | none => cases hz
      | some z' => exact ⟨z', rfl⟩
  | panic e m => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg => rw [hm] at h; exact absurd rfl (h msg)

/-! ## Panics -/

/-- The ops whose lowered evaluation may panic: calls (`Op.call`, including the arm64 calls and
bounds panics), nil checks (`NilCheck`, `LoweredNilCheck`) and, when memory ops fault
(`runSched`), every arm64 op. -/
def PanickingL (faulting : Bool) (op : Op) : Prop :=
  op.call = true ∨ op.nilCheck = true ∨ (faulting = true ∧ op.generic = false)

theorem PanickingL.of_panicking {faulting : Bool} {op : Op} (h : Panicking op) :
    PanickingL faulting op := by
  rcases h with h | rfl
  · exact .inl h
  · exact .inr (.inl rfl)

/-- Only calls and `NilCheck` make `evalOp` panic. -/
theorem evalOp_panic_op {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {e : Panic} {m : Mem} (ho : evalOp env ctx fr v argv ty = .panic e m) :
    Panicking v.op := by
  by_cases hc : v.op.call = true
  · exact .inl hc
  by_cases hn : v.op = .NilCheck
  · exact .inr hn
  exfalso
  unfold evalOp at ho
  split at ho
  all_goals first
    | cases ho
    | exact absurd ho argVal_not_panic
    | exact hn (memRoot_panic ho)
    | (rename_i heq; exact hc (by rw [heq]; rfl))
    | (split at ho <;> first
        | cases ho
        | exact absurd ho argVal_not_panic
        | (split at ho
           · exact absurd ho atomicRoot_ne_panic
           · cases ho))

theorem panicBounds_ne_ok {k : Int64} {args : List Val} {y : Val} :
    panicBounds k args ≠ .ok y := panicBounds_not_ok

/-- Of the arm64 ops evaluated with the activation, only calls, nil checks, bounds panics and
(when memory ops fault) nil-page accesses panic. -/
theorem arm64Op_panic_op {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} {e : Panic} {m : Mem} (hg : v.op.generic = false)
    (ho : arm64Op faulting env ctx fr v argv ty = .panic e m) : PanickingL faulting v.op := by
  cases hf : faulting
  · have hnf : nilFaults false ctx v argv = none := by simp [nilFaults]
    by_cases hc : v.op.call = true
    · exact .inl hc
    by_cases hn : v.op.nilCheck = true
    · exact .inr (.inl hn)
    exfalso
    subst hf
    unfold arm64Op at ho
    rw [hnf] at ho
    simp only at ho
    split at ho
    all_goals first
      | (rename_i heq; exact hc (by rw [heq]; rfl))
      | (rename_i heq; exact hn (by rw [heq]; rfl))
      | (repeat' (first | (cases ho; done) | exact absurd ho writeRes_not_panic | exact absurd ho atomicRoot_ne_panic | split at ho))
  · exact .inr (.inr ⟨rfl, hg⟩)

/-- **Only `PanickingL` ops make `evalValueL` panic.** -/
theorem evalValueL_panic_op {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {e : Panic} {m : Mem} (h : evalValueL md env ctx fr v = .panic e m) :
    PanickingL md.faulting v.op := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e' m' => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | panic e' m' =>
      unfold evalOpL at ho
      split at ho
      · exact .of_panicking (evalOp_panic_op ho)
      · rename_i hg
        have hg' : v.op.generic = false := by simpa using hg
        split at ho
        all_goals first
          | exact arm64Op_panic_op hg' ho
          | (split at ho
             · exact absurd ho atomicRoot_ne_panic
             · cases ho)

end GoFV.Proof
