import GoFV.Proof.Frame
import GoFV.Proof.Retype

variable [GoFV.SSA.Sem.Addrs]

/-!
# Facts about one value's evaluation

* `evalValue_typed`: a value's result is fixed by `Val.retype` at its own type shape, so every
  register of a run is (`Typed`, preserved by `enterBlock`: `typed_enter`); equivalently it has
  that shape (`evalValue_hasTy`, `Typed.hasTy`, from `Val.retype_hasTy`, #108).
* `evalValue_copy`: a `Copy` yields its argument at the copy's shape.
* `evalValue_eq_of_args`: two values with the same op, aux, auxint and ID whose arguments hold
  the same registers evaluate alike (in contexts agreeing on the value's shape, the tables and
  the parameters).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

theorem retype_idem (t : Ty) (v : Val) : (v.retype t).retype t = v.retype t :=
  Val.retype_idem t v

theorem retype_of_hasTy {t : Ty} {v : Val} (h : v.hasTy t = true) : v.retype t = v :=
  Val.retype_of_hasTy h

/-- Every register of a frame is fixed by `retype` at its value's shape. -/
def Typed (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ (x : ID) (y : Val), fr.regs[x]? = some (some y) → y.retype (ctx.tys[x]?.getD .other) = y

theorem typed_replicate (ctx : Ctx) (n : Nat) (fr : Frame) (h : fr.regs = Array.replicate n none) :
    Typed ctx fr := fun x y hx => by
  rw [h, Array.getElem?_replicate] at hx
  split at hx <;> cases hx

theorem panicBounds_not_ok {k : Int64} {args : List Val} {y : Val} :
    panicBounds k args ≠ .ok y := by
  unfold panicBounds
  split <;> nofun

/-- A value's result is fixed by `retype` at its own shape. -/
theorem evalValue_typed {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) : y.retype (ctx.tys[v.id]?.getD .other) = y := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h; exact retype_idem _ _
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h

/-- **A value's result has its own shape** (#108). -/
theorem evalValue_hasTy {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) : y.hasTy (ctx.tys[v.id]?.getD .other) = true := by
  rw [← evalValue_typed h]; exact Val.retype_hasTy _ _

/-- **Every register of a `Typed` frame has its value's shape** (#108). -/
theorem Typed.hasTy {ctx : Ctx} {fr : Frame} (h : Typed ctx fr) {x : ID} {y : Val}
    (hx : fr.regs[x]? = some (some y)) : y.hasTy (ctx.tys[x]?.getD .other) = true := by
  rw [← h x y hx]; exact Val.retype_hasTy _ _

theorem evalOp_copy {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hop : v.op = .Copy) : evalOp env ctx fr v argv ty = .ok (evalPure .Copy ty v.auxInt v.aux argv) := by
  simp only [evalOp, frameVal, hop]
  rfl

theorem evalValue_copy {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID} {y : Val}
    (hop : v.op = .Copy) (ha : v.args = #[w]) (hw : fr.regs[w]? = some (some y)) :
    evalValue env ctx fr v = .ok (y.retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind, Res.ofOption, pure]
  rw [show (some (some y)).bind id = some y from rfl]
  simp only [evalOp_copy hop]
  rfl

theorem evalValue_copy_inv {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID} {y : Val}
    (hop : v.op = .Copy) (ha : v.args = #[w]) (h : evalValue env ctx fr v = .ok y) :
    ∃ y0, fr.regs[w]? = some (some y0) ∧ y = y0.retype (ctx.tys[v.id]?.getD .other) := by
  cases hw : fr.regs[w]? with
  | some o =>
    cases o with
    | some y0 =>
      rw [evalValue_copy hop ha hw] at h
      cases h; exact ⟨y0, rfl, rfl⟩
    | none =>
      unfold evalValue at h
      rw [ha] at h
      simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind,
        Res.ofOption] at h
      cases h
  | none =>
    unfold evalValue at h
    rw [ha] at h
    simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind,
      Res.ofOption] at h
    cases h

theorem mapM_ofOption_eq {m m' : ID → String} {r r' : ID → Option Val} :
    ∀ {l l' : List ID}, l.length = l'.length →
      (∀ (k : Nat) a, l[k]? = some a → ∃ a' y, l'[k]? = some a' ∧ r a = some y ∧ r' a' = some y) →
      l.mapM (fun a => Res.ofOption (m a) (r a)) = l'.mapM (fun a => Res.ofOption (m' a) (r' a))
  | [], [], _, _ => rfl
  | a :: l, a' :: l', hl, h => by
    obtain ⟨b, y, hb, hy, hy'⟩ := h 0 a rfl
    cases hb
    rw [List.mapM_cons, List.mapM_cons, hy, hy',
      mapM_ofOption_eq (l := l) (l' := l') (by simpa using hl) (fun k x hx => h (k + 1) x hx)]
    rfl
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl

theorem argVal_params {ctx ctx' : Ctx} (h : ctx'.params = ctx.params) (fr : Frame) (n : AuxRef)
    (off : Int) (ty : Ty) : argVal ctx' fr n off ty = argVal ctx fr n off ty := by
  unfold argVal; rw [h]

theorem evalOp_frame (env : Env) (ctx : Ctx) (fr : Frame) (r : Array (Option Val)) (v : Value)
    (argv : List Val) (ty : Ty) :
    evalOp env ctx { fr with regs := r } v argv ty = evalOp env ctx fr v argv ty := rfl

/-- `evalOp` reads of the value only its op, aux, auxint and ID, and of the context only the
tables, the parameters and the activation. -/
theorem evalOp_congr {env : Env} {ctx ctx' : Ctx} {fr : Frame} {v v' : Value} {argv : List Val}
    {ty : Ty} (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt)
    (hid : v'.id = v.id) (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params)
    (hact : ctx'.act = ctx.act) :
    evalOp env ctx' fr v' argv ty = evalOp env ctx fr v argv ty := by
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
  dsimp only at htabs hpar hact
  subst htabs hpar hact
  unfold evalOp frameVal memRoot callOp callTarget argFloat atomicRoot Atomic.barrier
    Atomic.prefetch Atomic.rmwRoot Atomic.casRoot Atomic.rmw Atomic.cas Atomic.unmodelled
  simp only [hop, haux, hai, hid]
  rfl

theorem evalValue_eq_of_args {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value}
    (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id)
    (hsz : v'.args.size = v.args.size)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a →
      ∃ a' y, v'.args[k]? = some a' ∧ fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y))
    (hfr : fr' = { fr with regs := fr'.regs }) (hty : ctx'.tys[v.id]? = ctx.tys[v.id]?)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act) :
    evalValue env ctx' fr' v' = evalValue env ctx fr v := by
  unfold evalValue
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
  simp only [evalOp_frame, evalOp_congr hop haux hai hid htabs hpar hact]

theorem mapM_ofOption_def {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID} {L : List Val}, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L →
      ∀ a ∈ l, ∃ z, r a = some z
  | [], _, _ => fun _ h => absurd h List.not_mem_nil
  | a :: l, L, h => by
    rw [List.mapM_cons] at h
    cases ha : r a with
    | none => rw [ha] at h; cases h
    | some z =>
      rw [ha] at h
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _ at h
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L' =>
        intro b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact ⟨z, ha⟩
        · exact mapM_ofOption_def hl b hb
      | panic e m' => rw [hl] at h; cases h
      | stuck msg => rw [hl] at h; cases h

theorem mapM_ofOption_ne_panic {m : ID → String} {r : ID → Option Val} {e : Panic} {mm : Mem} :
    ∀ {l : List ID}, l.mapM (fun a => Res.ofOption (m a) (r a)) ≠ .panic e mm
  | [] => nofun
  | a :: l => by
    rw [List.mapM_cons]
    cases ha : r a with
    | none => simp only [Res.ofOption]; nofun
    | some z =>
      simp only [Res.ofOption]
      change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ ≠ _
      cases hl : l.mapM (fun a => Res.ofOption (m a) (r a)) with
      | ok L => nofun
      | panic e' m' => exact absurd hl mapM_ofOption_ne_panic
      | stuck msg => nofun

/-- A value that evaluates (or panics) has all its arguments' registers. -/
theorem evalValue_args_def {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    (h : ∀ msg, evalValue env ctx fr v ≠ .stuck msg) :
    ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z) := by
  intro a ha
  unfold evalValue at h
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

theorem argVal_not_panic {ctx : Ctx} {fr : Frame} {n : AuxRef} {off : Int} {ty : Ty} {e : Panic}
    {m : Mem} : argVal ctx fr n off ty ≠ .panic e m := by
  unfold argVal
  split
  · nofun
  · split
    · nofun
    · split <;> nofun

theorem writeRes_not_panic {what : String} {o : Option Mem} {e : Panic} {m : Mem} :
    writeRes what o ≠ .panic e m := by
  unfold writeRes; split <;> nofun

/-- Of the memory roots only `NilCheck` panics. -/
theorem memRoot_panic {ctx : Ctx} {v : Value} {argv : List Val} {e : Panic} {m : Mem}
    (h : memRoot ctx v argv = .panic e m) : v.op = .NilCheck := by
  by_cases hn : v.op = .NilCheck
  · exact hn
  exfalso
  unfold memRoot at h
  split at h
  all_goals (repeat' (first | exact absurd h writeRes_not_panic | (cases h; done) | split at h))
  all_goals simp_all

/-- A `NilCheck` on a word and a memory (`Val.asPtrWord`, §6). -/
theorem memRoot_nilCheck {ctx : Ctx} {v : Value} (hn : v.op = .NilCheck) (a : Val) (m : Mem)
    {p : Ptr} (hp : a.asPtrWord = some p) :
    memRoot ctx v [a, .mem m] = if p.blk == .nil then .panic .nilDeref m else .ok a := by
  unfold memRoot; rw [hn]; simp only [hp]

/-- A `NilCheck` that does not get stuck reads a pointer word and a memory, and panics exactly
when the word points into `Blk.nil`. -/
theorem memRoot_nilCheck_res {ctx : Ctx} {v : Value} {argv : List Val} {res : Res Val}
    (hn : v.op = .NilCheck) (h : memRoot ctx v argv = res) (hs : ∀ msg, res ≠ .stuck msg) :
    ∃ a m p, argv = [a, .mem m] ∧ a.asPtrWord = some p ∧
      res = if p.blk == .nil then .panic .nilDeref m else .ok a := by
  subst h
  unfold memRoot at hs ⊢; rw [hn] at hs ⊢
  rcases argv with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exfalso; simp only at hs; split at hs <;> exact hs _ rfl
  · exfalso; simp only at hs; split at hs <;> exact hs _ rfl
  case cons.cons.cons => exfalso; simp only at hs; split at hs <;> exact hs _ rfl
  rcases b with _ | _ | m | _ | _ | _ | _ | _ | _
  all_goals try (exfalso; simp only at hs; split at hs <;> exact hs _ rfl; done)
  simp only at hs ⊢
  cases hp : a.asPtrWord with
  | none => simp only [hp] at hs; exact absurd rfl (hs _)
  | some p => exact ⟨a, m, p, rfl, hp, rfl⟩

/-- The ops whose evaluation may panic: calls (`Op.call`, including `PanicBounds`) and
`NilCheck`. -/
def Panicking (op : Op) : Prop := op.call = true ∨ op = .NilCheck

theorem nilCheck_eq {op : Op} (h : op.nilCheck = true) : op = .NilCheck ∨ op = .ARM64LoweredNilCheck := by
  unfold Op.nilCheck at h; split at h <;> first | exact .inl rfl | exact .inr rfl | cases h

/-- Calls are scheduled as side-effecting roots. -/
theorem prio_call {op : Op} (h : op.call = true) : prio op = 2 := by
  unfold prio isRoot
  cases hn : op.nilCheck
  · simp [h]
  · rcases nilCheck_eq hn with rfl | rfl <;> exact absurd h (by decide)

/-- A value that can panic is not pure. -/
theorem prio_panicking {op : Op} (h : Panicking op) : prio op ≠ 0 := by
  rcases h with h | rfl
  · rw [prio_call h]; decide
  · decide

/-- **A `NilCheck` that evaluates passed a pointer into an allocation** (or a `uintptr` whose
`Ptr.ofAddr` is), and returns it. -/
theorem evalOp_nilCheck_blk {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {r : Val} (hop : v.op = .NilCheck) (h : evalOp env ctx fr v argv ty = .ok r) :
    (∃ p m, argv = [.ptr p, .mem m] ∧ r = .ptr p ∧ p.blk ≠ .nil) ∨
      (∃ x m, argv = [.int .w64 x, .mem m] ∧ r = .int .w64 x ∧ (Ptr.ofAddr x).blk ≠ .nil) := by
  unfold evalOp at h; rw [hop] at h
  change memRoot ctx v argv = .ok r at h
  unfold memRoot at h; rw [hop] at h
  rcases argv with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp only at h; split at h <;> cases h
  · simp only at h; split at h <;> cases h
  case cons.cons.cons => simp only at h; split at h <;> cases h
  rcases b with _ | _ | m | _ | _ | _ | _ | _ | _
  all_goals try (simp only at h; split at h <;> cases h; done)
  simp only at h
  cases hp : a.asPtrWord with
  | none => simp only [hp, reduceCtorEq] at h
  | some p =>
    simp only [hp] at h
    split at h
    · cases h
    · rename_i hb; injection h with h; subst h
      rcases a with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | q | _ | _ | _ | _ <;>
        simp only [Val.asPtrWord, reduceCtorEq, Option.some.injEq] at hp
      · subst hp; exact .inr ⟨_, _, rfl, rfl, by simpa using hb⟩
      · subst hp; exact .inl ⟨_, _, rfl, rfl, by simpa using hb⟩

/-- A call without arguments (it lacks its memory) is stuck. -/
theorem callOp_nil_stuck {env : Env} {ctx : Ctx} {v : Value} :
    ∃ msg, callOp env ctx v [] = .stuck msg := by
  have hr : ∃ a b, callTarget ctx v [] = (a, b, []) := by
    unfold callTarget; split <;> simp_all
  obtain ⟨a, b, hr⟩ := hr
  unfold callOp
  rw [hr]
  exact ⟨_, rfl⟩

theorem callOp_nil {env : Env} {ctx : Ctx} {v : Value} {e : Panic} {m : Mem} :
    callOp env ctx v [] ≠ .panic e m := by
  obtain ⟨_, h⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
  rw [h]; nofun

/-- The atomic roots never panic (arm64 faults on their invalid accesses: `stuck`). -/
theorem atomicRoot_ne_panic {v : Value} {argv : List Val} {e : Panic} {m : Mem} :
    atomicRoot v argv ≠ .panic e m := by
  unfold atomicRoot Atomic.barrier Atomic.prefetch Atomic.rmwRoot Atomic.casRoot Atomic.rmw
    Atomic.cas Atomic.unmodelled
  repeat' split
  all_goals nofun

/-- A panicking value other than a nil check is a side-effecting root. -/
theorem prio_panicking_two {op : Op} (h : Panicking op) (hn : op ≠ .NilCheck) : prio op = 2 := by
  rcases h with h | h
  · exact prio_call h
  · exact absurd h hn

/-- Only calls (including `PanicBounds`) and `NilCheck` panic. -/
theorem evalValue_panic_op {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic} {m : Mem}
    (h : evalValue env ctx fr v = .panic e m) : Panicking v.op := by
  by_cases hc : v.op.call = true
  · exact .inl hc
  by_cases hn : v.op = .NilCheck
  · exact .inr hn
  exfalso
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e' m' => exact absurd hm mapM_ofOption_ne_panic
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOp env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | panic e' m' =>
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

theorem typeShapes_getD (tabs : Tables) (t : TypeRef) :
    (typeShapes tabs)[t]?.getD .other = tabs.ty t := by
  unfold typeShapes
  rw [Array.getElem?_map]
  by_cases ht : t < tabs.types.size
  · simp [ht]
  · have hr : ((List.range tabs.types.size).toArray)[t]? = none := by simp [ht]
    have hn : tabs.type? t = none := by
      unfold Tables.type?
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt ht)]; rfl
    rw [hr]
    show Ty.other = tyOf tabs 32 t
    unfold tyOf
    rw [hn]

theorem tys_of_value {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.make tabs f).tys[x]? = some (tabs.ty v.type) := by
  unfold Func.value? at h
  simp only [Ctx.make, Array.getElem?_map]
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at h; cases h
  | some o =>
    rw [hx] at h; simp at h; subst h
    simp only [Option.map_some, valueTy, typeShapes_getD]

end GoFV.Proof
