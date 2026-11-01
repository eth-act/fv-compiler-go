import GoFV.SSA.Sem.Run

/-!
# cse: facts about `evalOp` at single ops

`evalOp_tail`: a value whose op is not a root and not `InitMem`/`Arg`/`ArgIntReg`/
`GetClosurePtr` takes
`evalOp`'s last arm (`frameVal`, else `evalPure`). From it: `evalOp_total` (such values and
`InitMem` always evaluate), `evalOp_ok_id` (two non-root values with the same op, aux and
auxint that both evaluate give the same result: IDs occur only in `stuck` messages),
`evalOp_load`. `evalOp_localAddr` and `evalOp_nilCheck_ok` unfold `evalOp` at one op.

`Op` (446 constructors) is split by `cases` once, in `evalOp_tail_ite`; every other proof
rewrites the op to a constructor first (never `simp` on an op variable, LEARNINGS).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem

theorem frameVal_op_aux {ctx : Ctx} {u v : Value} (hop : v.op = u.op) (hax : v.aux = u.aux) :
    frameVal ctx v = frameVal ctx u := by
  delta frameVal; rw [hop, hax]

/-- `evalOp`'s last arm, with its `isRoot` test. -/
private theorem evalOp_tail_ite {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hr : isRoot v.op = false) (hi : v.op ≠ .InitMem)
    (ha : v.op ≠ .Arg) (hb : v.op ≠ .ArgIntReg) (hc : v.op ≠ .GetClosurePtr) :
    evalOp env ctx fr v argv ty =
      match frameVal ctx v with
      | some x => pure x
      | none =>
        if isRoot v.op then .stuck s!"v{v.id}: {v.op.name} is not in phases P1–P3"
        else pure (evalPure v.op ty v.auxInt v.aux argv) := by
  delta evalOp
  generalize v.op = op at hr hi ha hb hc ⊢
  cases op
  -- `rfl` closes the ops of the last arm; the others contradict a hypothesis. (Trying the
  -- hypotheses first on all 446 goals is slower: `isRoot` compares `String`s.)
  all_goals (try rfl)
  all_goals first
    | exact absurd rfl hi | exact absurd rfl ha | exact absurd rfl hb | exact absurd rfl hc
    | exact absurd hr.symm Bool.false_ne_true

/-- A non-root value other than `InitMem`, `Arg`, `ArgIntReg`, `GetClosurePtr` takes
`evalOp`'s last arm. -/
theorem evalOp_tail {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hr : isRoot v.op = false) (hi : v.op ≠ .InitMem) (ha : v.op ≠ .Arg)
    (hb : v.op ≠ .ArgIntReg) (hc : v.op ≠ .GetClosurePtr) :
    evalOp env ctx fr v argv ty =
      match frameVal ctx v with
      | some x => pure x
      | none => pure (evalPure v.op ty v.auxInt v.aux argv) := by
  rw [evalOp_tail_ite hr hi ha hb hc, hr]
  rfl

theorem evalOp_initMem {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .InitMem) : evalOp env ctx fr v argv ty = .ok (.mem fr.mem0) := by
  delta evalOp; rw [hop]; rfl

theorem evalOp_closurePtr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .GetClosurePtr) :
    evalOp env ctx fr v argv ty = .ok (fr.closure.getD .poison) := by
  delta evalOp; rw [hop]; rfl

/-- **Non-root values evaluate**, unless they are `Arg`/`ArgIntReg` (parameter lookups). -/
theorem evalOp_total {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hr : isRoot v.op = false) (ha : v.op ≠ .Arg) (hb : v.op ≠ .ArgIntReg) :
    ∃ r, evalOp env ctx fr v argv ty = .ok r := by
  by_cases hi : v.op = .InitMem
  · exact ⟨_, evalOp_initMem hi⟩
  by_cases hc : v.op = .GetClosurePtr
  · exact ⟨_, evalOp_closurePtr hc⟩
  rw [evalOp_tail hr hi ha hb hc]
  cases frameVal ctx v <;> exact ⟨_, rfl⟩

/-- Two non-root values with the same op, aux and auxint that both evaluate (on the same
arguments) give the same result: their IDs occur only in `stuck` messages. -/
theorem evalOp_ok_id {env : Env} {ctx : Ctx} {fr : Frame} {u v : Value} {argv : List Val}
    {ty : Ty} {r1 r2 : Val} (hop : v.op = u.op) (hax : v.aux = u.aux)
    (hai : v.auxInt = u.auxInt) (hr : isRoot u.op = false)
    (h1 : evalOp env ctx fr u argv ty = .ok r1) (h2 : evalOp env ctx fr v argv ty = .ok r2) :
    r1 = r2 := by
  by_cases hi : u.op = .InitMem
  · rw [evalOp_initMem hi] at h1
    rw [evalOp_initMem (hop.trans hi)] at h2
    exact (Res.ok.inj h1).symm.trans (Res.ok.inj h2)
  by_cases hc : u.op = .GetClosurePtr
  · rw [evalOp_closurePtr hc] at h1
    rw [evalOp_closurePtr (hop.trans hc)] at h2
    exact (Res.ok.inj h1).symm.trans (Res.ok.inj h2)
  -- `Arg`/`ArgIntReg`: the same lookup on both sides, or `stuck`
  by_cases ha : u.op = .Arg
  · delta evalOp at h1 h2
    rw [ha] at h1
    rw [hop, ha, hax, hai] at h2
    generalize u.aux = o at h1 h2
    cases o <;> first | exact Res.ok.inj (h1.symm.trans h2) | cases h1
  by_cases hb : u.op = .ArgIntReg
  · delta evalOp at h1 h2
    rw [hb] at h1
    rw [hop, hb, hax] at h2
    generalize u.aux.bind ctx.tabs.aux? = o at h1 h2
    rcases o with _ | ⟨_, kind⟩
    · cases h1
    · cases kind <;> first | exact Res.ok.inj (h1.symm.trans h2) | cases h1
  rw [evalOp_tail hr hi ha hb hc] at h1
  rw [evalOp_tail (hop ▸ hr) (hop ▸ hi) (hop ▸ ha) (hop ▸ hb) (hop ▸ hc), frameVal_op_aux hop hax, hop,
    hax, hai] at h2
  exact Res.ok.inj (h1.symm.trans h2)

theorem evalOp_localAddr {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {n : AuxRef} (hop : v.op = .LocalAddr) (hax : v.aux = some n) :
    evalOp env ctx fr v argv ty = .ok (.ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩) := by
  delta evalOp frameVal; rw [hop, hax]; rfl

private theorem ite_stuck_ne_ok {c : Prop} [Decidable c] {a b : String} {r : Val} :
    (if c then (Res.stuck a : Res Val) else .stuck b) ≠ .ok r := by
  split <;> nofun

private theorem ite_panic_ok {c : Prop} [Decidable c] {e : Panic} {m : Mem} {x r : Val}
    (h : (if c then Res.panic e m else .ok x) = .ok r) : x = r := by
  split at h
  · cases h
  · cases h; rfl

/-- A `NilCheck` that evaluates returns its first argument. -/
theorem evalOp_nilCheck_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} {r : Val} (hop : v.op = .NilCheck) (h : evalOp env ctx fr v argv ty = .ok r) :
    ∃ rest, argv = r :: rest := by
  delta evalOp at h; rw [hop] at h
  change memRoot ctx v argv = .ok r at h
  delta memRoot at h; rw [hop] at h
  -- `memRoot`'s match on `NilCheck` and the arguments, ending in `stuck` (wildcard) or in
  -- `if _ then panic else ok (first argument)`
  rcases argv with _ | ⟨a, rest⟩
  · cases h
  rcases a with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | p | _ | _ | _ | _ <;>
    try (first | (cases h; done) | exact absurd h ite_stuck_ne_ok)
  all_goals
    rcases rest with _ | ⟨b, rest⟩ <;>
      try (first | (cases h; done) | exact absurd h ite_stuck_ne_ok)
    rcases b with _ | _ | m | _ | _ | _ | _ | _ | _ <;>
      try (first | (cases h; done) | exact absurd h ite_stuck_ne_ok)
    rcases rest with _ | ⟨c, rest⟩ <;>
      try (first | (cases h; done) | exact absurd h ite_stuck_ne_ok)
    exact ⟨_, congrArg (· :: _) (ite_panic_ok h)⟩

theorem evalOp_load {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hop : v.op = .Load) :
    evalOp env ctx fr v argv ty = .ok (evalPure .Load ty v.auxInt v.aux argv) := by
  have hr : isRoot v.op = false := by rw [hop]; decide
  have hf : frameVal ctx v = none := by delta frameVal; rw [hop]
  rw [evalOp_tail hr (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide)
    (by rw [hop]; decide), hf, hop]
  rfl

theorem argLen_zero_of_arg {op : Op} (h : op = .Arg ∨ op = .ArgIntReg) : op.argLen = 0 := by
  rcases h with rfl | rfl <;> rfl

/-! ## Non-vacuity -/

/-- A value of op `op` with ID `id` and aux `aux`. -/
private def mkValue (op : Op) (id : ID := 0) (aux : Option AuxRef := none) : Value :=
  { (default : Value) with op, id, aux }

/-- `v1` and `v2` (IDs 1 and 2) evaluate alike. -/
example (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) : Val.i64 3 = Val.i64 3 :=
  evalOp_ok_id (u := mkValue .Add64 1) (v := mkValue .Add64 2) (argv := [.i64 2, .i64 1])
    (env := env) (ctx := ctx) (fr := fr) (ty := ty) rfl rfl rfl (by decide) (by rfl) (by rfl)

example (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) (n : AuxRef) :
    evalOp env ctx fr (mkValue .LocalAddr 0 (some n)) [] ty = .ok (.ptr ⟨frameBlk ctx.tabs ctx.act n, 0⟩) :=
  evalOp_localAddr rfl rfl

example (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) (m : Mem) :
    ∃ rest, [Val.ptr ⟨.heap 0, 8⟩, .mem m] = .ptr ⟨.heap 0, 8⟩ :: rest :=
  evalOp_nilCheck_ok (env := env) (ctx := ctx) (fr := fr) (ty := ty) (v := mkValue .NilCheck)
    rfl (by rfl)

example (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) (argv : List Val) :
    evalOp env ctx fr (mkValue .Load) argv ty = .ok (evalPure .Load ty 0 none argv) :=
  evalOp_load rfl

example (env : Env) (ctx : Ctx) (fr : Frame) (ty : Ty) (argv : List Val) :
    ∃ r, evalOp env ctx fr (mkValue .Sub64) argv ty = .ok r :=
  evalOp_total (by decide) (by decide) (by decide)

example : Op.argLen .ArgIntReg = 0 := argLen_zero_of_arg (.inr rfl)

end GoFV.Proof.CSE
