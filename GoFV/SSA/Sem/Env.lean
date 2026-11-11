import GoFV.SSA.Sem.Val

variable [GoFV.SSA.Sem.Addrs]

/-!
# Environment, outcomes, the evaluation monad (`docs/plans/semantics.md` §5, §8)

Callees are contracts on Go-typed arguments (§5): runtime entry points (`Env.p1`, the
panicking ones; `Sem/Runtime.lean`, the rest) and program functions (`Env.withFuncs`, which
runs their SSA).
-/

namespace GoFV.SSA.Sem

/-- Outcome of a callee contract. -/
inductive COutcome where
  | returned (results : List Val) (m : Mem)
  | panicked (e : Panic) (m : Mem)
  | stuck (msg : String)
  deriving Inhabited

/-- Behaviour of a callee on Go-typed arguments (receiver first), its closure context (the
`GetClosurePtr` of a closure call) and the memory. -/
abbrev Contract := List Val → Option Val → Mem → COutcome

/-- What a function's run may call. -/
structure Env where
  /-- Callees by link symbol name. -/
  extern : String → Option Contract := fun _ => none
  /-- The global image (`Sem/Image.lean`, `globalImage`): initial allocations of the global
  symbols, by name; a run adds those its memory does not have yet. -/
  globals : List (String × Alloc) := []
  /-- Callees that never use the spill slots of their register arguments in their caller's
  outgoing-arguments area (a trusted fact about the runtime binary, §9.6: only
  `runtime.wbZero`/`runtime.wbMove` are relied on); a call of one clobbers only the slots of
  its stack arguments (`callFrame`). -/
  noSpill : String → Bool := fun _ => false
  /-- The closure context of the top-level activation (`R26` at entry, the funcval the caller
  called through; `docs/plans/closure-ctx.md`); `none` outside a closure. Read only by
  `entryFrame`: `runActivation` ignores it (a called program function gets the context its
  call passes, `clo`). -/
  closure : Option Val := none

namespace Env

/-- The runtime entry points P1 models: those that only panic (`runtime/panic.go`). -/
def p1 : Env where
  extern
    | "runtime.panicdivide" => some fun _ _ m => .panicked .divide m
    | "runtime.panicshift" => some fun _ _ m => .panicked .shift m
    | "runtime.panicoverflow" => some fun _ _ m => .panicked .overflow m
    | _ => none

instance : Inhabited Env := ⟨p1⟩

end Env

/-- Outcome of running a function (§8). -/
inductive Outcome where
  | returned (results : List Val) (mem : Mem)
  | panicked (e : Panic) (mem : Mem)
  | stuck (msg : String)
  | outOfFuel
  deriving Inhabited

namespace Outcome

/-- The outcomes that carry an obligation: returned or panicked. -/
def Defined : Outcome → Prop
  | .returned .. | .panicked .. => True
  | _ => False

/-- Rendering for test output; `stuck` messages are kept apart (`isStuck`). -/
def render : Outcome → String
  | .returned rs _ => "returned " ++ " ".intercalate (rs.map Val.render)
  | .panicked e _ => "panicked " ++ e.message
  | .stuck msg => "stuck " ++ msg
  | .outOfFuel => "outOfFuel"

end Outcome

/-- Result of evaluating a value or a block: a value, a panic (with the memory at the panic),
or stuck. -/
inductive Res (α : Type) where
  | ok (a : α)
  | panic (e : Panic) (m : Mem)
  | stuck (msg : String)
  deriving Inhabited

namespace Res

@[inline] def bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, k => k a
  | .panic e m, _ => .panic e m
  | .stuck msg, _ => .stuck msg

instance : Monad Res where
  pure := .ok
  bind := bind

@[inline] def ofOption {α : Type} (msg : String) : Option α → Res α
  | some a => .ok a
  | none => .stuck msg

@[simp] theorem bind_ok {α β : Type} (a : α) (k : α → Res β) : bind (.ok a) k = k a := rfl

end Res

end GoFV.SSA.Sem
