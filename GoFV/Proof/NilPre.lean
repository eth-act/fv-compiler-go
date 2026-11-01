import GoFV.Opt.NilCheckRel
import GoFV.SSA.Sem.Runtime

/-!
# The checked rewrite passes' precondition on calls and arguments (issue #151)

Two nil-check eliminations of `generic.rules` rest on facts the semantics leaves to the
environment and the caller rather than to the function:

- `:1367`/`:1372`: the first result of a malloc-family call (`runtime.newobject`, the
  size-specialised `mallocgc*SC*`; `Opt.NilCheck.mallocName`) is non-nil. `Env.AllocNonNil`:
  every such contract of the environment that returns gives a non-nil pointer first. The
  runtime's contracts satisfy it (`Env.runtime_allocNonNil`): `newobject` and `mallocSized`
  return `runtime.zerobase` or a fresh heap block.
- `:1384`: a generic function's dictionary parameter `.dict` is non-nil (the compiler always
  passes a dictionary). `DictArgs k args`: the arguments at the indices `k` are non-nil
  pointers; the rewrite passes take `k = Opt.NilCheck.dictParams tabs f` (`NilPre`), which only
  depends on the function's ABI assignments (`OwnAux`) and the names they refer to.
-/

namespace GoFV.SSA.Sem

/-- **Every malloc-family contract returns a non-nil pointer** first (`Opt.NilCheck.mallocName`). -/
def Env.AllocNonNil (env : Env) : Prop :=
  ∀ name c, GoFV.Opt.NilCheck.mallocName name = true → env.extern name = some c →
    ∀ args clo m rs m', c args clo m = .returned rs m' →
      ∃ p, rs.head? = some (.ptr p) ∧ p.blk ≠ .nil

/-- The arguments at the indices `k` are non-nil pointers. -/
def DictArgs (k : List Nat) (args : List Val) : Prop :=
  ∀ i ∈ k, ∃ p, args[i]? = some (.ptr p) ∧ p.blk ≠ .nil

/-- The precondition of nilcheckelim's checker with the rewrite passes' seeds
(`Opt.NilCheck.nrel true`) for `f` in the tables `tabs`: malloc-family contracts return non-nil
pointers and the dictionary arguments are non-nil. -/
def NilPre (tabs : Tables) (f : Func) (env : Env) (args : List Val) (_ : Mem) : Prop :=
  env.AllocNonNil ∧ DictArgs (GoFV.Opt.NilCheck.dictParams tabs f) args

theorem DictArgs.nil (args : List Val) : DictArgs [] args := fun _ h => absurd h List.not_mem_nil

/-- `Env.p1` has no malloc-family contract. -/
theorem Env.p1_allocNonNil : Env.p1.AllocNonNil := by
  intro name c hm hc
  simp only [Env.p1] at hc
  split at hc <;> first | (exfalso; revert hm; decide +kernel) | cases hc

theorem Runtime.alloc_nonNil {m : Mem} {n : Nat} {p : Ptr} {m' : Mem}
    (h : Runtime.alloc m n = some (p, m')) : p.blk ≠ .nil := by
  unfold Runtime.alloc at h
  split at h
  · cases h; nofun
  · split at h
    · cases h
    · cases h; simp [Mem.allocHeap]

/-- **The runtime's malloc-family contracts return non-nil pointers.** -/
theorem Env.runtime_allocNonNil : Env.runtime.AllocNonNil := by
  intro name c hm hc args clo m rs m' hr
  simp only [Env.runtime] at hc
  split at hc
  any_goals (exfalso; revert hm; decide +kernel)
  · -- `runtime.newobject`
    cases hc
    simp only [Runtime.newobject, Runtime.ok?] at hr
    split at hr
    · next o ho =>
      cases hr
      match args, ho with
      | [_], ho =>
        simp only [bind, Option.bind_eq_some_iff, pure] at ho
        obtain ⟨_, -, _, -, ⟨_, _⟩, hal, hh⟩ := ho
        simp only [Option.some.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        exact ⟨_, rfl, Runtime.alloc_nonNil hal⟩
    · cases hr
  · split at hc
    · cases hc
      simp only [Runtime.mallocSized, Runtime.ok?] at hr
      split at hr
      · next o ho =>
        cases hr
        match args, ho with
        | [_, _, _], ho =>
          simp only [bind, Option.bind_eq_some_iff, pure] at ho
          obtain ⟨_, -, ⟨_, _⟩, hal, hh⟩ := ho
          simp only [Option.some.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, -⟩ := hh
          exact ⟨_, rfl, Runtime.alloc_nonNil hal⟩
      · cases hr
    · split at hc
      · next hp =>
        exfalso
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
        rcases hp with ((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) <;> revert hm <;>
          decide +kernel
      · cases hc

end GoFV.SSA.Sem
