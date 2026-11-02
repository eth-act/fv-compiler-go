import GoFV.Opt.NilCheckRel
import GoFV.SSA.Sem.Runtime
import GoFV.Proof.Pass.CSEMemBytes

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
- `:1352`/`:1357`/`:1362` (issue #69): a malloc-family call of a positive size (`AllocReq`)
  returns a fresh heap block whose bytes are all zero, so a `Zero` of it, or a `Store` of a zero
  into it, changes no byte. `Env.AllocZero`; the runtime's contracts satisfy it
  (`Env.runtime_allocZero`). A zero-sized allocation returns `runtime.zerobase`, about which
  nothing is claimed.
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
        simp only [beq_iff_eq] at hp
        subst hp
        revert hm
        decide +kernel
      · split at hc
        · next hp =>
          exfalso
          simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
          rcases hp with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;> revert hm <;>
            decide +kernel
        · cases hc

/-- `Env.atAct` keeps the malloc-family contracts. -/
theorem Env.AllocNonNil.atAct {env : Env} (h : env.AllocNonNil) (act : Nat) :
    (env.atAct act).AllocNonNil := by
  intro name c hm hc
  have hn : isDeferName name = false := by
    cases hd : isDeferName name
    · rfl
    · exfalso
      simp only [isDeferName, Bool.or_eq_true, beq_iff_eq] at hd
      rcases hd with ((rfl | rfl) | rfl) | rfl <;> revert hm <;> decide +kernel
  rw [Env.atAct_extern_of hn] at hc
  exact h name c hm hc

/-- The bytes of block `b` are all zero where `m` holds it. -/
def Mem.BlockZero (m : Mem) (b : Blk) : Prop :=
  ∀ a, m.find? b = some a → ∀ x ∈ a.data, x = .b 0

/-- A malloc-family call asks for a positive number of zeroed bytes: `runtime.newobject` of a
type descriptor whose size word (`Runtime.typeInfo`) is positive, or a size-specialised malloc
`mallocgc*SC*(size, typ, needzero)` of a positive size with `needzero` set (as
`ssagen.newObject` calls them). -/
def AllocReq (name : String) (args : List Val) (m : Mem) : Prop :=
  if name = "runtime.newobject" then
    ∃ t p s pb, args = [t] ∧ Runtime.asPtr t = some p ∧ Runtime.typeInfo m p = some (s, pb) ∧
      s ≠ 0
  else ∃ w s t, args = [.int w s, t, .bool true] ∧ 0 < s.toInt

/-- **Every malloc-family contract asked for a positive number of zeroed bytes** (`AllocReq`)
**returns a fresh all-zero heap block** first (`Opt.NilCheck.mallocName`). -/
def Env.AllocZero (env : Env) : Prop :=
  ∀ name c, GoFV.Opt.NilCheck.mallocName name = true → env.extern name = some c →
    ∀ args clo m rs m', c args clo m = .returned rs m' → AllocReq name args m →
      ∃ p k, rs.head? = some (.ptr p) ∧ p.blk = .heap k ∧ m'.BlockZero p.blk

/-- `Env.p1` has no malloc-family contract. -/
theorem Env.p1_allocZero : Env.p1.AllocZero := by
  intro name c hm hc
  simp only [Env.p1] at hc
  split at hc <;> first | (exfalso; revert hm; decide +kernel) | cases hc

/-- A positive allocation is a heap block of zeros. -/
theorem Runtime.alloc_zero {m : Mem} {n : Nat} {p : Ptr} {m' : Mem}
    (h : Runtime.alloc m n = some (p, m')) (hn : n ≠ 0) : ∃ k, p.blk = .heap k ∧ m'.BlockZero p.blk := by
  unfold Runtime.alloc at h
  rw [if_neg (by simpa using hn)] at h
  split at h
  · cases h
  · cases h
    refine ⟨m.nextHeap, rfl, fun a ha x hx => ?_⟩
    change (m.set (.heap m.nextHeap) { data := Array.replicate n (.b 0) }).find? _ = some a at ha
    rw [GoFV.Proof.CSE.Mem.find?_set, if_pos rfl] at ha
    cases ha
    exact (Array.mem_replicate.1 hx).2

/-- **The runtime's malloc-family contracts return fresh all-zero heap blocks.** -/
theorem Env.runtime_allocZero : Env.runtime.AllocZero := by
  intro name c hm hc args clo m rs m' hr hreq
  simp only [Env.runtime] at hc
  split at hc
  any_goals (exfalso; revert hm; decide +kernel)
  · -- `runtime.newobject`
    cases hc
    simp only [AllocReq] at hreq
    obtain ⟨t, p, s, pb, rfl, hp, hti, hs⟩ := hreq
    simp only [Runtime.newobject, Runtime.ok?, bind, hp, Option.bind_some,
      hti, pure] at hr
    split at hr
    · next o ho =>
      cases hr
      cases hal : Runtime.alloc m s with
      | none => rw [hal] at ho; cases ho
      | some q =>
        rw [hal] at ho
        cases ho
        obtain ⟨k, hk, hz⟩ := Runtime.alloc_zero hal hs
        exact ⟨_, k, rfl, hk, hz⟩
    · cases hr
  · split at hc
    · next hsc =>
      cases hc
      have hne : name ≠ "runtime.newobject" := by
        rintro rfl; revert hsc; decide +kernel
      simp only [AllocReq, if_neg hne] at hreq
      obtain ⟨w, s, t, rfl, hs⟩ := hreq
      simp only [Runtime.mallocSized, Runtime.ok?, bind, Runtime.asInt, Option.bind_some, pure] at hr
      split at hr
      · next o ho =>
        cases hr
        cases hal : Runtime.alloc m s.toInt.toNat with
        | none => rw [hal] at ho; cases ho
        | some q =>
          rw [hal] at ho
          cases ho
          obtain ⟨k, hk, hz⟩ := Runtime.alloc_zero hal (by omega)
          exact ⟨_, k, rfl, hk, hz⟩
      · cases hr
    · split at hc
      · next hp =>
        exfalso
        simp only [beq_iff_eq] at hp
        subst hp
        revert hm
        decide +kernel
      · split at hc
        · next hp =>
          exfalso
          simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
          rcases hp with (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) <;> revert hm <;>
            decide +kernel
        · cases hc

/-- `Env.atAct` keeps the malloc-family contracts. -/
theorem Env.AllocZero.atAct {env : Env} (h : env.AllocZero) (act : Nat) :
    (env.atAct act).AllocZero := by
  intro name c hm hc
  have hn : isDeferName name = false := by
    cases hd : isDeferName name
    · rfl
    · exfalso
      simp only [isDeferName, Bool.or_eq_true, beq_iff_eq] at hd
      rcases hd with ((rfl | rfl) | rfl) | rfl <;> revert hm <;> decide +kernel
  rw [Env.atAct_extern_of hn] at hc
  exact h name c hm hc

end GoFV.SSA.Sem
