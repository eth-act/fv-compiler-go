import GoFV.SSA.Sem.Runtime
import GoFV.SSA.Sem.Run

/-!
# Environments whose memory runtime calls are the model's contracts (#151)

`Env.MemOps`: `runtime.memclrNoHeapPointers` and `runtime.memmove`, if the environment has them
at all, are `Runtime.memclr` and `Runtime.memmove`. A missing contract makes `callOp` stuck, so
the call lemmas of `GoFV.Proof.Pass.SegCall` (a call ⊑ the plain `Zero`/`Move` write) hold in
every such environment: `Env.runtime` and `Env.p1` (which has neither).

`Env.GrowLen` (issue #69): `runtime.growslice` and `runtime.growsliceNoAlias`, if present, return
a slice whose length is their integer `newLen` argument (`generic.rules:2128`), as
`Runtime.growslice` does (`Env.runtime_growLen`).

`Env.IfaceEq eq` (issues #69, #189): `runtime.ifaceeq` on an itab symbol of `eq.1` and
`runtime.efaceeq` on a type symbol of `eq.2` (the symbols of the pipeline's and the frontend's
tables whose type the export marks direct-interface and comparable, `RewriteCheck.eqPass`,
`Verified.pipelineEq`) return whether their data words are the
same pointer, and the memory they were given (`third_party/go/src/runtime/alg.go`: `efaceeq(t,
x, y)` returns `true` for a nil `t`, panics if `t.Equal` is nil, returns `x == y` if
`t.IsDirectIface()`, else `t.Equal(x, y)`; `ifaceeq(tab, x, y)` is it with `t := tab.Type`; a
comparable type has an `Equal` function, so on these symbols both return `x == y` and write
nothing). Neither runtime model has them (`Env.runtime_ifaceEq`, `Env.p1_ifaceEq`);
`Env.ifaceEqDemo` has them (`Env.ifaceEqDemo_ifaceEq`).
-/

namespace GoFV.SSA.Sem

/-- `runtime.memclrNoHeapPointers` and `runtime.memmove` are the runtime model's contracts, or
missing. -/
def Env.MemOps (env : Env) : Prop :=
  (∀ c, env.extern "runtime.memclrNoHeapPointers" = some c → c = Runtime.memclr) ∧
    (∀ c, env.extern "runtime.memmove" = some c → c = Runtime.memmove)

theorem Env.runtime_memOps : Env.runtime.MemOps :=
  ⟨fun _ h => (Option.some.inj h).symm, fun _ h => (Option.some.inj h).symm⟩

theorem Env.p1_memOps : Env.p1.MemOps :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

/-- `Env.atAct` keeps `runtime.memclrNoHeapPointers` and `runtime.memmove`. -/
theorem Env.MemOps.atAct {env : Env} (h : env.MemOps) (act : Nat) : (env.atAct act).MemOps :=
  ⟨fun c hc => h.1 c (by rwa [Env.atAct_extern_of (by decide +kernel)] at hc),
    fun c hc => h.2 c (by rwa [Env.atAct_extern_of (by decide +kernel)] at hc)⟩

/-- `runtime.growslice` and `runtime.growsliceNoAlias`, if the environment has them, return a
slice whose length is their `newLen` argument, which is an integer. -/
def Env.GrowLen (env : Env) : Prop :=
  ∀ name c, (name = "runtime.growslice" ∨ name = "runtime.growsliceNoAlias") →
    env.extern name = some c → ∀ args clo m rs m', c args clo m = .returned rs m' →
      (∀ p, args[1]? ≠ some (Val.ptr p)) ∧
      ∀ x, args[1]? = some (Val.int .w64 x) → ∃ p cap rest, rs = .agg [p, .int .w64 x, cap] :: rest

private theorem ofNat_toNat_toInt {x : BitVec 64} (h : ¬ x.toInt < 0) :
    BitVec.ofNat 64 x.toInt.toNat = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toInt_eq_toNat_cond] at h ⊢
  have := x.isLt
  split at h <;> omega

/-- A returning `Runtime.growslice`: its `newLen` is a nonnegative integer, the result's length. -/
theorem Runtime.growslice_len {args : List Val} {clo : Option Val} {m : Mem} {rs : List Val}
    {m' : Mem} (h : Runtime.growslice args clo m = .returned rs m') :
    ∃ (old : Val) (w : Width) (y : BitVec w.bits) (oc num et : Val), args = [old, .int w y, oc, num, et] ∧
      ¬ y.toInt < 0 ∧ ∃ p cap rest, rs = .agg [p, .int .w64 (BitVec.ofNat 64 y.toInt.toNat), cap] :: rest := by
  unfold Runtime.growslice at h
  match args with
  | [old, nl, oldCap, num, et] =>
    cases nl with
    | int w y =>
      refine ⟨old, w, y, oldCap, num, et, rfl, ?_⟩
      simp only [Runtime.asInt] at h
      split at h <;> try cases h
      rename_i oc' num' et' hm
      simp only [Option.some.injEq] at oc'
      subst oc'
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hn
          refine ⟨hn, ?_⟩
          split at h
          · cases h
            exact ⟨_, _, [], rfl⟩
          · split at h
            · cases h
            · unfold Runtime.ok? at h
              split at h
              · rename_i o hr
                cases h
                simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hr
                obtain ⟨_, _, _, _, _, _, rfl, rfl⟩ := hr
                exact ⟨_, _, [], rfl⟩
              · cases h
    | _ => simp [Runtime.asInt] at h
  | [] | [_] | [_, _] | [_, _, _] | [_, _, _, _] | _ :: _ :: _ :: _ :: _ :: _ :: _ => cases h

theorem Env.runtime_growLen : Env.runtime.GrowLen := by
  intro name c hn hc args clo m rs m' h
  have h' : Runtime.growslice args clo m = .returned rs m' := by
    rcases hn with rfl | rfl <;> cases hc <;> exact h
  obtain ⟨old, w, y, oc, num, et, rfl, hn, p, cap, rest, rfl⟩ := Runtime.growslice_len h'
  refine ⟨fun q h => by simp at h, fun x hx => ?_⟩
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hx
  cases hx
  exact ⟨p, cap, rest, by rw [ofNat_toNat_toInt hn]⟩

theorem Env.p1_growLen : Env.p1.GrowLen := by
  intro name c hn hc
  rcases hn with rfl | rfl <;> cases hc

theorem Env.GrowLen.atAct {env : Env} (h : env.GrowLen) (act : Nat) : (env.atAct act).GrowLen :=
  fun name c hn hc => h name c hn (by
    rcases hn with rfl | rfl <;> rwa [Env.atAct_extern_of (by decide +kernel)] at hc)

/-- `runtime.ifaceeq` on (a word pointing at the start of) an itab symbol of `eq.1` and
`runtime.efaceeq` on a type symbol of `eq.2`, if the environment has them, return the pointer
equality of their data words (`PtrOps.eqPtr false`, the `EqPtr` the compiler folds the call
to) and the memory they were given. -/
def Env.IfaceEq (eq : List String × List String) (env : Env) : Prop :=
  ∀ name c, env.extern name = some c → ∀ s,
    (name = "runtime.ifaceeq" ∧ s ∈ eq.1 ∨ name = "runtime.efaceeq" ∧ s ∈ eq.2) →
    ∀ d x y p q m, d.asPtrWord = some ⟨.global s, 0⟩ → x.asPtrWord = some p →
      y.asPtrWord = some q → c [d, x, y] none m = .returned [PtrOps.eqPtr false [x, y]] m

/-- An environment without `runtime.ifaceeq` and `runtime.efaceeq` has the contract. -/
theorem Env.ifaceEq_of_none {env : Env} (h1 : env.extern "runtime.ifaceeq" = none)
    (h2 : env.extern "runtime.efaceeq" = none) (eq : List String × List String) :
    env.IfaceEq eq := by
  intro name c hc s hs
  rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [h1] at hc; cases hc
  · rw [h2] at hc; cases hc

theorem Env.runtime_ifaceEq (eq : List String × List String) : Env.runtime.IfaceEq eq :=
  Env.ifaceEq_of_none rfl rfl eq

theorem Env.p1_ifaceEq (eq : List String × List String) : Env.p1.IfaceEq eq :=
  Env.ifaceEq_of_none rfl rfl eq

theorem Env.IfaceEq.atAct {eq : List String × List String} {env : Env} (h : env.IfaceEq eq)
    (act : Nat) : (env.atAct act).IfaceEq eq := fun name c hc s hs =>
  h name c (by
    rcases hs with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rwa [Env.atAct_extern_of (by decide +kernel)] at hc) s hs

/-- Fewer symbols: a weaker contract. -/
theorem Env.IfaceEq.sub {eq eq' : List String × List String} {env : Env} (h : env.IfaceEq eq)
    (h1 : ∀ s ∈ eq'.1, s ∈ eq.1) (h2 : ∀ s ∈ eq'.2, s ∈ eq.2) : env.IfaceEq eq' :=
  fun name c hc s hs => h name c hc s (hs.imp (fun ⟨a, b⟩ => ⟨a, h1 s b⟩) fun ⟨a, b⟩ => ⟨a, h2 s b⟩)

/-- The `ifaceeq`/`efaceeq` contract of a direct-interface comparable type: the data words'
pointer equality, the memory unchanged. -/
def Runtime.ifaceEqDirect : Contract := fun args _ m =>
  match args with
  | [_, x, y] => .returned [PtrOps.eqPtr false [x, y]] m
  | _ => .stuck "ifaceeq: three arguments"

/-- `Env.p1` with `runtime.ifaceeq` and `runtime.efaceeq` (`Runtime.ifaceEqDirect`): the
non-vacuity witness of `Env.IfaceEq`. -/
def Env.ifaceEqDemo : Env where
  extern n := if n = "runtime.ifaceeq" ∨ n = "runtime.efaceeq" then some Runtime.ifaceEqDirect
    else Env.p1.extern n

/-- **Non-vacuity of `Env.IfaceEq`**: an environment that has both calls satisfies it, for every
list of symbols. -/
theorem Env.ifaceEqDemo_ifaceEq (eq : List String × List String) : Env.ifaceEqDemo.IfaceEq eq := by
  intro name c hc s hs d x y p q m _ _ _
  have hn : name = "runtime.ifaceeq" ∨ name = "runtime.efaceeq" := hs.imp (·.1) (·.1)
  simp only [Env.ifaceEqDemo, hn, ↓reduceIte, Option.some.injEq] at hc
  subst hc
  rfl

end GoFV.SSA.Sem
