import GoFV.SSA.Sem.Run
import GoFV.Proof.FinishMono

variable [GoFV.SSA.Sem.Addrs]

/-!
# Refinement of functions (`docs/PLAN.md` §1)

A pass is correct when every run of the source that returns or panics is also a run of the
target, up to the refinement order on values (`Sem.Refines`: a source `poison` is refined by
anything); stuck and out-of-fuel source runs carry no obligation. `Refines tabs' f' tabs f`
states this for a target `f'` (with the tables `tabs'` of its section) and a source `f` (tables
`tabs`), for every environment, argument list, initial memory and fuel. The target may need a
different amount of fuel (passes that merge or delete blocks).

The statement is forward (source outcome ⇒ target outcome); since `run` is deterministic and
monotone in fuel (`runLoop_mono`), it gives the backward reading "every terminating run of the
target is a run of the source, unless the source is undefined" (`Refines.backward`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## Outcomes -/

/-- The source outcome `o` is refined by the target outcome `o'` (for a run of activation
`act`): results refined pointwise with a refined memory (`Mem.Refines`: a rewrite may make a
poison value defined, which may then be stored), or the same panic with refined memories once
the frames of `act` and of its callees are dropped (`Mem.dropFrames`: they are not observable
after a panic; the caller's frames, the heap and the globals are). -/
inductive OutcomeRefines (act : Nat) : Outcome → Outcome → Prop where
  | returned {rs rs' : List Val} {m m' : Mem} : RefinesList rs rs' → Mem.Refines m m' →
      OutcomeRefines act (.returned rs m) (.returned rs' m')
  | panicked (e : Panic) {m m' : Mem} : Mem.Refines (m.dropFrames act) (m'.dropFrames act) →
      OutcomeRefines act (.panicked e m) (.panicked e m')

theorem OutcomeRefines.refl {act : Nat} {o : Outcome} (h : o.Defined) : OutcomeRefines act o o := by
  cases o with
  | returned rs m => exact .returned (RefinesList.refl rs) (Mem.Refines.refl m)
  | panicked e m => exact .panicked e (Mem.Refines.refl _)
  | stuck => exact h.elim
  | outOfFuel => exact h.elim

theorem OutcomeRefines.trans {act : Nat} {a b c : Outcome} :
    OutcomeRefines act a b → OutcomeRefines act b c → OutcomeRefines act a c
  | .returned h1 m1, .returned h2 m2 => .returned (Sem.RefinesList.trans h1 h2) (m1.trans m2)
  | .panicked e m1, .panicked _ m2 => .panicked e (m1.trans m2)

theorem OutcomeRefines.defined_left {act : Nat} {a b : Outcome} (h : OutcomeRefines act a b) :
    a.Defined := by
  cases h <;> trivial

theorem OutcomeRefines.defined_right {act : Nat} {a b : Outcome} (h : OutcomeRefines act a b) :
    b.Defined := by
  cases h <;> trivial

/-- Equal memories at a panic refine each other (what lock-step simulations produce). -/
theorem OutcomeRefines.panicked_refl {act : Nat} (e : Panic) (m : Mem) :
    OutcomeRefines act (.panicked e m) (.panicked e m) :=
  .panicked e (Mem.Refines.refl _)

/-- Related outcomes of `runLoop` (the input of `finish`): refined results in a refined memory,
or the same panic with memories related by `P`. The panicking activation's deferred calls see its
frame (`finish`, §9.7), so lock-step simulations relate panics by equality (`finish_refines`);
`Mem.Refines` needs monotone contracts (`GoFV.Proof.finish_refines_mono`). -/
inductive LoopRefines (P : Mem → Mem → Prop) : Outcome → Outcome → Prop where
  | returned {rs rs' : List Val} {m m' : Mem} : RefinesList rs rs' → Mem.Refines m m' →
      LoopRefines P (.returned rs m) (.returned rs' m')
  | panicked (e : Panic) {m m' : Mem} : P m m' → LoopRefines P (.panicked e m) (.panicked e m')

/-- Equal memories at a panic (what lock-step simulations produce). -/
theorem LoopRefines.panicked_refl (e : Panic) (m : Mem) :
    LoopRefines Eq (.panicked e m) (.panicked e m) :=
  .panicked e rfl

theorem LoopRefines.refl {o : Outcome} (h : o.Defined) : LoopRefines Eq o o := by
  cases o with
  | returned rs m => exact .returned (RefinesList.refl rs) (Mem.Refines.refl m)
  | panicked e m => exact .panicked e rfl
  | stuck => exact h.elim
  | outOfFuel => exact h.elim

theorem LoopRefines.defined_left {P : Mem → Mem → Prop} {a b : Outcome}
    (h : LoopRefines P a b) : a.Defined := by
  cases h <;> trivial

theorem LoopRefines.defined_right {P : Mem → Mem → Prop} {a b : Outcome}
    (h : LoopRefines P a b) : b.Defined := by
  cases h <;> trivial

/-- `finish` of returned outcomes (Go-typed results, frame removal) preserves refinement. -/
theorem finish_returned_refines {env : Env} {outs : Array (Option AuxRef × Ty × Nat)}
    {di : DeferInfo} {act k : Nat} {rs rs' : List Val} {m m' : Mem}
    (hd : (finish env outs di act (.returned rs m)).Defined) (hr : RefinesList rs rs')
    (hm : Mem.Refines m m') :
    OutcomeRefines k (finish env outs di act (.returned rs m))
      (finish env outs di act (.returned rs' m')) := by
  by_cases hp : Val.anyPoison rs = true
  · simp only [finish, hp, ite_true] at hd; exact hd.elim
  · have hp' : Val.anyPoison rs = false := by simpa using hp
    have hp'' := (hr.noPoison hp').1
    simp only [finish, hp', hp'', Bool.false_eq_true, ↓reduceIte] at hd ⊢
    have hg := goResults_mono (outs := outs) (act := act) hp' hr hm
    revert hd
    generalize goResults outs act rs m = g at hg ⊢
    generalize goResults outs act rs' m' = g' at hg ⊢
    cases hg with
    | ok hv => intro _; exact .returned hv (hm.freeFrame act)
    | panic e hm' => intro _; exact .panicked e (hm'.dropFrames k)
    | stuck msg r => intro hd; exact hd.elim

/-- **`finish` preserves refinement** of loop outcomes that panic with equal memories. -/
theorem finish_refines {env : Env} {outs : Array (Option AuxRef × Ty × Nat)} {di : DeferInfo}
    {act k : Nat} {o o' : Outcome} (hd : (finish env outs di act o).Defined)
    (h : LoopRefines Eq o o') :
    OutcomeRefines k (finish env outs di act o) (finish env outs di act o') := by
  cases h with
  | panicked e hm => subst hm; exact OutcomeRefines.refl hd
  | returned hr hm => exact finish_returned_refines hd hr hm

/-! ## Fuel monotonicity -/

/-- A defined `runLoop` outcome does not change with more fuel. -/
theorem runLoop_mono (env : Env) (ctx : Ctx) :
    ∀ (fuel k : Nat) (fr : Frame) (b : ID) (i : Nat), (runLoop env ctx fuel fr b i).Defined →
      runLoop env ctx (fuel + k) fr b i = runLoop env ctx fuel fr b i := by
  intro fuel
  induction fuel with
  | zero => intro k fr b i h; exact h.elim
  | succ n ih =>
    intro k fr b i h
    rw [Nat.add_right_comm, runLoop_succ, runLoop_succ]
    rw [runLoop_succ] at h
    split
    · rfl
    · split
      · rfl
      · rfl
      · split
        · next e _ => split at h <;> simp_all
        · rfl
        · rfl
        · rfl

theorem runCtx_mono (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem) {fuel fuel' : Nat}
    (hle : fuel ≤ fuel') (h : (runCtx env ctx args mem fuel).Defined) :
    runCtx env ctx args mem fuel' = runCtx env ctx args mem fuel := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold runCtx at h ⊢
  split
  · rfl
  · next hn =>
    simp only [hn] at h
    rw [runLoop_mono env ctx _ k _ _ _ (finish_defined h)]

theorem run_mono {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (run env tabs f args mem fuel).Defined) :
    run env tabs f args mem fuel' = run env tabs f args mem fuel :=
  runCtx_mono env _ args mem hle h

/-- Two defined runs of the same function (with any fuels) have the same outcome. -/
theorem run_det {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (h : (run env tabs f args mem fuel).Defined)
    (h' : (run env tabs f args mem fuel').Defined) :
    run env tabs f args mem fuel' = run env tabs f args mem fuel := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · exact run_mono hle h
  · exact (run_mono hle h').symm

/-! ## Refinement of functions -/

/-- `f'` (with tables `tabs'`) refines `f` (with tables `tabs`): every returning or panicking
run of `f` is, up to value refinement, a run of `f'` with some fuel (`OutcomeRefines 0`: a
top-level run is activation `(Ctx.make tabs f).act = 0`). -/
def Refines (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (run env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (run env tabs f args mem fuel) (run env tabs' f' args mem fuel')

theorem Refines.refl (tabs : Tables) (f : Func) : Refines tabs f tabs f :=
  fun _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

/-- Refinement composes: the correctness of a pipeline from that of its passes. -/
theorem Refines.trans {t1 t2 t3 : Tables} {f1 f2 f3 : Func} (h12 : Refines t2 f2 t1 f1)
    (h23 : Refines t3 f3 t2 f2) : Refines t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- `Refines` restricted to the environments with `P` (e.g. monotone contracts). -/
def RefinesUnder (P : Env → Prop) (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env), P env → ∀ (args : List Val) (mem : Mem) (fuel : Nat),
    (run env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (run env tabs f args mem fuel) (run env tabs' f' args mem fuel')

theorem Refines.under (P : Env → Prop) {tabs tabs' : Tables} {f f' : Func}
    (h : Refines tabs' f' tabs f) : RefinesUnder P tabs' f' tabs f :=
  fun env _ => h env

theorem RefinesUnder.refl (P : Env → Prop) (tabs : Tables) (f : Func) :
    RefinesUnder P tabs f tabs f :=
  (Refines.refl tabs f).under P

theorem RefinesUnder.trans {P : Env → Prop} {t1 t2 t3 : Tables} {f1 f2 f3 : Func}
    (h12 : RefinesUnder P t2 f2 t1 f1) (h23 : RefinesUnder P t3 f3 t2 f2) :
    RefinesUnder P t3 f3 t1 f1 := by
  intro env hP args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env hP args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env hP args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- `Refines` restricted to the inputs `(env, args, mem)` with `P` (e.g. frame-safe contracts
and inputs that hold no pointer into the run's frame temporaries, `Sem.InitAvoids`). -/
def RefinesFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func) (tabs : Tables)
    (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (run env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (run env tabs f args mem fuel) (run env tabs' f' args mem fuel')

theorem RefinesUnder.from {P : Env → Prop} {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesUnder P tabs' f' tabs f) : RefinesFrom (fun env _ _ => P env) tabs' f' tabs f :=
  fun env args mem hP => h env hP args mem

theorem Refines.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables} {f f' : Func}
    (h : Refines tabs' f' tabs f) : RefinesFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesFrom.trans {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesFrom P t2 f2 t1 f1) (h23 : RefinesFrom P t3 f3 t2 f2) :
    RefinesFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesFrom P tabs' f' tabs f) : RefinesFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- Equal runs refine each other. -/
theorem Refines.of_run_eq {tabs tabs' : Tables} {f f' : Func}
    (h : ∀ env args mem fuel, run env tabs' f' args mem fuel = run env tabs f args mem fuel) :
    Refines tabs' f' tabs f :=
  fun env args mem fuel hd => ⟨fuel, by rw [h]; exact OutcomeRefines.refl hd⟩

/-- The backward reading (`docs/PLAN.md` §1): when the source is defined (with some fuel),
every defined run of the target (with any fuel) is a run of the source, up to refinement. -/
theorem Refines.backward {tabs tabs' : Tables} {f f' : Func} (h : Refines tabs' f' tabs f)
    {env : Env} {args : List Val} {mem : Mem} {fuel fuel' : Nat}
    (hs : (run env tabs f args mem fuel).Defined) (ht : (run env tabs' f' args mem fuel').Defined) :
    OutcomeRefines 0 (run env tabs f args mem fuel) (run env tabs' f' args mem fuel') := by
  obtain ⟨fuel'', h''⟩ := h env args mem fuel hs
  rw [run_det h''.defined_right ht]
  exact h''

/-- A source run returning one integer gives a target run returning the same integer (in a
refined memory; what the non-vacuity witnesses read off a refinement). -/
theorem Refines.returned_int {tabs tabs' : Tables} {f f' : Func} (h : Refines tabs' f' tabs f)
    {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat} {w : Width} {x : BitVec w.bits}
    (hs : run env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', run env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize run env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof
