import GoFV.SSA.Sem.Run
import GoFV.Proof.FinishMono

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

/-- The source outcome `o` is refined by the target outcome `o'`: the same panic with a refined
memory, or results refined pointwise with a refined memory (`Mem.Refines`: a rewrite may make a
poison value defined, which may then be stored). -/
inductive OutcomeRefines : Outcome → Outcome → Prop where
  | returned {rs rs' : List Val} {m m' : Mem} : RefinesList rs rs' → Mem.Refines m m' →
      OutcomeRefines (.returned rs m) (.returned rs' m')
  | panicked (e : Panic) {m m' : Mem} : Mem.Refines m m' →
      OutcomeRefines (.panicked e m) (.panicked e m')

theorem OutcomeRefines.refl {o : Outcome} (h : o.Defined) : OutcomeRefines o o := by
  cases o with
  | returned rs m => exact .returned (RefinesList.refl rs) (Mem.Refines.refl m)
  | panicked e m => exact .panicked e (Mem.Refines.refl m)
  | stuck => exact h.elim
  | outOfFuel => exact h.elim

theorem OutcomeRefines.trans {a b c : Outcome} :
    OutcomeRefines a b → OutcomeRefines b c → OutcomeRefines a c
  | .returned h1 m1, .returned h2 m2 => .returned (Sem.RefinesList.trans h1 h2) (m1.trans m2)
  | .panicked e m1, .panicked _ m2 => .panicked e (m1.trans m2)

theorem OutcomeRefines.defined_left {a b : Outcome} (h : OutcomeRefines a b) : a.Defined := by
  cases h <;> trivial

theorem OutcomeRefines.defined_right {a b : Outcome} (h : OutcomeRefines a b) : b.Defined := by
  cases h <;> trivial

/-- `finish` (Go-typed results, frame removal) preserves outcome refinement. -/
theorem finish_refines {outs : Array (Option AuxRef × Ty × Nat)} {act : Nat} {o o' : Outcome}
    (hd : (finish outs act o).Defined) (h : OutcomeRefines o o') :
    OutcomeRefines (finish outs act o) (finish outs act o') := by
  cases h with
  | panicked e hm => exact .panicked e hm
  | @returned rs rs' m m' hr hm =>
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
      | panic e hm' => intro _; exact .panicked e hm'
      | stuck msg r => intro hd; exact hd.elim

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
run of `f` is, up to value refinement, a run of `f'` with some fuel. -/
def Refines (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (run env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines (run env tabs f args mem fuel) (run env tabs' f' args mem fuel')

theorem Refines.refl (tabs : Tables) (f : Func) : Refines tabs f tabs f :=
  fun _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

/-- Refinement composes: the correctness of a pipeline from that of its passes. -/
theorem Refines.trans {t1 t2 t3 : Tables} {f1 f2 f3 : Func} (h12 : Refines t2 f2 t1 f1)
    (h23 : Refines t3 f3 t2 f2) : Refines t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

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
    OutcomeRefines (run env tabs f args mem fuel) (run env tabs' f' args mem fuel') := by
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
