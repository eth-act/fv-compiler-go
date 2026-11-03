import GoFV.Proof.RefineLoc

/-!
# Refinement over `runSched` (L1, `docs/plans/semantics2.md` §2, §6)

* `RefinesSched tabs' f' tabs f`: every returning or panicking `runSched` of `f` is, up to
  refinement (`OutcomeRefines 0`), a `runSched` of `f'` with some fuel (L1 → L1: `late
  nilcheck`, `flagalloc`).
* `RefinesSchedL tabs' f' tabs f`: every returning or panicking `runL` of `f` is a `runSched`
  of `f'` (L0 → L1: `schedule`).
* `RefinesSchedLF tabs' f' tabs f`: the same against `runLF`, `runL` with faulting memory ops
  (`LMode.faulting`: an access to the nil page is a `nilDeref` panic, as under `runSched`).

**The faulting gap.** `runSched` faults where `runL` reads `poison`: a load from the nil page
(`Ptr.nilFault`) is `poison` under `runL` (Phase 1's loads are pure) and a `nilDeref` panic under
`runSched` (the machine). So `schedule` cannot refine `runL` on a run that loads from the nil
page and goes on. The `schedule` theorem is therefore stated against `runLF` (decision proposed on
#385 and #96), which differs from `runL` only by those faults; `RefinesSchedLF.schedL` gives
`RefinesSchedLFrom (NoNilFault tabs f)`, a `runL` refinement on the inputs where `runL` and
`runLF` agree.

All have the `…From P` forms that restrict the inputs; `runSched` is deterministic and monotone
in fuel (`runSched_mono`, `runSched_det` in `GoFV.Proof.RefineLoc`), as is `runLF`.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- `runL` with faulting memory ops: `runL`'s context (`kahn` order) in `runSched`'s mode. -/
def runLF (env : Env) (tabs : Tables) (f : Func) (args : List Val) (mem : Mem) (fuel : Nat) :
    Outcome :=
  runCtxL ⟨f.lowered, true⟩ env (Ctx.makeL tabs f) args mem fuel

theorem runLF_mono {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runLF env tabs f args mem fuel).Defined) :
    runLF env tabs f args mem fuel' = runLF env tabs f args mem fuel :=
  runCtxL_mono _ env _ args mem hle h

theorem runLF_det {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (h : (runLF env tabs f args mem fuel).Defined)
    (h' : (runLF env tabs f args mem fuel').Defined) :
    runLF env tabs f args mem fuel' = runLF env tabs f args mem fuel := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · exact runLF_mono hle h
  · exact (runLF_mono hle h').symm

/-! ## `runSched` refines `runSched` (L1 → L1) -/

/-- `f'` (tables `tabs'`) refines `f` (tables `tabs`) under `runSched`, for the inputs with `P`. -/
def RefinesSchedFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func)
    (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runSched env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runSched env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

/-- `f'` refines `f` under `runSched`, for every input. -/
def RefinesSched (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runSched env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runSched env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

theorem RefinesSched.refl (tabs : Tables) (f : Func) : RefinesSched tabs f tabs f :=
  fun _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

theorem RefinesSched.trans {t1 t2 t3 : Tables} {f1 f2 f3 : Func}
    (h12 : RefinesSched t2 f2 t1 f1) (h23 : RefinesSched t3 f3 t2 f2) :
    RefinesSched t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesSched.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables}
    {f f' : Func} (h : RefinesSched tabs' f' tabs f) : RefinesSchedFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesSchedFrom.refl (P : Env → List Val → Mem → Prop) (tabs : Tables) (f : Func) :
    RefinesSchedFrom P tabs f tabs f :=
  (RefinesSched.refl tabs f).from P

theorem RefinesSchedFrom.trans {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesSchedFrom P t2 f2 t1 f1)
    (h23 : RefinesSchedFrom P t3 f3 t2 f2) : RefinesSchedFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesSchedFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesSchedFrom P tabs' f' tabs f) : RefinesSchedFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- Equal `runSched`s refine each other. -/
theorem RefinesSched.of_runSched_eq {tabs tabs' : Tables} {f f' : Func}
    (h : ∀ env args mem fuel,
      runSched env tabs' f' args mem fuel = runSched env tabs f args mem fuel) :
    RefinesSched tabs' f' tabs f :=
  fun env args mem fuel hd => ⟨fuel, by rw [h]; exact OutcomeRefines.refl hd⟩

/-- The backward reading of `RefinesSched`. -/
theorem RefinesSched.backward {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesSched tabs' f' tabs f) {env : Env} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hs : (runSched env tabs f args mem fuel).Defined)
    (ht : (runSched env tabs' f' args mem fuel').Defined) :
    OutcomeRefines 0 (runSched env tabs f args mem fuel)
      (runSched env tabs' f' args mem fuel') := by
  obtain ⟨fuel'', h''⟩ := h env args mem fuel hs
  rw [runSched_det h''.defined_right ht]
  exact h''

/-! ## `runSched` refines `runL` and `runLF` (L0 → L1) -/

/-- `f'` (scheduled, `runSched`) refines `f` (unscheduled, `runL`), for the inputs with `P`. -/
def RefinesSchedLFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func)
    (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runL env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runL env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

/-- `f'` (scheduled) refines `f` (unscheduled, `runL`), for every input. -/
def RefinesSchedL (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runL env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runL env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

/-- `f'` (scheduled, `runSched`) refines `f` under `runLF`, for the inputs with `P`. -/
def RefinesSchedLFFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func)
    (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runLF env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runLF env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

/-- `f'` (scheduled) refines `f` under `runLF`, for every input. -/
def RefinesSchedLF (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runLF env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runLF env tabs f args mem fuel)
        (runSched env tabs' f' args mem fuel')

theorem RefinesSchedL.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables}
    {f f' : Func} (h : RefinesSchedL tabs' f' tabs f) : RefinesSchedLFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesSchedLFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesSchedLFrom P tabs' f' tabs f) : RefinesSchedLFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

theorem RefinesSchedLF.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables}
    {f f' : Func} (h : RefinesSchedLF tabs' f' tabs f) : RefinesSchedLFFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesSchedLFFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesSchedLFFrom P tabs' f' tabs f) : RefinesSchedLFFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- The inputs on which `runL` and `runLF` of `f` agree: no run accesses the nil page. -/
def NoNilFault (tabs : Tables) (f : Func) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  ∀ fuel, runLF env tabs f args mem fuel = runL env tabs f args mem fuel

/-- A `runLF` refinement is a `runL` one on the inputs without nil-page accesses. -/
theorem RefinesSchedLFFrom.schedL {P : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (h : RefinesSchedLFFrom P tabs' f' tabs f) :
    RefinesSchedLFrom (fun env args mem => P env args mem ∧ NoNilFault tabs f env args mem)
      tabs' f' tabs f := by
  intro env args mem ⟨hP, hN⟩ fuel hd
  rw [← hN fuel] at hd ⊢
  exact h env args mem hP fuel hd

theorem RefinesSchedLF.schedL {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesSchedLF tabs' f' tabs f) :
    RefinesSchedLFrom (NoNilFault tabs f) tabs' f' tabs f :=
  ((h.from fun _ _ _ => True).schedL).mono fun _ _ _ hN => ⟨trivial, hN⟩

/-! ## Composition -/

/-- `runL` refinements (`lower` … `layout`) followed by `schedule`. -/
theorem RefinesLFrom.trans_schedL {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesLFrom P t2 f2 t1 f1) (h23 : RefinesSchedLFrom P t3 f3 t2 f2) :
    RefinesSchedLFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesL.trans_schedL {t1 t2 t3 : Tables} {f1 f2 f3 : Func}
    (h12 : RefinesL t2 f2 t1 f1) (h23 : RefinesSchedL t3 f3 t2 f2) :
    RefinesSchedL t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- `schedule` followed by `runSched` refinements (`late nilcheck`, `flagalloc`). -/
theorem RefinesSchedLFrom.trans_sched {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesSchedLFrom P t2 f2 t1 f1)
    (h23 : RefinesSchedFrom P t3 f3 t2 f2) : RefinesSchedLFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesSchedL.trans_sched {t1 t2 t3 : Tables} {f1 f2 f3 : Func}
    (h12 : RefinesSchedL t2 f2 t1 f1) (h23 : RefinesSched t3 f3 t2 f2) :
    RefinesSchedL t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesSchedLFFrom.trans_sched {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesSchedLFFrom P t2 f2 t1 f1)
    (h23 : RefinesSchedFrom P t3 f3 t2 f2) : RefinesSchedLFFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesSchedLF.trans_sched {t1 t2 t3 : Tables} {f1 f2 f3 : Func}
    (h12 : RefinesSchedLF t2 f2 t1 f1) (h23 : RefinesSched t3 f3 t2 f2) :
    RefinesSchedLF t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- The scheduled passes followed by `regalloc` (`RefinesLS`, L1 → L2). -/
theorem RefinesSchedFrom.trans_ls {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesSchedFrom P t2 f2 t1 f1) (h23 : RefinesLSFrom P t3 f3 t2 f2) :
    RefinesLSFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- A source `runSched` returning one integer gives a target `runSched` returning the same
integer (what the non-vacuity witnesses read off a refinement). -/
theorem RefinesSched.returned_int {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesSched tabs' f' tabs f) {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat}
    {w : Width} {x : BitVec w.bits} (hs : runSched env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', runSched env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize runSched env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

/-- `RefinesSched.returned_int` for `RefinesSchedLF`. -/
theorem RefinesSchedLF.returned_int {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesSchedLF tabs' f' tabs f) {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat}
    {w : Width} {x : BitVec w.bits} (hs : runLF env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', runSched env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize runSched env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof
