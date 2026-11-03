import GoFV.Proof.Refine
import GoFV.SSA.Sem.RunL

/-!
# Refinement over `runL` (L0 → L0, `docs/plans/semantics2.md` §2)

`RefinesL tabs' f' tabs f`: every returning or panicking `runL` of `f` is, up to refinement
(`OutcomeRefines 0`), a `runL` of `f'` with some fuel; Phase 1's `Refines` with `runL` for `run`
on both sides. `RefinesLFrom P` restricts the inputs as `RefinesFrom` does. `runLoopL` is
deterministic and monotone in fuel (`runLoopL_mono`, `runL_mono`, `runL_det`), so the backward
reading holds as in Phase 1 (`RefinesL.backward`).

On functions without arm64 ops or block kinds `runL = run` (`runL_generic`), so a Phase 1
refinement between two such functions is a `RefinesL` one (`RefinesL.of_generic`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## Fuel monotonicity of `runLoopL` -/

theorem runLoopL_succ (md : LMode) (env : Env) (ctx : Ctx) (fuel : Nat) (fr : Frame) (bid : ID)
    (i : Nat) : runLoopL md env ctx (fuel + 1) fr bid i =
      match ctx.f.block? bid with
      | none => .stuck s!"b{bid} is not in the function"
      | some b =>
        match enterBlockL md env ctx fr b i with
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg
        | .ok fr =>
          match stepTermL fr b with
          | .ok (.goto e) => runLoopL md env ctx fuel fr e.b e.i
          | .ok (.ret rs m) => .returned rs m
          | .panic e m => .panicked e m
          | .stuck msg => .stuck msg := (rfl)

/-- A defined `runLoopL` outcome does not change with more fuel. -/
theorem runLoopL_mono (md : LMode) (env : Env) (ctx : Ctx) :
    ∀ (fuel k : Nat) (fr : Frame) (b : ID) (i : Nat), (runLoopL md env ctx fuel fr b i).Defined →
      runLoopL md env ctx (fuel + k) fr b i = runLoopL md env ctx fuel fr b i := by
  intro fuel
  induction fuel with
  | zero => intro k fr b i h; exact h.elim
  | succ n ih =>
    intro k fr b i h
    rw [Nat.add_right_comm, runLoopL_succ, runLoopL_succ]
    rw [runLoopL_succ] at h
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

theorem runCtxL_mono (md : LMode) (env : Env) (ctx : Ctx) (args : List Val) (mem : Mem)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runCtxL md env ctx args mem fuel).Defined) :
    runCtxL md env ctx args mem fuel' = runCtxL md env ctx args mem fuel := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold runCtxL at h ⊢
  split
  · rfl
  · next hn =>
    simp only [hn] at h
    rw [runLoopL_mono md env ctx _ k _ _ _ (finish_defined h)]

theorem runL_mono {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runL env tabs f args mem fuel).Defined) :
    runL env tabs f args mem fuel' = runL env tabs f args mem fuel :=
  runCtxL_mono _ env _ args mem hle h

/-- Two defined `runL`s of the same function (with any fuels) have the same outcome. -/
theorem runL_det {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (h : (runL env tabs f args mem fuel).Defined)
    (h' : (runL env tabs f args mem fuel').Defined) :
    runL env tabs f args mem fuel' = runL env tabs f args mem fuel := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · exact runL_mono hle h
  · exact (runL_mono hle h').symm

/-! ## Refinement of lowered functions -/

/-- `f'` (tables `tabs'`) refines `f` (tables `tabs`) under `runL`, for the inputs with `P`. -/
def RefinesLFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func) (tabs : Tables)
    (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runL env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runL env tabs f args mem fuel) (runL env tabs' f' args mem fuel')

/-- `f'` refines `f` under `runL`, for every input. -/
def RefinesL (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runL env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runL env tabs f args mem fuel) (runL env tabs' f' args mem fuel')

theorem RefinesL.refl (tabs : Tables) (f : Func) : RefinesL tabs f tabs f :=
  fun _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

theorem RefinesL.trans {t1 t2 t3 : Tables} {f1 f2 f3 : Func} (h12 : RefinesL t2 f2 t1 f1)
    (h23 : RefinesL t3 f3 t2 f2) : RefinesL t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesL.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesL tabs' f' tabs f) : RefinesLFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesLFrom.refl (P : Env → List Val → Mem → Prop) (tabs : Tables) (f : Func) :
    RefinesLFrom P tabs f tabs f :=
  (RefinesL.refl tabs f).from P

theorem RefinesLFrom.trans {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesLFrom P t2 f2 t1 f1) (h23 : RefinesLFrom P t3 f3 t2 f2) :
    RefinesLFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesLFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesLFrom P tabs' f' tabs f) : RefinesLFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- Equal `runL`s refine each other. -/
theorem RefinesL.of_runL_eq {tabs tabs' : Tables} {f f' : Func}
    (h : ∀ env args mem fuel, runL env tabs' f' args mem fuel = runL env tabs f args mem fuel) :
    RefinesL tabs' f' tabs f :=
  fun env args mem fuel hd => ⟨fuel, by rw [h]; exact OutcomeRefines.refl hd⟩

/-- A Phase 1 refinement between functions without arm64 ops or block kinds is a `runL` one. -/
theorem RefinesLFrom.of_generic {P : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hf : f.lowered = false) (hf' : f'.lowered = false)
    (h : RefinesFrom P tabs' f' tabs f) : RefinesLFrom P tabs' f' tabs f := by
  intro env args mem hP fuel hd
  rw [runL_generic env tabs hf] at hd ⊢
  obtain ⟨fuel', ho⟩ := h env args mem hP fuel hd
  exact ⟨fuel', by rw [runL_generic env tabs' hf']; exact ho⟩

/-- The backward reading: when the source is defined, every defined `runL` of the target is a
run of the source, up to refinement. -/
theorem RefinesL.backward {tabs tabs' : Tables} {f f' : Func} (h : RefinesL tabs' f' tabs f)
    {env : Env} {args : List Val} {mem : Mem} {fuel fuel' : Nat}
    (hs : (runL env tabs f args mem fuel).Defined) (ht : (runL env tabs' f' args mem fuel').Defined) :
    OutcomeRefines 0 (runL env tabs f args mem fuel) (runL env tabs' f' args mem fuel') := by
  obtain ⟨fuel'', h''⟩ := h env args mem fuel hs
  rw [runL_det h''.defined_right ht]
  exact h''

/-- A source `runL` returning one integer gives a target `runL` returning the same integer (in a
refined memory; what the non-vacuity witnesses read off a refinement). -/
theorem RefinesL.returned_int {tabs tabs' : Tables} {f f' : Func} (h : RefinesL tabs' f' tabs f)
    {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat} {w : Width} {x : BitVec w.bits}
    (hs : runL env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', runL env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize runL env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof
