import GoFV.Proof.RefineL
import GoFV.SSA.Sem.RunSched
import GoFV.SSA.Sem.RunLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# Refinement over `runSched` and `runLoc` (L1, L2; `docs/plans/semantics2.md` §2)

`runSched` is `runCtxL` in the scheduled mode, so it inherits `runCtxL_mono`: `runSched_mono`,
`runSched_det`. `runLoopLoc` is deterministic and monotone in fuel (`runLoopLoc_mono`), hence
`runLoc_mono`, `runLoc_det`.

* `RefinesLoc tabs' f' tabs f`: every returning or panicking `runLoc` of `f` is, up to refinement
  (`OutcomeRefines 0`), a `runLoc` of `f'` with some fuel (L2 → L2: `loop rotate`, `trim`).
* `RefinesLS tabs' f' tabs f`: every returning or panicking `runSched` of `f` is a `runLoc` of
  `f'` (L1 → L2: `regalloc`).

Both have the `…From P` forms that restrict the inputs, as `RefinesLFrom`.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## `runSched` -/

theorem runSched_mono {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runSched env tabs f args mem fuel).Defined) :
    runSched env tabs f args mem fuel' = runSched env tabs f args mem fuel :=
  runCtxL_mono _ env _ args mem hle h

/-- Two defined `runSched`s of the same function (with any fuels) have the same outcome. -/
theorem runSched_det {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (h : (runSched env tabs f args mem fuel).Defined)
    (h' : (runSched env tabs f args mem fuel').Defined) :
    runSched env tabs f args mem fuel' = runSched env tabs f args mem fuel := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · exact runSched_mono hle h
  · exact (runSched_mono hle h').symm

/-! ## `runLoc` -/

theorem runLoopLoc_succ (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) (bid : ID) :
    runLoopLoc env lc (fuel + 1) s bid =
      match lc.ctx.f.block? bid with
      | none => .stuck s!"b{bid} is not in the function"
      | some b =>
        match enterBlockLoc env lc s b with
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg
        | .ok s =>
          match stepTermLoc lc s b with
          | .ok (.goto e, s) => runLoopLoc env lc fuel s e.b
          | .ok (.ret rs m, _) => .returned rs m
          | .panic e m => .panicked e m
          | .stuck msg => .stuck msg := (rfl)

/-- A defined `runLoopLoc` outcome does not change with more fuel. -/
theorem runLoopLoc_mono (env : Env) (lc : LocCtx) :
    ∀ (fuel k : Nat) (s : LocState) (b : ID), (runLoopLoc env lc fuel s b).Defined →
      runLoopLoc env lc (fuel + k) s b = runLoopLoc env lc fuel s b := by
  intro fuel
  induction fuel with
  | zero => intro k s b h; exact h.elim
  | succ n ih =>
    intro k s b h
    rw [Nat.add_right_comm, runLoopLoc_succ, runLoopLoc_succ]
    rw [runLoopLoc_succ] at h
    split
    · rfl
    · split
      · rfl
      · rfl
      · split
        · next e _ _ => split at h <;> simp_all
        · rfl
        · rfl
        · rfl

theorem runCtxLoc_mono (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem)
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runCtxLoc env lc args mem fuel).Defined) :
    runCtxLoc env lc args mem fuel' = runCtxLoc env lc args mem fuel := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  unfold runCtxLoc at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · next hn =>
    simp only [hn] at h
    rw [runLoopLoc_mono env lc _ k _ _ (finish_defined h)]

theorem runLoc_mono {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel') (h : (runLoc env tabs f args mem fuel).Defined) :
    runLoc env tabs f args mem fuel' = runLoc env tabs f args mem fuel :=
  runCtxLoc_mono env _ args mem hle h

/-- Two defined `runLoc`s of the same function (with any fuels) have the same outcome. -/
theorem runLoc_det {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel fuel' : Nat} (h : (runLoc env tabs f args mem fuel).Defined)
    (h' : (runLoc env tabs f args mem fuel').Defined) :
    runLoc env tabs f args mem fuel' = runLoc env tabs f args mem fuel := by
  rcases Nat.le_total fuel fuel' with hle | hle
  · exact runLoc_mono hle h
  · exact (runLoc_mono hle h').symm

/-! ## Refinement of allocated functions (L2 → L2) -/

/-- `f'` (tables `tabs'`) refines `f` (tables `tabs`) under `runLoc`, for the inputs with `P`. -/
def RefinesLocFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func)
    (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runLoc env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runLoc env tabs f args mem fuel)
        (runLoc env tabs' f' args mem fuel')

/-- `f'` refines `f` under `runLoc`, for every input. -/
def RefinesLoc (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runLoc env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runLoc env tabs f args mem fuel)
        (runLoc env tabs' f' args mem fuel')

theorem RefinesLoc.refl (tabs : Tables) (f : Func) : RefinesLoc tabs f tabs f :=
  fun _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

theorem RefinesLoc.trans {t1 t2 t3 : Tables} {f1 f2 f3 : Func} (h12 : RefinesLoc t2 f2 t1 f1)
    (h23 : RefinesLoc t3 f3 t2 f2) : RefinesLoc t3 f3 t1 f1 := by
  intro env args mem fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesLoc.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesLoc tabs' f' tabs f) : RefinesLocFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesLocFrom.refl (P : Env → List Val → Mem → Prop) (tabs : Tables) (f : Func) :
    RefinesLocFrom P tabs f tabs f :=
  (RefinesLoc.refl tabs f).from P

theorem RefinesLocFrom.trans {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesLocFrom P t2 f2 t1 f1) (h23 : RefinesLocFrom P t3 f3 t2 f2) :
    RefinesLocFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem RefinesLocFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesLocFrom P tabs' f' tabs f) : RefinesLocFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- Equal `runLoc`s refine each other. -/
theorem RefinesLoc.of_runLoc_eq {tabs tabs' : Tables} {f f' : Func}
    (h : ∀ env args mem fuel, runLoc env tabs' f' args mem fuel = runLoc env tabs f args mem fuel) :
    RefinesLoc tabs' f' tabs f :=
  fun env args mem fuel hd => ⟨fuel, by rw [h]; exact OutcomeRefines.refl hd⟩

/-- The backward reading: when the source is defined, every defined `runLoc` of the target is a
run of the source, up to refinement. -/
theorem RefinesLoc.backward {tabs tabs' : Tables} {f f' : Func} (h : RefinesLoc tabs' f' tabs f)
    {env : Env} {args : List Val} {mem : Mem} {fuel fuel' : Nat}
    (hs : (runLoc env tabs f args mem fuel).Defined)
    (ht : (runLoc env tabs' f' args mem fuel').Defined) :
    OutcomeRefines 0 (runLoc env tabs f args mem fuel) (runLoc env tabs' f' args mem fuel') := by
  obtain ⟨fuel'', h''⟩ := h env args mem fuel hs
  rw [runLoc_det h''.defined_right ht]
  exact h''

/-! ## Refinement of a scheduled function by an allocated one (L1 → L2) -/

/-- `f'` (allocated, tables `tabs'`, `runLoc`) refines `f` (scheduled, tables `tabs`,
`runSched`), for the inputs with `P`. -/
def RefinesLSFrom (P : Env → List Val → Mem → Prop) (tabs' : Tables) (f' : Func) (tabs : Tables)
    (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (runSched env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runSched env tabs f args mem fuel)
        (runLoc env tabs' f' args mem fuel')

/-- `f'` (allocated) refines `f` (scheduled), for every input. -/
def RefinesLS (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem) (fuel : Nat),
    (runSched env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (runSched env tabs f args mem fuel)
        (runLoc env tabs' f' args mem fuel')

theorem RefinesLS.from (P : Env → List Val → Mem → Prop) {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesLS tabs' f' tabs f) : RefinesLSFrom P tabs' f' tabs f :=
  fun env args mem _ => h env args mem

theorem RefinesLSFrom.mono {P Q : Env → List Val → Mem → Prop} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : RefinesLSFrom P tabs' f' tabs f) : RefinesLSFrom Q tabs' f' tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-- An allocated refinement followed by `runLoc` refinements (`loop rotate`, `trim`). -/
theorem RefinesLSFrom.trans_loc {P : Env → List Val → Mem → Prop} {t1 t2 t3 : Tables}
    {f1 f2 f3 : Func} (h12 : RefinesLSFrom P t2 f2 t1 f1) (h23 : RefinesLocFrom P t3 f3 t2 f2) :
    RefinesLSFrom P t3 f3 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

/-- The backward reading of `RefinesLS`. -/
theorem RefinesLS.backward {tabs tabs' : Tables} {f f' : Func} (h : RefinesLS tabs' f' tabs f)
    {env : Env} {args : List Val} {mem : Mem} {fuel fuel' : Nat}
    (hs : (runSched env tabs f args mem fuel).Defined)
    (ht : (runLoc env tabs' f' args mem fuel').Defined) :
    OutcomeRefines 0 (runSched env tabs f args mem fuel) (runLoc env tabs' f' args mem fuel') := by
  obtain ⟨fuel'', h''⟩ := h env args mem fuel hs
  rw [runLoc_det h''.defined_right ht]
  exact h''

end GoFV.Proof
