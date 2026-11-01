import GoFV.Opt.RewriteCheck

/-!
# What a checked rewrite pass returns (issue #113)

`checkedRewrite t` returns either its input with the input's tables, or a result the validator
(`GoFV.Opt.RewriteCheck.validate`) accepted in the result's tables, which the input cannot tell
from its own (`GoFV.Opt.tabsAgree`), against the rewrite log and a function `f₃` obtained from the
input by the log's nil-check eliminations (`RewriteCheck.nilOK`), then its Load-of-Store
forwardings (`RewriteCheck.fwdRel`), then its struct-store splits (`RewriteCheck.ssRel`, all
issue #151), each step optional; a validated result has the atom, closure and replay facts the
refinement proof consumes.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.Opt GoFV.Rules

theorem ssAccepts_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    {log : Array RwEvent} (h : RewriteCheck.ssAccepts penv t f out log = true) :
    ∃ f₃ log₃, (f₃ = f ∨ (RewriteCheck.ssRel out.tables f f₃ = true ∧
      checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
      RewriteCheck.validate out.tables t f₃ out.func log₃ = true := by
  unfold RewriteCheck.ssAccepts at h
  split at h
  next f' log' _ =>
  split at h
  · exact ⟨f, log, .inl rfl, h⟩
  · simp only [Bool.and_eq_true] at h
    exact ⟨f', log', .inr ⟨h.1.1, h.1.2⟩, h.2⟩

theorem fwdAccepts_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    {log : Array RwEvent} (h : RewriteCheck.fwdAccepts penv t f out log = true) :
    ∃ f₂, (f₂ = f ∨ (RewriteCheck.fwdRel out.tables f f₂ = true ∧
      checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
      ∃ f₃ log₃, (f₃ = f₂ ∨ (RewriteCheck.ssRel out.tables f₂ f₃ = true ∧
        checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
        RewriteCheck.validate out.tables t f₃ out.func log₃ = true := by
  unfold RewriteCheck.fwdAccepts at h
  split at h
  next f' log' _ =>
  split at h
  · exact ⟨f, .inl rfl, ssAccepts_cases h⟩
  · simp only [Bool.and_eq_true] at h
    exact ⟨f', .inr ⟨h.1.1, h.1.2⟩, ssAccepts_cases h.2⟩

/-- What an accepted run (`checkedRun`) returns. -/
theorem checkedRun_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRun t penv f = .ok (some out)) :
    tabsAgree penv.tables out.tables f = true ∧
      ∃ f₁, (f₁ = f ∨ RewriteCheck.nilOK penv out.tables f f₁ = true) ∧
      ∃ f₂, (f₂ = f₁ ∨ (RewriteCheck.fwdRel out.tables f₁ f₂ = true ∧
        checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
        ∃ f₃ log₃, (f₃ = f₂ ∨ (RewriteCheck.ssRel out.tables f₂ f₃ = true ∧
          checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
          RewriteCheck.validate out.tables t f₃ out.func log₃ = true := by
  unfold checkedRun at h
  cases hr : rewriteRun t true true penv f with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    split at h
    · next hv =>
      cases h
      rw [RewriteCheck.accepts, Bool.and_eq_true] at hv
      obtain ⟨hta, hv⟩ := hv
      refine ⟨hta, ?_⟩
      split at hv
      next f' log' _ =>
      split at hv
      · exact ⟨f, .inl rfl, fwdAccepts_cases hv⟩
      · rw [Bool.and_eq_true] at hv
        exact ⟨f', .inr hv.1, fwdAccepts_cases hv.2⟩
    · cases h

/-- The replay does not read the table's forwardings or struct-store splits. -/
theorem replay_noLoads (tabs : Tables) (t : Interp.Table) (f : Func) :
    ∀ (M : RewriteCheck.Defs) (B : RewriteCheck.BMap) (evs : List RwEvent),
      RewriteCheck.replay tabs { t with loads := #[] } f M B evs =
        RewriteCheck.replay tabs t f M B evs
  | _, _, [] => rfl
  | M, B, ev :: evs => by
    cases ev <;> simp only [RewriteCheck.replay, replay_noLoads tabs t f _ _ evs]

theorem replay_noSS (tabs : Tables) (t : Interp.Table) (f : Func) :
    ∀ (M : RewriteCheck.Defs) (B : RewriteCheck.BMap) (evs : List RwEvent),
      RewriteCheck.replay tabs { t with structStores := #[] } f M B evs =
        RewriteCheck.replay tabs t f M B evs
  | _, _, [] => rfl
  | M, B, ev :: evs => by
    cases ev <;> simp only [RewriteCheck.replay, replay_noSS tabs t f _ _ evs]

/-- The validator does not read the table's forwardings (`fwdPre` does). -/
theorem validate_noLoads (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) :
    RewriteCheck.validate tabs { t with loads := #[] } f g log =
      RewriteCheck.validate tabs t f g log := by
  simp only [RewriteCheck.validate, replay_noLoads]

/-- The validator does not read the table's struct-store splits (`ssPre` does). -/
theorem validate_noSS (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) :
    RewriteCheck.validate tabs { t with structStores := #[] } f g log =
      RewriteCheck.validate tabs t f g log := by
  simp only [RewriteCheck.validate, replay_noSS]

theorem checkedRewrite_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ f₁, (f₁ = f ∨ RewriteCheck.nilOK penv out.tables f f₁ = true) ∧
        ∃ f₂, (f₂ = f₁ ∨ (RewriteCheck.fwdRel out.tables f₁ f₂ = true ∧
          checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
          ∃ f₃ log₃, (f₃ = f₂ ∨ (RewriteCheck.ssRel out.tables f₂ f₃ = true ∧
            checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
            RewriteCheck.validate out.tables t f₃ out.func log₃ = true) := by
  -- an accepted run with a table the validator reads alike
  have run : ∀ T : Interp.Table, (∀ tabs f g log, RewriteCheck.validate tabs T f g log =
      RewriteCheck.validate tabs t f g log) → ∀ o, checkedRun T penv f = .ok (some o) → o = out →
      (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ f₁, (f₁ = f ∨ RewriteCheck.nilOK penv out.tables f f₁ = true) ∧
        ∃ f₂, (f₂ = f₁ ∨ (RewriteCheck.fwdRel out.tables f₁ f₂ = true ∧
          checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
          ∃ f₃ log₃, (f₃ = f₂ ∨ (RewriteCheck.ssRel out.tables f₂ f₃ = true ∧
            checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
            RewriteCheck.validate out.tables t f₃ out.func log₃ = true) := by
    intro T hT o ho he
    subst he
    have := checkedRun_cases ho
    simp only [hT] at this
    exact .inr this
  have hv1 : ∀ tabs f g log, RewriteCheck.validate tabs { t with loads := #[] } f g log =
      RewriteCheck.validate tabs t f g log := fun tabs f g log => validate_noLoads tabs t f g log
  have hv2 : ∀ tabs f g log, RewriteCheck.validate tabs
      { { t with loads := #[] } with structStores := #[] } f g log =
      RewriteCheck.validate tabs t f g log := fun tabs f g log => by
    rw [validate_noSS, validate_noLoads]
  unfold checkedRewrite at h
  cases h1 : checkedRun t penv f with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r =>
    simp only [h1, bind, Except.bind] at h
    cases r with
    | some o =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact run t (fun _ _ _ _ => rfl) o h1 h
    | none =>
      dsimp only at h
      -- the third run, without forwardings and struct-store splits
      have tier3 : (if t.structStores.isEmpty = true then
            (pure { func := f, tables := penv.tables } : Except String PassOut) else
            (do
              match ← checkedRun { { t with loads := #[] } with structStores := #[] } penv f with
              | some out => pure out
              | none => pure { func := f, tables := penv.tables })) = .ok out →
          (out.func = f ∧ out.tables = penv.tables) ∨
          (tabsAgree penv.tables out.tables f = true ∧
            ∃ f₁, (f₁ = f ∨ RewriteCheck.nilOK penv out.tables f f₁ = true) ∧
            ∃ f₂, (f₂ = f₁ ∨ (RewriteCheck.fwdRel out.tables f₁ f₂ = true ∧
              checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
              ∃ f₃ log₃, (f₃ = f₂ ∨ (RewriteCheck.ssRel out.tables f₂ f₃ = true ∧
                checkOK { tabs := out.tables, typs := penv.typs } f₃ = true)) ∧
                RewriteCheck.validate out.tables t f₃ out.func log₃ = true) := by
        intro h3
        split at h3
        · simp only [pure, Except.pure, Except.ok.injEq] at h3
          subst h3; exact .inl ⟨rfl, rfl⟩
        cases h4 : checkedRun { { t with loads := #[] } with structStores := #[] } penv f with
        | error e => simp [h4, bind, Except.bind] at h3
        | ok r =>
          simp only [h4, bind, Except.bind] at h3
          cases r with
          | some o =>
            simp only [pure, Except.pure, Except.ok.injEq] at h3
            exact run _ hv2 o h4 h3
          | none =>
            simp only [pure, Except.pure, Except.ok.injEq] at h3
            subst h3; exact .inl ⟨rfl, rfl⟩
      generalize hm : (if t.loads.isEmpty = true then (pure none : Except String (Option PassOut))
        else checkedRun { t with loads := #[] } penv f) = m at h
      cases m with
      | error e => cases h
      | ok r =>
        cases r with
        | none => exact tier3 h
        | some o =>
          cases hL : t.loads.isEmpty with
          | true => rw [hL] at hm; cases hm
          | false =>
            rw [hL] at hm
            simp only [Bool.false_eq_true, ite_false] at hm
            simp only [pure, Except.pure, Except.ok.injEq] at h
            exact run _ hv1 o hm h

/-- A table without nil-check eliminations (`Interp.Table.nilChecks`) has no nil-check events. -/
theorem nilEvent?_none {t : Interp.Table} (h : t.nilChecks = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.nilEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.nilEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem nilPre_none {t : Interp.Table} (h : t.nilChecks = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.nilPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.nilStep t f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.nilStep, nilEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.nilPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without Load-of-Store forwardings (`Interp.Table.loads`) has no forwarding events. -/
theorem fwdEvent?_none {t : Interp.Table} (h : t.loads = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.fwdEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.fwdEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem fwdPre_none {t : Interp.Table} (h : t.loads = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.fwdPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.fwdStep t f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.fwdStep, fwdEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.fwdPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without struct-store splits (`Interp.Table.structStores`) has no split events. -/
theorem ssEvent?_none {t : Interp.Table} (h : t.structStores = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.ssEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.ssEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem ssPre_none {t : Interp.Table} (h : t.structStores = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.ssPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.ssStep t) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.ssStep, ssEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.ssPre
  rw [← Array.foldl_toList, key]
  simp

/-- `checkedRewrite_cases` for a table without nil-check eliminations, forwardings and
struct-store splits. -/
theorem checkedRewrite_cases_noNil {t : Interp.Table} (h0 : t.nilChecks = #[])
    (h1 : t.loads = #[]) (h2 : t.structStores = #[]) {penv : PassEnv}
    {f : Func} {out : PassOut} (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ log, RewriteCheck.validate out.tables t f out.func log = true) := by
  unfold checkedRewrite at h
  have hE : t.loads.isEmpty = true := by rw [h1]; rfl
  have hE2 : t.structStores.isEmpty = true := by rw [h2]; rfl
  cases h3 : checkedRun t penv f with
  | error e => simp [h3, bind, Except.bind] at h
  | ok r =>
    simp only [h3, bind, Except.bind] at h
    cases r with
    | none =>
      simp only [hE, hE2, ite_true, pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl⟩
    | some o =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold checkedRun at h3
      cases hr : rewriteRun t true true penv f with
      | error e => simp [hr, bind, Except.bind] at h3
      | ok r =>
        obtain ⟨o', n, log⟩ := r
        simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h3
        split at h3
        · next hv =>
          cases h3
          rw [RewriteCheck.accepts, Bool.and_eq_true, nilPre_none h0] at hv
          simp only [beq_self_eq_true, ite_true] at hv
          rw [RewriteCheck.fwdAccepts, fwdPre_none h1] at hv
          simp only [beq_self_eq_true, ite_true] at hv
          rw [RewriteCheck.ssAccepts, ssPre_none h2] at hv
          simp only [beq_self_eq_true, ite_true] at hv
          exact .inr ⟨hv.1, log, hv.2⟩
        · cases h3


theorem validate_parts {tabs : Tables} {t : Interp.Table} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs t f g log = true) :
    RewriteCheck.atomsOK f g = true ∧ RewriteCheck.closedOK f = true ∧
      RewriteCheck.closedOK g = true := by
  unfold RewriteCheck.validate at hv
  simp only [Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2⟩

end GoFV.Proof.Pass.Rewrite
