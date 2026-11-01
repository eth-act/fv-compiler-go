import GoFV.Opt.RewriteCheck

/-!
# What a checked rewrite pass returns (issue #113)

`checkedRewrite t` returns either its input with the input's tables, or a result the validator
(`GoFV.Opt.RewriteCheck.validate`) accepted in the result's tables, which the input cannot tell
from its own (`GoFV.Opt.tabsAgree`), against the rewrite log and a function `f₂` obtained from the
input by the log's nil-check eliminations (`RewriteCheck.nilOK`) and then its Load-of-Store
forwardings (`RewriteCheck.fwdRel`, both issue #151), each step optional; a validated result has
the atom, closure and replay facts the refinement proof consumes.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.Opt GoFV.Rules

theorem fwdAccepts_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    {log : Array RwEvent} (h : RewriteCheck.fwdAccepts penv t f out log = true) :
    ∃ f₂ log₂, (f₂ = f ∨ (RewriteCheck.fwdRel out.tables f f₂ = true ∧
      checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
      RewriteCheck.validate out.tables t f₂ out.func log₂ = true := by
  unfold RewriteCheck.fwdAccepts at h
  split at h
  next f' log' _ =>
  split at h
  · exact ⟨f, log, .inl rfl, h⟩
  · simp only [Bool.and_eq_true] at h
    exact ⟨f', log', .inr ⟨h.1.1, h.1.2⟩, h.2⟩

theorem checkedRewrite_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ f₁, (f₁ = f ∨ RewriteCheck.nilOK penv out.tables f f₁ = true) ∧
        ∃ f₂ log, (f₂ = f₁ ∨ (RewriteCheck.fwdRel out.tables f₁ f₂ = true ∧
          checkOK { tabs := out.tables, typs := penv.typs } f₂ = true)) ∧
          RewriteCheck.validate out.tables t f₂ out.func log = true) := by
  unfold checkedRewrite at h
  cases hr : rewriteRun t true true penv f with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    simp only [hr, bind, Except.bind] at h
    split at h
    · next hv =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [RewriteCheck.accepts, Bool.and_eq_true] at hv
      obtain ⟨hta, hv⟩ := hv
      refine .inr ⟨hta, ?_⟩
      split at hv
      next f' log' _ =>
      split at hv
      · exact ⟨f, .inl rfl, fwdAccepts_cases hv⟩
      · rw [Bool.and_eq_true] at hv
        exact ⟨f', .inr hv.1, fwdAccepts_cases hv.2⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl⟩

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

/-- `checkedRewrite_cases` for a table without nil-check eliminations and forwardings. -/
theorem checkedRewrite_cases_noNil {t : Interp.Table} (h0 : t.nilChecks = #[])
    (h1 : t.loads = #[]) {penv : PassEnv}
    {f : Func} {out : PassOut} (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ log, RewriteCheck.validate out.tables t f out.func log = true) := by
  unfold checkedRewrite at h
  cases hr : rewriteRun t true true penv f with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    simp only [hr, bind, Except.bind] at h
    split at h
    · next hv =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [RewriteCheck.accepts, Bool.and_eq_true, nilPre_none h0] at hv
      simp only [beq_self_eq_true, ite_true] at hv
      rw [RewriteCheck.fwdAccepts, fwdPre_none h1] at hv
      simp only [beq_self_eq_true, ite_true] at hv
      exact .inr ⟨hv.1, log, hv.2⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl⟩


theorem validate_parts {tabs : Tables} {t : Interp.Table} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs t f g log = true) :
    RewriteCheck.atomsOK f g = true ∧ RewriteCheck.closedOK f = true ∧
      RewriteCheck.closedOK g = true := by
  unfold RewriteCheck.validate at hv
  simp only [Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2⟩

end GoFV.Proof.Pass.Rewrite
