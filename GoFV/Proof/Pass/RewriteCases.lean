import GoFV.Opt.RewriteCheck

/-!
# What a checked rewrite pass returns (issue #113)

`checkedRewrite t` keeps the input's tables and returns either its input or a result the
validator (`GoFV.Opt.RewriteCheck.validate`) accepted against the rewrite log; a validated result
has the atom, closure and replay facts the refinement proof consumes.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.Opt GoFV.Rules

theorem checkedRewrite_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRewrite t penv f = .ok out) :
    out.tables = penv.tables ∧
      (out.func = f ∨ ∃ log, RewriteCheck.validate penv.tables t f out.func log = true) := by
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
      exact ⟨rfl, .inr ⟨log, hv⟩⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨rfl, .inl rfl⟩

theorem validate_parts {tabs : Tables} {t : Interp.Table} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs t f g log = true) :
    RewriteCheck.atomsOK f g = true ∧ RewriteCheck.closedOK f = true ∧
      RewriteCheck.closedOK g = true := by
  unfold RewriteCheck.validate at hv
  simp only [Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2⟩

end GoFV.Proof.Pass.Rewrite
