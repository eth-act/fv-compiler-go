import GoFV.Proof.Low.Sim
import GoFV.Proof.Low.Val
import GoFV.Proof.Low.ProvenARM64
import GoFV.Proof.Low.TabsAgreeL
import GoFV.Proof.Low.Contract
import GoFV.Proof.RefineL
import GoFV.Proof.Checked
import GoFV.Opt.LowerChecked

/-!
# The checked `lower` refines its input (issue #385)

`checkedLowerWith_refines`: for a rule set whose rules all have their lowered obligation
(`ArmRuleSet.AllSound`), the checked lowering pass (`GoFV.Opt.LowerCheck.checkedLowerWith`:
`applyRewrite` with the set's table and its log, kept only if the input and output pass `check`,
the tables agree for the input, `tabsAgreeL`, and `validateL` accepts the log) refines an input
whose atoms are generic: every returning or panicking `runL` of the input is, up to refinement, a
`runL` of the output, under monotone contracts. A rejected result is the input; an accepted one is
related by the validator (`validateL_termRef`: atoms' arguments and terminators refine as terms in
lowered mode) and the atom simulation over `runL` (`atomSimL_refines`), and the input runs alike in
both tables (`runL_tabsAgreeL`).

`lower_refines`: the instance for `GoFV.Opt.lowerChecked` (the checked lower with the proven
`ARM64.rules`, `GoFV.Rules.ProvenARM64.lower`, `arm64_allSound`, on the input with its `useFMA`
shapes contracted): the output refines a contraction of the generic input (`Contract`, decision
on #384: the twelve fused multiply-add shapes, `docs/plans/semantics2.md` §2.1).
`lower_refines_run`: without fused multiply-add shapes the contraction is the input, and the
output refines Phase 1's `run` of it. Adding rule lemmas grows the set; the theorems stay as
stated.
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LowerCheck GoFV.Rules GoFV.Proof

/-- What `checkedRunL` accepted. -/
theorem checkedRunL_some {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRunL t penv f = .ok (some out)) :
    ∃ log, tabsAgreeL penv.tables out.tables f = true ∧
      checkOK { tabs := penv.tables, typs := penv.typs } f = true ∧
      checkOK { tabs := out.tables, typs := penv.typs } out.func = true ∧
      validateL out.tables t f out.func log = true := by
  unfold checkedRunL at h
  cases hr : rewriteRun t true true penv f with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true] at hc
      exact ⟨log, hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩
    · cases h

/-- The checked lowering pass keeps the input or a result `checkedRunL` accepted. -/
theorem checkedLowerWith_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedLowerWith t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨ checkedRunL t penv f = .ok (some out) := by
  unfold checkedLowerWith at h
  cases hr : checkedRunL t penv f with
  | error e => rw [hr] at h; cases h
  | ok o =>
    rw [hr] at h
    cases o with
    | none => cases h; exact .inl ⟨rfl, rfl⟩
    | some o => cases h; exact .inr rfl

/-- **The checked lowering pass refines its input**, for a rule set whose rules have their
lowered obligation and an input whose atoms are generic. -/
theorem checkedLowerWith_refines {s : RuleSet} (hs : ArmRuleSet.AllSound s) {penv : PassEnv}
    {f : Func} {out : PassOut} (h : checkedLowerWith (Interp.Table.ofRuleSet s) penv f = .ok out)
    (hfa : ∀ tabs x u, f.value? x = some u → termVL tabs u = false → u.op.generic = true) :
    RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func penv.tables f := by
  rcases checkedLowerWith_cases h with ⟨he, ht⟩ | hc
  · rw [he, ht]; exact RefinesLFrom.refl _ _ _
  obtain ⟨log, hta, hcf, hcg, hv⟩ := checkedRunL_some hc
  obtain ⟨hgl, hsh, hA, hclf, hclg⟩ := validateL_parts hv
  obtain ⟨h1, h2⟩ := validateL_termRef hs hv
  have R := atomSimL_refines (checkOK_sound hcf) (checkOK_sound hcg) hA hclf hclg hsh hgl
    (hfa out.tables) h1 h2
  intro env args mem hP fuel hd
  rw [← runL_tabsAgreeL hta] at hd ⊢
  exact R env args mem hP fuel hd

/-- **`lower` refines its input up to contraction**: the checked lower with the proven
`ARM64.rules` (`GoFV.Opt.lowerChecked`) on a generic function refines its contraction at the
`useFMA` shapes (`Contract`). -/
theorem lower_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : lowerChecked penv f = .ok out) (hf : f.lowered = false) :
    ∃ f', Contract f f' ∧
      RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func penv.tables f' :=
  ⟨_, ⟨_, rfl⟩, checkedLowerWith_refines arm64_allSound h
    fun tabs _ _ hx ht => contractAt_atoms hf _ tabs hx ht⟩

/-- `lower_refines` without fused multiply-add shapes (the contraction is the input), with
Phase 1's `run` of the input: every returning or panicking run of the generic input is, up to
refinement, a `runL` of the output. -/
theorem lower_refines_run {penv : PassEnv} {f : Func} {out : PassOut}
    (h : lowerChecked penv f = .ok out) (hf : f.lowered = false)
    (hc : FmaContract.contractAll f = f) {env : Env} (hE : env.Mono)
    {args : List Val} {mem : Mem} {fuel : Nat} (hd : (run env penv.tables f args mem fuel).Defined) :
    ∃ fuel', OutcomeRefines 0 (run env penv.tables f args mem fuel)
      (runL env out.tables out.func args mem fuel') := by
  have R := checkedLowerWith_refines arm64_allSound h
    fun tabs _ _ hx ht => contractAt_atoms hf _ tabs hx ht
  rw [hc] at R
  rw [← runL_generic env penv.tables hf] at hd ⊢
  exact R env args mem hE fuel hd

end GoFV.Proof.Low
