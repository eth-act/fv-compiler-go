import GoFV.Proof.Pass.RewriteCases
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim
import GoFV.Proof.TabsAgree
import GoFV.Proof.Rules.Proven
import GoFV.Opt.Opt

/-!
# The checked rewrite passes refine their input (issue #113)

`checkedRewrite_refines`: for a rule set all of whose value rules are sound (`RuleSet.AllSound`,
one `Rule.Sound` lemma per rule), the checked rewrite pass (`GoFV.Opt.checkedRewrite`: the
rewrite pass with its log, kept only if `RewriteCheck.validate` accepts it) refines its input
under monotone contracts (`Env.Mono`), in the pass's extended tables. A rejected result is the
input (`RefinesUnder.refl`); an accepted one relates the atoms' arguments and the controls as
terms in the extended tables (`validate_termRef`), which the atom simulation lifts to the function
(`AtomSim.atomSim_refines`), and the input runs alike in both tables (`tabsAgree`,
`refinesUnder_of_tabsAgree`).

The instances depend on the proven-rule sets explicitly: `opt_refines` (also `middle opt` and
`late opt`, the same pass under another name) is about `optChecked`, the pass with the rules of
`Proven.generic` (`scripts/rule-proofs.py proven`: the generic rules with a merged lemma) and its
proof is `generic_allSound`; likewise `divisible_refines`/`divmod_refines`. Adding lemmas grows
these sets (and what the checked passes optimise); the theorems stay as stated.

`Term.RetypeShapes` (register typing at integer shapes, issue #108) is `Term.retypeShapes`.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof GoFV.Proof.Rules

theorem checkedRewrite_refines {s : RuleSet} (hs : s.AllSound)
    {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : checkedRewrite (Interp.Table.ofRuleSet s) penv f = .ok out)
    (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  rcases checkedRewrite_cases h with ⟨he, ht⟩ | ⟨hta, log, hv⟩
  · rw [he, ht]; exact RefinesUnder.refl _ _ _
  · obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
    obtain ⟨h1, h2⟩ := validate_termRef hv hs Term.retypeShapes
    exact refinesUnder_of_tabsAgree hta (AtomSim.atomSim_refines hf hg hA hcf hcg h1 h2)

/-- `opt`, `middle opt` and `late opt` with the proven generic rules, validated. -/
theorem opt_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : optChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f :=
  checkedRewrite_refines generic_allSound h hf hg

/-- `divisible` with its proven rules, validated. -/
theorem divisible_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divisibleChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f :=
  checkedRewrite_refines divisible_allSound h hf hg

/-- `divmod` with its proven rules, validated. -/
theorem divmod_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divmodChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f :=
  checkedRewrite_refines divmod_allSound h hf hg

end GoFV.Proof.Pass.Rewrite
