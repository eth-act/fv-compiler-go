import GoFV.Proof.Pass.RewriteCases
import GoFV.Proof.Pass.RewriteTerm
import GoFV.Proof.AtomSim
import GoFV.Proof.TabsAgree
import GoFV.Proof.Pass.NilSim
import GoFV.Proof.Pass.LoadFwd
import GoFV.Proof.Pass.StructStoreSim
import GoFV.Proof.Checked
import GoFV.Proof.Rules.Proven
import GoFV.Opt.Opt

/-!
# The checked rewrite passes refine their input (issue #113)

`checkedRewrite_refines`: for a rule set all of whose value rules are sound (`RuleSet.AllSound`,
one `Rule.Sound` lemma per rule), the checked rewrite pass (`GoFV.Opt.checkedRewrite`: the
rewrite pass with its log, kept only if `RewriteCheck.validate` accepts it) refines its input
`f` under `RwPre penv.tables f` (monotone contracts, `Env.Mono`; malloc-family contracts that
return non-nil pointers and non-nil dictionary arguments, `NilPre`, for the nil-check
eliminations of issue #151), in the pass's extended tables. A rejected result is the input
(`RefinesUnder.refl`); an accepted one relates the atoms' arguments and the controls as terms in
the extended tables (`validate_termRef`), which the atom simulation lifts to the function
(`AtomSim.atomSim_refines`), and the input runs alike in both tables (`tabsAgree`,
`refinesFrom_of_tabsAgree`). The log's nil-check eliminations, Load-of-Store forwardings and
struct-store splits (issue #151) are applied to the input first, each by its own refinement
(`Nil.refinesFrom_of_rel`, `LoadFwd.fwd_refines`, `StructStore.ss_refines`).

The instances depend on the proven-rule sets explicitly: `opt_refines` (also `middle opt` and
`late opt`, the same pass under another name) is about `optChecked`, the pass with the rules of
`Proven.generic` (`scripts/rule-proofs.py proven`: the generic rules with a merged lemma) and its
proof is `generic_allSound`; likewise `divisible_refines`/`divmod_refines`. Adding lemmas grows
these sets (and what the checked passes optimise); the theorems stay as stated.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof GoFV.Proof.Rules

/-- **The validator alone** (issue #17): a rewrite of `f` into `g` that `RewriteCheck.validate`
accepts in the tables `tabs'` with a sound rule table, both checked, refines in `tabs'`; with
`tabsAgree tabs tabs' f` the source may run in its own tables `tabs`. For a rewrite step whose
log has no nil-check eliminations or Load forwardings (the dec rules: decompose builtin, run with
`removeDead := false`), `RewriteCheck.accepts` is `tabsAgree` and `validate`. -/
theorem validate_refines {s : RuleSet} (hs : s.AllSound) {tabs tabs' : Tables} {f g : Func}
    {log : Array RwEvent} {ce ce' : CheckEnv}
    (hv : RewriteCheck.validate tabs' (Interp.Table.ofRuleSet s) f g log = true)
    (hta : tabsAgree tabs tabs' f = true)
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) :
    RefinesUnder Env.Mono tabs' g tabs f := by
  obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
  obtain ⟨h1, h2⟩ := validate_termRef hv hs
  exact refinesUnder_of_tabsAgree hta (AtomSim.atomSim_refines hf hg hA hcf hcg h1 h2)

/-- The precondition of the checked rewrite passes on `f` in the tables `tabs`: monotone
contracts, malloc-family contracts that return non-nil pointers, non-nil dictionary arguments
(`NilPre`: the nil-check eliminations `generic.rules:1367`/`:1372`/`:1384`, issue #151). It
depends on `f` only through its dictionary parameters (`Opt.NilCheck.dictParams`). -/
def RwPre (tabs : Tables) (f : Func) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  env.Mono ∧ NilPre tabs f env args mem

/-- `RwPre` holds on `Env.p1` (no malloc-family contract) for a function without dictionary
parameters. -/
theorem RwPre.p1 {tabs : Tables} {f : Func} (h : NilCheck.dictParams tabs f = [])
    (args : List Val) (mem : Mem) : RwPre tabs f Env.p1 args mem :=
  ⟨Env.p1_mono, Env.p1_allocNonNil, by rw [h]; exact DictArgs.nil args⟩

theorem RefinesUnder.toRw {tabs₀ tabs tabs' : Tables} {f₀ f f' : Func}
    (h : RefinesUnder Env.Mono tabs' f' tabs f) : RefinesFrom (RwPre tabs₀ f₀) tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.1) h.from

theorem checkedRewrite_refines {s : RuleSet} (hs : s.AllSound)
    {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : checkedRewrite (Interp.Table.ofRuleSet s) penv f = .ok out)
    (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables f) out.tables out.func penv.tables f := by
  rcases checkedRewrite_cases h with ⟨he, ht⟩ | ⟨hta, f₁, hn, f₂, hfw, f₃, log₃, hss, hv⟩
  · rw [he, ht]; exact RefinesUnder.toRw (RefinesUnder.refl _ _ _)
  obtain ⟨hA, hcf, hcg⟩ := validate_parts hv
  obtain ⟨h1, h2⟩ := validate_termRef hv hs
  -- nil-check eliminations first (nilcheckelim's relation with the rewrite passes' seeds)
  obtain ⟨ce₁, hf₁, hN⟩ : ∃ ce₁, check ce₁ f₁ = .ok () ∧
      RefinesFrom (RwPre penv.tables f) out.tables f₁ out.tables f := by
    rcases hn with rfl | hn
    · exact ⟨ce, hf, RefinesUnder.toRw (RefinesUnder.refl _ _ _)⟩
    simp only [RewriteCheck.nilOK, Bool.and_eq_true, beq_iff_eq] at hn
    obtain ⟨⟨hr, hck⟩, hd⟩ := hn
    refine ⟨_, checkOK_sound hck, RefinesFrom.mono (fun env args mem hp => ?_)
      (Nil.refinesFrom_of_rel ⟨ce, check_wf hf⟩ (Dom.certOK_of_check (check_domCert hf))
        (Nil.nrel_sound hr))⟩
    unfold NilPre
    rw [hd]
    exact hp.2
  -- then the Load-of-Store forwardings
  obtain ⟨ce₂, hf₂, hF⟩ : ∃ ce₂, check ce₂ f₂ = .ok () ∧
      RefinesUnder Env.Mono out.tables f₂ out.tables f₁ := by
    rcases hfw with rfl | ⟨hrel, hck⟩
    · exact ⟨ce₁, hf₁, RefinesUnder.refl _ _ _⟩
    have hf₂ := checkOK_sound hck
    exact ⟨_, hf₂, LoadFwd.fwd_refines hf₁ hf₂ hrel⟩
  -- then the struct-store splits
  obtain ⟨ce₃, hf₃, hS⟩ : ∃ ce₃, check ce₃ f₃ = .ok () ∧
      RefinesUnder Env.Mono out.tables f₃ out.tables f₂ := by
    rcases hss with rfl | ⟨hrel, hck⟩
    · exact ⟨ce₂, hf₂, RefinesUnder.refl _ _ _⟩
    have hf₃ := checkOK_sound hck
    exact ⟨_, hf₃, StructStore.ss_refines hf₂ hf₃ hrel⟩
  -- then the validated rewrite
  exact refinesFrom_of_tabsAgree hta
    (hN.trans (RefinesUnder.toRw
      (hF.trans (hS.trans (AtomSim.atomSim_refines hf₃ hg hA hcf hcg h1 h2)))))

/-- `opt`, `middle opt` and `late opt` with the proven generic rules, validated. -/
theorem opt_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : optChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables f) out.tables out.func penv.tables f :=
  checkedRewrite_refines generic_allSound h hf hg

/-- `divisible` with its proven rules, validated. -/
theorem divisible_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divisibleChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables f) out.tables out.func penv.tables f :=
  checkedRewrite_refines divisible_allSound h hf hg

/-- `divmod` with its proven rules, validated. -/
theorem divmod_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : divmodChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesFrom (RwPre penv.tables f) out.tables out.func penv.tables f :=
  checkedRewrite_refines divmod_allSound h hf hg

end GoFV.Proof.Pass.Rewrite
