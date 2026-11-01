import GoFV.Proof.ProveCheck.Sim
import GoFV.Proof.AtomSim

/-!
# The checked prove refines its input (issue #24)

`proveChecked_refines`: the proven-only checked pass (`GoFV.Opt.proveChecked`) refines its input
under monotone contracts. If the relation `proveRel` rejects the reverted output, the result is
the input; otherwise it is the atom simulation under prove's source invariant (`proveInv`:
path facts and `Phi` range invariants), whose premises are `prove_atomArgs` and `prove_steps`.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.AtomSim

/-- `checkedResult` returns its input or an output `proveRel` accepts. -/
theorem checkedResult_cases (tabs : Tables) (f g : Func) :
    (ProveCheck.checkedResult tabs f g).1 = f ∨
      ∃ F inv RB, ProveCheck.proveRel tabs f (ProveCheck.checkedResult tabs f g).1 F inv RB = true := by
  unfold ProveCheck.checkedResult
  split
  · exact .inl rfl
  · generalize ProveCheck.asmOf f tabs = A
    rcases A with ⟨C, F, inv, RB⟩
    dsimp only
    generalize ProveCheck.revert tabs true F inv RB f g = R
    rcases R with ⟨h, st⟩
    dsimp only
    split
    · rename_i hrel; exact .inr ⟨F, inv, RB, hrel⟩
    · exact .inl rfl

/-- **The checked prove refines its input.** -/
theorem proveChecked_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : proveChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold proveChecked ProveCheck.proveCheckedStats at h
  cases hp : Prove.Prover.ofEnv penv with
  | error e => simp [hp, bind, Except.bind] at h
  | ok p =>
    cases hq : Prove.prove p f with
    | error e => simp [hp, hq, bind, Except.bind] at h
    | ok g0 =>
      simp only [hp, hq, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only at hg ⊢
      rcases checkedResult_cases penv.tables f g0 with he | ⟨F, inv, RB, hrel⟩
      · rw [he]; exact RefinesUnder.refl _ _ _
      · have hwf := check_wf hf
        have hc := Dom.certOK_of_check (check_domCert hf)
        have hR := proveRel_spec hrel
        exact atomSimInv_refines hf hg hR.atoms (proveInv hwf hc hR) (prove_atomArgs hwf hc hR)
          (prove_steps hwf hc hR)

end GoFV.Proof.ProveCheck
