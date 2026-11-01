import GoFV.Proof.Pass.MemCombineStore
import GoFV.Proof.TabsAgree

/-!
# memcombine refines its input (issue #35)

`memcombine_refines`: the validated pass (`GoFV.Opt.memcombineChecked`: memcombine, accepted by
`MemCombine.Check.mcOK` in the result's tables, which the input cannot tell from its own,
`tabsAgree`) refines its input under monotone contracts. A rejected or unchanged result is the
input; an accepted one is the generalised atom simulation (`AtomSim.atomSimX_refines`) with the
trivial source invariant: its atoms are `f`'s but combined stores (`atomsXOK_spec`); an
unchanged atom's arguments and the controls are refined as terms (`mc_ref`), and a combined store
writes a memory refining the source's chain of stores (`store_chgRef`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim GoFV.Proof.Pass.Rewrite

section
variable {tabs : Tables} {f g : Func} {R : Array Bool} {ce ce' : CheckEnv}
  (hwf : WF ce f) (hwg : WF ce' g) (K : McFacts tabs f g R)
include hwf hwg K

/-- **Atoms' arguments**: an unchanged atom's are refined as terms, a combined store writes a
refined memory. -/
theorem mc_atomArgs : AtomArgsRefX (SrcInv.triv tabs f) g := by
  intro b hb gb hgb a ha u hu ht
  have hbf : b ∈ f.blocks := K.blocks_eq ▸ hb
  obtain ⟨fb, gb', hfb, hgb', BA⟩ := (atomsXOK_spec K.atoms).block b hbf
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨haf, u', hu', hop, hty, hai, -, hsz, -, -⟩ := BA.sub a ha u hu ht
  have hlg := listed_of_wf hwg hb hgb ha hu
  have hlf := listed_of_wf hwf hbf hfb haf hu'
  have hv := K.val a (GoFV.Proof.CheckFacts.lt_of_value? hu)
  unfold valOK at hv
  rw [hlg, hlf] at hv
  simp only [ht, Bool.false_eq_true, ite_false, Bool.or_eq_true] at hv
  rcases hv with hv | hv
  · have hT := mc_atomArgs_same hwf hwg K hb hgb hfb ha haf hu hu' ht hv
    exact .inl ⟨u', hu', hop, hty, hai, (sameVal_spec hv).2.2.2.1, hsz, fun i hi =>
      ⟨fun _ => TermRef.toP (hT i hi) _ _ _, fun _ _ _ _ _ _ _ => TermRef.toP (hT i hi) _ _ _⟩⟩
  · obtain ⟨h1, h2⟩ := storeOK_op hv
    exact .inr ⟨u', hu', h1.trans h2.symm, .inl h2, store_chgRef hwf hwg K hu' hv⟩

end

/-- An accepted result refines its input. -/
theorem mc_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (hf : check ce f = .ok ())
    (hg : check ce' g = .ok ()) (h : mcOK tabs f g = true) :
    RefinesUnder Env.Mono tabs g tabs f := by
  have K := mcOK_spec h
  have hwf := check_wf hf
  have hwg := check_wf hg
  exact atomSimX_refines hf hg (atomsXOK_spec K.atoms) (SrcInv.triv tabs f)
    (mc_atomArgs hwf hwg K)
    (TermStepRef.toStepRefsP (ControlsRef.toTermStepRef (mc_controls hwf hwg K)
      fun b hb fb gb hfb hgb => by
        obtain ⟨gb', hgb', hk, hs, hid, -⟩ :=
          KnownBits.blocksOK_facts K.blocks (K.blocks_eq ▸ hb) hfb
        rw [hgb] at hgb'; cases hgb'
        exact ⟨hk.symm, hs.symm, hid.symm⟩) _)

/-- **memcombine (validated) refines its input.** -/
theorem memcombine_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : memcombineChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold memcombineChecked at h
  cases hc : memcombineCfg penv with
  | error e => simp [hc, bind, Except.bind] at h
  | ok cu =>
    obtain ⟨c, u⟩ := cu
    cases hm : memcombine c u penv.tables f with
    | error e => simp [hc, hm, bind, Except.bind] at h
    | ok gt =>
      obtain ⟨g, t⟩ := gt
      simp only [hc, hm, bind, Except.bind] at h
      split at h
      · rename_i hok
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Bool.and_eq_true] at hok
        exact refinesUnder_of_tabsAgree hok.1.2 (mc_refines hf hg hok.2)
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact RefinesUnder.refl _ _ _

end GoFV.Proof.MemCombine
