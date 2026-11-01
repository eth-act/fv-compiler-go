import GoFV.Proof.Pass.KnownBitsTerm

/-!
# known bits refines its input (issue #26)

`knownBits_refines`: the validated pass (`GoFV.Opt.knownBitsPass`) refines its input under
monotone contracts. A rejected or unchanged result is the input; an accepted one (`kbOK`) is the
atom simulation under known bits' source invariant (`kbInv`: registers have the bits their final
entries claim), whose premises are `kb_atomArgs` and `kb_controls`.
-/

namespace GoFV.Proof.KnownBits

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.AtomSim

/-- **known bits refines its input.** -/
theorem knownBits_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : knownBitsPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold knownBitsPass Pass.ofFunc knownBitsChecked at h
  cases hk : knownBitsWith penv.tables penv.typeOrder f with
  | error e => simp [hk, bind, Except.bind] at h
  | ok r =>
    obtain ⟨g, E, R⟩ := r
    simp only [hk, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only at hg ⊢
    split
    · rename_i hok
      simp only [hok, ↓reduceIte] at hg
      simp only [Bool.and_eq_true] at hok
      have K := kbOK_spec hok.2
      have hwf := check_wf hf
      exact atomSimInv_refines hf hg K.atoms (kbInv hwf K) (kb_atomArgs hwf K) (kb_controls hwf K)
    · exact RefinesUnder.refl _ _ _

end GoFV.Proof.KnownBits
