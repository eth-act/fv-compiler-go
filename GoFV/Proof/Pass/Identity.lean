import GoFV.Proof.Refine
import GoFV.Opt.CheckBCE
import GoFV.Opt.SoftFloat

/-!
# `check bce` and `softfloat` refine their input

Both return their input unchanged in the configurations they accept (`checkbce_eq`,
`softfloat_off`; `softfloat` with `Config.SoftFloat` set is an error, so it has no output to
refine). No well-formedness hypothesis is needed.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

/-- **`check bce` refines its input.** -/
theorem checkbce_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkbcePass penv f = .ok out) : Refines out.tables out.func penv.tables f := by
  simp only [checkbcePass, Pass.ofFunc, checkbce_eq, pure, Except.pure, bind, Except.bind] at h
  cases h
  exact Refines.refl _ _

/-- **`softfloat` refines its input.** -/
theorem softfloat_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : softfloatPass penv f = .ok out) : Refines out.tables out.func penv.tables f := by
  simp only [softfloatPass, Pass.ofFunc, softfloat, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · next v hv =>
    cases h
    split at hv
    · cases hv
    · next b _ =>
      split at hv
      · cases hv
      · cases hv
        exact Refines.refl _ _

end GoFV.Proof
