import GoFV.Proof.Pass.NilLateLSim
import GoFV.Opt.NilCheckLate

/-!
# `late nilcheck` refines under `runSched`

`nilcheckelim2_refinesSched`: the `late nilcheck` pass (`GoFV.Opt.nilcheckelim2Pass`, #408)
refines its input under `runSched` (L1 → L1) whenever the validator `nilLateB`
(`GoFV.Opt.NilLateCheck`) accepts the input and output: `g` is `f` with some `LoweredNilCheck`s
removed, each followed in its block by a value that faults on the same pointer with the same
memory, through values that cannot be `stuck` and panic only like the check
(`refinesSched_of_nlRel`, `GoFV.Proof.Pass.NilLateLSim`).
-/

namespace GoFV.Proof.NilLateL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof GoFV.Opt GoFV.Opt.NilLate

/-- **`late nilcheck` refines under `runSched`** where `nilLateB` accepts. -/
theorem nilcheckelim2_refinesSched {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : nilcheckelim2Pass penv f = .ok out) (hf : check ce f = .ok ())
    (hv : nilLateB penv.tables f out.func = true) :
    RefinesSched out.tables out.func penv.tables f := by
  have ht : out.tables = penv.tables := by
    unfold nilcheckelim2Pass Pass.ofFunc at h
    cases hp : nilcheckelim2 penv f with
    | error e => rw [hp] at h; cases h
    | ok g => rw [hp] at h; cases h; rfl
  rw [ht]
  exact refinesSched_of_nlRel (nlRel_of hv) (check_wf hf) (Dom.certOK_of_check (check_domCert hf))

end GoFV.Proof.NilLateL
