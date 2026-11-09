import GoFV.Opt.DeadStoreCheck
import GoFV.Proof.Witness.InitF10

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness for dse: the certificates of `f10` (kernel evaluation)

dse's result on `f10` is `f10Out` (`v8 = Zero …` became `Copy v7`), its checker `DSE.drel`
accepts it, and input and output pass `check`. The run and the witness: `GoFV.Proof.Witness.DSE`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- dse's result: `v8` is `Copy v7`, `v5` has one use less. -/
def f10Out : Func :=
  { f10 with
    valueTab := (f10Values.set! 5 (some (mkVa 5 .LocalAddr 37 0 (some 4) p0 2 #[2, 1]))).set! 8
      (some (mkVa 8 .Copy 31 0 none (pos 2 55 6 1) 1 #[7])) }

/-! ## Leaf certificates (kernel evaluation) -/

theorem f10_dse : (dse f10Tabs 31 f10).toOption = some f10Out := by decide +kernel

theorem f10_checks :
    (check f10CheckEnv f10).toBool = true ∧ (check f10CheckEnv f10Out).toBool = true ∧
      DSE.drel f10Tabs f10 f10Out = true := by
  decide +kernel

/-- The eliminated store. -/
theorem f10_elim :
    (f10.value? 8).map (·.op) = some .Zero ∧ (f10Out.value? 8).map (·.op) = some .Copy := by
  decide +kernel

end GoFV.Proof.Witness
