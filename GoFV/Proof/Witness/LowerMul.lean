import GoFV.Proof.Witness.LowerAdd
import GoFV.Proof.Low.ValMul

/-!
# Witness for a strength-reduced multiplication in `lower`: `mul10` (hand-written, issue #385)

`mul10(x, y int) int { return x * 10 }` in lowered form, as the checked lower's replay holds it
when `(MUL x (MOVDconst [c])) && canMulStrengthReduce(config, c) => {mulStrengthReduce(v, x, c)}`
(`ARM64.rules:1043`) fires at `v4 = MUL v2 v3` (`v3 = MOVDconst [10]`, `v2` the register
argument `x`): Go's recipe for 10 builds `v6 = ADDshiftLL [2] v2 v2` (`5x`) and `v7 = SLLconst
[1] v6` (`10x`), and `v4` becomes `Copy v7`, the event `Interp.mulDefs` logs. The validator accepts
the event (`mulOKL`, by kernel evaluation), so `mul_step` applies to it: every lowered denotation
after it refines the one before. (The whole `lowerChecked` run is not evaluated here: Go's
`Config.mulRecipes` table, `GoFV.Rules.Arm64.mulRecipes`, takes 195,075 hash-map insertions.)
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof GoFV.Opt.LowerCheck

/-- The replayed definitions at the event: `mul10` lowered up to its `MUL`. -/
def mulM : GoFV.Opt.RewriteCheck.Defs := #[none,
  some (mkV 1 .InitMem 28 none p0 1 #[] 1),
  some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
  some (mkVI 3 .ARM64MOVDconst 2 10 none p0 1 #[] 1),
  some (mkV 4 .ARM64MUL 2 none p0 1 #[2, 3] 1),
  some (mkV 5 .MakeResult 33 none p0 1 #[4, 1] 1)]

/-- The definitions the event logs: `v4` as `Copy v7`, then `v7` and its arguments' definitions
(`Interp.mulDefs`: `v6`). -/
def mulDefs : List Value :=
  [mkV 4 .Copy 2 none p0 1 #[7] 1,
   mkVI 7 .ARM64SLLconst 2 1 none p0 1 #[6] 1,
   mkVI 6 .ARM64ADDshiftLL 2 2 none p0 1 #[2, 2] 1]

/-- By kernel evaluation: the validator accepts the event, and `v7` is 10 times `v2`. -/
theorem mul10_ok : mulOKL laTabs mulM 4 mulDefs = some mulDefs ∧
    mulCoef (mulDefs.drop 1) 2 2 7 = some 10 := by
  decide +kernel

/-- **Validator witness** for `mul_step` (`ARM64.rules:1043`): on `mul10`, the strength-reduced
`MUL` by 10 passes `mulOKL`, so on every set closed under arguments every lowered denotation after
the event refines the one before. -/
theorem mul10_step : ∃ ds, mulOKL laTabs mulM 4 mulDefs = some ds ∧
    ∀ (C : ID → Prop), GoFV.Proof.Pass.Rewrite.DefClosed mulM C → ∀ ρ,
      GoFV.Proof.Low.TypedL true mulM.get? laTabs ρ → ∀ n y, C y →
        Sem.Refines (GoFV.Proof.Low.denL true mulM.get? laTabs ρ n y)
          (GoFV.Proof.Low.denL true (GoFV.Proof.Pass.Rewrite.putAll mulM ds).get? laTabs ρ
            (n * ds.length) y) :=
  ⟨mulDefs, mul10_ok.1, fun _ hC _ hT => GoFV.Proof.Low.Val.mul_step mul10_ok.1 hC hT⟩

end GoFV.Proof.Witness
