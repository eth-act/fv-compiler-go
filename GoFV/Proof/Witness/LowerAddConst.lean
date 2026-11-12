import GoFV.Proof.Witness.LowerAdd

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`: `addc` (hand-written, issue #385)

`addc(x, y int) int { return x + 5 }` as `lower` sees it (one block: `v3 = Const64 <int> [5]`,
`v4 = Add64 v2 v3` of the register argument `v2`, returned by `v5 = MakeResult v4 v1`). The
checked lower fires `(Const64 [val]) => (MOVDconst [int64(val)])` (`ARM64.rules:182`),
`(Add64 ...) => (ADD ...)` (5) and `(ADD x (MOVDconst <t> [c])) && !t.IsPtr() => (ADDconst [c] x)`
(970): `v4` becomes `ADDconst [5] v2`. `addc(3, 4)` returns 8 under `run` of the input and `runL`
of the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `addc`, the input of `lower`: `add` with `y` replaced by the constant 5. -/
def lacFunc : Func :=
  { laFunc with
    valueTab := laFunc.valueTab.set! 3 (some (mkVI 3 .Const64 2 5 none p0 1 #[] 1)) }

/-- The pass environment of `lower` on `addc`. -/
def lacPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "addc" }

theorem lac_generic : lacFunc.lowered = false := by decide +kernel

/-- `addc` has no fused multiply-add shape: its contraction is itself. -/
theorem lac_noFma : GoFV.Opt.FmaContract.contractAll lacFunc = lacFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `ADDconst [5] v2`,
and `addc(3, 4) = 8` under `run` of the input and `runL` of the result. -/
theorem lac_checks :
    (lowerChecked lacPassEnv lacFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 1) 8)) =
      some (some (.ARM64ADDconst, 5, #[2]), true, true) ∧
    returnsInt (run Env.p1 laTabs lacFunc [.int .w64 3, .int .w64 4] {} 1) 8 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an `ADD` of a constant
taking it as an immediate (`ARM64.rules:970`): on `addc`, the checked lower makes `v4`
`ADDconst [5] v2`, and every returning or panicking `run` of `addc` is, up to refinement, a `runL`
of the result. -/
theorem lac_lower :
    ∃ out, lowerChecked lacPassEnv lacFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64ADDconst, 5, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract lacFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre lacPassEnv.tables lacFunc) env mem)
        out.tables out.func lacPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre lacPassEnv.tables lacFunc) env mem → ∀ fuel,
        (run env laTabs lacFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs lacFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lac_checks
  cases hc : lowerChecked lacPassEnv lacFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc lac_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc lac_generic lac_noFma hE hro hd⟩

end GoFV.Proof.Witness
