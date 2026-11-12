import GoFV.Proof.Witness.LowerNarrowArgs

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`'s shift-pair masks: `msk` (hand-written, issue #385)

A function of the global `g` of `LowerNarrowArgs` (`narFunc`, `narMem`: `g` holds
`0x1_0000_019a`):

* `msk() int { u := uint64(g); return int((u << 40 >> 40) * (u >> 5 << 5)) }`: `lower` gives
  `v7 = ANDconst [16777215] v4` (`(SRLconst [40] (SLLconst [40] v4))`, `ARM64.rules:1617`, the
  mask `1<<24 - 1`) and `v10 = ANDconst [-32] v4` (`(SLLconst [5] (SRLconst [5] v4))`, `1618`, the
  mask `^(1<<5 - 1)`), multiplied by `v11 = MUL v7 v10` (a `MUL` absorbs no shift, so the shift
  pairs stay for the mask rules).

By `lower_refines` every returning or panicking `run` of it is, up to refinement, a `runL` of the
result; it returns `410 * 4294967680 = 1760936748800`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `msk`. -/
def mskFunc : Func := narFunc 12 12 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 2 #[3, 1] 1),
  some (mkVI 5 .Const64 9 40 none p0 2 #[] 1),
  some (mkVI 6 .Lsh64x64 2 1 none p0 1 #[4, 5] 1),
  some (mkVI 7 .Rsh64Ux64 2 1 none p0 1 #[6, 5] 1),
  some (mkVI 8 .Const64 9 5 none p0 2 #[] 1),
  some (mkVI 9 .Rsh64Ux64 2 1 none p0 1 #[4, 8] 1),
  some (mkVI 10 .Lsh64x64 2 1 none p0 1 #[9, 8] 1),
  some (mkV 11 .Mul64 2 none p0 1 #[7, 10] 1),
  some (mkV 12 .MakeResult 33 none p0 1 #[11, 1] 1)]

theorem msk_generic : mskFunc.lowered = false := by decide +kernel

/-- `msk` has no fused multiply-add shape: its contraction is itself. -/
theorem msk_noFma : GoFV.Opt.FmaContract.contractAll mskFunc = mskFunc := by decide +kernel

/-- The values of `msk`'s lowered result that the mask rules give, and their product. -/
def mskShow (f : Func) : List (Option (Op × Int64 × Array ID)) :=
  [7, 10, 11].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.args)

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `msk` whose `v7`, `v10`, `v11`
are `ANDconst [16777215] v4`, `ANDconst [-32] v4` and `MUL v7 v10`, and `msk` returns
1760936748800 under `run` of the input and `runL` of the result. -/
theorem msk_checks :
    (lowerChecked (narPassEnv "msk") mskFunc).toOption.map (fun o =>
      (mskShow o.func, o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 1760936748800)) =
      some ([some (.ARM64ANDconst, 16777215, #[4]), some (.ARM64ANDconst, -32, #[4]),
        some (.ARM64MUL, 0, #[7, 10])], true, true) ∧
    returnsInt (run Env.p1 narTabs mskFunc [] narMem 1) 1760936748800 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on the shift-pair masks:
on `msk`, the checked lower's `v7` and `v10` are `ANDconst [16777215] v4` (`ARM64.rules:1617`,
`GoFV.Proof.Low.Rules.r_ARM64_1617_sound`) and `ANDconst [-32] v4` (`1618`,
`GoFV.Proof.Low.Rules.r_ARM64_1618_sound`), and every returning or panicking `run` of `msk` is, up
to refinement, a `runL` of the result. -/
theorem msk_lower :
    ∃ out, lowerChecked (narPassEnv "msk") mskFunc = .ok out ∧ out.func.lowered = true ∧
      mskShow out.func = [some (.ARM64ANDconst, 16777215, #[4]), some (.ARM64ANDconst, -32, #[4]),
        some (.ARM64MUL, 0, #[7, 10])] ∧
      (∃ f', GoFV.Proof.Low.Contract mskFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.LowerCheck.roPre (narPassEnv "msk").tables mskFunc) env mem)
        out.tables out.func (narPassEnv "msk").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre (narPassEnv "msk").tables mskFunc) env mem → ∀ fuel,
        (run env narTabs mskFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs mskFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := msk_checks
  cases hc : lowerChecked (narPassEnv "msk") mskFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc msk_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc msk_generic msk_noFma hE hro hd⟩

end GoFV.Proof.Witness
