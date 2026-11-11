import GoFV.Proof.Witness.LowerNarrowArgs

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`'s narrow left shifts: `lsh` (hand-written, issue #385)

A function of the global `g` of `LowerNarrowArgs` (`narFunc`, `narMem`: `g` holds
`0x1_0000_019a`), with a 32-bit load `v4` of `g`:

* `lsh() int { return int(int32(g) << 3) }` with the shift unbounded: `v6 = Lsh32x64 <int32> v4
  (Const64 [3])`. `lower` renames `v6` to `Lsh64x64` (`ARM64.rules:148`, false on the narrow
  operand), then lowers it by `169` to `CSEL [LessThanU] (SLL v4 v5) (Const64 [0]) (CMPconst [64]
  v5)`, which later rules fold to `v6 = CSEL0 [LessThanU] v9 v11` with `v9 = SLLconst [3] v4` and
  `v11 = CMPconst [64] v5`. The validator replays the rename as no change and `169` in its form on
  `Lsh32x64` (`GoFV.Rules.Derive.lshSplit`, `GoFV.Opt.LowerCheck.lshRule`).

By `lower_refines` every returning or panicking `run` of it is, up to refinement, a `runL` of the
result; it returns `410 << 3 = 3280`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `lsh`. -/
def lshFunc : Func := narFunc 8 8 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 8 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 5 none p0 1 #[3, 1] 1),
  some (mkVI 5 .Const64 9 3 none p0 1 #[] 1),
  some (mkVI 6 .Lsh32x64 5 0 none p0 1 #[4, 5] 1),
  some (mkV 7 .SignExt32to64 2 none p0 1 #[6] 1),
  some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]

theorem lsh_generic : lshFunc.lowered = false := by decide +kernel

/-- `lsh` has no fused multiply-add shape: its contraction is itself. -/
theorem lsh_noFma : GoFV.Opt.FmaContract.contractAll lshFunc = lshFunc := by decide +kernel

/-- The values of `lsh`'s lowered result that lower the shift. -/
def lshShow (f : Func) : List (Option (Op × Int64 × Array ID)) :=
  [6, 9, 11].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.args)

/-- What `lshShow` gives on the checked lower's result: `CSEL0 [LessThanU]` (`4582`, its Go
opcode number) of `SLLconst [3] v4` and `CMPconst [64] v5`. -/
def lshOut : List (Option (Op × Int64 × Array ID)) :=
  [some (.ARM64CSEL0, 4582, #[9, 11]), some (.ARM64SLLconst, 3, #[4]),
    some (.ARM64CMPconst, 64, #[5])]

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `lsh` whose `v6`, `v9`, `v11`
are `CSEL0 [LessThanU] v9 v11`, `SLLconst [3] v4` and `CMPconst [64] v5`, and `lsh` returns 3280
under `run` of the input and `runL` of the result. -/
theorem lsh_checks :
    (lowerChecked (narPassEnv "lsh") lshFunc).toOption.map (fun o =>
      (lshShow o.func, o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 3280)) =
      some (lshOut, true, true) ∧
    returnsInt (run Env.p1 narTabs lshFunc [] narMem 1) 3280 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a narrow left shift:
on `lsh`, the checked lower renames `Lsh32x64` (`ARM64.rules:148`, `GoFV.Proof.Low.Rules.
r_ARM64_148_3_lsh_sound`) and lowers it by `169` in its form on the narrow shift, giving
`CSEL0 [LessThanU] (SLLconst [3] v4) (CMPconst [64] v5)`, and every returning or panicking `run`
of `lsh` is, up to refinement, a `runL` of the result. -/
theorem lsh_lower :
    ∃ out, lowerChecked (narPassEnv "lsh") lshFunc = .ok out ∧ out.func.lowered = true ∧
      lshShow out.func = lshOut ∧
      (∃ f', GoFV.Proof.Low.Contract lshFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "lsh").tables lshFunc) env mem)
        out.tables out.func (narPassEnv "lsh").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "lsh").tables lshFunc) env mem → ∀ fuel,
        (run env narTabs lshFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs lshFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lsh_checks
  cases hc : lowerChecked (narPassEnv "lsh") lshFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc lsh_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc lsh_generic lsh_noFma hE hro hd⟩

end GoFV.Proof.Witness
