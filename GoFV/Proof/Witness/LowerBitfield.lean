import GoFV.Proof.Witness.LowerNarrowArgs

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower`'s bit-field peepholes and byte swaps: `bfx`, `bfm`, `bsw` (hand-written, issue #385)

Three functions of the global `g` of `LowerNarrowArgs` (`narFunc`, `narMem`: `g` holds
`0x1_0000_019a`):

* `bfx() int { return int(uint64(uint32(g)) >> 3) }`: `v5 = Trunc64to32 <uint32> v4`, `v6 =
  ZeroExt32to64 <uint64> v5`, `v8 = Rsh64Ux64 <uint64> v6 (Const64 [3])`; `lower` folds
  `(SRLconst [3] (MOVWUreg v4))` into `v10 = UBFX [armBFAuxInt(3, 29)] v4` (`ARM64.rules:1703`;
  the bounds check of the shift, `CSEL0` of `CMPconst [64] (MOVDconst [3])`, stays).
* `bfm() int { return int(g & 0xff) }`: `v6 = And64 v4 (Const64 [255])`; `lower` folds
  `(ANDconst [255] v4)` into `MOVBUreg v4` (`ARM64.rules:1855`).
* `bsw() int { return int(bits.ReverseBytes16(h)) }` with `h` the low halfword of `g` (`v4 = Load
  <uint16>`): `v5 = Bswap16 <uint16> v4`, `v6 = ZeroExt16to64 <int> v5`; `lower` gives `v5 =
  REV16W v4` (`ARM64.rules:110`).

By `lower_refines` every returning or panicking `run` of each is, up to refinement, a `runL` of the
result; they return 51, 154 and 39425.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `bfx`. -/
def bfxFunc : Func := narFunc 9 9 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
  some (mkV 5 .Trunc64to32 10 none p0 1 #[4] 1),
  some (mkV 6 .ZeroExt32to64 9 none p0 1 #[5] 1),
  some (mkVI 7 .Const64 9 3 none p0 1 #[] 1),
  some (mkV 8 .Rsh64Ux64 9 none p0 1 #[6, 7] 1),
  some (mkV 9 .MakeResult 33 none p0 1 #[8, 1] 1)]

/-- `bfm`. -/
def bfmFunc : Func := narFunc 7 7 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
  some (mkVI 5 .Const64 2 255 none p0 1 #[] 1),
  some (mkV 6 .And64 2 none p0 1 #[4, 5] 1),
  some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]

/-- `bsw`. -/
def bswFunc : Func := narFunc 7 7 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 8 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 11 none p0 1 #[3, 1] 1),
  some (mkV 5 .Bswap16 11 none p0 1 #[4] 1),
  some (mkV 6 .ZeroExt16to64 2 none p0 1 #[5] 1),
  some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]

theorem bfx_generic : bfxFunc.lowered = false := by decide +kernel
theorem bfm_generic : bfmFunc.lowered = false := by decide +kernel
theorem bsw_generic : bswFunc.lowered = false := by decide +kernel

/-- The three functions have no fused multiply-add shape: their contraction is themselves. -/
theorem bfx_noFma : GoFV.Opt.FmaContract.contractAll bfxFunc = bfxFunc := by decide +kernel
theorem bfm_noFma : GoFV.Opt.FmaContract.contractAll bfmFunc = bfmFunc := by decide +kernel
theorem bsw_noFma : GoFV.Opt.FmaContract.contractAll bswFunc = bswFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `bfx` whose `v10` is `UBFX [797] v4` (`797 = 29 | 3<<8`), and
`bfx` returns 51 under `run` of the input and `runL` of the result. -/
theorem bfx_checks :
    (lowerChecked (narPassEnv "bfx") bfxFunc).toOption.map (fun o =>
      ((o.func.value? 10).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 51)) =
      some (some (.ARM64UBFX, 797, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs bfxFunc [] narMem 1) 51 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `bfm` whose `v6` is `MOVBUreg v4`, and
`bfm` returns 154 under `run` of the input and `runL` of the result. -/
theorem bfm_checks :
    (lowerChecked (narPassEnv "bfm") bfmFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 154)) =
      some (some (.ARM64MOVBUreg, 0, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs bfmFunc [] narMem 1) 154 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `bsw` whose `v5` is `REV16W v4`, and
`bsw` returns 39425 under `run` of the input and `runL` of the result. -/
theorem bsw_checks :
    (lowerChecked (narPassEnv "bsw") bswFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 39425)) =
      some (some (.ARM64REV16W, 0, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs bswFunc [] narMem 1) 39425 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a bit-field extract: on `bfx`, the checked lower's `v10` is `UBFX [armBFAuxInt(3, 29)] v4`
(`ARM64.rules:1703`, `GoFV.Proof.Low.Rules.r_ARM64_1703_sound`), and every returning or panicking `run` of `bfx` is, up to
refinement, a `runL` of the result. -/
theorem bfx_lower :
    ∃ out, lowerChecked (narPassEnv "bfx") bfxFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 10).map (fun v => (v.op, v.auxInt, v.args)) = some (.ARM64UBFX, 797, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract bfxFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.LowerCheck.roPre (narPassEnv "bfx").tables bfxFunc) env mem)
        out.tables out.func (narPassEnv "bfx").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre (narPassEnv "bfx").tables bfxFunc) env mem → ∀ fuel,
        (run env narTabs bfxFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs bfxFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := bfx_checks
  cases hc : lowerChecked (narPassEnv "bfx") bfxFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc bfx_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc bfx_generic bfx_noFma hE hro hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a byte mask: on `bfm`, the checked lower's `v6` is `MOVBUreg v4` (`ARM64.rules:1855`,
`GoFV.Proof.Low.Rules.r_ARM64_1855_sound`), and every returning or panicking `run` of `bfm` is, up to
refinement, a `runL` of the result. -/
theorem bfm_lower :
    ∃ out, lowerChecked (narPassEnv "bfm") bfmFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) = some (.ARM64MOVBUreg, 0, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract bfmFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.LowerCheck.roPre (narPassEnv "bfm").tables bfmFunc) env mem)
        out.tables out.func (narPassEnv "bfm").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre (narPassEnv "bfm").tables bfmFunc) env mem → ∀ fuel,
        (run env narTabs bfmFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs bfmFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := bfm_checks
  cases hc : lowerChecked (narPassEnv "bfm") bfmFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc bfm_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc bfm_generic bfm_noFma hE hro hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a halfword byte swap: on `bsw`, the checked lower's `v5` is `REV16W v4` (`ARM64.rules:110`,
`GoFV.Proof.Low.Rules.r_ARM64_110_sound`), and every returning or panicking `run` of `bsw` is, up to
refinement, a `runL` of the result. -/
theorem bsw_lower :
    ∃ out, lowerChecked (narPassEnv "bsw") bswFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) = some (.ARM64REV16W, 0, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract bswFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.LowerCheck.roPre (narPassEnv "bsw").tables bswFunc) env mem)
        out.tables out.func (narPassEnv "bsw").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre (narPassEnv "bsw").tables bswFunc) env mem → ∀ fuel,
        (run env narTabs bswFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs bswFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := bsw_checks
  cases hc : lowerChecked (narPassEnv "bsw") bswFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc bsw_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc bsw_generic bsw_noFma hE hro hd⟩

end GoFV.Proof.Witness
