import GoFV.Proof.Witness.LowerNarrowArgs

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower`'s constant folds, masked shifts, shifted `MVN` and bit tests: `pkf`, `tbx` (hand-written, issue #385)

Two functions of the global `g` of `LowerNarrowArgs` (`narFunc`, `narMem`: `g` holds
`0x1_0000_019a`):

* `pkf() int { return (g + 3 - 5) + ^(g >> 3) + g << (g & 63) + int(int16(h) & 127) }` with `h`
  the low halfword of `g` (`v18 = Load <uint16>`): `lower` gives `v8 = SUBconst [2] v4` (`(SUB
  (ADDconst [3] v4) (MOVDconst [5]))` as `SUBconst [5]`, `ARM64.rules:971`, folded with the
  `ADDconst` into `ADDconst [-2]`, `1216`, then `SUBconst [2]`, `1000`), `v11 = MVNshiftRL [3] v4`
  (`1430`), `v14 = SLL v4 v4` (the `ANDconst [63]` amount dropped, `986`) and `v21 = ANDconst [127]
  v18` (the `MOVHreg` of the `ANDconst` dropped, `1398`).
* `tbx() int { if !(g < 0) { return 1 }; return 0 }`: `lower` branches by `TBNZ [0] (XORconst [1]
  (LessThan …))` and turns it into `TBZ [0] (LessThan …)` (`556`).

By `lower_refines` every returning or panicking `run` of each is, up to refinement, a `runL` of the
result; they return 288230407424442750 and 1.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `pkf`. -/
def pkfFunc : Func := narFunc 23 23 #[none,
  some (mkV 1 .InitMem 28 none p0 3 #[] 1),
  some (mkV 2 .SB 4 none p0 2 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 4 #[3, 1] 1),
  some (mkVI 5 .Const64 2 3 none p0 1 #[] 1),
  some (mkV 6 .Add64 2 none p0 1 #[4, 5] 1),
  some (mkVI 7 .Const64 2 5 none p0 1 #[] 1),
  some (mkV 8 .Sub64 2 none p0 1 #[6, 7] 1),
  some (mkVI 9 .Const64 9 3 none p0 1 #[] 1),
  some (mkVI 10 .Rsh64Ux64 2 1 none p0 1 #[4, 9] 1),
  some (mkV 11 .Com64 2 none p0 1 #[10] 1),
  some (mkVI 12 .Const64 2 63 none p0 1 #[] 1),
  some (mkV 13 .And64 2 none p0 1 #[4, 12] 1),
  some (mkVI 14 .Lsh64x64 2 1 none p0 1 #[4, 13] 1),
  some (mkV 15 .Add64 2 none p0 1 #[8, 11] 1),
  some (mkV 16 .Add64 2 none p0 1 #[15, 14] 1),
  some (mkV 17 .Addr 8 (some 4) p0 1 #[2] 1),
  some (mkV 18 .Load 11 none p0 1 #[17, 1] 1),
  some (mkVI 19 .Const16 11 127 none p0 1 #[] 1),
  some (mkV 20 .And16 11 none p0 1 #[18, 19] 1),
  some (mkV 21 .SignExt16to64 2 none p0 1 #[20] 1),
  some (mkV 22 .Add64 2 none p0 1 #[16, 21] 1),
  some (mkV 23 .MakeResult 33 none p0 1 #[22, 1] 1)]

/-- `tbx`. -/
def tbxFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[7] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7]),
    some (mkB 2 .Ret p0 #[9] #[] #[⟨1, 0⟩] #[8, 9]),
    some (mkB 3 .Ret p0 #[11] #[] #[⟨1, 1⟩] #[10, 11])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 3 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkVI 5 .Const64 2 0 none p0 1 #[] 1),
    some (mkV 6 .Less64 7 none p0 1 #[4, 5] 1),
    some (mkV 7 .Not 7 none p0 1 #[6] 1),
    some (mkVI 8 .Const64 2 1 none p0 1 #[] 2),
    some (mkV 9 .MakeResult 33 none p0 1 #[8, 1] 2),
    some (mkVI 10 .Const64 2 0 none p0 1 #[] 3),
    some (mkV 11 .MakeResult 33 none p0 1 #[10, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

theorem pkf_generic : pkfFunc.lowered = false := by decide +kernel
theorem tbx_generic : tbxFunc.lowered = false := by decide +kernel

/-- The two functions have no fused multiply-add shape: their contraction is themselves. -/
theorem pkf_noFma : GoFV.Opt.FmaContract.contractAll pkfFunc = pkfFunc := by decide +kernel
theorem tbx_noFma : GoFV.Opt.FmaContract.contractAll tbxFunc = tbxFunc := by decide +kernel

/-- The values of `pkf`'s lowered result that the peepholes give. -/
def pkfShow (f : Func) : List (Option (Op × Int64 × Array ID)) :=
  [8, 11, 14, 21].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.args)

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `pkf` whose `v8`, `v11`,
`v14`, `v21` are `SUBconst [2] v4`, `MVNshiftRL [3] v4`, `SLL v4 v4` and `ANDconst [127] v18`, and
`pkf` returns 288230407424442750 under `run` of the input and `runL` of the result. -/
theorem pkf_checks :
    (lowerChecked (narPassEnv "pkf") pkfFunc).toOption.map (fun o =>
      (pkfShow o.func, o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 288230407424442750)) =
      some ([some (.ARM64SUBconst, 2, #[4]), some (.ARM64MVNshiftRL, 3, #[4]),
        some (.ARM64SLL, 0, #[4, 4]), some (.ARM64ANDconst, 127, #[18])], true, true) ∧
    returnsInt (run Env.p1 narTabs pkfFunc [] narMem 1) 288230407424442750 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `tbx` whose `b1` is `TBZ [0]
v6`, and `tbx` returns 1 under `run` of the input and `runL` of the result. -/
theorem tbx_checks :
    (lowerChecked (narPassEnv "tbx") tbxFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 2) 1)) =
      some (some (.ARM64TBZ, 0, #[6]), true, true) ∧
    returnsInt (run Env.p1 narTabs tbxFunc [] narMem 2) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on the constant folds,
the masked shift amount, the shifted `MVN` and the sign extension of a mask: on `pkf`, the checked
lower's `v8`, `v11`, `v14`, `v21` are `SUBconst [2] v4` (`ARM64.rules:971`, `1216`,
`GoFV.Proof.Low.Rules.r_ARM64_971_sound`, `GoFV.Proof.Low.Rules.r_ARM64_1216_sound`),
`MVNshiftRL [3] v4` (`1430`, `GoFV.Proof.Low.Rules.r_ARM64_1430_sound`), `SLL v4 v4` (`986`,
`GoFV.Proof.Low.Rules.r_ARM64_986_sound`) and `ANDconst [127] v18` (`1398`,
`GoFV.Proof.Low.Rules.r_ARM64_1398_sound`), and every returning or panicking `run` of `pkf` is, up
to refinement, a `runL` of the result. -/
theorem pkf_lower :
    ∃ out, lowerChecked (narPassEnv "pkf") pkfFunc = .ok out ∧ out.func.lowered = true ∧
      pkfShow out.func = [some (.ARM64SUBconst, 2, #[4]), some (.ARM64MVNshiftRL, 3, #[4]),
        some (.ARM64SLL, 0, #[4, 4]), some (.ARM64ANDconst, 127, #[18])] ∧
      (∃ f', GoFV.Proof.Low.Contract pkfFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "pkf").tables pkfFunc) env mem)
        out.tables out.func (narPassEnv "pkf").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "pkf").tables pkfFunc) env mem → ∀ fuel,
        (run env narTabs pkfFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs pkfFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := pkf_checks
  cases hc : lowerChecked (narPassEnv "pkf") pkfFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc pkf_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc pkf_generic pkf_noFma hE hro hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a bit test of a
negated condition: on `tbx`, the checked lower's `b1` is `TBZ [0] v6` (`ARM64.rules:556`,
`GoFV.Proof.Low.Rules.r_ARM64_556_sound`), and every returning or panicking `run` of `tbx` is, up
to refinement, a `runL` of the result. -/
theorem tbx_lower :
    ∃ out, lowerChecked (narPassEnv "tbx") tbxFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)) =
        some (.ARM64TBZ, 0, #[6]) ∧
      (∃ f', GoFV.Proof.Low.Contract tbxFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage
            (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "tbx").tables tbxFunc) env mem)
        out.tables out.func (narPassEnv "tbx").tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms (narPassEnv "tbx").tables tbxFunc) env mem → ∀ fuel,
        (run env narTabs tbxFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs tbxFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := tbx_checks
  cases hc : lowerChecked (narPassEnv "tbx") tbxFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, GoFV.Proof.Low.lower_refines hc tbx_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc tbx_generic tbx_noFma hE hro hd⟩

end GoFV.Proof.Witness
