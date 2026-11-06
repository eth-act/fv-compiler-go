import GoFV.Proof.Witness.LowerCopyArgs

/-!
# Witness function for `lower` testing a truncation against zero: `nzw` (hand-written, issue #385)

`nzw(x, y int) int { if int32(x) != 0 { return y }; return x }` as `lower` sees it (entry block
`b1`: `v4 = Trunc64to32 <int32> v2` of the register argument `x`, `v5 = Const32 <int32> [0]`,
`v6 = Neq32 v4 v5`, `If v6` to `b2`, returning `y`, and `b3`, returning `x`). The checked lower
fires `(Trunc64to32 ...) => (Copy ...)` (196), the compare's lowering to `NotEqual (CMPW v4 v5)`,
the constant operand as `CMPWconst [0] v4`, `(If (NotEqual cc) yes no) => (NE cc yes no)` and
`(NE (CMPWconst [0] x) yes no) => (NZW x yes no)` (`ARM64.rules:601`); `lower` eliminates the
`Copy` inline, so `b1` becomes `NZW v2`, where the replay has `NZW v4`: the validator accepts the
control, the source of the narrowing `Copy` `v4`, whose low 32 bits `NZW` tests (`builtL`,
`GoFV.Proof.Low.Val.brVal_r32`). By `lower_refines` every returning or panicking `run` of `nzw`
is, up to refinement, a `runL` of the result; `nzw(2^32, 7)` returns `2^32` and `nzw(5, 7)`
returns 7 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- `nzw`, the input of `lower`. -/
def nzwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[6] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5, 6]),
    some (mkB 2 .Ret p0 #[7] #[] #[⟨1, 0⟩] #[7]),
    some (mkB 3 .Ret p0 #[8] #[] #[⟨1, 1⟩] #[8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .Trunc64to32 5 none p0 1 #[2] 1),
    some (mkVI 5 .Const32 5 0 none p0 1 #[] 1),
    some (mkV 6 .Neq32 3 none p0 1 #[4, 5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[3, 1] 2),
    some (mkV 8 .MakeResult 33 none p0 1 #[2, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `nzw`. -/
def nzwPassEnv : PassEnv :=
  { cpaPassEnv with funcName := GoStr.ofString "nzw" }

theorem nzw_generic : nzwFunc.lowered = false := by decide +kernel

/-- `nzw` has no fused multiply-add shape: its contraction is itself. -/
theorem nzw_noFma : GoFV.Opt.FmaContract.contractAll nzwFunc = nzwFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `b1` is `NZW v2`, and
`nzw(2^32, 7) = 2^32`, `nzw(5, 7) = 7` under `run` of the input and `runL` of the result. -/
theorem nzw_checks :
    (lowerChecked nzwPassEnv nzwFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.controls)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (2 ^ 32), .int .w64 7] {} 2) (2 ^ 32),
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 7] {} 2) 7)) =
      some (some (.ARM64NZW, #[2]), true, true, true) ∧
    returnsInt (run Env.p1 cpaTabs nzwFunc [.int .w64 (2 ^ 32), .int .w64 7] {} 2) (2 ^ 32) = true ∧
    returnsInt (run Env.p1 cpaTabs nzwFunc [.int .w64 5, .int .w64 7] {} 2) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a block rule whose
control is the source of a narrowing `Copy`: on `nzw`, the checked lower branches by `NZW` on `x`,
and every returning or panicking `run` of `nzw` is, up to refinement, a `runL` of the result. -/
theorem nzw_lower :
    ∃ out, lowerChecked nzwPassEnv nzwFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.controls)) = some (.ARM64NZW, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract nzwFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func nzwPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env cpaTabs nzwFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cpaTabs nzwFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nzw_checks
  cases hc : lowerChecked nzwPassEnv nzwFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, GoFV.Proof.Low.lower_refines hc nzw_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc nzw_generic nzw_noFma hE hd⟩

end GoFV.Proof.Witness
