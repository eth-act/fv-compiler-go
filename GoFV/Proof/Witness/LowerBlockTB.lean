import GoFV.Proof.Witness.LowerCondSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a sign test: `tbn` (hand-written, issue #385)

`tbn(x, y int) int { if x < 0 { return y }; return x }` as `lower` sees it (entry block `b1`:
`v4 = Const64 [0]`, `v5 = Less64 v2 v4` of the register argument `x`, `If v5` to `b2`, returning
`y`, and `b3`, returning `x`). The checked lower fires `(Less64 x y) => (LessThan (CMP x y))`
(`ARM64.rules:256`, a fresh `v8 = CMP v2 v4`), `(Const64 [val]) => (MOVDconst [int64(val)])`,
`(CMP x (MOVDconst [c])) => (CMPconst [c] x)`, `(If (LessThan cc) yes no) => (LT cc yes no)`
(`463`) and `(LT (CMPconst [0] x) yes no) => (TBNZ [63] x yes no)` (`647`): `b1` becomes `TBNZ
[63] v2`, a test of `x`'s sign bit. By `lower_refines` every returning or panicking `run` of `tbn`
is, up to refinement, a `runL` of the result; `tbn(-3, 7)` returns 7 and `tbn(5, 7)` returns 5
under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- `tbn`, the input of `lower`. -/
def tbnFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[5] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5]),
    some (mkB 2 .Ret p0 #[6] #[] #[⟨1, 0⟩] #[6]),
    some (mkB 3 .Ret p0 #[7] #[] #[⟨1, 1⟩] #[7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 0 none p0 1 #[] 1),
    some (mkV 5 .Less64 3 none p0 1 #[2, 4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[3, 1] 2),
    some (mkV 7 .MakeResult 33 none p0 1 #[2, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `tbn` (`typ.Flags` is type 29). -/
def tbnPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "tbn" }

theorem tbn_generic : tbnFunc.lowered = false := by decide +kernel

/-- `tbn` has no fused multiply-add shape: its contraction is itself. -/
theorem tbn_noFma : GoFV.Opt.FmaContract.contractAll tbnFunc = tbnFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `b1` is `TBNZ [63] v2`,
and `tbn(-3, 7) = 7`, `tbn(5, 7) = 5` under `run` of the input and `runL` of the result. -/
theorem tbn_checks :
    (lowerChecked tbnPassEnv tbnFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (-3), .int .w64 7] {} 2) 7,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 7] {} 2) 5)) =
      some (some (.ARM64TBNZ, 63, #[2]), true, true, true) ∧
    returnsInt (run Env.p1 lcsTabs tbnFunc [.int .w64 (-3), .int .w64 7] {} 2) 7 = true ∧
    returnsInt (run Env.p1 lcsTabs tbnFunc [.int .w64 5, .int .w64 7] {} 2) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a block rule with a
variable control: on `tbn`, the checked lower branches by `TBNZ [63]` on `x`, and every
returning or panicking `run` of `tbn` is, up to refinement, a `runL` of the result. -/
theorem tbn_lower :
    ∃ out, lowerChecked tbnPassEnv tbnFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)) =
        some (.ARM64TBNZ, 63, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract tbnFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms tbnPassEnv.tables tbnFunc) env mem)
        out.tables out.func tbnPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms tbnPassEnv.tables tbnFunc) env mem → ∀ fuel,
        (run env lcsTabs tbnFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcsTabs tbnFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := tbn_checks
  cases hc : lowerChecked tbnPassEnv tbnFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, GoFV.Proof.Low.lower_refines hc tbn_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc tbn_generic tbn_noFma hE hro hd⟩

end GoFV.Proof.Witness
