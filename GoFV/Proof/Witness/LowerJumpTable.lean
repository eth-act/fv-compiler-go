import GoFV.Proof.Witness.LowerBlockTB

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a jump table: `jtb` (hand-written, issue #385)

`jtb(x, y int) int { switch x { case 0: return 10; case 1: return 20 } }` with the bounds check
already gone, as `lower` sees it (entry block `b1`: `JumpTable v2` on the register argument `x`, to
`b2`, returning 10, and `b3`, returning 20). The checked lower fires `(JumpTable idx) =>
(JUMPTABLE {makeJumpTableSym(b)} idx (MOVDaddr <typ.Uintptr> {makeJumpTableSym(b)} (SB)))`
(`ARM64.rules:478`): `b1` becomes `JUMPTABLE v2 v7` with the table's address `v7 = MOVDaddr
{main.add.jump1} v8` (the function's symbol is `smin`'s tables' `main.add`) on a fresh `v8 = SB`,
which the validator checks by its effect
(`GoFV.Opt.LowerCheck.jumpOKL`). By `lower_refines` every returning or panicking `run` of `jtb` is,
up to refinement, a `runL` of the result; `jtb(0, 7)` returns 10 and `jtb(1, 7)` returns 20 under
both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- The tables of `smin` with `uintptr` (type 4, `typ.Uintptr` of the table's address). -/
def jtbTabs : Tables :=
  { lcsTabs with types := lcsTabs.types.set! 4 (some (mkT .UINTPTR (some 8) "uintptr")) }

/-- `jtb`, the input of `lower`. -/
def jtbFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .JumpTable p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2]),
    some (mkB 2 .Ret p0 #[4] #[] #[⟨1, 0⟩] #[3, 4]),
    some (mkB 3 .Ret p0 #[6] #[] #[⟨1, 1⟩] #[5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .Const64 2 10 none p0 1 #[] 2),
    some (mkV 4 .MakeResult 33 none p0 1 #[3, 1] 2),
    some (mkVI 5 .Const64 2 20 none p0 1 #[] 3),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `jtb`. -/
def jtbPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "jtb", tables := jtbTabs,
                    typs := lcsPassEnv.typs.push ("Uintptr", 4) }

theorem jtb_generic : jtbFunc.lowered = false := by decide +kernel

/-- `jtb` has no fused multiply-add shape: its contraction is itself. -/
theorem jtb_noFma : GoFV.Opt.FmaContract.contractAll jtbFunc = jtbFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `b1` is `JUMPTABLE v2
v7`, and `jtb(0, 7) = 10`, `jtb(1, 7) = 20` under `run` of the input and `runL` of the result. -/
theorem jtb_checks :
    (lowerChecked jtbPassEnv jtbFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.controls)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 0, .int .w64 7] {} 2) 10,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 1, .int .w64 7] {} 2) 20)) =
      some (some (.ARM64JUMPTABLE, #[2, 7]), true, true, true) ∧
    returnsInt (run Env.p1 jtbTabs jtbFunc [.int .w64 0, .int .w64 7] {} 2) 10 = true ∧
    returnsInt (run Env.p1 jtbTabs jtbFunc [.int .w64 1, .int .w64 7] {} 2) 20 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a jump table: on
`jtb`, the checked lower branches by `JUMPTABLE` on `x`, and every returning or panicking `run`
of `jtb` is, up to refinement, a `runL` of the result. -/
theorem jtb_lower :
    ∃ out, lowerChecked jtbPassEnv jtbFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.controls)) = some (.ARM64JUMPTABLE, #[2, 7]) ∧
      (∃ f', GoFV.Proof.Low.Contract jtbFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre jtbPassEnv.tables jtbFunc) env mem)
        out.tables out.func jtbPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre jtbPassEnv.tables jtbFunc) env mem → ∀ fuel,
        (run env jtbTabs jtbFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env jtbTabs jtbFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := jtb_checks
  cases hc : lowerChecked jtbPassEnv jtbFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, GoFV.Proof.Low.lower_refines hc jtb_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc jtb_generic jtb_noFma hE hro hd⟩

end GoFV.Proof.Witness
