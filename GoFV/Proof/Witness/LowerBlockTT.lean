import GoFV.Proof.Witness.LowerCondSel

/-!
# Witness function for `lower` on a bit test: `tbt` (hand-written, issue #385)

`tbt(x, y int) int { if x&4 != 0 { return y }; return x }` as `lower` sees it (entry block `b1`:
`v4 = Const64 [4]`, `v5 = And64 v2 v4` of the register argument `x`, `v6 = Const64 [0]`,
`v7 = Neq64 v5 v6`, `If v7` to `b2`, returning `y`, and `b3`, returning `x`). The checked lower
fires `(Neq64 x y) => (NotEqual (CMP x y))`, `(And64 x y) => (AND x y)`, `(AND x (MOVDconst [c]))
=> (ANDconst [c] x)`, `(CMP x (MOVDconst [c])) => (CMPconst [c] x)`, `(If (NotEqual cc) yes no)
=> (NE cc yes no)` (`462`), `(NE (CMPconst [0] x:(ANDconst [c] y)) yes no) && x.Uses == 1 => (NE
(TSTconst [c] y) yes no)` (`559`, a fresh `TSTconst [4] v2`) and `(NE (TSTconst [c] x) yes no) &&
oneBit(c) => (TBNZ [int64(ntz64(c))] x yes no)` (`622`): `b1` becomes `TBNZ [2] v2`, a test of
`x`'s bit 2. By `lower_refines` every returning or panicking `run` of `tbt` is, up to refinement,
a `runL` of the result; `tbt(5, 7)` returns 7 and `tbt(3, 7)` returns 3 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- `tbt`, the input of `lower`. -/
def tbtFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[7] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7]),
    some (mkB 2 .Ret p0 #[8] #[] #[⟨1, 0⟩] #[8]),
    some (mkB 3 .Ret p0 #[9] #[] #[⟨1, 1⟩] #[9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 4 none p0 1 #[] 1),
    some (mkV 5 .And64 2 none p0 1 #[2, 4] 1),
    some (mkVI 6 .Const64 2 0 none p0 1 #[] 1),
    some (mkV 7 .Neq64 3 none p0 1 #[5, 6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[3, 1] 2),
    some (mkV 9 .MakeResult 33 none p0 1 #[2, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `tbt` (`typ.Flags` is type 29). -/
def tbtPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "tbt" }

theorem tbt_generic : tbtFunc.lowered = false := by decide +kernel

/-- `tbt` has no fused multiply-add shape: its contraction is itself. -/
theorem tbt_noFma : GoFV.Opt.FmaContract.contractAll tbtFunc = tbtFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `b1` is `TBNZ [2] v2`,
and `tbt(5, 7) = 7`, `tbt(3, 7) = 3` under `run` of the input and `runL` of the result. -/
theorem tbt_checks :
    (lowerChecked tbtPassEnv tbtFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 7] {} 2) 7,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 7] {} 2) 3)) =
      some (some (.ARM64TBNZ, 2, #[2]), true, true, true) ∧
    returnsInt (run Env.p1 lcsTabs tbtFunc [.int .w64 5, .int .w64 7] {} 2) 7 = true ∧
    returnsInt (run Env.p1 lcsTabs tbtFunc [.int .w64 3, .int .w64 7] {} 2) 3 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a block rule that
builds a new control: on `tbt`, the checked lower replaces `CMPconst [0] (ANDconst [4] x)` by a
fresh `TSTconst [4] x` and branches by `TBNZ [2]` on `x`, and every returning or panicking `run`
of `tbt` is, up to refinement, a `runL` of the result. -/
theorem tbt_lower :
    ∃ out, lowerChecked tbtPassEnv tbtFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)) =
        some (.ARM64TBNZ, 2, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract tbtFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func tbtPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lcsTabs tbtFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcsTabs tbtFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := tbt_checks
  cases hc : lowerChecked tbtPassEnv tbtFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, GoFV.Proof.Low.lower_refines hc tbt_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc tbt_generic tbt_noFma hE hd⟩

end GoFV.Proof.Witness
