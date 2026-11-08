import GoFV.Proof.Witness.LowerAdd

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a `BitLen64`: `blen` (hand-written, issue #385)

`blen(x, y int) int { return bits.Len64(uint64(x)) }` as `lower` sees it (one block: `v4 =
BitLen64 <int> v2` of the first register argument, returned by `v5 = MakeResult v4 v1`). The
checked lower fires `(BitLen64 x) => (SUB (MOVDconst [64]) (CLZ <typ.Int> x))` (`ARM64.rules:104`,
`GoFV.Proof.Low.Rules.r_ARM64_104_sound`): `v4` becomes `ARM64SUB` of a fresh `MOVDconst [64]` and
a fresh `CLZ v2`. By `lower_refines` every returning or panicking `run` of `blen` is, up to
refinement, a `runL` of the result; `blen(5, 0)` returns 3 and `blen(0, 0)` returns 0 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The definition tables of `blen`: `add`'s and `uint64` (type 3). -/
def lblTabs : Tables :=
  { laTabs with types := laTabs.types.set! 3 (some (mkT .UINT64 (some 8) "uint64")) }

/-- `blen`, the input of `lower`. -/
def lblFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 0 #[] 1),
    some (mkV 4 .BitLen64 2 none p0 1 #[2] 1),
    some (mkV 5 .MakeResult 33 none p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `blen` (`typ.UInt64` is type 3). -/
def lblPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "blen", tables := lblTabs,
                   typs := #[("Int", 2), ("UInt64", 3), ("Mem", 28), ("Void", 31)] }

theorem lbl_generic : lblFunc.lowered = false := by decide +kernel

/-- `blen` has no fused multiply-add shape: its contraction is itself. -/
theorem lbl_noFma : GoFV.Opt.FmaContract.contractAll lblFunc = lblFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `ARM64SUB`, and
`blen(5, 0) = 3`, `blen(0, 0) = 0` under `run` of the input and `runL` of the result. -/
theorem lbl_checks :
    (lowerChecked lblPassEnv lblFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (·.op), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 0] {} 1) 3,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 0, .int .w64 0] {} 1) 0)) =
      some (some .ARM64SUB, true, true, true) ∧
    returnsInt (run Env.p1 lblTabs lblFunc [.int .w64 5, .int .w64 0] {} 1) 3 = true ∧
    returnsInt (run Env.p1 lblTabs lblFunc [.int .w64 0, .int .w64 0] {} 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `BitLen64`: on
`blen`, the checked lower computes the bit length as `64 − CLZ` (`ARM64SUB`), and every returning
or panicking `run` of `blen` is, up to refinement, a `runL` of the result. -/
theorem lbl_lower :
    ∃ out, lowerChecked lblPassEnv lblFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (·.op) = some .ARM64SUB ∧
      (∃ f', GoFV.Proof.Low.Contract lblFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func lblPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lblTabs lblFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lblTabs lblFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lbl_checks
  cases hc : lowerChecked lblPassEnv lblFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc lbl_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc lbl_generic lbl_noFma hE hd⟩

end GoFV.Proof.Witness
