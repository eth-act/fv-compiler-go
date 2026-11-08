import GoFV.Proof.Witness.LowerCopyPtr

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a negative offset: `neg` (hand-written, issue #385)

`neg(p *[2]int) int { q := &p[1]; return *(*int)(unsafe.Add(unsafe.Pointer(q), -8)) }` as `lower`
sees it (one block: `v3 = OffPtr <*int> [8] v2`, `v4 = OffPtr <*int> [-8] v3`, `v5 = Load <int> v4
v1`, returned by `v6 = MakeResult v5 v1`). The checked lower with the proven `ARM64.rules` fires
`(OffPtr [off] ptr) => (ADDconst [off] ptr)` (306) twice and then `(ADDconst [c] y) && c < 0 =>
(SUBconst [-c] y)` (1000): `v4` becomes `SUBconst [8] v3`. By `lower_refines` every returning or
panicking `run` of `neg` is, up to refinement, a `runL` of the result; on `ldo`'s heap block both
return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `neg`, the input of `lower`. -/
def negFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 8 0 (some 5) p0 1 #[] 1),
    some (mkVI 3 .OffPtr 3 8 none p0 1 #[2] 1),
    some (mkVI 4 .OffPtr 3 (-8) none p0 1 #[3] 1),
    some (mkV 5 .Load 2 none p0 1 #[4, 1] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` for `neg`. -/
def negPassEnv : PassEnv :=
  { cpyPassEnv with funcName := GoStr.ofString "neg" }

theorem neg_generic : negFunc.lowered = false := by decide +kernel

/-- `neg` has no fused multiply-add shape: its contraction is itself. -/
theorem neg_noFma : GoFV.Opt.FmaContract.contractAll negFunc = negFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `SUBconst [8] v3`,
and `neg` returns 0 under `run` of the input and `runL` of the result (`cpy`'s tables). -/
theorem neg_checks :
    (lowerChecked negPassEnv negFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldsArgs ldoMem 1) 0)) =
      some (some (.ARM64SUBconst, 8, #[3]), true, true) ∧
    returnsInt (run Env.p1 cpyTabs negFunc ldsArgs ldoMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `(ADDconst [c] y) && c <
0 => (SUBconst [-c] y)`: on `neg`, the checked lower turns the `OffPtr [-8]` into `SUBconst [8] v3`,
and every returning or panicking `run` of `neg` is, up to refinement, a `runL` of the result. -/
theorem neg_lower :
    ∃ out, lowerChecked negPassEnv negFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64SUBconst, 8, #[3]) ∧
      (∃ f', GoFV.Proof.Low.Contract negFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func negPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env cpyTabs negFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cpyTabs negFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := neg_checks
  cases hc : lowerChecked negPassEnv negFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc neg_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc neg_generic neg_noFma hE hd⟩

end GoFV.Proof.Witness
