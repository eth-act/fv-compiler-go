import GoFV.Proof.Witness.LowerLoadStore

/-!
# Witness function for `lower` folding an offset into a load: `ldo` (hand-written, issue #385)

`ldo(p *[2]int) int { return p[1] }` as `lower` sees it (one block: `v3 = OffPtr <*int> [8] v2` of
the register argument `v2`, `v4 = Load <int> v3 v1`, returned by `v5 = MakeResult v4 v1`). The
checked lower with the proven `ARM64.rules` fires `(OffPtr [off] ptr) => (ADDconst [off] ptr)`
(306), `(Load <t> ptr mem) && (is64BitInt(t) || isPtr(t)) => (MOVDload ptr mem)` (320) and then
`(MOVDload [off1] {sym} (ADDconst [off2] ptr) mem) && … => (MOVDload [off1+int32(off2)] {sym} ptr
mem)` (676), so `v4` becomes `MOVDload [8] v2 v1`; the validator accepts the log, and by
`lower_refines` every returning or panicking `run` of `ldo` is, up to refinement, a `runL` of the
result; on a 16-byte heap block holding 7 at offset 8 both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `ldo`: the tables of `ldst` (`*int` is type 3; the result an `int`). -/
def ldoFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 5) p0 1 #[] 1),
    some (mkVI 3 .OffPtr 3 8 none p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .MakeResult 33 none p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- A 16-byte heap block holding 7 at offset 8. -/
def ldoMem : Mem :=
  { blocks := #[(.heap 0, { data := (Array.replicate 16 (.b 0)).set! 8 (.b 7) })], nextHeap := 1 }

theorem ldo_generic : ldoFunc.lowered = false := by decide +kernel

/-- `ldo` has no fused multiply-add shape: its contraction is itself. -/
theorem ldo_noFma : GoFV.Opt.FmaContract.contractAll ldoFunc = ldoFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `MOVDload [8] v2
v1`, and `ldo` returns 7 under `run` of the input and `runL` of the result. -/
theorem ldo_checks :
    (lowerChecked ldsPassEnv ldoFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldsArgs ldoMem 1) 7)) =
      some (some (.ARM64MOVDload, 8, #[2, 1]), true, true) ∧
    returnsInt (run Env.p1 ldsTabs ldoFunc ldsArgs ldoMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an offset folded into a
load: on `ldo`, the checked lower folds the `OffPtr`'s offset into the load (`MOVDload [8] v2 v1`),
and every returning or panicking `run` of `ldo` is, up to refinement, a `runL` of the result. -/
theorem ldo_lower :
    ∃ out, lowerChecked ldsPassEnv ldoFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDload, 8, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract ldoFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func ldsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env ldsTabs ldoFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ldsTabs ldoFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := ldo_checks
  cases hc : lowerChecked ldsPassEnv ldoFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc ldo_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc ldo_generic ldo_noFma hE hd⟩

end GoFV.Proof.Witness
