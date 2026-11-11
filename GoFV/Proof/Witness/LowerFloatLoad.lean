import GoFV.Proof.Witness.LowerPeep

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`'s float loads: `fld` (hand-written, issue #385)

`fld() int { f := *(*float64)(unsafe.Pointer(&g)); *(*float64)(unsafe.Pointer(&g)) = f; return g }`
on the global `g` of `LowerNarrowArgs` (`narMem`: `g` holds `0x1_0000_019a`), as `lower` sees it:
`v4 = Load <float64> v3 v1` of `v3 = Addr {g} v2`, `v5 = Store {float64} v3 v4 v1`, `v6 = Load <int>
v3 v5`. `lower` gives `v4 = FMOVDload {g} v2 v1` (`(Load <t> ptr mem) && is64BitFloat(t) =>
(FMOVDload ptr mem)`, `ARM64.rules:322`, then the symbol folded, `868`); the float load is a term
of the lowered function (`GoFV.Proof.Low.ldOp?`).

By `lower_refines` every returning or panicking `run` of `fld` is, up to refinement, a `runL` of
the result; it returns 4294967706 (the float load and store copy the eight bytes of `g`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `nar` with `float64` (type 13) and its type aux (aux 6). -/
def fldTabs : Tables :=
  { narTabs with
    types := narTabs.types.set! 13 (some (mkT .FLOAT64 (some 8) "float64"))
    auxes := narTabs.auxes.push (some { fmt := GoStr.ofString "float64", kind := .type 13 }) }

/-- The pass environment of `lower` on `fld`. -/
def fldPassEnv : PassEnv :=
  { narPassEnv "fld" with tables := fldTabs
                          typs := (narPassEnv "fld").typs.push ("Float64", 13) }

/-- `fld`. -/
def fldFunc : Func := narFunc 7 7 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 3 #[2] 1),
  some (mkV 4 .Load 13 none p0 1 #[3, 1] 1),
  some (mkV 5 .Store 28 (some 6) p0 2 #[3, 4, 1] 1),
  some (mkV 6 .Load 2 none p0 1 #[3, 5] 1),
  some (mkV 7 .MakeResult 33 none p0 1 #[6, 5] 1)]

theorem fld_generic : fldFunc.lowered = false := by decide +kernel

/-- `fld` has no fused multiply-add shape: its contraction is itself. -/
theorem fld_noFma : GoFV.Opt.FmaContract.contractAll fldFunc = fldFunc := by decide +kernel

/-- The float load of `fld`'s lowered result. -/
def fldShow (f : Func) : Option (Op × Int64 × Option AuxRef × Array ID) :=
  (f.value? 4).map fun v => (v.op, v.auxInt, v.aux, v.args)

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `fld` whose `v4` is
`FMOVDload {g} v2 v1`, and `fld` returns 4294967706 under `run` of the input and `runL` of the
result. -/
theorem fld_checks :
    (lowerChecked fldPassEnv fldFunc).toOption.map (fun o =>
      (fldShow o.func, o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 4294967706)) =
      some (some (.ARM64FMOVDload, 0, some 4, #[2, 1]), true, true) ∧
    returnsInt (run Env.p1 fldTabs fldFunc [] narMem 1) 4294967706 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on the float loads: on
`fld`, the checked lower's `v4` is `FMOVDload {g} v2 v1` (`ARM64.rules:322`, `868`,
`GoFV.Proof.Low.Rules.r_ARM64_322_sound`, `GoFV.Proof.Low.Rules.r_ARM64_868_sound`), and every
returning or panicking `run` of `fld` is, up to refinement, a `runL` of the result. -/
theorem fld_lower :
    ∃ out, lowerChecked fldPassEnv fldFunc = .ok out ∧ out.func.lowered = true ∧
      fldShow out.func = some (.ARM64FMOVDload, 0, some 4, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract fldFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre fldPassEnv.tables fldFunc) env mem)
        out.tables out.func fldPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre fldPassEnv.tables fldFunc) env mem → ∀ fuel,
        (run env fldTabs fldFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env fldTabs fldFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := fld_checks
  cases hc : lowerChecked fldPassEnv fldFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hv, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hv, GoFV.Proof.Low.lower_refines hc fld_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc fld_generic fld_noFma hE hro hd⟩

end GoFV.Proof.Witness
