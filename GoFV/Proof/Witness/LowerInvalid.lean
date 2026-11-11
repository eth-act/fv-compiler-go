import GoFV.Proof.Low.Lower
import GoFV.Proof.Witness.LowerAdd
import GoFV.Proof.Witness.MemCombineStore
import GoFV.Opt.VerifiedFull

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on an input with an `Invalid` value: `littleEndian.PutUint16` (issue #385)

`encoding/binary.littleEndian.PutUint16` (`GoFV.Proof.Witness.MemCombineStore`: section 30 of
`std/std/encoding/binary/littleEndian.PutUint16,1.ssa`, the input of `memcombine`, transcribed
by hand). Its `lower` input is memcombine's result (writebarrier has no store to expand there and
keeps it): memcombine combines the two byte stores into the 2-byte `v43 = Store {uint16} v36 v9
v1` and resets `v30` in place to `Invalid` (`clobber`), as stock does. The input is therefore
`Func.lowered`, and `lowerGuard` rejected it; read as `Unknown` (`invUnknown`) it is generic, so
`lowerGuard` accepts it. The checked lower keeps a lowered result, which frees `v30` and lowers
`v43` to `MOVHstore v36 v9 v1`; `run` of the input, `v30` included, writes `1, 2` into `b = [0,
0]` for `v = 0x0201`, and by `lower_refines_runU` every returning or panicking `run` of the input
is, up to refinement, a `runL` of the result (`runL` of which writes `1, 2` too).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.LowerCheck GoFV.Proof

/-- memcombine's result on `PutUint16`: the input of `lower`. -/
def lpiMc : PassOut :=
  match memcombineChecked lePut16PassEnv lePut16 with
  | .ok o => o
  | .error _ => { func := lePut16, tables := lePut16Tabs }

/-- Its tables with the `flags` (32) and `void` (33) types of section 0, which `lower` reads and
`lePut16Tabs` leaves out. -/
def lpiTabs : Tables :=
  { lpiMc.tables with
    types := (lpiMc.tables.types.set! 32 (some (mkT .SSA none "flags"))).set! 33
      (some (mkT .SSA none "void")) }

/-- The pass environment of `lower` (arm64, the export's fixed configuration). -/
def lpiPassEnv : PassEnv :=
  { laPassEnv with funcName := lePut16PassEnv.funcName,
                   typs := leU16Typs ++ #[("Flags", 32), ("Void", 33)], tables := lpiTabs }

/-- By kernel evaluation: the input holds `v30 = Invalid`, so it is lowered, but not once read
with `Unknown`, and it has no fused multiply-add shape; the checked lower keeps a lowered result
without `v30` whose `v43` is `MOVHstore v36 v9 v1`; `PutUint16([0, 0], 0x0201)` writes `1, 2`
under `run` of the input and `runL` of the result. -/
theorem lpi_checks :
    (lpiMc.func.value? 30).map (·.op) = some .Invalid ∧ lpiMc.func.lowered = true ∧
    (invUnknown lpiMc.func).lowered = false ∧
    GoFV.Opt.FmaContract.contractAll lpiMc.func = lpiMc.func ∧
    (lowerChecked lpiPassEnv lpiMc.func).toOption.map (fun o =>
      ((o.func.value? 43).map (fun v => (v.op, v.args)),
        o.func.lowered && (o.func.value? 30).isNone &&
          wrote12 (runL Env.p1 o.tables o.func lePut16Args lePut16Mem 2))) =
      some (some (.ARM64MOVHstore, #[36, 9, 1]), true) ∧
    wrote12 (run Env.p1 lpiTabs lpiMc.func lePut16Args lePut16Mem 2) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines_runU` on an input with an `Invalid` value: on
memcombine's result for `PutUint16` (lowered only by its `v30 = Invalid`), `lowerGuard` accepts,
the checked lower keeps a lowered result without `v30`, `run` of the input returns having written
`1, 2`, and every returning or panicking `run` of the input is, up to refinement, a `runL` of the
result. -/
theorem lpi_lower :
    (lpiMc.func.value? 30).map (·.op) = some .Invalid ∧ lpiMc.func.lowered = true ∧
    ∃ out, lowerChecked lpiPassEnv lpiMc.func = .ok out ∧
      Verified.lowerGuard lpiPassEnv lpiMc.func out = true ∧ out.func.lowered = true ∧
      out.func.value? 30 = none ∧
      (∃ fuel m, run Env.p1 lpiTabs lpiMc.func lePut16Args lePut16Mem fuel = .returned [] m ∧
        m.read ⟨.heap 0, 0⟩ 2 = some #[.b 1, .b 2]) ∧
      ∀ env, env.Mono → ∀ args mem,
        RoImage (LowerCheck.roPre lpiTabs (invUnknown lpiMc.func)) env mem → ∀ fuel,
        (run env lpiTabs lpiMc.func args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lpiTabs lpiMc.func args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h30, hlow, hinv, hfma, h1, hrun⟩ := lpi_checks
  refine ⟨h30, hlow, ?_⟩
  cases hc : lowerChecked lpiPassEnv lpiMc.func with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq,
      Bool.and_eq_true] at h1
    obtain ⟨-, ⟨hl, hn⟩, -⟩ := h1
    have hg : Verified.lowerGuard lpiPassEnv lpiMc.func out = true := by
      simp only [Verified.lowerGuard, hinv, hfma, beq_self_eq_true, decide_true, Bool.and_self]
    obtain ⟨m, hm, hrd⟩ := wrote12_iff.1 hrun
    exact ⟨out, rfl, hg, hl, Option.isNone_iff_eq_none.1 hn, ⟨2, m, hm, hrd⟩,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_runU hc hinv hfma hE hro hd⟩

end GoFV.Proof.Witness
