import GoFV.Proof.Witness.ObjEndToEnd
import GoFV.Proof.Witness.ObjWholeS

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: generic SSA to machine words in G48's mode (`verified_mach_S`)

`ObjEndToEnd`'s witness (`pallocSum.start` from its generic SSA through `verifiedPipelineFull`,
`p = 7`, `plRunEnv`) for `verified_mach_S`: the activation in G48's mode (`ObjWholeS`: `SP` at
`outargs 0`'s fixed base `0x4000000000000000`, `SepFromW`, `SPInv` at the entry, `RunPreS` by
`runPreS_simple`). By compiled evaluation (`native_decide`, listed in
`scripts/axioms-allowlist.txt`; `e2e_factsS`): as `ObjEndToEnd.e2e_facts`, with `ObjWholeS.lcFacts`.
-/

namespace GoFV.Proof.Witness.ObjEndToEndS

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Gen.Check GoFV.Arm64 GoFV.Asm
open GoFV.Proof.Gen GoFV.Proof.Obj GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (OutcomeRefines)
open GoFV.Proof.Witness (plRunEnv plRunEnv_mono plRunEnv_frameSafe plRunEnv_allocNonNil
  plRunEnv_wbPre plRunEnv_tempOblivious plRunEnv_memOps plRunEnv_keeps plRunEnv_allocZero
  plRunEnv_growLen plRunEnv_ifaceEq noActB noArgPtrB noNilPtrB)
open GoFV.Proof.Witness.ObjEndToEnd (penv f0 sec0 dcl isRetG initAvoids)

/-- What compiled evaluation checks. -/
def e2eFactsS : Bool :=
  ((verifiedPipelineFull penv f0 0 sec0.zvar dcl).toOption.map fun r =>
      r.fullyVerified &&
        r.nnf.all (fun x => noActB x.2 && noArgPtrB x.1 x.2 && noNilPtrB x.1 x.2) &&
        refsLive (LocCtx.make r.st.tables r.st.func) &&
        ObjWholeS.lcFacts plRunEnv (liveCtx (LocCtx.make r.st.tables r.st.func))) == some true &&
    isRetG (GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5) &&
    (NilCheck.dictParams penv.tables f0).isEmpty && (pipelineRo penv f0).isEmpty

theorem e2e_factsS : e2eFactsS = true := by
  native_decide

/-- **Non-vacuity of `verified_mach_S`**: on `pallocSum.start` with `p = 7` in G48's mode (`SP` at
`outargs 0`'s fixed base, `SepFromW`, `SPInv`, the `CallOKS` contracts), the verified pipeline
returns a `fullyVerified` state, the generic `run` returns, and `verified_mach_S` applies with every
premise discharged: a `runLoc` of the allocated function refines the `run`, it is `finish` of its
body's defined outcome, and when the body returns, `runMach` of the linked words from the
function's entry returns to the caller's `0x40` (`MachRet`) with the results in `X0`
(`ResultRel`). -/
theorem verified_mach_S_witness :
    ∃ r, verifiedPipelineFull penv f0 0 sec0.zvar dcl = .ok r ∧ r.fullyVerified = true ∧
      (∃ rs m, GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5 = .returned rs m) ∧
      ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5)
          (runLoc plRunEnv r.st.tables r.st.func ObjWholeS.args {} fuel') ∧
        ∃ raw, runLoopLoc plRunEnv (liveCtx (LocCtx.make r.st.tables r.st.func)) fuel'
            (locInit plRunEnv (liveCtx (LocCtx.make r.st.tables r.st.func)) ObjWholeS.args {})
            (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.f.entry = raw ∧
          runLoc plRunEnv r.st.tables r.st.func ObjWholeS.args {} fuel' =
            finish plRunEnv (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.outs
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.defers
              (liveCtx (LocCtx.make r.st.tables r.st.func)).ctx.act raw ∧
          raw.Defined ∧
          ∀ rs mm, raw = .returned rs mm →
            ∃ E t' n, (ObjWholeS.E0 (liveCtx (LocCtx.make r.st.tables r.st.func))).Extends E ∧
              runMach GenG2.H0 ObjG7.startCode (ObjWholeS.s0.x 30) n ObjWholeS.s0 = .returned t' ∧
              MachRet ObjWholeS.s0 t' ∧ ResultRel E [0] rs mm t' := by
  have hf := e2e_factsS
  simp only [e2eFactsS, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hf
  obtain ⟨⟨⟨hp, hrun⟩, hdict⟩, hro⟩ := hf
  cases hpe : verifiedPipelineFull penv f0 0 sec0.zvar dcl with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨hv, hn⟩, hrl⟩, hlcf⟩ := hp
    have hx2 : ∀ x ∈ r.nnf,
        (noActB x.2 = true ∧ noArgPtrB x.1 x.2 = true) ∧ noNilPtrB x.1 x.2 = true := fun x hx => by
      have := List.all_eq_true.1 hn x hx
      simpa only [Bool.and_eq_true] using this
    have hnn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 plRunEnv ObjWholeS.args {} := fun x hx =>
      noNilFault_of_noAct (hx2 x hx).1.1 plRunEnv ObjWholeS.args {}
    have hap : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 plRunEnv ObjWholeS.args {} := fun x hx =>
      argPtrsOK_of_none (hx2 x hx).1.2 plRunEnv ObjWholeS.args {}
    have hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 plRunEnv ObjWholeS.args {} := fun x hx =>
      nilPtrsOK_of_none (hx2 x hx).2 plRunEnv ObjWholeS.args {}
    have hvpre : VPre (NilCheck.dictParams penv.tables f0) (pipelineRo penv f0)
        (pipelineEq penv) plRunEnv ObjWholeS.args {} :=
      ⟨plRunEnv_mono, plRunEnv_frameSafe, initAvoids, plRunEnv_allocNonNil,
        by rw [hdict]; exact DictArgs.nil ObjWholeS.args, plRunEnv_wbPre, plRunEnv_tempOblivious,
        plRunEnv_memOps,
        by rw [hro]; exact RoImage.nil (env := plRunEnv) (plRunEnv_keeps Mem.KeepsRo.refl) {},
        plRunEnv_keeps Mem.KeepsFrame.refl, plRunEnv_allocZero, plRunEnv_growLen,
        plRunEnv_ifaceEq _⟩
    obtain ⟨rs0, m0, hrun0⟩ : ∃ rs m, GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5 =
        .returned rs m := by
      revert hrun
      cases GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5 <;> simp [isRetG]
    have hd : (GoFV.SSA.run plRunEnv penv.tables f0 ObjWholeS.args {} 5).Defined := by
      rw [hrun0]; trivial
    obtain ⟨hO, hH, hME, hroom, hg, hnone, -, hEE, hpc, -, -, hic⟩ := ObjWholeS.obj_premises
    obtain ⟨hc, hrok, houts, hE, hb1, hbm, hk, hentry, hu, hes, hargs, sI, hsI, hent, hinv, hspI,
      hP⟩ := ObjWholeS.lc_premises hlcf
    have hc62 : checkG62 (LocCtx.make r.st.tables r.st.func) GenG3.ps GenG3.bs GenG3.g =
        .ok (GenG3.tab, GenG3.kt) := by
      simpa [checkG62, hrl] using hc
    rw [← hentry] at hpc
    obtain ⟨hmt, hcr⟩ := ObjWholeS.lc_ro hlcf
    obtain ⟨fuel', href, raw, hraw, hfin, hdef, hret, -⟩ :=
      verified_mach_S hpe hv hvpre hnn hap hnp hd rfl hc62 hO hH hic hrok hME hroom hg
        (fun _ _ _ h => by rw [hnone] at h; cases h) (fun _ _ _ h => by rw [hnone] at h; cases h)
        hE (hEE _) hb1 hbm hk hsI hes hargs hent (fun _ _ _ h => by rw [hnone] at h; cases h) hinv
        rfl (fun _ => hspI) hu
        (hpc _) hP (fun _ => hmt) (by rw [hcr]; intro n a h; cases h)
    rw [houts] at hret
    exact ⟨r, rfl, hv, ⟨rs0, m0, hrun0⟩, fuel', href, raw, hraw, hfin, hdef, hret⟩

end GoFV.Proof.Witness.ObjEndToEndS
