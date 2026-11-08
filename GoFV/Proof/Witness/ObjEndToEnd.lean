import GoFV.Proof.Obj.EndToEnd
import GoFV.Proof.Witness.ObjWhole
import GoFV.Proof.Witness.PipelineFull

/-!
# Non-vacuity witness: generic SSA to machine words (`verified_mach`)

`pallocSum.start` of `std/runtime` from its first export section (the input of `number lines`,
`GenG3.startSsa`), in the pass environment `gofv-ssa-opt --verified` builds for it (`baseEnv`, the
whole-file environment), through `verifiedPipelineFull` (`fullyVerified`) to the allocated
function; genssa's Progs (`GenG3.ps`) are accepted by `checkG18` and its return by `retRegsOK`
against the pipeline's output (`ObjWhole.lcFacts`), and the assembler's words by `checkObj`
(`ObjWhole.obj_premises`). On the argument `p = 7` in the Phase 1 test environment `plRunEnv`
(`VPre` as for `isNaN` in `PipelineFull.lean`), the generic `run` returns; `verified_mach`
gives the `runLoc` that refines it, its body's outcome, and the machine run that returns to the
caller with it, the result in the ABI's result register `X0`. By compiled evaluation
(`native_decide`, listed in `scripts/axioms-allowlist.txt`; `e2e_facts`): the
export parses, the pipeline is `fullyVerified` with `schedule` inputs free of memory ops,
pointer-shaped parameter pieces and checked pointers, `lcFacts` holds of its output, the generic
`run` returns, and the input has no dictionary parameter and no read-only symbol.
-/

namespace GoFV.Proof.Witness.ObjEndToEnd

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Gen.Check GoFV.Arm64 GoFV.Asm
open GoFV.Proof.Gen GoFV.Proof.Obj GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (OutcomeRefines)
open GoFV.Proof.Witness (plRunEnv plRunEnv_mono plRunEnv_frameSafe plRunEnv_allocNonNil
  plRunEnv_wbPre plRunEnv_tempOblivious plRunEnv_memOps plRunEnv_keeps plRunEnv_allocZero
  plRunEnv_growLen plRunEnv_ifaceEq noActB noArgPtrB noNilPtrB)

/-! ## The pass environment (`gofv-ssa-opt --verified`, `GoFVTest/Driver/Main.lean`) -/

/-- The file's `ptrcache` as a predicate. -/
def ptrCacheFn (ts : Array TypeRef) : TypeRef → Bool :=
  let m : Std.HashMap TypeRef Unit := ts.foldl (fun m t => m.insert t ()) {}
  fun t => m.contains t

/-- The file's `typelink` groups as a key: each member maps to its group's first number. -/
def typeLinkFn (groups : Array (Array TypeRef)) : TypeRef → TypeRef :=
  let m : Std.HashMap TypeRef TypeRef :=
    groups.foldl (fun m g => match g[0]? with
      | some r => g.foldl (fun m t => m.insert t r) m
      | none => m) {}
  fun t => m.getD t t

/-- `t` with its arrays at least as long as `all`'s. -/
def padTables (t all : Tables) : Tables :=
  let pad {α} (a : Array (Option α)) (n : Nat) : Array (Option α) :=
    if a.size < n then a ++ Array.replicate (n - a.size) none else a
  { t with types := pad t.types all.types.size, auxes := pad t.auxes all.auxes.size
           slots := pad t.slots all.slots.size }

/-- The whole-file pass environment of an export file's header with the given tables. -/
def baseEnv (e : ExportFile) (tables : Tables) : PassEnv :=
  let typs := ((e.sections[0]?).bind (·.typs)).getD #[]
  { passName := "", pkg := e.pkg, funcName := e.name, abi := e.abi, nosplit := e.nosplit
    pgohot := e.pgohot, config := e.config, typs
    typeOrder := TypeOrder.ofGroups e.typeOrder e.typeCmp
    tables, frontend := e.frontendTables, ptrCache := ptrCacheFn e.ptrCache
    typeLink := typeLinkFn e.typeLink }

/-- The parsed export of `pallocSum.start`. -/
def exIn : Except String (ExportFile × ExportExt) := parseExportExt GenG3.startSsa.toUTF8

def file : ExportFile :=
  match exIn with
  | .ok x => x.1
  | .error _ => default

def ext : ExportExt :=
  match exIn with
  | .ok x => x.2
  | .error _ => default

/-- The first section: the input of `number lines`. -/
def sec0 : Section := (file.sections[0]?).getD default

def penv : PassEnv := baseEnv file (padTables (({} : Tables).addAll sec0.defs) file.frontendTables)

/-- The generic SSA input. -/
def f0 : Func := sec0.func

def dcl : Nat := (ext.dclLen? 0).getD 0

/-! ## The facts -/

def isRetG : Outcome → Bool
  | .returned _ _ => true
  | _ => false

/-- What compiled evaluation checks. -/
def e2eFacts : Bool :=
  ((verifiedPipelineFull penv f0 0 sec0.zvar dcl).toOption.map fun r =>
      r.fullyVerified &&
        r.nnf.all (fun x => noActB x.2 && noArgPtrB x.1 x.2 && noNilPtrB x.1 x.2) &&
        ObjWhole.lcFacts plRunEnv (LocCtx.make r.st.tables r.st.func)) == some true &&
    isRetG (GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5) &&
    (NilCheck.dictParams penv.tables f0).isEmpty && (pipelineRo penv f0).isEmpty

theorem e2e_facts : e2eFacts = true := by
  native_decide

theorem initAvoids : InitAvoids plRunEnv ObjWhole.args {} := by
  intro a n
  refine ⟨fun v h => ?_, fun _ _ h => ?_, rfl, fun g hg x hx => ?_⟩
  · simp only [ObjWhole.args, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    trivial
  · simp at h
  · simp only [plRunEnv, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [Array.toList_replicate, List.mem_replicate] at hx
      rw [hx.2]
      trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      rw [hx]
      trivial

/-- **Non-vacuity of `verified_mach`**: on `pallocSum.start` with `p = 7`, the verified pipeline
returns a `fullyVerified` state, the generic `run` returns, and `verified_mach` applies with every
premise discharged: a `runLoc` of the allocated function refines the `run`, it is `finish` of its
body's defined outcome, and when the body returns, `runMach` of the linked words from the
function's entry returns to the caller's `0x40` (`MachRet`) with the results in `X0`
(`ResultRel`). (Its panic branch is exercised by `ObjPanic.objWhole_panic_witness`.) -/
theorem verified_mach_witness :
    ∃ r, verifiedPipelineFull penv f0 0 sec0.zvar dcl = .ok r ∧ r.fullyVerified = true ∧
      (∃ rs m, GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5 = .returned rs m) ∧
      ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5)
          (runLoc plRunEnv r.st.tables r.st.func ObjWhole.args {} fuel') ∧
        ∃ raw, runLoopLoc plRunEnv (LocCtx.make r.st.tables r.st.func) fuel'
            (locInit plRunEnv (LocCtx.make r.st.tables r.st.func) ObjWhole.args {})
            (LocCtx.make r.st.tables r.st.func).ctx.f.entry = raw ∧
          runLoc plRunEnv r.st.tables r.st.func ObjWhole.args {} fuel' =
            finish plRunEnv (LocCtx.make r.st.tables r.st.func).ctx.outs
              (LocCtx.make r.st.tables r.st.func).ctx.defers
              (LocCtx.make r.st.tables r.st.func).ctx.act raw ∧
          raw.Defined ∧
          ∀ rs mm, raw = .returned rs mm →
            ∃ E t' n, (ObjWhole.E0 (LocCtx.make r.st.tables r.st.func)).Extends E ∧
              runMach GenG2.H0 ObjG7.startCode (ObjWhole.s0.x 30) n ObjWhole.s0 = .returned t' ∧
              MachRet ObjWhole.s0 t' ∧ ResultRel E [0] rs mm t' := by
  have hf := e2e_facts
  simp only [e2eFacts, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hf
  obtain ⟨⟨⟨hp, hrun⟩, hdict⟩, hro⟩ := hf
  cases hpe : verifiedPipelineFull penv f0 0 sec0.zvar dcl with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hp
    obtain ⟨⟨hv, hn⟩, hlcf⟩ := hp
    have hx2 : ∀ x ∈ r.nnf,
        (noActB x.2 = true ∧ noArgPtrB x.1 x.2 = true) ∧ noNilPtrB x.1 x.2 = true := fun x hx => by
      have := List.all_eq_true.1 hn x hx
      simpa only [Bool.and_eq_true] using this
    have hnn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 plRunEnv ObjWhole.args {} := fun x hx =>
      noNilFault_of_noAct (hx2 x hx).1.1 plRunEnv ObjWhole.args {}
    have hap : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 plRunEnv ObjWhole.args {} := fun x hx =>
      argPtrsOK_of_none (hx2 x hx).1.2 plRunEnv ObjWhole.args {}
    have hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 plRunEnv ObjWhole.args {} := fun x hx =>
      nilPtrsOK_of_none (hx2 x hx).2 plRunEnv ObjWhole.args {}
    have hvpre : VPre (NilCheck.dictParams penv.tables f0) (pipelineRo penv f0)
        (pipelineEq penv) plRunEnv ObjWhole.args {} :=
      ⟨plRunEnv_mono, plRunEnv_frameSafe, initAvoids, plRunEnv_allocNonNil,
        by rw [hdict]; exact DictArgs.nil ObjWhole.args, plRunEnv_wbPre, plRunEnv_tempOblivious,
        plRunEnv_memOps,
        by rw [hro]; exact RoImage.nil (env := plRunEnv) (plRunEnv_keeps Mem.KeepsRo.refl) {},
        plRunEnv_keeps Mem.KeepsFrame.refl, plRunEnv_allocZero, plRunEnv_growLen,
        plRunEnv_ifaceEq _⟩
    obtain ⟨rs0, m0, hrun0⟩ : ∃ rs m, GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5 =
        .returned rs m := by
      revert hrun
      cases GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5 <;> simp [isRetG]
    have hd : (GoFV.SSA.run plRunEnv penv.tables f0 ObjWhole.args {} 5).Defined := by
      rw [hrun0]; trivial
    obtain ⟨hO, hH, hME, hroom, hg, hpass, hlf, -, hEE, hpc, -, -, hic⟩ := ObjWhole.obj_premises
    obtain ⟨hc, hrok, houts, hE, hb1, hbm, hk, hentry, sI, hsI, hent, hinv, hP⟩ :=
      ObjWhole.lc_premises hlcf
    rw [← hentry] at hpc
    obtain ⟨fuel', href, raw, hraw, hfin, hdef, hret, -⟩ :=
      verified_mach hpe hv hvpre hnn hap hnp hd rfl hc hO hH hic hrok houts hME hroom hg hpass
        hlf hE (hEE _) hb1 hbm hk hsI hent hinv (hpc _) hP
    exact ⟨r, rfl, hv, ⟨rs0, m0, hrun0⟩, fuel', href, raw, hraw, hfin, hdef, hret⟩

end GoFV.Proof.Witness.ObjEndToEnd
