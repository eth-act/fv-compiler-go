import GoFV.Proof.Obj.Whole
import GoFV.Proof.Pass.PipelineFull

variable [GoFV.SSA.Sem.Addrs]

/-!
# Generic SSA to machine words (`docs/plans/proofs3.md` §1)

`verifiedPipelineFull_refines` (Phase 2: every returning or panicking `run` of the generic SSA
input is refined by a `runLoc` of `trim`'s output) composed with `obj_whole_ret` (Phase 3: a
returning `runLoc` body of a function `checkG50L`, `retRegsOK` and `checkObj` accept is matched by
`runMach` of the linked words, with the results in their ABI registers) and `obj_whole_panic` (a
panicking body by a panicking `runMach`), on slice G50: `checkG50` accepts the pipeline's output
`LocCtx.make tabs f` when `refsLive` holds of it and `checkG50L` accepts `liveCtx` of it (the homes
of removed values dropped), under which `runLoc` runs alike (`runLoopLoc_live`). `runLoc` is
`finish` of its body `runLoopLoc` (`runLoc_eq`), whose outcome is returned or panicked when
`runLoc`'s is (`finish_defined`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Opt GoFV.Opt.Verified GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (enterListLoc OutcomeRefines)

/-- A `runLoc` outcome that is returned or panicked has the right number of arguments. -/
theorem runLoc_args {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel : Nat} (h : (runLoc env tabs f args mem fuel).Defined) :
    args.length = (LocCtx.make tabs f).ctx.params.size := by
  by_cases hne : args.length = (LocCtx.make tabs f).ctx.params.size
  · exact hne
  · have hb : (args.length != (LocCtx.make tabs f).ctx.params.size) = true := by simpa using hne
    simp only [runLoc, runCtxLoc, hb, ↓reduceIte] at h
    exact h.elim

/-- **Generic SSA to machine words.** `f` goes through the verified pipeline (`fullyVerified`)
to the allocated function `r.st.func` (tables `r.st.tables`); genssa's P0 Progs `ps` of it are
accepted by `checkG50` (so `checkG50L` accepts them on `lc`, `LocCtx.make` of the pipeline's
output without the homes of removed values, `liveCtx`), its returns by `retRegsOK` (the register
results in their ABI registers, `ownOutRegs`), and the assembler's output `o` by `checkObj`
(`ObjEnv`: linked at `base` to `code`, the caller's return address `s0.x 30`). On every input of
Phase 1's `VPre` with the pipeline's premises, a `run` of `f` that returns or panics is refined by
a `runLoc` of `r.st.func` (`OutcomeRefines`), which is `finish` of its body `runLoopLoc` on `lc`
from `locInit`; when the body returns `(rs, mm)`, `runMach` of the linked words from the
function's entry `s0` returns to `s0.x 30` with the caller's `SP`, `g` and frame pointer
(`MachRet`), `rs` in the result registers (`R0`–`R15` or `F0`–`F15`) and `mm` (with the results
on the stack, in their `PPARAMOUT` variables) injected into the memory (`ResultRel`); when the
body panics with `pe` and the panic premises hold (the
trusted `HookPanicMap` and `BoundsOK`, and `RunPanicPre`: the run's panics come from nil checks,
loads, stores and acquire loads that fault in the nil page, bounds checks and static, interface or
closure calls whose callee panics by the trusted `CallPanicOK`, `ICallPanicOK`), `runMach` panics
with `pe` or, for a bounds check, with the runtime's report of the same failure (`BoundsAgree`).

Premises of the machine side: those of `obj_whole_ret` (trusted: `HookMap`, `runtime.morestack`'s
contract `MorestackOK` at the morestack tail's call, and in `RunPre` the callee contracts
`CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK`; the caller's side: `MachEntry`,
`EntryMatch`/`EntryEnv` of the arguments, memory and frame at the entry, and for a function with
a stack check the spill slots apart from `g` (`TailSep`) and the entry values surviving the
morestack tail (`MoreEntry`)). -/
theorem verified_mach
    {penv : PassEnv} {f : Func} {zv : Array (ID × Nat)} {dcl : Nat} {r : FState}
    (hpipe : verifiedPipelineFull penv f 0 zv dcl = .ok r) (hv : r.fullyVerified = true)
    {e : Env} {args : List Val} {mem : Mem}
    (hP : VPre (NilCheck.dictParams penv.tables f) (pipelineRo penv f) (pipelineEq penv) e args
      mem)
    (hn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 e args mem)
    (ha : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 e args mem)
    (hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 e args mem) {fuel : Nat}
    (hd : (GoFV.SSA.run e penv.tables f args mem fuel).Defined)
    {lc : LocCtx} (hlc : lc = liveCtx (LocCtx.make r.st.tables r.st.func))
    {H : Hooks} {g : G2In} {L : Link} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    {kt : KTab} {E0 : MatchEnv} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64} {code : Code} {room : Nat} {s0 : MState}
    (hc : checkG50 (LocCtx.make r.st.tables r.st.func) ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    (hrok : retRegsOK lc kt = true)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hms : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → ∀ n add,
      tailCall o.text o.relocs.toList tail = some (n, add) →
      MorestackOK H code (s0.x 30) (L.sym n + BitVec.ofInt 64 add) otab.autosize gOff s0)
    (hsep : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → TailSep spills.toList s0)
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    {sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc e lc (locInit e lc args mem) (blkE.values.toList.take k) = .ok sI)
    (hent : EntryMatch E0 sI s0)
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry E0 spills.toList gOff sI s0)
    (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI)
    (huE : uL35 lc [] blkE k = [])
    (hpc : ObjEnv.map otab ps L base (E0.pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hRP : RunPre e H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e penv.tables f args mem fuel)
        (runLoc e r.st.tables r.st.func args mem fuel') ∧
      ∃ raw, runLoopLoc e lc fuel' (locInit e lc args mem) lc.ctx.f.entry = raw ∧
        runLoc e r.st.tables r.st.func args mem fuel' =
          finish e lc.ctx.outs lc.ctx.defers lc.ctx.act raw ∧
        raw.Defined ∧
      (∀ rs mm, raw = .returned rs mm →
        ∃ E t' n, E0.Extends E ∧ runMach H code (s0.x 30) n s0 = .returned t' ∧
          MachRet s0 t' ∧ ResultRel E (ownOutRegs lc) rs mm t') ∧
      (∀ pe mm, raw = .panicked pe mm → HookPanicMap H L ps.toList (ObjEnv.map otab ps L base) →
        BoundsOK H g L ps.toList →
        RunPanicPre e H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI →
        ∃ pe' n t', BoundsAgree pe pe' ∧ runMach H code (s0.x 30) n s0 = .panicked pe' t') := by
  obtain ⟨fuel', href⟩ := verifiedPipelineFull_refines hpipe hv hP hn ha hnp hd
  have hd' : (runLoc e r.st.tables r.st.func args mem fuel').Defined := href.defined_right
  have hargs := runLoc_args hd'
  obtain ⟨hr, hc⟩ := checkG50_spec hc
  have heq : runLoc e r.st.tables r.st.func args mem fuel' =
      finish e lc.ctx.outs lc.ctx.defers lc.ctx.act
        (runLoopLoc e lc fuel' (locInit e lc args mem) lc.ctx.f.entry) := by
    rw [runLoc_eq hargs, hlc, runLoopLoc_live hr]
    rfl
  subst hlc
  refine ⟨fuel', href, _, rfl, heq, finish_defined (heq ▸ hd'), fun rs mm hraw => ?_,
    fun pe mm hraw hHP hbok hPP => ?_⟩
  · exact obj_whole_ret hc hO hH hic hrok hME hroom hg hms hsep hE hEE hbE hbm hk
      (by exact rfl) hpre hent hmore hinv huE hpc hRP hraw
  · exact obj_whole_panic hc hO hH hHP hbok hic hME hroom hg hms hsep hE hEE hbE hbm hk
      (by exact rfl) hpre hent hmore hinv huE hpc hRP hPP hraw

end GoFV.Proof.Obj
