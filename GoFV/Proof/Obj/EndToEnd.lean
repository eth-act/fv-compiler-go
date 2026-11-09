import GoFV.Proof.Obj.Whole
import GoFV.Proof.Pass.PipelineFull

/-!
# Generic SSA to machine words (`docs/plans/proofs3.md` §1)

`verifiedPipelineFull_refines` (Phase 2: every returning or panicking `run` of the generic SSA
input is refined by a `runLoc` of `trim`'s output) composed with `obj_whole_ret` (Phase 3: a
returning `runLoc` body of a function `checkG30`, `retRegsOK` and `checkObj` accept is matched by
`runMach` of the linked words, with the results in their ABI registers) and `obj_whole_panic` (a
panicking body by a panicking `runMach`). `runLoc` is `finish` of its body `runLoopLoc`
(`runLoc_eq`), whose outcome is returned or panicked when `runLoc`'s is (`finish_defined`).
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
accepted by `checkG30`, its returns by `retRegsOK` (the results in the ABI registers `outs`), and
the assembler's output `o` by `checkObj` (`ObjEnv`: linked at `base` to `code`, the caller's
return address `s0.x 30`). On every input of Phase 1's `VPre` with the pipeline's premises, a
`run` of `f` that returns or panics is refined by a `runLoc` of `r.st.func` (`OutcomeRefines`),
which is `finish` of its body `runLoopLoc` from `locInit`; when the body returns `(rs, mm)`,
`runMach` of the linked words from the function's entry `s0` returns to `s0.x 30` with the
caller's `SP`, `g` and frame pointer (`MachRet`), `rs` in the result registers and `mm` injected
into the memory (`ResultRel`); when the body panics with `pe` and the panic premises hold (the
trusted `HookPanicMap` and `BoundsOK`, and `RunPanicPre`: the run's panics come from nil checks,
bounds checks and static calls whose callee panics by the trusted `CallPanicOK`), `runMach`
panics with `pe` or, for a bounds check, with the runtime's report of the same failure
(`BoundsAgree`).

Premises of the machine side: those of `obj_whole_ret` (trusted: `HookMap`, and in `RunPre` the
callee contracts `CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK`; the caller's side:
`MachEntry`, the stack check passing, `EntryMatch`/`EntryEnv` of the arguments, memory and frame
at the entry). -/
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
    {lc : LocCtx} (hlc : lc = LocCtx.make r.st.tables r.st.func)
    {H : Hooks} {g : G2In} {L : Link} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    {kt : KTab} {E0 : MatchEnv} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64} {code : Code} {room : Nat} {s0 : MState}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {outs : List Nat} (hrok : retRegsOK lc kt = true) (houts : ownOutRegs lc = some outs)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      CheckPasses otab.autosize gOff s0)
    (hlf : otab.autosize = 0 ∨ otab.leaf = false)
    (hE : G28Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    {sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc e lc (locInit e lc args mem) (blkE.values.toList.take k) = .ok sI)
    (hent : EntryMatch E0 sI s0) (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI)
    (huE : uL lc blkE k = [])
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
          MachRet s0 t' ∧ ResultRel E outs rs mm t') ∧
      (∀ pe mm, raw = .panicked pe mm → HookPanicMap H L ps.toList (ObjEnv.map otab ps L base) →
        BoundsOK H g L ps.toList → RunPanicPre e H lc g L E0 lc.ctx.f.entry k sI →
        ∃ pe' n t', BoundsAgree pe pe' ∧ runMach H code (s0.x 30) n s0 = .panicked pe' t') := by
  obtain ⟨fuel', href⟩ := verifiedPipelineFull_refines hpipe hv hP hn ha hnp hd
  have hd' : (runLoc e r.st.tables r.st.func args mem fuel').Defined := href.defined_right
  have hargs := runLoc_args hd'
  have heq := runLoc_eq (env := e) (mem := mem) (fuel := fuel') hargs
  subst hlc
  refine ⟨fuel', href, _, rfl, heq, finish_defined (heq ▸ hd'), fun rs mm hraw => ?_,
    fun pe mm hraw hHP hbok hPP => ?_⟩
  · exact obj_whole_ret hc hO hH hic hrok houts hME hroom hg hpass hlf hE hEE hbE hbm hk hpre hent
      hinv huE hpc hRP hraw
  · exact obj_whole_panic hc hO hH hHP hbok hic hME hroom hg hpass hE hEE hbE hbm hk hpre hent hinv
      huE hpc hRP hPP hraw

end GoFV.Proof.Obj
