import GoFV.Proof.Obj.EndToEnd

/-!
# The end-to-end theorems at the fixed address assignment (`docs/plans/proofs3.md` §8)

The semantics takes its concrete addresses as a parameter (`Addrs`); `verifiedPipeline_refines`,
`verifiedPipelineFull_refines` and `verified_mach_ret` hold for every assignment. At
`Addrs.fixed` (#156's addresses, `Ptr.convertible_fixed`: #607's `Ptr.convertible`), the
assignment every executable runs, they are the statements before the parameter: these are their
instances, stated with the executables' instance (`open scoped GoFV.SSA.Sem.Fixed`).
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Opt GoFV.Opt.Verified GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (enterListLoc OutcomeRefines)
open scoped GoFV.SSA.Sem.Fixed

/-- `verifiedPipeline_refines` at `Addrs.fixed`. -/
theorem verifiedPipeline_refines_fixed {env : PassEnv} {f : Func} {start : Nat}
    {zv : Array (ID × Nat)} {r : VState} (h : verifiedPipeline env f start zv = .ok r)
    (hv : r.verified = true) :
    VRefines (NilCheck.dictParams env.tables f) (pipelineRo env f)
      (pipelineEq env) r.tables r.func env.tables f :=
  verifiedPipeline_refines h hv

/-- `verifiedPipelineFull_refines` at `Addrs.fixed`. -/
theorem verifiedPipelineFull_refines_fixed {env : PassEnv} {f : Func} {zv : Array (ID × Nat)}
    {dcl : Nat} {r : FState} (h : verifiedPipelineFull env f 0 zv dcl = .ok r)
    (hv : r.fullyVerified = true) {e : Env} {args : List Val} {mem : Mem}
    (hP : VPre (NilCheck.dictParams env.tables f) (pipelineRo env f)
      (pipelineEq env) e args mem)
    (hn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 e args mem)
    (ha : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 e args mem)
    (hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 e args mem) {fuel : Nat}
    (hd : (GoFV.SSA.run e env.tables f args mem fuel).Defined) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e env.tables f args mem fuel)
      (runLoc e r.st.tables r.st.func args mem fuel') :=
  verifiedPipelineFull_refines h hv hP hn ha hnp hd

/-- `verified_mach_ret` at `Addrs.fixed`. -/
theorem verified_mach_ret_fixed
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
    (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      CheckPasses otab.autosize gOff s0)
    (hlf : otab.autosize = 0 ∨ otab.leaf = false)
    (hE : G10Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    {sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc e lc (locInit e lc args mem) (blkE.values.toList.take k) = .ok sI)
    (hent : EntryMatch E0 sI s0) (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI)
    (hpc : ObjEnv.map otab ps L base (E0.pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hRP : RunPre e H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e penv.tables f args mem fuel)
        (runLoc e r.st.tables r.st.func args mem fuel') ∧
      ∃ raw, runLoopLoc e lc fuel' (locInit e lc args mem) lc.ctx.f.entry = raw ∧
        runLoc e r.st.tables r.st.func args mem fuel' =
          finish e lc.ctx.outs lc.ctx.defers lc.ctx.act raw ∧
        raw.Defined ∧
        ∀ rs mm, raw = .returned rs mm →
          ∃ E bF blkF sF sF' t' n, E0.Extends E ∧
            runMach H code (s0.x 30) n s0 = .returned t' ∧ ExitRel E sF s0 t' ∧
            lc.ctx.f.block? bF = some blkF ∧
            stepTermLoc lc sF blkF = .ok (.ret rs mm, sF') :=
  verified_mach_ret hpipe hv hP hn ha hnp hd hlc hc hO hH hic hME hroom hg hpass hlf hE hEE hbE
    hbm hk hpre hent hinv hpc hRP

end GoFV.Proof.Obj
