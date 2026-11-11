import GoFV.Proof.Obj.EndToEnd
import GoFV.Proof.Gen.G49Mach

/-!
# The end-to-end theorem at the machine layout (`docs/plans/proofs3.md` §8 items 4 and 6, #553)

`verified_mach` holds under every address assignment, and its activation premise `G49Env` puts
the `Blk.local` block of every accessed frame variable at `SP + frameOff`. At `Addrs.fixed`, which
spaces those blocks `2^24` apart, no activation of a function that accesses two of them at distinct
operands is a `G49Env` (`g49Env_fixed_apart`), so there `verified_mach` holds of such a function
only vacuously. `verified_mach_atSP` states it at `Addrs.atSP (baseSP g L E0.sp)`, where activation
0's `local` blocks sit, undecoded, at their frame operands from `SP`: the activation is
`envAtSP g L E0`, and `G49Env` is no premise, it follows (`g49Env_atSP`) from the activation
without the variables' places at `Addrs.fixed` (`G28Env`), which constrains no frame variable.
In G48's mode (`verified_mach_S`) `SPInv` pins `SP` to the `outargs` block's fixed base at
`Addrs.fixed`, so a function that accesses any `local` variable has no `G49Env` there
(`g49Env_fixed_outSP`); `verified_mach_S_atSP` states `verified_mach_S` at
`Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat`, with activation 0's `outargs` block at `SP` too
(`envAtSPO g L E0`).
The checked premises (`verifiedPipelineFull`, `checkG64`, `needs48`, `retRegsOK`, `entryStoresOK`,
`memTyL`, `checkObj`'s `ObjEnv`) take no address assignment (§8 item 6,
`GoFVTest/AddrsFree.lean`): they are the verdicts `gofv-ssa-opt --e2e` computes. The others
(the input's `VPre`, the caller's entry relation, the callee contracts) are stated at the
machine layout.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen GoFV.Opt GoFV.Opt.Verified GoFV.Proof.Pipeline GoFV.Proof.PipelineFull
open GoFV.Proof (enterListLoc OutcomeRefines)

/-- The pipeline's `runLoc` context is that of activation 0. -/
theorem liveCtx_make_act (tabs : Tables) (f : Func) :
    (liveCtx (LocCtx.make tabs f)).ctx.act = 0 := by
  simp only [liveCtx, LocCtx.make, Ctx.makeL]
  split <;> rfl

/-- **Generic SSA to machine words at the machine layout.** `verified_mach` at the address
assignment `A = Addrs.atSP (baseSP g L E0.sp)` (activation 0's `local` blocks at their frame
operands from `E0.sp`, undecoded; every other block as at `Addrs.fixed`), for the activation
`envAtSP g L E0`, with the premise `G49Env` replaced by `G28Env` of `E0` at `Addrs.fixed` (no
place of a frame variable asked; `g49Env_atSP`). Every other premise is `verified_mach`'s: the
checks as `gofv-ssa-opt --e2e` computes them, the rest at `A`. -/
theorem verified_mach_atSP
    {g : G2In} {L : Link} {E0 : MatchEnv} [A : Addrs] (hA : A = Addrs.atSP (baseSP g L E0.sp))
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
    {H : Hooks} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    {kt : KTab} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64} {code : Code} {room : Nat} {s0 : MState}
    (hc : checkG64 (LocCtx.make r.st.tables r.st.func) ps bstart g = .ok (tab, kt))
    (hn48 : needs48 lc = false)
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
    (hE : @G28Env Addrs.fixed lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv (envAtSP g L E0) L ps.toList otab.autosize s0)
    {sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc e lc (locInit e lc args mem) (blkE.values.toList.take k) = .ok sI)
    (hes : entryStoresOK lc g k = true) (hargs : argsOK lc g spills.toList k = true)
    (hent : EntryMatch (envAtSP g L E0) g (InWins L E0.sp (pendWins lc g)) sI s0)
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry (envAtSP g L E0) spills.toList gOff sI s0)
    (hinv : G3Inv (envAtSP g L E0) lc (kAt lc kt lc.ctx.f.entry blkE k) sI)
    (huE : uL35 lc [] blkE k = [])
    (hpc : ObjEnv.map otab ps L base ((envAtSP g L E0).pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hRP : RunPre e H lc g L (endP L.text ps.toList) (envAtSP g L E0) lc.ctx.f.entry k sI)
    (hmt : constRo (symNames g) ≠ [] → memTyL lc = true)
    (hro : RoMem (constRo (symNames g)) (addGlobals e mem)) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e penv.tables f args mem fuel)
        (runLoc e r.st.tables r.st.func args mem fuel') ∧
      ∃ raw, runLoopLoc e lc fuel' (locInit e lc args mem) lc.ctx.f.entry = raw ∧
        runLoc e r.st.tables r.st.func args mem fuel' =
          finish e lc.ctx.outs lc.ctx.defers lc.ctx.act raw ∧
        raw.Defined ∧
      (∀ rs mm, raw = .returned rs mm →
        ∃ E t' n, (envAtSP g L E0).Extends E ∧ runMach H code (s0.x 30) n s0 = .returned t' ∧
          MachRet s0 t' ∧ ResultRel E (ownOutRegs lc) rs mm t') ∧
      (∀ pe mm, raw = .panicked pe mm → HookPanicMap H L ps.toList (ObjEnv.map otab ps L base) →
        BoundsOK H g L ps.toList →
        RunPanicPre e H lc g L (endP L.text ps.toList) (envAtSP g L E0) lc.ctx.f.entry k sI →
        ∃ pe' n t', BoundsAgree pe pe' ∧ runMach H code (s0.x 30) n s0 = .panicked pe' t') := by
  subst hA
  have hact : lc.ctx.act = 0 := hlc ▸ liveCtx_make_act _ _
  letI : Addrs := Addrs.atSP (baseSP g L E0.sp)
  exact verified_mach hpipe hv hP hn ha hnp hd hlc hc hn48 hO hH hic hrok hME hroom hg hms hsep
    (g49Env_atSP hE hact) hEE hbE hbm hk hpre hes hargs hent hmore hinv huE hpc hRP hmt hro

/-- **Generic SSA to machine words at the machine layout, in G48's mode.** `verified_mach_S` at
the address assignment `A = Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat` (activation 0's `local`
blocks at their frame operands from `E0.sp` and its `outargs` block at `E0.sp`, undecoded; every
other block as at `Addrs.fixed`), for the activation `envAtSPO g L E0`, with the premise `G49Env`
replaced by `G28Env` of `E0` at `Addrs.fixed` (no place of a frame variable asked;
`g49Env_atSPO`). Every other premise is `verified_mach_S`'s: the checks as
`gofv-ssa-opt --e2e` computes them, the rest at `A`. -/
theorem verified_mach_S_atSP
    {g : G2In} {L : Link} {E0 : MatchEnv} [A : Addrs]
    (hA : A = Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat)
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
    {H : Hooks} {ps : Array Prog} {bstart : ID → Option Nat} {tab : PcTab}
    {kt : KTab} {spills : Array Spill} {o : ObjIn} {otab : Tab}
    {base : BitVec 64} {code : Code} {room : Nat} {s0 : MState}
    (hc : checkG64 (LocCtx.make r.st.tables r.st.func) ps bstart g = .ok (tab, kt))
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
    (hE : @G28Env Addrs.fixed lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv (envAtSPO g L E0) L ps.toList otab.autosize s0)
    {sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc e lc (locInit e lc args mem) (blkE.values.toList.take k) = .ok sI)
    (hes : entryStoresOK lc g k = true) (hargs : argsOK lc g spills.toList k = true)
    (hent : EntryMatch (envAtSPO g L E0) g (InWins L E0.sp (pendWins lc g)) sI s0)
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry (envAtSPO g L E0) spills.toList gOff sI s0)
    (hinv : G3Inv (envAtSPO g L E0) lc (kAt lc kt lc.ctx.f.entry blkE k) sI true)
    (hosp : E0.outSP = true)
    (hspI : lc.ctx.f.lowered = true → SPInv (envAtSPO g L E0) sI)
    (huE : uL35 lc [] blkE k = [])
    (hpc : ObjEnv.map otab ps L base ((envAtSPO g L E0).pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hRP : RunPreS e H lc g L (endP L.text ps.toList) (envAtSPO g L E0) lc.ctx.f.entry k sI)
    (hmt : constRo (symNames g) ≠ [] → memTyL lc = true)
    (hro : RoMem (constRo (symNames g)) (addGlobals e mem)) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e penv.tables f args mem fuel)
        (runLoc e r.st.tables r.st.func args mem fuel') ∧
      ∃ raw, runLoopLoc e lc fuel' (locInit e lc args mem) lc.ctx.f.entry = raw ∧
        runLoc e r.st.tables r.st.func args mem fuel' =
          finish e lc.ctx.outs lc.ctx.defers lc.ctx.act raw ∧
        raw.Defined ∧
      (∀ rs mm, raw = .returned rs mm →
        ∃ E t' n, (envAtSPO g L E0).Extends E ∧ runMach H code (s0.x 30) n s0 = .returned t' ∧
          MachRet s0 t' ∧ ResultRel E (ownOutRegs lc) rs mm t') ∧
      (∀ pe mm, raw = .panicked pe mm → HookPanicMap H L ps.toList (ObjEnv.map otab ps L base) →
        BoundsOK H g L ps.toList →
        RunPanicPreS e H lc g L (endP L.text ps.toList) (envAtSPO g L E0) lc.ctx.f.entry k sI →
        ∃ pe' n t', BoundsAgree pe pe' ∧ runMach H code (s0.x 30) n s0 = .panicked pe' t') := by
  subst hA
  have hact : lc.ctx.act = 0 := hlc ▸ liveCtx_make_act _ _
  letI : Addrs := Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat
  exact verified_mach_S hpipe hv hP hn ha hnp hd hlc hc hO hH hic hrok hME hroom hg hms hsep
    (g49Env_atSPO hE hact) hEE hbE hbm hk hpre hes hargs hent hmore hinv hosp hspI huE hpc hRP
    hmt hro


end GoFV.Proof.Obj
