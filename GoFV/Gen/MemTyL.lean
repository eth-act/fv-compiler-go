import GoFV.Opt.MemTy
import GoFV.SSA.Sem.RunLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# Values of an allocated function whose shape may hold a memory (`docs/plans/proofs3.md` §10)

`memTyL lc`: every value of `lc`'s function whose shape (`LocCtx.ty`) may hold a memory
(`WBCheck.memFree`) has an op whose result's memories are built from its arguments' and the
activation's (`memOpL`): Phase 1's memory ops (`WBCheck.memOpOK`)
and tuple ops without memories (`WBCheck.memFreeOps`), and the arm64 memory ops (`arm64MemOps`:
stores, pair loads, calls, nil checks, barriers, atomics, `LDAR*`, the bulk ops, `LoweredWB`, the
bounds panics). A value of any other shape holds no memory once `runLoc` shapes it; `LoadReg`
and `StoreReg` copy their argument. Then every
memory `runLoc` holds is built by writes, the write-barrier buffer, and contracts
(`GoFV/Proof/Obj/RoLoc.lean`), so the read-only allocations of the initial memory stay
(`RoMem`). The driver checks it as it checks `entryStoresOK`.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.WBCheck

/-- The arm64 ops whose values may hold memories. -/
def arm64MemOps : List Op :=
  [.ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore, .ARM64FMOVSstore,
   .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD, .ARM64FSTPS,
   .ARM64FSTPQ, .ARM64MOVBstoreidx, .ARM64MOVHstoreidx, .ARM64MOVWstoreidx, .ARM64MOVDstoreidx,
   .ARM64FMOVSstoreidx, .ARM64FMOVDstoreidx, .ARM64MOVHstoreidx2, .ARM64MOVWstoreidx4,
   .ARM64MOVDstoreidx8, .ARM64FMOVSstoreidx4, .ARM64FMOVDstoreidx8,
   .ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64FLDPD, .ARM64FLDPS, .ARM64FLDPQ,
   .ARM64CALLstatic, .ARM64CALLclosure, .ARM64CALLinter, .ARM64LoweredNilCheck,
   .ARM64LoweredPanicBoundsRR, .ARM64LoweredPanicBoundsRC, .ARM64LoweredPanicBoundsCR,
   .ARM64LoweredPanicBoundsCC, .ARM64DMB, .ARM64PRFM,
   .ARM64STLRB, .ARM64STLRW, .ARM64STLR, .ARM64LoweredAtomicExchange8,
   .ARM64LoweredAtomicExchange32, .ARM64LoweredAtomicExchange64,
   .ARM64LoweredAtomicExchange8Variant, .ARM64LoweredAtomicExchange32Variant,
   .ARM64LoweredAtomicExchange64Variant, .ARM64LoweredAtomicAdd32, .ARM64LoweredAtomicAdd64,
   .ARM64LoweredAtomicAdd32Variant, .ARM64LoweredAtomicAdd64Variant,
   .ARM64LoweredAtomicCas32, .ARM64LoweredAtomicCas64, .ARM64LoweredAtomicCas32Variant,
   .ARM64LoweredAtomicCas64Variant, .ARM64LoweredAtomicAnd8, .ARM64LoweredAtomicAnd32,
   .ARM64LoweredAtomicAnd64, .ARM64LoweredAtomicOr8, .ARM64LoweredAtomicOr32,
   .ARM64LoweredAtomicOr64, .ARM64LoweredAtomicAnd8Variant, .ARM64LoweredAtomicAnd32Variant,
   .ARM64LoweredAtomicAnd64Variant, .ARM64LoweredAtomicOr8Variant,
   .ARM64LoweredAtomicOr32Variant, .ARM64LoweredAtomicOr64Variant,
   .ARM64LDAR, .ARM64LDARB, .ARM64LDARW,
   .ARM64LoweredZero, .ARM64LoweredZeroLoop, .ARM64LoweredMove, .ARM64LoweredMoveLoop,
   .ARM64LoweredWB]

/-- The ops of an allocated function whose values may hold memories. -/
def memOpL (op : Op) : Bool :=
  memOpOK op || memFreeOps.contains op || arm64MemOps.contains op

/-- Every value of `lc`'s function whose shape may hold a memory has an op of `memOpL`. -/
def memTyL (lc : LocCtx) : Bool :=
  lc.ctx.f.valueTab.all fun
    | some v => memFree (lc.ty v.id) || memOpL v.op
    | none => true

/-- The first value `memTyL` rejects: its ID, op and shape. -/
def memTyLWhy (lc : LocCtx) : String :=
  match lc.ctx.f.valueTab.toList.findSome? (fun
      | some v => if memFree (lc.ty v.id) || memOpL v.op then none else some v
      | none => none) with
  | some v => s!"memTyL: v{v.id} {v.op.name} of shape {repr (lc.ty v.id)}"
  | none => "memTyL: ok"

end GoFV.Gen.Check
