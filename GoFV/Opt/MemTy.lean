import GoFV.SSA.Sem.Run

variable [GoFV.SSA.Sem.Addrs]

/-!
# Values whose shape may hold a memory (issues #36, #151)

`memTyOK tabs f`: every listed value of `f` whose shape may hold a memory (`memFree`) is a memory
op (`memOpOK`: memory roots, calls, atomics, tuple ops) or an op whose results hold none
(`memFreeOps`: integer ops with tuple results, tail calls), and `f` has none of the write-barrier
ops. Then every memory a run of `f` holds is built by the memory ops (`GoFV.Proof.MemInv`): the
writebarrier checker (`WBCheck.wbOK`) and the segment layer's read-only `Move`s
(`RewriteCheck.roSegsOK`) ask it.
-/

namespace GoFV.Opt.WBCheck

open GoFV.SSA

/-- The values of block `b` of `h`. -/
@[inline] def vals (h : Func) (b : ID) : Array ID := ((h.block? b).map (·.values)).getD #[]

/-- The symbol name an `Addr`'s aux names. -/
def symName? (tabs : Tables) (aux : Option AuxRef) : Option String :=
  match aux.bind tabs.aux? with
  | some { kind := .sym name .., .. } => some name.toStringLossy
  | _ => none

/-- A shape that holds no memory (and no tuple, which may carry one). -/
def memFree : Sem.Ty → Bool
  | .mem | .tuple _ => false
  | .agg fs _ => memFreeFields fs
  | _ => true
where
  memFreeFields : List (Nat × Sem.Ty) → Bool
    | [] => true
    | (_, t) :: fs => memFree t && memFreeFields fs

/-- The ops of `f` whose values may hold memories: memory roots, calls, atomics, tuple ops. -/
def memOps : List Op :=
  [.InitMem, .Phi, .Copy, .Select0, .Select1, .SelectN, .MakeResult,
   .Store, .Move, .Zero, .VarDef, .VarLive, .KeepAlive, .PanicBounds,
   .StaticCall, .ClosureCall, .InterCall, .StaticLECall, .ClosureLECall, .InterLECall,
   .AtomicLoad8, .AtomicLoad32, .AtomicLoad64, .AtomicLoadPtr, .AtomicLoadAcq32,
   .AtomicLoadAcq64]

/-- The atomic roots (`atomicRoot`) whose values may hold memories. -/
def atomicRootOps : List Op :=
  [.AtomicStore8, .AtomicStore32, .AtomicStore64, .AtomicStorePtrNoWB, .AtomicStoreRel32,
   .AtomicStoreRel64, .AtomicExchange8, .AtomicExchange32, .AtomicExchange64, .AtomicAdd32,
   .AtomicAdd64, .AtomicCompareAndSwap32, .AtomicCompareAndSwap64, .AtomicCompareAndSwapRel32,
   .AtomicAnd8, .AtomicOr8, .AtomicAnd32, .AtomicOr32, .AtomicAnd64value, .AtomicAnd32value,
   .AtomicAnd8value, .AtomicOr64value, .AtomicOr32value, .AtomicOr8value,
   .AtomicStore8Variant, .AtomicStore32Variant, .AtomicStore64Variant, .AtomicAdd32Variant,
   .AtomicAdd64Variant, .AtomicExchange8Variant, .AtomicExchange32Variant,
   .AtomicExchange64Variant, .AtomicCompareAndSwap32Variant, .AtomicCompareAndSwap64Variant,
   .AtomicAnd64valueVariant, .AtomicOr64valueVariant, .AtomicAnd32valueVariant,
   .AtomicOr32valueVariant, .AtomicAnd8valueVariant, .AtomicOr8valueVariant, .PubBarrier,
   .PrefetchCache, .PrefetchCacheStreamed]

@[inline] def memOpOK (op : Op) : Bool := memOps.contains op || atomicRootOps.contains op

/-- Ops of tuple type whose results hold no memory: integer ops with results of integers and
booleans, and tail calls (`TailLECall*`, which the semantics never completes: `stuck`). -/
def memFreeOps : List Op :=
  [.Mul32uhilo, .Mul64uhilo, .Mul32uover, .Mul64uover, .Add64carry, .Sub64borrow, .Div128u,
   .TailLECall, .TailLECallInter]

/-- Every listed value of `f` whose shape may hold a memory is a memory op or of `memFreeOps`,
and `f` has none of the write-barrier ops. -/
def memTyOK (tabs : Tables) (f : Func) : Bool :=
  f.blocks.all fun b => (vals f b).all fun x =>
    match f.value? x with
    | some v =>
      v.op != .WB && v.op != .WBend && v.op != .StoreWB && v.op != .MoveWB &&
        v.op != .ZeroWB && (memFree (tabs.ty v.type) || memOpOK v.op || memFreeOps.contains v.op)
    | none => false

end GoFV.Opt.WBCheck
