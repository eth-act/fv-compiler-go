import GoFV.Opt.TabsAgree
import GoFV.Opt.DeadAutosCheck

variable [GoFV.SSA.Sem.Addrs]

/-!
# Extended tables with extra frame temporaries (`tabsAgreeMod`)

`decompose user` and `decompose builtin` add the `PAUTO` names of the pieces they split a
variable into to the definition tables. `Sem.frameLocals` allocates a frame block for every
frame variable the tables define, so running the source `f` in the output tables `tabs'` has a
frame with extra blocks, and `tabsAgree tabs tabs' f` (same frame) fails.
`tabsAgreeMod tabs tabs' f` allows exactly that: the frame variables of `tabs'` are those of
`tabs` plus names `tabs` does not define, each non-forgeable (a `Blk.temp` block, which no
integer converts to and no value of `f` names). The source never points into those blocks, so
its run in `tabs'` has the same outcomes, for inputs that hold no pointer into a frame
temporary and contracts that cannot tell whether temporaries they have no pointer to exist
(`GoFV.Proof.run_tabsAgreeMod`).

The proof is a lock-step simulation whose memories differ by the extra blocks; like `dead auto
elim`'s (`DAE.opOK`) it covers every value whose memory- or tuple-shaped arguments come last for
the ops it handles (`tamMemOps`), and whose result shape may hold a pointer only for the ops
whose results it shows avoid the extra blocks (`tamPtrOps`).
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Sem

/-- The ops `Sem.evalOp` evaluates by name (every other op is a frame value, `stuck` if it is a
root, or `evalPure`). -/
def evalOpArms : List Op :=
  [.InitMem, .Arg, .ArgIntReg, .ArgFloatReg, .PanicBounds, .StaticLECall, .StaticCall,
    .ClosureLECall, .ClosureCall, .InterLECall, .InterCall, .GetClosurePtr, .Store, .StoreWB,
    .Move, .MoveWB, .Zero, .ZeroWB, .VarDef, .VarLive, .KeepAlive, .WBend, .NilCheck, .SP,
    .GetCallerSP, .LocalAddr, .Addr, .ConstString]

/-- A root `Sem.evalOp` does not evaluate by name: `Sem.atomicRoot` (the P5 atomics, barriers and
prefetches; `stuck` for the others). Its memory argument comes last and its result is a memory or a
(value, memory) pair (`GoFV.Proof.atomicRoot_sim`). -/
def atomicRootOp (op : Op) : Bool := isRoot op && !evalOpArms.contains op

/-- A root `Sem.evalOp` does not evaluate: always `stuck` (tail calls, the ops `atomicRoot`
does not model). -/
def stuckRoot (op : Op) : Bool :=
  isRoot op && !evalOpArms.contains op && !Sem.Atomic.modelled op

/-- Ops whose last argument may be memory- or tuple-shaped (`DAE.memOps`, the pre-`expand calls`
calls, the other loads, tuple ops). -/
def tamMemOps : List Op :=
  DAE.memOps ++ [.StaticLECall, .InterLECall, .ClosureLECall,
    .Dereference, .AtomicLoad8, .AtomicLoadAcq32, .AtomicLoadAcq64, .SelectNAddr, .MakeTuple]

/-- Ops whose pointer-, blob- or memory-shaped results the proof handles. -/
def tamPtrOps : List Op :=
  DAE.ptrOps ++ [.StaticLECall, .InterLECall, .ClosureLECall,
    .Dereference, .AtomicLoad8, .AtomicLoadAcq32, .AtomicLoadAcq64, .SelectNAddr, .MakeTuple,
    .StringMake, .SliceMake, .IMake, .ComplexMake, .StructMake, .ArrayMake1, .StringPtr,
    .SlicePtr, .SlicePtrUnchecked, .ITab, .IData, .StructSelect, .ArraySelect, .ConstSlice,
    .ConstInterface, .ConstString, .SP, .Mul32uhilo, .Mul32uover, .Mul64uhilo, .Mul64uover,
    .Div128u, .Add64carry, .Sub64borrow, .Invalid]

/-- Value `fv` of `f`: a memory- or tuple-shaped argument only last and only for `tamMemOps` or an
`atomicRootOp` (any for a `Phi` or a `stuckRoot`), a result shape that may hold a pointer only for
`tamPtrOps` or an `atomicRootOp` (or a `stuckRoot`). -/
def tamOpOK (tabs : Tables) (f : Func) (fv : Value) : Bool :=
  stuckRoot fv.op ||
  (fv.op == .Phi || fv.args.all (DAE.plainArg tabs f) ||
      ((tamMemOps.contains fv.op || atomicRootOp fv.op) &&
        fv.args.pop.all (DAE.plainArg tabs f))) &&
    (tamPtrOps.contains fv.op || atomicRootOp fv.op || DAE.noPtrTy (tabs.ty fv.type))

/-- `tabsAgree` up to extra frame temporaries (see the module comment): the frame variables of
`tabs'` that `tabs` defines are `tabs`' frame variables, every other one is not forgeable, the
open-coded defer variables are the same (`deferInfo`), and every value of `f` is in the ops the
proof covers (`tamOpOK`). Every other conjunct is
`tabsAgree`'s. -/
def tabsAgreeMod (tabs tabs' : Tables) (f : Func) : Bool :=
  let ps := abiParams tabs f
  let params := (ps.filter (!·.out)).map (·.name)
  let ls := frameLocals tabs params
  let ls' := frameLocals tabs' params
  let sh := typeShapes tabs
  let sh' := typeShapes tabs'
  decide ((abiParams tabs' f).toList = ps.toList) &&
  decide (deferInfo tabs' = deferInfo tabs) &&
  ps.toList.all (fun p => Ty.beq (tabs'.ty p.type) (tabs.ty p.type)) &&
  decide (ls'.toList.filter (fun l => (tabs.aux? l.1).isSome) = ls.toList) &&
  ls'.toList.all (fun l => (tabs.aux? l.1).isSome || !tabs'.forgeable l.1) &&
  ls.toList.all (fun l => tabs'.forgeable l.1 == tabs.forgeable l.1) &&
  outargsSize tabs' == outargsSize tabs &&
  f.valueTab.toList.all (fun o => Ty.beq (valueTy sh' o) (valueTy sh o) && valueAuxAgree tabs tabs' o) &&
  f.valueTab.toList.all fun o => match o with
    | some fv => tamOpOK tabs f fv
    | none => true

end GoFV.Opt
