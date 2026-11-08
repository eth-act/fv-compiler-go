import GoFV.Gen.Check3
import GoFV.SSA.Sem.TyEq

/-!
# The results of a return in their ABI registers (`docs/plans/proofs3.md` §9)

`retRegsOK lc kt` checks, of the allocated function of `lc` and the class tables `kt` of the genssa
validator (`checkG18`'s), that every `Ret` block returns its results in the registers the ABI
gives the function's own results (`f.OwnAux`'s assignments, `ownOutRegs`, as `callRegs` reads a
callee's): its one control is a `MakeResult` of shape `tuple (args.map lc.ty)` whose arguments are
the results, each homed in the next result register (an integer register, `R0`–`R15`) and
holding its class there before the terminator (`kAt`), then the memory (no home).
`GoFV/Proof/Obj/Results.lean` proves what it gives (`ret_results`): `runLoc`'s returned values
are the contents of those registers, related to the machine's (`ResultRel`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem

/-- The Go registers of the function's own results by its ABI (`abiParams`: `f.OwnAux`'s
assignments), in order; `none` if a result is on the stack. -/
def ownOutRegs (lc : LocCtx) : Option (List Nat) :=
  let outs := (abiParams lc.ctx.tabs lc.ctx.f).toList.filter (·.out)
  if outs.all (!·.regs.isEmpty) then some (outs.flatMap (·.regs.toList.map abiReg)) else none

/-- The return of `blk` (ID `bid`) puts its results in `outs` (see the module comment): the
`MakeResult` control `c` with arguments `args`, `n + 1` of them for `n` results. -/
def retArgsOK (lc : LocCtx) (kt : KTab) (outs : List Nat) (bid : ID) (blk : Block)
    (args : List ID) : Bool :=
  let K := kAt lc kt bid blk blk.values.size
  args.length == outs.length + 1 &&
    (match args.getLast? with
     | some a => memTy (lc.ty a) && lc.home a == none
     | none => false) &&
    (args.zip outs).all fun (a, r) =>
      lc.home a == some (.reg r) && decide (r < 16) && (cls (lc.ty a)).isSome &&
        K.get r == cls (lc.ty a)

/-- A `Ret` block returns its results in `outs`; any other block is accepted. -/
def retBlockOK (lc : LocCtx) (kt : KTab) (outs : List Nat) (bid : ID) (blk : Block) : Bool :=
  blk.kind != .Ret ||
    match blk.controls.toList with
    | [c] =>
      match lc.ctx.f.value? c with
      | some v =>
        v.op == .MakeResult && Ty.beq (lc.ty c) (.tuple (v.args.toList.map lc.ty)) &&
          retArgsOK lc kt outs bid blk v.args.toList
      | none => false
    | _ => false

/-- Every `Ret` block of the function returns its results in their ABI registers. -/
def retRegsOK (lc : LocCtx) (kt : KTab) : Bool :=
  match ownOutRegs lc with
  | none => false
  | some outs =>
    lc.ctx.f.blocks.toList.all fun bid =>
      match lc.ctx.f.block? bid with
      | some blk => retBlockOK lc kt outs bid blk
      | none => true

end GoFV.Gen.Check
