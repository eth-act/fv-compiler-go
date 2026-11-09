import GoFV.Gen.Check44
import GoFV.SSA.Sem.TyEq

/-!
# The results of a return in their ABI registers (`docs/plans/proofs3.md` §9)

`retRegsOK lc kt` checks, of the allocated function of `lc` and the class tables `kt` of the genssa
validator (`checkG30`'s), that every `Ret` block returns its register-assigned results in the
registers the ABI gives the function's own results (`f.OwnAux`'s assignments, `ownOutRegs`, as
`callRegs` reads a callee's): its one control is a `MakeResult` whose arguments are those
results, each homed in the next result register (an integer register, `R0`–`R15`, or, at a float
shape, an `F` register, `F0`–`F15`) and holding its class there before the terminator (`kAt`),
then the memory (no home). A result the ABI puts on the
stack (or a zero-sized one) has no register and no `MakeResult` argument: `expand calls` stores it
to its `PPARAMOUT` variable (`rewriteFuncResults`), where `goResults` reads it from the memory at
the return. The `MakeResult`'s type is a tuple of as many
shapes (`expand calls` gives it the results' register types, `abi.RegisterTypes`, which need not
be the arguments' own: a pointer of another element type, a `uintptr` itab word for a `*itab`),
each of a class no wider than its argument's (`retypeL` then keeps the register's relation,
`valRel_retypeL_le`), the memory's last.
`GoFV/Proof/Obj/Results.lean` proves what it gives (`ret_results`, `ret_resultsP` in Phase 1's
mode): `runLoc`'s returned values are the contents of those registers, related to the machine's
(`ResultRel`); the stack results are in the returned memory, which `ResultRel` injects into the
machine's.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem

/-- The Go registers of the function's own register-assigned results by its ABI (`abiParams`:
`f.OwnAux`'s assignments), in order; a result on the stack has none. -/
def ownOutRegs (lc : LocCtx) : List Nat :=
  ((abiParams lc.ctx.tabs lc.ctx.f).toList.filter (·.out)).flatMap (·.regs.toList.map abiReg)

/-- A result `a` at component shape `t` in register `r` with the class map `K` before the
terminator: homed in `r`, of a class `c` that `K` gives `r`; in an integer register (`R0`–`R15`)
read at a shape of a class no wider, or in an `F` register (`F0`–`F15`, Go registers 31–46) at
a float shape (`fTy`) read at a float shape of its class. -/
def retArgOK (lc : LocCtx) (K : KMap) (a : ID) (t : Ty) (r : Nat) : Bool :=
  lc.home a == some (.reg r) &&
    match cls (lc.ty a), cls t with
    | some c, some c' =>
      K.get r == some c &&
        ((decide (r < 16) && decide (c' ≤ c)) ||
          (decide (31 ≤ r) && decide (r < 47) && fTy (lc.ty a) && fTy t && c' == c))
    | _, _ => false

/-- The return of `blk` (ID `bid`) puts its results in `outs` (see the module comment): the
`MakeResult` control with arguments `args` and component shapes `ts`, `n + 1` of each for `n`
results. -/
def retArgsOK (lc : LocCtx) (kt : KTab) (outs : List Nat) (bid : ID) (blk : Block)
    (args : List ID) (ts : List Ty) : Bool :=
  let K := kAt lc kt bid blk blk.values.size
  args.length == outs.length + 1 && ts.length == args.length &&
    (match args.getLast?, ts.getLast? with
     | some a, some t => memTy (lc.ty a) && memTy t && lc.home a == none
     | _, _ => false) &&
    ((args.zip ts).zip outs).all fun ((a, t), r) => retArgOK lc K a t r

/-- A `Ret` block returns its results in `outs`; any other block is accepted. -/
def retBlockOK (lc : LocCtx) (kt : KTab) (outs : List Nat) (bid : ID) (blk : Block) : Bool :=
  blk.kind != .Ret ||
    match blk.controls.toList with
    | [c] =>
      match lc.ctx.f.value? c, lc.ty c with
      | some v, .tuple ts => v.op == .MakeResult && retArgsOK lc kt outs bid blk v.args.toList ts
      | _, _ => false
    | _ => false

/-- Every `Ret` block of the function returns its register-assigned results in their ABI
registers. -/
def retRegsOK (lc : LocCtx) (kt : KTab) : Bool :=
  lc.ctx.f.blocks.toList.all fun bid =>
    match lc.ctx.f.block? bid with
    | some blk => retBlockOK lc kt (ownOutRegs lc) bid blk
    | none => true

end GoFV.Gen.Check
