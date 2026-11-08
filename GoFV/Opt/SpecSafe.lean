import GoFV.SSA.Sem.Run
import GoFV.Opt.Speculate

variable [GoFV.SSA.Sem.Addrs]

/-!
# Ops that are safe to execute speculatively, for the semantics

`specSafeOp op`: the semantics evaluates a value with this op totally from its arguments'
values, without effect and without panicking (`GoFV.Proof.evalValue_specSafe`): not a root
(calls, nil checks, side effects, memory results), not a `Phi`, not a parameter read (`Arg` and
`ArgIntReg` are stuck on a name that is not a parameter). The checked passes that execute values
on paths where the input did not (branchelim, the comparison fusions of early fuse) check it on
the values they speculate; `canSpeculativelyExecute` (`GoFV.Opt.Speculate`) is Go's syntactic
version of the same condition (`specSafe_of_canSpeculativelyExecute`).
-/

namespace GoFV.Opt

open GoFV.SSA

/-- See the module doc. -/
def specSafeOp (op : Op) : Bool :=
  !Sem.isRoot op && op != .Phi && op != .Arg && op != .ArgIntReg

/-- Every listed value of block `b` has a speculation-safe op. -/
def specSafeBlock (f : Func) (b : ID) : Bool :=
  match f.block? b with
  | some x => x.values.all fun id => match f.value? id with
    | some v => specSafeOp v.op
    | none => false
  | none => false

end GoFV.Opt
