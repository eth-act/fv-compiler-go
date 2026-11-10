import GoFV.Gen.Entry49

variable [GoFV.SSA.Sem.Addrs]

/-!
# The incoming stack arguments at the entry (`docs/plans/proofs3.md` §9)

G62's `Arg` of a parameter the ABI assigns to the stack (`GoFV/Gen/Check62.lean`) emits no code:
`runLoc` writes the argument's piece to the slot of its `NAME_PARAM` operand `x+off(FP)`, where
the caller stored it before the `CALL` (ABI0: `8 + offset` above the callee's entry `SP`). The
end-to-end theorem runs the `Arg`s at the head of the entry block with the entry values
(`entryLen`, before value `k`) and relates their slots at the entry from the caller's side
(`EntryMatch.stack`), so no `Arg` is a step of the simulation and `ArgOK`, `g62_value`'s premise,
holds vacuously at every state it reaches.

`argsOK lc g spills k`, a premise of the end-to-end theorem checked by the driver:
* `argsBefore lc k`: every `Arg` of the function sits in the entry block before value `k`, and
  no edge goes to the entry block (so no `Arg` runs after `k`);
* a function with an `Arg` has no pending window of a register-assigned parameter (`pendWins`)
  and no morestack spill (`spills`: the morestack tail spills the register arguments only), so its
  slots lie outside the bytes `EntryMatch` leaves out and the tail writes.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- Every `Arg` of the function sits in the entry block before value `k`, and no edge goes to the
entry block. -/
def argsBefore (lc : LocCtx) (k : Nat) : Bool :=
  (List.range lc.ctx.f.blockTab.size).all fun b =>
    match lc.ctx.f.block? b with
    | none => true
    | some blk =>
      blk.succs.all (·.b != lc.ctx.f.entry) &&
        (List.range blk.values.size).all fun i =>
          (b == lc.ctx.f.entry && decide (i < k)) ||
            (blk.values[i]?.bind lc.ctx.f.value?).all (·.op != .Arg)

/-- The function has no `Arg`. -/
def noArg (lc : LocCtx) : Bool :=
  (List.range lc.ctx.f.valueTab.size).all fun i => (lc.ctx.f.value? i).all (·.op != .Arg)

/-- The checks of the incoming stack arguments at the entry (module doc). -/
def argsOK (lc : LocCtx) (g : G2In) (spills : List Spill) (k : Nat) : Bool :=
  argsBefore lc k && (noArg lc || ((pendWins lc g).isEmpty && spills.isEmpty))

end GoFV.Gen.Check
