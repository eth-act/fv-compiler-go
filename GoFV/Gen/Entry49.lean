import GoFV.Gen.Check49

variable [GoFV.SSA.Sem.Addrs]

/-!
# The entry stores of the register-assigned parameters (`docs/plans/proofs3.md` §8 item 8, §9)

Phase 1 initialises the `Blk.local` block of every `PPARAM` with its argument's image
(`frameAllocs`). A parameter the ABI assigns to registers has its block at its `NAME_PARAM`
operand in the caller's spill area (G49, `VarsAt49`), which holds whatever the caller left there
until genssa's entry stores (`MOVD R1, x+8(FP)`, `STP (R0, R1), x+0(FP)`) put the argument's
registers there. So the relation at the function's entry (`EntryMatch`) leaves those windows
out (`pendWins`: the windows of the register-assigned parameters the function accesses), and the
whole-function simulation runs the entry stores (`entryStores`: the stores of registers to frame
variables at their `NAME_PARAM` operands that only G49's frame-variable path accepts, from value
`k` of the entry block, as long as they last) before it relates the memory in full.

`entryStoresOK lc g k`: the entry stores from value `k` cover every byte of every pending
window. It is a premise of the end-to-end theorem, checked by the driver.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- An entry store: a store to a frame variable in a `Blk.local` block at its `NAME_PARAM`
operand that `vkind51` rejects (so `vkind49` accepts it through `vkindVar49`, if at all): its
operand offset and its width in bytes (`MOV{D,W,H,B}store`'s, or 16 for `STP`). -/
def entryStore? (lc : LocCtx) (g : G2In) (v : Value) : Option (Int × Nat) :=
  match vkind51 lc g v with
  | .ok _ => none
  | .error _ =>
    match frameVar49? lc g v with
    | some (_, .PARAM, off) =>
      match storeOp? v.op with
      | some (_, n) => some (off, n)
      | none => if v.op == .ARM64STP then some (off, 16) else none
    | _ => none

/-- The entry stores at the head of `ids`, as long as they last. -/
def storesFrom (lc : LocCtx) (g : G2In) : List ID → List (Int × Nat)
  | [] => []
  | id :: ids =>
    match (lc.ctx.f.value? id).bind (entryStore? lc g) with
    | some w => w :: storesFrom lc g ids
    | none => []

/-- The entry stores from value `k` of the entry block. -/
def entryStores (lc : LocCtx) (g : G2In) (k : Nat) : List (Int × Nat) :=
  match lc.ctx.f.block? lc.ctx.f.entry with
  | some blk => storesFrom lc g (blk.values.toList.drop k)
  | none => []

/-- A parameter (not a result) the function's ABI assigns to registers. -/
def regParam (lc : LocCtx) (x : AuxRef) : Bool :=
  (abiParams lc.ctx.tabs lc.ctx.f).any fun p => !p.out && p.name == some x && !p.regs.isEmpty

/-- The pending windows: the `NAME_PARAM` windows (operand offset, size) of the
register-assigned parameters in `Blk.local` blocks the function accesses. -/
def pendWins (lc : LocCtx) (g : G2In) : List (Int × Nat) :=
  (accessedVars lc).filterMap fun x =>
    if lc.ctx.tabs.forgeable x && regParam lc x then
      match varWin49 lc g x with
      | some (.PARAM, lo, hi) => some (lo, (hi - lo).toNat)
      | _ => none
    else none

/-- Byte `o` of the `NAME_PARAM` operands is in one of the windows `ws`. -/
def inWins (ws : List (Int × Nat)) (o : Int) : Bool :=
  ws.any fun (o', n) => o' ≤ o && o < o' + n

/-- The entry stores from value `k` cover every byte of every pending window. -/
def entryStoresOK (lc : LocCtx) (g : G2In) (k : Nat) : Bool :=
  let st := entryStores lc g k
  (pendWins lc g).all fun (o, n) => (List.range n).all fun j => inWins st (o + j)

/-- The number of values at the head of the entry block that set up the activation, in any order:
the entry values (`entryOp`: the arguments in registers, `SP`, `SB`, `InitMem`, …) and the `Arg`s
of the incoming stack arguments (G62, no code; `runLoc` writes their slots, which the caller's
side `EntryMatch.stack` relates). The position of the entry stores, the end-to-end theorem's `k`
as the driver takes it. -/
def entryLen (lc : LocCtx) : Nat :=
  match lc.ctx.f.block? lc.ctx.f.entry with
  | some blk =>
    (blk.values.toList.takeWhile fun id =>
      (lc.ctx.f.value? id).any fun v => entryOp v.op || v.op == .Arg).length
  | none => 0

/-- A value among the first `k` of the entry block writes the closure context register `R26`
(`ctxReg`; its home has the register): the entry state's `R26` may then hold a value, which the
morestack path must keep, so the morestack tail must call `runtime.morestack` (a function with
`NEEDCTXT`), not `runtime.morestack_noctxt`, which zeroes `R26` (`MorestackOK`'s context). -/
def ctxtBefore (lc : LocCtx) (k : Nat) : Bool :=
  match lc.ctx.f.block? lc.ctx.f.entry with
  | some blk =>
    (blk.values.toList.take k).any fun id =>
      (lc.ctx.f.value? id).any fun v =>
        (lc.home v.id).any fun h => h.regList.contains (some ctxReg)
  | none => false

/-- Why `entryStoresOK lc g k` fails: the first pending window with a byte no entry store
writes. -/
def entryStoresWhy (lc : LocCtx) (g : G2In) (k : Nat) : String :=
  let st := entryStores lc g k
  match (pendWins lc g).find? fun (o, n) => !(List.range n).all fun j => inWins st (o + j) with
  | some (o, n) => s!"entry stores ({st.length}) do not cover the pending window [{o}, {o + n})"
  | none => "accepted"

end GoFV.Gen.Check
