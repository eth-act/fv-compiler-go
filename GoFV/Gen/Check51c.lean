import GoFV.Gen.Check50

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G51 group c: boolean operands of arithmetic and shifted logic
(`docs/plans/proofs3.md` §4)

G1's `ADD`, `SUB`, `ADDconst`, `SUBconst`, G16's `ADDshiftLL`, G36's shifted adds and subtracts
(`shOp36?`) and G27's shifted logic ops (`logSh?`) ask that each argument be at least as wide as
the result: only the low bits of a narrow argument's register are known. A boolean (class 1) is
known on all 64 bits: its register is 0 or 1 (`ValRel` of `.bool`, `Arm64.reg`). G51c accepts
these ops where an argument has class 1 (`wid51c`: at least the result's class, or 1), with every
other condition of the existing check (`8 ≤ c`, the shift amount in `[0, 64)`), and emitting the
same Prog:

* `ADD`, `SUB x y` (`arith51c`): `OP Rm, Rn, Rd`, one of `x`, `y` a boolean;
* `ADDconst`, `SUBconst [k] x` (`arithK51c`): `OP $k, Rn, Rd`, `x` a boolean;
* `ADDshiftLL [k] x y` (`addSh51c`): `ADD Rm<<k, Rn, Rd` (`shiftLLA`), one of `x`, `y` a boolean;
* the shifted adds and subtracts of G36 and the shifted logic ops of G27 (`sh51c`):
  `op Rm SHIFT k, Rn, Rd` (`shiftA`), one of `x`, `y` a boolean, and `y` of class 64 or a boolean
  for a right shift (`shWid51c`).

`vkind51c lc v` is `none` off these ops (`op51c`). `GoFV/Proof/Gen/G51c.lean` proves what an
accepted value satisfies.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- The ops of G51c: G1's register and constant adds and subtracts, `ADDshiftLL`, G36's shifted
adds and subtracts, G27's shifted logic ops. -/
def op51c (op : Op) : Bool :=
  op == .ARM64ADD || op == .ARM64SUB || op == .ARM64ADDconst || op == .ARM64SUBconst ||
    op == .ARM64ADDshiftLL || (logSh? op).isSome || (shOp36? op).isSome

/-- An argument of class `ca` for a result of class `c`: at least as wide, or a boolean (its whole
register is 0 or 1). -/
def wid51c (c ca : Nat) : Bool := decide (c ≤ ca) || ca == 1

/-- The shifted argument's class `cb` for shift kind `typ` (0 `LSL`): `wid51c` for a left shift,
else 64 or a boolean (a right shift reads the whole register). -/
def shWid51c (typ c cb : Nat) : Bool := if typ == 0 then wid51c c cb else cb == 64 || cb == 1

/-- `ADD`, `SUB x y` with a boolean argument: `OP Rm, Rn, Rd`. -/
def arith51c (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && wid51c c ca && wid51c c cb && (ca == 1 || cb == 1) do
    throw s!"v{v.id}: arithmetic widths"
  let as := if v.op == .ARM64ADD then As.ADD else As.SUB
  return .prog (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd })

/-- `ADDconst`, `SUBconst [k] x` of a boolean `x`: `OP $k, Rn, Rd`. -/
def arithK51c (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless v.args.size == 1 do throw s!"v{v.id}: shape"
  let (ca, rn) ← argObj lc v 0
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && ca == 1 do throw s!"v{v.id}: arithmetic widths"
  let as := if v.op == .ARM64ADDconst then As.ADD else As.SUB
  return .prog (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd })

/-- `ADDshiftLL [k] x y` with a boolean argument, `0 ≤ k < 64`: `ADD Rm<<k, Rn, Rd`. -/
def addSh51c (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && wid51c c ca && wid51c c cb && (ca == 1 || cb == 1) do
    throw s!"v{v.id}: arithmetic widths"
  return .prog (.ofShape
    { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd })

/-- A shifted add, subtract or logic op `x op (y SHIFT k)` with a boolean argument, `0 ≤ k < 64`:
`op Rm SHIFT k, Rn, Rd`; `what` names the widths in the error. -/
def sh51c (lc : LocCtx) (v : Value) (as : As) (typ : Nat) (what : String) :
    Except String VKind2 := do
  unless v.args.size == 2 do throw s!"v{v.id}: shape"
  unless 0 ≤ v.auxInt.toInt && v.auxInt.toInt < 64 do throw s!"v{v.id}: shift amount"
  let (ca, rn) ← argObj lc v 0
  let (cb, rm) ← argObj lc v 1
  let (c, rd) ← resObj lc v
  unless 8 ≤ c && wid51c c ca && shWid51c typ c cb && (ca == 1 || cb == 1) do
    throw s!"v{v.id}: {what} widths"
  return .prog (.ofShape
    { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd })

/-- What a value of G51c's ops emits (module doc), or why it is outside the slice. -/
def kind51c (lc : LocCtx) (v : Value) : Except String VKind2 := do
  unless (lc.temps[v.id]?).join == none do throw s!"v{v.id}: temporary register"
  match logSh? v.op, shOp36? v.op with
  | some (as, typ), _ => sh51c lc v as typ "shifted logic"
  | none, some (as, typ) => sh51c lc v as typ "arithmetic"
  | none, none =>
    if v.op == .ARM64ADDshiftLL then addSh51c lc v
    else if v.op == .ARM64ADD || v.op == .ARM64SUB then arith51c lc v
    else if v.op == .ARM64ADDconst || v.op == .ARM64SUBconst then arithK51c lc v
    else throw s!"v{v.id}: op {v.op.name}"

/-- G51c's check of `v`: `none` off its ops (`op51c`). -/
def vkind51c (lc : LocCtx) (v : Value) : Option (Except String VKind2) :=
  if op51c v.op then some (kind51c lc v) else none

end GoFV.Gen.Check
