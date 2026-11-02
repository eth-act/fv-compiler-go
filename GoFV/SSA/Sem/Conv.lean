import GoFV.SSA.Sem.Cmp
import GoFV.SSA.Sem.Mem

/-!
# Integer conversions, constants, tuples (`docs/plans/semantics.md` §4.5, §4.8)
-/

namespace GoFV.SSA.Sem

namespace Conv

def signExt (w w' : Width) : List Val → Val := int1 w fun x => .int w' (x.signExtend w'.bits)
def zeroExt (w w' : Width) : List Val → Val := int1 w fun x => .int w' (x.setWidth w'.bits)
def trunc (w w' : Width) : List Val → Val := int1 w fun x => .int w' (x.setWidth w'.bits)

/-- `CvtBoolToUint8`: 0/1. -/
def boolToUint8 : List Val → Val
  | [b] => match b.asBool with
    | some b => .i8 (if b then 1 else 0)
    | none => .poison
  | _ => .poison

/-- `Const8` … `Const64`: the auxint is sign-extended to 64 bits even for unsigned types
(gO 339); the value is its low `w` bits. -/
def const (w : Width) (auxInt : Int64) : Val := .int w (BitVec.ofInt w.bits auxInt.toInt)

/-- `ConstBool`: auxint 0/1 (other auxints are rejected by the checker). -/
def constBool (auxInt : Int64) : Val := .bool (auxInt != 0)

end Conv

namespace Tuple

/-- `Select0`/`Select1`: a component of a `TUPLE`. -/
def select (i : Nat) : List Val → Val
  | [.tuple vs] => vs.getD i .poison
  | _ => .poison

/-- `SelectN [i]`: component `i` of a call's `RESULTS` tuple. -/
def selectN (auxInt : Int64) : List Val → Val
  | [.tuple vs] => if auxInt.toInt < 0 then .poison else vs.getD auxInt.toInt.toNat .poison
  | _ => .poison

/-- `SelectNAddr [i]`: the address of stack-assigned result `i` of a call, which the call's
tuple carries after its memory (`callOp`), as the word address arithmetic computes it
(`Ptr.word`: after `expand calls` it is `OffPtr [off] SP` of the `uintptr` `SP`, an integer
word); `poison` for a register result or a non-call. -/
def selectNAddr (auxInt : Int64) : List Val → Val
  | [.tuple vs] =>
    match vs.getLast? with
    | some (.agg addrs) =>
      if auxInt.toInt < 0 then .poison
      else match addrs[auxInt.toInt.toNat]? with
        | some (.ptr p) => p.word
        | _ => .poison
    | _ => .poison
  | _ => .poison

/-- `MakeTuple x y`. -/
def make : List Val → Val
  | [x, y] => .tuple [x, y]
  | _ => .poison

end Tuple

end GoFV.SSA.Sem
