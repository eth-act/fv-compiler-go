import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Cmp

/-!
# Pointers, composites, loads (`docs/plans/semantics.md` §3.3, §4.7; phase P2)

The pure P2 families of `evalPure`. Pointer arithmetic keeps the allocation and adds to the
offset mod 2^64; `Convert` and pointer comparison use the concrete addresses of `Sem/Mem`.
`Load`/`Dereference` read the snapshot their memory argument names (§3.4) and are pure.
-/

namespace GoFV.SSA.Sem

namespace Val

/-- The pointer of a pointer value. -/
def asPtr : Val → Option Ptr
  | .ptr p => some p
  | _ => none

end Val

namespace Ptr

/-- `p + k` (offset mod 2^64). -/
def add (p : Ptr) (k : BitVec 64) : Ptr := { p with off := p.off + k }

end Ptr

/-- A 64-bit integer of any width, sign-extended (an index or offset argument). -/
def asOffset : Val → Option (BitVec 64)
  | .int w x => some (x.signExtend 64)
  | _ => none

namespace PtrOps

/-- `OffPtr [off] p`: `p + off` (an integer `p`, e.g. a `uintptr`, adds as an integer). -/
def offPtr (auxInt : Int64) : List Val → Val
  | [.ptr p] => .ptr (p.add (BitVec.ofInt 64 auxInt.toInt))
  | [.int .w64 x] => .int .w64 (x + BitVec.ofInt 64 auxInt.toInt)
  | _ => .poison

/-- `AddPtr p i`: `p + i`. -/
def addPtr : List Val → Val
  | [.ptr p, i] => match asOffset i with
    | some k => .ptr (p.add k)
    | none => .poison
  | [.int .w64 x, i] => match asOffset i with
    | some k => .int .w64 (x + k)
    | none => .poison
  | _ => .poison

/-- `PtrIndex <*T> p i`: `p + i·sizeof(T)` (`elem` from the result type). -/
def ptrIndex (elem : Option Nat) : List Val → Val
  | [.ptr p, i] => match elem, asOffset i with
    | some e, some k => .ptr (p.add (k * BitVec.ofNat 64 e))
    | _, _ => .poison
  | _ => .poison

/-- `SubPtr p q`: the difference of concrete addresses. -/
def subPtr : List Val → Val
  | [.ptr p, .ptr q] => match p.addr?, q.addr? with
    | some a, some b => .int .w64 (a - b)
    | _, _ => if p.blk == q.blk then .int .w64 (p.off - q.off) else .poison
  | _ => .poison

/-- `EqPtr`/`NeqPtr` (`neg`). -/
def eqPtr (neg : Bool) : List Val → Val
  | [.ptr p, .ptr q] => .bool (p.eq q != neg)
  | _ => .poison

/-- `IsNonNil p`. -/
def isNonNil : List Val → Val
  | [.ptr p] => .bool (!p.isNil)
  | [.int _ x] => .bool (x != 0)
  | _ => .poison

/-- `Convert x mem` to shape `t`: pointer → integer by concrete address, integer → pointer
by `Ptr.ofAddr`; the memory argument only orders it. -/
def convert (t : Ty) : List Val → Val
  | [x, _] => match t, x with
    | .int .w64, .ptr p => match p.addr? with
      | some a => .int .w64 a
      | none => .poison
    | .ptr _, .int .w64 a => .ptr (Ptr.ofAddr a)
    | _, x => x
  | _ => .poison

/-- `EqInter`/`NeqInter`/`EqSlice`/`NeqSlice`: compare the first words (itab, slice pointer;
`generic.rules:790-792`). -/
def eqFirst (neg : Bool) : List Val → Val
  | [.agg (.ptr p :: _), .agg (.ptr q :: _)] => .bool (p.eq q != neg)
  | _ => .poison

end PtrOps

namespace Comp

/-- `StringMake`, `SliceMake`, `IMake`, `ComplexMake`, `StructMake`, `ArrayMake1`. -/
def make (args : List Val) : Val := .agg args

/-- Component `i` of a composite (`StringPtr` 0, `StringLen` 1, `SlicePtr` 0, `SliceLen` 1,
`SliceCap` 2, `ITab` 0, `IData` 1, `StructSelect [i]`, `ArraySelect [i]`). -/
def select (i : Nat) : List Val → Val
  | [.agg vs] => vs.getD i .poison
  | _ => .poison

/-- `StructSelect [i]`/`ArraySelect [i]` with the index from the auxint. -/
def selectAux (auxInt : Int64) : List Val → Val :=
  if auxInt.toInt < 0 then fun _ => .poison else select auxInt.toInt.toNat

end Comp

/-- `Load <T> p mem`, `Dereference <T> p mem`. -/
def loadOp (t : Ty) : List Val → Val
  | [.ptr p, .mem m] => m.load t p
  | _ => .poison

end GoFV.SSA.Sem
