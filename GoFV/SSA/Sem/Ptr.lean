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

/-- The pointer of a pointer-shaped word: a pointer, or a 64-bit integer read as the pointer
at that concrete address (`uintptr`-typed words such as `ConstNil <uintptr>` or an itab word
after `decompose builtin`). -/
def asPtrWord : Val → Option Ptr
  | .ptr p => some p
  | .int .w64 x => some (Ptr.ofAddr x)
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

/-- The result of pointer arithmetic: `poison` when it leaves its block's address window
(Go's unsafe rules: arithmetic stays inside the allocation or one past its end; §3.3). -/
def ptrRes (p : Ptr) : Val := if p.inWindow then .ptr p else .poison

/-- `OffPtr [off] p`: `p + off` (an integer `p`, e.g. a `uintptr`, adds as an integer). -/
def offPtr (auxInt : Int64) : List Val → Val
  | [.ptr p] => ptrRes (p.add (BitVec.ofInt 64 auxInt.toInt))
  | [.int .w64 x] => .int .w64 (x + BitVec.ofInt 64 auxInt.toInt)
  | _ => .poison

/-- `AddPtr p i`: `p + i`. -/
def addPtr : List Val → Val
  | [.ptr p, i] => match asOffset i with
    | some k => ptrRes (p.add k)
    | none => .poison
  | [.int .w64 x, i] => match asOffset i with
    | some k => .int .w64 (x + k)
    | none => .poison
  | _ => .poison

/-- `PtrIndex <*T> p i`: `p + i·sizeof(T)` (`elem` from the result type). -/
def ptrIndex (elem : Option Nat) : List Val → Val
  | [.ptr p, i] => match elem, asOffset i with
    | some e, some k => ptrRes (p.add (k * BitVec.ofNat 64 e))
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
  | [a, b] => match a.asPtrWord, b.asPtrWord with
    | some p, some q => .bool (p.eq q != neg)
    | _, _ => .poison
  | _ => .poison

/-- `IsNonNil p`. -/
def isNonNil : List Val → Val
  | [.ptr p] => .bool (!p.isNil)
  | [.int _ x] => .bool (x != 0)
  | _ => .poison

/-- `Convert x mem` to shape `t`: pointer → integer by concrete address (`poison` unless the
pointer converts back to itself, `Ptr.convertible`), integer → pointer by `Ptr.ofAddr`; the
memory argument only orders it. -/
def convert (t : Ty) : List Val → Val
  | [x, _] => match t, x with
    | .int .w64, .ptr p => match p.convertible, p.addr? with
      | true, some a => .int .w64 a
      | _, _ => .poison
    | .ptr _, .int .w64 a => .ptr (Ptr.ofAddr a)
    | _, x => x
  | _ => .poison

/-- `EqInter`/`NeqInter`/`EqSlice`/`NeqSlice`: compare the first words (itab, slice pointer;
`generic.rules:790-792`). -/
def eqFirst (neg : Bool) : List Val → Val
  | [.agg (a :: _), .agg (b :: _)] => match a.asPtrWord, b.asPtrWord with
    | some p, some q => .bool (p.eq q != neg)
    | _, _ => .poison
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

/-- `AtomicLoad{8,32,64,Ptr} p mem`, `AtomicLoadAcq{32,64} p mem` (sequential semantics,
§9 P5 pulled forward: they only read): `(value, mem)`. An access that is not naturally
aligned within its allocation reads `poison`. -/
def atomicLoad (t : Ty) : List Val → Val
  | [.ptr p, .mem m] =>
    match t with
    | .tuple [vt, .mem] =>
      let v := if vt.size == 0 || p.off.toNat % vt.size != 0 then .poison else m.load vt p
      .tuple [v, .mem m]
    | _ => .poison
  | _ => .poison

/-- `MemEq p q n mem`: the `n` bytes at `p` and `q` are equal; `poison` if either range is
invalid or holds poison bytes. -/
def memEq : List Val → Val
  | [.ptr p, .ptr q, .int _ n, .mem m] =>
    match m.read p n.toNat, m.read q n.toNat with
    | some a, some b =>
      if a.any (· == .poison) || b.any (· == .poison) then .poison else .bool (a == b)
    | _, _ => .poison
  | _ => .poison

/-- `Load <T> p mem`, `Dereference <T> p mem`. -/
def loadOp (t : Ty) : List Val → Val
  | [.ptr p, .mem m] => m.load t p
  | _ => .poison

end GoFV.SSA.Sem
