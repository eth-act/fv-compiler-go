import GoFV.SSA.Sem.Mem
import GoFV.SSA.Sem.Cmp

/-!
# Pointers, composites, loads (`docs/plans/semantics.md` §3.3, §4.7; phase P2)

The pure P2 families of `evalPure`. Pointer arithmetic keeps the allocation and adds to the
offset mod 2^64; `Convert` and pointer comparison use the concrete addresses of `Sem/Mem`.
`Load`/`Dereference` read the snapshot their memory argument names (§3.4) and are pure.
-/

namespace GoFV.SSA.Sem

variable [Addrs]

/-- A 64-bit integer of any width, sign-extended (an index or offset argument). -/
def asOffset : Val → Option (BitVec 64)
  | .int w x => some (x.signExtend 64)
  | _ => none

namespace PtrOps

/-- The result of pointer arithmetic, as its word (`Ptr.word`, §3.2): `poison` when it leaves
its block's address window (Go's unsafe rules: arithmetic stays inside the allocation or one past
its end; §3.3). -/
def ptrRes (p : Ptr) : Val := if p.inWindow then p.word else .poison

/-- The result of pointer arithmetic on an integer word `x` (a pointer-typed value holding a
concrete address, §3.3): the integer `x + k`, under the window rule of the pointer at that
address (`ptrRes`), so the word behaves as that pointer (`Ptr.ofAddr_add_of_inWindow`). -/
def wordRes (x k : BitVec 64) : Val :=
  if ((Ptr.ofAddr x).add k).inWindow then .int .w64 (x + k) else .poison

/-- `OffPtr [off] p`: `p + off` (an integer word adds as an integer, `wordRes`). -/
def offPtr (auxInt : Int64) : List Val → Val
  | [.ptr p] => ptrRes (p.add (BitVec.ofInt 64 auxInt.toInt))
  | [.int .w64 x] => wordRes x (BitVec.ofInt 64 auxInt.toInt)
  | _ => .poison

/-- `AddPtr p i`: `p + i`. -/
def addPtr : List Val → Val
  | [.ptr p, i] => match asOffset i with
    | some k => ptrRes (p.add k)
    | none => .poison
  | [.int .w64 x, i] => match asOffset i with
    | some k => wordRes x k
    | none => .poison
  | _ => .poison

/-- `PtrIndex <*T> p i`: `p + i·sizeof(T)` (`elem` from the result type; an integer word adds
as an integer, like `AddPtr`). -/
def ptrIndex (elem : Option Nat) : List Val → Val
  | [.ptr p, i] => match elem, asOffset i with
    | some e, some k => ptrRes (p.add (k * BitVec.ofNat 64 e))
    | _, _ => .poison
  | [.int .w64 x, i] => match elem, asOffset i with
    | some e, some k => wordRes x (k * BitVec.ofNat 64 e)
    | _, _ => .poison
  | _ => .poison

/-- `SubPtr p q`: the difference of concrete addresses. -/
def subPtr : List Val → Val
  | [a, b] => match a.asPtrWord, b.asPtrWord with
    | some p, some q => match p.addr?, q.addr? with
      | some x, some y => .int .w64 (x - y)
      | _, _ => if p.blk == q.blk then .int .w64 (p.off - q.off) else .poison
    | _, _ => .poison
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
pointer converts back to itself, `Ptr.convertible`); an integer keeps its word at a pointer
shape (§3.3), so integer → pointer is the identity; the memory argument only orders it. -/
def convert (t : Ty) : List Val → Val
  | [x, _] => match t, x with
    | .int .w64, .ptr p => match p.convertible, p.addr? with
      | true, some a => .int .w64 a
      | _, _ => .poison
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
  | [a, .mem m] =>
    match a.asPtrWord, t with
    | some p, .tuple [vt, .mem] =>
      let v := if vt.size == 0 || p.off.toNat % vt.size != 0 then .poison else m.load vt p
      .tuple [v, .mem m]
    | _, _ => .poison
  | _ => .poison

/-- `MemEq p q n mem`: the `n` bytes at `p` and `q` are equal; `poison` if either range is
invalid or holds poison bytes. -/
def memEq : List Val → Val
  | [x, y, .int _ n, .mem m] =>
    match x.asPtrWord, y.asPtrWord with
    | some p, some q =>
      match m.read p n.toNat, m.read q n.toNat with
      | some a, some b =>
        if a.any (· == .poison) || b.any (· == .poison) then .poison else .bool (a == b)
      | _, _ => .poison
    | _, _ => .poison
  | _ => .poison

/-- `Load <T> p mem`, `Dereference <T> p mem`. -/
def loadOp (t : Ty) : List Val → Val
  | [a, .mem m] => match a.asPtrWord with
    | some p => m.load t p
    | none => .poison
  | _ => .poison

/-- `WB [n] mem` (the write-barrier buffer, §9): `(the buffer, mem)` with a fresh buffer of `n`
pointer-sized entries (`Mem.wbAlloc`); the write-barrier sequence stores the entries for the GC
into it, and `WBend` frees it. -/
def wbOp (n : Int64) : List Val → Val
  | [.mem m] => .tuple [.ptr ⟨.wbuf, 0⟩, .mem (m.wbAlloc n.toInt.toNat)]
  | _ => .poison

end GoFV.SSA.Sem
