/-!
# Semantic values (`docs/plans/semantics.md` §3.2–§3.4)

The value domain of `GoFV.SSA.run`. Phase P1 (integers, booleans, control flow): integers of
the four widths, booleans, tuples (`TUPLE` and `RESULTS` types) and `poison` (§3.5). Phase P2
(memory, pointers, composites): pointers with provenance (`Ptr`), memory snapshots (`Mem`),
composite values (`agg`), byte blobs of non-SSA-able values and zero-sized values. Floats
(P4) are added as further constructors.

Integers carry no sign: signedness lives in the op (`Less64` vs `Less64U`), as in Go.
-/

namespace GoFV.SSA.Sem

/-- Integer widths of Go SSA (`int`, `uint`, `uintptr` are `w64` on arm64). -/
inductive Width where
  | w8 | w16 | w32 | w64
  deriving DecidableEq, Repr, Inhabited

namespace Width

/-- Number of bits. -/
@[reducible] def bits : Width → Nat
  | .w8 => 8 | .w16 => 16 | .w32 => 32 | .w64 => 64

/-- Number of bytes. -/
def bytes (w : Width) : Nat := w.bits / 8

/-- The width of an integer type of `size` bytes. -/
def ofSize? : Int → Option Width
  | 1 => some .w8 | 2 => some .w16 | 4 => some .w32 | 8 => some .w64 | _ => none

end Width

/-- An allocation (§3.3): the provenance part of a pointer. Globals are named by their link
symbol, frame objects by activation and `*ir.Name` (aux number), heap objects by creation
order. -/
inductive Blk where
  /-- No allocation: the nil pointer (offset 0) and integers converted to pointers that
  point into no allocation. -/
  | nil
  | global (sym : String)
  /-- A `PAUTO`/`PPARAM`/`PPARAMOUT` variable of activation `act`. -/
  | local (act : Nat) (name : Nat)
  /-- The outgoing-arguments area of activation `act` (what `SP` points to). -/
  | outargs (act : Nat)
  | heap (n : Nat)
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A pointer: an allocation and a byte offset (mod 2^64) (§3.3). -/
structure Ptr where
  blk : Blk
  off : BitVec 64
  deriving DecidableEq, Repr, Inhabited

/-- The nil pointer. -/
def Ptr.null : Ptr := ⟨.nil, 0⟩

/-- A byte of memory: a concrete byte, byte `i` of a stored pointer, or poison (§3.4). -/
inductive Byte where
  | b (x : BitVec 8)
  | frag (p : Ptr) (i : Nat)
  | poison
  deriving DecidableEq, Repr, Inhabited

/-- An allocation's state: its bytes (the size is `data.size`) and writability. Freed
allocations are removed from the memory. -/
structure Alloc where
  data : Array Byte
  writable : Bool := true
  deriving DecidableEq, Repr, Inhabited

/-- A memory snapshot: the allocations that exist, by block. A block that is not listed has
no bytes (every access to it is invalid). -/
structure Mem where
  blocks : Array (Blk × Alloc) := #[]
  /-- Next fresh `Blk.heap` number. -/
  nextHeap : Nat := 0
  /-- Next fresh activation number (frame blocks of activation `a` are `Blk.local a _` and
  `Blk.outargs a`; the run's own activation is 0). -/
  nextAct : Nat := 1
  deriving DecidableEq, Repr, Inhabited

/-- A semantic value. -/
inductive Val where
  /-- An integer of any Go integer kind, as a bit pattern. -/
  | int (w : Width) (x : BitVec w.bits)
  | bool (b : Bool)
  /-- A memory snapshot (`InitMem`, `Store`, …, the memory component of calls and
  `MakeResult`). -/
  | mem (m : Mem)
  /-- `TUPLE` and `RESULTS` values (`MakeResult`, `Mul64uhilo`, call results). -/
  | tuple (vs : List Val)
  /-- `*T`, `unsafe.Pointer`, map/chan/func words. -/
  | ptr (p : Ptr)
  /-- A composite value: struct fields, `[1]T`, string (ptr, len), slice (ptr, len, cap),
  interface (itab/type, data); the shape comes from the SSA type. -/
  | agg (vs : List Val)
  /-- A non-SSA-able value (`Dereference`, `Load` of a big type after `expand calls`). -/
  | blob (bs : List Byte)
  /-- A zero-sized value (`Empty`). -/
  | empty
  /-- The result of a partial op outside its domain, of `Unknown`, of a read of
  uninitialised or invalid memory, and of ops whose semantics belongs to a later phase
  (§3.5). Observing it is `stuck`. -/
  | poison
  deriving Inhabited, Repr

namespace Val

/-- `int` of width 8/16/32/64 (convenience constructors with a fixed width). -/
abbrev i8 (x : BitVec 8) : Val := .int .w8 x
abbrev i16 (x : BitVec 16) : Val := .int .w16 x
abbrev i32 (x : BitVec 32) : Val := .int .w32 x
abbrev i64 (x : BitVec 64) : Val := .int .w64 x

mutual
/-- Decidable equality (nested `List Val`, dependent `BitVec`). -/
def beq : Val → Val → Bool
  | .int w x, .int w' y =>
    if h : w = w' then (h ▸ x) == y else false
  | .bool a, .bool b => a == b
  | .mem m, .mem m' => m == m'
  | .tuple as, .tuple bs => beqList as bs
  | .ptr p, .ptr q => p == q
  | .agg as, .agg bs => beqList as bs
  | .blob as, .blob bs => as == bs
  | .empty, .empty => true
  | .poison, .poison => true
  | _, _ => false
def beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

instance : BEq Val := ⟨beq⟩

/-- Rendering of a block for test output (stable across sections of one function). -/
def renderBlk : Blk → String
  | .nil => "nil"
  | .global s => s
  | .local a n => s!"local{a}.a{n}"
  | .outargs a => s!"outargs{a}"
  | .heap n => s!"heap{n}"

/-- Short rendering for test output: integers signed (`toInt`), pointers as block+offset. -/
partial def render : Val → String
  | .int w x => s!"i{w.bits}:{x.toInt}"
  | .bool b => toString b
  | .mem _ => "mem"
  | .tuple vs => "(" ++ ", ".intercalate (vs.map render) ++ ")"
  | .ptr p => s!"&{renderBlk p.blk}+{p.off.toNat}"
  | .agg vs => "{" ++ ", ".intercalate (vs.map render) ++ "}"
  | .blob bs => s!"blob[{bs.length}]"
  | .empty => "empty"
  | .poison => "poison"

end Val

/-- Byte refinement (§3.5): a `poison` byte is refined by any byte; other bytes (concrete
bytes and pointer fragments) only by themselves. -/
inductive Byte.Refines : Byte → Byte → Prop where
  | poison (b : Byte) : Byte.Refines .poison b
  | refl (b : Byte) : Byte.Refines b b

/-- Pointwise refinement of byte lists of equal length. -/
inductive BytesRefine : List Byte → List Byte → Prop where
  | nil : BytesRefine [] []
  | cons {a b : Byte} {as bs : List Byte} : Byte.Refines a b → BytesRefine as bs →
      BytesRefine (a :: as) (b :: bs)

theorem BytesRefine.refl : (bs : List Byte) → BytesRefine bs bs
  | [] => .nil
  | b :: bs => .cons (.refl b) (BytesRefine.refl bs)

/-- Allocation refinement: the same writability, the bytes refined pointwise. -/
structure Alloc.Refines (a a' : Alloc) : Prop where
  writable : a.writable = a'.writable
  data : BytesRefine a.data.toList a'.data.toList

/-- Allocation lists with the same blocks in the same order, allocations refined. -/
inductive AllocsRefine : List (Blk × Alloc) → List (Blk × Alloc) → Prop where
  | nil : AllocsRefine [] []
  | cons (b : Blk) {a a' : Alloc} {l l' : List (Blk × Alloc)} : Alloc.Refines a a' →
      AllocsRefine l l' → AllocsRefine ((b, a) :: l) ((b, a') :: l')

theorem AllocsRefine.refl : (l : List (Blk × Alloc)) → AllocsRefine l l
  | [] => .nil
  | (b, a) :: l => .cons b ⟨rfl, BytesRefine.refl _⟩ (AllocsRefine.refl l)

/-- Memory refinement (§3.5): the same allocations (blocks, order, sizes, writability), heap
counter and activation counter, every byte refined. -/
structure Mem.Refines (m m' : Mem) : Prop where
  nextHeap : m.nextHeap = m'.nextHeap
  nextAct : m.nextAct = m'.nextAct
  blocks : AllocsRefine m.blocks.toList m'.blocks.toList

theorem Mem.Refines.refl (m : Mem) : Mem.Refines m m := ⟨rfl, rfl, AllocsRefine.refl _⟩

mutual
/-- Refinement (§3.5): `Refines src tgt` iff `src` is `poison` or `src = tgt`, pointwise through
tuples and composites, and bytewise through memories and blobs (`Mem.Refines`,
`BytesRefine`). A pass is correct when every value it computes refines the source's. -/
inductive Refines : Val → Val → Prop where
  | poison (v : Val) : Refines .poison v
  | int (w : Width) (x : BitVec w.bits) : Refines (.int w x) (.int w x)
  | bool (b : Bool) : Refines (.bool b) (.bool b)
  | mem {m m' : Mem} : Mem.Refines m m' → Refines (.mem m) (.mem m')
  | tuple {as bs : List Val} : RefinesList as bs → Refines (.tuple as) (.tuple bs)
  | ptr (p : Ptr) : Refines (.ptr p) (.ptr p)
  | agg {as bs : List Val} : RefinesList as bs → Refines (.agg as) (.agg bs)
  | blob {bs bs' : List Byte} : BytesRefine bs bs' → Refines (.blob bs) (.blob bs')
  | empty : Refines .empty .empty
/-- Pointwise refinement of lists of equal length. -/
inductive RefinesList : List Val → List Val → Prop where
  | nil : RefinesList [] []
  | cons {a b : Val} {as bs : List Val} : Refines a b → RefinesList as bs →
      RefinesList (a :: as) (b :: bs)
end

mutual
theorem Refines.refl : (v : Val) → Refines v v
  | .int w x => .int w x
  | .bool b => .bool b
  | .mem m => .mem (Mem.Refines.refl m)
  | .tuple vs => .tuple (RefinesList.refl vs)
  | .ptr p => .ptr p
  | .agg vs => .agg (RefinesList.refl vs)
  | .blob bs => .blob (BytesRefine.refl bs)
  | .empty => .empty
  | .poison => .poison _
theorem RefinesList.refl : (vs : List Val) → RefinesList vs vs
  | [] => .nil
  | v :: vs => .cons (Refines.refl v) (RefinesList.refl vs)
end

/-- The shape (layout) of an SSA type (`Sem/Layout.lean` computes it from the export). -/
inductive Ty where
  | int (w : Width)
  | bool
  | mem
  /-- `TUPLE` (two components) and `RESULTS` (memory last). -/
  | tuple (ts : List Ty)
  /-- Any type the semantics does not evaluate and whose size is unknown (`void`, `flags`,
  types the export has no size for, …). -/
  | other
  /-- Pointer-shaped types; `elem` is the element size of `*T` (for `PtrIndex`). -/
  | ptr (elem : Option Nat)
  /-- An SSA-able composite: its fields at their byte offsets, and its size (string, slice,
  interface, struct, `[1]T`). -/
  | agg (fields : List (Nat × Ty)) (size : Nat)
  /-- A type kept as bytes: arrays of more than one element. -/
  | blob (size : Nat)
  /-- A zero-sized type. -/
  | empty
  /-- A type of known size whose values a later phase evaluates (floats, complex: P4); loads
  give `poison`, stores write poison bytes. -/
  | opaque (size : Nat)
  deriving Inhabited, Repr

/-- Why a run panicked (§6): `PanicBounds`, `NilCheck` of nil, and the runtime's panicking
entry points the environment models (`runtime.panicdivide`, `runtime.panicshift`,
`runtime.panicoverflow`). -/
inductive Panic where
  /-- `PanicBounds [kind] x y`: `kind` is the `ssa.BoundsKind` auxint (`op.go:470-489`), `x`
  the index read signed or unsigned as the kind says, `y` the length/capacity (signed). -/
  | bounds (kind : Nat) (x y : Int)
  | divide
  | shift
  /-- `runtime.panicoverflow` (`math/bits.Div64` with a quotient overflow). -/
  | overflow
  /-- Any other panicking runtime entry point, by symbol name. -/
  | runtime (name : String)
  /-- A `runtime.Error` with the given text (`errorString`: `makeslice: len out of range`, …). -/
  | error (msg : String)
  /-- `NilCheck` of a nil pointer (§6). -/
  | nilDeref
  deriving DecidableEq, Repr, Inhabited

namespace Panic

/-- The text of the `runtime.Error` Go reports for the panic (`runtime/error.go`
`boundsErrorFmts`/`boundsNegErrorFmts`, `divideError`, `shiftError`), for comparison with
native runs. -/
def message : Panic → String
  | .bounds kind x y =>
    let neg := x < 0
    let s := match kind / 2 with
      | 0 => if neg then s!"index out of range [{x}]"
             else s!"index out of range [{x}] with length {y}"
      | 1 => if neg then s!"slice bounds out of range [:{x}]"
             else s!"slice bounds out of range [:{x}] with length {y}"
      | 2 => if neg then s!"slice bounds out of range [:{x}]"
             else s!"slice bounds out of range [:{x}] with capacity {y}"
      | 3 => if neg then s!"slice bounds out of range [{x}:]"
             else s!"slice bounds out of range [{x}:{y}]"
      | 4 => if neg then s!"slice bounds out of range [::{x}]"
             else s!"slice bounds out of range [::{x}] with length {y}"
      | 5 => if neg then s!"slice bounds out of range [::{x}]"
             else s!"slice bounds out of range [::{x}] with capacity {y}"
      | 6 => if neg then s!"slice bounds out of range [:{x}:]"
             else s!"slice bounds out of range [:{x}:{y}]"
      | 7 => if neg then s!"slice bounds out of range [{x}::]"
             else s!"slice bounds out of range [{x}:{y}:]"
      | _ => s!"cannot convert slice with length {y} to array or pointer to array with length {x}"
    "runtime error: " ++ s
  | .divide => "runtime error: integer divide by zero"
  | .shift => "runtime error: negative shift amount"
  | .overflow => "runtime error: integer overflow"
  | .runtime name => s!"panic in {name}"
  | .error msg => "runtime error: " ++ msg
  | .nilDeref => "runtime error: invalid memory address or nil pointer dereference"

end Panic

end GoFV.SSA.Sem
