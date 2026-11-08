/-!
# Semantic values (`docs/plans/semantics.md` §3.2–§3.4)

The value domain of `GoFV.SSA.run`. Phase P1 (integers, booleans, control flow): integers of
the four widths, booleans, tuples (`TUPLE` and `RESULTS` types) and `poison` (§3.5). Phase P2
(memory, pointers, composites): pointers with provenance (`Ptr`), memory snapshots (`Mem`),
composite values (`agg`), byte blobs of non-SSA-able values and zero-sized values. Floats
(P4) are their IEEE 754 bit patterns in `int .w32`/`int .w64` (`Sem/Float.lean`).

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
  /-- A `PAUTO` of activation `act` whose address the function does not convert to an integer
  (no `addrconv` flag, `Tables.forgeable`): it has the address of `local act name`, but no
  integer converts back to it (`Ptr.ofAddr` never returns it, §3.3), so a conjured pointer
  points into no allocation. -/
  | temp (act : Nat) (name : Nat)
  | heap (n : Nat)
  /-- The write-barrier buffer (`WB`, §9): the entries a write-barrier sequence hands to the GC.
  It has no address (`Ptr.ofAddr` never returns it), only `WB` creates it and `WBend` frees it. -/
  | wbuf
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- A pointer: an allocation and a byte offset (mod 2^64) (§3.3). -/
structure Ptr where
  blk : Blk
  off : BitVec 64
  deriving DecidableEq, Repr, Inhabited

/-- The nil pointer. -/
def Ptr.null : Ptr := ⟨.nil, 0⟩

/-- The address window of a block: offsets below it keep a pointer's concrete address inside
the block's encoding (`nil` and heap blocks `2^40`, frame blocks `2^24`; globals have no
addresses). Every allocation is smaller than its window (heap allocations at most
`Runtime.maxModelAlloc = 2^24`, frame variables below Go's 10 MB stack-variable limit), so
in-bounds and one-past-the-end pointers stay inside (§3.3). -/
def Blk.window? : Blk → Option Nat
  | .nil | .heap _ => some (2 ^ 40)
  | .local _ _ | .temp _ _ | .outargs _ => some (2 ^ 24)
  | .global _ | .wbuf => none

/-- `p`'s offset is inside its block's address window. -/
def Ptr.inWindow (p : Ptr) : Bool :=
  match p.blk.window? with
  | some w => decide (p.off.toNat < w)
  | none => true

/-- `p + k` (offset mod 2^64). -/
def Ptr.add (p : Ptr) (k : BitVec 64) : Ptr := { p with off := p.off + k }

/-! ## Concrete addresses, a parameter of the semantics -/

/-- The base addresses of #156, the instance `Addrs.fixed`: `nil` at 0, heap objects at
`(n + 1)·2^40`, the frame objects of activation `a` from `2^62` (its outgoing-arguments area at
`2^62 + a·2^42`, its variable `k` at `+ k·2^24`). Globals and the write-barrier buffer have
none. -/
def Blk.fixedBase? : Blk → Option Nat
  | .nil => some 0
  | .heap n => some ((n + 1) * 2 ^ 40)
  | .local a k | .temp a k => some (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24)
  | .outargs a => some (2 ^ 62 + a * 2 ^ 42)
  | .global _ | .wbuf => none

/-- The decoding of #156, the instance `Addrs.fixed`: the inverse of `Blk.fixedBase?` on the
encodings of heap and frame blocks; any other address points into no allocation (`Blk.nil`). -/
def Ptr.fixedOfAddr (x : BitVec 64) : Ptr :=
  let n := x.toNat
  if n < 2 ^ 40 then ⟨.nil, x⟩
  else if n < 2 ^ 62 then ⟨.heap (n / 2 ^ 40 - 1), BitVec.ofNat 64 (n % 2 ^ 40)⟩
  else
    let r := n - 2 ^ 62
    let a := r / 2 ^ 42
    let k := (r % 2 ^ 42) / 2 ^ 24
    let off := BitVec.ofNat 64 (r % 2 ^ 24)
    if k == 0 then ⟨.outargs a, off⟩ else ⟨.local a k, off⟩

/-- **Concrete addresses** (`docs/plans/proofs3.md` §8, option 2), a parameter of the semantics
(instance-implicit; every theorem holds for every instance): where each block sits (`baseOf`),
the pointer an integer word reads as (`decode`), and the caller's `SP` of an activation
(`GetCallerSP`). The nil page and the heap are fixed below `2^62` (the runtime's allocator puts
`heap n` at `(n + 1)·2^40`; `decode_low`), the addresses from `2^62` up decode to frame blocks
other than frame temporaries (`decode_high`), the frame blocks' bases are free. Every address
decodes to a pointer inside its window (`decode_inWindow`) whose address it is (`decode_addr`),
and pointer arithmetic inside a window is integer arithmetic on the address (`decode_add`): the
windows of decoded blocks tile the address space. A frame block need not be decoded at all: then
no integer converts to it (`Ptr.convertible`), as for a frame temporary. `Addrs.fixed`
(`Sem/Addrs.lean`) is the assignment of #156. -/
class Addrs where
  /-- The base address of a block. -/
  baseOf : Blk → Option Nat
  /-- The pointer at a concrete address. -/
  decode : BitVec 64 → Ptr
  /-- `GetCallerSP` of activation `act`: its caller's `SP`. -/
  callerSP : Nat → BitVec 64
  baseOf_nil : baseOf .nil = some 0
  baseOf_heap : ∀ n, baseOf (.heap n) = some ((n + 1) * 2 ^ 40)
  baseOf_global : ∀ s, baseOf (.global s) = none
  baseOf_wbuf : baseOf .wbuf = none
  decode_low : ∀ x : BitVec 64, x.toNat < 2 ^ 62 → decode x = Ptr.fixedOfAddr x
  decode_high : ∀ x : BitVec 64, 2 ^ 62 ≤ x.toNat →
    ∃ a, (decode x).blk = .outargs a ∨ ∃ k, (decode x).blk = .local a k
  decode_addr : ∀ x : BitVec 64,
    (baseOf (decode x).blk).map (fun b => BitVec.ofNat 64 b + (decode x).off) = some x
  decode_inWindow : ∀ x : BitVec 64, (decode x).inWindow = true
  decode_add : ∀ x k : BitVec 64, ((decode x).add k).inWindow = true →
    decode (x + k) = (decode x).add k

/-- The base address of a block, for `Convert` (ptr ↔ uintptr) and pointer comparison
(`Addrs.baseOf`; globals have none). -/
def Blk.base? [Addrs] (b : Blk) : Option Nat := Addrs.baseOf b

/-- The concrete address of a pointer (`none` for globals). -/
def Ptr.addr? [Addrs] (p : Ptr) : Option (BitVec 64) :=
  p.blk.base?.map fun b => BitVec.ofNat 64 b + p.off

/-- The pointer at a concrete address (`Addrs.decode`): the inverse of `Ptr.addr?` on the
decoded blocks; nil-page addresses point into no allocation (`Blk.nil`). -/
def Ptr.ofAddr [Addrs] (x : BitVec 64) : Ptr := Addrs.decode x

/-- `p` converts to an integer and back to itself: `Ptr.ofAddr` of its concrete address is `p`
(the round trip; `Ptr.convertible_ofAddr`: every pointer `Ptr.ofAddr` gives converts). Such a
pointer lies inside its window and is no frame temporary or global. Under `Addrs.fixed` that is:
inside its window, its block's number small enough for the address encoding (heap objects below
`2^22 - 1`; frames of the activations below `3·2^20`, whose addresses end below `2^64`), and not a
frame temporary (`Ptr.convertible_fixed`). -/
def Ptr.convertible [Addrs] (p : Ptr) : Bool :=
  match p.addr? with
  | some x => Ptr.ofAddr x == p
  | none => false

/-- `p` is held as a pointer at the word shapes (`Ptr.word`, `Val.hasTy`): it has no integer
form (`Ptr.convertible`: a global, a frame temporary, a block the addresses do not decode to) and
lies inside its block's window. A pointer outside its window is past the end of its allocation
(every allocation is smaller than its window, `Blk.window?`), which Go's `unsafe.Pointer` rules
forbid; it is no value (`Ptr.word` is `poison`). -/
def Ptr.held [Addrs] (p : Ptr) : Bool := !p.convertible && p.inWindow

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
  /-- An integer of any Go integer kind, or a `float32`/`float64` (P4), as a bit pattern. -/
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
  | .temp a n => s!"temp{a}.a{n}"
  | .heap n => s!"heap{n}"
  | .wbuf => "wbuf"

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
  /-- An SSA-able composite: its fields at their byte offsets, and its size (interface,
  struct, `[1]T`, complex). -/
  | agg (fields : List (Nat × Ty)) (size : Nat)
  /-- A type kept as bytes: arrays of more than one element. -/
  | blob (size : Nat)
  /-- A zero-sized type. -/
  | empty
  /-- A type of known size whose values the semantics does not decode (a struct whose field
  offsets the export lacks); loads give `poison`, stores write poison bytes. -/
  | opaque (size : Nat)
  /-- A string: its data pointer (element size 1) at offset 0 and its length (`int`) at 8;
  size 16. Its values have a nonnegative length (`Val.strOK`). -/
  | str
  /-- A slice: its data pointer (`elem` the element size) at offset 0, its length at 8 and
  its capacity at 16 (`int`s); size 24. Its values have `0 ≤ len ≤ cap` (`Val.sliceOK`). -/
  | slice (elem : Option Nat)
  deriving Inhabited, Repr

namespace Val

/-- A value of the pointer shape (`Val.hasTy _ (.ptr _)`): a 64-bit integer (the pointer at
that concrete address, §3.3), a pointer held as a pointer (`Ptr.held`: one that does not
convert to an integer, inside its window; a convertible one is held as its address,
`Ptr.word`) or `poison`. -/
def isPtrWord [Addrs] : Val → Bool
  | .ptr p => p.held
  | .int .w64 _ | .poison => true
  | _ => false

/-- The lengths of a string value (`Ty.str`, components pointer and length) are valid: the
length is a nonnegative signed `int` (sign bit clear). A `poison` length is not one. -/
def strOK : List Val → Bool
  | [_, .int .w64 l] => !l.msb
  | _ => false

/-- The lengths of a slice value (`Ty.slice`, components pointer, length, capacity) are valid:
`0 ≤ len ≤ cap` as signed `int`s. -/
def sliceOK : List Val → Bool
  | [_, .int .w64 l, .int .w64 c] => !l.msb && !c.msb && l.ule c
  | _ => false

/-- The string with components `vs`, or `poison` if they are not valid (`strOK`). -/
def ofStr (vs : List Val) : Val := if strOK vs then .agg vs else .poison

/-- The slice with components `vs`, or `poison` if they are not valid (`sliceOK`). -/
def ofSlice (vs : List Val) : Val := if sliceOK vs then .agg vs else .poison

end Val

/-- The layout of a string as an aggregate (`Ty.str` without its length invariant). -/
def Ty.strAgg : Ty := .agg [(0, .ptr (some 1)), (8, .int .w64)] 16

/-- The layout of a slice as an aggregate (`Ty.slice e` without its length invariant). -/
def Ty.sliceAgg (e : Option Nat) : Ty := .agg [(0, .ptr e), (8, .int .w64), (16, .int .w64)] 24

/-- A shape's aggregate layout: strings and slices as their aggregates, others unchanged.
Encoding, decoding and retyping at `t` are those at `t.asAgg` followed by the length check
`Val.checkLen t` (`GoFV/Proof/ValRefine.lean`). -/
def Ty.asAgg : Ty → Ty
  | .str => Ty.strAgg
  | .slice e => Ty.sliceAgg e
  | t => t

/-- The length check of a string or slice shape on a value of its aggregate layout: `poison`
unless the lengths are valid (`Val.ofStr`, `Val.ofSlice`); the identity at other shapes. -/
def Val.checkLen : Ty → Val → Val
  | .str, .agg vs => Val.ofStr vs
  | .slice _, .agg vs => Val.ofSlice vs
  | _, v => v

/-- The shape of an interface (`Sem/Layout.lean`): the type/itab word as an integer, the data
word as a pointer. -/
def Ty.iface : Ty := .agg [(0, .int .w64), (8, .ptr (some 1))] 16


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
  /-- `runtime.gopanic(v)` (P5): the bytes of the `any` argument `v` (its encoding at the
  interface shape), which `recover` returns. -/
  | value (bytes : List Byte)
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
  | .value _ => "panic value"

end Panic

end GoFV.SSA.Sem
