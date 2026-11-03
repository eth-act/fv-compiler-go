import GoFV.SSA.Sem.Val

/-!
# Memory (`docs/plans/semantics.md` §3.3, §3.4; phase P2)

Snapshots of allocations (`Mem`), concrete addresses of pointers, and typed loads and stores:
values are encoded to bytes and decoded from them by their type's shape (`Ty`, computed by
`Sem/Layout.lean`), little-endian, pointers as eight `Byte.frag`s.

Access rule (as clifv): an access of `n` bytes at `⟨blk, off⟩` is valid iff `blk` has an
allocation, `off + n ≤ size`, `off + n < 2^64` and `off + n` is inside `blk`'s address window
(`Blk.endsInWindow`). Invalid loads give `poison` (loads are pure); invalid
stores/moves/zeroes are `stuck` (the caller turns `none` into `stuck`); stores into
read-only data (`writable = false`) likewise.
-/

namespace GoFV.SSA.Sem

/-! ## Concrete addresses -/

/-- The base address of a block, for `Convert` (ptr ↔ uintptr) and pointer comparison:
`nil` at 0, heap objects at `(n + 1)·2^40`, frame objects of activation `a` from `2^62`.
Globals have no concrete address in the semantics (`none`). -/
def Blk.base? : Blk → Option Nat
  | .nil => some 0
  | .heap n => some ((n + 1) * 2 ^ 40)
  | .local a k | .temp a k => some (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24)
  | .outargs a => some (2 ^ 62 + a * 2 ^ 42)
  | .global _ | .wbuf => none

/-- The concrete address of a pointer (`none` for globals). -/
def Ptr.addr? (p : Ptr) : Option (BitVec 64) :=
  p.blk.base?.map fun b => BitVec.ofNat 64 b + p.off

/-- The pointer at a concrete address: the inverse of `Ptr.addr?` on the encodings of heap and
frame blocks; any other address points into no allocation (`Blk.nil`). -/
def Ptr.ofAddr (x : BitVec 64) : Ptr :=
  let n := x.toNat
  if n < 2 ^ 40 then ⟨.nil, x⟩
  else if n < 2 ^ 62 then ⟨.heap (n / 2 ^ 40 - 1), BitVec.ofNat 64 (n % 2 ^ 40)⟩
  else
    let r := n - 2 ^ 62
    let a := r / 2 ^ 42
    let k := (r % 2 ^ 42) / 2 ^ 24
    let off := BitVec.ofNat 64 (r % 2 ^ 24)
    if k == 0 then ⟨.outargs a, off⟩ else ⟨.local a k, off⟩

namespace Val

/-- The pointer of a pointer-shaped word: a pointer, or a 64-bit integer read as the pointer
at that concrete address (§3.3: a pointer-typed value may hold an integer word, e.g. a
`uintptr` itab word after `decompose builtin` or concrete bytes loaded at a pointer type).
Every op that dereferences, compares or offsets a pointer reads its operand through it. -/
def asPtrWord : Val → Option Ptr
  | .ptr p => some p
  | .int .w64 x => some (Ptr.ofAddr x)
  | _ => none

end Val

/-- `p` is the nil pointer (concrete address 0). -/
def Ptr.isNil (p : Ptr) : Bool := p.blk == .nil && p.off == 0

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

/-- An access of block `b` ending at offset `e` stays inside its address window (globals have
none): the bytes of a valid access are addressed by in-window pointers (`OffPtr` into it is not
`poison`, issue #151). -/
def Blk.endsInWindow (b : Blk) (e : Nat) : Bool :=
  match b.window? with
  | some w => decide (e ≤ w)
  | none => true

/-- A pointer as the word a program computes for it by address arithmetic: its concrete address
when it converts back to itself (`Ptr.convertible`, `Ptr.ofAddr_addr`), else the pointer. -/
def Ptr.word (p : Ptr) : Val :=
  match p.convertible, p.addr? with
  | true, some a => .int .w64 a
  | _, _ => .ptr p

/-- Pointer equality (`EqPtr`): the same block and offset (§3.3: pointers of different
allocations are never equal; a pointer that left its allocation is `poison`). -/
def Ptr.eq (p q : Ptr) : Bool := p.blk == q.blk && p.off == q.off

/-! ## Allocations -/

namespace Mem

/-- The allocation of block `b`. -/
def find? (m : Mem) (b : Blk) : Option Alloc :=
  (m.blocks.find? (·.1 == b)).map (·.2)

/-- Set (or add) the allocation of block `b`. -/
def set (m : Mem) (b : Blk) (a : Alloc) : Mem :=
  match m.blocks.findIdx? (·.1 == b) with
  | some i => { m with blocks := m.blocks.set! i (b, a) }
  | none => { m with blocks := m.blocks.push (b, a) }

/-- A fresh heap allocation holding `data`. -/
def allocHeap (m : Mem) (data : Array Byte) : Ptr × Mem :=
  let b := Blk.heap m.nextHeap
  (⟨b, 0⟩, { m.set b { data } with nextHeap := m.nextHeap + 1 })

/-- `n` bytes at `p`, if the access is valid (an empty access always is: Go compares and
copies zero bytes at nil pointers). A valid access ends below `2^64`: no access wraps around
the address space, as on the machine (an allocation's bytes beyond are unreachable); and it
ends inside its block's address window (`Blk.endsInWindow`). -/
def read (m : Mem) (p : Ptr) (n : Nat) : Option (Array Byte) := do
  if n == 0 then return #[]
  let a ← m.find? p.blk
  let off := p.off.toNat
  if off + n ≤ a.data.size ∧ off + n < 2 ^ 64 ∧ p.blk.endsInWindow (off + n) = true then
    some (a.data.extract off (off + n))
  else none

/-- Write `bs` at `p`, if the access is valid (in bounds, below `2^64`, inside the window, as
`read`) and the allocation writable (an empty write always is, and changes nothing). -/
def write (m : Mem) (p : Ptr) (bs : Array Byte) : Option Mem := do
  if bs.isEmpty then return m
  let a ← m.find? p.blk
  let off := p.off.toNat
  if a.writable && off + bs.size ≤ a.data.size && off + bs.size < 2 ^ 64 &&
      p.blk.endsInWindow (off + bs.size) then
    let data := (List.range bs.size).foldl (fun d i => d.set! (off + i) bs[i]!) a.data
    some (m.set p.blk { a with data })
  else none

/-- A write of `n` bytes at `p` would succeed (`write`'s conditions, whatever the bytes). -/
def canWrite (m : Mem) (p : Ptr) (n : Nat) : Bool :=
  n == 0 ||
    match m.find? p.blk with
    | some a => a.writable && p.off.toNat + n ≤ a.data.size && p.off.toNat + n < 2 ^ 64 &&
        p.blk.endsInWindow (p.off.toNat + n)
    | none => false

/-- Make every byte of block `b` poison (`VarDef`); no effect on a missing block. -/
def poisonBlock (m : Mem) (b : Blk) : Mem :=
  match m.find? b with
  | some a => m.set b { a with data := Array.replicate a.data.size .poison }
  | none => m

/-- Make the bytes of block `b` below offset `n` poison (a callee's frame in its caller's
outgoing-arguments area, `callOp`); no effect on a missing block. -/
def poisonBelow (m : Mem) (b : Blk) (n : Nat) : Mem :=
  match m.find? b with
  | some a => m.set b { a with data := a.data.mapIdx fun i x => if i < n then .poison else x }
  | none => m

/-- Remove block `b` (the frame at return: pointers into it then point into no allocation,
and which frame variables existed is not observable). -/
def free (m : Mem) (b : Blk) : Mem := { m with blocks := m.blocks.filter (·.1 != b) }

/-- `WB [n] m`: `m` with a fresh write-barrier buffer of `n` pointer-sized entries (poison). -/
def wbAlloc (m : Mem) (n : Nat) : Mem :=
  m.set .wbuf { data := Array.replicate (8 * n) .poison }

/-- `m` without the frames of activation `act` and of every later one (`Blk.local a _`,
`Blk.outargs a` with `a ≥ act`): the memory a panic of the activation `act` is compared by
(the frames of the panicking run and of its callees are not observable; the caller's frames,
which have smaller activation numbers, and the heap and globals are). -/
def dropFrames (act : Nat) (m : Mem) : Mem :=
  { m with blocks := m.blocks.filter fun (b, _) => match b with
    | .local a _ | .temp a _ | .outargs a => decide (a < act)
    | _ => true }

end Mem

/-! ## Encoding and decoding -/

/-- Size in bytes of a shape (0 for the unsized ones). -/
def Ty.size : Ty → Nat
  | .int w => w.bytes
  | .bool => 1
  | .ptr _ => 8
  | .agg _ n => n
  | .blob n => n
  | .opaque n => n
  | .str => 16
  | .slice _ => 24
  | .empty | .mem | .tuple _ | .other => 0

/-- Little-endian bytes of an integer. -/
def intBytes (n : Nat) (x : Nat) : Array Byte :=
  (List.range n).toArray.map fun i => .b (BitVec.ofNat 8 (x / 2 ^ (8 * i)))

/-- The bytes of a pointer. -/
def ptrBytes (p : Ptr) : Array Byte := (List.range 8).toArray.map fun i => .frag p i

/-- The concrete value of little-endian bytes, if all are concrete. -/
def bytesNat? (bs : Array Byte) : Option Nat :=
  bs.foldr (fun b acc => match b, acc with
    | .b x, some n => some (x.toNat + 256 * n)
    | _, _ => none) (some 0)

/-- The pointer stored in 8 bytes, if they are its eight fragments in order. -/
def bytesPtr? (bs : Array Byte) : Option Ptr :=
  match (bs[0]? : Option Byte) with
  | some (.frag p 0) =>
    if bs.size == 8 && (List.range 8).all (fun i => (bs[i]? : Option Byte) == some (.frag p i)) then some p
    else none
  | _ => none

/-- An integer of width `w` from its bytes: concrete bytes, or (64-bit) the word of a stored
pointer (`Ptr.word`, §3.2: its concrete address if it converts back to itself; else the pointer,
e.g. a `uintptr` holding a closure's code word, a global without a concrete address); otherwise
`poison`. -/
def decodeInt (w : Width) (bs : Array Byte) : Val :=
  match bytesNat? bs with
  | some n => .int w (BitVec.ofNat w.bits n)
  | none =>
    match w, bytesPtr? bs with
    | .w64, some p => p.word
    | _, _ => .poison

/-- A pointer word from 8 bytes: a stored pointer from its fragments, as its word (`Ptr.word`:
its address if it converts back to itself, §3.2), concrete bytes as the 64-bit integer they hold
(the pointer at that address, `Val.asPtrWord`, §3.3), so a word loads back as it was stored. -/
def decodePtr (bs : Array Byte) : Val :=
  match bytesPtr? bs with
  | some p => p.word
  | none => match bytesNat? bs with
    | some n => .int .w64 (BitVec.ofNat 64 n)
    | none => .poison

mutual
/-- The value of shape `t` stored at `off` in `bs`. -/
def decode (bs : Array Byte) (off : Nat) : Ty → Val
  | .int w => decodeInt w (bs.extract off (off + w.bytes))
  | .bool => match bs[off]? with
    | some (.b x) => if x.toNat ≤ 1 then .bool (x == 1) else .poison
    | _ => .poison
  | .ptr _ => decodePtr (bs.extract off (off + 8))
  | .agg fs _ => .agg (decodeFields bs off fs)
  | .blob n => .blob (bs.extract off (off + n)).toList
  | .empty => .empty
  | .str => Val.ofStr [decodePtr (bs.extract off (off + 8)),
      decodeInt .w64 (bs.extract (off + 8) (off + 16))]
  | .slice _ => Val.ofSlice [decodePtr (bs.extract off (off + 8)),
      decodeInt .w64 (bs.extract (off + 8) (off + 16)),
      decodeInt .w64 (bs.extract (off + 16) (off + 24))]
  | .opaque _ | .other | .mem | .tuple _ => .poison
def decodeFields (bs : Array Byte) (off : Nat) : List (Nat × Ty) → List Val
  | [] => []
  | (o, t) :: fs => decode bs (off + o) t :: decodeFields bs off fs
end

/-- Write `src` into `dst` at `off` (bytes beyond `dst` are dropped). -/
def putBytes (dst : Array Byte) (off : Nat) (src : Array Byte) : Array Byte :=
  (List.range src.size).foldl (fun d i => if off + i < d.size then d.set! (off + i) src[i]! else d) dst

/-- The 8 bytes of a word-sized value: `encode` at `.ptr _` and at `.int .w64` (both store a
pointer as its fragments and a 64-bit integer as its bytes). -/
def encodeWord : Val → Array Byte
  | .int .w64 x => intBytes 8 x.toNat
  | .ptr p => ptrBytes p
  | .blob bs => if bs.length == 8 then bs.toArray else Array.replicate 8 .poison
  | _ => Array.replicate 8 .poison

/-- The words `vs` written into `buf` at the offsets `os` (as `encodeFields` at word fields:
the string and slice components). -/
def encodeWords (buf : Array Byte) : List Nat → List Val → Array Byte
  | o :: os, v :: vs => encodeWords (putBytes buf o (encodeWord v)) os vs
  | _, _ => buf

mutual
/-- The bytes of value `v` stored as shape `t` (exactly `t.size` bytes): `poison` bytes for
`poison`, for padding, and for a value of another shape. An integer of another width stores its
low bytes, zero-extended, and a boolean at an integer shape 0 or 1, as `Val.retype` reads them
(lowered code, `docs/plans/semantics2.md` §3). -/
def encode : Ty → Val → Array Byte
  | .int w, .int _ x => intBytes w.bytes x.toNat
  | .int w, .bool b => intBytes w.bytes (if b then 1 else 0)
  | .int .w64, .ptr p => ptrBytes p
  | .bool, .bool b => #[.b (if b then 1 else 0)]
  | .ptr _, .ptr p => ptrBytes p
  | .ptr _, .int .w64 x => intBytes 8 x.toNat
  | .agg fs n, .agg vs => encodeFields (Array.replicate n .poison) fs vs
  | .str, .agg vs => encodeWords (Array.replicate 16 .poison) [0, 8] vs
  | .slice _, .agg vs => encodeWords (Array.replicate 24 .poison) [0, 8, 16] vs
  | t, .blob bs => if bs.length == t.size then bs.toArray else Array.replicate t.size .poison
  | t, _ => Array.replicate t.size .poison
def encodeFields (buf : Array Byte) : List (Nat × Ty) → List Val → Array Byte
  | (o, t) :: fs, v :: vs => encodeFields (putBytes buf o (encode t v)) fs vs
  | _, _ => buf
end

/-- The `n > 0` bytes of `bs` at `off` are all `poison`. -/
def allPoison (bs : Array Byte) (off n : Nat) : Bool :=
  n != 0 && (bs.extract off (off + n)).all (· matches .poison)

mutual
/-- The value of shape `t` that a `Load` reads at `off` in `bs`: `decode`, except that an
aggregate whose (non-empty) bytes are all `poison` is `poison`, at every aggregate level (§3.4).
A stored `poison` aggregate so loads back as `poison`. -/
def decodeLoad (bs : Array Byte) (off : Nat) : Ty → Val
  | .agg fs n => if allPoison bs off n then .poison else .agg (decodeLoadFields bs off fs)
  | .int w => decode bs off (.int w)
  | .bool => decode bs off .bool
  | .ptr e => decode bs off (.ptr e)
  | .blob n => decode bs off (.blob n)
  | .empty => .empty
  | .opaque n => decode bs off (.opaque n)
  | .other => .poison
  | .mem => .poison
  | .tuple _ => .poison
  | .str => if allPoison bs off 16 then .poison else decode bs off .str
  | .slice e => if allPoison bs off 24 then .poison else decode bs off (.slice e)
def decodeLoadFields (bs : Array Byte) (off : Nat) : List (Nat × Ty) → List Val
  | [] => []
  | (o, t) :: fs => decodeLoad bs (off + o) t :: decodeLoadFields bs off fs
end

namespace Mem

/-- `Load <T> p m`: the value of shape `t` at `p` in snapshot `m` (`decodeLoad`); `poison` if
the access is invalid (§3.4). -/
def load (m : Mem) (t : Ty) (p : Ptr) : Val :=
  match t with
  | .empty => .empty
  | .other | .mem | .tuple _ => .poison
  | t => match m.read p t.size with
    | some bs => decodeLoad bs 0 t
    | none => .poison

end Mem

end GoFV.SSA.Sem
