import GoFV.SSA.Sem.Val

/-!
# Memory (`docs/plans/semantics.md` §3.3, §3.4; phase P2)

Snapshots of allocations (`Mem`), concrete addresses of pointers, and typed loads and stores:
values are encoded to bytes and decoded from them by their type's shape (`Ty`, computed by
`Sem/Layout.lean`), little-endian, pointers as eight `Byte.frag`s.

Access rule (as clifv): an access of `n` bytes at `⟨blk, off⟩` is valid iff `blk` has an
allocation and `off + n ≤ size`. Invalid loads give `poison` (loads are pure); invalid
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
  | .local a k => some (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24)
  | .outargs a => some (2 ^ 62 + a * 2 ^ 42)
  | .global _ => none

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

/-- `p` is the nil pointer (concrete address 0). -/
def Ptr.isNil (p : Ptr) : Bool := p.blk == .nil && p.off == 0

/-- Pointer equality (`EqPtr`): same allocation and offset, or equal concrete addresses. Two
different globals, or a global and another block, are different. -/
def Ptr.eq (p q : Ptr) : Bool :=
  if p.blk == q.blk then p.off == q.off
  else match p.addr?, q.addr? with
    | some a, some b => a == b
    | _, _ => false

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
copies zero bytes at nil pointers). -/
def read (m : Mem) (p : Ptr) (n : Nat) : Option (Array Byte) := do
  if n == 0 then return #[]
  let a ← m.find? p.blk
  let off := p.off.toNat
  if off + n ≤ a.data.size then some (a.data.extract off (off + n)) else none

/-- Write `bs` at `p`, if the access is valid and the allocation writable (an empty write
always is, and changes nothing). -/
def write (m : Mem) (p : Ptr) (bs : Array Byte) : Option Mem := do
  if bs.isEmpty then return m
  let a ← m.find? p.blk
  let off := p.off.toNat
  if a.writable && off + bs.size ≤ a.data.size then
    let data := (List.range bs.size).foldl (fun d i => d.set! (off + i) bs[i]!) a.data
    some (m.set p.blk { a with data })
  else none

/-- Make every byte of block `b` poison (`VarDef`); no effect on a missing block. -/
def poisonBlock (m : Mem) (b : Blk) : Mem :=
  match m.find? b with
  | some a => m.set b { a with data := Array.replicate a.data.size .poison }
  | none => m

/-- Remove block `b` (the frame at return: pointers into it then point into no allocation,
and which frame variables existed is not observable). -/
def free (m : Mem) (b : Blk) : Mem := { m with blocks := m.blocks.filter (·.1 != b) }

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

/-- An integer of width `w` from its bytes: concrete bytes, or (64-bit) the concrete address
of a stored pointer; a stored pointer to a global, which has no concrete address, stays a
pointer (a `uintptr` holding a code or data address, e.g. a closure's code word); otherwise
`poison`. -/
def decodeInt (w : Width) (bs : Array Byte) : Val :=
  match bytesNat? bs with
  | some n => .int w (BitVec.ofNat w.bits n)
  | none =>
    match w, bytesPtr? bs with
    | .w64, some p => match p.addr? with
      | some a => .int .w64 a
      | none => .ptr p
    | _, _ => .poison

/-- A pointer from 8 bytes: its fragments, or a concrete address. -/
def decodePtr (bs : Array Byte) : Val :=
  match bytesPtr? bs with
  | some p => .ptr p
  | none => match bytesNat? bs with
    | some n => .ptr (Ptr.ofAddr (BitVec.ofNat 64 n))
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
  | .opaque _ | .other | .mem | .tuple _ => .poison
def decodeFields (bs : Array Byte) (off : Nat) : List (Nat × Ty) → List Val
  | [] => []
  | (o, t) :: fs => decode bs (off + o) t :: decodeFields bs off fs
end

/-- Write `src` into `dst` at `off` (bytes beyond `dst` are dropped). -/
def putBytes (dst : Array Byte) (off : Nat) (src : Array Byte) : Array Byte :=
  (List.range src.size).foldl (fun d i => if off + i < d.size then d.set! (off + i) src[i]! else d) dst

mutual
/-- The bytes of value `v` stored as shape `t` (exactly `t.size` bytes): `poison` bytes for
`poison`, for padding, and for a value of another shape. -/
def encode : Ty → Val → Array Byte
  | .int w, .int w' x => if w' == w then intBytes w.bytes x.toNat else Array.replicate w.bytes .poison
  | .int .w64, .ptr p => ptrBytes p
  | .bool, .bool b => #[.b (if b then 1 else 0)]
  | .ptr _, .ptr p => ptrBytes p
  | .ptr _, .int .w64 x => intBytes 8 x.toNat
  | .agg fs n, .agg vs => encodeFields (Array.replicate n .poison) fs vs
  | t, .blob bs => if bs.length == t.size then bs.toArray else Array.replicate t.size .poison
  | t, _ => Array.replicate t.size .poison
def encodeFields (buf : Array Byte) : List (Nat × Ty) → List Val → Array Byte
  | (o, t) :: fs, v :: vs => encodeFields (putBytes buf o (encode t v)) fs vs
  | _, _ => buf
end

namespace Mem

/-- `Load <T> p m`: the value of shape `t` at `p` in snapshot `m`; `poison` if the access is
invalid (§3.4). -/
def load (m : Mem) (t : Ty) (p : Ptr) : Val :=
  match t with
  | .empty => .empty
  | .other | .mem | .tuple _ => .poison
  | t => match m.read p t.size with
    | some bs => decode bs 0 t
    | none => .poison

end Mem

end GoFV.SSA.Sem
