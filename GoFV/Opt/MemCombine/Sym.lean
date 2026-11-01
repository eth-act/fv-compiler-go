import GoFV.Opt.RewriteCheck

/-!
# memcombine's checker: values as symbolic bytes (issue #35)

`symOf tabs D tgt wide n x` describes the integer value of `x` (definitions `D`, fuel `n`) as its
little-endian bytes (`SB`): constant bytes, byte `k` of an opaque integer value (`vb`), or the
byte at `base + idx + off` of a memory value (`mb`, from a `Load` whose pointer `splitP` takes
apart). It follows the ops `memcombine` builds and matches — constants, `Copy`, `Load`,
`ZeroExt`, `Trunc`, `Lsh`/`Rsh…U` by a constant multiple of 8, `Bswap`, `Or` of values whose
bytes do not overlap — and treats any other integer value as opaque. The side list holds the
`Load`s it went through (`LoadRec`: pointer, memory, the split pointer, size): a wide load of
the target is valid when loads of the source cover its bytes (`MemCombine.Check.rootOK`).

The proof reads `symOf` both ways (`GoFV.Proof.MemCombine`): a source value that is an integer
has the bytes its description names (soundness), and a target value whose bytes are all defined
is the integer of those bytes (completeness), so equal descriptions refine.
-/

namespace GoFV.Opt.MemCombine.Check

open GoFV.SSA

/-- A symbolic byte. -/
inductive SB where
  /-- A constant byte. -/
  | lit (b : BitVec 8)
  /-- Byte `k` (little-endian) of the integer value `x`. -/
  | vb (x : ID) (k : Nat)
  /-- The byte at `base + idx + off` in the memory value `m`. -/
  | mb (m base : ID) (idx : Option ID) (off : Int)
  deriving DecidableEq, Repr, Inhabited

/-- Definitions of values. -/
abbrev Defs := ID → Option Value

/-- A `Load` a description reads through: its pointer and memory, the pointer split into
`base + idx + off`, and its size in bytes. -/
structure LoadRec where
  ptr : ID
  mem : ID
  base : ID
  idx : Option ID
  off : Int
  size : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The definitions of the values listed in `h` (`GoFV.Proof.Term.listedDefs`). -/
def listedD (h : Func) (x : ID) : Option Value :=
  (h.value? x).filter fun v => h.blocks.contains v.block && (h.block? v.block).any (·.values.contains x)

/-- Byte `k` (little-endian) of the natural number `x`. -/
def byteOf (x k : Nat) : BitVec 8 := BitVec.ofNat 8 (x / 2 ^ (8 * k))

/-- The `n` little-endian bytes of the `8n`-bit two's complement of `c`. -/
def litBytes (n : Nat) (c : Int) : List SB :=
  (List.range n).map fun k => .lit (byteOf (BitVec.ofInt (8 * n) c).toNat k)

/-- `n` zero bytes. -/
def zeros (n : Nat) : List SB := List.replicate n (.lit 0)

/-- The `Or` of two symbolic bytes, if one of them is zero (or both are constants). -/
def orSB (a b : SB) : Option SB :=
  match a, b with
  | .lit x, .lit y => some (.lit (x ||| y))
  | .lit x, b => if x = 0 then some b else none
  | a, .lit y => if y = 0 then some a else none
  | _, _ => none

/-- Bytewise `Or` of two descriptions of the same length. -/
def orBytes : List SB → List SB → Option (List SB)
  | [], [] => some []
  | a :: as, b :: bs => do
    let c ← orSB a b
    let cs ← orBytes as bs
    return c :: cs
  | _, _ => none

/-- The integer width of a shape. -/
def intW : Sem.Ty → Option Sem.Width
  | .int w => some w
  | _ => none

/-- `x`'s type is a pointer shape. -/
def ptrTyped (tabs : Tables) (D : Defs) (x : ID) : Bool :=
  match D x with
  | some v => match tabs.ty v.type with
    | .ptr _ => true
    | _ => false
  | none => false

/-- The constant of a `Const64` with a 64-bit shape. -/
def const64 (tabs : Tables) (D : Defs) (x : ID) : Option Int :=
  match D x with
  | some v =>
    if v.op == .Const64 && intW (tabs.ty v.type) == some .w64 then some v.auxInt.toInt else none
  | none => none

/-- `Add64 (Const64 c) j` or `Add64 j (Const64 c)` with a 64-bit shape: `(c, j)`. -/
def addConst (tabs : Tables) (D : Defs) (y : ID) : Option (Int × ID) :=
  match D y with
  | some v =>
    if v.op == .Add64 && v.args.size == 2 && intW (tabs.ty v.type) == some .w64 then
      match const64 tabs D v.args[0]!, const64 tabs D v.args[1]! with
      | some c, _ => some (c, v.args[1]!)
      | none, some c => some (c, v.args[0]!)
      | none, none => none
    else none
  | none => none

/-- `p` as `base + idx + off`: through pointer-typed `OffPtr`s and one pointer-typed `AddPtr`
(whose index loses an added `Const64`). -/
def splitP (tabs : Tables) (D : Defs) : Nat → ID → Option ID → Int → ID × Option ID × Int
  | 0, p, i, o => (p, i, o)
  | n + 1, p, i, o =>
    match D p with
    | some v =>
      if !ptrTyped tabs D p then (p, i, o)
      else if v.op == .OffPtr && v.args.size == 1 then
        splitP tabs D n v.args[0]! i (o + v.auxInt.toInt)
      else if v.op == .AddPtr && v.args.size == 2 && i.isNone then
        match addConst tabs D v.args[1]! with
        | some (c, j) => splitP tabs D n v.args[0]! (some j) (o + c)
        | none => splitP tabs D n v.args[0]! (some v.args[1]!) o
      else (p, i, o)
    | none => (p, i, o)

/-- `ZeroExt` ops: from and to widths. -/
def zextW : Op → Option (Sem.Width × Sem.Width)
  | .ZeroExt8to16 => some (.w8, .w16) | .ZeroExt8to32 => some (.w8, .w32)
  | .ZeroExt8to64 => some (.w8, .w64) | .ZeroExt16to32 => some (.w16, .w32)
  | .ZeroExt16to64 => some (.w16, .w64) | .ZeroExt32to64 => some (.w32, .w64)
  | _ => none

/-- `Trunc` ops: from and to widths. -/
def truncW : Op → Option (Sem.Width × Sem.Width)
  | .Trunc16to8 => some (.w16, .w8) | .Trunc32to8 => some (.w32, .w8)
  | .Trunc32to16 => some (.w32, .w16) | .Trunc64to8 => some (.w64, .w8)
  | .Trunc64to16 => some (.w64, .w16) | .Trunc64to32 => some (.w64, .w32)
  | _ => none

/-- `Lsh{w}x64` ops. -/
def lshW : Op → Option Sem.Width
  | .Lsh8x64 => some .w8 | .Lsh16x64 => some .w16 | .Lsh32x64 => some .w32
  | .Lsh64x64 => some .w64
  | _ => none

/-- `Rsh{w}Ux64` ops. -/
def rshuW : Op → Option Sem.Width
  | .Rsh8Ux64 => some .w8 | .Rsh16Ux64 => some .w16 | .Rsh32Ux64 => some .w32
  | .Rsh64Ux64 => some .w64
  | _ => none

/-- `Bswap` ops. -/
def bswapW : Op → Option Sem.Width
  | .Bswap16 => some .w16 | .Bswap32 => some .w32 | .Bswap64 => some .w64
  | _ => none

/-- `Or` ops. -/
def orW : Op → Option Sem.Width
  | .Or8 => some .w8 | .Or16 => some .w16 | .Or32 => some .w32 | .Or64 => some .w64
  | _ => none

/-- `Const` ops. -/
def constW : Op → Option Sem.Width
  | .Const8 => some .w8 | .Const16 => some .w16 | .Const32 => some .w32 | .Const64 => some .w64
  | _ => none

/-- A shift amount: a `Const64` multiple of 8 below `w`, in bytes. -/
def shiftBytes (tabs : Tables) (D : Defs) (w : Sem.Width) (s : ID) : Option Nat :=
  match const64 tabs D s with
  | some c => if 0 ≤ c ∧ c % 8 = 0 ∧ c < w.bits then some (c / 8).toNat else none
  | none => none

/-- The values a description reads: opaque values, memories, bases and indices. -/
def SB.ids : SB → List ID
  | .lit _ => []
  | .vb x _ => [x]
  | .mb m b i _ => [m, b] ++ i.toList

/-- The opaque values of a description (`vb`). -/
def SB.vbId? : SB → Option ID
  | .vb x _ => some x
  | _ => none

/-- The opaque values of a description's `vb` bytes. -/
def vbIds (bs : List SB) : List ID := bs.filterMap SB.vbId?

/-- `s` reads memory (`mb`). -/
def SB.isMb : SB → Bool
  | .mb .. => true
  | _ => false

/-- A description: symbolic bytes and the loads they read through. -/
abbrev Desc := List SB × List LoadRec

/-- The description of the argument `a`, if it has `w`'s bytes. -/
def symArg (rec : ID → Option Desc) (a : ID) (w : Sem.Width) : Option Desc :=
  (rec a).bind fun r => if r.1.length = w.bytes then some r else none

/-- The bytes `kept` (with the loads `sd`) of a description that drops `dropped`; the target
(`tgt`) drops an opaque value's byte only if it keeps a byte of the same value. -/
def keepB (tgt : Bool) (kept dropped : List SB) (sd : List LoadRec) : Option Desc :=
  if !tgt || (vbIds dropped).all (vbIds kept).contains then some (kept, sd) else none

/-- A `Load` of `wt`'s bytes through a pointer `splitP` takes apart (8-byte loads only if
`wide`). -/
def symLoad (tabs : Tables) (D : Defs) (wide : Bool) (v : Value) (wt : Sem.Width) : Option Desc :=
  if v.args.size = 2 && (wide || wt.bytes < 8) then
    let s := splitP tabs D 64 v.args[0]! none 0
    if ptrTyped tabs D s.1 then
      some ((List.range wt.bytes).map fun (k : Nat) => .mb v.args[1]! s.1 s.2.1 (s.2.2 + (k : Int)),
        [⟨v.args[0]!, v.args[1]!, s.1, s.2.1, s.2.2, wt.bytes⟩])
    else none
  else none

/-- `Lsh` by `k` bytes. -/
def symLsh (tabs : Tables) (D : Defs) (tgt : Bool) (rec : ID → Option Desc) (w : Sem.Width)
    (v : Value) : Option Desc :=
  if v.args.size = 2 then
    match shiftBytes tabs D w v.args[1]! with
    | some k => (symArg rec v.args[0]! w).bind fun r =>
      keepB tgt (zeros k ++ r.1.take (w.bytes - k)) (r.1.drop (w.bytes - k)) r.2
    | none => none
  else none

/-- `Rsh…U` by `k` bytes. -/
def symRsh (tabs : Tables) (D : Defs) (tgt : Bool) (rec : ID → Option Desc) (w : Sem.Width)
    (v : Value) : Option Desc :=
  if v.args.size = 2 then
    match shiftBytes tabs D w v.args[1]! with
    | some k => (symArg rec v.args[0]! w).bind fun r => keepB tgt (r.1.drop k ++ zeros k) (r.1.take k) r.2
    | none => none
  else none

/-- `Or` of byte-disjoint operands. -/
def symOr (rec : ID → Option Desc) (w : Sem.Width) (v : Value) : Option Desc :=
  if v.args.size = 2 then
    (symArg rec v.args[0]! w).bind fun a => (symArg rec v.args[1]! w).bind fun b =>
      (orBytes a.1 b.1).map fun c => (c, a.2 ++ b.2)
  else none

/-- The bytes of `v`'s op result (`wt`: the width of `v`'s type; `rec`: the description of an
argument). `tgt` (the target's descriptions): drop an opaque value's byte (`Trunc`, shifts, a
narrower type) only while keeping another byte of it, so a description whose bytes are defined
has every opaque value it reads defined at its full width. `wide`: look into `Load`s of every
size; otherwise only into `Load`s narrower than 8 bytes (an 8-byte load of a pointer's bytes is
an integer without concrete bytes, so the source's descriptions are not `wide`). -/
def symOp (tabs : Tables) (D : Defs) (tgt wide : Bool) (rec : ID → Option Desc) (v : Value)
    (wt : Sem.Width) : Option Desc :=
  if let some w := constW v.op then
    if v.args.size = 0 then some (litBytes w.bytes v.auxInt.toInt, []) else none
  else if v.op = .Copy then
    if v.args.size = 1 then rec v.args[0]! else none
  else if v.op = .Load then symLoad tabs D wide v wt
  else if let some (w, w') := zextW v.op then
    if v.args.size = 1 then
      (symArg rec v.args[0]! w).map fun r => (r.1 ++ zeros (w'.bytes - w.bytes), r.2)
    else none
  else if let some (w, w') := truncW v.op then
    if v.args.size = 1 then
      (symArg rec v.args[0]! w).bind fun r => keepB tgt (r.1.take w'.bytes) (r.1.drop w'.bytes) r.2
    else none
  else if let some w := lshW v.op then symLsh tabs D tgt rec w v
  else if let some w := rshuW v.op then symRsh tabs D tgt rec w v
  else if let some w := bswapW v.op then
    if v.args.size = 1 then (symArg rec v.args[0]! w).map fun r => (r.1.reverse, r.2) else none
  else if let some w := orW v.op then symOr rec w v
  else none

/-- The bytes of `x`'s value at its type's integer width, and the pointers of the loads read. -/
def symOf (tabs : Tables) (D : Defs) (tgt wide : Bool) : Nat → ID → Option Desc
  | 0, _ => none
  | n + 1, x =>
    match D x with
    | none => none
    | some v =>
      match intW (tabs.ty v.type) with
      | none => none
      | some wt =>
        match (symOp tabs D tgt wide (symOf tabs D tgt wide n) v wt).bind fun r =>
            if wt.bytes ≤ r.1.length then keepB tgt (r.1.take wt.bytes) (r.1.drop wt.bytes) r.2
            else none with
        | some r => some r
        | none => some ((List.range wt.bytes).map (.vb x), [])

end GoFV.Opt.MemCombine.Check
