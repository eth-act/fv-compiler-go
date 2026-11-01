import GoFV.Opt.RewriteCheck

/-!
# memcombine's checker: values as symbolic bytes (issue #35)

`symOf tabs D n x` describes the integer value of `x` (definitions `D`, fuel `n`) as its
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

/-- The bytes of `v`'s op result (`wt`: the width of `v`'s type; `rec`: the description of an
argument; `ld`: look into `Load`s, else they are opaque). -/
def symOp (tabs : Tables) (D : Defs) (ld : Bool) (rec : ID → Option (List SB × List LoadRec))
    (v : Value) (wt : Sem.Width) : Option (List SB × List LoadRec) :=
  let arg (i : Nat) (w : Sem.Width) : Option (List SB × List LoadRec) :=
    match v.args[i]? with
    | some a => (rec a).bind fun (bs, sd) =>
        if bs.length = w.bytes then some (bs, sd) else none
    | none => none
  if let some w := constW v.op then
    if v.args.size = 0 then some (litBytes w.bytes v.auxInt.toInt, []) else none
  else if v.op = .Copy then
    if v.args.size = 1 then rec v.args[0]! else none
  else if v.op = .Load then
    if ld && v.args.size = 2 then
      let p := v.args[0]!
      let (b, i, o) := splitP tabs D 64 p none 0
      if ptrTyped tabs D b then
        some ((List.range wt.bytes).map fun (k : Nat) => .mb v.args[1]! b i (o + (k : Int)),
          [⟨p, v.args[1]!, b, i, o, wt.bytes⟩])
      else none
    else none
  else if let some (w, w') := zextW v.op then
    if v.args.size = 1 then (arg 0 w).map fun (bs, sd) => (bs ++ zeros (w'.bytes - w.bytes), sd)
    else none
  else if let some (w, w') := truncW v.op then
    if v.args.size = 1 then (arg 0 w).map fun (bs, sd) => (bs.take w'.bytes, sd) else none
  else if let some w := lshW v.op then
    if v.args.size = 2 then
      match shiftBytes tabs D w v.args[1]! with
      | some k => (arg 0 w).map fun (bs, sd) => (zeros k ++ bs.take (w.bytes - k), sd)
      | none => none
    else none
  else if let some w := rshuW v.op then
    if v.args.size = 2 then
      match shiftBytes tabs D w v.args[1]! with
      | some k => (arg 0 w).map fun (bs, sd) => (bs.drop k ++ zeros k, sd)
      | none => none
    else none
  else if let some w := bswapW v.op then
    if v.args.size = 1 then (arg 0 w).map fun (bs, sd) => (bs.reverse, sd) else none
  else if let some w := orW v.op then
    if v.args.size = 2 then do
      let (a, sa) ← arg 0 w
      let (b, sb) ← arg 1 w
      let c ← orBytes a b
      return (c, sa ++ sb)
    else none
  else none

/-- The bytes of `x`'s value at its type's integer width, and the pointers of the loads read. -/
def symOf (tabs : Tables) (D : Defs) (ld : Bool) : Nat → ID → Option (List SB × List LoadRec)
  | 0, _ => none
  | n + 1, x =>
    match D x with
    | none => none
    | some v =>
      match intW (tabs.ty v.type) with
      | none => none
      | some wt =>
        match (symOp tabs D ld (symOf tabs D ld n) v wt).bind fun (bs, sd) =>
            if wt.bytes ≤ bs.length then some (bs.take wt.bytes, sd) else none with
        | some r => some r
        | none => some ((List.range wt.bytes).map (.vb x), [])

/-- The values a description reads: opaque values, memories, bases and indices. -/
def SB.ids : SB → List ID
  | .lit _ => []
  | .vb x _ => [x]
  | .mb m b i _ => [m, b] ++ i.toList

/-- The opaque values of a description (`vb`). -/
def SB.vbId? : SB → Option ID
  | .vb x _ => some x
  | _ => none

/-- `s` reads memory (`mb`). -/
def SB.isMb : SB → Bool
  | .mb .. => true
  | _ => false

end GoFV.Opt.MemCombine.Check
