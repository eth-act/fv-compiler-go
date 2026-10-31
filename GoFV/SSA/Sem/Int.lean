import GoFV.SSA.Sem.Val

/-!
# Integer arithmetic and bit operations (`docs/plans/semantics.md` §4.1, §4.2)

Each family is a function on argument lists of `Val`s. Arguments of the wrong shape (or
`poison`) give `poison`: well-typed SSA never has the former, and pure ops propagate the latter
(§3.5). The partial ops (division by zero, a broken "not −1" promise, `Ctz*NonZero` of 0,
`Avg64u` with `x < y`, `Div128u` overflow, a carry that is not 0/1) also give `poison`.

Families are separate definitions so that a rule lemma unfolds only its own.
-/

namespace GoFV.SSA.Sem

namespace Val

/-- The bits of an integer of width `w`. -/
def asInt (w : Width) : Val → Option (BitVec w.bits)
  | .int w' x => if h : w' = w then some (h ▸ x) else none
  | _ => none

/-- The unsigned value of an integer of any width. -/
def asNat : Val → Option Nat
  | .int _ x => some x.toNat
  | _ => none

@[simp] theorem asInt_int (w : Width) (x : BitVec w.bits) : (Val.int w x).asInt w = some x := by
  simp [asInt]

end Val

/-- A unary op of width `w`. -/
@[inline] def int1 (w : Width) (f : BitVec w.bits → Val) : List Val → Val
  | [a] => match a.asInt w with
    | some x => f x
    | none => .poison
  | _ => .poison

/-- A binary op whose arguments both have width `w`. -/
@[inline] def int2 (w : Width) (f : BitVec w.bits → BitVec w.bits → Val) : List Val → Val
  | [a, b] => match a.asInt w, b.asInt w with
    | some x, some y => f x y
    | _, _ => .poison
  | _ => .poison

/-- A ternary op whose arguments all have width `w`. -/
@[inline] def int3 (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val) :
    List Val → Val
  | [a, b, c] => match a.asInt w, b.asInt w, c.asInt w with
    | some x, some y, some z => f x y z
    | _, _, _ => .poison
  | _ => .poison

namespace Int

/-- `Add`, `Sub`, `Mul`, `And`, `Or`, `Xor` of width `w`. -/
def add (w : Width) : List Val → Val := int2 w fun x y => .int w (x + y)
def sub (w : Width) : List Val → Val := int2 w fun x y => .int w (x - y)
def mul (w : Width) : List Val → Val := int2 w fun x y => .int w (x * y)
def and (w : Width) : List Val → Val := int2 w fun x y => .int w (x &&& y)
def or (w : Width) : List Val → Val := int2 w fun x y => .int w (x ||| y)
def xor (w : Width) : List Val → Val := int2 w fun x y => .int w (x ^^^ y)
def neg (w : Width) : List Val → Val := int1 w fun x => .int w (-x)
def com (w : Width) : List Val → Val := int1 w fun x => .int w (~~~x)

/-- `Hmul32`/`Hmul64` (`signed`) and `Hmul32u`/`Hmul64u`: the high half of the double-width
product. -/
def hmul (w : Width) (signed : Bool) : List Val → Val := int2 w fun x y =>
  let n := w.bits
  let p : BitVec (2 * n) :=
    if signed then x.signExtend (2 * n) * y.signExtend (2 * n)
    else x.setWidth (2 * n) * y.setWidth (2 * n)
  .int w (p.extractLsb' n n)

/-- `Mul32uhilo`/`Mul64uhilo`: `(hi, lo)` of the unsigned double-width product. -/
def mulhilo (w : Width) : List Val → Val := int2 w fun x y =>
  let n := w.bits
  let p : BitVec (2 * n) := x.setWidth (2 * n) * y.setWidth (2 * n)
  .tuple [.int w (p.extractLsb' n n), .int w (p.extractLsb' 0 n)]

/-- `Mul32uover`/`Mul64uover`: `(lo, overflowed)` of the unsigned product. -/
def mulover (w : Width) : List Val → Val := int2 w fun x y =>
  .tuple [.int w (x * y), .bool (decide (2 ^ w.bits ≤ x.toNat * y.toNat))]

/-- `Avg64u x y` = `⌊(x + y) / 2⌋` without overflow; the op may assume `x ≥ y` (gO 65). -/
def avgu (w : Width) : List Val → Val := int2 w fun x y =>
  if x.toNat < y.toNat then .poison
  else .int w (BitVec.ofNat w.bits ((x.toNat + y.toNat) / 2))

/-- Signed division (`Div8` … `Div64`), truncated, `MIN / −1 = MIN`. `notMinusOne` is the
auxint promise of `Div16/32/64` (divisor ≠ −1 or dividend ≠ MIN); broken ⇒ `poison`. -/
def divs (w : Width) (notMinusOne : Bool) : List Val → Val := int2 w fun x y =>
  if y = 0 then .poison
  else if notMinusOne && x = BitVec.intMin w.bits && y = -1 then .poison
  else .int w (x.sdiv y)

/-- Unsigned division. -/
def divu (w : Width) : List Val → Val := int2 w fun x y =>
  if y = 0 then .poison else .int w (x / y)

/-- Signed remainder (sign of the dividend), `MIN % −1 = 0`. `notMinusOne` is the auxint
promise of `Mod16/32/64` (divisor ≠ −1). -/
def mods (w : Width) (notMinusOne : Bool) : List Val → Val := int2 w fun x y =>
  if y = 0 then .poison
  else if notMinusOne && y = -1 then .poison
  else .int w (x.srem y)

/-- Unsigned remainder. -/
def modu (w : Width) : List Val → Val := int2 w fun x y =>
  if y = 0 then .poison else .int w (x % y)

/-- `Div128u hi lo y` = `(q, r)` of the 128-bit dividend `hi:lo`; `y = 0` or `hi ≥ y` (quotient
overflow) ⇒ `poison` (`math/bits.Div64` panics before). -/
def div128u : List Val → Val := int3 .w64 fun hi lo y =>
  if y.toNat = 0 ∨ y.toNat ≤ hi.toNat then .poison
  else
    let n := hi.toNat * 2 ^ 64 + lo.toNat
    .tuple [.i64 (BitVec.ofNat 64 (n / y.toNat)), .i64 (BitVec.ofNat 64 (n % y.toNat))]

/-- `Add64carry x y c` = `(x + y + c, carry)`; `c ∉ {0, 1}` ⇒ `poison`. -/
def addcarry : List Val → Val := int3 .w64 fun x y c =>
  if 1 < c.toNat then .poison
  else
    let s := x.toNat + y.toNat + c.toNat
    .tuple [.i64 (BitVec.ofNat 64 s), .i64 (BitVec.ofNat 64 (s / 2 ^ 64))]

/-- `Sub64borrow x y c` = `(x − y − c, borrow)`; `c ∉ {0, 1}` ⇒ `poison`. -/
def subborrow : List Val → Val := int3 .w64 fun x y c =>
  if 1 < c.toNat then .poison
  else
    .tuple [.i64 (x - y - c),
      .i64 (if x.toNat < y.toNat + c.toNat then 1 else 0)]

/-- A count of width `w` as a result of the value's own integer type (`rw`). -/
@[inline] def count (rw : Option Width) (n : Nat) : Val :=
  match rw with
  | some rw => .int rw (BitVec.ofNat rw.bits n)
  | none => .poison

/-- `Ctz*` (ctz 0 = w) and `Ctz*NonZero` (`nonZero`: 0 ⇒ `poison`); the result has the
value's type `rw`. -/
def ctz (w : Width) (nonZero : Bool) (rw : Option Width) : List Val → Val := int1 w fun x =>
  if nonZero && x = 0 then .poison else count rw x.ctz.toNat

/-- `BitLen*`: number of significant bits (`BitLen 0 = 0`). -/
def bitLen (w : Width) (rw : Option Width) : List Val → Val := int1 w fun x =>
  count rw (w.bits - x.clz.toNat)

/-- `PopCount*`. -/
def popCount (w : Width) (rw : Option Width) : List Val → Val := int1 w fun x =>
  count rw x.cpop.toNat

/-- Byte swap of the `k` low bytes of `x`. -/
def bswapNat : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, x => (x % 256) * 256 ^ k + bswapNat k (x / 256)

/-- `Bswap16/32/64`. -/
def bswap (w : Width) : List Val → Val := int1 w fun x =>
  .int w (BitVec.ofNat w.bits (bswapNat (w.bits / 8) x.toNat))

/-- `BitRev*`. -/
def bitRev (w : Width) : List Val → Val := int1 w fun x => .int w x.reverse

/-- `RotateLeft*`: rotate by the amount (any integer width) mod `w` (gO 259-262). -/
def rotateLeft (w : Width) : List Val → Val
  | [a, b] => match a.asInt w, b.asNat with
    | some x, some n => .int w (x.rotateLeft n)
    | _, _ => .poison
  | _ => .poison

/-- `Min64`, `Max64` (signed) and `Min64u`, `Max64u`. -/
def min (w : Width) (signed : Bool) : List Val → Val := int2 w fun x y =>
  .int w (if (if signed then x.slt y else x.ult y) then x else y)
def max (w : Width) (signed : Bool) : List Val → Val := int2 w fun x y =>
  .int w (if (if signed then y.slt x else y.ult x) then x else y)

/-- `Slicemask x`: 0 if `x = 0`, −1 if `x > 0`, undefined (`poison`) if `x < 0` (gO 588). -/
def slicemask (w : Width) : List Val → Val := int1 w fun x =>
  if x.msb then .poison else .int w (if x = 0 then 0 else -1)

end Int

end GoFV.SSA.Sem
