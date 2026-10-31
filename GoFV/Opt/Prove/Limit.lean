/-!
# prove: limit arithmetic (`prove.go:120-484`)

`limit` (signed and unsigned bounds of a value) and its arithmetic, verbatim. Go's `int64`/
`uint64` are `Int64`/`UInt64` (wrapping); a Go shift by a count `≥ 64` gives `0` (or `-1` for
a negative signed operand), unlike Lean's shifts which reduce the count modulo 64, so every
shift goes through `shl`/`shr`/`sar` below. A bit count `b` (Go `uint`) is a `Nat`.
-/

namespace GoFV.Opt.Prove

/-! ## Go integer helpers -/

/-- Go `x << s` on `uint64`. -/
@[inline] def shl (x : UInt64) (s : Nat) : UInt64 := if s ≥ 64 then 0 else x <<< s.toUInt64
/-- Go `x >> s` on `uint64`. -/
@[inline] def shr (x : UInt64) (s : Nat) : UInt64 := if s ≥ 64 then 0 else x >>> s.toUInt64
/-- Go `x << s` on `int64`. -/
@[inline] def shlI (x : Int64) (s : Nat) : Int64 := if s ≥ 64 then 0 else x <<< s.toInt64
/-- Go `x >> s` on `int64` (arithmetic). -/
@[inline] def sar (x : Int64) (s : Nat) : Int64 :=
  if s ≥ 64 then (if x < 0 then -1 else 0) else x >>> s.toInt64

/-- A Go `uint` computed from a (possibly negative) integer expression such as
`uint(8*size-1)`: wraps modulo 2⁶⁴. -/
@[inline] def goUint (i : Int) : Nat := (i % (2 ^ 64 : Int)).toNat

/-- `bits.Len64`. -/
@[inline] def len64 (x : UInt64) : Nat := if x == 0 then 0 else x.toNat.log2 + 1

/-- `bits.LeadingZeros64`. -/
@[inline] def leadingZeros64 (x : UInt64) : Nat := 64 - len64 x

/-- `bits.TrailingZeros64` (64 for 0). -/
def trailingZeros64 (x : UInt64) : Nat := Id.run do
  if x == 0 then return 64
  let mut n := 0
  for i in [0:64] do
    if (x >>> i.toUInt64) &&& 1 != 0 then return n
    n := n + 1
  return n

/-- `bits.OnesCount64`. -/
def onesCount64 (x : UInt64) : Nat := Id.run do
  let mut n := 0
  for i in [0:64] do
    if (x >>> i.toUInt64) &&& 1 != 0 then n := n + 1
  return n

/-- Go `max`/`min` on `int64`/`uint64`. -/
@[inline] def maxI (a b : Int64) : Int64 := if a < b then b else a
@[inline] def minI (a b : Int64) : Int64 := if b < a then b else a
@[inline] def maxU (a b : UInt64) : UInt64 := if a < b then b else a
@[inline] def minU (a b : UInt64) : UInt64 := if b < a then b else a

def maxInt64 : Int64 := 0x7FFFFFFFFFFFFFFF
def minInt64 : Int64 := -0x8000000000000000
def maxUint64 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-! ## `limit` -/

/-- `limit`: `min ≤ v ≤ max` (signed), `umin ≤ v ≤ umax` (unsigned). The default is Go's zero
limit (what `f.Cache.allocLimitSlice` gives values outside the blocks). -/
structure Limit where
  min : Int64
  max : Int64
  umin : UInt64
  umax : UInt64
  deriving DecidableEq, Inhabited, Repr

namespace Limit

def intersect (l l2 : Limit) : Limit :=
  { min := maxI l.min l2.min, umin := maxU l.umin l2.umin,
    max := minI l.max l2.max, umax := minU l.umax l2.umax }

def signedMin (l : Limit) (m : Int64) : Limit := { l with min := maxI l.min m }
def signedMinMax (l : Limit) (lo hi : Int64) : Limit :=
  { l with min := maxI l.min lo, max := minI l.max hi }
def unsignedMin (l : Limit) (m : UInt64) : Limit := { l with umin := maxU l.umin m }
def unsignedMax (l : Limit) (m : UInt64) : Limit := { l with umax := minU l.umax m }
def unsignedMinMax (l : Limit) (lo hi : UInt64) : Limit :=
  { l with umin := maxU l.umin lo, umax := minU l.umax hi }

def nonzero (l : Limit) : Bool := l.min > 0 || l.umin > 0 || l.max < 0
def maybeZero (l : Limit) : Bool := !l.nonzero
def nonnegative (l : Limit) : Bool := l.min ≥ 0
def unsat (l : Limit) : Bool := l.min > l.max || l.umin > l.umax

end Limit

/-- `fitsInBits(x, b)`. -/
def fitsInBits (x : Int64) (b : Nat) : Bool :=
  if b == 64 then true else
  let m : Int64 := shlI (-1) (goUint (b - 1 : Int))
  let mM : Int64 := -m - 1
  x ≥ m && x ≤ mM

/-- `fitsInBitsU(x, b)`. -/
@[inline] def fitsInBitsU (x : UInt64) (b : Nat) : Bool := shr x b == 0

/-- `safeAdd(x, y, b)`. -/
def safeAdd (x y : Int64) (b : Nat) : Option Int64 :=
  let s := x + y
  if x ≥ 0 && y ≥ 0 && s < 0 then none
  else if x < 0 && y < 0 && s ≥ 0 then none
  else if !fitsInBits s b then none
  else some s

/-- `safeAddU(x, y, b)`. -/
def safeAddU (x y : UInt64) (b : Nat) : Option UInt64 :=
  let s := x + y
  if s < x || s < y then none
  else if !fitsInBitsU s b then none
  else some s

/-- `safeSub(x, y, b)`. -/
def safeSub (x y : Int64) (b : Nat) : Option Int64 :=
  if y == minInt64 then
    if x == maxInt64 then none else safeAdd (x + 1) (-(y + 1)) b
  else safeAdd x (-y) b

/-- `safeSubU(x, y, b)`. -/
def safeSubU (x y : UInt64) (b : Nat) : Option UInt64 :=
  if x < y then none else
  let s := x - y
  if !fitsInBitsU s b then none else some s

/-- `noLimitForBitsize(bitsize)`. -/
def noLimitForBitsize (bitsize : Nat) : Limit :=
  let h := goUint (bitsize - 1 : Int)
  { min := -(shlI 1 h), max := shlI 1 h - 1, umin := 0, umax := shl 1 bitsize - 1 }

/-- `noLimit()`. -/
def noLimit : Limit := noLimitForBitsize 64

/-- `convertIntWithBitsize[uint64](x int64, b)`. -/
def convI2U (x : Int64) (b : Nat) : UInt64 :=
  match b with
  | 32 => x.toInt32.toInt64.toUInt64
  | 16 => x.toInt16.toInt64.toUInt64
  | 8 => x.toInt8.toInt64.toUInt64
  | _ => x.toUInt64

/-- `convertIntWithBitsize[int64](x uint64, b)`. -/
def convU2I (x : UInt64) (b : Nat) : Int64 :=
  match b with
  | 32 => x.toUInt32.toInt32.toInt64
  | 16 => x.toUInt16.toInt16.toInt64
  | 8 => x.toUInt8.toInt8.toInt64
  | _ => x.toInt64

namespace Limit

/-- `l.unsignedFixedLeadingBits()`: `(fixed, count)`. -/
def unsignedFixedLeadingBits (l : Limit) : UInt64 × Nat :=
  let varying := len64 (l.umin ^^^ l.umax)
  let count := leadingZeros64 (l.umin ^^^ l.umax)
  (l.umin &&& ~~~(shl 1 varying - 1), count)

/-- `l.add(l2, b)`. -/
def add (l l2 : Limit) (b : Nat) : Limit :=
  let lc : Option UInt64 :=
    if l.min == l.max then some (convI2U l.min b)
    else if l.umin == l.umax then some l.umin else none
  let l2c : Option UInt64 :=
    if l2.min == l2.max then some (convI2U l2.min b)
    else if l2.umin == l2.umax then some l2.umin else none
  match lc, l2c with
  | some a, some c =>
    let r := (a + c) &&& (shl 1 b - 1)
    let ir := convU2I r b
    { min := ir, max := ir, umin := r, umax := r }
  | _, _ =>
    let r := noLimit
    let r := match safeAdd l.min l2.min b, safeAdd l.max l2.max b with
      | some lo, some hi => { r with min := lo, max := hi }
      | _, _ => r
    match safeAddU l.umin l2.umin b, safeAddU l.umax l2.umax b with
    | some lo, some hi => { r with umin := lo, umax := hi }
    | _, _ => r

/-- `l.sub(l2, b)`. -/
def sub (l l2 : Limit) (b : Nat) : Limit :=
  let r := noLimit
  let r := match safeSub l.min l2.max b, safeSub l.max l2.min b with
    | some lo, some hi => { r with min := lo, max := hi }
    | _, _ => r
  match safeSubU l.umin l2.umax b, safeSubU l.umax l2.umin b with
  | some lo, some hi => { r with umin := lo, umax := hi }
  | _, _ => r

/-- `l.mul(l2, b)`. -/
def mul (l l2 : Limit) (b : Nat) : Limit :=
  let r := noLimit
  let p := l.umax.toNat * l2.umax.toNat
  let hi := p / 2 ^ 64
  let lo := UInt64.ofNat p
  if hi == 0 && fitsInBitsU lo b then { r with umax := lo, umin := l.umin * l2.umin } else r

/-- `l.exp2(b)`. -/
def exp2 (l : Limit) (b : Nat) : Limit :=
  let r := noLimit
  if l.umax < b.toUInt64 then
    { r with umin := shl 1 l.umin.toNat, umax := shl 1 l.umax.toNat }
  else r

/-- `l.com(b)`. -/
def com (l : Limit) (b : Nat) : Limit :=
  match b with
  | 32 => { min := (~~~l.max.toInt32).toInt64, max := (~~~l.min.toInt32).toInt64,
            umin := (~~~l.umax.toUInt32).toUInt64, umax := (~~~l.umin.toUInt32).toUInt64 }
  | 16 => { min := (~~~l.max.toInt16).toInt64, max := (~~~l.min.toInt16).toInt64,
            umin := (~~~l.umax.toUInt16).toUInt64, umax := (~~~l.umin.toUInt16).toUInt64 }
  | 8 => { min := (~~~l.max.toInt8).toInt64, max := (~~~l.min.toInt8).toInt64,
           umin := (~~~l.umax.toUInt8).toUInt64, umax := (~~~l.umin.toUInt8).toUInt64 }
  | _ => { min := ~~~l.max, max := ~~~l.min, umin := ~~~l.umax, umax := ~~~l.umin }

/-- `l.neg(b)`. -/
def neg (l : Limit) (b : Nat) : Limit := (l.com b).add ⟨1, 1, 1, 1⟩ b

/-- `l.ctz(b)`. -/
def ctz (l : Limit) (b : Nat) : Limit :=
  let (fixed, fixedCount) := l.unsignedFixedLeadingBits
  if fixedCount == 64 then
    let c := Nat.min (trailingZeros64 fixed) b
    { min := c.toInt64, max := c.toInt64, umin := c.toUInt64, umax := c.toUInt64 }
  else
    let varying := 64 - fixedCount
    if l.umin &&& (shl 1 varying - 1) != 0 then
      noLimit.unsignedMax (varying - 1).toUInt64
    else
      noLimit.unsignedMax (Nat.min (trailingZeros64 fixed) b).toUInt64

/-- `l.bitlen(b)`. -/
def bitlen (l : Limit) (_b : Nat) : Limit :=
  noLimit.unsignedMinMax (len64 l.umin).toUInt64 (len64 l.umax).toUInt64

/-- `l.popcount(b)`. -/
def popcount (l : Limit) (_b : Nat) : Limit :=
  let (fixed, fixedCount) := l.unsignedFixedLeadingBits
  let varying := 64 - fixedCount
  let fc := (onesCount64 fixed).toUInt64
  let mask := shl 1 varying - 1
  let mx := fc + varying.toUInt64
  let mx := if onesCount64 (l.umax &&& mask) != varying then mx - 1 else mx
  let mn := if l.umin &&& mask != 0 then fc + 1 else fc
  noLimit.unsignedMinMax mn mx

/-- `l.constValue()`. -/
def constValue (l : Limit) : Option Int64 :=
  if l.min == l.max then some l.min
  else if l.umin == l.umax then some l.umin.toInt64
  else none

end Limit

end GoFV.Opt.Prove
