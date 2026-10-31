import GoFV.Rules.GoVal

/-!
# Magic numbers for division (`magic.go`)

Pure ports of `umagic`, `smagic`, `udivisible`, `sdivisible` and their `…OK` predicates over
`Nat`/`Int` (Go's `math/big` arithmetic is exact, the `uint64` arithmetic wraps). Arguments are
the `int64` sign extension of the rule's constant, as in Go (`umagic8(c int8)` calls
`umagic(8, int64(c))`).
-/

namespace GoFV.Rules.Magic

open GoFV.Rules

/-- `uint64(c) << (64 - n) >> (64 - n)`: the low `n` bits of `c`. -/
@[inline] def lowBits (n : Nat) (c : Int) : Nat := (c.emod (2 ^ n)).toNat

/-- `x & (x - 1) != 0` on a `w`-bit pattern `x`. -/
@[inline] def notPow2 (w : Nat) (x : Int) : Bool :=
  andPred (if w = 64 then .int64 else if w = 32 then .int32 else if w = 16 then .int16 else .int8) x != 0

/-- `umagicOK8..64(c)`: `c & (c - 1) != 0` in the width of `c`. -/
def umagicOK (w : Nat) (c : Int) : Bool := notPow2 w c

/-- `smagicOK(n, c)`, `sdivisibleOK(n, c)`: `c ≥ 0 && c & (c - 1) != 0` (on `int64(c)`). -/
def smagicOK (c : Int) : Bool := c ≥ 0 && notPow2 64 c

/-- `udivisibleOK(n, c)`: the low `n` bits are not a power of two (or zero). -/
def udivisibleOK (n : Nat) (c : Int) : Bool :=
  let d := lowBits n c
  d &&& (d - 1) != 0

/-- `umagic(n, c)`: `(s, m)` with `s = ⌈log2 c⌉`, `m = ⌈2^(n+s)/c⌉ - 2^n`. -/
def umagic (n : Nat) (c : Int) : Except String (Int × Nat) := do
  let d := lowBits n c
  if d = 0 then throw "umagic: zero divisor"
  let s := bitsLen d
  let M := (2 ^ (n + s) + d - 1) / d
  if (M >>> n) % 2 != 1 then throw "umagic: n+1st bit isn't set"
  let M := M - 2 ^ n
  return (s, M % 2 ^ 64)

/-- `smagic(n, c)`: `(s, m)` with `s = ⌈log2 c⌉ - 1`, `m = ⌈2^(n+s)/c⌉`. -/
def smagic (n : Nat) (c : Int) : Except String (Int × Nat) := do
  if c ≤ 0 then throw "smagic: non-positive divisor"
  let C := c.toNat
  let s := bitsLen C - 1
  let M := (2 ^ (n + s) + C - 1) / C
  if (M >>> n) % 2 != 0 then throw "smagic: n+1st bit is set"
  if (M >>> (n - 1)) % 2 == 0 then throw "smagic: nth bit is not set"
  return (s, M % 2 ^ 64)

/-- Newton–Raphson inverse of the odd `d0` modulo 2^64, as `magic.go` computes it. -/
def inv64 (d0 : Nat) : Nat := Id.run do
  let m64 := 2 ^ 64
  let mut m := d0 % m64
  for _ in [0:5] do
    -- m = m * (2 - m*d0) in uint64
    m := (m * ((2 + m64 * m64 - (m * d0) % m64) % m64)) % m64
  return m

/-- `udivisible(n, c)`: `(k, m, max)`. -/
def udivisible (n : Nat) (c : Int) : Except String (Int × Nat × Nat) := do
  let d := lowBits n c
  if d = 0 then throw "udivisible: zero divisor"
  let k := trailingZeros d 64
  let d0 := d >>> k
  let mask := 2 ^ n - 1
  let m := inv64 d0 &&& mask
  return (k, m, mask / d)

/-- `sdivisible(n, c)`: `(k, m, a, max)`. -/
def sdivisible (n : Nat) (c : Int) : Except String (Int × Nat × Nat × Nat) := do
  let d := (c.emod (2 ^ 64)).toNat
  if d = 0 then throw "sdivisible: zero divisor"
  let k := trailingZeros d 64
  let d0 := d >>> k
  let mask := 2 ^ n - 1
  let m := inv64 d0 &&& mask
  -- -(1 << k) as uint64
  let negPow := (2 ^ 64 - 2 ^ k) % 2 ^ 64
  let a := ((mask >>> 1) / d0) &&& negPow
  let max := ((2 * a) % 2 ^ 64) >>> k
  return (k, m, a, max)

/-- `modularMultiplicativeInverse(x)` (`rewrite.go`): panics on even `x`. -/
def modInverse (x : Nat) : Except String Nat := do
  if x % 2 != 1 then throw "even numbers in a power-of-two modulus do not have a multiplicative inverse"
  return inv64 x

end GoFV.Rules.Magic
