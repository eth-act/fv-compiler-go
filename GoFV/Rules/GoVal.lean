import GoFV.Rules.Syntax
import GoFV.SSA.Value

/-!
# Go values of rule expressions

The dynamic values a rule expression (`GoFV.Rules.Expr`) evaluates to, and Go's semantics of
the basic operations on them (docs/contracts/rules.md, "Go expression semantics"): fixed-width
wrapping integer arithmetic, shifts, integer/float conversions and IEEE `float32`/`float64`
arithmetic. Integers are kept as `Int` normalised to their Go type's range.
-/

namespace GoFV.Rules

open GoFV.SSA

/-- The runtime value of a rule expression. Pointers to compiler objects are IDs or table
numbers: `val` a `*Value`, `blk` a `*Block`, `typ` a `*types.Type`, `aux` an `Aux`/`Sym`/
`*AuxCall`/`*obj.LSym` (`none` = nil). `strct` is a Go struct value (`umagicData`, the result
of `bitsMulU64`, …) with its fields by name. The remaining constructors are the opaque handles
rule expressions select fields from (`config`, `config.ctxt`, `b.Func`, `b.Func.pass`, …). -/
inductive GVal where
  | int (i : Int)
  | bool (b : Bool)
  | f32 (x : Float32)
  | f64 (x : Float)
  | str (s : ByteArray)
  | val (id : ID)
  | blk (id : ID)
  | typ (t : TypeRef)
  | aux (a : Option AuxRef)
  | op (o : Op)
  | args (v : ID)
  | strct (fields : List (String × GVal))
  | rsv (r : Reserved)
  | ctxt | arch | byteOrder | func | pass | irSyms
  | nil
  deriving Inhabited

namespace GoTy

/-- Width and signedness of an integer type (`int`/`uint`/`uintptr` are 64-bit). -/
def intInfo? : GoTy → Option (Nat × Bool)
  | .int | .int64 => some (64, true)
  | .int8 => some (8, true)
  | .int16 => some (16, true)
  | .int32 => some (32, true)
  | .uint | .uint64 | .uintptr => some (64, false)
  | .uint8 => some (8, false)
  | .uint16 => some (16, false)
  | .uint32 => some (32, false)
  | _ => none

end GoTy

/-- `x` wrapped to a `w`-bit integer (two's complement if `signed`). -/
@[inline] def wrapInt (w : Nat) (signed : Bool) (x : Int) : Int :=
  if signed then x.bmod (2 ^ w) else x.emod (2 ^ w)

/-- `x` wrapped to the integer type `ty`; untyped constants are left alone. -/
@[inline] def wrapTo (ty : GoTy) (x : Int) : Int :=
  match ty.intInfo? with
  | some (w, s) => wrapInt w s x
  | none => x

/-- The 64-bit two's complement pattern of `x`. -/
@[inline] def pat64 (x : Int) : Nat := (x.emod (2 ^ 64)).toNat

/-- A bitwise operator on Go integers of type `ty`, computed on 64-bit patterns (every Go
integer type has at most 64 bits). -/
@[inline] def bitwise (ty : GoTy) (op : Nat → Nat → Nat) (a b : Int) : Int :=
  let (w, s) := ty.intInfo?.getD (64, true)
  wrapInt w s (op (pat64 a) (pat64 b))

/-- `x & (x - 1)` in type `ty`. -/
@[inline] def andPred (ty : GoTy) (x : Int) : Int := bitwise ty (· &&& ·) x (x - 1)

/-- Go's `/` on integers: truncation toward zero. -/
@[inline] def goQuo (x y : Int) : Int := x.tdiv y

/-- Go's `%` on integers: the sign of the dividend. -/
@[inline] def goRem (x y : Int) : Int := x.tmod y

/-- Go's `x << s` for a `w`-bit result (wrapped by the caller). -/
@[inline] def goShl (x : Int) (s : Nat) (w : Nat) : Int :=
  if s ≥ w then 0 else x * 2 ^ s

/-- Go's `x >> s` (arithmetic for signed `x`, which `Int.shiftRight` is; unsigned `x` is
non-negative). -/
@[inline] def goShr (x : Int) (s : Nat) : Int := x >>> s

/-- `x` as the unsigned 64-bit pattern of a two's complement integer. -/
@[inline] def toU64 (x : Int) : UInt64 := UInt64.ofInt x

/-- `math.Float64frombits`. -/
@[inline] def f64OfBits (b : Int) : Float := Float.ofBits (toU64 b)

/-- `math.Float64bits` as an `int64` pattern. -/
@[inline] def f64Bits (x : Float) : Int := wrapInt 64 true x.toBits.toNat

/-- `math.Float32bits`. -/
@[inline] def f32Bits (x : Float32) : Int := x.toBits.toNat

/-- Go's conversion of a float (already truncated toward zero by the caller's `trunc`) to a
`w`-bit signed integer as amd64 does it (the compiler runs on amd64): out of range or NaN gives
the most negative value. -/
def floatToSigned (x : Float) (w : Nat) : Int :=
  if x.isNaN then -(2 ^ (w - 1)) else
  let lo : Float := Float.ofInt (-(2 ^ (w - 1)))
  let hi : Float := Float.ofInt (2 ^ (w - 1))
  if x < lo || x ≥ hi then -(2 ^ (w - 1)) else
  let t := if x < 0 then x.ceil else x.floor
  -- `t` is an integer within (−2^63, 2^63): `toInt64` is exact there.
  if t < 0 then -((-t).toUInt64.toNat : Int) else (t.toUInt64.toNat : Int)

/-- Go's `math.Trunc`. -/
@[inline] def floatTrunc (x : Float) : Float := if x < 0 then x.ceil else x.floor

/-- Go's `math.RoundToEven` (bit manipulation, `math/floor.go`). -/
def floatRoundToEven (x : Float) : Float :=
  let bits := x.toBits
  let shift : UInt64 := 64 - 11 - 1
  let bias : UInt64 := 1023
  let mask : UInt64 := 0x7FF
  let fracMask : UInt64 := (1 <<< shift) - 1
  let halfMinusULP : UInt64 := (1 <<< (shift - 1)) - 1
  let e := (bits >>> shift) &&& mask
  if e ≥ bias then
    let e := e - bias
    if e < shift then
      let bits := bits + (halfMinusULP + ((bits >>> (shift - e)) &&& 1))
      Float.ofBits (bits &&& ~~~(fracMask >>> e))
    else Float.ofBits bits
  else if e == bias - 1 && (bits &&& fracMask) != 0 then
    Float.ofBits ((bits &&& ((1 : UInt64) <<< 63)) ||| (bias <<< shift))
  else
    Float.ofBits (bits &&& ((1 : UInt64) <<< 63))

/-- `float32(x)` of an integer value (round to nearest even, as Go's conversion). -/
@[inline] def intToF32 (x : Int) : Float32 := (Int64.ofInt x).toFloat32

/-- `float64(x)` of an integer value. -/
@[inline] def intToF64 (x : Int) : Float := (Int64.ofInt x).toFloat

/-- `bits.Len64`. -/
def bitsLen (x : Nat) : Nat := Nat.log2 x + (if x = 0 then 0 else 1)

/-- `bits.TrailingZeros` of a `w`-bit pattern (`w` for zero). -/
def trailingZeros (x : Nat) (w : Nat) : Nat := Id.run do
  if x % 2 ^ w = 0 then return w
  let mut n := 0
  let mut y := x
  for _ in [0:w] do
    if y % 2 = 1 then break
    y := y / 2
    n := n + 1
  return n

/-- `bits.OnesCount` of a natural number. -/
def onesCount (x : Nat) : Nat := Id.run do
  let mut n := 0
  let mut y := x
  while y > 0 do
    n := n + y % 2
    y := y / 2
  return n

end GoFV.Rules
