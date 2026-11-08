import GoFV.SSA.Sem.Int
import GoFV.SSA.Sem.Float.Convert

variable [GoFV.SSA.Sem.Addrs]

/-!
# Float ops (`docs/plans/semantics.md` §4.6, phase P4)

A `float32`/`float64` value is its IEEE 754 bit pattern, held in `Val.int .w32`/`.w64` (as in
Go's registers and memory: loads, stores, ABI pieces and `Copy` need no float case; the op
gives the bits their meaning, as signedness for integers). Every op is the AArch64 instruction
`lower` selects for it (`_gen/ARM64.rules`), defined by the ASL port `GoFV.IEEE`
(`Sem/Float/*`, from clifv's validated `FV/Float`) with the Linux process default
`FPCR = 0` (`DN = 0`: NaN operands propagate, the first signalling NaN quietened, else the
first quiet NaN; invalid operations give the default NaN; `FZ = 0`: subnormals kept) and
rounding to nearest even:

* `Add/Sub/Mul/Div{32,64}F` `FADD/FSUB/FMUL/FDIV`, except the operand order of the commutative
  `Add`/`Mul` (below); `Neg{32,64}F` `FNEG`, `Abs` `FABSD`,
  `Copysign x y` (`|x|` with the sign of `y`): the sign bit only, also of NaNs;
* `Sqrt`/`Sqrt32` `FSQRT`; `Floor`/`Ceil`/`Trunc`/`Round`/`RoundToEven` `FRINTM/P/Z/A/N`
  (`FPRoundInt` toward −∞, +∞, zero, nearest ties away, nearest even);
* `FMA x y z` = `FMADDD z x y` = `x*y + z` rounded once (`FPMulAdd`);
* `Min/Max{32,64}F` `FMIN/FMAX` (Go's `min`/`max`: NaN-propagating, `−0 < +0`);
* `Eq/Neq/Less/Leq{32,64}F` `FCMP` and the condition: unordered (a NaN operand) makes every
  comparison false except `Neq`;
* `Cvt{32,64}[U]to{32,64}F` `SCVTF/UCVTF` (round to nearest even), `Cvt{32,64}Fto{32,64}[U]`
  `FCVTZS/FCVTZU`: truncation toward zero, saturating out of range, NaN ↦ 0 (the Go spec
  leaves out-of-range conversions implementation-defined; this is arm64's); `Cvt32Fto64F`
  `FCVT` (exact; a signalling NaN is quietened, the payload kept), `Cvt64Fto32F` `FCVT`
  (rounds; NaN payload truncated); `Round32F`/`Round64F` (`LoweredRound*F`) the identity;
* `Const64F [c]`: the bits `c`; `Const32F [c]`: `c` holds the float64 bits of a
  float32-exact value (gO 347), converted to binary32.

**Commutative ops.** Go marks `Add{32,64}F`, `Mul{32,64}F`, `Eq{32,64}F`, `Neq{32,64}F`
commutative: `cse` puts their arguments in value-ID order and the rules match them in both
orders. arm64's `FPProcessNaNs` is not symmetric when both operands are NaNs of the same kind
(both quiet or both signalling) with different encodings: the first one wins. IEEE 754 and the
Go spec leave the NaN result's encoding unspecified, so the semantics resolves it symmetrically:
these ops take their operands in the order of their encodings (`ordered`, smaller first), which
is arm64's result in every other case and makes them commutative (`ordered_comm`). Another
encoding choice the rules do not respect is the sign of a NaN: `generic.rules:1325`
(`x * -1` → `-x`) keeps a NaN's sign under `Mul` but flips it under `Neg` (§10).

`lower`'s fusion of `a + x*y` into `FMADD` (`ARM64.rules` "useFMA", allowed by the Go spec) is
not a generic op: the generic semantics rounds `Mul` and `Add` separately (§9.4).
-/

namespace GoFV.SSA.Sem

open GoFV.IEEE (Fmt RMode Cmp)

namespace FOps

/-- `g x y` with the operands in the order of their encodings, the smaller first: the
operand order of the commutative float ops (`Add`, `Mul`, `Eq`, `Neq`). -/
def ordered {f : Fmt} {α : Type} (g : IEEE.Bits f → IEEE.Bits f → α) (x y : IEEE.Bits f) : α :=
  if y.toNat < x.toNat then g y x else g x y

theorem ordered_comm {f : Fmt} {α : Type} (g : IEEE.Bits f → IEEE.Bits f → α)
    (x y : IEEE.Bits f) : ordered g x y = ordered g y x := by
  unfold ordered
  by_cases h1 : y.toNat < x.toNat
  · have h2 : ¬ x.toNat < y.toNat := Nat.lt_asymm h1
    simp only [h1, h2, ↓reduceIte]
  · by_cases h2 : x.toNat < y.toNat
    · simp only [h1, h2, ↓reduceIte]
    · have : x = y := BitVec.eq_of_toNat_eq (Nat.le_antisymm (Nat.not_lt.1 h1) (Nat.not_lt.1 h2))
      subst this; rfl

/-- A binary same-width float op at width `w` (`w32`: binary32, `w64`: binary64). -/
def bin (g : (f : Fmt) → IEEE.Bits f → IEEE.Bits f → IEEE.Bits f) : Width → List Val → Val
  | .w32 => int2 .w32 fun x y => .int .w32 (g Fmt.b32 x y)
  | .w64 => int2 .w64 fun x y => .int .w64 (g Fmt.b64 x y)
  | _ => fun _ => .poison

/-- A unary same-width float op. -/
def un (g : (f : Fmt) → IEEE.Bits f → IEEE.Bits f) : Width → List Val → Val
  | .w32 => int1 .w32 fun x => .int .w32 (g Fmt.b32 x)
  | .w64 => int1 .w64 fun x => .int .w64 (g Fmt.b64 x)
  | _ => fun _ => .poison

/-- A float comparison: the condition on `FPCompare`'s result. -/
def cmp (c : Cmp → Bool) : Width → List Val → Val
  | .w32 => int2 .w32 fun x y => .bool (c (IEEE.compare Fmt.b32 x y))
  | .w64 => int2 .w64 fun x y => .bool (c (IEEE.compare Fmt.b64 x y))
  | _ => fun _ => .poison

def add : Width → List Val → Val := bin fun f => ordered (IEEE.add f .rne)
def sub : Width → List Val → Val := bin fun f => IEEE.sub f .rne
def mul : Width → List Val → Val := bin fun f => ordered (IEEE.mul f .rne)
def div : Width → List Val → Val := bin fun f => IEEE.div f .rne
def min : Width → List Val → Val := bin fun f => IEEE.min f .rne
def max : Width → List Val → Val := bin fun f => IEEE.max f .rne

/-- `x` with the sign bit of `y`. -/
def copysignBits (f : Fmt) (x y : IEEE.Bits f) : IEEE.Bits f :=
  let s : IEEE.Bits f := BitVec.ofNat _ (2 ^ (f.E + f.F))
  (x &&& ~~~s) ||| (y &&& s)

def copysign : Width → List Val → Val := bin copysignBits
def neg : Width → List Val → Val := un IEEE.neg
def abs : Width → List Val → Val := un IEEE.abs
def sqrt : Width → List Val → Val := un fun f => IEEE.sqrt f .rne
/-- `Floor` (`rmi`), `Ceil` (`rpi`), `Trunc` (`rz`), `Round` (`rna`), `RoundToEven` (`rne`). -/
def roundInt (rm : RMode) : Width → List Val → Val := un fun f => IEEE.roundInt f rm

/-- `FMA x y z` = `x*y + z` with one rounding (`FMADD d = a + n*m` with `a = z`). -/
def fma : Width → List Val → Val
  | .w32 => int3 .w32 fun x y z => .int .w32 (IEEE.mulAdd Fmt.b32 .rne z x y)
  | .w64 => int3 .w64 fun x y z => .int .w64 (IEEE.mulAdd Fmt.b64 .rne z x y)
  | _ => fun _ => .poison

/-- A commutative comparison (`Eq`, `Neq`): `FPCompare`'s `eq`/`un` do not depend on the
operand order; `ordered` makes that structural. -/
def cmpC (c : Cmp → Bool) : Width → List Val → Val
  | .w32 => int2 .w32 fun x y => .bool (ordered (fun a b => c (IEEE.compare Fmt.b32 a b)) x y)
  | .w64 => int2 .w64 fun x y => .bool (ordered (fun a b => c (IEEE.compare Fmt.b64 a b)) x y)
  | _ => fun _ => .poison

def eq : Width → List Val → Val := cmpC (· == .eq)
def neq : Width → List Val → Val := cmpC (· != .eq)
def less : Width → List Val → Val := cmp (· == .lt)
def leq : Width → List Val → Val := cmp fun c => c == .lt || c == .eq

/-- `Round32F`/`Round64F`: the identity on a float of width `w`. -/
def round (w : Width) : List Val → Val := int1 w fun x => .int w x

/-- `Cvt{w}[U]to{w'}F`: the signed (`unsigned = false`) or unsigned integer of width `w` as a
float of width `w'`, rounded to nearest even (`SCVTF`/`UCVTF`, `FixedToFP`). -/
def ofInt (unsigned : Bool) (w : Width) : Width → List Val → Val
  | .w32 => int1 w fun x => .int .w32 (IEEE.fromFixed Fmt.b32 w.bits x unsigned .rne)
  | .w64 => int1 w fun x => .int .w64 (IEEE.fromFixed Fmt.b64 w.bits x unsigned .rne)
  | _ => fun _ => .poison

/-- `Cvt{w}Fto{w'}[U]`: the float of width `w` truncated toward zero to a signed or unsigned
integer of width `w'`, saturating, NaN ↦ 0 (`FCVTZS`/`FCVTZU`, `FPToFixed`). -/
def toInt (unsigned : Bool) (w' : Width) : Width → List Val → Val
  | .w32 => int1 .w32 fun x => .int w' (IEEE.toFixed Fmt.b32 x unsigned w'.bits .rz)
  | .w64 => int1 .w64 fun x => .int w' (IEEE.toFixed Fmt.b64 x unsigned w'.bits .rz)
  | _ => fun _ => .poison

/-- `Cvt32Fto64F` (exact) and `Cvt64Fto32F` (rounds to nearest even) (`FCVT`, `FPConvert`). -/
def f32to64 : List Val → Val := int1 .w32 fun x => .int .w64 (IEEE.convert Fmt.b32 Fmt.b64 .rne x)
def f64to32 : List Val → Val := int1 .w64 fun x => .int .w32 (IEEE.convert Fmt.b64 Fmt.b32 .rne x)

/-- `Const64F [c]`: the bits of `c`. -/
def const64 (auxInt : Int64) : Val := .int .w64 (BitVec.ofInt 64 auxInt.toInt)

/-- `Const32F [c]`: `c` is the float64 bits of a float32-exact value (gO 347). -/
def const32 (auxInt : Int64) : Val :=
  .int .w32 (IEEE.convert Fmt.b64 Fmt.b32 .rne (BitVec.ofInt 64 auxInt.toInt))

end FOps

end GoFV.SSA.Sem
