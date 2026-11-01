/-
Kernel-checked witnesses for the IEEE core (`GoFV/SSA/Sem/Float/*`, ported with clifv's
`FV/Float`; eth-act/clifv `docs/contracts/float.md`) and for the Go float ops of `evalPure`
(`Sem/Float.lean`): concrete binary32/binary64 cases with known results, each evaluated by the
kernel.
-/
import GoFV.SSA.Sem.Pure

namespace GoFVTest.FloatWitness
open GoFV.IEEE

/-! ## Addition, subtraction, signed zeros -/

-- 1 + 2 = 3
example : add .b32 .rne 0x3F800000#32 0x40000000#32 = 0x40400000#32 := by decide +kernel
example : add .b64 .rne 0x3FF0000000000000#64 0x4000000000000000#64 = 0x4008000000000000#64 := by
  decide +kernel
-- 0.1 + 0.2 = 0.30000000000000004
example : add .b64 .rne 0x3FB999999999999A#64 0x3FC999999999999A#64 = 0x3FD3333333333334#64 := by
  decide +kernel
-- 3 - 1 = 2
example : sub .b32 .rne 0x40400000#32 0x3F800000#32 = 0x40000000#32 := by decide +kernel
-- -0 + +0 = +0 (rne), -0 (rmi); -0 + -0 = -0
example : add .b32 .rne 0x80000000#32 0x00000000#32 = 0x00000000#32 := by decide +kernel
example : add .b32 .rmi 0x80000000#32 0x00000000#32 = 0x80000000#32 := by decide +kernel
example : add .b32 .rne 0x80000000#32 0x80000000#32 = 0x80000000#32 := by decide +kernel
-- x - x = +0 (rne), -0 (rmi)
example : sub .b64 .rne 0x3FF0000000000000#64 0x3FF0000000000000#64 = 0#64 := by decide +kernel
example : sub .b64 .rmi 0x3FF0000000000000#64 0x3FF0000000000000#64 = 0x8000000000000000#64 := by
  decide +kernel
-- 1 + 2^-24 (b32): a tie, rounds to even 1.0; rpi rounds up
example : add .b32 .rne 0x3F800000#32 0x33800000#32 = 0x3F800000#32 := by decide +kernel
example : add .b32 .rpi 0x3F800000#32 0x33800000#32 = 0x3F800001#32 := by decide +kernel

/-! ## NaNs and infinities -/

-- ∞ - ∞ = default NaN, both as `add` of opposite infinities and as `sub`
example : add .b32 .rne 0x7F800000#32 0xFF800000#32 = 0x7FC00000#32 := by decide +kernel
example : sub .b32 .rne 0x7F800000#32 0x7F800000#32 = 0x7FC00000#32 := by decide +kernel
example : sub .b64 .rne 0x7FF0000000000000#64 0x7FF0000000000000#64 = 0x7FF8000000000000#64 := by
  decide +kernel
-- sNaN + 1 = the sNaN quietened
example : add .b32 .rne 0x7F800001#32 0x3F800000#32 = 0x7FC00001#32 := by decide +kernel
-- two quiet NaNs: the first operand wins; a signalling second operand beats a quiet first one
example : add .b32 .rne 0x7FC00002#32 0xFFC00003#32 = 0x7FC00002#32 := by decide +kernel
example : mul .b32 .rne 0x7FC00002#32 0x7F800003#32 = 0x7FC00003#32 := by decide +kernel
-- NaN sign and payload are kept
example : div .b64 .rne 0xFFF8000000000123#64 0x3FF0000000000000#64 = 0xFFF8000000000123#64 := by
  decide +kernel
-- 0 * ∞, 0 / 0, ∞ / ∞, sqrt(-1) are invalid
example : mul .b32 .rne 0x00000000#32 0xFF800000#32 = 0x7FC00000#32 := by decide +kernel
example : div .b32 .rne 0x80000000#32 0x00000000#32 = 0x7FC00000#32 := by decide +kernel
example : div .b32 .rne 0x7F800000#32 0xFF800000#32 = 0x7FC00000#32 := by decide +kernel
example : sqrt .b32 .rne 0xBF800000#32 = 0x7FC00000#32 := by decide +kernel
-- 1 / ±0 = ±∞, sqrt(-0) = -0, sqrt(+∞) = +∞
example : div .b32 .rne 0x3F800000#32 0x80000000#32 = 0xFF800000#32 := by decide +kernel
example : sqrt .b64 .rne 0x8000000000000000#64 = 0x8000000000000000#64 := by decide +kernel
example : sqrt .b32 .rne 0x7F800000#32 = 0x7F800000#32 := by decide +kernel

/-! ## Rounding: overflow, subnormals, inexact quotients and roots -/

-- max finite * 2 overflows: +∞ (rne, rpi), max finite (rz, rmi); negative: -∞ under rmi
example : mul .b32 .rne 0x7F7FFFFF#32 0x40000000#32 = 0x7F800000#32 := by decide +kernel
example : mul .b32 .rz 0x7F7FFFFF#32 0x40000000#32 = 0x7F7FFFFF#32 := by decide +kernel
example : mul .b32 .rmi 0x7F7FFFFF#32 0x40000000#32 = 0x7F7FFFFF#32 := by decide +kernel
example : mul .b32 .rmi 0xFF7FFFFF#32 0x40000000#32 = 0xFF800000#32 := by decide +kernel
example : add .b64 .rne 0x7FEFFFFFFFFFFFFF#64 0x7FEFFFFFFFFFFFFF#64 = 0x7FF0000000000000#64 := by
  decide +kernel
-- subnormal results: min normal / 2 is exact; min subnormal * 1.5 rounds to 2 ulp (tie to even);
-- min subnormal * 0.5 is a tie between 0 and 1 ulp: +0 under rne, 1 ulp under rpi
example : mul .b32 .rne 0x00800000#32 0x3F000000#32 = 0x00400000#32 := by decide +kernel
example : mul .b32 .rne 0x00000001#32 0x3FC00000#32 = 0x00000002#32 := by decide +kernel
example : mul .b32 .rne 0x00000001#32 0x3F000000#32 = 0x00000000#32 := by decide +kernel
example : mul .b32 .rpi 0x00000001#32 0x3F000000#32 = 0x00000001#32 := by decide +kernel
example : mul .b64 .rne 0x0010000000000000#64 0x3CB0000000000000#64 = 0x0000000000000001#64 := by
  decide +kernel
-- subnormal - subnormal, subnormal + subnormal crossing into the normal range
example : sub .b32 .rne 0x00000003#32 0x00000001#32 = 0x00000002#32 := by decide +kernel
example : add .b32 .rne 0x007FFFFF#32 0x00000001#32 = 0x00800000#32 := by decide +kernel
-- 1 / 3
example : div .b32 .rne 0x3F800000#32 0x40400000#32 = 0x3EAAAAAB#32 := by decide +kernel
example : div .b32 .rz 0x3F800000#32 0x40400000#32 = 0x3EAAAAAA#32 := by decide +kernel
example : div .b64 .rne 0x3FF0000000000000#64 0x4008000000000000#64 = 0x3FD5555555555555#64 := by
  decide +kernel
-- sqrt 2, sqrt 4
example : sqrt .b32 .rne 0x40000000#32 = 0x3FB504F3#32 := by decide +kernel
example : sqrt .b64 .rne 0x4000000000000000#64 = 0x3FF6A09E667F3BCD#64 := by decide +kernel
example : sqrt .b64 .rne 0x4010000000000000#64 = 0x4000000000000000#64 := by decide +kernel
-- sqrt of the smallest subnormal: 2^-74.5 (b32)
example : sqrt .b32 .rne 0x00000001#32 = 0x1A3504F3#32 := by decide +kernel

/-! ## Fused multiply-add -/

-- a = 1 + 2^-27: a*a - 1 is 2^-26 after rounding the product, 2^-26 + 2^-54 fused
example : add .b64 .rne (mul .b64 .rne 0x3FF0000002000000#64 0x3FF0000002000000#64)
    0xBFF0000000000000#64 = 0x3E50000000000000#64 := by decide +kernel
example : mulAdd .b64 .rne 0xBFF0000000000000#64 0x3FF0000002000000#64 0x3FF0000002000000#64 =
    0x3E50000001000000#64 := by decide +kernel
-- a quiet-NaN addend does not hide 0 * ∞; otherwise NaN priority is addend, op1, op2
example : mulAdd .b32 .rne 0x7FC00005#32 0x00000000#32 0x7F800000#32 = 0x7FC00000#32 := by
  decide +kernel
example : mulAdd .b32 .rne 0x7FC00005#32 0x3F800000#32 0x7F800001#32 = 0x7FC00001#32 := by
  decide +kernel
-- +∞ + (-∞) via the product is invalid; exact zero sum: +0 (rne), -0 (rmi)
example : mulAdd .b32 .rne 0x7F800000#32 0xBF800000#32 0x7F800000#32 = 0x7FC00000#32 := by
  decide +kernel
example : mulAdd .b32 .rne 0xBF800000#32 0x3F800000#32 0x3F800000#32 = 0x00000000#32 := by
  decide +kernel
example : mulAdd .b32 .rmi 0xBF800000#32 0x3F800000#32 0x3F800000#32 = 0x80000000#32 := by
  decide +kernel

/-! ## Sign operations, min/max, compare -/

example : neg .b32 0x7FC00000#32 = 0xFFC00000#32 := by decide +kernel
example : abs .b64 0xBFF0000000000000#64 = 0x3FF0000000000000#64 := by decide +kernel
example : max .b32 .rne 0x80000000#32 0x00000000#32 = 0x00000000#32 := by decide +kernel
example : min .b32 .rne 0x00000000#32 0x80000000#32 = 0x80000000#32 := by decide +kernel
example : max .b32 .rne 0xFF800000#32 0x00000001#32 = 0x00000001#32 := by decide +kernel
example : min .b32 .rne 0x3F800000#32 0x7F800001#32 = 0x7FC00001#32 := by decide +kernel
example : compare .b32 0x80000000#32 0x00000000#32 = .eq := by decide +kernel
example : compare .b32 0x3F800000#32 0x40000000#32 = .lt := by decide +kernel
example : compare .b64 0x7FF0000000000000#64 0x7FEFFFFFFFFFFFFF#64 = .gt := by decide +kernel
example : compare .b32 0x7FC00000#32 0x7FC00000#32 = .un := by decide +kernel

/-! ## Round to integral -/

-- 2.5: 2 (rne), 3 (rna), 3 (rpi), 2 (rmi, rz); -2.5 (b32): -2 (rne), -3 (rmi)
example : roundInt .b64 .rne 0x4004000000000000#64 = 0x4000000000000000#64 := by decide +kernel
example : roundInt .b64 .rna 0x4004000000000000#64 = 0x4008000000000000#64 := by decide +kernel
example : roundInt .b64 .rpi 0x4004000000000000#64 = 0x4008000000000000#64 := by decide +kernel
example : roundInt .b64 .rmi 0x4004000000000000#64 = 0x4000000000000000#64 := by decide +kernel
example : roundInt .b64 .rz 0x4004000000000000#64 = 0x4000000000000000#64 := by decide +kernel
example : roundInt .b32 .rne 0xC0200000#32 = 0xC0000000#32 := by decide +kernel
example : roundInt .b32 .rmi 0xC0200000#32 = 0xC0400000#32 := by decide +kernel
-- 3.5 → 4 (rne); -0.3 → -0 (rpi); 0.3 → +0 (rz); 0.7 → 1 (rpi); sNaN quietened
example : roundInt .b64 .rne 0x400C000000000000#64 = 0x4010000000000000#64 := by decide +kernel
example : roundInt .b32 .rpi 0xBE99999A#32 = 0x80000000#32 := by decide +kernel
example : roundInt .b32 .rz 0x3E99999A#32 = 0x00000000#32 := by decide +kernel
example : roundInt .b32 .rpi 0x3F333333#32 = 0x3F800000#32 := by decide +kernel
example : roundInt .b32 .rne 0x7F800001#32 = 0x7FC00001#32 := by decide +kernel

/-! ## Format conversion -/

-- 0.1 (b64) → b32 rounds; 1 + 2^-24 (b64) is a tie: 1.0 (rne), 1 + 2^-23 (rpi)
example : convert .b64 .b32 .rne 0x3FB999999999999A#64 = 0x3DCCCCCD#32 := by decide +kernel
example : convert .b64 .b32 .rne 0x3FF0000010000000#64 = 0x3F800000#32 := by decide +kernel
example : convert .b64 .b32 .rpi 0x3FF0000010000000#64 = 0x3F800001#32 := by decide +kernel
-- overflow to ∞ (rne) or max finite (rz); underflow to the smallest subnormal / zero
example : convert .b64 .b32 .rne 0x7FEFFFFFFFFFFFFF#64 = 0x7F800000#32 := by decide +kernel
example : convert .b64 .b32 .rz 0x7FEFFFFFFFFFFFFF#64 = 0x7F7FFFFF#32 := by decide +kernel
example : convert .b64 .b32 .rne 0x0000000000000001#64 = 0x00000000#32 := by decide +kernel
example : convert .b64 .b32 .rpi 0x0000000000000001#64 = 0x00000001#32 := by decide +kernel
-- NaN payloads: truncated to the top 22 payload bits, quiet bit set, sign kept
example : convert .b64 .b32 .rne 0x7FF8000000000001#64 = 0x7FC00000#32 := by decide +kernel
example : convert .b64 .b32 .rne 0xFFF4000020000000#64 = 0xFFE00001#32 := by decide +kernel
-- widening is exact; NaN payload moves to the top
example : convert .b32 .b64 .rne 0x3DCCCCCD#32 = 0x3FB99999A0000000#64 := by decide +kernel
example : convert .b32 .b64 .rne 0x7F800001#32 = 0x7FF8000020000000#64 := by decide +kernel
example : convert .b32 .b64 .rne 0x00000001#32 = 0x36A0000000000000#64 := by decide +kernel

/-! ## Float ↔ integer -/

-- 1e10 saturates to INT32_MAX; NaN → 0; -1.5 → 0 (unsigned), -1 (signed); -∞ → INT64_MIN
example : toFixed .b32 0x501502F9#32 false 32 .rz = 0x7FFFFFFF#32 := by decide +kernel
example : toFixed .b32 0x501502F9#32 true 32 .rz = 0xFFFFFFFF#32 := by decide +kernel
example : toFixed .b64 0x7FF8000000000000#64 false 64 .rz = 0#64 := by decide +kernel
example : toFixed .b32 0xBFC00000#32 true 32 .rz = 0#32 := by decide +kernel
example : toFixed .b32 0xBFC00000#32 false 32 .rz = 0xFFFFFFFF#32 := by decide +kernel
example : toFixed .b64 0xFFF0000000000000#64 false 64 .rz = 0x8000000000000000#64 := by
  decide +kernel
example : toFixed .b64 0x7FF0000000000000#64 true 64 .rz = 0xFFFFFFFFFFFFFFFF#64 := by
  decide +kernel
-- -2^31 fits exactly; 2.5 under rne → 2, rna → 3
example : toFixed .b32 0xCF000000#32 false 32 .rz = 0x80000000#32 := by decide +kernel
example : toFixed .b64 0x4004000000000000#64 false 64 .rne = 2#64 := by decide +kernel
example : toFixed .b64 0x4004000000000000#64 false 64 .rna = 3#64 := by decide +kernel
-- 2^64 - 1 → 2^64 (b32, rne); as signed (-1) → -1.0
example : fromFixed .b32 64 0xFFFFFFFFFFFFFFFF#64 true .rne = 0x5F800000#32 := by decide +kernel
example : fromFixed .b32 64 0xFFFFFFFFFFFFFFFF#64 false .rne = 0xBF800000#32 := by decide +kernel
example : fromFixed .b32 64 0xFFFFFFFFFFFFFFFF#64 true .rz = 0x5F7FFFFF#32 := by decide +kernel
example : fromFixed .b64 32 0#32 false .rmi = 0#64 := by decide +kernel
/-! ## Go float ops (`evalPure`, arm64 semantics) -/

open GoFV.SSA GoFV.SSA.Sem in
/-- `evalPure op` on `args` is `r`. -/
def evals (op : Op) (args : List Val) (r : Val) (auxInt : Int64 := 0) : Bool :=
  Val.beq (evalPure op .other auxInt none args) r

open GoFV.SSA.Sem

-- 1.0 + 2.0 = 3.0; float32 0.1f * 3 = 0.3f rounded (0x3E99999A)
example : evals .Add64F [.i64 0x3FF0000000000000, .i64 0x4000000000000000] (.i64 0x4008000000000000) := by
  decide +kernel
example : evals .Mul32F [.i32 0x3DCCCCCD, .i32 0x40400000] (.i32 0x3E99999A) := by decide +kernel
-- comparisons are unordered on NaN: only Neq holds
example : evals .Less64F [.i64 0x7FF8000000000000, .i64 0] (.bool false) := by decide +kernel
example : evals .Leq64F [.i64 0, .i64 0x7FF8000000000000] (.bool false) := by decide +kernel
example : evals .Eq64F [.i64 0x7FF8000000000000, .i64 0x7FF8000000000000] (.bool false) := by
  decide +kernel
example : evals .Neq64F [.i64 0x7FF8000000000000, .i64 0x7FF8000000000000] (.bool true) := by
  decide +kernel
-- -0 == +0
example : evals .Eq32F [.i32 0x80000000, .i32 0] (.bool true) := by decide +kernel
-- Go's min/max: min(-0, +0) = -0, max(-0, +0) = +0, NaN propagates (quietened sNaN)
example : evals .Min64F [.i64 0, .i64 0x8000000000000000] (.i64 0x8000000000000000) := by
  decide +kernel
example : evals .Max64F [.i64 0x8000000000000000, .i64 0] (.i64 0) := by decide +kernel
example : evals .Max32F [.i32 0x3F800000, .i32 0x7F800001] (.i32 0x7FC00001) := by decide +kernel
-- float → int: truncation, saturation, NaN ↦ 0 (FCVTZS/FCVTZU)
example : evals .Cvt64Fto64 [.i64 0xC004000000000000] (.i64 (-2)) := by decide +kernel
example : evals .Cvt64Fto32 [.i64 0x4415AF1D78B58C40] (.i32 0x7FFFFFFF) := by decide +kernel
example : evals .Cvt64Fto32 [.i64 0x7FF8000000000000] (.i32 0) := by decide +kernel
example : evals .Cvt64Fto64U [.i64 0xBFF0000000000000] (.i64 0) := by decide +kernel
example : evals .Cvt32Fto64U [.i32 0x7F800000] (.i64 0xFFFFFFFFFFFFFFFF) := by decide +kernel
-- int → float rounds to nearest even: 2^53 + 1 → 2^53; uint64 max → 2^64
example : evals .Cvt64to64F [.i64 0x20000000000001] (.i64 0x4340000000000000) := by decide +kernel
example : evals .Cvt64Uto64F [.i64 0xFFFFFFFFFFFFFFFF] (.i64 0x43F0000000000000) := by
  decide +kernel
-- Round ties away from zero, RoundToEven to even; Floor/Ceil/Trunc of -2.5
example : evals .Round [.i64 0x4004000000000000] (.i64 0x4008000000000000) := by decide +kernel
example : evals .RoundToEven [.i64 0x4004000000000000] (.i64 0x4000000000000000) := by
  decide +kernel
example : evals .Floor [.i64 0xC004000000000000] (.i64 0xC008000000000000) := by decide +kernel
example : evals .Ceil [.i64 0xC004000000000000] (.i64 0xC000000000000000) := by decide +kernel
example : evals .Trunc [.i64 0xC004000000000000] (.i64 0xC000000000000000) := by decide +kernel
-- FMA x y z = x*y + z rounded once: (1 + 2^-52)(1 - 2^-52) - 1 = -2^-104 (unfused: 0)
example : evals .FMA [.i64 0x3FF0000000000001, .i64 0x3FEFFFFFFFFFFFFE, .i64 0xBFF0000000000000]
    (.i64 0xB970000000000000) := by decide +kernel
-- Copysign: |x| with y's sign; Abs and Neg touch the sign bit only, also of NaNs
example : evals .Copysign [.i64 0x4000000000000000, .i64 0x8000000000000000]
    (.i64 0xC000000000000000) := by decide +kernel
example : evals .Abs [.i64 0xFFF8000000000001] (.i64 0x7FF8000000000001) := by decide +kernel
example : evals .Neg32F [.i32 0x7FC00000] (.i32 0xFFC00000) := by decide +kernel
-- float32 ↔ float64: exact widening; narrowing rounds (0.1 → 0x3DCCCCCD)
example : evals .Cvt32Fto64F [.i32 0x3DCCCCCD] (.i64 0x3FB99999A0000000) := by decide +kernel
example : evals .Cvt64Fto32F [.i64 0x3FB999999999999A] (.i32 0x3DCCCCCD) := by decide +kernel
-- constants: Const32F holds the float64 bits of a float32-exact value
example : evals .Const32F [] (.i32 0x3FC00000) 0x3FF8000000000000 := by decide +kernel
example : evals .Const64F [] (.i64 0x3FF8000000000000) 0x3FF8000000000000 := by decide +kernel
-- commutative ops take their operands in encoding order: two quiet NaNs give the smaller
-- (arm64 gives the first), in either order; `Sub` keeps arm64's operand order
example : evals .Add64F [.i64 0x7FF8000000000002, .i64 0x7FF8000000000001] (.i64 0x7FF8000000000001) := by
  decide +kernel
example : evals .Add64F [.i64 0x7FF8000000000001, .i64 0x7FF8000000000002] (.i64 0x7FF8000000000001) := by
  decide +kernel
example : evals .Sub64F [.i64 0x7FF8000000000002, .i64 0x7FF8000000000001] (.i64 0x7FF8000000000002) := by
  decide +kernel
-- `FOps.ordered_comm` at two different NaNs
example : FOps.ordered (GoFV.IEEE.add .b64 .rne) 0x7FF8000000000002#64 0x7FF8000000000001#64 =
    FOps.ordered (GoFV.IEEE.add .b64 .rne) 0x7FF8000000000001#64 0x7FF8000000000002#64 :=
  FOps.ordered_comm _ _ _
-- a signalling NaN wins over a quiet one in either order (quietened)
example : evals .Mul32F [.i32 0x7FC00005, .i32 0xFF800001] (.i32 0xFFC00001) := by decide +kernel
-- sqrt(2) in float32; ill-typed arguments are poison
example : evals .Sqrt32 [.i32 0x40000000] (.i32 0x3FB504F3) := by decide +kernel
example : evals .Add64F [.i32 0, .i64 0] .poison := by decide +kernel

end GoFVTest.FloatWitness
