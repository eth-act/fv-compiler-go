import GoFV.Asm.Link

/-!
# Operand classes and optab lookup (`asm7.go`; `docs/PASSES3.md` D4)

Literal ports of `ctxt7.aclass` and `ctxt7.oplook` with everything they use: the class lattice
`cmp` (`xcmp[i][j] = cmp(j, i)` for `i, j < C_GOK`, `buildop`), the constant classifiers
(`conclass`, `con32class`, `con64class`, `isaddcon`, `isbitcon`, `movcon` …), the offset
classes (`autoclass`, `oregclass`, `loadStoreClass`, `loadStorePairClass`), `Optab.size`
(`optabSize`), `regoff`, `offsetshift`, `movesize`, `splitImm24uScaled`, the opcode predicates
and `isUnsafePoint`/`isRestartable`.

Operand classes are `Nat` (the raw `C_*` value; `Addr.cls` caches it, 0 = not computed, as Go's
`Addr.Class`); the generated `ARM64.C_*` constants are `Int`, so the bodies compare in `Int`.
Go `int64` values are `Int` (inputs are in range); `uint64` arithmetic is `UInt64`; the Go
conversions `int32(x)`, `uint32(x)`, `int16(x)` are `Aclass.wrapI32` … (two's complement).

Deviations forced by the export, none reachable from compiled code:
- `aclass` checks `a.Sym.Type == objabi.STLSBSS` (TLS variables); symbol kinds are not exported,
  and `STLSBSS` symbols (`runtime.tls_g`) are only defined and referenced by assembly, so the
  port treats every symbol as not `STLSBSS`.
- `oplook`'s SVE branch (`buildcfg.Experiment.SIMD && isSVE(p.As)`): `GoFV.Asm.As` has no SVE
  opcodes (compiled code has none), so the branch cannot be taken.
- `ctxt.Diag` is a `throw` (Go reports and continues; no corpus function has diagnostics).

Go's `aclass` also mutates its operand (`a.Reg = REG_NONE` for `NAME_AUTO`/`NAME_PARAM` based
on `REGSP`): `aclassAddr` returns the updated `Addr`, and `oplook` stores it back into the Prog
(the only first call on each operand; later calls on the same operand are idempotent).
-/

namespace GoFV.Asm

open ARM64 AsmM

namespace Aclass

/-- Go `int32(x)`. -/
@[inline] def wrapI32 (x : Int) : Int := x.bmod (2 ^ 32)
/-- Go `uint32(x)`. -/
@[inline] def wrapU32 (x : Int) : Int := x.emod (2 ^ 32)
/-- Go `int16(x)`. -/
@[inline] def wrapI16 (x : Int) : Int := x.bmod (2 ^ 16)
/-- Go `uint64(x)` of an `int64`. -/
@[inline] def toU64 (x : Int) : UInt64 := UInt64.ofInt x
/-- Go `int64(x)` of a `uint64`. -/
@[inline] def ofU64 (x : UInt64) : Int := x.toInt64.toInt
/-- `uint64(int64(intW(x)))`: sign-extends the low `w` bits of `x`. -/
@[inline] def sextU (w : Nat) (x : UInt64) : UInt64 := toU64 ((x.toNat : Int).bmod (2 ^ w))
/-- `bits.RotateLeft64(x, k)` for `0 ≤ k < 64`. -/
@[inline] def rotl64 (x : UInt64) (k : Nat) : UInt64 :=
  if k % 64 = 0 then x else (x <<< k.toUInt64) ||| (x >>> (64 - k).toUInt64)

end Aclass

open Aclass

/-- `cmp` (`asm7.go:2365-2737`): whether an operand of class `b` matches an optab operand of
class `a`. -/
def cmp (a b : Nat) : Bool := Id.run do
  let a : Int := a
  let b : Int := b
  let isIn (l : List Int) : Bool := l.contains b
  if a == b then return true
  -- `cmp(C_LCON, b)` for the `C_MOVCON2` and `C_VCON` cases.
  let lcon := b == C_LCON || isIn [C_ZCON, C_BITCON, C_ADDCON, C_ADDCON0, C_ABCON, C_ABCON0,
    C_MBCON, C_MOVCON, C_ADDCON2, C_AMCON]
  if a == C_RSP then return b == C_REG
  if a == C_ZREG then return b == C_REG
  if a == C_ADDCON0 then return b == C_ZCON || b == C_ABCON0
  if a == C_ADDCON then
    return b == C_ZCON || b == C_ABCON0 || b == C_ADDCON0 || b == C_ABCON || b == C_AMCON
  if a == C_MBCON then return b == C_ABCON0
  if a == C_BITCON then return b == C_ABCON0 || b == C_ABCON || b == C_MBCON
  if a == C_MOVCON then
    return b == C_MBCON || b == C_ZCON || b == C_ADDCON0 || b == C_ABCON0 || b == C_AMCON
  if a == C_ADDCON2 then return b == C_ZCON || b == C_ADDCON || b == C_ADDCON0
  if a == C_LCON then
    return b == C_ZCON || b == C_BITCON || b == C_ADDCON || b == C_ADDCON0 || b == C_ABCON ||
      b == C_ABCON0 || b == C_MBCON || b == C_MOVCON || b == C_ADDCON2 || b == C_AMCON
  if a == C_MOVCON2 then return lcon
  if a == C_VCON then return lcon
  if a == C_LACON then return b == C_AACON || b == C_AACON2
  if a == C_SEXT2 then return b == C_SEXT1
  if a == C_SEXT4 then return b == C_SEXT1 || b == C_SEXT2
  if a == C_SEXT8 then return b >= C_SEXT1 && b <= C_SEXT4
  if a == C_SEXT16 then return b >= C_SEXT1 && b <= C_SEXT8
  if a == C_LEXT then return b >= C_SEXT1 && b <= C_SEXT16
  if a == C_NSAUTO_8 then return b == C_NSAUTO_16
  if a == C_NSAUTO_4 then return b == C_NSAUTO_16 || b == C_NSAUTO_8
  if a == C_NSAUTO then return isIn [C_NSAUTO_4, C_NSAUTO_8, C_NSAUTO_16]
  if a == C_NPAUTO_16 then return isIn [C_NSAUTO_16]
  if a == C_NPAUTO then return isIn [C_NSAUTO_16, C_NSAUTO_8, C_NPAUTO_16]
  if a == C_NQAUTO_16 then return isIn [C_NSAUTO_16, C_NPAUTO_16]
  if a == C_NAUTO4K then
    return isIn [C_NSAUTO_16, C_NSAUTO_8, C_NSAUTO_4, C_NSAUTO, C_NPAUTO_16, C_NPAUTO,
      C_NQAUTO_16]
  if a == C_PSAUTO_16 then return b == C_ZAUTO
  if a == C_PSAUTO_8 then return b == C_ZAUTO || b == C_PSAUTO_16
  if a == C_PSAUTO_4 then return isIn [C_ZAUTO, C_PSAUTO_16, C_PSAUTO_8]
  if a == C_PSAUTO then return isIn [C_ZAUTO, C_PSAUTO_16, C_PSAUTO_8, C_PSAUTO_4]
  if a == C_PPAUTO_16 then return isIn [C_ZAUTO, C_PSAUTO_16]
  if a == C_PPAUTO then return isIn [C_ZAUTO, C_PSAUTO_16, C_PSAUTO_8, C_PPAUTO_16]
  if a == C_PQAUTO_16 then return isIn [C_ZAUTO, C_PSAUTO_16, C_PPAUTO_16]
  if a == C_UAUTO4K then
    return isIn [C_ZAUTO, C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO, C_PPAUTO_16, C_PQAUTO_16,
      C_UAUTO4K_2, C_UAUTO4K_4, C_UAUTO4K_8, C_UAUTO4K_16]
  if a == C_UAUTO8K then
    return isIn [C_ZAUTO, C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO, C_PPAUTO_16, C_PQAUTO_16,
      C_UAUTO4K_2, C_UAUTO4K_4, C_UAUTO4K_8, C_UAUTO4K_16,
      C_UAUTO8K_4, C_UAUTO8K_8, C_UAUTO8K_16]
  if a == C_UAUTO16K then
    return isIn [C_ZAUTO, C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO, C_PPAUTO_16, C_PQAUTO_16,
      C_UAUTO4K_4, C_UAUTO4K_8, C_UAUTO4K_16,
      C_UAUTO8K_4, C_UAUTO8K_8, C_UAUTO8K_16,
      C_UAUTO16K_8, C_UAUTO16K_16]
  if a == C_UAUTO32K then
    return isIn [C_ZAUTO, C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO, C_PPAUTO_16, C_PQAUTO_16,
      C_UAUTO4K_8, C_UAUTO4K_16,
      C_UAUTO8K_8, C_UAUTO8K_16,
      C_UAUTO16K_8, C_UAUTO16K_16,
      C_UAUTO32K_16]
  if a == C_UAUTO64K then
    return isIn [C_ZAUTO, C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO_16, C_PQAUTO_16, C_UAUTO4K_16, C_UAUTO8K_16, C_UAUTO16K_16,
      C_UAUTO32K_16]
  if a == C_LAUTO then
    return isIn [C_ZAUTO, C_NSAUTO, C_NSAUTO_4, C_NSAUTO_8, C_NSAUTO_16, C_NPAUTO_16, C_NPAUTO,
      C_NQAUTO_16, C_NAUTO4K,
      C_PSAUTO, C_PSAUTO_4, C_PSAUTO_8, C_PSAUTO_16,
      C_PPAUTO, C_PPAUTO_16, C_PQAUTO_16,
      C_UAUTO4K, C_UAUTO4K_2, C_UAUTO4K_4, C_UAUTO4K_8, C_UAUTO4K_16,
      C_UAUTO8K, C_UAUTO8K_4, C_UAUTO8K_8, C_UAUTO8K_16,
      C_UAUTO16K, C_UAUTO16K_8, C_UAUTO16K_16,
      C_UAUTO32K, C_UAUTO32K_16,
      C_UAUTO64K]
  if a == C_NSOREG_8 then return b == C_NSOREG_16
  if a == C_NSOREG_4 then return b == C_NSOREG_8 || b == C_NSOREG_16
  if a == C_NSOREG then return isIn [C_NSOREG_4, C_NSOREG_8, C_NSOREG_16]
  if a == C_NPOREG_16 then return isIn [C_NSOREG_16]
  if a == C_NPOREG then return isIn [C_NSOREG_16, C_NSOREG_8, C_NPOREG_16]
  if a == C_NQOREG_16 then return isIn [C_NSOREG_16, C_NPOREG_16]
  if a == C_NOREG4K then
    return isIn [C_NSOREG_16, C_NSOREG_8, C_NSOREG_4, C_NSOREG, C_NPOREG_16, C_NPOREG,
      C_NQOREG_16]
  if a == C_PSOREG_16 then return b == C_ZOREG
  if a == C_PSOREG_8 then return b == C_ZOREG || b == C_PSOREG_16
  if a == C_PSOREG_4 then return isIn [C_ZOREG, C_PSOREG_16, C_PSOREG_8]
  if a == C_PSOREG then return isIn [C_ZOREG, C_PSOREG_16, C_PSOREG_8, C_PSOREG_4]
  if a == C_PPOREG_16 then return isIn [C_ZOREG, C_PSOREG_16]
  if a == C_PPOREG then return isIn [C_ZOREG, C_PSOREG_16, C_PSOREG_8, C_PPOREG_16]
  if a == C_PQOREG_16 then return isIn [C_ZOREG, C_PSOREG_16, C_PPOREG_16]
  if a == C_UOREG4K then
    return isIn [C_ZOREG, C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG, C_PPOREG_16, C_PQOREG_16,
      C_UOREG4K_2, C_UOREG4K_4, C_UOREG4K_8, C_UOREG4K_16]
  if a == C_UOREG8K then
    return isIn [C_ZOREG, C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG, C_PPOREG_16, C_PQOREG_16,
      C_UOREG4K_2, C_UOREG4K_4, C_UOREG4K_8, C_UOREG4K_16,
      C_UOREG8K_4, C_UOREG8K_8, C_UOREG8K_16]
  if a == C_UOREG16K then
    return isIn [C_ZOREG, C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG, C_PPOREG_16, C_PQOREG_16,
      C_UOREG4K_4, C_UOREG4K_8, C_UOREG4K_16,
      C_UOREG8K_4, C_UOREG8K_8, C_UOREG8K_16,
      C_UOREG16K_8, C_UOREG16K_16]
  if a == C_UOREG32K then
    return isIn [C_ZOREG, C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG, C_PPOREG_16, C_PQOREG_16,
      C_UOREG4K_8, C_UOREG4K_16,
      C_UOREG8K_8, C_UOREG8K_16,
      C_UOREG16K_8, C_UOREG16K_16,
      C_UOREG32K_16]
  if a == C_UOREG64K then
    return isIn [C_ZOREG, C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG_16, C_PQOREG_16, C_UOREG4K_16, C_UOREG8K_16, C_UOREG16K_16,
      C_UOREG32K_16]
  if a == C_LOREG then
    return isIn [C_ZOREG, C_NSOREG, C_NSOREG_4, C_NSOREG_8, C_NSOREG_16, C_NPOREG, C_NPOREG_16,
      C_NQOREG_16, C_NOREG4K,
      C_PSOREG, C_PSOREG_4, C_PSOREG_8, C_PSOREG_16,
      C_PPOREG, C_PPOREG_16, C_PQOREG_16,
      C_UOREG4K, C_UOREG4K_2, C_UOREG4K_4, C_UOREG4K_8, C_UOREG4K_16,
      C_UOREG8K, C_UOREG8K_4, C_UOREG8K_8, C_UOREG8K_16,
      C_UOREG16K, C_UOREG16K_8, C_UOREG16K_16,
      C_UOREG32K, C_UOREG32K_16,
      C_UOREG64K]
  if a == C_LBRA then return b == C_SBRA
  return false

/-- `xcmp[i][j]` (`asm7.go:202`, filled by `buildop`, `asm7.go:2773-2779`): `cmp(j, i)` for
`i, j < C_GOK`, else `false`. -/
def xcmp (i j : Nat) : Bool :=
  (i : Int) < C_GOK && (j : Int) < C_GOK && cmp j i

/-- `movesize` (`asm7.go:8449-8470`): the log2 of the access size of a move, or −1. -/
def movesize : As → Int
  | .FMOVQ => 4
  | .MOVD | .FMOVD => 3
  | .MOVW | .MOVWU | .FMOVS => 2
  | .MOVH | .MOVHU => 1
  | .MOVB | .MOVBU => 0
  | _ => -1

/-! ## Opcode predicates (`asm7.go:1492-1590`) -/

def isSTLXRop : As → Bool
  | .STLXR | .STLXRW | .STLXRB | .STLXRH | .STXR | .STXRW | .STXRB | .STXRH => true
  | _ => false

def isSTXPop : As → Bool
  | .STXP | .STLXP | .STXPW | .STLXPW => true
  | _ => false

def isANDop : As → Bool
  | .AND | .ORR | .EOR | .ANDS | .TST | .BIC | .EON | .ORN | .BICS => true
  | _ => false

def isANDWop : As → Bool
  | .ANDW | .ORRW | .EORW | .ANDSW | .TSTW | .BICW | .EONW | .ORNW | .BICSW => true
  | _ => false

def isADDop : As → Bool
  | .ADD | .ADDS | .SUB | .SUBS | .CMN | .CMP => true
  | _ => false

def isADDWop : As → Bool
  | .ADDW | .ADDSW | .SUBW | .SUBSW | .CMNW | .CMPW => true
  | _ => false

def isADDSop : As → Bool
  | .ADDS | .ADDSW | .SUBS | .SUBSW => true
  | _ => false

def isNEGop : As → Bool
  | .NEG | .NEGW | .NEGS | .NEGSW => true
  | _ => false

def isLoadStorePairOp : As → Bool
  | .FLDPQ | .FSTPQ | .LDP | .STP | .LDPW | .STPW => true
  | _ => false

def isMOVop : As → Bool
  | .MOVB | .MOVBU | .MOVH | .MOVHU | .MOVW | .MOVWU | .MOVD | .FMOVS | .FMOVD | .FMOVQ => true
  | _ => false

/-- `isRegShiftOrExt` (`asm7.go:1575-1577`): `(a.Index-obj.RBaseARM64)&REG_EXT != 0 ||
(a.Index-obj.RBaseARM64)&REG_LSL != 0`, in `int16` (`obj.RBaseARM64 = REG_R0`). -/
def isRegShiftOrExt (a : Addr) : Bool :=
  let d := (a.index - REG_R0).emod (2 ^ 16) |>.toNat
  d &&& REG_EXT.toNat != 0 || d &&& REG_LSL.toNat != 0

/-- `ispcdisp` (`asm7.go:1586-1588`); `v` is an `int32`. -/
def ispcdisp (v : Int) : Bool :=
  -maxPCDisp < v && v < maxPCDisp && v % 4 == 0

/-- `isaddcon` (`asm7.go:1590-1599`). -/
def isaddcon (v : Int) : Bool := Id.run do
  let mut v := v
  if v < 0 then return false
  if v % 0x1000 == 0 then v := v >>> 12
  return v <= 0xFFF

/-- `isaddcon2` (`asm7.go:1601-1603`). -/
def isaddcon2 (v : Int) : Bool := 0 <= v && v <= 0xFFFFFF

/-- `sequenceOfOnes` (`asm7.go:1638-1643`). -/
def sequenceOfOnes (x : UInt64) : Bool :=
  let y := x &&& (0 - x)
  let y := y + x
  (y - 1) &&& y == 0

/-- `isbitcon` (`asm7.go:1611-1636`). -/
def isbitcon (x : UInt64) : Bool := Id.run do
  let mut x := x
  if x == 0xFFFFFFFFFFFFFFFF || x == 0 then return false
  if x != (x >>> 32 ||| x <<< 32) then
    pure ()
  else if x != (x >>> 16 ||| x <<< 48) then
    x := sextU 32 x
  else if x != (x >>> 8 ||| x <<< 56) then
    x := sextU 16 x
  else if x != (x >>> 4 ||| x <<< 60) then
    x := sextU 8 x
  else
    return true
  return sequenceOfOnes x || sequenceOfOnes (~~~x)

/-- `log2` (`asm7.go:1705-1710`): `bits.Len64(x) - 1`; Go panics on 0. -/
def log2 (x : UInt64) : UInt32 :=
  if x == 0 then panic! "log2 of 0" else x.toNat.log2.toUInt32

/-- `bitconEncode` (`asm7.go:1657-1703`): the `N:R:S` field of a bitcon `x` (`mode` 32 or 64). -/
def bitconEncode (x : UInt64) (mode : Nat) : UInt32 := Id.run do
  let mut x := x
  if mode == 32 then
    x := x &&& 0xffffffff
    x := x <<< 32 ||| x
  let mut period : UInt32 := 0
  if x != (x >>> 32 ||| x <<< 32) then
    period := 64
  else if x != (x >>> 16 ||| x <<< 48) then
    period := 32
    x := sextU 32 x
  else if x != (x >>> 8 ||| x <<< 56) then
    period := 16
    x := sextU 16 x
  else if x != (x >>> 4 ||| x <<< 60) then
    period := 8
    x := sextU 8 x
  else if x != (x >>> 2 ||| x <<< 62) then
    period := 4
    x := toU64 (ofU64 (x <<< 60) >>> 60)
  else
    period := 2
    x := toU64 (ofU64 (x <<< 62) >>> 62)
  let mut neg := false
  if ofU64 x < 0 then
    x := ~~~x
    neg := true
  let y := x &&& (0 - x)
  let mut s := log2 y
  let mut n := log2 (x + y) - s
  if neg then
    s := n + s
    n := period - n
  let mut N : UInt32 := 0
  if mode == 64 && period == 64 then N := 1
  let modeM1 : UInt32 := (mode - 1).toUInt32
  let R : UInt32 := (period - s) &&& (period - 1) &&& modeM1
  let hiS : UInt32 := (63 : UInt32) &&& ~~~((period <<< 1) - 1)
  let S : UInt32 := (n - 1) ||| hiS
  return N <<< 22 ||| R <<< 16 ||| S <<< 10

/-- `autoclass` (`asm7.go:1712-1837`): the class of a stack offset `l`. -/
def autoclass (l : Int) : Nat := Int.toNat <| Id.run do
  if l == 0 then return C_ZAUTO
  if l < 0 then
    if l >= -256 && l % 16 == 0 then return C_NSAUTO_16
    if l >= -256 && l % 8 == 0 then return C_NSAUTO_8
    if l >= -256 && l % 4 == 0 then return C_NSAUTO_4
    if l >= -256 then return C_NSAUTO
    if l >= -512 && l % 16 == 0 then return C_NPAUTO_16
    if l >= -512 && l % 8 == 0 then return C_NPAUTO
    if l >= -1024 && l % 16 == 0 then return C_NQAUTO_16
    if l >= -4095 then return C_NAUTO4K
    return C_LAUTO
  if l <= 255 then
    if l % 16 == 0 then return C_PSAUTO_16
    if l % 8 == 0 then return C_PSAUTO_8
    if l % 4 == 0 then return C_PSAUTO_4
    return C_PSAUTO
  if l <= 504 then
    if l % 16 == 0 then return C_PPAUTO_16
    if l % 8 == 0 then return C_PPAUTO
  if l <= 1008 then
    if l % 16 == 0 then return C_PQAUTO_16
  if l <= 4095 then
    if l % 16 == 0 then return C_UAUTO4K_16
    if l % 8 == 0 then return C_UAUTO4K_8
    if l % 4 == 0 then return C_UAUTO4K_4
    if l % 2 == 0 then return C_UAUTO4K_2
    return C_UAUTO4K
  if l <= 8190 then
    if l % 16 == 0 then return C_UAUTO8K_16
    if l % 8 == 0 then return C_UAUTO8K_8
    if l % 4 == 0 then return C_UAUTO8K_4
    if l % 2 == 0 then return C_UAUTO8K
  if l <= 16380 then
    if l % 16 == 0 then return C_UAUTO16K_16
    if l % 8 == 0 then return C_UAUTO16K_8
    if l % 4 == 0 then return C_UAUTO16K
  if l <= 32760 then
    if l % 16 == 0 then return C_UAUTO32K_16
    if l % 8 == 0 then return C_UAUTO32K
  if l <= 65520 && l % 16 == 0 then return C_UAUTO64K
  return C_LAUTO

/-- `oregclass` (`asm7.go:1839-1841`). -/
def oregclass (l : Int) : Nat := (autoclass l - C_ZAUTO + C_ZOREG).toNat

/-- `ctxt7.offsetshift` (`asm7.go:1848-1874`): the offset `v` scaled for class `cls`. -/
def offsetshift (p : Prog) (v : Int) (cls : Nat) : AsmM Int := do
  let c : Int := cls
  let mut s : Nat := 0
  if c >= C_SEXT1 && c <= C_SEXT16 then
    s := (c - C_SEXT1).toNat
  else if c == C_UAUTO4K || c == C_UOREG4K || c == C_ZOREG then
    s := 0
  else if c == C_UAUTO8K || c == C_UOREG8K then
    s := 1
  else if c == C_UAUTO16K || c == C_UOREG16K then
    s := 2
  else if c == C_UAUTO32K || c == C_UOREG32K then
    s := 3
  else if c == C_UAUTO64K || c == C_UOREG64K then
    s := 4
  else
    fail s!"offsetshift: bad class: {cls} ({p.as.name})"
  let vs := v >>> s
  if vs <<< s != v then
    fail s!"offsetshift: odd offset: {v} ({p.as.name})"
  return vs

/-- `movcon` (`asm7.go:1880-1887`): the bit offset of the single aligned 16-bit field of `v`,
or −1. -/
def movcon (v : Int) : Int := Id.run do
  for s in [(0 : Nat), 16, 32, 48] do
    if toU64 v &&& ~~~((0xFFFF : UInt64) <<< s.toUInt64) == 0 then return (s : Int)
  return -1

/-- `rclass` (`asm7.go:1889-1912`): the class of register `r` (`int16`). -/
def rclass (r : Int) : Nat := Int.toNat <|
  if REG_R0 <= r && r <= REG_R30 then C_REG
  else if r == REGZERO then C_ZREG
  else if REG_F0 <= r && r <= REG_F31 then C_FREG
  else if REG_V0 <= r && r <= REG_V31 then C_VREG
  else if r == REGSP then C_RSP
  else if r >= REG_ARNG && r < REG_ELEM then C_ARNG
  else if r >= REG_ELEM && r < REG_ZARNG then C_ELEM
  else if (r >= REG_UXTB && r < REG_SPECIAL) || (r >= REG_LSL && r < REG_ARNG) then C_EXTREG
  else if r >= REG_SPECIAL then C_SPR
  else C_GOK

/-- `conclass` (`asm7.go:1914-1983`): the class of constant `v` (`mode` 32 or 64). -/
def conclass (v : Int) (mode : Nat) : Nat := Int.toNat <| Id.run do
  let mut vbitcon := toU64 v
  if mode == 32 then vbitcon := toU64 v <<< 32 ||| toU64 v
  let mut vnotcon := -v - 1
  if mode == 32 then vnotcon := wrapU32 vnotcon
  if v == 0 then return C_ZCON
  if isaddcon v then
    if v <= 0xFFF then
      if isbitcon vbitcon then return C_ABCON0
      return C_ADDCON0
    if isbitcon vbitcon then return C_ABCON
    if movcon v >= 0 then return C_AMCON
    if movcon vnotcon >= 0 then return C_AMCON
    return C_ADDCON
  if movcon v >= 0 then
    if isbitcon vbitcon then return C_MBCON
    return C_MOVCON
  if movcon vnotcon >= 0 then
    if isbitcon vbitcon then return C_MBCON
    return C_MOVCON
  if isbitcon vbitcon then return C_BITCON
  if isaddcon2 v then return C_ADDCON2
  if wrapU32 v == v || v == wrapI32 v then return C_LCON
  return C_VCON

/-- `ctxt7.con32class` (`asm7.go:1988-1990`). -/
def con32class (a : Addr) : AsmM Nat := pure (conclass (wrapU32 a.offset) 32)

/-- `ctxt7.con64class` (`asm7.go:1993-2023`). -/
def con64class (a : Addr) : AsmM Nat := pure <| Int.toNat <| Id.run do
  let mut zeroCount := 0
  let mut negCount := 0
  for i in [0:4] do
    let immh := (a.offset >>> (i * 16)) % 0x10000
    if immh == 0 then
      zeroCount := zeroCount + 1
    else if immh == 0xffff then
      negCount := negCount + 1
  if zeroCount >= 3 || negCount >= 3 then
    return C_MOVCON
  else if zeroCount == 2 || negCount == 2 then
    return C_MOVCON2
  let u := toU64 a.offset
  for i in [0:4] do
    let mask := (0xffff : UInt64) <<< (i * 16).toUInt64
    for period in [2, 4, 8, 16, 32] do
      let x := (u &&& ~~~mask) ||| (rotl64 u (max period 16) &&& mask)
      if isbitcon x then return C_MOVCON2
  if zeroCount == 1 || negCount == 1 then
    return C_MOVCON3
  else
    return C_VCON

/-- `ctxt7.loadStoreClass` (`asm7.go:2026-2079`): reclassifies a load/store by its offset. -/
def loadStoreClass (p : Prog) (lsc : Nat) (v : Int) : Nat := Id.run do
  let sc : Int := p.scond
  if sc == C_XPRE || sc == C_XPOST then return lsc
  let k (c : Int) : Nat := c.toNat
  if cmp (k C_NSAUTO) lsc || cmp (k C_NSOREG) lsc then return lsc
  let mut needsPool := true
  if v >= -4095 && v <= 4095 then needsPool := false
  match p.as with
  | .MOVB | .MOVBU =>
    if cmp (k C_UAUTO4K) lsc || cmp (k C_UOREG4K) lsc then return lsc
    if v >= 0 && v <= 0xffffff then needsPool := false
  | .MOVH | .MOVHU =>
    if cmp (k C_UAUTO8K) lsc || cmp (k C_UOREG8K) lsc then return lsc
    if v >= 0 && v <= 0xfff000 + (0xfff <<< 1) && (v % 2 == 0 || v <= 0xfff + (0xfff <<< 1)) then
      needsPool := false
  | .MOVW | .MOVWU | .FMOVS =>
    if cmp (k C_UAUTO16K) lsc || cmp (k C_UOREG16K) lsc then return lsc
    if v >= 0 && v <= 0xfff000 + (0xfff <<< 2) && (v % 4 == 0 || v <= 0xfff + (0xfff <<< 2)) then
      needsPool := false
  | .MOVD | .FMOVD =>
    if cmp (k C_UAUTO32K) lsc || cmp (k C_UOREG32K) lsc then return lsc
    if v >= 0 && v <= 0xfff000 + (0xfff <<< 3) && (v % 8 == 0 || v <= 0xfff + (0xfff <<< 3)) then
      needsPool := false
  | .FMOVQ =>
    if cmp (k C_UAUTO64K) lsc || cmp (k C_UOREG64K) lsc then return lsc
    if v >= 0 && v <= 0xfff000 + (0xfff <<< 4) && (v % 16 == 0 || v <= 0xfff + (0xfff <<< 4))
    then
      needsPool := false
  | _ => pure ()
  if needsPool && cmp (k C_LAUTO) lsc then return k C_LAUTOPOOL
  if needsPool && cmp (k C_LOREG) lsc then return k C_LOREGPOOL
  return lsc

/-- `ctxt7.loadStorePairClass` (`asm7.go:2082-2105`). -/
def loadStorePairClass (p : Prog) (lsc : Nat) (v : Int) : Nat := Id.run do
  let sc : Int := p.scond
  if sc == C_XPRE || sc == C_XPOST then return lsc
  let k (c : Int) : Nat := c.toNat
  if cmp (k C_NAUTO4K) lsc || cmp (k C_NOREG4K) lsc then return lsc
  if cmp (k C_UAUTO4K) lsc || cmp (k C_UOREG4K) lsc then return lsc
  let mut needsPool := true
  if v >= 0 && v <= 0xffffff then needsPool := false
  if needsPool && cmp (k C_LAUTO) lsc then return k C_LAUTOPOOL
  if needsPool && cmp (k C_LOREG) lsc then return k C_LOREGPOOL
  return lsc

/-- `ctxt7.aclass` (`asm7.go:2107-2244`): the class of operand `a`; sets `instoffset` as Go
does, and returns `a` with Go's in-place update (`a.Reg = REG_NONE` for `NAME_AUTO`/`NAME_PARAM`
operands based on `REGSP`). -/
def aclassAddr (a : Addr) : AsmM (Nat × Addr) := do
  let setOff (v : Int) : AsmM Unit := modify fun s => { s with instoffset := v }
  let ret (c : Int) (a : Addr) : AsmM (Nat × Addr) := pure (c.toNat, a)
  let autosize := (← get).autosize
  let extrasize := (← get).extrasize
  let clearSP (a : Addr) : Addr := if a.reg == REGSP then { a with reg := 0 } else a
  match a.type with
  | .NONE => ret C_NONE a
  | .REG => pure (rclass a.reg, a)
  | .REGREG => ret C_PAIR a
  | .SHIFT => ret C_SHIFT a
  | .REGLIST => ret C_LIST a
  | .MEM =>
    -- The base register should be an integer register.
    if wrapI16 REG_F0 <= a.reg && a.reg <= wrapI16 REG_V31 then return (C_GOK.toNat, a)
    match a.name with
    | .EXTERN | .STATIC =>
      match a.sym with
      | none => ret C_GOK a
      | some _ =>
        setOff a.offset
        -- `a.Sym.Type == objabi.STLSBSS` (module doc): never for compiled code.
        ret C_ADDR a
    | .GOTREF => ret C_GOTADDR a
    | .AUTO =>
      let a := clearSP a
      let v := autosize + a.offset - extrasize
      setOff v
      pure (autoclass v, a)
    | .PARAM =>
      let a := clearSP a
      let v := autosize + a.offset + 8
      setOff v
      pure (autoclass v, a)
    | .NONE =>
      if a.index != 0 then
        if a.offset != 0 then
          if isRegShiftOrExt a then return (C_ROFF.toNat, a)
          return (C_GOK.toNat, a)
        return (C_ROFF.toNat, a)
      setOff a.offset
      pure (oregclass a.offset, a)
    | _ => ret C_GOK a
  | .FCONST => ret C_FCON a
  | .TEXTSIZE => ret C_TEXTSIZE a
  | .CONST | .ADDR =>
    let r : Option (Nat × Addr) ← match a.name with
      | .NONE =>
        setOff a.offset
        if a.reg != 0 && a.reg != REGZERO then pure none
        else pure (some (conclass a.offset 64, a))
      | .EXTERN | .STATIC =>
        match a.sym with
        | none => pure (some (C_GOK.toNat, a))
        | some _ =>
          setOff a.offset
          pure (some (C_VCONADDR.toNat, a))
      | .AUTO =>
        setOff (autosize + a.offset - extrasize)
        pure none
      | .PARAM =>
        setOff (autosize + a.offset + 8)
        pure none
      | _ => pure (some (C_GOK.toNat, a))
    match r with
    | some x => pure x
    | none =>
      let a := if a.name == .AUTO || a.name == .PARAM then clearSP a else a
      let cf := (← get).instoffset
      if isaddcon cf || isaddcon (-cf) then return (C_AACON.toNat, a)
      if isaddcon2 cf then return (C_AACON2.toNat, a)
      ret C_LACON a
  | .BRANCH => ret C_SBRA a
  | .SPECIAL =>
    let opd := a.offset
    if SPOP_EQ <= opd && opd <= SPOP_NV then ret C_COND a else ret C_SPOP a
  | _ => ret C_GOK a

/-- `ctxt7.aclass` (`asm7.go:2107-2244`) without the operand update (see `aclassAddr`). -/
def aclass (a : Addr) : AsmM Nat := return (← aclassAddr a).1

/-- `ctxt7.regoff` (`asm7.go:1486-1490`): `int32(instoffset)` after `aclass(a)`. -/
def regoff (a : Addr) : AsmM Int := do
  modify fun s => { s with instoffset := 0 }
  let _ ← aclass a
  return wrapI32 (← get).instoffset

/-- `ctxt7.oplook` (`asm7.go:2254-2363`): the optab entry of Prog `p`; caches the operand
classes in its `Addr`s and the entry in `Prog.Optab` (1-based), as Go does. -/
def oplook (p : Nat) : AsmM ARM64.Optab := do
  let mut pr ← getP p
  if pr.optab != 0 then
    match optabAt? pr.optab with
    | some o => return o
    | none => fail s!"oplook: bad Optab {pr.optab}"
  let k (c : Int) : Nat := c.toNat
  let mut a1 : Nat := pr.from_.cls.toNat
  if a1 == 0 then
    let (c, fr) ← aclassAddr pr.from_
    pr := { pr with from_ := fr }
    a1 := c
    -- do not break C_ADDCON2 when S bit is set
    if (pr.as == .ADDS || pr.as == .ADDSW || pr.as == .SUBS || pr.as == .SUBSW) &&
        a1 == k C_ADDCON2 then
      a1 := k C_LCON
    if pr.from_.type == .CONST && pr.from_.name == .NONE then
      if pr.as == .MOVW || isADDWop pr.as || isANDWop pr.as then
        -- For 32-bit instruction with constant, we need to
        -- treat its offset value as 32 bits to classify it.
        a1 ← con32class pr.from_
        -- do not break C_ADDCON2 when S bit is set
        if (pr.as == .ADDSW || pr.as == .SUBSW) && a1 == k C_ADDCON2 then
          a1 := k C_LCON
      if (pr.as == .MOVD || isANDop pr.as || isADDop pr.as) &&
          (a1 == k C_LCON || a1 == k C_VCON) then
        -- more specific classification of 64-bit integers
        a1 ← con64class pr.from_
    if pr.from_.type == .MEM then
      if isMOVop pr.as && (cmp (k C_LAUTO) a1 || cmp (k C_LOREG) a1) then
        a1 := loadStoreClass pr a1 (← get).instoffset
      if isLoadStorePairOp pr.as && (cmp (k C_LAUTO) a1 || cmp (k C_LOREG) a1) then
        a1 := loadStorePairClass pr a1 (← get).instoffset
    pr := { pr with from_ := { pr.from_ with cls := a1 } }
  let mut a2 : Nat := k C_NONE
  if pr.reg != 0 then a2 := rclass pr.reg
  let mut a3 : Nat := k C_NONE
  -- p.GetFrom3(): the first RestArgs operand at obj.Source.
  match pr.rest.findIdx? (fun x => (x.1 : Int) == GoFV.Asm.Obj.Source) with
  | some i =>
    let (pos, ad) := pr.rest[i]!
    a3 := ad.cls.toNat
    if a3 == 0 then
      let (c, ad) ← aclassAddr ad
      a3 := c
      pr := { pr with rest := pr.rest.set! i (pos, { ad with cls := c }) }
  | none => pure ()
  let mut a4 : Nat := pr.to.cls.toNat
  if a4 == 0 then
    let (c, t) ← aclassAddr pr.to
    pr := { pr with to := t }
    a4 := c
    if pr.to.type == .MEM then
      if isMOVop pr.as && (cmp (k C_LAUTO) a4 || cmp (k C_LOREG) a4) then
        a4 := loadStoreClass pr a4 (← get).instoffset
      if isLoadStorePairOp pr.as && (cmp (k C_LAUTO) a4 || cmp (k C_LOREG) a4) then
        a4 := loadStorePairClass pr a4 (← get).instoffset
    pr := { pr with to := { pr.to with cls := a4 } }
  let mut a5 : Nat := k C_NONE
  if pr.regTo2 != 0 then
    a5 := rclass pr.regTo2
  else
    -- p.GetTo2(): the first RestArgs operand at obj.Destination.
    match pr.rest.findIdx? (fun x => (x.1 : Int) == GoFV.Asm.Obj.Destination) with
    | some i =>
      let (pos, ad) := pr.rest[i]!
      a5 := ad.cls.toNat
      if a5 == 0 then
        let (c, ad) ← aclassAddr ad
        a5 := c
        pr := { pr with rest := pr.rest.set! i (pos, { ad with cls := c }) }
    | none => pure ()
  setP p pr
  if let some (start, stop) := oprange pr.as then
    for i in [start:stop] do
      let op := optab[i]!
      if xcmp a1 op.a1 && xcmp a2 op.a2 && xcmp a3 op.a3 && xcmp a4 op.a4 && xcmp a5 op.a5 &&
          pr.scond == op.scond then
        setP p { pr with optab := i + 1 }
        return op
  fail s!"oplook: illegal combination: {pr.as.name} {a1} {a2} {a3} {a4} {a5}, \
    {pr.from_.type.name} {pr.to.type.name}"

/-- `Optab.size` (`asm7.go:1107-1140`): the size of Prog `p` encoded with `o` (8 for the
`adrp`+`ld/st` form of an aligned `C_ADDR` move, else `o.size_`). -/
def optabSize (o : ARM64.Optab) (p : Nat) : AsmM Int := do
  let pr ← getP p
  let sz := movesize pr.as
  if 0 <= sz && sz <= 3 then
    let align : Int := 1 <<< sz.toNat
    let ok (a : Addr) : AsmM Bool := do
      if a.offset % align != 0 then return false
      match a.sym with
      | none => fail "optabSize: nil symbol of a C_ADDR operand"
      | some s =>
        let al ← symAlign s
        if al != 0 then return al >= align
        return true
    -- `o.a1 == C_ADDR && ok(&p.From) || o.a4 == C_ADDR && ok(&p.To)`, short-circuiting.
    if (o.a1 : Int) == C_ADDR then
      if ← ok pr.from_ then return 8
    if (o.a4 : Int) == C_ADDR then
      if ← ok pr.to then return 8
  return o.size_

/-- `splitImm24uScaled` (`asm7.go:1455-1484`): `hi, lo` with `v == hi + lo<<shift`
(`v` is an `int32`). -/
def splitImm24uScaled (v : Int) (shift : Nat) : Except String (Int × Int) := do
  if v < 0 then throw s!"{v} is not a 24 bit unsigned immediate"
  if v > 0xfff000 + (0xfff <<< shift) then
    throw s!"{v} is too large for a scaled 24 bit unsigned immediate"
  -- Try hi <= 0xfff and lo <= 0xfff such that v = hi + (lo << shift).
  let hi := max (v - (0xfff <<< shift)) (v % (2 ^ shift))
  if hi <= 0xfff then
    let lo := (v - hi) >>> shift
    if lo <= 0xfff then return (hi, lo)
  -- Try hi shifted left by 12 bits.
  let mut lo := (v >>> shift) % 0x1000
  let mut hi := v - (lo <<< shift)
  if hi > 0xfff000 then
    hi := 0xfff000
    lo := (v - hi) >>> shift
  -- `hi&^0xfff000 == 0`
  if hi % 0x1000 == 0 && hi >>> 24 == 0 && hi + (lo <<< shift) == v then return (hi, lo)
  throw s!"{v} cannot be split into valid hi/lo"

/-- `ctxt7.isUnsafePoint` (`asm7.go:1312-1318`). -/
def isUnsafePoint (p : Prog) : Bool :=
  p.from_.reg == REGTMP || p.to.reg == REGTMP || p.reg == REGTMP ||
    (p.from_.type == .REGREG && p.from_.offset == REGTMP) ||
    (p.to.type == .REGREG && p.to.offset == REGTMP)

/-- `ctxt7.isRestartable` (`asm7.go:1322-1335`). -/
def isRestartable (p : Nat) : AsmM Bool := do
  if isUnsafePoint (← getP p) then return false
  let o ← oplook p
  return (← optabSize o p) > 4 && o.flag.toNat &&& NOTUSETMP.toNat == 0

end GoFV.Asm
