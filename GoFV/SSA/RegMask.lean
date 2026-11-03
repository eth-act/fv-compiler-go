import GoFV.SSA.OpInfo

/-!
# Register masks

The `regMask` operations of `regalloc.go` (go1.27.3, lines 167-260): a two-word bit set over
the dense register numbers of `GoFV.SSA.ARM64.registers`. `pickReg` takes the lowest set bit
(the RISCV64 preference of `regAllocState.pickReg` does not apply to arm64).
-/

namespace GoFV.SSA

namespace RegMask

/-- `noRegister` (255): Go's sentinel for "no register". -/
def noReg : Nat := 255

@[inline] def inter (r s : RegMask) : RegMask := ⟨r.v1 &&& s.v1, r.v2 &&& s.v2⟩
@[inline] def union (r s : RegMask) : RegMask := ⟨r.v1 ||| s.v1, r.v2 ||| s.v2⟩
/-- `r.minus(s)` (`&^`). -/
@[inline] def minus (r s : RegMask) : RegMask := ⟨r.v1 &&& ~~~s.v1, r.v2 &&& ~~~s.v2⟩
@[inline] def isEmpty (r : RegMask) : Bool := r.v1 == 0 && r.v2 == 0

/-- `regMaskAt(i)`. -/
@[inline] def single (i : Nat) : RegMask :=
  if i < 64 then ⟨(1 : UInt64) <<< i.toUInt64, 0⟩ else ⟨0, (1 : UInt64) <<< (i - 64).toUInt64⟩

@[inline] def addReg (r : RegMask) (i : Nat) : RegMask := r.union (single i)
@[inline] def removeReg (r : RegMask) (i : Nat) : RegMask := r.minus (single i)

@[inline] def hasReg (r : RegMask) (i : Nat) : Bool :=
  if i < 64 then (r.v1 >>> i.toUInt64) &&& 1 != 0
  else if i < 128 then (r.v2 >>> (i - 64).toUInt64) &&& 1 != 0
  else false

/-- Index of the lowest set bit of a non-zero word. -/
def ctz (x : UInt64) : Nat := Id.run do
  for i in [0:64] do
    if (x >>> i.toUInt64) &&& 1 != 0 then return i
  return 64

/-- `r.pickReg()`: the lowest register (`none` for the empty set, where Go panics). -/
def pick? (r : RegMask) : Option Nat :=
  if r.v1 != 0 then some (ctz r.v1)
  else if r.v2 != 0 then some (ctz r.v2 + 64)
  else none

/-- Population count of one word. -/
def popcount (x : UInt64) : Nat := Id.run do
  let mut n := 0
  for i in [0:64] do
    if (x >>> i.toUInt64) &&& 1 != 0 then n := n + 1
  return n

/-- `countRegs(r)`. -/
def count (r : RegMask) : Nat := popcount r.v1 + popcount r.v2

/-- Parse a hex mask as written in `config` lines (`13ffffff`). -/
def ofHex? (s : String) : Option RegMask := do
  let mut n : Nat := 0
  for c in s.toList do
    let d ← if c.isDigit then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else none
    n := n * 16 + d
  return ⟨(n % 2 ^ 64).toUInt64, (n / 2 ^ 64).toUInt64⟩

end RegMask

end GoFV.SSA
