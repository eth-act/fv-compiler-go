import GoFV.SSA.GoStr

/-!
# Source positions

Go's `src.XPos{index, lico}` with the `lico` bit fields split out (`docs/contracts/export.md`,
`pos`): `lico = line<<12 | col<<4 | xlogue<<2 | stmt`.
-/

namespace GoFV.SSA

/-- A `src.XPos`. `index` is the position base (`PosBase` table key, `p<index>`). -/
structure Pos where
  index : Nat
  line : Nat
  col : Nat
  /-- 0 `PosDefaultStmt`, 1 `PosIsStmt`, 2 `PosNotStmt`. -/
  stmt : Nat
  /-- 0 none, 1 `PosPrologueEnd`, 2 `PosEpilogueBegin`. -/
  xlogue : Nat
  deriving DecidableEq, Inhabited, Repr, Hashable

namespace Pos

/-- `src.NoXPos`. -/
def none : Pos := ⟨0, 0, 0, 0, 0⟩

/-- `lico` as Go packs it. -/
def lico (p : Pos) : Nat := p.line <<< 12 ||| p.col <<< 4 ||| p.xlogue <<< 2 ||| p.stmt

/-- `XPos.IsKnown`: index or line non-zero. -/
def isKnown (p : Pos) : Bool := p.index != 0 || p.line != 0

/-- `XPos.Before`: `(index, lico)` lexicographically smaller. -/
def before (p q : Pos) : Bool :=
  p.index < q.index || (p.index == q.index && p.lico < q.lico)

/-- `XPos.SameFileAndLine`. -/
def sameFileAndLine (p q : Pos) : Bool := p.index == q.index && p.line == q.line

end Pos

/-- A `src.PosBase` (`posbase` line). -/
structure PosBase where
  /-- Absolute file name. -/
  file : GoStr
  line : Int
  col : Int
  /-- `InliningIndex()`, −1 if not inlined. -/
  inl : Int
  deriving DecidableEq, Inhabited, Repr

end GoFV.SSA
