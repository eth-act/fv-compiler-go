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

/-- `lico == 0`: Go's "no position" lico, on which `IsStmt` and `withStmt` are special. -/
def licoZero (p : Pos) : Bool := p.line == 0 && p.col == 0 && p.xlogue == 0 && p.stmt == 0

/-- `PosDefaultStmt`, `PosIsStmt`, `PosNotStmt` (`cmd/internal/src/pos.go`). -/
abbrev defaultStmt : Nat := 0
abbrev isStmtMark : Nat := 1
abbrev notStmt : Nat := 2

/-- `XPos.IsStmt()`: `PosNotStmt` for `lico == 0`, else the stmt bits. -/
def isStmt (p : Pos) : Nat := if p.licoZero then notStmt else p.stmt

/-- `lico.withStmt`: a zero lico stays zero, otherwise the stmt bits are replaced. -/
def withStmt (p : Pos) (s : Nat) : Pos := if p.licoZero then p else { p with stmt := s }

/-- `XPos.WithNotStmt`. -/
def withNotStmt (p : Pos) : Pos := p.withStmt notStmt
/-- `XPos.WithDefaultStmt`. -/
def withDefaultStmt (p : Pos) : Pos := p.withStmt defaultStmt
/-- `XPos.WithIsStmt`. -/
def withIsStmt (p : Pos) : Pos := p.withStmt isStmtMark

/-- `XPos.SameFile`. -/
def sameFile (p q : Pos) : Bool := p.index == q.index

/-- `XPos.After`. -/
def after (p q : Pos) : Bool := q.before p

/-- `withStmt` leaves a zero lico unchanged (Go: `if x == 0 { return lico(0) }`). -/
theorem withStmt_licoZero {p : Pos} (h : p.licoZero) (s : Nat) : p.withStmt s = p := by
  simp [withStmt, h]

/-- Non-vacuity: `NoXPos` has a zero lico. -/
example : Pos.none.licoZero := rfl

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
