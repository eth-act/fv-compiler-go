import GoFV.SSA.Value

/-!
# Blocks

`ssa.Block` (`docs/contracts/ir.md`): controls and values as value IDs, edges as
`(block ID, reverse index)`.
-/

namespace GoFV.SSA

/-- `ssa.BranchPrediction`. -/
inductive BranchPrediction where
  | unlikely | unknown | likely
  deriving DecidableEq, Inhabited, Repr, Hashable

namespace BranchPrediction

/-- Go's integer value (−1, 0, 1). -/
def toInt : BranchPrediction → Int
  | .unlikely => -1 | .unknown => 0 | .likely => 1

def ofInt? : Int → Option BranchPrediction
  | -1 => some .unlikely | 0 => some .unknown | 1 => some .likely | _ => none

end BranchPrediction

/-- `ssa.Edge`: the block at the other end and the index of the reverse edge there
(`b.Succs[j] = ⟨c, i⟩` iff `c.Preds[i] = ⟨b, j⟩`). -/
structure Edge where
  b : ID
  i : Nat
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- An `ssa.Block`. -/
structure Block where
  id : ID
  kind : BlockKind
  pos : Pos
  likely : BranchPrediction
  auxInt : Int64
  aux : Option AuxRef
  /-- The non-nil `Controls` (at most 2). -/
  controls : Array ID
  succs : Array Edge
  preds : Array Edge
  /-- `b.Values`, in order. -/
  values : Array ID
  deriving DecidableEq, Inhabited

end GoFV.SSA
