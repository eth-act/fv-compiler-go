import GoFV.SSA.Op
import GoFV.SSA.AuxData

/-!
# Values

`ssa.Value` (`docs/contracts/ir.md`). Arguments are value IDs; the value's block is a block ID.
-/

namespace GoFV.SSA

/-- `ssa.ID` of a value or block (Go: `int32`, dense from 1). -/
abbrev ID := Nat

/-- An `ssa.Value`. -/
structure Value where
  id : ID
  op : Op
  type : TypeRef
  /-- `v.AuxInt`, Go `int64` (floats as `math.Float64bits`). -/
  auxInt : Int64
  aux : Option AuxRef
  pos : Pos
  /-- `v.Uses`: occurrences of `v` in `Args` and `Controls` of live values/blocks. -/
  uses : Nat
  args : Array ID
  /-- `v.Block.ID`. -/
  block : ID
  deriving DecidableEq, Inhabited

end GoFV.SSA
