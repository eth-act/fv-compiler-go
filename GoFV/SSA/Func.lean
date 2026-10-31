import GoFV.SSA.Block

/-!
# Functions

`ssa.Func` as the passes see it (`docs/contracts/ir.md`): `f.Blocks` order as a list of block
IDs, blocks and values in tables indexed by ID, plus the per-function state that decides what
a pass allocates or reuses (ID counters, free lists, constant cache, local slot maps) and the
CFG caches that survive between passes.
-/

namespace GoFV.SSA

/-- A `CanonicalLocalSplits` key: parent slot, offset, type. -/
structure SplitKey where
  parent : SlotRef
  off : Int
  type : TypeRef
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- One `SparseTree` node of `cache sdom`: `b<ID>:<parent>:<child>:<sibling>:<entry>:<exit>`
(`parent`/`child`/`sibling` are block IDs, `none` for nil). -/
structure SdomNode where
  block : ID
  parent : Option ID
  child : Option ID
  sibling : Option ID
  entry : Int
  exit : Int
  deriving DecidableEq, Inhabited, Repr

/-- One `cachedLineStarts` file range: `<index>:<first>:<last>`. -/
structure LineRange where
  index : Nat
  first : Int
  last : Int
  deriving DecidableEq, Inhabited, Repr

/-- The `f.cached*` analyses that are non-nil (`cache` lines). -/
structure Caches where
  postorder : Option (Array ID) := none
  /-- Per block of `f.Blocks` (in the exported order): its immediate dominator. -/
  idom : Option (Array (ID × Option ID)) := none
  sdom : Option (Array SdomNode) := none
  /-- Only presence is exported. -/
  loopnest : Bool := false
  /-- `f.auxmap`: CSE's aux numbering, sorted by id. -/
  auxmap : Option (Array (AuxRef × Int)) := none
  lineStarts : Option (Array LineRange) := none
  deriving DecidableEq, Inhabited, Repr

/-- An `ssa.Func`. -/
structure Func where
  entry : ID
  /-- `f.Type`. -/
  type : TypeRef
  ownAux : Option AuxRef
  /-- `f.vid.last`: the last value ID handed out. -/
  vidLast : Nat
  /-- `f.bid.last`. -/
  bidLast : Nat
  /-- `f.Blocks`, in order. -/
  blocks : Array ID
  /-- Blocks by ID (`none` for IDs not in `f.Blocks`). -/
  blockTab : Array (Option Block)
  /-- Values by ID (`none` for IDs not in any block). -/
  valueTab : Array (Option Value)
  /-- `f.Names`, in order, each with `f.NamedValues[*s]`. -/
  names : Array (SlotRef × Array ID)
  /-- `NamedValues` keys not in `f.Names` (sorted as exported). -/
  namedx : Array (SlotKey × Array ID)
  /-- `f.CanonicalLocalSplits`, sorted by key. -/
  splits : Array (SplitKey × SlotRef)
  /-- `f.CanonicalLocalSlots`, sorted by key. -/
  canon : Array (SlotKey × SlotRef)
  /-- `f.constants`: non-empty entries, keys ascending, values in slice order. -/
  consts : Array (Int64 × Array ID)
  /-- `f.freeValues`, head first. -/
  freeValues : Array ID
  /-- `f.freeBlocks`, head first. -/
  freeBlocks : Array ID
  cache : Caches
  deriving DecidableEq, Inhabited

namespace Func

/-- The block with ID `id`, if it is in the function. -/
@[inline] def block? (f : Func) (id : ID) : Option Block := (f.blockTab[id]?).join

/-- The value with ID `id`, if it is in the function. -/
@[inline] def value? (f : Func) (id : ID) : Option Value := (f.valueTab[id]?).join

end Func

end GoFV.SSA
