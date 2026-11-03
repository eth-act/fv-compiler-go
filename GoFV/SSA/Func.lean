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

/-- `SparseTreeNode` (`sparsetree.go`): dominator-tree links (block IDs, `none` for nil) and
the entry/exit numbers. The default is Go's zero node (blocks outside the tree). -/
structure SdomNode where
  parent : Option ID
  child : Option ID
  sibling : Option ID
  entry : Int
  exit : Int
  deriving DecidableEq, Inhabited, Repr

/-- One `cachedLineStarts` entry: `<index>:<first>:<last>` followed by the leftover pending
lines `:<line>=<val>` (dense order), or `<index>:-` (`bounds = none`, no pending lines). -/
structure LineRange where
  index : Nat
  bounds : Option (Int × Int)
  pending : Array (Int × Int)
  deriving DecidableEq, Inhabited, Repr

/-- A loop of the cached loop nest (`likelyadjust.go` `loop`); `outer` is an index into
`LoopNest.loops`. -/
structure Loop where
  header : ID
  outer : Option Nat
  nBlocks : Int
  depth : Int
  isInner : Bool
  /-- `containsUnavoidableCall` (computed and stored by `regalloc`). -/
  unavoidableCall : Bool
  deriving DecidableEq, Inhabited, Repr

/-- `f.cachedLoopnest` (`loopnest`, format 5): `b2l` has `b2lSize` slots (the block count when
the nest was built); its non-nil entries `(block ID, index into loops)` ascending by ID. -/
structure LoopNest where
  b2lSize : Nat
  irreducible : Bool
  loops : Array Loop
  b2l : Array (ID × Nat)
  deriving DecidableEq, Inhabited, Repr

/-- The `f.cached*` analyses that are non-nil (`cache` lines). -/
structure Caches where
  postorder : Option (Array ID) := none
  /-- `f.cachedIdom`, indexed by block ID (size `NumBlocks()` when computed; `none` for the
  entry and unreachable blocks). Exported for the blocks of `f.Blocks`, in that order. -/
  idom : Option (Array (Option ID)) := none
  /-- `f.cachedSdom`, indexed by block ID (exported like `idom`). -/
  sdom : Option (Array SdomNode) := none
  /-- `f.cachedLoopnest` (contents from format 5; no format-4 file has one). -/
  loopnest : Option LoopNest := none
  /-- `f.auxmap`: CSE's aux numbering (`none` key = nil aux), sorted by id. -/
  auxmap : Option (Array (Option AuxRef × Int)) := none
  lineStarts : Option (Array LineRange) := none
  deriving DecidableEq, Inhabited, Repr

/-- An `f.RegAlloc` entry (`ssa.Location`): a register (Go's dense register number, the index
into `GoFV.SSA.ARM64.registers`), a `LocalSlot`, a `LocPair` or `LocResults` of registers
(`none` for nil elements). -/
inductive Location where
  | reg (r : Nat)
  | slot (k : SlotKey)
  | pair (a b : Option Nat)
  | results (rs : Array (Option Nat))
  deriving DecidableEq, Inhabited, Repr

/-- State of the lowered passes (format 5; all empty before `lower`). -/
structure Lowered where
  /-- Blocks with `FlagsLiveAtEnd` (set by `flagalloc`), ascending ID. -/
  flagsLive : Array ID := #[]
  /-- Non-zero `Block.Hotness` (set by `loop rotate`), ascending ID. -/
  hotness : Array (ID × Nat) := #[]
  scheduled : Bool := false
  laidout : Bool := false
  /-- `f.RegAlloc` when non-nil: its length and the non-nil entries, ascending ID. -/
  regAlloc : Option (Nat × Array (ID × Location)) := none
  /-- `f.tempRegs` when non-nil, ascending ID. -/
  tempRegs : Option (Array (ID × Nat)) := none
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
  /-- `f.freeValues`, head first (a `List`: `newValue` pops and `freeValue` pushes the head). -/
  freeValues : List ID
  /-- `f.freeBlocks`, head first. -/
  freeBlocks : List ID
  cache : Caches
  /-- Lowered-pass state (format 5). -/
  low : Lowered := {}
  deriving DecidableEq, Inhabited

namespace Func

/-- The block with ID `id`, if it is in the function. -/
@[inline] def block? (f : Func) (id : ID) : Option Block := (f.blockTab[id]?).join

/-- The value with ID `id`, if it is in the function. -/
@[inline] def value? (f : Func) (id : ID) : Option Value := (f.valueTab[id]?).join

end Func

end GoFV.SSA
