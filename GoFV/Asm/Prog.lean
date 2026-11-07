import GoFV.Asm.As
import GoFV.SSA.Export

/-!
# Prog IR and the `gofv-prog 3` file

Lean mirrors of `cmd/internal/obj`'s `Addr`, `Prog`, `Reloc`, the `FuncInfo` fields and the
frame layout, as the Phase 3 export writes them (`docs/contracts/export.md`, "gofv-prog 3";
`docs/PASSES3.md` §1.1, §2). Every field is kept, defaults included: `checkaddr` and `aclass`
branch on them. Register fields are obj register numbers (`int16`, `REG_R0 = 8192`, arrangement
and extension encodings included; `GoFV.SSA.ARM64.Register.objNum` maps dense SSA registers to
them). Prog identity is a stable ID (allocation order in `objw`, then list order for Progs the
assembler adds), separate from the list order.
-/

namespace GoFV.Asm

open GoFV.SSA (GoStr Pos PosBase Token)

/-- `obj.AddrType` (`cmd/internal/obj/link.go`), in Go's order. -/
inductive AddrType where
  | NONE | BRANCH | TEXTSIZE | MEM | CONST | FCONST | SCONST | REG | ADDR | SHIFT | REGREG
  | REGREG2 | INDIR | REGLIST | SPECIAL
  deriving DecidableEq, Inhabited, Repr

/-- `obj.AddrName`, in Go's order. -/
inductive AddrName where
  | NONE | EXTERN | STATIC | AUTO | PARAM | GOTREF | TOCREF
  deriving DecidableEq, Inhabited, Repr

namespace AddrType
def all : Array AddrType := #[.NONE, .BRANCH, .TEXTSIZE, .MEM, .CONST, .FCONST, .SCONST, .REG,
  .ADDR, .SHIFT, .REGREG, .REGREG2, .INDIR, .REGLIST, .SPECIAL]
def name : AddrType → String
  | .NONE => "NONE" | .BRANCH => "BRANCH" | .TEXTSIZE => "TEXTSIZE" | .MEM => "MEM"
  | .CONST => "CONST" | .FCONST => "FCONST" | .SCONST => "SCONST" | .REG => "REG"
  | .ADDR => "ADDR" | .SHIFT => "SHIFT" | .REGREG => "REGREG" | .REGREG2 => "REGREG2"
  | .INDIR => "INDIR" | .REGLIST => "REGLIST" | .SPECIAL => "SPECIAL"
end AddrType

namespace AddrName
def all : Array AddrName := #[.NONE, .EXTERN, .STATIC, .AUTO, .PARAM, .GOTREF, .TOCREF]
def name : AddrName → String
  | .NONE => "NONE" | .EXTERN => "EXTERN" | .STATIC => "STATIC" | .AUTO => "AUTO"
  | .PARAM => "PARAM" | .GOTREF => "GOTREF" | .TOCREF => "TOCREF"
end AddrName

/-- `Addr.Val`: what the compiler and assembler store there for arm64. -/
inductive AddrVal where
  | none
  /-- A branch target (`*obj.Prog`), by Prog ID. -/
  | target (id : Nat)
  /-- The typed-nil `*obj.Prog` of `To.SetTarget(nil)` (`linkpatch` when `brloop` gives up on
  an infinite `JMP` chain): `Val != nil` but `Target() == nil`. The exporter writes it as a fresh
  Prog ID with a `warn` line, so it never appears in a parsed file. -/
  | nilTarget
  /-- `TYPE_TEXTSIZE`'s argument size (`int32`). -/
  | textSize (n : Int)
  /-- A `TYPE_FCONST` `float64`, as raw bits. -/
  | float (bits : UInt64)
  /-- A `TYPE_SCONST` string. -/
  | str (s : ByteArray)
  deriving DecidableEq, Inhabited

/-- `obj.Addr`. `sym` is a symbol number of the file (`y<n>`). -/
structure Addr where
  type : AddrType := .NONE
  reg : Int := 0
  index : Int := 0
  scale : Int := 0
  name : AddrName := .NONE
  /-- `Class`: the operand class `aclass` caches (+1), 0 before assembly. -/
  cls : Int := 0
  offset : Int := 0
  sym : Option Nat := none
  val : AddrVal := .none
  deriving DecidableEq, Inhabited

/-- `obj.Prog` (the fields arm64 code and the assembler use; the x86-only `Forwd`, `Rel`,
`Back`, `Ft`, `Tt` are always zero and not exported). -/
structure Prog where
  /-- Stable ID (`docs/contracts/export.md`, "Prog identity"). -/
  id : Nat
  /-- `Pc`: allocation number before assembly, the byte PC after `span7`. -/
  pc : Int
  spadj : Int
  isize : Nat
  /-- `Optab`: 1-based index into the sorted `optab`, 0 before `span7`. -/
  optab : Nat
  /-- `Pool`, by Prog ID. -/
  pool : Option Nat
  as : As
  scond : Nat
  from_ : Addr
  reg : Int
  /-- `RestArgs`: operand position (`obj.Source` 0, `obj.Destination` 1) and operand. -/
  rest : Array (Nat × Addr)
  to : Addr
  regTo2 : Int
  mark : Nat
  pos : Pos
  deriving DecidableEq, Inhabited

/-- `type` definition: the facts of a `*types.Type` the frame and liveness steps read. `none`
fields are `?` (size not calculated). `ptrMask` is the pointer bitmap (bit `i` = word `i`,
little-endian bytes) over `ptrdata`; empty when there are no pointer words. -/
structure TypeDef where
  size : Option Int
  align : Option Int
  ptrdata : Option Int
  hasPtr : Option Bool
  ptrMask : Option ByteArray
  str : GoStr
  deriving DecidableEq, Inhabited

/-- `name` definition: an `*ir.Name` of `Dcl`. `cls` is `ir.Class.String()`, `esc` is `n.Esc()`
(0 `EscUnknown`, 1 `EscNone`, 2 `EscHeap`, 3 `EscNever`), `linkName`/`linkAbi` the symbol
`n.Linksym()` resolves to (computed without a lookup), and `aux` the number of the same object in
the companion `.ssa` file's aux table (`none`: the `.ssa` file never references it). -/
structure NameDef where
  sym : GoStr
  cls : String
  type : Option Nat
  esc : Nat
  linkName : GoStr
  linkAbi : Nat
  aux : Option Nat
  deriving DecidableEq, Inhabited

/-- `inl` definition: node of the global inlining tree. -/
structure InlDef where
  parent : Option Nat
  pos : Pos
  func : Option Nat
  name : GoStr
  deriving DecidableEq, Inhabited

/-- What `.prog` files add to a position base (v3): `Filename()` (the name positions report,
`RelFilename`), and the base's own position `Pos()` (`RelFilename()`, `Line()`, `Col()`), which
`src.Pos.Before`, `RelLine` and `RelCol` read. -/
structure PosBaseExt where
  filename : GoStr
  posFilename : GoStr
  posLine : Nat
  posCol : Nat
  deriving DecidableEq, Inhabited, Repr

/-- A definition line. Definitions are numbered per file and written before their first use. -/
inductive Def where
  | type (n : Nat) (d : TypeDef)
  | name (n : Nat) (d : NameDef)
  /-- An `*obj.LSym` by name and ABI. -/
  | sym (n : Nat) (name : GoStr) (abi : Nat)
  /-- A position base; `fileIndex` is `PosBase.FileIndex()` (`none`: not registered). -/
  | posBase (i : Nat) (b : PosBase) (fileIndex : Option Int) (ext : PosBaseExt)
  | inl (k : Nat) (d : InlDef)
  deriving DecidableEq, Inhabited

/-- Flags of a `Dcl` entry, in the contract's order. -/
structure NameFlags where
  used : Bool := false
  addrtaken : Bool := false
  needzero : Bool := false
  opendeferslot : Bool := false
  nonmergeable : Bool := false
  autotmp : Bool := false
  outregs : Bool := false
  /-- `n.Heapaddr != nil`. -/
  heapaddr : Bool := false
  /-- `n.IsOutputParamHeapAddr()`. -/
  outheapaddr : Bool := false
  deriving DecidableEq, Inhabited

namespace NameFlags
def table : List (String × (NameFlags → Bool) × (NameFlags → NameFlags)) := [
  ("used", (·.used), ({ · with used := true })),
  ("addrtaken", (·.addrtaken), ({ · with addrtaken := true })),
  ("needzero", (·.needzero), ({ · with needzero := true })),
  ("opendeferslot", (·.opendeferslot), ({ · with opendeferslot := true })),
  ("nonmergeable", (·.nonmergeable), ({ · with nonmergeable := true })),
  ("autotmp", (·.autotmp), ({ · with autotmp := true })),
  ("outregs", (·.outregs), ({ · with outregs := true })),
  ("heapaddr", (·.heapaddr), ({ · with heapaddr := true })),
  ("outheapaddr", (·.outheapaddr), ({ · with outheapaddr := true }))]
end NameFlags

/-- A `Dcl` entry: the name, its `FrameOffset` and flags at that point. -/
structure DclEntry where
  name : Nat
  off : Int
  flags : NameFlags
  deriving DecidableEq, Inhabited

/-- The frame section: `AllocFrame`'s input and output (A1, A2). -/
structure Frame where
  defs : Array Def
  /-- `Dcl` when `AllocFrame` starts. -/
  dclIn : Array DclEntry
  /-- `Dcl` after (sorted, followers after their leader, truncated). -/
  dclOut : Array DclEntry
  /-- `OptDcl`: the truncated tail. -/
  optDcl : Array DclEntry
  /-- MergeLocals partitions: leader, followers in order. -/
  merges : Array (Nat × Array Nat)
  stksize : Int
  stkptrsize : Int
  stkalign : Int
  warns : Array GoStr
  deriving Inhabited

/-- `obj.RegSpill`. -/
structure Spill where
  addr : Addr
  reg : Int
  reg2 : Int
  spill : As
  unspill : As
  deriving DecidableEq, Inhabited

/-- `FuncInfo`'s metadata symbols (`funcaux` line), by symbol number. -/
structure FuncAux where
  gcArgs : Option Nat
  gcLocals : Option Nat
  stackObjects : Option Nat
  openCodedDeferInfo : Option Nat
  argInfo : Option Nat
  argLiveInfo : Option Nat
  wrapInfo : Option Nat
  deriving DecidableEq, Inhabited

/-- The text symbol and its `FuncInfo` at a cut point (`fn`, `spill`, `inlmark`, `jumptable`,
`funcaux` lines). `attr` is the raw `LSym.Attribute` (ABI bits included). -/
structure FuncInfo where
  sym : Nat
  args : Int
  locals : Int
  funcID : Nat
  funcFlag : Nat
  startLine : Int
  attr : Nat
  spills : Array Spill
  /-- `InlMarks`: Prog ID and global inlining index. -/
  inlMarks : Array (Nat × Int)
  /-- `JumpTables`: table symbol, target Prog IDs. -/
  jumpTables : Array (Nat × Array Nat)
  aux : FuncAux
  deriving DecidableEq, Inhabited

/-- `ssa.Spill` of `f.RegArgs`: obj register, frame offset, type. -/
structure RegArg where
  reg : Int
  off : Int
  type : Option Nat
  deriving DecidableEq, Inhabited

/-- The text symbol's `FuncInfo` header (`fn` line fields other than the records). -/
structure TextInfo where
  sym : Nat
  args : Int
  locals : Int
  funcID : Nat
  funcFlag : Nat
  startLine : Int
  attr : Nat
  deriving DecidableEq, Inhabited

/-- The genin section: what `genssa` reads besides the SSA and the frame, recorded when
`ssagen.Compile` calls it (after `buildssa`). -/
structure GenIn where
  defs : Array Def
  /-- `curfn.Pos()`. -/
  fnPos : Pos
  /-- `curfn.HasDefer()`. -/
  hasDefer : Bool
  /-- `curfn.OpenCodedDeferDisallowed()`. -/
  openDeferDisallowed : Bool
  /-- The symbol `curfn.WrappedFunc.Linksym()` resolves to: name and ABI. -/
  wrapped : Option (GoStr × Nat)
  /-- Open-coded defers (`emitOpenDeferInfo`): `deferBitsTemp` and the closure slots in defer
  order. -/
  openDefer : Option (Nat × Array Nat)
  /-- `f.RegArgs` when `genssa` starts. -/
  regArgs : Array RegArg
  /-- The text symbol's `FuncInfo` header when `genssa` starts (set by `InitTextSym`). -/
  text : TextInfo
  warns : Array GoStr
  deriving Inhabited

/-- `ssa.LocListEntry`: a location list entry in SSA coordinates (`BlockStart` = -10000,
`BlockEnd` = -20000, `FuncEnd` = -30000 as value IDs) and its DWARF location expression. -/
structure LocEntry where
  startBlock : Int
  startValue : Int
  endBlock : Int
  endValue : Int
  expr : ByteArray
  deriving Inhabited

instance : BEq LocEntry where
  beq a b := a.startBlock == b.startBlock && a.startValue == b.startValue &&
    a.endBlock == b.endBlock && a.endValue == b.endValue && a.expr.data == b.expr.data

/-- `ssa.FuncDebug` after `BuildFuncDebug` (E1, `dbg*` lines of `prog0`, v3). -/
structure FuncDebug where
  entry : Int
  /-- `Slots` by `SlotID`: name, type, offset. -/
  slots : Array (Nat × Option Nat × Int)
  /-- `Vars` by `VarID` with `VarSlots`. -/
  vars : Array (Nat × Array Nat)
  /-- The nonempty `LocationLists`: (`VarID`, entries). -/
  lists : Array (Nat × Array LocEntry)
  regOutputParams : Array Nat
  /-- `GetPC` at the cut for the list endpoints it resolves through a Prog (every endpoint
  but `FuncEnd` and the entry block's `BlockStart`): (block, value, Prog ID). -/
  pcs : Array (Int × Int × Nat)
  deriving Inhabited

/-- `obj.Reloc`; `type` is `objabi.RelocType.String()`. -/
structure Reloc where
  off : Int
  siz : Nat
  type : String
  add : Int
  sym : Option Nat
  deriving DecidableEq, Inhabited

/-- The prog0 section: the Prog list after `genssa` (after `defframe`, before `Flush`; P0). -/
structure Prog0 where
  defs : Array Def
  progs : Array Prog
  fn : FuncInfo
  /-- `Dcl` names with `Needzero` after liveness. -/
  needzero : Array Nat
  regArgs : Array RegArg
  /-- The text symbol's `Size`, `Align`, `P` and `R` at the cut (v3; `R` holds the marker
  relocations the frontend and the SSA passes added). -/
  textSize : Int
  textAlign : Int
  text : ByteArray
  relocs : Array Reloc
  /-- `LSym.Align` of the symbols the Prog operands reference, where nonzero (v3). -/
  symAlign : Array (Nat × Int)
  /-- `FuncInfo.Autot`: the type symbols of autos recorded for DWARF (a set, number order). -/
  autot : Array Nat
  /-- `curfn.DebugInfo` after `genssa` (`none`: not set). -/
  dbg : Option FuncDebug
  warns : Array GoStr
  deriving Inhabited

/-- Contents of a data symbol (`data` line): kind (`objabi.SymKind.String()`), size, alignment,
raw attributes, bytes, relocations. -/
structure SymData where
  sym : Nat
  kind : String
  size : Int
  align : Int
  attr : Nat
  data : ByteArray
  relocs : Array Reloc
  deriving DecidableEq, Inhabited

/-- `FuncInfo.Pcln`: the pc-value table symbols and funcdata slots (`none`: nil). -/
structure Pcln where
  pcsp : Option Nat
  pcfile : Option Nat
  pcline : Option Nat
  pcinline : Option Nat
  pcdata : Array (Option Nat)
  funcdata : Array (Option Nat)
  deriving DecidableEq, Inhabited

/-- A node of the function's local inlining tree (`Pcln.InlTree`). -/
structure InlNode where
  parent : Int
  pos : Pos
  func : Option Nat
  name : GoStr
  parentPC : Int
  deriving DecidableEq, Inhabited

/-- The asm section: the function after `Flush` and the `Compile` tail (M). -/
structure Asm where
  defs : Array Def
  progs : Array Prog
  fn : FuncInfo
  textSize : Int
  textAlign : Int
  /-- `LSym.P` of the text symbol. -/
  text : ByteArray
  /-- `LSym.R` of the text symbol, in append order. -/
  relocs : Array Reloc
  pcln : Pcln
  usedFiles : Array Nat
  inlTree : Array InlNode
  /-- Contents of the function's metadata symbols and the assembler's constant symbols. -/
  data : Array SymData
  warns : Array GoStr
  deriving Inhabited

/-- The location list of a `dwarf.Var`: none, the `FuncDebug` variable's, or one `dwarfgen`
built (the heap-dereference list of a conservative variable). -/
inductive VarList where
  | none
  | var (k : Nat)
  | entries (es : Array LocEntry)
  deriving Inhabited, BEq

/-- `dwarf.Var` (`var` line). -/
structure DwVar where
  scope : Int
  name : GoStr
  tag : Nat
  withLoclist : Bool
  isReturnValue : Bool
  isInlFormal : Bool
  dictIndex : Nat
  stackOffset : Int
  type : Option Nat
  declFile : GoStr
  declLine : Nat
  declCol : Nat
  inlIndex : Int
  childIndex : Int
  isInAbstract : Bool
  closureOffset : Int
  list : VarList
  deriving Inhabited, BEq

/-- `dwarf.Scope`; its variables by index into `Dwarf.vars`. -/
structure DwScope where
  parent : Int
  ranges : Array (Int × Int)
  vars : Array Nat
  deriving Inhabited, BEq

/-- `dwarf.InlCall`; `CallPos` as (`FileIndex()`, `RelLine()`); its variables by index into
`Dwarf.vars`. -/
structure DwInlCall where
  inlIndex : Int
  callFile : Int
  callLine : Nat
  absFun : Option Nat
  children : Array Nat
  root : Bool
  ranges : Array (Int × Int)
  vars : Array Nat
  deriving Inhabited, BEq

/-- `populateDWARF`'s `dwarf.FnState` (`dwfn` line): the DWARF symbols, the name, `StartPos`
as (`FileIndex()`, `RelLine()`), `External`, `s.Wrapper()`, `UseBASEntries`, `DwTextCount`. -/
structure DwFn where
  info : Nat
  loc : Option Nat
  ranges : Nat
  absfn : Option Nat
  lines : Nat
  name : GoStr
  startFile : Int
  startLine : Nat
  external : Bool
  wrapper : Bool
  useBASEntries : Bool
  dwTextCount : Nat
  deriving Inhabited

/-- The facts `dwarfgen.Info` reads of an `*ir.Name` (`dwname` line) besides its definition:
`Op() == ONAME`, `Used()`, `IsAutoTmp`, `InlFormal()`, `InlLocal()`, `DictIndex`, `FrameOffset()`,
`IsOutputParamInRegisters()`, `Heapaddr`, `Canonical()` (when not itself), `TypeSymName` of its
type (`none`: not computed, the type's size is unknown), `IsUntyped()`, kind `TSSA`,
`CanSSA` (`none`: unknown) and `Pos()`. -/
structure DwName where
  name : Nat
  oname : Bool
  used : Bool
  autotmp : Bool
  inlFormal : Bool
  inlLocal : Bool
  dictIndex : Nat
  frameOffset : Int
  outregs : Bool
  heapaddr : Option Nat
  canonical : Option Nat
  typeSym : Option GoStr
  untyped : Bool
  tssa : Bool
  canSSA : Option Bool
  pos : Pos
  deriving Inhabited, BEq

/-- The dwarf section (v3): `populateDWARF`'s state and the function's DWARF symbols at the
end of `Compile` (E2). -/
structure Dwarf where
  defs : Array Def
  /-- `none` when `populateDWARF` did not run. -/
  fn : Option DwFn
  /-- `dwarfgen.Info`'s inputs besides the frame, `FuncDebug` and Progs: `fn.Dcl`; `Needctxt()`
  and the closure variables' offsets (`NewClosureStructIter`, with `Heapaddr` entries);
  `fn.Marks` (position, scope); `fn.Parents`; the signature's parameter names
  (`RecvParamsResults`, `none` when not a name); the pre-inlining `Inl.Dcl` of the function (if
  inlined) and of the inlined functions: (function, abstract-function symbol, names); the
  names' facts. -/
  dcl : Array Nat
  needctxt : Bool
  closure : Array (Nat × Int)
  marks : Array (Pos × Nat)
  parents : Array Nat
  params : Array (Option Nat)
  precursors : Array (Nat × Nat × Array Nat)
  names : Array DwName
  /-- Every distinct `dwarf.Var` of the scopes and inlined calls (identity matters:
  `putscope` skips the variables of inlined calls), the scopes' first. -/
  vars : Array DwVar
  scopes : Array DwScope
  inlCalls : Array DwInlCall
  /-- Child-DIE references (`ReferenceChildDIE`): symbol, relocation index, abstract function,
  declaration index; the relocations' `Add` are written before any child offset is added. -/
  dieRefs : Array (Nat × Nat × Nat × Int)
  /-- `RegisterChildDIEOffsets` of the abstract function: (`ChildIndex`, offset). -/
  dieOffs : Option (Nat × Array (Int × Int))
  /-- info, loc, ranges, debug lines, abstract function (those that exist). -/
  data : Array SymData
  warns : Array GoStr
  deriving Inhabited

/-- A `gofv-prog 3` file. -/
structure ProgFile where
  pkg : GoStr
  name : GoStr
  abi : Nat
  config : Array (String × Token)
  frame : Frame
  genin : GenIn
  prog0 : Prog0
  asm : Asm
  dwarf : Dwarf
  deriving Inhabited

end GoFV.Asm
