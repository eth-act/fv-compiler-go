import GoFV.SSA.Type
import GoFV.SSA.Pos

/-!
# Aux objects and local slots

Go's `Aux` interface values and `*LocalSlot`s as the export carries them
(`docs/contracts/export.md`, `aux`/`abiparam`/`reloc`/`rtype`/`slot` lines). Values, blocks and
functions refer to them by per-file table number (`AuxRef` `a<n>`, `SlotRef` `s<n>`); two
references are equal iff the Go values are `==`.
-/

namespace GoFV.SSA

/-- Per-file aux table number (`a<n>`, from 1). -/
abbrev AuxRef := Nat
/-- Per-file local slot table number (`s<n>`, from 1). -/
abbrev SlotRef := Nat

/-- `ir.Class`. -/
inductive NameClass where
  | Pxxx | PEXTERN | PAUTO | PAUTOHEAP | PPARAM | PPARAMOUT | PTYPEPARAM | PFUNC
  deriving DecidableEq, Inhabited, Repr, Hashable

namespace NameClass

def all : Array NameClass :=
  #[.Pxxx, .PEXTERN, .PAUTO, .PAUTOHEAP, .PPARAM, .PPARAMOUT, .PTYPEPARAM, .PFUNC]

/-- `ir.Class.String()`. -/
def name : NameClass → String
  | .Pxxx => "Pxxx" | .PEXTERN => "PEXTERN" | .PAUTO => "PAUTO" | .PAUTOHEAP => "PAUTOHEAP"
  | .PPARAM => "PPARAM" | .PPARAMOUT => "PPARAMOUT" | .PTYPEPARAM => "PTYPEPARAM"
  | .PFUNC => "PFUNC"

def ofName? (s : String) : Option NameClass := all.find? (·.name == s)

end NameClass

/-- Flags of an `*ir.Name` (`name` aux), in export order. -/
structure NameFlags where
  addrtaken : Bool := false
  used : Bool := false
  autotmp : Bool := false
  nonmergeable : Bool := false
  opendeferslot : Bool := false
  readonly : Bool := false
  /-- Format 3: the address of this variable reaches a conversion to an integer in the
  function's `start` section (`Convert` to `uintptr`, through pointer/integer arithmetic,
  copies and phis), computed once by the exporter and kept in every section. -/
  addrconv : Bool := false
  /-- Format 4: ssagen's `deferBits` variable of a function with open-coded defers (the
  `uint8` autotmp whose bits say which `opendeferslot` closures are still to run). -/
  deferbits : Bool := false
  deriving DecidableEq, Inhabited, Repr, Hashable

def NameFlags.table : List (String × (NameFlags → Bool) × (NameFlags → NameFlags)) :=
  [("addrtaken", (·.addrtaken), ({ · with addrtaken := true })),
   ("used", (·.used), ({ · with used := true })),
   ("autotmp", (·.autotmp), ({ · with autotmp := true })),
   ("nonmergeable", (·.nonmergeable), ({ · with nonmergeable := true })),
   ("opendeferslot", (·.opendeferslot), ({ · with opendeferslot := true })),
   ("readonly", (·.readonly), ({ · with readonly := true })),
   ("addrconv", (·.addrconv), ({ · with addrconv := true })),
   ("deferbits", (·.deferbits), ({ · with deferbits := true }))]

/-- Flags of an `*obj.LSym` (`sym` aux), in export order. -/
structure SymFlags where
  dupok : Bool := false
  «local» : Bool := false
  static : Bool := false
  contentaddressable : Bool := false
  wrapper : Bool := false
  abiwrapper : Bool := false
  deriving DecidableEq, Inhabited, Repr, Hashable

def SymFlags.table : List (String × (SymFlags → Bool) × (SymFlags → SymFlags)) :=
  [("dupok", (·.dupok), ({ · with dupok := true })),
   ("local", (·.local), ({ · with «local» := true })),
   ("static", (·.static), ({ · with static := true })),
   ("contentaddressable", (·.contentaddressable), ({ · with contentaddressable := true })),
   ("wrapper", (·.wrapper), ({ · with wrapper := true })),
   ("abiwrapper", (·.abiwrapper), ({ · with abiwrapper := true }))]

/-- A relocation of an `*obj.LSym` (`reloc` line). -/
structure Reloc where
  off : Int
  siz : Int
  /-- `objabi.RelocType.String()`. -/
  type : String
  add : Int
  target : GoStr
  targetAbi : Int
  deriving DecidableEq, Inhabited, Repr

/-- What `rewriteFixedLoad` folds a load from a type descriptor to (`rtype` line). Fields that
need an uncalculated size are `none`. -/
structure RType where
  size : Option Int
  ptrdata : Option Int
  hash : Option Int
  abiKind : Option Int
  gcdata : GoStr
  elemSym : GoStr
  deriving DecidableEq, Inhabited, Repr

/-- `abi.ABIParamAssignment` (`abiparam` line). -/
structure ABIParam where
  /-- `true` for results (`out`). -/
  out : Bool
  index : Nat
  type : TypeRef
  name : Option AuxRef
  /-- `abi.RegIndex` list; empty if on the stack. -/
  regs : Array Nat
  offset : Int
  deriving DecidableEq, Inhabited, Repr

/-- `*ssa.AuxCall` ABI data (`call` aux); `none` when `abiInfo == nil`. -/
structure CallABI where
  /-- `abiInfo.Config().Which()`. -/
  abi : Nat
  nin : Nat
  nout : Nat
  spillOff : Int
  spillSize : Int
  inRegs : Int
  outRegs : Int
  /-- `nin + nout` parameter assignments: inputs, then outputs. -/
  params : Array ABIParam
  deriving DecidableEq, Inhabited, Repr

/-- The Go dynamic type of an aux value with its contents. -/
inductive AuxKind where
  /-- `*ir.Name`; `esc` is `n.Esc()` (0 `EscUnknown`, 1 `EscNone`, 2 `EscHeap`, 3 `EscNever`),
  `pos` is `n.Pos()`. -/
  | name (sym : GoStr) (cls : NameClass) (type : TypeRef) (frameOffset : Int) (esc : Nat)
      (flags : NameFlags) (pos : Pos)
  /-- `*obj.LSym`. `data` is `lsym.P`, only for `SRODATA` symbols. -/
  | sym (name : GoStr) (abi : Nat) (kind : String) (size : Int) (flags : SymFlags)
      (typeInfo itabInfo : Option TypeRef) (data : Option ByteArray) (relocs : Array Reloc)
      (rtype : Option RType)
  /-- `stringAux` with the name of its `StringData` symbol. -/
  | str (s : GoStr) (dataSym : GoStr)
  /-- `*AuxCall`: the callee symbol (an aux) and the ABI analysis. -/
  | call (fn : Option AuxRef) (abi : Option CallABI)
  /-- `*AuxNameOffset`. -/
  | nameOff (name : AuxRef) (offset : Int)
  /-- `*types.Type`. -/
  | type (t : TypeRef)
  /-- `int64Aux`. -/
  | int (n : Int)
  /-- `auxMark`. -/
  | mark
  /-- `PanicBoundsC`. -/
  | pbc (c : Int)
  /-- `PanicBoundsCC`. -/
  | pbcc (cx cy : Int)
  /-- Any other Go type (`%T`); must not occur. -/
  | unknown (goType : GoStr)
  deriving DecidableEq, Inhabited

/-- An `aux` line (with its sub-lines). -/
structure AuxDef where
  /-- `fmt.Sprint(aux)`, what `LongString` prints inside `{…}`. -/
  fmt : GoStr
  kind : AuxKind
  deriving DecidableEq, Inhabited

/-- A `*LocalSlot` (`slot` line). -/
structure SlotDef where
  name : AuxRef
  type : TypeRef
  off : Int
  splitOf : Option SlotRef
  splitOffset : Int
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- A `LocalSlot` written inline (`namedx`, `canon`): same fields as `SlotDef`. -/
abbrev SlotKey := SlotDef

end GoFV.SSA
