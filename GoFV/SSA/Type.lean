import GoFV.SSA.GoStr

/-!
# Types

Go's `*types.Type`, as far as the export (`docs/contracts/export.md`, `type`/`field` lines)
carries it. A function refers to types by their per-file table number (`TypeRef`, `t<n>`);
two references are equal iff the Go pointers are equal. The table itself is
`GoFV.SSA.Tables.types`.
-/

namespace GoFV.SSA

/-- Per-file type table number (`t<n>`, from 1). -/
abbrev TypeRef := Nat

/-- `types.Kind`, constructors named as Go's `T*` constants without the prefix. -/
inductive TypeKind where
  | xxx
  | INT8 | UINT8 | INT16 | UINT16 | INT32 | UINT32 | INT64 | UINT64 | INT | UINT | UINTPTR
  | COMPLEX64 | COMPLEX128
  | FLOAT32 | FLOAT64
  | BOOL
  | PTR | FUNC | SLICE | ARRAY | STRUCT | CHAN | MAP | INTER | FORW | ANY | STRING | UNSAFEPTR
  | IDEAL | NIL | BLANK
  | FUNCARGS | CHANARGS
  | SSA | TUPLE | RESULTS
  deriving DecidableEq, Inhabited, Repr, Hashable

namespace TypeKind

def all : Array TypeKind := #[.xxx, .INT8, .UINT8, .INT16, .UINT16, .INT32, .UINT32, .INT64,
  .UINT64, .INT, .UINT, .UINTPTR, .COMPLEX64, .COMPLEX128, .FLOAT32, .FLOAT64, .BOOL, .PTR,
  .FUNC, .SLICE, .ARRAY, .STRUCT, .CHAN, .MAP, .INTER, .FORW, .ANY, .STRING, .UNSAFEPTR, .IDEAL,
  .NIL, .BLANK, .FUNCARGS, .CHANARGS, .SSA, .TUPLE, .RESULTS]

/-- The export spelling (Go's constant name without `T`). -/
def name : TypeKind → String
  | .xxx => "xxx" | .INT8 => "INT8" | .UINT8 => "UINT8" | .INT16 => "INT16"
  | .UINT16 => "UINT16" | .INT32 => "INT32" | .UINT32 => "UINT32" | .INT64 => "INT64"
  | .UINT64 => "UINT64" | .INT => "INT" | .UINT => "UINT" | .UINTPTR => "UINTPTR"
  | .COMPLEX64 => "COMPLEX64" | .COMPLEX128 => "COMPLEX128" | .FLOAT32 => "FLOAT32"
  | .FLOAT64 => "FLOAT64" | .BOOL => "BOOL" | .PTR => "PTR" | .FUNC => "FUNC"
  | .SLICE => "SLICE" | .ARRAY => "ARRAY" | .STRUCT => "STRUCT" | .CHAN => "CHAN"
  | .MAP => "MAP" | .INTER => "INTER" | .FORW => "FORW" | .ANY => "ANY" | .STRING => "STRING"
  | .UNSAFEPTR => "UNSAFEPTR" | .IDEAL => "IDEAL" | .NIL => "NIL" | .BLANK => "BLANK"
  | .FUNCARGS => "FUNCARGS" | .CHANARGS => "CHANARGS" | .SSA => "SSA" | .TUPLE => "TUPLE"
  | .RESULTS => "RESULTS"

def ofName? (s : String) : Option TypeKind := all.find? (·.name == s)

end TypeKind

/-- The `flags` of a `type` line, in the export's order. -/
structure TypeFlags where
  /-- `t.HasPointers()` (only exported when the size is known). -/
  hasptr : Bool := false
  notinheap : Bool := false
  noalg : Bool := false
  shape : Bool := false
  /-- `types.IsDirectIface(t)`. -/
  direct : Bool := false
  /-- `types.IsComparable(t)`. -/
  comparable : Bool := false
  /-- `t.Sym() != nil`. -/
  named : Bool := false
  emptyiface : Bool := false
  variadic : Bool := false
  deriving DecidableEq, Inhabited, Repr, Hashable

namespace TypeFlags

/-- Flag names in export order, with their getters and setters. -/
def table : List (String × (TypeFlags → Bool) × (TypeFlags → TypeFlags)) :=
  [("hasptr", (·.hasptr), ({ · with hasptr := true })),
   ("notinheap", (·.notinheap), ({ · with notinheap := true })),
   ("noalg", (·.noalg), ({ · with noalg := true })),
   ("shape", (·.shape), ({ · with shape := true })),
   ("direct", (·.direct), ({ · with direct := true })),
   ("comparable", (·.comparable), ({ · with comparable := true })),
   ("named", (·.named), ({ · with named := true })),
   ("emptyiface", (·.emptyiface), ({ · with emptyiface := true })),
   ("variadic", (·.variadic), ({ · with variadic := true }))]

end TypeFlags

/-- A struct field or function parameter (`field` line). -/
structure Field where
  /-- `Field.Sym.Name`, empty if there is no symbol. -/
  name : GoStr
  type : TypeRef
  /-- `Field.Offset`; `none` when not calculated (`?`). -/
  offset : Option Int
  embedded : Bool
  deriving DecidableEq, Inhabited, Repr

/-- The kind-specific part of a type. -/
inductive TypeTail where
  /-- Scalars, `STRING`, `UNSAFEPTR`, `INTER`, `MAP`, `CHAN`, `SSA`, …. -/
  | none
  /-- `PTR`, `SLICE`: the element type. -/
  | elem (t : TypeRef)
  /-- `ARRAY`: element type and `NumElem`. -/
  | array (elem : TypeRef) (n : Int)
  /-- `STRUCT`: the fields. -/
  | struct (fields : Array Field)
  /-- `FUNC`: receiver, parameters and results (in that order in `fields`). -/
  | func (nrecv nparams nresults : Nat) (fields : Array Field)
  /-- `TUPLE`: the two components. -/
  | tuple (first second : TypeRef)
  /-- `RESULTS`: the result types (memory last). -/
  | results (ts : Array TypeRef)
  deriving DecidableEq, Inhabited, Repr

/-- A `type` line (with its `field` lines). -/
structure TypeDef where
  kind : TypeKind
  /-- `t.Size()`; `none` when never calculated (`?`). -/
  size : Option Int
  align : Option Int
  /-- `types.PtrDataSize(t)`; `none` when unknown or for `SSA`/`TUPLE`/`RESULTS`. -/
  ptrdata : Option Int
  flags : TypeFlags
  /-- `t.String()`. -/
  str : GoStr
  /-- `types.TypeSymName(t)`, empty when not applicable. -/
  symName : GoStr
  tail : TypeTail
  deriving DecidableEq, Inhabited, Repr

end GoFV.SSA
