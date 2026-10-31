/-!
# Op metadata types

Types of the per-op metadata in `GoFV.SSA.Op` (generated): Go's `auxType` and `SymEffect`
(`cmd/compile/internal/ssa/op.go`).
-/

namespace GoFV.SSA

/-- `ssa.auxType`: how a value's `Aux`/`AuxInt` fields are interpreted. Constructors are Go's
`aux*` constants without the prefix, in the same order. -/
inductive AuxType where
  | None | Bool | Int8 | Int16 | Int32 | Int64 | Int128 | UInt8 | Float32 | Float64
  | FlagConstant | CCop | NameOffsetInt8 | String | Sym | SymOff | SymValAndOff | Typ | TypSize
  | Call | CallOff | PanicBoundsC | PanicBoundsCC
  | ARM64BitField | ARM64ConditionalParams | S390XRotateParams | S390XCCMask | S390XCCMaskInt8
  | S390XCCMaskUint8 | SizeAndAlign
  deriving DecidableEq, Inhabited, Repr

/-- `ssa.SymEffect`, Go's bit set `SymRead | SymWrite | SymAddr` (`SymNone` is all false). -/
structure SymEffect where
  read : Bool
  write : Bool
  addr : Bool
  deriving DecidableEq, Inhabited, Repr

end GoFV.SSA
