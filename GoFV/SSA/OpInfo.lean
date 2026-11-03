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

/-- `ssa.regMask` (`regalloc.go`): bit `i` of `v1` (`i < 64`) or `v2` (`i ≥ 64`) allows register
number `i` of the arch's register list (`GoFV.SSA.ARM64.registers`). -/
structure RegMask where
  v1 : UInt64 := 0
  v2 : UInt64 := 0
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- `ssa.inputInfo` / `ssa.outputInfo`: argument or result index `idx` and its allowed registers. -/
structure RegIdx where
  idx : Nat
  regs : RegMask
  deriving DecidableEq, Inhabited, Repr

/-- `ssa.regInfo` as stored in `opcodeTable` (`op.go`): `inputs` (non-empty masks only) and
`outputs` in allocation order (fewest allowed registers first), registers clobbered by the op,
and whether it clobbers its first/second argument's register. -/
structure RegInfo where
  inputs : List RegIdx := []
  clobbers : RegMask := {}
  clobbersArg0 : Bool := false
  clobbersArg1 : Bool := false
  outputs : List RegIdx := []
  deriving DecidableEq, Inhabited, Repr

/-- `ssa.Register` without `objNum` (the `cmd/internal/obj` register number, an assembler
detail): the dense register number `num` and Go's name (`Register.String()`). -/
structure Register where
  num : Nat
  name : String
  deriving DecidableEq, Inhabited, Repr

end GoFV.SSA
