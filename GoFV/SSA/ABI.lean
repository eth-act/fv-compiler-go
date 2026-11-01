import GoFV.SSA.Export

/-!
# ABI assignment queries

The parts of `cmd/compile/internal/abi` (`abiutils.go`) and of the `*AuxCall` accessors
(`ssa/op.go:121-297`) that passes read, over the exported ABI analysis (`aux … call` with its
`abiparam` lines, `config abi0`/`abi1`; `docs/contracts/export.md`). The register assignment
itself (`ABIAnalyze*`) is not here: its result arrives precomputed in each `AuxCall`.

Also `types.(*Type).Registers` (`types/size.go`, the register counts `CalcSize` records) and
`ssa.CanSSA` (`value.go:620`), which the ABI queries and their users need.
-/

namespace GoFV.SSA

/-- `abi.ABIConfig`: register counts and `offsetForLocals` (`config abi<which>` is
`<intregs>:<floatregs>:<localsoffset>`). -/
structure ABIConfig where
  intRegs : Nat
  floatRegs : Nat
  localsOffset : Int
  deriving DecidableEq, Inhabited, Repr

namespace ABIConfig

/-- Decimal digits (non-empty), on characters. -/
def natOfChars? (ds : List Char) : Option Nat :=
  if ds.isEmpty then none
  else ds.foldl (fun acc c => acc.bind fun n =>
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- Parse a `config abi0`/`abi1` value. On characters: `String.splitOn`, `toNat?` and `toInt?`
are well-founded recursions the kernel does not reduce (`expandCalls_witness` evaluates the
pass with `decide +kernel`). -/
def parse? (s : String) : Option ABIConfig :=
  match s.toList.splitOn ':' with
  | [i, f, l] => do
    let off ← match l with
      | '-' :: ds => (natOfChars? ds).map fun n => -(n : Int)
      | ds => (natOfChars? ds).map Int.ofNat
    return ⟨← natOfChars? i, ← natOfChars? f, off⟩
  | _ => none

/-- `FloatIndexFor(r)`: negative for an integer register. -/
@[inline] def floatIndexFor (c : ABIConfig) (r : Nat) : Int := (r : Int) - c.intRegs

end ABIConfig

/-- `ssa.ArgOpAndRegisterFor(r, cfg)` (`expand_calls.go:883`): `ArgFloatReg` with the float
index, or `ArgIntReg` with `r`. -/
def argOpAndRegisterFor (c : ABIConfig) (r : Nat) : Op × Int64 :=
  let i := c.floatIndexFor r
  if i >= 0 then (.ArgFloatReg, Int64.ofInt i) else (.ArgIntReg, Int64.ofNat r)

namespace ABIParam

/-- `a.Offset()`: the stack offset; Go `Fatalf`s for a register parameter. -/
def stackOffset (p : ABIParam) : Except String Int :=
  if p.regs.isEmpty then .ok p.offset
  else .error "register allocated parameters have no offset"

/-- `a.FrameOffset(info)` (`abiutils.go:249`). -/
def frameOffset (p : ABIParam) (info : CallABI) (c : ABIConfig) : Except String Int :=
  if p.offset == -1 then .error "function parameter has no ABI-defined frame-pointer offset"
  else if p.regs.isEmpty then .ok (p.offset - c.localsOffset)
  else .ok (p.offset + info.spillOff - c.localsOffset)

end ABIParam

namespace CallABI

/-- `InParams()`. -/
def inParams (a : CallABI) : Array ABIParam := a.params.extract 0 a.nin
/-- `OutParams()`. -/
def outParams (a : CallABI) : Array ABIParam := a.params.extract a.nin (a.nin + a.nout)

/-- `InParam(i)`. -/
def inParam (a : CallABI) (i : Nat) : Except String ABIParam :=
  if i < a.nin then match a.params[i]? with
    | some p => .ok p
    | none => .error s!"abi: no in param {i}"
  else .error s!"abi: in param {i} out of range ({a.nin})"

/-- `OutParam(i)`. -/
def outParam (a : CallABI) (i : Nat) : Except String ABIParam :=
  if i < a.nout then match a.params[a.nin + i]? with
    | some p => .ok p
    | none => .error s!"abi: no out param {i}"
  else .error s!"abi: out param {i} out of range ({a.nout})"

/-- `OffsetOfResult(i)`. -/
def offsetOfResult (a : CallABI) (i : Nat) : Except String Int := do (← a.outParam i).stackOffset
/-- `OffsetOfArg(i)`. -/
def offsetOfArg (a : CallABI) (i : Nat) : Except String Int := do (← a.inParam i).stackOffset

end CallABI

/-- `types.(*Type).Registers()`: the integer and float register counts `CalcSize` records
(`types/size.go`): scalars 1, complex 2 float, string/interface 2, slice 3, arrays of length 0/1
as their element (longer: 255/255), structs the field sums capped at 255/255. -/
def regCounts (tabs : Tables) : Nat → TypeRef → Except String (Nat × Nat)
  | 0, t => .error s!"Registers: type t{t} too deep"
  | fuel + 1, t => do
    let some d := tabs.type? t | throw s!"Registers: type t{t} not defined"
    match d.kind with
    | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT | .UINT
    | .UINTPTR | .BOOL | .PTR | .UNSAFEPTR | .CHAN | .MAP | .FUNC => return (1, 0)
    | .FLOAT32 | .FLOAT64 => return (0, 1)
    | .COMPLEX64 | .COMPLEX128 => return (0, 2)
    | .STRING | .INTER => return (2, 0)
    | .SLICE => return (3, 0)
    | .ARRAY =>
      match d.tail with
      | .array e n =>
        if n == 0 then return (0, 0)
        else if n == 1 then regCounts tabs fuel e
        else return (255, 255)
      | _ => throw s!"Registers: array t{t} without element"
    | .STRUCT =>
      match d.tail with
      | .struct fs => do
        let mut i := 0
        let mut f := 0
        for fld in fs do
          let (a, b) ← regCounts tabs fuel fld.type
          i := i + a
          f := f + b
        return if i > 255 || f > 255 then (255, 255) else (i, f)
      | _ => throw s!"Registers: struct t{t} without fields"
    | k => throw s!"Registers: type t{t} of kind {k.name}"

/-- Recursion bound for type walks (types nest far less deeply on the corpus). -/
def typeFuel : Nat := 1000

/-- `config.NumParamRegs(t)`; Go `Fatalf`s for types that cannot go in registers. -/
def numParamRegs (tabs : Tables) (t : TypeRef) : Except String Nat := do
  let (i, f) ← regCounts tabs typeFuel t
  if i == 255 && f == 255 then throw s!"cannot represent parameters of type t{t} in registers"
  return i + f

/-- The `Config.Types` entries `appendParamTypes` reaches through the synthesized slice, string
and interface structs and `FloatForComplex`. -/
structure RegTypes where
  bytePtr : TypeRef
  int : TypeRef
  unsafePtr : TypeRef
  float32 : TypeRef
  float64 : TypeRef

/-- `appendParamTypes(rts, t)` (`abiutils.go:145`) for 64-bit registers. -/
def appendParamTypes (tabs : Tables) (rt : RegTypes) :
    Nat → Array TypeRef → TypeRef → Except String (Array TypeRef)
  | 0, _, t => .error s!"appendParamTypes: type t{t} too deep"
  | fuel + 1, rts, t => do
    let some d := tabs.type? t | throw s!"appendParamTypes: type t{t} not defined"
    let some w := d.size | throw s!"appendParamTypes: type t{t}: size not calculated"
    if w == 0 then return rts
    match d.kind with
    | .COMPLEX64 => return rts.push rt.float32 |>.push rt.float32
    | .COMPLEX128 => return rts.push rt.float64 |>.push rt.float64
    | .BOOL | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT
    | .UINT | .UINTPTR | .FLOAT32 | .FLOAT64 | .PTR | .UNSAFEPTR | .MAP | .CHAN | .FUNC =>
      if w <= 8 then return rts.push t
      else throw s!"appendParamTypes: type t{t} wider than a register"
    | .ARRAY =>
      match d.tail with
      | .array e n => do
        let mut rts := rts
        for _ in [0:n.toNat] do rts ← appendParamTypes tabs rt fuel rts e
        return rts
      | _ => throw s!"appendParamTypes: array t{t} without element"
    | .STRUCT =>
      match d.tail with
      | .struct fs => do
        let mut rts := rts
        for fld in fs do
          let some fd := tabs.type? fld.type | throw s!"appendParamTypes: t{fld.type} not defined"
          if fd.size.getD 0 > 0 then rts ← appendParamTypes tabs rt fuel rts fld.type
        return rts
      | _ => throw s!"appendParamTypes: struct t{t} without fields"
    | .SLICE => return rts.push rt.bytePtr |>.push rt.int |>.push rt.int
    | .STRING => return rts.push rt.bytePtr |>.push rt.int
    | .INTER => return rts.push rt.unsafePtr |>.push rt.unsafePtr
    | _ => return rts

/-- `abi.RegisterTypes(params)` (`abiutils.go:118`): the register types of the
register-assigned parameters, in order. -/
def registerTypes (tabs : Tables) (rt : RegTypes) (ps : Array ABIParam) :
    Except String (Array TypeRef) :=
  ps.foldlM (init := #[]) fun rts p =>
    if p.regs.isEmpty then pure rts else appendParamTypes tabs rt typeFuel rts p.type

/-- `MaxStruct` (`decompose.go:412`). -/
def maxStruct : Nat := 4

/-- `ssa.CanSSA(t)` (`value.go:620`) with the SIMD experiment off. -/
def canSSA (tabs : Tables) (ptrSize : Int) : Nat → TypeRef → Except String Bool
  | 0, t => .error s!"CanSSA: type t{t} too deep"
  | fuel + 1, t => do
    let some d := tabs.type? t | throw s!"CanSSA: type t{t} not defined"
    let some w := d.size | throw s!"CanSSA: type t{t}: size not calculated"
    if w == 0 then return true
    if w > maxStruct * ptrSize then return false
    match d.kind, d.tail with
    | .ARRAY, .array e n => if n <= 1 then canSSA tabs ptrSize fuel e else return false
    | .STRUCT, .struct fs =>
      if d.flags.direct then return true
      if fs.size > maxStruct then return false
      fs.allM fun fld => canSSA tabs ptrSize fuel fld.type
    | _, _ => return true

end GoFV.SSA
