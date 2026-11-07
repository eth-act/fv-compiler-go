import GoFV.Gen.State
import GoFV.SSA.ABI
import GoFV.Asm.Abi

/-!
# Argument and wrapper metadata for traceback (B3)

Port of `emitArgInfo`, `EmitArgInfo` and `emitWrappedFuncInfo` (`ssagen/ssa.go:6835-6987`,
go1.27.3 pin 2aae1000ea1d; `docs/PASSES3.md` B3), with the `objw`/`obj` writers they use
(`objw.Uint8`, `objw.SymPtrOff`: `objw/objw.go:17-19,51-57,73-77`; `LSym.WriteInt`/`WriteOff`
and `prepwrite`: `cmd/internal/obj/data.go`), and the parts of `cmd/compile/internal/abi`
(`abiutils.go`) the argument metadata reads: `FrameOffset`, `RegisterTypesAndOffsets`'s
offsets (`appendParamOffsets`) and `align`.

- `<fn>.arginfo<abi>`: the `TraceArgs*` byte stream over `f.OwnAux.ABIInfo().InParams()` (the
  dictionary parameter of a shape instantiation, a name containing `[`, skipped), at most
  `TraceArgsLimit` components and `TraceArgsMaxDepth` nesting levels; `Align` 1,
  `ContentAddressable`, `FUNCDATA_ArgInfo`.
- `<wrapped>.wrapinfo`: an `R_ADDROFF` to the wrapped function's symbol (4 bytes, `Align` 4,
  `ContentAddressable`), `FUNCDATA_WrapInfo`; none with `Flag_linkshared`.

A symbol the port writes is recorded as `SymOut`: `prepwrite` turns the fresh (`Sxxx`) symbol
into `SDATA` and grows `Size` to the end of the last write; attributes are the raw
`obj.Attribute` bits (ABI0 symbols: no ABI bits).
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm

namespace ArgMeta

/-- `obj.AttrContentAddressable` (`cmd/internal/obj/link.go`: bit 15 of `Attribute`). -/
def attrContentAddressable : Nat := 1 <<< 15

/-- An `Int` `.ssa` `config` value. -/
def configInt (env : Env) (key : String) : Except String Int :=
  match env.config? key with
  | some #[.word w] =>
    match w.toInt? with
    | some n => pure n
    | none => throw s!"config {key}: not an integer"
  | _ => throw s!"config {key}: missing"

/-- `types.PtrSize`. -/
def ptrSize (env : Env) : Except String Int := configInt env "ptrsize"

/-- The `abi.ABIConfig` of `abiInfo.Config().Which()` (`config abi<which>`). -/
def abiConfig (env : Env) (which : Nat) : Except String ABIConfig :=
  match env.config? s!"abi{which}" with
  | some #[.word w] =>
    match ABIConfig.parse? w with
    | some c => pure c
    | none => throw s!"config abi{which}: not <int>:<float>:<offset>"
  | _ => throw s!"config abi{which}: missing"

/-- `f.OwnAux.ABIInfo()`. -/
def ownABI (env : Env) : Except String CallABI := do
  let some a := env.f.ownAux | throw "f.OwnAux is nil"
  match (← env.auxDef a).kind with
  | .call _ (some c) => pure c
  | .call _ none => throw "f.OwnAux has no ABI info"
  | _ => throw s!"f.OwnAux a{a} is not an AuxCall"

/-- `curfn.LSym`: name and ABI (`curfn.LSym.ABI()` is `curfn.ABI`: `InitLSym` sets
`LSym = Nname.LinksymABI(ABI)`). -/
def textSym (env : Env) : Except String (GoStr × Nat) :=
  match env.inSyms[env.genin.text.sym]? with
  | some s => pure s
  | none => throw s!"text symbol y{env.genin.text.sym} not defined"

/-- The `.ssa` definition of a type. -/
def tdef (tabs : Tables) (t : TypeRef) : Except String SSA.TypeDef :=
  match tabs.type? t with
  | some d => pure d
  | none => throw s!"type t{t} not defined"

/-- `t.Size()`. -/
def tsize (tabs : Tables) (t : TypeRef) : Except String Int := do
  match (← tdef tabs t).size with
  | some s => pure s
  | none => throw s!"type t{t}: size not calculated"

/-- `align(a, t)` (`abiutils.go:492`): `a` rounded up to `uint8(t.Alignment())` (unchanged for
0). -/
def alignFor (tabs : Tables) (a : Int) (t : TypeRef) : Except String Int := do
  let some al := (← tdef tabs t).align | throw s!"type t{t}: alignment not calculated"
  let al : Int := al % 256
  if al == 0 then return a
  return (a + al - 1) / al * al

/-- `appendParamOffsets(offsets, at, t)` (`abiutils.go:197`) for 64-bit registers, SIMD off:
the offsets of the register pieces of `t` placed at `at`, and the next unused offset. The
synthesized slice, string and interface structs have 8-byte fields at 0, 8 (, 16). -/
partial def appendParamOffsets (tabs : Tables) (offsets : Array Int) (at_ : Int) (t : TypeRef) :
    Except String (Array Int × Int) := do
  let d ← tdef tabs t
  let some w := d.size | throw s!"type t{t}: size not calculated"
  if w == 0 then return (offsets, at_)
  match d.kind with
  | .BOOL | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT
  | .UINT | .UINTPTR | .COMPLEX64 | .COMPLEX128 | .FLOAT32 | .FLOAT64
  | .PTR | .UNSAFEPTR | .MAP | .CHAN | .FUNC =>
    if d.kind == .COMPLEX64 || d.kind == .COMPLEX128 || w > 8 then
      let s := w / 2
      return (offsets.push at_ |>.push (at_ + s), at_ + w)
    else
      return (offsets.push at_, at_ + w)
  | .ARRAY =>
    let .array te n := d.tail | throw s!"array t{t} without element"
    let mut offsets := offsets
    let mut at_ := at_
    for _ in [0:n.toNat] do
      at_ ← alignFor tabs at_ te
      (offsets, at_) ← appendParamOffsets tabs offsets at_ te
    return (offsets, at_)
  | .STRUCT =>
    let .struct fs := d.tail | throw s!"struct t{t} without fields"
    let at0 := at_
    let mut offsets := offsets
    let mut at_ := at_
    for h : i in [0:fs.size] do
      let f := fs[i]
      let some fo := f.offset | throw s!"struct t{t}: field offset not calculated"
      at_ := at0 + fo
      (offsets, at_) ← appendParamOffsets tabs offsets at_ f.type
      if (← tsize tabs f.type) == 0 && i == fs.size - 1 then at_ := at_ + 1
    at_ ← alignFor tabs at_ t
    return (offsets, at_)
  | .SLICE => return (offsets.push at_ |>.push (at_ + 8) |>.push (at_ + 16), at_ + 24)
  | .STRING | .INTER => return (offsets.push at_ |>.push (at_ + 8), at_ + 16)
  | _ => return (offsets, at_)

/-- The offsets of `pa.RegisterTypesAndOffsets()` (`abiutils.go:137`). -/
def registerOffsets (tabs : Tables) (pa : ABIParam) : Except String (Array Int) := do
  if pa.regs.isEmpty then return #[]
  return (← appendParamOffsets tabs #[] 0 pa.type).1

/-- Records the contents of symbol `k`. -/
def writeSym (k : Nat) (o : SymOut) : GenM Unit :=
  modify fun s => { s with symData := s.symData.insert k o }

/-- `p := pp.Prog(obj.AFUNCDATA)` with `From` the constant `kind` and `To` the extern symbol
`sym`. -/
def funcdata (kind : Int) (sym : Nat) : GenM Unit := do
  let p ← GenM.prog .FUNCDATA
  GenM.modP p fun x => { x with from_ := GenM.constAddr kind,
                                to := { type := .MEM, name := .EXTERN, sym := some sym } }

/-! ## `EmitArgInfo` -/

/-- A type `visitType` visits: an exported type, or one of the scalars `EmitArgInfo`
synthesizes (`types.Types[TUINTPTR]`, `types.FloatForComplex(t)`), of which only the size is
read. -/
inductive ArgTy where
  | ref (t : TypeRef)
  | scalar (size : Int)

/-- The writer state: the bytes so far (`wOff` is their count) and the component count `n`. -/
structure ArgInfoSt where
  out : ByteArray := .empty
  n : Int := 0

abbrev ArgInfoM := StateT ArgInfoSt (Except String)

/-- `writebyte(uint8(o))`. -/
def writebyte (o : Int) : ArgInfoM Unit :=
  modify fun s => { s with out := s.out.push (UInt8.ofNat (o % 256).toNat) }

def incN : ArgInfoM Unit := modify fun s => { s with n := s.n + 1 }

/-- `write1(sz, offset)`: one non-aggregate argument, field or element. -/
def write1 (sz offset : Int) : ArgInfoM Unit := do
  if offset >= Abi.TraceArgsSpecial then
    writebyte Abi.TraceArgsOffsetTooLarge
  else
    writebyte offset
    writebyte sz
  incN

/-- `visitType(baseOffset, t, depth)`: writes `t` out recursively; `false` stops the walk. -/
partial def visitType (tabs : Tables) (ptrSize : Int) (baseOffset : Int) (t : ArgTy)
    (depth : Int) : ArgInfoM Bool := do
  if (← get).n >= Abi.TraceArgsLimit then
    writebyte Abi.TraceArgsDotdotdot
    return false
  if let .scalar sz := t then
    write1 sz baseOffset
    return true
  let .ref r := t | return true
  let d ← tdef tabs r
  let some size := d.size | throw s!"type t{r}: size not calculated"
  -- isAggregate (no SIMD types: GOEXPERIMENT simd is off)
  match d.kind with
  | .STRUCT | .ARRAY | .COMPLEX64 | .COMPLEX128 | .INTER | .STRING | .SLICE => pure ()
  | _ =>
    write1 size baseOffset
    return true
  writebyte Abi.TraceArgsStartAgg
  let depth := depth + 1
  if depth >= Abi.TraceArgsMaxDepth then
    writebyte Abi.TraceArgsDotdotdot
    writebyte Abi.TraceArgsEndAgg
    incN
    return true
  let visit (off : Int) (t : ArgTy) : ArgInfoM Bool := visitType tabs ptrSize off t depth
  match d.kind with
  | .INTER | .STRING =>
    if ← visit baseOffset (.scalar ptrSize) then
      discard <| visit (baseOffset + ptrSize) (.scalar ptrSize)
  | .SLICE =>
    if ← visit baseOffset (.scalar ptrSize) then
      if ← visit (baseOffset + ptrSize) (.scalar ptrSize) then
        discard <| visit (baseOffset + ptrSize * 2) (.scalar ptrSize)
  | .COMPLEX64 | .COMPLEX128 =>
    let half := size / 2
    if ← visit baseOffset (.scalar half) then
      discard <| visit (baseOffset + half) (.scalar half)
  | .ARRAY =>
    let .array te n := d.tail | throw s!"array t{r} without element"
    if n == 0 then
      incN
    else
      let es ← tsize tabs te
      let mut b := baseOffset
      for _ in [0:n.toNat] do
        if !(← visit b (.ref te)) then break
        b := b + es
  | _ =>
    let .struct fs := d.tail | throw s!"struct t{r} without fields"
    if fs.isEmpty then
      incN
    else
      for f in fs do
        let some fo := f.offset | throw s!"struct t{r}: field offset not calculated"
        if !(← visit (baseOffset + fo) (.ref f.type)) then break
  writebyte Abi.TraceArgsEndAgg
  return true

/-- `EmitArgInfo(f, abiInfo)`'s byte stream: `skipDict` is `strings.Contains(f.LSym.Name,
"[")`. -/
def argInfoBytes (env : Env) (abi : CallABI) (skipDict : Bool) : Except String ByteArray := do
  let tabs := env.tabs
  let ps ← ptrSize env
  let cfg ← abiConfig env abi.abi
  let ins := abi.inParams
  let start := if skipDict then 1 else 0
  if start > ins.size then throw s!"slice bounds out of range [{start}:{ins.size}]"
  let go : ArgInfoM Unit := do
    for a in ins.extract start ins.size do
      let off ← liftM (m := Except String) (a.frameOffset abi cfg)
      if !(← visitType tabs ps off (.ref a.type) 0) then break
    writebyte Abi.TraceArgsEndSeq
  let ((), st) ← go.run {}
  if (st.out.size : Int) > Abi.TraceArgsMaxLen then throw "ArgInfo too large"
  return st.out

end ArgMeta

open ArgMeta

/-- `emitArgInfo(e, f, pp)` (`ssagen/ssa.go:6836`): nothing for a function without receiver
and parameters; else `EmitArgInfo` into `<fn>.arginfo<abi>` (ABI0), `ContentAddressable`,
`FuncInfo.ArgInfo`, and the `FUNCDATA_ArgInfo` Prog. -/
def emitArgInfo : GenM Unit := do
  let env ← GenM.env
  let ft ← GenM.lift (tdef env.tabs env.f.type)
  let .func nrecv nparams _ _ := ft.tail | throw s!"f.Type t{env.f.type} is not a function type"
  if nrecv == 0 && nparams == 0 then return
  let abi ← GenM.lift (ownABI env)
  let (name, fabi) ← GenM.lift (textSym env)
  let x ← GenM.sym (name ++ GoStr.ofString s!".arginfo{fabi}") 0
  let data ← GenM.lift (argInfoBytes env abi (name.bytes.data.contains '['.toNat.toUInt8))
  writeSym x { kind := "SDATA", size := data.size, align := 1, attr := attrContentAddressable, data }
  modify fun s => { s with aux := { s.aux with argInfo := some x } }
  funcdata Abi.FUNCDATA_ArgInfo x

/-- `emitWrappedFuncInfo(e, pp)` (`ssagen/ssa.go:6961`): for a wrapper (`curfn.WrappedFunc`),
`<wrapped>.wrapinfo` (ABI0) holding `objw.SymPtrOff` to the wrapped function's symbol,
`ContentAddressable`, `Align` 4, `FuncInfo.WrapInfo`, and the `FUNCDATA_WrapInfo` Prog;
nothing with `Flag_linkshared`. -/
def emitWrappedFuncInfo : GenM Unit := do
  let env ← GenM.env
  if ← GenM.lift env.linkshared then return
  let some (wname, wabi) := env.genin.wrapped | return
  let w ← GenM.sym wname wabi
  let x ← GenM.sym (wname ++ GoStr.ofString ".wrapinfo") 0
  writeSym x { kind := "SDATA", size := 4, align := 4, attr := attrContentAddressable,
               data := ⟨#[0, 0, 0, 0]⟩,
               relocs := #[{ off := 0, siz := 4, type := "R_ADDROFF", add := 0, sym := some w }] }
  modify fun s => { s with aux := { s.aux with wrapInfo := some x } }
  funcdata Abi.FUNCDATA_WrapInfo x

end GoFV.Gen
