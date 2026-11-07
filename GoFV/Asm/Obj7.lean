import GoFV.Asm.Link
import GoFV.SSA.Sem.Float.Convert

/-!
# `linkpatch`, `progedit` and `preprocess` (D1, D2)

Literal ports of the first steps of `obj.Flushplist` for one arm64 text symbol
(`docs/PASSES3.md` §D1–D2):

* `cmd/internal/obj/pass.go:37-181`: `brloop`, `checkaddr`, `linkpatch` (which calls
  `progedit` on every Prog and resolves branch targets);
* `cmd/internal/obj/arm64/obj7.go:44-65` (`zrReplace`), `:306-473` (`progedit`,
  `rewriteToUseGot`), `:67-304` (`stacksplit`), `:475-916` (`preprocess`, `nocache`);
* `cmd/internal/obj/sym.go:159-239`: the constant symbols `Float32Sym`, `Float64Sym`,
  `Int32Sym`, `Int64Sym`, `Int128Sym`;
* `cmd/internal/obj/link.go:1251-1287`: `SpillRegisterArgs`, `UnspillRegisterArgs`.

Go's `for p := Text; p != nil; p = p.Link` loops whose body may reassign `p` are `walk`, whose
body returns the Prog `p` holds at the end of the iteration. `ctxt.Diag` is `throw` (no corpus
function has assembler diagnostics).
-/

namespace GoFV.Asm

open GoFV.SSA (GoStr Pos)
open AsmM
open ARM64

/-! ## Helpers -/

/-- `int32(x)`: two's-complement wrap to 32 bits. -/
private def wrap32 (x : Int) : Int := (x + 2 ^ 31) % 2 ^ 32 - 2 ^ 31

/-- `int16(x)`. -/
private def wrap16 (x : Int) : Int := (x + 2 ^ 15) % 2 ^ 16 - 2 ^ 15

/-- `uint64(x)` as a natural number. -/
private def toU64 (x : Int) : Nat := (x % 2 ^ 64).toNat

/-- `fmt.Sprintf("%0<w>x", v)`: lower-case hex, zero-padded to at least `w` digits. -/
private def hexPad (v : Nat) (w : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 v)
  "".pushn '0' (w - s.length) ++ s

/-- `n` little-endian bytes of `v` (`binary.LittleEndian.PutUint<8n>`). -/
private def leBytes (v : Nat) (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [0:n] do
    b := b.push (UInt8.ofNat (v >>> (8 * i) % 256))
  return b

/-- `Addr.Target()` (`link.go:254-259`): the branch target of a `TYPE_BRANCH` operand; the
typed-nil `*Prog` (`AddrVal.nilTarget`) is `nil`. -/
def Addr.target? (a : Addr) : Option Nat :=
  if a.type = .BRANCH then
    match a.val with
    | .target id => some id
    | _ => none
  else none

/-- `Addr.SetTarget(t)` (`link.go:260-265`); `none` stores the typed-nil `*Prog`. -/
def Addr.setTarget (a : Addr) (t : Option Nat) : Except String Addr :=
  if a.type != .BRANCH then
    throw "SetTarget: setting branch target when type is not TYPE_BRANCH"
  else
    match t with
    | some id => pure { a with val := .target id }
    | none => pure { a with val := .nilTarget }

/-- Sets `p.To`'s branch target (`p.To.SetTarget(t)`). -/
private def setToTarget (p : Nat) (t : Option Nat) : AsmM Unit := do
  let pp ← getP p
  match pp.to.setTarget t with
  | .ok a => setP p { pp with to := a }
  | .error e => throw e

/-- `lico.withXlogue` / `XPos.WithXlogue` (`cmd/internal/src/pos.go:441-450`,
`xpos.go:85-88`): a zero `lico` becomes "not a statement" first unless `x` is 0. -/
def posWithXlogue (p : Pos) (x : Nat) : Pos :=
  if p.licoZero then
    if x == 0 then p else { p with stmt := Pos.notStmt, xlogue := x }
  else { p with xlogue := x }

/-- `for p := start; p != nil; p = p.Link { p = body(p) }`. -/
partial def walk (start : Option Nat) (body : Nat → AsmM Nat) : AsmM Unit := do
  match start with
  | none => pure ()
  | some p =>
    let p ← body p
    walk (← linkOf p) body

/-- The text symbol's ABI (`LSym.ABI()`, `link.go:1031`: `Attribute / attrABIBase`). -/
private def textABI : AsmM Nat := return (← get).fn.attr / Obj.attrABIBase.toNat

/-! ## `pass.go` -/

/-- `brloop` (`pass.go:37-50`): the ultimate destination of the series of unconditional jumps
beginning at `p`; `none` for an infinite loop. -/
def brloop (p : Nat) : AsmM (Option Nat) := do
  let mut q := p
  let mut c : Nat := 0
  for _ in [0:5000] do
    let qp ← getP q
    match qp.to.target? with
    | none => return some q
    | some t =>
      if qp.as != .JMP then return some q
      c := c + 1
      if c >= 5000 then return none
      q := t
  throw "brloop: unreachable"

/-- `checkaddr` (`pass.go:53-123`): checks that `a` has an expected encoding. -/
def checkaddr (p : Prog) (a : Addr) : AsmM Unit := do
  let valNil := a.val == .none
  let bad : AsmM Unit := throw s!"checkaddr: invalid encoding for argument (Prog {p.id})"
  match a.type with
  | .NONE | .REGREG2 | .REGLIST => pure ()
  | .BRANCH | .TEXTSIZE =>
    if a.reg != 0 || a.index != 0 || a.scale != 0 || a.name != .NONE then bad
  | .MEM => pure ()
  | .CONST =>
    if a.name != .NONE || a.sym.isSome || a.reg != 0 then
      throw s!"checkaddr: argument is TYPE_CONST, should be TYPE_ADDR, in Prog {p.id}"
    if a.reg != 0 || a.scale != 0 || a.name != .NONE || a.sym.isSome || !valNil then bad
  | .FCONST | .SCONST =>
    if a.reg != 0 || a.index != 0 || a.scale != 0 || a.name != .NONE || a.offset != 0 ||
        a.sym.isSome then bad
  | .REG =>
    if a.scale != 0 || a.name != .NONE || a.sym.isSome then bad
  | .ADDR =>
    if !valNil then bad
    else if a.reg == 0 && a.index == 0 && a.scale == 0 && a.name == .NONE && a.sym.isNone then
      throw s!"checkaddr: argument is TYPE_ADDR, should be TYPE_CONST, in Prog {p.id}"
  | .SHIFT | .REGREG =>
    if a.index != 0 || a.scale != 0 || a.name != .NONE || a.sym.isSome || !valNil then bad
  | .INDIR =>
    if a.reg != 0 || a.index != 0 || a.scale != 0 || a.name == .NONE || a.offset != 0 ||
        a.sym.isNone || !valNil then bad
  | .SPECIAL =>
    if a.reg != 0 || a.index != 0 || a.scale != 0 || a.name != .NONE || a.cls != 0 ||
        a.sym.isSome then bad

/-! ## Constant symbols (`sym.go:159-239`) -/

/-- The `LookupInit` body shared by the constant symbols: `Size`, `Align`, `P`,
`Type = SRODATA` (`rodataKind`), `AttrLocal`, `AttrContentAddressable`; run once per symbol. -/
private def constSym (name : String) (size align : Int) (p : ByteArray) : AsmM Nat := do
  let k ← lookup (GoStr.ofString name) Obj.ABI0.toNat
  if !(← get).symData.contains k then
    setSymData k { sym := k, kind := "SRODATA", size, align,
                   attr := Obj.AttrLocal.toNat ||| Obj.AttrContentAddressable.toNat, data := p,
                   relocs := #[] }
    modify fun s => { s with symAlign := s.symAlign.insert k align }
  return k

/-- `ctxt.Float32Sym(f)` (`sym.go:163-176`), `f` given by its `math.Float32bits`. -/
def float32Sym (bits : Nat) : AsmM Nat :=
  constSym s!"$f32.{hexPad bits 8}" 4 4 (leBytes bits 4)

/-- `ctxt.Float64Sym(f)` (`sym.go:178-191`), `f` given by its `math.Float64bits`. -/
def float64Sym (bits : Nat) : AsmM Nat :=
  constSym s!"$f64.{hexPad bits 16}" 8 8 (leBytes bits 8)

/-- `ctxt.Int32Sym(i)` (`sym.go:193-205`): the name formats `uint64(i)`. -/
def int32Sym (i : Int) : AsmM Nat :=
  constSym s!"$i32.{hexPad (toU64 i) 8}" 4 4 (leBytes (toU64 i) 4)

/-- `ctxt.Int64Sym(i)` (`sym.go:207-219`). -/
def int64Sym (i : Int) : AsmM Nat :=
  constSym s!"$i64.{hexPad (toU64 i) 16}" 8 8 (leBytes (toU64 i) 8)

/-- `ctxt.Int128Sym(hi, lo)` (`sym.go:221-239`), little-endian: `lo` then `hi`. -/
def int128Sym (hi lo : Int) : AsmM Nat :=
  constSym s!"$i128.{hexPad (toU64 hi) 16}{hexPad (toU64 lo) 16}" 16 8
    (leBytes (toU64 lo) 8 ++ leBytes (toU64 hi) 8)

/-! ## `progedit` (`obj7.go:44-65`, `:306-473`) -/

/-- `zrReplace` (`obj7.go:46-65`): instructions whose `$0` From operand becomes `REGZERO`. -/
def zrReplace : As → Bool
  | .MOVD | .MOVW | .MOVWU | .MOVH | .MOVHU | .MOVB | .MOVBU | .SBC | .SBCW | .SBCS | .SBCSW
  | .ADC | .ADCW | .ADCS | .ADCSW | .FMOVD | .FMOVS | .MSR => true
  | _ => false

/-- `float32(f64)` as `math.Float32bits`: IEEE round-to-nearest-even narrowing (NaNs keep the
top payload bits and are quieted, as the hardware conversion does). -/
private def f64to32bits (bits : UInt64) : Nat :=
  (IEEE.convert .b64 .b32 .rne (BitVec.ofNat 64 bits.toNat)).toNat

/-- `rewriteToUseGot` (`obj7.go:398-473`). It reads `Sym.Local()` and `Sym.Type` of arbitrary
data symbols, which the export does not carry; the corpus is built without `-dynlink`. -/
def rewriteToUseGot (_p : Nat) : AsmM Unit :=
  throw "rewriteToUseGot: -dynlink not supported"

/-- `progedit` (`obj7.go:306-395`). -/
def progedit (pid : Nat) : AsmM Unit := do
  let mut p ← getP pid
  p := { p with from_ := { p.from_ with cls := 0 }, to := { p.to with cls := 0 } }
  -- Previously we rewrote $0 to ZR, but we have now removed this change.
  if p.from_.type == .CONST && p.from_.offset == 0 && zrReplace p.as then
    p := { p with from_ := { p.from_ with type := .REG, reg := REGZERO } }
  -- Rewrite BR/BL to symbol as TYPE_BRANCH.
  match p.as with
  | .JMP | .CALL | .RET =>
    if p.to.sym.isSome then
      p := { p with to := { p.to with type := .BRANCH } }
  | _ => pure ()
  -- Rewrite float and vector constants to values stored in memory.
  match p.as with
  | .VMOVS =>
    if p.from_.type == .CONST then
      let s ← int32Sym p.from_.offset
      p := { p with from_ := { p.from_ with type := .MEM, sym := some s, name := .EXTERN,
                                            offset := 0 } }
  | .VMOVD =>
    if p.from_.type == .CONST then
      let s ← int64Sym p.from_.offset
      p := { p with from_ := { p.from_ with type := .MEM, sym := some s, name := .EXTERN,
                                            offset := 0 } }
  | .VMOVQ =>
    if p.from_.type == .CONST then
      -- p.GetFrom3() (link.go:356-363)
      let some (_, f3) := p.rest.find? (·.1 == Obj.Source.toNat)
        | throw "progedit: VMOVQ without a Source RestArgs operand"
      let s ← int128Sym f3.offset p.from_.offset
      p := { p with from_ := { p.from_ with type := .MEM, sym := some s, name := .EXTERN,
                                            offset := 0 },
                    rest := #[] }
  | .FMOVS =>
    if p.from_.type == .FCONST then
      let .float f64 := p.from_.val | throw "progedit: FMOVS FCONST without a float64"
      let f32 := f64to32bits f64
      if chipfloat7 f64 > 0 then pure ()
      else if f32 == 0 then
        p := { p with from_ := { p.from_ with type := .REG, reg := REGZERO } }
      else
        let s ← float32Sym f32
        p := { p with from_ := { p.from_ with type := .MEM, sym := some s, name := .EXTERN,
                                              offset := 0 } }
  | .FMOVD =>
    if p.from_.type == .FCONST then
      let .float f64 := p.from_.val | throw "progedit: FMOVD FCONST without a float64"
      if chipfloat7 f64 > 0 then pure ()
      else if f64 == 0 then
        p := { p with from_ := { p.from_ with type := .REG, reg := REGZERO } }
      else
        let s ← float64Sym f64.toNat
        p := { p with from_ := { p.from_ with type := .MEM, sym := some s, name := .EXTERN,
                                              offset := 0 } }
  | _ => pure ()
  setP pid p
  if (← read).flagDynlink then
    rewriteToUseGot pid

/-! ## `linkpatch` (`pass.go:125-181`) -/

/-- The first Prog from `q` along `Link` whose `Pc` is `off` (`pass.go:147-153`; `Forwd` is
always nil on arm64). -/
private partial def findPc (off : Int) : Option Nat → AsmM (Option Nat)
  | none => pure none
  | some q => do
    if (← getP q).pc == off then pure (some q) else findPc off (← linkOf q)

/-- `linkpatch` (`pass.go:125-181`): `checkaddr` and `progedit` on every Prog, branch targets
by `To.Offset` (the target's `Pc`, still the allocation number), then, with `Flag_optimize`,
jump chains collapsed with `brloop`. -/
def linkpatch : AsmM Unit := do
  let text := (← get).text
  walk (some text) fun pid => do
    let p ← getP pid
    checkaddr p p.from_
    for (_, v) in p.rest do
      checkaddr p v
    checkaddr p p.to
    progedit pid
    let p ← getP pid
    if p.to.type != .BRANCH then return pid
    if p.to.val != .none then return pid
    if p.to.sym.isSome then return pid
    let q ← findPc p.to.offset (some text)
    match q with
    | none =>
      throw s!"linkpatch: branch out of range ({toU64 p.to.offset % 2 ^ 32}) in Prog {pid}"
    | some _ => setToTarget pid q
    return pid
  if !(← read).flagOptimize then return
  -- Collapse series of jumps to jumps.
  walk (some text) fun pid => do
    let p ← getP pid
    let some t := p.to.target? | return pid
    setToTarget pid (← brloop t)
    let p ← getP pid
    if let some t := p.to.target? then
      if p.to.type == .BRANCH then
        let tp ← getP t
        setP pid { p with to := { p.to with offset := tp.pc } }
    return pid

/-! ## Register argument spills (`link.go:1251-1287`) -/

/-- `FuncInfo.SpillRegisterArgs(last, pa)` (`link.go:1253-1268`). -/
def spillRegisterArgs (last : Nat) : AsmM Nat := do
  let mut last := last
  for ra in (← get).fn.spills do
    let spill ← appendp last
    let fr : Addr :=
      if ra.reg2 != 0 then { type := .REGREG, reg := ra.reg, offset := ra.reg2 }
      else { type := .REG, reg := ra.reg }
    modP spill fun x => { x with as := ra.spill, from_ := fr, to := ra.addr }
    last := spill
  return last

/-- `FuncInfo.UnspillRegisterArgs(last, pa)` (`link.go:1272-1287`). -/
def unspillRegisterArgs (last : Nat) : AsmM Nat := do
  let mut last := last
  for ra in (← get).fn.spills do
    let unspill ← appendp last
    let to : Addr :=
      if ra.reg2 != 0 then { type := .REGREG, reg := ra.reg, offset := ra.reg2 }
      else { type := .REG, reg := ra.reg }
    modP unspill fun x => { x with as := ra.unspill, from_ := ra.addr, to := to }
    last := unspill
  return last

/-! ## `stacksplit` (`obj7.go:67-304`) -/

/-- Appends a Prog after `p` (`obj.Appendp`) and sets it with `f`. -/
private def appendSet (p : Nat) (f : Prog → Prog) : AsmM Nat := do
  let q ← appendp p
  modP q f
  return q

/-- `c.stacksplit(p, framesize)` (`obj7.go:67-304`): the stack-bound check after `p` and the
`morestack` call at the end of the function; returns the last Prog of the check. -/
def stacksplit (p0 : Nat) (framesize : Int) : AsmM Nat := do
  let mut p := p0
  let ctx ← read
  if ctx.maymorestack != "" then
    p ← spillRegisterArgs p
    -- Save LR and make room for FP, REGCTXT. Leave room for caller's saved FP.
    let frameSize : Int := 32
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .REG, reg := REGLINK },
               to := { type := .MEM, offset := -frameSize, reg := REGSP },
               scond := C_XPRE.toNat, spadj := frameSize }
    -- Save FP.
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .REG, reg := REGFP },
               to := { type := .MEM, reg := REGSP, offset := -8 } }
    p ← appendSet p fun x =>
      { x with as := .SUB, from_ := { type := .CONST, offset := 8 }, reg := REGSP,
               to := { type := .REG, reg := REGFP } }
    -- Save REGCTXT (for simplicity we do this whether or not we need it.)
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .REG, reg := REGCTXT },
               to := { type := .MEM, reg := REGSP, offset := 8 } }
    -- BL maymorestack
    let mms ← lookup (GoStr.ofString ctx.maymorestack) (← textABI)
    p ← appendSet p fun x =>
      { x with as := .CALL, to := { type := .BRANCH, sym := some mms } }
    -- Restore REGCTXT.
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .MEM, reg := REGSP, offset := 8 },
               to := { type := .REG, reg := REGCTXT } }
    -- Restore FP.
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .MEM, reg := REGSP, offset := -8 },
               to := { type := .REG, reg := REGFP } }
    -- Restore LR and SP.
    p ← appendSet p fun x =>
      { x with as := .MOVD, from_ := { type := .MEM, offset := frameSize, reg := REGSP },
               scond := C_XPOST.toNat, to := { type := .REG, reg := REGLINK },
               spadj := -frameSize }
    p ← unspillRegisterArgs p
  -- Jump back to here after morestack returns.
  let startPred := p
  -- MOV g_stackguard(g), RT1
  let cfunc ← textAttr Obj.AttrCFunc
  p ← appendSet p fun x =>
    { x with as := .MOVD,
             from_ := { type := .MEM, reg := REGG, offset := if cfunc then 3 * 8 else 2 * 8 },
             to := { type := .REG, reg := REGRT1 } }
  -- Mark the stack bound check and morestack call async nonpreemptible.
  p ← startUnsafePoint p
  let mut q : Option Nat := none
  if framesize <= Abi.StackSmall then
    -- small stack: SP < stackguard
    p ← appendSet p fun x =>
      { x with as := .CMP, from_ := { type := .REG, reg := REGRT1 }, reg := REGSP }
  else if framesize <= Abi.StackBig then
    -- large stack: SP-framesize < stackguard-StackSmall
    p ← appendSet p fun x =>
      { x with as := .SUB, from_ := { type := .CONST, offset := framesize - Abi.StackSmall },
               reg := REGSP, to := { type := .REG, reg := REGRT2 } }
    p ← appendSet p fun x =>
      { x with as := .CMP, from_ := { type := .REG, reg := REGRT1 }, reg := REGRT2 }
  else
    -- Such a large stack we need to protect against underflow.
    p ← appendSet p fun x =>
      { x with as := .SUBS, from_ := { type := .CONST, offset := framesize - Abi.StackSmall },
               reg := REGSP, to := { type := .REG, reg := REGRT2 } }
    p ← appendSet p fun x => { x with as := .BLO, to := { type := .BRANCH } }
    q := some p
    p ← appendSet p fun x =>
      { x with as := .CMP, from_ := { type := .REG, reg := REGRT1 }, reg := REGRT2 }
  -- BLS do-morestack
  let bls ← appendSet p fun x => { x with as := .BLS, to := { type := .BRANCH } }
  let end_ ← endUnsafePoint bls (-1)
  let last ← lastProg
  -- Now we are at the end of the function, but logically we are still in function prologue.
  let spfix ← appendSet last fun x => { x with as := .NOP, spadj := -framesize }
  let mut pcdata ← emitEntryStackMap spfix
  pcdata ← startUnsafePoint pcdata
  if let some blo := q then
    setToTarget blo (some pcdata)
  setToTarget bls (some pcdata)
  let spill ← spillRegisterArgs pcdata
  -- MOV LR, R3
  let movlr ← appendSet spill fun x =>
    { x with as := .MOVD, from_ := { type := .REG, reg := REGLINK },
             to := { type := .REG, reg := REG_R3 } }
  let debug := movlr
  -- BL runtime.morestack(SB)
  let needCtxt ← textAttr Obj.AttrNeedCtxt
  let morestack : String :=
    if cfunc then "runtime.morestackc"
    else if !needCtxt then "runtime.morestack_noctxt"
    else "runtime.morestack"
  let ms ← lookup (GoStr.ofString morestack) Obj.ABI0.toNat
  let call ← appendSet debug fun x =>
    { x with as := .CALL, to := { type := .BRANCH, sym := some ms } }
  -- The instructions which unspill regs should be preemptible.
  pcdata ← endUnsafePoint call (-1)
  let unspill ← unspillRegisterArgs pcdata
  -- B start
  let jmp ← appendSet unspill fun x =>
    { x with as := .JMP, to := { type := .BRANCH }, spadj := framesize }
  setToTarget jmp (← linkOf startPred)
  return end_

/-! ## `preprocess` (`obj7.go:475-916`) -/

/-- `nocache(p)` (`obj7.go:912-916`). -/
def nocache (p : Prog) : Prog :=
  { p with optab := 0, from_ := { p.from_ with cls := 0 }, to := { p.to with cls := 0 } }

/-- `newprog()` spliced after `p` without `Appendp` (`obj7.go:768-778`): `q.Pos = p.Pos`,
`q.Link = p.Link`, `p.Link = q`; `f` sets the other fields. -/
private def spliceAfter (p : Nat) (f : Prog → Prog) : AsmM Nat := do
  let q ← newProg
  let pp ← getP p
  modP q fun x => { f x with pos := pp.pos }
  setLink q (← linkOf p)
  setLink p (some q)
  return q

/-- The `ATEXT` case of `preprocess` (`obj7.go:519-695`); returns the loop's `p`. -/
private def preprocessText (p0 : Nat) (textstksiz : Int) : AsmM Nat := do
  let mut p := p0
  modify fun s => { s with text := p }
  modify fun s => { s with autosize := wrap32 textstksiz }
  if (← getP p).mark &&& LEAF.toNat != 0 && (← get).autosize == 0 then
    -- A leaf function with no locals has no frame.
    setTextAttr Obj.AttrNoFrame true
  if !(← textAttr Obj.AttrNoFrame) then
    -- If there is a stack frame at all, it includes space to save the LR.
    modify fun s => { s with autosize := wrap32 (s.autosize + 8) }
  let autosize := (← get).autosize
  if autosize != 0 then
    let extrasize : Int ←
      if autosize.tmod 16 == 8 then pure 8
      else if autosize % 16 == 0 then pure 16
      else throw s!"preprocess: unaligned frame size {autosize - 8} - must be 16 aligned"
    modify fun s => { s with autosize := wrap32 (s.autosize + extrasize),
                             fn := { s.fn with locals := wrap32 (s.fn.locals + extrasize) } }
    let autosize := (← get).autosize
    -- low 32 bits for autosize, high 32 bits for extrasize
    -- (`int64(autosize) | int64(extrasize)<<32`; a negative autosize already sets them)
    let off := if autosize < 0 then autosize else autosize + extrasize * 2 ^ 32
    modP p fun x => { x with to := { x.to with offset := off } }
  else
    -- NOFRAME
    modP p fun x => { x with to := { x.to with offset := 0 } }
  let text := (← get).text
  if (← get).autosize == 0 && (← getP text).mark &&& LEAF.toNat == 0 then
    modP text fun x => { x with mark := x.mark ||| LEAF.toNat }
  if (← getP text).mark &&& LEAF.toNat != 0 then
    setTextAttr Obj.AttrLeaf true
    if ← textAttr Obj.AttrNoFrame then
      return p
  if (← getP p).mark &&& LEAF.toNat != 0 && (← get).autosize < Abi.StackSmall then
    -- A leaf function with a small stack can be marked NOSPLIT, avoiding a stack check.
    setTextAttr Obj.AttrNoSplit true
  if !(← textAttr Obj.AttrNoSplit) then
    p ← stacksplit p (← get).autosize -- emit split check
  let autosize := (← get).autosize
  let ppos := (← getP p).pos
  let aoffset := if autosize > 0xf0 then 0xf0 else autosize
  -- Frame is non-empty. Make sure to save link register, even if it is a leaf function.
  let q := p
  let mut q1 := q
  let mut prologueEnd := q
  if autosize > aoffset then
    -- SUB $autosize, RSP, R20
    q1 ← appendSet q fun x =>
      { x with pos := ppos, as := .SUB, from_ := { type := .CONST, offset := autosize },
               reg := REGSP, to := { type := .REG, reg := REG_R20 } }
    prologueEnd := q1
    -- STP (R29, R30), -8(R20)
    q1 ← appendSet q1 fun x =>
      { x with pos := ppos, as := .STP, from_ := { type := .REGREG, reg := REGFP,
                                                   offset := REGLINK },
               to := { type := .MEM, reg := REG_R20, offset := -8 } }
    -- This is not async preemptible, as if we open a frame at the current SP, it will
    -- clobber the saved LR.
    q1 ← startUnsafePoint q1
    -- MOVD R20, RSP
    q1 ← appendSet q1 fun x =>
      { x with pos := ppos, as := .MOVD, from_ := { type := .REG, reg := REG_R20 },
               to := { type := .REG, reg := REGSP }, spadj := autosize }
    q1 ← endUnsafePoint q1 (-1)
    -- buildcfg.GOOS == "ios" branch: the corpus is linux/arm64.
  else
    -- small frame, update SP and save LR in a single MOVD.W instruction.
    q1 ← appendSet q fun x =>
      { x with as := .MOVD, pos := ppos, from_ := { type := .REG, reg := REGLINK },
               to := { type := .MEM, offset := -aoffset, reg := REGSP },
               scond := C_XPRE.toNat, spadj := aoffset }
    prologueEnd := q1
    -- Frame pointer.
    q1 ← appendSet q1 fun x =>
      { x with pos := ppos, as := .MOVD, from_ := { type := .REG, reg := REGFP },
               to := { type := .MEM, reg := REGSP, offset := -8 } }
  modP prologueEnd fun x => { x with pos := posWithXlogue x.pos 1 }
  let _ ← appendSet q1 fun x =>
    { x with pos := ppos, as := .SUB, from_ := { type := .CONST, offset := 8 }, reg := REGSP,
             to := { type := .REG, reg := REGFP } }
  return p

/-- The `ARET` case of `preprocess` (`obj7.go:697-853`); returns the loop's `p`. -/
private def preprocessRet (p0 : Nat) : AsmM Nat := do
  let mut p := p0
  modP p nocache
  let pp ← getP p
  if pp.from_.type == .CONST then
    throw s!"preprocess: using BECOME (Prog {p}) is not supported!"
  let retJMP := pp.to.sym
  let retReg := if pp.to.reg == 0 then REGLINK else pp.to.reg
  modP p fun x => { x with to := {} }
  let autosize := (← get).autosize
  let aoffset := autosize
  if (← getP (← get).text).mark &&& LEAF.toNat != 0 then
    if aoffset != 0 then
      -- Restore frame pointer: ADD $framesize-8, RSP, R29
      modP p fun x =>
        { x with as := .ADD, from_ := { x.from_ with type := .CONST, offset := autosize - 8 },
                 reg := REGSP, to := { x.to with type := .REG, reg := REGFP } }
      -- Pop stack frame: ADD $framesize, RSP, RSP
      p ← appendSet p fun x =>
        { x with as := .ADD, from_ := { type := .CONST, offset := autosize },
                 to := { type := .REG, reg := REGSP }, spadj := -autosize }
  else if aoffset <= 0xF0 then
    -- MOVD -8(RSP), R29
    modP p fun x =>
      { x with as := .MOVD,
               from_ := { x.from_ with type := .MEM, reg := REGSP, offset := -8 },
               to := { x.to with type := .REG, reg := REGFP } }
    p ← appendp p
    -- MOVD.P offset(RSP), R30
    modP p fun x =>
      { x with as := .MOVD, from_ := { type := .MEM, offset := aoffset, reg := REGSP },
               scond := C_XPOST.toNat, to := { type := .REG, reg := REGLINK },
               spadj := -aoffset }
  else
    -- LDP -8(RSP), (R29, R30)
    modP p fun x =>
      { x with as := .LDP,
               from_ := { x.from_ with type := .MEM, offset := -8, reg := REGSP },
               to := { x.to with type := .REGREG, reg := REGFP, offset := REGLINK } }
    if aoffset < 1 <<< 12 then
      -- ADD $aoffset, RSP, RSP
      p ← spliceAfter p fun x =>
        { x with as := .ADD, from_ := { type := .CONST, offset := aoffset },
                 to := { type := .REG, reg := REGSP }, spadj := -aoffset }
    else
      -- MOVD $aoffset, REGTMP
      p ← spliceAfter p fun x =>
        { x with as := .MOVD, from_ := { type := .CONST, offset := aoffset },
                 to := { type := .REG, reg := REGTMP } }
      -- ADD REGTMP, RSP, RSP
      p ← spliceAfter p fun x =>
        { x with as := .ADD, from_ := { type := .REG, reg := REGTMP },
                 to := { type := .REG, reg := REGSP }, spadj := -aoffset }
  -- debugRETZERO is false.
  if (← getP p).as != .RET then
    p ← spliceAfter p id
  if let some s := retJMP then
    modP p fun x =>
      { x with as := .JMP, to := { x.to with type := .BRANCH, sym := some s },
               spadj := autosize }
    return p
  modP p fun x =>
    { x with as := .RET, to := { x.to with type := .MEM, offset := 0, reg := retReg },
             spadj := autosize }
  return p

/-- `preprocess` (`obj7.go:475-910`): frame layout, prologue (with `stacksplit`), epilogues,
`Spadj`, `GETCALLERPC`, the SPWRITE check and the `TYPE_SHIFT` rewrite. -/
def preprocess : AsmM Unit := do
  let text := (← get).text
  if (← linkOf text).isNone then return
  let tp ← getP text
  let mut textstksiz := tp.to.offset
  if textstksiz == -8 then
    -- Historical way to mark NOFRAME.
    setTextAttr Obj.AttrNoFrame true
    textstksiz := 0
  if textstksiz < 0 then
    throw s!"preprocess: negative frame size {textstksiz} - did you mean NOFRAME?"
  if ← textAttr Obj.AttrNoFrame then
    if textstksiz != 0 then
      throw s!"preprocess: NOFRAME functions must have a frame size of 0, not {textstksiz}"
  let .textSize args := tp.to.val | throw "preprocess: TEXT To.Val is not an int32"
  modify fun s => { s with fn := { s.fn with args, locals := wrap32 textstksiz } }
  -- find leaf subroutines
  walk (some text) fun p => do
    match (← getP p).as with
    | .TEXT => modP p fun x => { x with mark := x.mark ||| LEAF.toNat }
    | .CALL =>
      let t := (← get).text
      modP t fun x => { x with mark := x.mark - (x.mark &&& LEAF.toNat) }
    | _ => pure ()
    return p
  walk (some text) fun p0 => do
    let mut p := p0
    match (← getP p).as with
    | .TEXT => p ← preprocessText p textstksiz
    | .RET => p ← preprocessRet p
    | .ADD | .SUB =>
      let pp ← getP p
      if pp.to.type == .REG && pp.to.reg == REGSP && pp.from_.type == .CONST then
        setP p { pp with spadj := wrap32 (if pp.as == .ADD then -pp.from_.offset
                                          else pp.from_.offset) }
    | .GETCALLERPC =>
      if ← textAttr Obj.AttrLeaf then
        -- MOVD LR, Rd
        modP p fun x => { x with as := .MOVD,
                                 from_ := { x.from_ with type := .REG, reg := REGLINK } }
      else
        -- MOVD (RSP), Rd
        modP p fun x => { x with as := .MOVD,
                                 from_ := { x.from_ with type := .MEM, reg := REGSP } }
    | _ => pure ()
    let pp ← getP p
    if pp.to.type == .REG && pp.to.reg == REGSP && pp.spadj == 0 then
      if (← get).fn.funcFlag &&& Abi.FuncFlagSPWrite.toNat == 0 then
        modify fun s => { s with fn := { s.fn with
          funcFlag := s.fn.funcFlag ||| Abi.FuncFlagSPWrite.toNat } }
        -- !ctxt.IsAsm: the compiler never writes SP outside Spadj.
        throw s!"preprocess: invalid auto-SPWRITE in non-assembly (Prog {p})"
    if pp.from_.type == .SHIFT && (pp.to.reg == REG_RSP || pp.reg == REG_RSP) then
      let offset := pp.from_.offset
      let o := toU64 offset
      let op := o &&& (3 <<< 22)
      if op != SHIFT_LL.toNat then
        throw s!"preprocess: illegal combination: Prog {p}"
      let r : Int := (o >>> 16 &&& 31 : Nat)
      let mut shift : Int := (o >>> 10 &&& 63 : Nat)
      if shift > 4 then
        -- asmout case 27 has the same check.
        shift := 7
      setP p { pp with from_ := { pp.from_ with type := .REG,
                                                reg := wrap16 (REG_LSL + r + (shift % 8) * 32),
                                                offset := 0 } }
    return p

end GoFV.Asm
