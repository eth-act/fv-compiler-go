import GoFV.Gen.State
import GoFV.Asm.Reg
import GoFV.Asm.OpAsm
import GoFV.Asm.Abi

/-!
# arm64 `ssaGenValue`, part B (C3)

Port of the cases of `cmd/compile/internal/arm64/ssa.go`'s `ssaGenValue` that emit atomics,
block zeroing/copying, calls and runtime calls (`docs/PASSES3.md` C3, I3 #549):

* `ssa.go:1038-1352`: the LL/SC (`LDAXR`/`STLXR`/`CBNZ` loops) and LSE (`SWPAL`, `LDADDAL`,
  `CASAL`, `LDCLRAL`, `LDORAL`) atomics. Local back edges are `TYPE_BRANCH` operands whose
  `Val` is the target Prog (`To.SetTarget`), by Prog ID.
* `ssa.go:1495-1735` with the helpers `zero16`, `zero8`, `move32`, `move16`, `move8`
  (`ssa.go:2114-2223`): `LoweredZero`, `LoweredZeroLoop`, `LoweredMove`, `LoweredMoveLoop`.
* `ssa.go:1736-1850`: `CALLstatic`/`CALLclosure`/`CALLinter` (`State.Call`), `CALLtail`/
  `CALLtailinter` (`State.TailCall`), `LoweredWB` (`runtime.gcWriteBarrier<n>`),
  `LoweredMemEq` (`runtime.memequal`), `LoweredPanicBounds{RR,RC,CR,CC}` with the
  `PCDATA_PanicBounds` entry (`ssa.BoundsKind.Code`, `ssa/op.go:495-535`;
  `abi.BoundsEncode`, `internal/abi/bounds.go`) — the `CR` case moves an out-of-range constant
  `x` into a register without setting `xIsReg`, exactly as Go does (#541) — and
  `LoweredNilCheck`.
* `ssa.go:1878-1934`: `PRFM`, `LoweredGetClosurePtr` (`ssagen.CheckLoweredGetClosurePtr`,
  `ssagen/ssa.go:7831-7847`), `LoweredGetCallerSP`, `LoweredGetCallerPC`, `DMB`, the
  `FlagConstant`/`InvertFlags` fatals, `Clobber`, `ClobberReg`.

The runtime symbols are `typecheck.LookupRuntimeFunc` symbols (`ssagen/ssa.go:118-153`):
`runtime.<name>` with ABI `ABIInternal` (1). Go's `Fatalf`/`panic` become `throw`. The
`base.Debug.Nil` warning of `LoweredNilCheck` (`ssa.go:1848`) does not change the Prog list and
is not reproduced.
-/

namespace GoFV.Gen.Arm64

open GoFV.SSA
open GoFV.Asm
open GoFV.Asm.ARM64 (REGTMP REGSP REGZERO REG_R0 REG_R24 REG_R25 REG_F16 REG_F17 SPOP_EQ C_XPOST)

namespace ValueB

open GenM

/-- `obj.ABIInternal`. -/
private def abiInternal : Nat := 1

/-- `arm64`'s `Arch.FixedFrameSize` (`cmd/internal/sys/arch.go`: 8, the saved LR). -/
private def fixedFrameSize : Int := 8

/-- `s.Prog(as)` followed by setting its fields. -/
def emit (as : As) (f : Prog → Prog) : GenM Nat := do
  let p ← sprog as
  modP p f
  return p

/-- `v.Args[i].Reg()`. -/
def argReg (v : Value) (i : Nat) : GenM Int := do
  let some a := v.args[i]? | throw s!"genValue: v{v.id} has no argument {i}"
  lift ((← env).reg a)

def reg0 (v : Value) : GenM Int := do lift ((← env).reg0 v.id)
def vreg (v : Value) : GenM Int := do lift ((← env).reg v.id)
def regTmp (v : Value) : GenM Int := do lift ((← env).regTmp v.id)

def regA (r : Int) : Addr := { type := .REG, reg := r }
def memA (r : Int) (off : Int := 0) : Addr := { type := .MEM, reg := r, offset := off }
def constA (c : Int) : Addr := { type := .CONST, offset := c }
/-- A `TYPE_BRANCH` operand with `SetTarget(p)`. -/
def branchTo (p : Nat) : Addr := { type := .BRANCH, val := .target p }
/-- `TYPE_REGREG` pair `(r1, r2)`: `Reg = r1`, `Offset = r2`. -/
def regRegA (r1 r2 : Int) : Addr := { type := .REGREG, reg := r1, offset := r2 }

/-- `CSET EQ, out` (`TYPE_SPECIAL` condition in `From.Offset`). -/
def csetEq (out : Int) : GenM Nat :=
  emit .CSET fun p => { p with from_ := { type := .SPECIAL, offset := SPOP_EQ }, to := regA out }

/-- `p.To.SetTarget(t)` on an already emitted branch. -/
def setTarget (p t : Nat) : GenM Unit :=
  modP p fun x => { x with to := { x.to with val := .target t } }

/-! ## Helpers (`ssa.go:2114-2223`) -/

/-- `zero16`: `STP (ZR, ZR), off(reg)`, or `STP.P (ZR, ZR), 16(reg)` with `postInc`. -/
def zero16 (reg : Int) (off : Int) (postInc : Bool) : GenM Unit := do
  let p ← emit .STP fun p => { p with from_ := regRegA REGZERO REGZERO, to := memA reg off }
  if postInc then
    if off != 0 then throw "genValue: can't postinc with non-zero offset"
    modP p fun x => { x with scond := C_XPOST.toNat, to := { x.to with offset := 16 } }

/-- `zero8`: `MOVD ZR, off(reg)`. -/
def zero8 (reg : Int) (off : Int) : GenM Unit := do
  discard <| emit .MOVD fun p => { p with from_ := regA REGZERO, to := memA reg off }

/-- `move32`: `FLDPQ off(src), (tmp1, tmp2)`; `FSTPQ (tmp1, tmp2), off(dst)` (post-increment
by 32 with `postInc`). -/
def move32 (src dst tmp1 tmp2 : Int) (off : Int) (postInc : Bool) : GenM Unit := do
  let ld ← emit .FLDPQ fun p => { p with from_ := memA src off, to := regRegA tmp1 tmp2 }
  let st ← emit .FSTPQ fun p => { p with from_ := regRegA tmp1 tmp2, to := memA dst off }
  if postInc then
    if off != 0 then throw "genValue: can't postinc with non-zero offset"
    modP ld fun x => { x with scond := C_XPOST.toNat, from_ := { x.from_ with offset := 32 } }
    modP st fun x => { x with scond := C_XPOST.toNat, to := { x.to with offset := 32 } }

/-- `move16`: `FMOVQ off(src), tmp1`; `FMOVQ tmp1, off(dst)` (post-increment by 16 with
`postInc`). -/
def move16 (src dst tmp1 : Int) (off : Int) (postInc : Bool) : GenM Unit := do
  let ld ← emit .FMOVQ fun p => { p with from_ := memA src off, to := regA tmp1 }
  let st ← emit .FMOVQ fun p => { p with from_ := regA tmp1, to := memA dst off }
  if postInc then
    if off != 0 then throw "genValue: can't postinc with non-zero offset"
    modP ld fun x => { x with scond := C_XPOST.toNat, from_ := { x.from_ with offset := 16 } }
    modP st fun x => { x with scond := C_XPOST.toNat, to := { x.to with offset := 16 } }

/-- `move8`: `MOVD off(src), tmp`; `MOVD tmp, off(dst)`. -/
def move8 (src dst tmp : Int) (off : Int) : GenM Unit := do
  discard <| emit .MOVD fun p => { p with from_ := memA src off, to := regA tmp }
  discard <| emit .MOVD fun p => { p with from_ := regA tmp, to := memA dst off }

/-- The straight-line tail of `LoweredZero`/`LoweredZeroLoop` (`ssa.go:1503-1523`,
`1579-1598`). -/
def zeroTail (ptrReg : Int) (n : Int) : GenM Unit := do
  let mut off : Int := 0
  let mut n := n
  while n >= 16 do
    zero16 ptrReg off false
    off := off + 16
    n := n - 16
  if n > 8 then
    zero8 ptrReg off
    off := off + 8
    n := n - 8
  if n != 0 then zero8 ptrReg (off + n - 8)

/-- The straight-line tail of `LoweredMove`/`LoweredMoveLoop` (`ssa.go:1622-1648`,
`1708-1734`). -/
def moveTail (src dst tmpReg1 tmpFReg1 tmpFReg2 : Int) (n : Int) : GenM Unit := do
  let mut off : Int := 0
  let mut n := n
  while n >= 32 do
    move32 src dst tmpFReg1 tmpFReg2 off false
    off := off + 32
    n := n - 32
  while n >= 16 do
    move16 src dst tmpFReg1 off false
    off := off + 16
    n := n - 16
  if n > 8 then
    move8 src dst tmpReg1 off
    off := off + 8
    n := n - 8
  if n != 0 then move8 src dst tmpReg1 (off + n - 8)

/-! ## Bounds failures (`internal/abi/bounds.go`, `ssa/op.go:470-535`) -/

/-- `ssa.BoundsKind.Code`: the runtime's `abi.BoundsErrorCode` and whether `x` is signed
(`BoundsIndex` … `BoundsSlice3CU` alternate signed/unsigned, `BoundsConvert` is unsigned). -/
def boundsCode (k : Int) : Except String (Int × Bool) :=
  if 0 ≤ k && k < 16 then pure (k / 2, k % 2 == 0)
  else if k == 16 then pure (GoFV.Asm.Abi.BoundsConvert, false)
  else throw s!"bad bounds kind {k}"

/-- `abi.BoundsEncode`. The bit fields are disjoint once the range checks pass, so Go's `|=`
is `+` here. -/
def boundsEncode (code : Int) (signed xIsReg yIsReg : Bool) (xVal yVal : Int) :
    Except String Int := do
  let mut c : Int := 0
  if xIsReg then
    c := c + 1
    if signed then c := c + 4
    if xVal < 0 || xVal > GoFV.Asm.Abi.BoundsMaxReg then throw "bad xReg"
    c := c + xVal * 8
  else
    if xVal < 0 || xVal > GoFV.Asm.Abi.BoundsMaxConst then throw "bad xConst"
    c := c + xVal * 4
  if yIsReg then
    c := c + 2
    if yVal < 0 || yVal > GoFV.Asm.Abi.BoundsMaxReg then throw "bad yReg"
    c := c + yVal * 128
  else
    if yVal < 0 || yVal > GoFV.Asm.Abi.BoundsMaxConst then throw "bad yConst"
    c := c + yVal * 128
  return c * GoFV.Asm.Abi.numBoundsCodes + code

/-- The aux kind of `v`. -/
def auxKind (v : Value) : GenM AuxKind := do
  let some a := v.aux | throw s!"genValue: v{v.id} has no aux"
  return (← lift ((← env).auxDef a)).kind

/-- `MOVD $c, R<k>` into `REG_R0 + k`. -/
def movConst (c : Int) (k : Int) : GenM Unit := do
  discard <| emit .MOVD fun p => { p with from_ := constA c, to := regA (REG_R0 + k) }

/-- `ssa.go:1752-1835`. -/
def panicBounds (v : Value) : GenM Unit := do
  let (code, signed) ← lift (boundsCode v.auxInt.toInt)
  let mut xIsReg := false
  let mut yIsReg := false
  let mut xVal : Int := 0
  let mut yVal : Int := 0
  match v.op with
  | .ARM64LoweredPanicBoundsRR =>
    xIsReg := true
    xVal := (← argReg v 0) - REG_R0
    yIsReg := true
    yVal := (← argReg v 1) - REG_R0
  | .ARM64LoweredPanicBoundsRC =>
    xIsReg := true
    xVal := (← argReg v 0) - REG_R0
    let .pbc c ← auxKind v | throw s!"genValue: v{v.id}: aux is not PanicBoundsC"
    if c >= 0 && c <= GoFV.Asm.Abi.BoundsMaxConst then
      yVal := c
    else
      yIsReg := true
      if yVal == xVal then yVal := 1
      movConst c yVal
  | .ARM64LoweredPanicBoundsCR =>
    yIsReg := true
    yVal := (← argReg v 0) - REG_R0
    let .pbc c ← auxKind v | throw s!"genValue: v{v.id}: aux is not PanicBoundsC"
    if c >= 0 && c <= GoFV.Asm.Abi.BoundsMaxConst then
      xVal := c
    else
      -- Go does not set `xIsReg` here (#541).
      if xVal == yVal then xVal := 1
      movConst c xVal
  | .ARM64LoweredPanicBoundsCC =>
    let .pbcc cx cy ← auxKind v | throw s!"genValue: v{v.id}: aux is not PanicBoundsCC"
    if cx >= 0 && cx <= GoFV.Asm.Abi.BoundsMaxConst then
      xVal := cx
    else
      xIsReg := true
      movConst cx xVal
    if cy >= 0 && cy <= GoFV.Asm.Abi.BoundsMaxConst then
      yVal := cy
    else
      yIsReg := true
      yVal := 1
      movConst cy yVal
  | _ => throw s!"genValue: v{v.id} is not a PanicBounds op"
  let c ← lift (boundsEncode code signed xIsReg yIsReg xVal yVal)
  discard <| emit .PCDATA fun p =>
    { p with from_ := constAddr GoFV.Asm.Abi.PCDATA_PanicBounds, to := constAddr c }
  let y ← sym (GoStr.ofString "runtime.panicBounds") abiInternal
  discard <| emit .CALL fun p => { p with to := { type := .MEM, name := .EXTERN, sym := some y } }

/-! ## Atomics (`ssa.go:1038-1352`) -/

def atomic (v : Value) : GenM Bool := do
  match v.op with
  | .ARM64LoweredAtomicExchange64 | .ARM64LoweredAtomicExchange32
  | .ARM64LoweredAtomicExchange8 =>
    let (ld, st) : As × As := match v.op with
      | .ARM64LoweredAtomicExchange8 => (.LDAXRB, .STLXRB)
      | .ARM64LoweredAtomicExchange32 => (.LDAXRW, .STLXRW)
      | _ => (.LDAXR, .STLXR)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    let p ← emit ld fun p => { p with from_ := memA r0, to := regA out }
    discard <| emit st fun p => { p with from_ := regA r1, to := memA r0, regTo2 := REGTMP }
    discard <| emit .CBNZ fun x => { x with from_ := regA REGTMP, to := branchTo p }
  | .ARM64LoweredAtomicExchange64Variant | .ARM64LoweredAtomicExchange32Variant
  | .ARM64LoweredAtomicExchange8Variant =>
    let swap : As := match v.op with
      | .ARM64LoweredAtomicExchange8Variant => .SWPALB
      | .ARM64LoweredAtomicExchange32Variant => .SWPALW
      | _ => .SWPALD
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    discard <| emit swap fun p => { p with from_ := regA r1, to := memA r0, regTo2 := out }
  | .ARM64LoweredAtomicAdd64 | .ARM64LoweredAtomicAdd32 =>
    let (ld, st) : As × As :=
      if v.op == .ARM64LoweredAtomicAdd32 then (.LDAXRW, .STLXRW) else (.LDAXR, .STLXR)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    let p ← emit ld fun p => { p with from_ := memA r0, to := regA out }
    discard <| emit .ADD fun p => { p with from_ := regA r1, to := regA out }
    discard <| emit st fun p => { p with from_ := regA out, to := memA r0, regTo2 := REGTMP }
    discard <| emit .CBNZ fun x => { x with from_ := regA REGTMP, to := branchTo p }
  | .ARM64LoweredAtomicAdd64Variant | .ARM64LoweredAtomicAdd32Variant =>
    let op : As := if v.op == .ARM64LoweredAtomicAdd32Variant then .LDADDALW else .LDADDALD
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    discard <| emit op fun p => { p with from_ := regA r1, to := memA r0, regTo2 := out }
    discard <| emit .ADD fun p => { p with from_ := regA r1, to := regA out }
  | .ARM64LoweredAtomicCas64 | .ARM64LoweredAtomicCas32 =>
    let (ld, st, cmp) : As × As × As :=
      if v.op == .ARM64LoweredAtomicCas32 then (.LDAXRW, .STLXRW, .CMPW)
      else (.LDAXR, .STLXR, .CMP)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let r2 ← argReg v 2
    let out ← reg0 v
    let p ← emit ld fun p => { p with from_ := memA r0, to := regA REGTMP }
    discard <| emit cmp fun p => { p with from_ := regA r1, reg := REGTMP }
    let p2 ← emit .BNE fun p => { p with to := { p.to with type := .BRANCH } }
    discard <| emit st fun p => { p with from_ := regA r2, to := memA r0, regTo2 := REGTMP }
    discard <| emit .CBNZ fun x => { x with from_ := regA REGTMP, to := branchTo p }
    let p5 ← csetEq out
    setTarget p2 p5
  | .ARM64LoweredAtomicCas64Variant | .ARM64LoweredAtomicCas32Variant =>
    let (cas, cmp, mov) : As × As × As :=
      if v.op == .ARM64LoweredAtomicCas32Variant then (.CASALW, .CMPW, .MOVW)
      else (.CASALD, .CMP, .MOVD)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let r2 ← argReg v 2
    let out ← reg0 v
    discard <| emit mov fun p => { p with from_ := regA r1, to := regA REGTMP }
    discard <| emit cas fun p => { p with from_ := regA REGTMP, to := memA r0, regTo2 := r2 }
    discard <| emit cmp fun p => { p with from_ := regA r1, reg := REGTMP }
    discard <| csetEq out
  | .ARM64LoweredAtomicAnd64 | .ARM64LoweredAtomicOr64 | .ARM64LoweredAtomicAnd32
  | .ARM64LoweredAtomicOr32 | .ARM64LoweredAtomicAnd8 | .ARM64LoweredAtomicOr8 =>
    let (ld, st) : As × As :=
      if v.op == .ARM64LoweredAtomicAnd8 || v.op == .ARM64LoweredAtomicOr8 then (.LDAXRB, .STLXRB)
      else if v.op == .ARM64LoweredAtomicAnd32 || v.op == .ARM64LoweredAtomicOr32 then
        (.LDAXRW, .STLXRW)
      else (.LDAXR, .STLXR)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    let tmp ← regTmp v
    let p ← emit ld fun p => { p with from_ := memA r0, to := regA out }
    discard <| emit (opAsm v.op) fun p => { p with from_ := regA r1, reg := out, to := regA tmp }
    discard <| emit st fun p => { p with from_ := regA tmp, to := memA r0, regTo2 := REGTMP }
    discard <| emit .CBNZ fun x => { x with from_ := regA REGTMP, to := branchTo p }
  | .ARM64LoweredAtomicAnd8Variant | .ARM64LoweredAtomicAnd32Variant
  | .ARM64LoweredAtomicAnd64Variant =>
    let clr : As := match v.op with
      | .ARM64LoweredAtomicAnd32Variant => .LDCLRALW
      | .ARM64LoweredAtomicAnd8Variant => .LDCLRALB
      | _ => .LDCLRALD
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    discard <| emit .MVN fun p => { p with from_ := regA r1, to := regA REGTMP }
    discard <| emit clr fun p => { p with from_ := regA REGTMP, to := memA r0, regTo2 := out }
  | .ARM64LoweredAtomicOr8Variant | .ARM64LoweredAtomicOr32Variant
  | .ARM64LoweredAtomicOr64Variant =>
    let orr : As := match v.op with
      | .ARM64LoweredAtomicOr32Variant => .LDORALW
      | .ARM64LoweredAtomicOr8Variant => .LDORALB
      | _ => .LDORALD
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let out ← reg0 v
    discard <| emit orr fun p => { p with from_ := regA r1, to := memA r0, regTo2 := out }
  | _ => return false
  return true

/-! ## Zeroing and copying (`ssa.go:1495-1735`) -/

def zeroMove (v : Value) : GenM Bool := do
  let loopSize : Int := 64
  match v.op with
  | .ARM64LoweredZero =>
    let ptrReg ← argReg v 0
    let n := v.auxInt.toInt
    if n < 16 then throw s!"genValue: Zero too small {n}"
    zeroTail ptrReg n
  | .ARM64LoweredZeroLoop =>
    let ptrReg ← argReg v 0
    let countReg ← regTmp v
    let n := v.auxInt.toInt
    if n < 3 * loopSize then throw s!"genValue: ZeroLoop size too small {n}"
    let cntInit ← emit .MOVD fun p => { p with from_ := constA (n / loopSize), to := regA countReg }
    for _ in [0:(loopSize / 16).toNat] do
      zero16 ptrReg 0 true
    discard <| emit .SUB fun p => { p with from_ := constA 1, to := regA countReg }
    let some head ← linkOf cntInit | throw s!"genValue: v{v.id}: cntInit.Link is nil"
    discard <| emit .CBNZ fun p => { p with from_ := regA countReg, to := branchTo head }
    zeroTail ptrReg (n % loopSize)
  | .ARM64LoweredMove =>
    let dstReg ← argReg v 0
    let srcReg ← argReg v 1
    if dstReg != srcReg then
      let n := v.auxInt.toInt
      if n < 16 then throw s!"genValue: Move too small {n}"
      moveTail srcReg dstReg REG_R25 REG_F16 REG_F17 n
  | .ARM64LoweredMoveLoop =>
    let dstReg ← argReg v 0
    let srcReg ← argReg v 1
    if dstReg != srcReg then
      let countReg := REG_R24
      let n := v.auxInt.toInt
      if n < 3 * loopSize then throw s!"genValue: ZeroLoop size too small {n}"
      let cntInit ← emit .MOVD fun p =>
        { p with from_ := constA (n / loopSize), to := regA countReg }
      for _ in [0:(loopSize / 32).toNat] do
        move32 srcReg dstReg REG_F16 REG_F17 0 true
      discard <| emit .SUB fun p => { p with from_ := constA 1, to := regA countReg }
      let some head ← linkOf cntInit | throw s!"genValue: v{v.id}: cntInit.Link is nil"
      discard <| emit .CBNZ fun p => { p with from_ := regA countReg, to := branchTo head }
      moveTail srcReg dstReg REG_R25 REG_F16 REG_F17 (n % loopSize)
  | _ => return false
  return true

/-! ## Calls, runtime calls, nil checks (`ssa.go:1736-1850`) -/

def calls (v : Value) : GenM Bool := do
  match v.op with
  | .ARM64CALLstatic | .ARM64CALLclosure | .ARM64CALLinter => discard <| call v
  | .ARM64CALLtail | .ARM64CALLtailinter => discard <| tailCall v
  | .ARM64LoweredWB =>
    -- `ir.Syms.GCWriteBarrier[v.AuxInt-1]`: `runtime.gcWriteBarrier1` … `8`.
    let k := v.auxInt.toInt
    if k < 1 || k > 8 then throw s!"genValue: v{v.id}: GCWriteBarrier index {k - 1} out of range"
    let y ← sym (GoStr.ofString s!"runtime.gcWriteBarrier{k}") abiInternal
    discard <| emit .CALL fun p => { p with to := { type := .MEM, name := .EXTERN, sym := some y } }
  | .ARM64LoweredMemEq =>
    let y ← sym (GoStr.ofString "runtime.memequal") abiInternal
    discard <| emit .CALL fun p => { p with to := { type := .MEM, name := .EXTERN, sym := some y } }
  | .ARM64LoweredPanicBoundsRR | .ARM64LoweredPanicBoundsRC | .ARM64LoweredPanicBoundsCR
  | .ARM64LoweredPanicBoundsCC => panicBounds v
  | .ARM64LoweredNilCheck =>
    let r ← argReg v 0
    let p ← sprog .MOVB
    let from_ ← addAux (memA r) v
    modP p fun x => { x with from_, to := regA REGTMP }
  | _ => return false
  return true

/-! ## Miscellaneous (`ssa.go:1878-1934`) -/

/-- `ssagen.CheckLoweredGetClosurePtr` (`ssagen/ssa.go:7831-7847`). -/
def checkLoweredGetClosurePtr (v : Value) : GenM Unit := do
  let e ← env
  let bad : GenM Unit := throw s!"genValue: badly placed LoweredGetClosurePtr: b{v.block} v{v.id}"
  if e.f.entry != v.block then bad
  let entry ← lift (e.block e.f.entry)
  for w in entry.values do
    if w == v.id then break
    let wv ← lift (e.value w)
    match wv.op with
    | .ArgIntReg | .ArgFloatReg => pure ()
    | _ => bad

def misc (v : Value) : GenM Bool := do
  match v.op with
  | .ARM64PRFM =>
    let r ← argReg v 0
    discard <| emit (opAsm v.op) fun p => { p with from_ := memA r, to := constA v.auxInt.toInt }
  | .ARM64LoweredGetClosurePtr => checkLoweredGetClosurePtr v
  | .ARM64LoweredGetCallerSP =>
    let r ← vreg v
    discard <| emit .MOVD fun p =>
      { p with from_ := { type := .ADDR, offset := -fixedFrameSize, name := .PARAM }, to := regA r }
  | .ARM64LoweredGetCallerPC =>
    let r ← vreg v
    discard <| emit .GETCALLERPC fun p => { p with to := regA r }
  | .ARM64DMB =>
    discard <| emit (opAsm v.op) fun p => { p with from_ := constA v.auxInt.toInt }
  | .ARM64FlagConstant =>
    throw s!"genValue: FlagConstant op should never make it to codegen v{v.id}"
  | .ARM64InvertFlags =>
    throw s!"genValue: InvertFlags should never make it to codegen v{v.id}"
  | .Clobber =>
    discard <| emit .MOVW fun p => { p with from_ := constA 0xdeaddead, to := regA REGTMP }
    let p ← sprog .MOVW
    let to ← addAux (memA REGSP) v
    modP p fun x => { x with from_ := regA REGTMP, to }
    let p ← sprog .MOVW
    let to ← addAux2 (memA REGSP) v (v.auxInt.toInt + 4)
    modP p fun x => { x with from_ := regA REGTMP, to }
  | .ClobberReg =>
    let r ← vreg v
    -- `int64(uint64(0xdeaddeaddeaddead))`.
    discard <| emit .MOVD fun p =>
      { p with from_ := constA ((0xdeaddeaddeaddead : Int) - 2 ^ 64), to := regA r }
  | _ => return false
  return true

end ValueB

/-- C3 part B: `true` iff `v.Op` is one of part B's ops (then emitted). -/
def ssaGenValueB (v : Value) : GenM Bool := do
  if ← ValueB.atomic v then return true
  if ← ValueB.zeroMove v then return true
  if ← ValueB.calls v then return true
  ValueB.misc v

end GoFV.Gen.Arm64
