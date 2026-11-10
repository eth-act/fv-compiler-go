import GoFV.Gen.Check57

variable [GoFV.SSA.Sem.Addrs]

/-!
# The genssa validator, slice G48: stack arguments and stack results
(`docs/plans/proofs3.md` §8, item 7)

Go's internal ABI assigns the arguments and results that do not fit its registers to the
caller's outgoing-arguments area, at `ABIParam.offset` (which includes arm64's fixed frame word,
so `≥ 8`). Phase 1's outgoing area is the block `Blk.outargs act`, which `SP` points to (`SP` is
`.ptr ⟨.outargs act, 0⟩`): the caller stores a stack argument with `MOVDstore [o] SP x mem` before
the call, the callee's contract reads it there (`decodeArgs`), and writes a stack result there
(`encodeResults`), which the caller loads after the call with `MOVDload [o] SP mem`. Up to G57,
`callRegs` (`Gen/Check2.lean`) rejects such calls (`stack argument`, `stack result`; G15's
`callRegsZ` drops only the zero-sized stack inputs), and the accesses off `SP` without a frame
variable have their base in the Go register `SP`, which is no X register.

G48 accepts, tried when G57 rejects a value (`vkind48`):

* a static call as G47 checks it (`callKind47`), on its ABI without its stack-assigned inputs and
  outputs (`callRegsS`): their values pass through the outgoing area, not through registers;
* an access off `SP` without an aux (`spKind48`): a store of G3 (`MOVD`/`MOVW`/`MOVH`/`MOVB`),
  `STP` of two 64-bit registers, `STPW` of the low words of two registers of at least 32 bits,
  `FMOVS`/`FMOVD` stores, `FSTPD` of two 64-bit floats; a load of G3, `FMOVS`/`FMOVD` loads.
  Its window `[o, o + n)` lies in `[8, outargsSize)` (`outWin48`): above the fixed frame word,
  where the callee's prologue saves `LR` (`Blk.writableFrom`), and inside the outgoing area. The
  operand is `o(RSP)` (`memA regSP o`); the base, an `SP` value, is homed in the Go register `SP`
  at a 64-bit shape (`spBase48`).

Besides, the function homes nothing but `SP` values and `Phi`s in the Go register `SP`
(`spHomes48`): an access off `SP` reads its base from that register, which then holds `SP`'s pointer
or `poison` (the proof's `SPInv`, with `SPHomes`).

`checkG48 lc ps bstart g` is slice G57 (`GoFV/Gen/Check57.lean`) with these values and that home
check. G48's slice number predates G49–G57; it is checked last, on top of G57.
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- `callRegs` of the ABI without its stack-assigned inputs and outputs (no ABI register). -/
def callRegsS (abi : CallABI) : Except String (List Nat × List Nat) :=
  callRegs { abi with params := abi.params.filter (!·.regs.isEmpty) }

/-- A static call as G47 checks it (`callKind47`), on its ABI without its stack-assigned inputs
and outputs (`callRegsS`). -/
def callKind48 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 := do
  if (lc.temps[v.id]?).join != none then throw s!"v{v.id}: temporary register"
  let some (name, abi, cabi) := callOf? lc.ctx.tabs v.aux | throw s!"v{v.id}: call without ABI"
  let (ins, outs) ← callRegsS cabi
  unless outs.Nodup do throw s!"v{v.id}: result registers repeat"
  let some m := v.args.back? | throw s!"v{v.id}: call without memory"
  unless memTy (lc.ty m) && lc.home m == none do throw s!"v{v.id}: call memory"
  unless (ins ++ outs).all abiRegOK do throw s!"v{v.id}: ABI register above F15"
  let rargs := v.args.toList.dropLast
  unless rargs.length == ins.length do throw s!"v{v.id}: call arguments"
  unless (rargs.zip ins).all (fun (a, r) => regHome? lc a == some r) do
    throw s!"v{v.id}: an argument not in its ABI register"
  unless fArgsOK lc rargs ins do throw s!"v{v.id}: float register argument shape"
  match lc.home v.id with
  | some (.results rs) =>
    unless rs.toList == outs.map some do throw s!"v{v.id}: result registers"
  | none => unless outs.isEmpty do throw s!"v{v.id}: result registers"
  | _ => throw s!"v{v.id}: call home"
  unless callTy outs.length (lc.ty v.id) do
    throw s!"v{v.id}: {callTyErr outs.length (lc.ty v.id)}"
  unless fOutsOK (tupleTys (lc.ty v.id)) outs do throw s!"v{v.id}: float register result shape"
  return .prog (callPat g name abi)

/-- The `n` bytes at offset `o` of the outgoing area lie above its fixed frame word and inside
it. -/
def outWin48 (lc : LocCtx) (o : Int) (n : Nat) : Bool :=
  8 ≤ o && o + n ≤ outargsSize lc.ctx.tabs

/-- The memory operand `o(RSP)` of an access `v` off `SP` at `o = v.auxInt`. -/
def spDst48 (v : Value) (a : Addr) : Bool := a == memA regSP v.auxInt.toInt

/-- The base of an access off `SP` is homed in the Go register `SP` (`spReg`) at a 64-bit shape:
it reads its base from that register, which holds `SP`'s pointer or `poison` (`spHomes48`). -/
def spBase48 (lc : LocCtx) (v : Value) : Bool :=
  match v.args[0]? with
  | some a => lc.home a == some (.reg spReg) && cls (lc.ty a) == some 64
  | none => false

/-- `STP (Rx, Ry), o(RSP)`. -/
def stpSP48 (rx ry o : Int) : Shape := { as := .STP, from_ := pairA rx ry, to := memA regSP o }

/-- `STPW (Rx, Ry), o(RSP)`. -/
def stpwSP48 (rx ry o : Int) : Shape := { as := .STPW, from_ := pairA rx ry, to := memA regSP o }

/-- `FSTPD (Fx, Fy), o(RSP)`. -/
def fstpdSP48 (rx ry o : Int) : Shape := { as := .FSTPD, from_ := pairA rx ry, to := memA regSP o }

/-- What an access `v` off `SP` without an aux and with no temporary emits (module doc), or why it
is outside G48. -/
def spKind48 (lc : LocCtx) (v : Value) : Except String VKind2 := do
  if let some (as, n, sg) := loadOp? v.op then
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    unless outWin48 lc v.auxInt.toInt n do throw s!"v{v.id}: SP access outside the outgoing area"
    memArg lc v 1
    let (c, rd) ← resObj lc v
    unless 8 ≤ c || (c == 1 && n == 1 && !sg) do throw s!"v{v.id}: load widths"
    return .prog ⟨plain as (spDst48 v) (· == regA rd), as.name⟩
  if let some (as, n) := storeOp? v.op then
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    unless outWin48 lc v.auxInt.toInt n do throw s!"v{v.id}: SP access outside the outgoing area"
    let (cs, rs) ← argObj lc v 1
    memArg lc v 2
    unless 8 * n ≤ cs || (cs == 1 && n == 1) do throw s!"v{v.id}: store widths"
    return .prog ⟨plain as (· == regA rs) (spDst48 v), as.name⟩
  match v.op with
  | .ARM64STP =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    unless outWin48 lc v.auxInt.toInt 16 do throw s!"v{v.id}: SP access outside the outgoing area"
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog (.ofShape (stpSP48 rx ry v.auxInt.toInt))
  | .ARM64STPW =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    unless outWin48 lc v.auxInt.toInt 8 do throw s!"v{v.id}: SP access outside the outgoing area"
    let (cx, rx) ← argObj lc v 1
    let (cy, ry) ← argObj lc v 2
    memArg lc v 3
    unless 32 ≤ cx && 32 ≤ cy do throw s!"v{v.id}: pair store widths"
    return .prog (.ofShape (stpwSP48 rx ry v.auxInt.toInt))
  | .ARM64FSTPD =>
    unless v.args.size == 4 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: pair store shape"
    unless outWin48 lc v.auxInt.toInt 16 do throw s!"v{v.id}: SP access outside the outgoing area"
    let (cx, rx) ← fargObj lc v 1
    let (cy, ry) ← fargObj lc v 2
    memArg lc v 3
    unless cx == 64 && cy == 64 do throw s!"v{v.id}: pair store widths"
    return .prog (.ofShape (fstpdSP48 rx ry v.auxInt.toInt))
  | .ARM64FMOVSload | .ARM64FMOVDload =>
    unless v.args.size == 2 do throw s!"v{v.id}: load shape"
    unless outWin48 lc v.auxInt.toInt (fBytes v.op) do
      throw s!"v{v.id}: SP access outside the outgoing area"
    memArg lc v 1
    let (c, rd) ← fresObj lc v
    unless c == 8 * fBytes v.op do throw s!"v{v.id}: load widths"
    return .prog ⟨plain (fmovAs c) (spDst48 v) (· == regA rd), (fmovAs c).name⟩
  | .ARM64FMOVSstore | .ARM64FMOVDstore =>
    unless v.args.size == 3 && memTy (lc.ty v.id) && lc.home v.id == none do
      throw s!"v{v.id}: store shape"
    unless outWin48 lc v.auxInt.toInt (fBytes v.op) do
      throw s!"v{v.id}: SP access outside the outgoing area"
    let (cs, rs) ← fargObj lc v 1
    memArg lc v 2
    unless cs == 8 * fBytes v.op do throw s!"v{v.id}: store widths"
    return .prog ⟨plain (fmovAs cs) (· == regA rs) (spDst48 v), (fmovAs cs).name⟩
  | _ => throw s!"v{v.id}: SP access {v.op.name}"

/-- G48's values (module doc), or why `v` is outside the slice; `e` is G57's reason, kept for the
other values. -/
def kind48 (lc : LocCtx) (g : G2In) (v : Value) (e : String) : Except String VKind2 :=
  if v.op = .ARM64CALLstatic then callKind48 lc g v
  else if v.aux = none ∧ spArg lc v = true then
    if (lc.temps[v.id]?).join != none then .error s!"v{v.id}: temporary register"
    else if !spBase48 lc v then .error s!"v{v.id}: SP access base not homed in SP"
    else spKind48 lc v
  else .error e

/-- What `v` emits in G48, or why it is outside the slice: G57's kinds, then G48's calls and
accesses off `SP`. -/
def vkind48 (lc : LocCtx) (g : G2In) (v : Value) : Except String VKind2 :=
  match vkind57 lc g v with
  | .ok kd => .ok kd
  | .error e => kind48 lc g v e

/-- `SPHomes`: the home of a value that lists the Go register `SP` (`spReg`) is a `Phi`'s (which
writes nothing) or `SP`'s own register home, at a 64-bit shape and with no temporary: the register
`SP` holds `SP`'s value or `poison` (`SPInv`). -/
def spHomes48 (lc : LocCtx) : Bool :=
  (List.range lc.ctx.f.valueTab.size).all fun i =>
    match lc.ctx.f.value? i with
    | some v =>
      match lc.home v.id with
      | some l =>
        !l.regList.contains (some spReg) || v.op == .Phi ||
          (l == .reg spReg && v.op == .SP && cls (lc.ty v.id) == some 64 &&
            (lc.temps[v.id]?).join == none)
      | none => true
    | none => true

/-- G57's check with G48's value check, and only `SP` homed in `SP` (`spHomes48`). -/
def checkG48L (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) :=
  if lc.ctx.f.lowered then do
    let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
    let cx : Cx := { lc, ps, idx, bstart }
    let c : Cx2 := { cx, g, vk := vkind48 lc g, tm := cx.termG3 }
    let tab ← c.blocks lc.ctx.f.blocks.toList
    unless pbOK lc ps.toList tab do throw "bounds panic PCDATA"
    unless loopOK lc ps tab do throw "loop branch target"
    unless movdOK35 lc && uEdgesOK35 lc do throw "MOVDnop/MOVDreg: upper bits unknown"
    if let some i := (List.range lc.homes.size).find? (!homeOK10 lc ·) then throw (homeErr lc i)
    unless cloFirst lc do throw "LoweredGetClosurePtr after code"
    unless spHomes48 lc do throw "a value other than SP homed in SP"
    checkFrame lc g
    checkVars49 lc g
    let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
    let kt : KTab := lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)
    checkK lc kt
    let ids := ps.toList.map (·.id)
    unless ids.all (· < 2 ^ 32) && ids.Nodup do throw "Prog IDs"
    return (tab, kt)
  else checkNL30 lc ps bstart g

/-- Slice G48 of the genssa validator (module doc): `refsLive`, then G48's check on `liveCtx lc`. -/
def checkG48 (lc : LocCtx) (ps : Array Prog) (bstart : ID → Option Nat) (g : G2In) :
    Except String (PcTab × KTab) := do
  unless refsLive lc do throw "a value refers to an ID that is no value of the function"
  checkG48L (liveCtx lc) ps bstart g

end GoFV.Gen.Check
