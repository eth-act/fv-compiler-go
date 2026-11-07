import GoFV.Gen.Arm64Value
import GoFV.Gen.Frame
import GoFV.SSA.ABI

/-!
# `defframe` (C6)

Port of `ssagen.defframe` (`cmd/compile/internal/ssagen/ssa.go:7536-7641`): the `TEXT` argument
and frame sizes, the spills of partially live register arguments (`Arch.SpillArgReg`), and the
zeroing of ambiguously live autos with range merging (`Arch.ZeroRange`); plus the
`f.OwnAux.ABIInfo()` accessors it and `genssa` use (`ArgWidth`, `abiutils.go:79`).
-/

namespace GoFV.Gen

open GoFV.SSA GoFV.Asm

/-- `f.OwnAux.ABIInfo()`. -/
def GenM.ownABI : GenM CallABI := do
  let env ← GenM.env
  let some a := env.f.ownAux | throw "f.OwnAux is nil"
  match (← GenM.lift (env.auxDef a)).kind with
  | .call _ (some abi) => pure abi
  | _ => throw s!"f.OwnAux a{a} has no ABI info"

/-- `ABIParamResultInfo.ArgWidth()` (`abiutils.go:79`). -/
def GenM.argWidth (abi : CallABI) : GenM Int := do
  let c ← GenM.lift (abiConfigOf (← GenM.env) abi.abi)
  return abi.spillSize + abi.spillOff - c.localsOffset

/-- `t.HasPointers()` of an `.ssa` type (size must be calculated). -/
def GenM.typeHasPointers (t : TypeRef) : GenM Bool := do
  let d ← GenM.lift ((← GenM.env).typeDef t)
  if d.size.isNone then throw s!"type t{t}: HasPointers needs the size"
  return d.flags.hasptr

/-- `ssa.CanSSA(t)`. -/
def GenM.canSSA (t : TypeRef) : GenM Bool := do
  GenM.lift (GoFV.SSA.canSSA (← GenM.env).tabs 8 typeFuel t)

/-- `n.Addrtaken()` (static: read from the `Dcl` flags when `AllocFrame` starts). -/
def GenM.addrtaken (n : Nat) : GenM Bool := do
  return ((← GenM.env).inFlags[n]?).any (·.addrtaken)

/-- `n.Type()` of a `Dcl` name as an `.ssa` type. -/
def GenM.nameType (n : Nat) : GenM TypeRef := do
  match (← GenM.nameInfo n).ssaType with
  | some t => pure t
  | none => throw s!"name n{n}: no .ssa type"

/-- The `Dcl` name of an ABI parameter (`a.Name`; `none`: nil, or not a `Dcl` name, which
`partLiveArgs` never contains). -/
def GenM.paramName? (p : ABIParam) : GenM (Option Nat) := do
  return p.name.bind (← GenM.env).nameOfAux?

/-- C6: `defframe` (`ssagen/ssa.go:7536`). -/
def defframe : GenM Unit := do
  let ctx ← read
  let env := ctx.env
  let fr := ctx.frame
  let maxarg ← GenM.lift (roundUp (← get).maxarg fr.stkalign)
  modify fun s => { s with maxarg }
  let frame := Arm64.padFrame (maxarg + fr.stksize)
  let abi ← GenM.ownABI
  let argw ← GenM.lift (roundUp (← GenM.argWidth abi) regSize)
  let text := (← get).text
  GenM.modP text fun x =>
    { x with to := { x.to with type := .TEXTSIZE, val := .textSize argw, offset := frame } }
  let mut p := text
  -- Spill partially live register arguments.
  if abi.inRegs != 0 && (← GenM.lift env.flagN) == 0 then
    let partLive := (← get).live.partLiveArgs
    let mut spilled : Std.HashSet (Nat × Int) := {}
    let some entry := env.f.block? env.f.entry | throw "no entry block"
    for vid in entry.values do
      let v ← GenM.lift (env.value vid)
      if v.op.call then break
      if v.op != .StoreReg then continue
      let some a0 := v.args[0]? | throw s!"v{vid}: StoreReg without argument"
      if (← GenM.lift (env.value a0)).op != .ArgIntReg then continue
      -- `partLiveArgs` holds `Dcl` names only: test it first (the other tests are pure).
      let some (.slot k) := env.loc? vid | throw s!"v{vid}: AutoVar of a non-slot location"
      let some n := env.nameOfAux? k.name | continue
      if !partLive.contains n then continue
      let x ← GenM.nameInfo n
      if x.cls != "PPARAM" || (← GenM.addrtaken n) || !(← GenM.canSSA (← GenM.nameType n)) then
        continue
      spilled := spilled.insert (n, k.off)
    for a in abi.inParams do
      let some n ← GenM.paramName? a | continue
      if !partLive.contains n || a.regs.size ≤ 1 then continue
      if (← GenM.addrtaken n) || !(← GenM.canSSA (← GenM.nameType n)) then continue
      let (rts, offs) ← GenM.lift (registerTypesAndOffsets env a)
      for i in [0:a.regs.size] do
        let some t := rts[i]? | throw s!"defframe: no register type {i}"
        let some o := offs[i]? | throw s!"defframe: no register offset {i}"
        if !(← GenM.typeHasPointers t) then continue
        if spilled.contains (n, o) then continue
        let reg ← GenM.lift (objRegForAbiReg a.regs[i]!)
        p ← Arm64.spillArgReg p t reg n o
  -- Zero ambiguously live variables.
  let mut lo : Int := 0
  let mut hi : Int := 0
  for d in (← get).dcl do
    if !d.flags.needzero then continue
    let x ← GenM.nameInfo d.name
    if x.cls != "PAUTO" then throw s!"needzero class {x.cls}"
    let sz ← GenM.lift x.size
    if sz % 8 != 0 || d.off % 8 != 0 || sz == 0 then
      throw s!"var {x.d.sym.toStringLossy} has size {sz} offset {d.off}"
    if lo != hi && d.off + sz >= lo - 16 then
      lo := d.off
      continue
    p ← Arm64.zeroRange p (frame + lo) (hi - lo)
    lo := d.off
    hi := lo + sz
  let _ ← Arm64.zeroRange p (frame + lo) (hi - lo)

end GoFV.Gen
