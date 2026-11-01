import GoFV.Opt.ExpandCalls.Decompose
import GoFV.Opt.ExpandCalls.Select

/-!
# expand calls (`expand_calls.go`)

ABI lowering for linux/arm64 (`docs/PASSES.md`, expand calls): incoming aggregate arguments
become `*Make`s of `ArgIntReg`/`ArgFloatReg`/`Arg` parts, call results become `*Make`s of
`SelectN`/`Load` parts, call arguments and function results are dismantled into register lists
and stack stores, and the `*LECall`s become `StaticCall`/`ClosureCall`/`InterCall`/`TailCall*`
with `RESULTS` types of their register results. Phases in Go's order — scan (mem selectors,
`SelectNAddr`), args, selects, calls, exits — each in `f.Blocks` × `b.Values` encounter
order; every allocation goes through the free list, the constant cache (`ConstOffPtrSP`) and
`NewPtr`/`NewResults`, exactly where Go's does. The pass's Go maps are lookup-only.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace ExpandCalls

/-- `f.spSb()` (`func.go:826`): SP and SB of `f.Entry`, created (SB first) if missing. -/
def spSb (uintptr : TypeRef) : M (ID × ID) := do
  let f ← getF
  let mut sp : Option ID := none
  let mut sb : Option ID := none
  for v in (f.getB f.entry).values do
    let x ← val v
    if x.op == .SB then sb := some v
    if x.op == .SP then sp := some v
    if sb.isSome && sp.isSome then break
  let sbV ← match sb with
    | some v => pure v
    | none => newV f.entry Pos.none .SB uintptr
  let spV ← match sp with
    | some v => pure v
    | none => newV f.entry Pos.none .SP uintptr
  return (spV, sbV)

/-- The kinds of values the scan collects. -/
structure Lists where
  selects : Array ID := #[]
  calls : Array ID := #[]
  args : Array ID := #[]
  exitBlocks : Array ID := #[]
  m0 : Option ID := none

/-- `isBlockMultiValueExit(b)`. -/
def isBlockMultiValueExit (b : Block) : M Bool := do
  if b.kind != .Ret && b.kind != .RetJmp then return false
  match b.controls[0]? with
  | some c => return (← val c).op == .MakeResult
  | none => return false

/-- The scan (`:67-119`). -/
def scan : M Lists := do
  let mut ls : Lists := {}
  let c ← read
  for b in (← getF).blocks do
    for v in ((← getF).getB b).values do
      let x ← val v
      match x.op with
      | .InitMem => ls := { ls with m0 := some v }
      | .ClosureLECall | .InterLECall | .StaticLECall | .TailLECall | .TailLECallInter =>
        ls := { ls with calls := ls.calls.push v }
      | .Arg => ls := { ls with args := ls.args.push v }
      | .Store =>
        let a := x.args[1]!
        let ax ← val a
        if ax.op == .SelectN && !(← canSSA ax.type) then
          if ax.uses > 1 then throw s!"Saw double use of wide SelectN v{a} operand of Store v{v}"
          modify fun s => { s with wideSelects := s.wideSelects.insert a v }
      | .SelectN =>
        if x.type == c.mem then
          let call := x.args[0]!
          let (info, _) ← callABI (← val call).aux
          if (← get).memForCall.contains call then
            throw s!"Saw two memories for call v{call}"
          modV v fun y => { y with auxInt := Int64.ofInt info.outRegs }
          modify fun s => { s with memForCall := s.memForCall.insert call v }
        else ls := { ls with selects := ls.selects.push v }
      | .SelectNAddr =>
        let call := x.args[0]!
        let (info, _) ← callABI (← val call).aux
        let off ← info.offsetOfResult x.auxInt.toInt.toNat
        let o ← offsetFrom (← getF).entry c.sp (Int64.ofInt off) x.type
        modF (·.copyOf v o)
      | _ => pure ()
    if ← isBlockMultiValueExit ((← getF).getB b) then
      ls := { ls with exitBlocks := ls.exitBlocks.push b }
  return ls

/-- Args (`:122-134`). -/
def rewriteArgs (ls : Lists) : M Unit := do
  let c ← read
  let some m0 := ls.m0 | if ls.args.isEmpty then return else throw "no InitMem"
  let f ← getF
  let (info, cfg) ← callABI f.ownAux
  for v in ls.args do
    let x ← val v
    if x.op != .Arg then throw s!"Wanted OpArg, instead saw v{v}"
    let some p := info.inParams.find? (fun p => p.name.isSome && p.name == x.aux)
      | throw s!"Did not match param of v{v} in prInfo"
    let offset ← if p.regs.isEmpty then p.frameOffset info cfg else pure 0
    let entry := (← getF).entry
    let auxBase ← offsetFrom entry c.sp (Int64.ofInt offset) (← ptrTo x.type)
    let rc := Cursor.init p.regs cfg false (some auxBase) 0
    let pos := ((← getF).getB entry).pos
    discard <| rewriteSelectOrArg (2 * typeFuel) pos entry v (some v) m0 x.type rc

/-- Selects (`:137-185`). -/
def rewriteSelects (ls : Lists) : M Unit := do
  let c ← read
  for v in ls.selects do
    let x ← val v
    if x.op == .Invalid then continue
    let call := x.args[0]!
    let cx ← val call
    let (info, cfg) ← callABI cx.aux
    let mem ← match (← get).memForCall[call]? with
      | some m => pure m
      | none => do
        let m ← newV cx.block cx.pos .SelectN c.mem (Int64.ofInt info.outRegs) none #[call]
        modify fun s => { s with memForCall := s.memForCall.insert call m }
        pure m
    let i := x.auxInt.toInt.toNat
    let regs := (← info.outParam i).regs
    if let some store := (← get).wideSelects[v]? then
      let sx ← val store
      let storeAddr := sx.args[0]!
      let mem := sx.args[2]!
      if !regs.isEmpty then
        let rc := Cursor.init regs cfg false (some storeAddr) 0
        let mem ← rewriteWideSelectToStores (2 * typeFuel) cx.pos cx.block v mem x.type rc
        modF (·.copyOf store mem)
      else
        let offset ← info.offsetOfResult i
        let auxBase ← offsetFrom (← getF).entry c.sp (Int64.ofInt offset) (← ptrTo x.type)
        let ta ← typeAux x.type
        let move ← newV sx.block sx.pos .Move c.mem (Int64.ofInt (← tsize x.type)) ta
          #[storeAddr, auxBase, mem]
        modF (·.copyOf store move)
      continue
    let auxBase ← if regs.isEmpty then do
        let offset ← info.offsetOfResult i
        pure (some (← offsetFrom (← getF).entry c.sp (Int64.ofInt offset) (← ptrTo x.type)))
      else pure none
    let rc := Cursor.init regs cfg false auxBase 0
    discard <| rewriteSelectOrArg (2 * typeFuel) cx.pos cx.block v (some v) mem x.type rc

/-- Calls (`:187-209`). -/
def rewriteCalls (ls : Lists) : M Unit := do
  let c ← read
  for v in ls.calls do
    let x ← val v
    let (newOp, argStart) ← match x.op with
      | .StaticLECall => pure (Op.StaticCall, 0)
      | .TailLECall => pure (.TailCall, 0)
      | .TailLECallInter => pure (.TailCallInter, 1)
      | .ClosureLECall => pure (.ClosureCall, 2)
      | .InterLECall => pure (.InterCall, 1)
      | _ => throw s!"v{v} is not an LECall"
    rewriteCallArgs v argStart
    modV v fun y => { y with op := newOp }
    let (info, _) ← callABI x.aux
    let rts ← registerTypes (← get).tabs (← regTypes) info.outParams
    let t ← newResults (rts.push c.mem)
    modV v fun y => { y with type := t }

/-- Exits (`:212-216`). -/
def rewriteExits (ls : Lists) : M Unit := do
  for b in ls.exitBlocks do
    let some v := ((← getF).getB b).controls[0]? | throw s!"exit b{b} without control"
    rewriteFuncResults v b (← getF).ownAux
    modF (·.setControl b v)

def run : M Unit := do
  let ls ← scan
  rewriteArgs ls
  rewriteSelects ls
  rewriteCalls ls
  rewriteExits ls

end ExpandCalls

open ExpandCalls in
/-- The `expand calls` pass (`expandCalls`, `expand_calls.go:21`). -/
def expandCallsPass : Pass := fun env f => do
  let word (k : String) : Except String String := match env.config? k with
    | some #[.word w] => pure w
    | _ => throw s!"config {k}: missing"
  let int (k : String) : Except String Int := do
    match decInt? (← word k) with
    | some n => pure n
    | none => throw s!"config {k}: not an integer"
  let typ (n : String) : Except String TypeRef := match env.typ? n with
    | some t => pure t
    | none => throw s!"typs: no {n}"
  if (← int "regsize") != 8 then throw "expand calls: only RegSize 8 is ported"
  if (← env.flag "bigendian") then throw "expand calls: only little endian is ported"
  let cfg (k : String) : Except String ABIConfig := do
    match ABIConfig.parse? (← word k) with
    | some c => pure c
    | none => throw s!"config {k}: not <int>:<float>:<offset>"
  let abiConfigs := #[← cfg "abi0", ← cfg "abi1"]
  let uintptr ← typ "Uintptr"
  let ctx0 : Ctx :=
    { sp := 0, ptrSize := ← int "ptrsize", fixedFrameSize := ← int "fixedframesize", abiConfigs
      mem := ← typ "Mem", resultMem := ← typ "ResultMem", int := ← typ "Int", uintptr
      bytePtr := ← typ "BytePtr", unsafePtr := ← typ "UnsafePtr", float32 := ← typ "Float32"
      float64 := ← typ "Float64", order := env.typeOrder
      typeFloor := max env.tables.types.size env.typeOrder.rank.size
      auxFloor := env.tables.auxes.size }
  let st0 : St := { f, tabs := env.tables }
  let ((sp, _), st) ← (spSb uintptr).run ctx0 |>.run st0
  let ((), st) ← run.run { ctx0 with sp } |>.run st
  return { func := st.f, tables := st.tabs }

end GoFV.Opt
