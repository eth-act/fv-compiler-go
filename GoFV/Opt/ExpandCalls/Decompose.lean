import GoFV.Opt.ExpandCalls.State

/-!
# expand calls: dismantling call arguments and function results

`decomposeAsNecessary` (`expand_calls.go:362`) with `decomposeOne`/`decomposePair`
(`:338-352`): pre-order, each selector is allocated before its recursion; leaves go to the
register list or become `Store`s threaded on memory. `rewriteCallArgs` (`:270`) and
`rewriteFuncResults` (`:220`) drive it per argument/result.
-/

namespace GoFV.Opt.ExpandCalls

open GoFV.SSA

mutual

/-- `x.decomposeAsNecessary(pos, b, a, m0, rc)`. -/
def decomposeAsNecessary : Nat → Pos → ID → ID → ID → Cursor → M ID
  | 0, _, _, _, _, _ => throw "decomposeAsNecessary: too deep"
  | fuel + 1, pos, b, a, m0, rc => do
    let aty := (← val a).type
    if (← tsize aty) == 0 then return m0
    if (← val a).op == .Dereference then modV a fun x => { x with op := .Load }
    if !rc.hasRegs && !(← canSSA aty) then
      let some dest := rc.storeDest | throw "decomposeAsNecessary: no store destination"
      let dst ← offsetFrom b dest rc.storeOffset (← ptrTo aty)
      let x ← val a
      if x.op == .Load then
        let ta ← typeAux aty
        return ← newV b pos .Move (← read).mem (Int64.ofInt (← tsize aty)) ta
          #[dst, x.args[0]!, m0]
      else throw "Store of not a load"
    let d ← tdef aty
    let c ← read
    match d.kind with
    | .ARRAY =>
      let .array et n := d.tail | throw s!"array t{aty} without element"
      let mut pos := pos
      let mut mem := m0
      let mut rc := rc
      for i in [0:n.toNat] do
        let e ← newV b pos .ArraySelect et (Int64.ofNat i) none #[a]
        pos := pos.withNotStmt
        let (r, rc') ← rc.next et
        rc := rc'
        mem ← decomposeAsNecessary fuel pos b e mem r
      return mem
    | .STRUCT =>
      let .struct fs := d.tail | throw s!"struct t{aty} without fields"
      let mut pos := pos
      let mut mem := m0
      let mut rc := rc
      for h : i in [0:fs.size] do
        let et := fs[i].type
        let e ← newV b pos .StructSelect et (Int64.ofNat i) none #[a]
        pos := pos.withNotStmt
        let (r, rc') ← rc.next et
        rc := rc'
        mem ← decomposeAsNecessary fuel pos b e mem r
      return mem
    | .SLICE =>
      let pt ← ptrTo (← telem aty)
      let (mem, rc) ← decomposeOne fuel pos b a m0 pt .SlicePtr rc
      let pos := pos.withNotStmt
      let (mem, rc) ← decomposeOne fuel pos b a mem c.int .SliceLen rc
      return (← decomposeOne fuel pos b a mem c.int .SliceCap rc).1
    | .STRING =>
      return (← decomposePair fuel pos b a m0 c.bytePtr c.int .StringPtr .StringLen rc).1
    | .INTER =>
      let (mem, rc) ← decomposeOne fuel pos b a m0 c.uintptr .ITab rc
      let pos := pos.withNotStmt
      let x ← val a
      if x.op == .IMake then
        let mut data := x.args[1]!
        for _ in [0:(← getF).valueTab.size + 1] do
          let dx ← val data
          if dx.op != .StructMake && dx.op != .ArrayMake1 then break
          let mut found := false
          for y in dx.args do
            if (← tsize (← val y).type) > 0 then
              data := y
              found := true
              break
          if !found then throw "IMake data: aggregate without a sized part"
        let (r, _) ← rc.next (← val data).type
        return ← decomposeAsNecessary fuel pos b data mem r
      return (← decomposeOne fuel pos b a mem c.bytePtr .IData rc).1
    | .COMPLEX64 =>
      return (← decomposePair fuel pos b a m0 c.float32 c.float32 .ComplexReal .ComplexImag rc).1
    | .COMPLEX128 =>
      return (← decomposePair fuel pos b a m0 c.float64 c.float64 .ComplexReal .ComplexImag rc).1
    | k =>
      if (k == .INT64 || k == .UINT64) && (← tsize aty) > 8 then
        throw "decomposeAsNecessary: 64-bit integer wider than a register"
      if rc.hasRegs then
        rc.addArg a
        return m0
      let some dest := rc.storeDest | throw "decomposeAsNecessary: no store destination"
      let dst ← offsetFrom b dest rc.storeOffset (← ptrTo aty)
      let ta ← typeAux aty
      newV b pos .Store c.mem 0 ta #[dst, a, m0]

/-- `x.decomposeOne(pos, b, a, mem, t0, o0, &rc)`: the memory and the advanced cursor. -/
def decomposeOne : Nat → Pos → ID → ID → ID → TypeRef → Op → Cursor → M (ID × Cursor)
  | 0, _, _, _, _, _, _, _ => throw "decomposeOne: too deep"
  | fuel + 1, pos, b, a, mem, t0, o0, rc => do
    let e ← newV b pos o0 t0 0 none #[a]
    let (r, rc) ← rc.next t0
    let mem ← decomposeAsNecessary fuel pos.withNotStmt b e mem r
    return (mem, rc)

/-- `x.decomposePair(pos, b, a, mem, t0, t1, o0, o1, &rc)`. -/
def decomposePair : Nat → Pos → ID → ID → ID → TypeRef → TypeRef → Op → Op → Cursor →
    M (ID × Cursor)
  | 0, _, _, _, _, _, _, _, _, _ => throw "decomposePair: too deep"
  | fuel + 1, pos, b, a, mem, t0, t1, o0, o1, rc => do
    let e ← newV b pos o0 t0 0 none #[a]
    let pos := pos.withNotStmt
    let (r, rc) ← rc.next t0
    let mem ← decomposeAsNecessary fuel pos b e mem r
    let e ← newV b pos o1 t1 0 none #[a]
    let (r, rc) ← rc.next t1
    let mem ← decomposeAsNecessary fuel pos b e mem r
    return (mem, rc)

end

/-- `decomposeAsNecessary` with the type recursion bound. -/
def decompose (pos : Pos) (b a m0 : ID) (rc : Cursor) : M ID :=
  decomposeAsNecessary (2 * typeFuel) pos b a m0 rc

/-- `x.rewriteCallArgs(v, firstArg)` (`:270`). -/
def rewriteCallArgs (v : ID) (firstArg : Nat) : M Unit := do
  let x ← val v
  let (info, cfg) ← callABI x.aux
  let m0 := x.args[x.args.size - 1]!
  let mut mem := m0
  modify fun s => { s with regValues := #[] }
  let argsWithoutMem := x.args.extract firstArg (x.args.size - 1)
  let c ← read
  let isTail := x.op == .TailLECall || x.op == .TailLECallInter
  let sp ← if isTail then newV x.block Pos.none .GetCallerSP c.uintptr 0 none #[mem] else pure c.sp
  for h : i in [0:argsWithoutMem.size] do
    let a := argsWithoutMem[i]
    let p ← info.inParam i
    if (← val a).op == .Dereference then modV a fun y => { y with op := .Load }
    let aOffset : Int64 ← if p.regs.isEmpty then pure (Int64.ofInt (← info.offsetOfArg i))
      else pure 0
    let ax ← val a
    if x.op == .TailLECall && ax.op == .Arg && ax.auxInt == 0 then
      let some n := ax.aux | throw "OpArg without aux"
      match (← auxDef n).kind with
      | .name _ .PPARAM _ fo .. =>
        if fo + c.fixedFrameSize == aOffset.toInt then continue
      | .name .. => pure ()
      | _ => throw s!"OpArg aux a{n} is not an ir.Name"
    let rc := Cursor.init p.regs cfg (!p.regs.isEmpty) (some sp) aOffset
    mem ← decompose x.pos x.block a mem rc
  let preArgs := x.args.extract 0 firstArg
  let regs := (← get).regValues
  modF fun f => ((f.resetArgs v).addArgs v preArgs).addArgs v regs |>.addArg v mem
  for a in argsWithoutMem do
    if (← val a).uses == 0 then invalidateRecursively a

/-- `x.rewriteFuncResults(v, b, f.OwnAux)` (`:220`). -/
def rewriteFuncResults (v b : ID) (ownAux : Option AuxRef) : M Unit := do
  let x ← val v
  let (info, cfg) ← callABI ownAux
  let m0 := x.args[x.args.size - 1]!
  let mut mem := m0
  modify fun s => { s with regValues := #[] }
  let argsWithoutMem := x.args.extract 0 (x.args.size - 1)
  let c ← read
  for h : j in [0:argsWithoutMem.size] do
    let a := argsWithoutMem[j]
    let p ← info.outParam j
    let some name := p.name | throw s!"result {j} of the function has no name"
    let auxBase ← newV b x.pos .LocalAddr (← ptrTo p.type) 0 (some name) #[c.sp, mem]
    if (← val a).op == .Dereference then modV a fun y => { y with op := .Load }
    if p.regs.isEmpty then
      let ax ← val a
      if ax.op == .Load then
        let ptr ← val ax.args[0]!
        if ptr.op == .LocalAddr && ptr.aux == some name then continue
    let rc := Cursor.init p.regs cfg (!p.regs.isEmpty) (some auxBase) 0
    mem ← decompose x.pos b a mem rc
  let regs := (← get).regValues
  modF fun f => ((f.resetArgs v).addArgs v regs).addArg v mem
  for a in argsWithoutMem do
    if (← val a).uses == 0 then invalidateRecursively a
  let rts ← registerTypes (← get).tabs (← regTypes) info.outParams
  let t ← newResults (rts.push c.mem)
  modV v fun y => { y with type := t }

end GoFV.Opt.ExpandCalls
