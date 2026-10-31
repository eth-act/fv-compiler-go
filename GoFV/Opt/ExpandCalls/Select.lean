import GoFV.Opt.ExpandCalls.State

/-!
# expand calls: assembling incoming arguments and call results

`rewriteSelectOrArg` (`expand_calls.go:491`): an aggregate `OpArg`/`OpSelectN` becomes a
`*Make` of its parts, children allocated before the reused parent (`makeOf`, `:498`); leaves are
`ArgIntReg`/`ArgFloatReg`/`Arg` or `SelectN`/`Load`. `rewriteWideSelectToStores` (`:706`):
a non-SSAable register result stored to memory becomes per-leaf `SelectN` + `Store`.
-/

namespace GoFV.Opt.ExpandCalls

open GoFV.SSA

/-- `makeOf(a, op, args)` (`:498`) at position `pos`, block `b`, type `aty` (Go's `at`). -/
def makeOf (pos : Pos) (b : ID) (aty : TypeRef) (a : Option ID) (op : Op) (args : Array ID) :
    M ID := do
  match a with
  | none => newV b pos op aty 0 none args
  | some a =>
    modF (·.resetArgs a)
    modV a fun x => { x with aux := none, auxInt := 0, pos, op, type := aty }
    modF (·.addArgs a args)
    return a

/-- `x.rewriteSelectOrArg(pos, b, container, a, m0, at, rc)`. -/
def rewriteSelectOrArg : Nat → Pos → ID → ID → Option ID → ID → TypeRef → Cursor → M ID
  | 0, _, _, _, _, _, _, _ => throw "rewriteSelectOrArg: too deep"
  | fuel + 1, pos, b, container, a, m0, aty, rc => do
    let c ← read
    if aty == c.mem then
      let some a := a | throw "rewriteSelectOrArg: memory part"
      modF (·.copyOf a m0)
      return a
    let size ← tsize aty
    if size == 0 then return ← makeOf pos b aty a .Empty #[]
    let sk : SelKey := ⟨container, rc.storeOffset, 0, aty⟩
    if let some dupe := (← get).commonSelectors[sk]? then
      match a with
      | none => return dupe
      | some a => modF (·.copyOf a dupe); return a
    let rec_ := rewriteSelectOrArg fuel
    let finish (r : ID) : M ID := do
      modify fun s => { s with commonSelectors := s.commonSelectors.insert sk r }
      return r
    let d ← tdef aty
    match d.kind with
    | .ARRAY =>
      let .array et n := d.tail | throw s!"array t{aty} without element"
      let mut rc := rc
      let mut args := #[]
      for _ in [0:n.toNat] do
        let (r, rc') ← rc.next et
        rc := rc'
        args := args.push (← rec_ pos b container none m0 et r)
      finish (← makeOf pos b aty a .ArrayMake1 args)
    | .STRUCT =>
      let .struct fs := d.tail | throw s!"struct t{aty} without fields"
      let mut rc := rc
      let mut pos := pos
      let mut args := #[]
      for fld in fs do
        let (r, rc') ← rc.next fld.type
        rc := rc'
        args := args.push (← rec_ pos b container none m0 fld.type r)
        pos := pos.withNotStmt
      if fs.size > maxStruct && !d.flags.direct then
        throw s!"Too many fields ({fs.size}, {size} bytes)"
      finish (← makeOf pos b aty a .StructMake args)
    | .SLICE =>
      let pt ← ptrTo (← telem aty)
      let (r, rc) ← rc.next c.bytePtr
      let x0 ← rec_ pos b container none m0 pt r
      let pos := pos.withNotStmt
      let (r, rc) ← rc.next c.int
      let x1 ← rec_ pos b container none m0 c.int r
      let (r, _) ← rc.next c.int
      let x2 ← rec_ pos b container none m0 c.int r
      finish (← makeOf pos b aty a .SliceMake #[x0, x1, x2])
    | .STRING =>
      let (r, rc) ← rc.next c.bytePtr
      let x0 ← rec_ pos b container none m0 c.bytePtr r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next c.int
      let x1 ← rec_ pos b container none m0 c.int r
      finish (← makeOf pos b aty a .StringMake #[x0, x1])
    | .INTER =>
      let (r, rc) ← rc.next c.uintptr
      let x0 ← rec_ pos b container none m0 c.uintptr r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next c.bytePtr
      let x1 ← rec_ pos b container none m0 c.bytePtr r
      finish (← makeOf pos b aty a .IMake #[x0, x1])
    | .COMPLEX64 | .COMPLEX128 =>
      let ft := if d.kind == .COMPLEX64 then c.float32 else c.float64
      let (r, rc) ← rc.next ft
      let x0 ← rec_ pos b container none m0 ft r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next ft
      let x1 ← rec_ pos b container none m0 ft r
      finish (← makeOf pos b aty a .ComplexMake #[x0, x1])
    | k =>
      if (k == .INT64 || k == .UINT64) && size > 8 then
        throw "rewriteSelectOrArg: 64-bit integer wider than a register"
      let cx ← val container
      if cx.op == .Arg then
        if rc.hasRegs then
          let (op, i) ← rc.argOpAndRegisterFor
          let some name := cx.aux | throw "OpArg without aux"
          let r ← makeOf pos b aty a op #[]
          let na ← newNameOffset name rc.storeOffset
          modV r fun x => { x with auxInt := i, aux := some na }
          finish r
        else
          let key : SelKey := ⟨container, rc.storeOffset, size, aty⟩
          let w? := (← get).commonArgs[key]?
          let hit ← match w? with
            | some w => pure ((← val w).uses != 0)
            | none => pure false
          if hit then
            let w := w?.get!
            match a with
            | none => finish w
            | some a => modF (·.copyOf a w); finish a
          else
            let r ← match a with
              | none => newV cx.block cx.pos .Arg aty (cx.auxInt + rc.storeOffset) cx.aux
              | some a => pure a
            modify fun s => { s with commonArgs := s.commonArgs.insert key r }
            finish r
      else if cx.op == .SelectN then
        let call := cx.args[0]!
        let (info, _) ← callABI (← val call).aux
        let which := cx.auxInt.toInt.toNat
        if rc.hasRegs then
          let mut firstReg := 0
          for i in [0:which] do firstReg := firstReg + (← info.outParam i).regs.size
          let reg := (rc.nextSlice + firstReg % 256) % 256
          let r ← makeOf pos b aty a .SelectN #[call]
          modV r fun x => { x with auxInt := Int64.ofNat reg }
          finish r
        else
          let off := rc.storeOffset + Int64.ofInt (← info.offsetOfResult which)
          let o ← offsetFrom (← getF).entry c.sp off (← ptrTo aty)
          finish (← makeOf pos b aty a .Load #[o, m0])
      else throw s!"Expected container OpArg or OpSelectN, saw {cx.op.name}"

/-- `x.rewriteWideSelectToStores(pos, b, container, m0, aty, rc)`. -/
def rewriteWideSelectToStores : Nat → Pos → ID → ID → ID → TypeRef → Cursor → M ID
  | 0, _, _, _, _, _, _ => throw "rewriteWideSelectToStores: too deep"
  | fuel + 1, pos, b, container, m0, aty, rc => do
    let c ← read
    let size ← tsize aty
    if size == 0 then return m0
    let rec_ := rewriteWideSelectToStores fuel
    let d ← tdef aty
    match d.kind with
    | .ARRAY =>
      let .array et n := d.tail | throw s!"array t{aty} without element"
      let mut rc := rc
      let mut m0 := m0
      for _ in [0:n.toNat] do
        let (r, rc') ← rc.next et
        rc := rc'
        m0 ← rec_ pos b container m0 et r
      return m0
    | .STRUCT =>
      let .struct fs := d.tail | throw s!"struct t{aty} without fields"
      let mut rc := rc
      let mut m0 := m0
      let mut pos := pos
      for fld in fs do
        let (r, rc') ← rc.next fld.type
        rc := rc'
        m0 ← rec_ pos b container m0 fld.type r
        pos := pos.withNotStmt
      return m0
    | .SLICE =>
      let pt ← ptrTo (← telem aty)
      let (r, rc) ← rc.next c.bytePtr
      let m0 ← rec_ pos b container m0 pt r
      let pos := pos.withNotStmt
      let (r, rc) ← rc.next c.int
      let m0 ← rec_ pos b container m0 c.int r
      let (r, _) ← rc.next c.int
      rec_ pos b container m0 c.int r
    | .STRING =>
      let (r, rc) ← rc.next c.bytePtr
      let m0 ← rec_ pos b container m0 c.bytePtr r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next c.int
      rec_ pos b container m0 c.int r
    | .INTER =>
      let (r, rc) ← rc.next c.uintptr
      let m0 ← rec_ pos b container m0 c.uintptr r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next c.bytePtr
      rec_ pos b container m0 c.bytePtr r
    | .COMPLEX64 | .COMPLEX128 =>
      let ft := if d.kind == .COMPLEX64 then c.float32 else c.float64
      let (r, rc) ← rc.next ft
      let m0 ← rec_ pos b container m0 ft r
      let pos := pos.withNotStmt
      let (r, _) ← rc.next ft
      rec_ pos b container m0 ft r
    | k =>
      if (k == .INT64 || k == .UINT64) && size > 8 then
        throw "rewriteWideSelectToStores: 64-bit integer wider than a register"
      let cx ← val container
      if cx.op != .SelectN then
        throw s!"Expected container OpSelectN, saw {cx.op.name}"
      if !rc.hasRegs then throw "Expected rc to have registers"
      let call := cx.args[0]!
      let (info, _) ← callABI (← val call).aux
      let mut firstReg := 0
      for i in [0:cx.auxInt.toInt.toNat] do firstReg := firstReg + (← info.outParam i).regs.size
      let reg := (rc.nextSlice + firstReg % 256) % 256
      let sel ← newV b pos .SelectN aty (Int64.ofNat reg) none #[call]
      let some dest := rc.storeDest | throw "rewriteWideSelectToStores: no store destination"
      let dst ← offsetFrom b dest rc.storeOffset (← ptrTo aty)
      let ta ← typeAux aty
      newV b pos .Store c.mem 0 ta #[dst, sel, m0]

end GoFV.Opt.ExpandCalls
