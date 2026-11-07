import GoFV.Gen.State
import GoFV.Gen.MergeLocals
import GoFV.SSA.ABI

/-!
# Frame layout, `f.RegArgs` and open-coded defer info (A1–A3)

Ports (go1.27.3):

* `ssagen.AllocFrame`, `cmpstackvarlt`, `needAlloc` (`ssagen/pgen.go:29-295`): `Used`
  recomputation (autos reset, then `f.RegAlloc` `LocalSlot` homes and `*ir.Name` auxes of the
  values), `liveness.MergeLocals` (`GoFV.Gen.MergeLocals`), the `sort.SliceStable` of `Dcl`, the
  follower repositioning, frame offsets (truncation into `FuncDebug.OptDcl`), follower offsets
  and the `stksize`/`stkptrsize` rounding — the `frame` section's `out`, `opt`, `merge` and
  `stack` lines.
* The `buildssa` tail (`ssagen/ssa.go:601-617`): `f.RegArgs` from the input parameters of
  `f.OwnAux`'s ABI analysis, with `ABIParamAssignment.RegisterTypesAndOffsets`
  (`abi/abiutils.go:137-240`, `appendParamOffsets`; `appendParamTypes` is
  `GoFV.SSA.appendParamTypes`), `ABIParamAssignment.FrameOffset` (`abiutils.go:249`) and
  `ssa.ObjRegForAbiReg` (`ssa/op.go:195-210`).
* `state.emitOpenDeferInfo` (`ssagen/ssa.go:270-290`), run by `genssa`'s port on the frame it
  is given.
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm (DclEntry)

/-! ## Helpers -/

/-- `types.RoundUp(o, r)`: Go `Fatalf`s unless `r` is 1, 2, 4 or 8. -/
def roundUp (o r : Int) : Except String Int :=
  if r < 1 || r > 8 || (r.toNat &&& (r.toNat - 1)) != 0 then throw s!"Round {r}"
  else pure ((o + r - 1) / r * r)

/-! ## A1, A2: `AllocFrame` -/

/-- `types.RegSize` (arm64). -/
def regSize : Int := 8

/-- `types.MaxWidth` (`arm64.Arch.MAXWIDTH = 1 << 50`). -/
def maxWidth : Int := 2 ^ 50

/-- `needAlloc(n)` (`pgen.go:104`): autos and register-assigned results live in this frame. -/
def needAlloc (x : NameInfo) (fl : GoFV.Asm.NameFlags) : Except String Bool :=
  match x.cls with
  | "PAUTO" => pure true
  | "PPARAM" => pure false
  | "PPARAMOUT" => pure fl.outregs
  | c => throw s!"frame: n{x.n} has unexpected Class {c}"

/-- A `Dcl` entry with the facts the layout reads. -/
private structure FEntry where
  d : DclEntry
  info : NameInfo
  needAlloc : Bool
  deriving Inhabited

/-- `cmpstackvarlt(a, b, mls)` (`pgen.go:30`). -/
private def cmpstackvarlt (mls : Option MergeLocalsState) (a b : FEntry) :
    Except String Bool := do
  if a.needAlloc != b.needAlloc then return b.needAlloc
  if !a.needAlloc then return a.d.off < b.d.off
  if let some mls := mls then
    let aFollow := mls.subsumed a.d.name
    let bFollow := mls.subsumed b.d.name
    if aFollow != bFollow then return bFollow
  if a.d.flags.used != b.d.flags.used then return a.d.flags.used
  let ap ← a.info.hasPointers
  let bp ← b.info.hasPointers
  if ap != bp then return ap
  let az := a.d.flags.needzero
  let bz := b.d.flags.needzero
  if az != bz then return az
  let aa ← a.info.align
  let ba ← b.info.align
  if aa != ba then return aa > ba
  if a.d.flags.opendeferslot != b.d.flags.opendeferslot then return a.d.flags.opendeferslot
  if a.d.flags.opendeferslot then return a.d.off > b.d.off
  return goStrLt a.info.d.sym b.info.d.sym

/-- `(*ssafn).AllocFrame(f)` (`pgen.go:123-295`) on `Dcl` as it is when `AllocFrame` starts. -/
def allocFrame (env : Env) : Except String FrameOut := do
  let mut stksize : Int := 0
  let mut stkptrsize : Int := 0
  let mut stkalign : Int := regSize
  let mut dcl : Array FEntry := #[]
  let mut pos : Std.HashMap Nat Nat := {}
  for d in env.dclIn do
    let info ← env.name d.name
    pos := pos.insert d.name dcl.size
    dcl := dcl.push { d, info, needAlloc := ← needAlloc info d.flags }
  let setUsed (dcl : Array FEntry) (n : Nat) : Array FEntry :=
    match pos[n]? with
    | some i => dcl.modify i fun e => { e with d.flags.used := true }
    | none => dcl  -- not in `Dcl`: `SetUsed` has no effect on the layout
  -- Mark the PAUTO's unused.
  for i in [0:dcl.size] do
    let e := dcl[i]!
    if e.d.flags.opendeferslot then continue
    if e.needAlloc then dcl := dcl.set! i { e with d.flags.used := false }
  -- `f.RegAlloc` `LocalSlot` homes.
  if let some (_, es) := env.f.low.regAlloc then
    for (_, l) in es do
      if let .slot k := l then
        if let some n := env.nameOfAux? k.name then dcl := setUsed dcl n
  -- Values with an `*ir.Name` aux.
  for bid in env.f.blocks do
    let b ← env.block bid
    for vid in b.values do
      let v ← env.value vid
      let some a := v.aux | continue
      let .name _ cls .. := (← env.auxDef a).kind | continue
      let some n := env.nameOfAux? a | continue
      match cls with
      | .PPARAMOUT =>
        let outregs := (env.inFlags[n]?).any (·.outregs)
        if outregs && v.op == .VarDef then continue
        dcl := setUsed dcl n
      | .PPARAM | .PAUTO => dcl := setUsed dcl n
      | _ => pure ()
  let mls ← if (← env.mergeLocals) != 0 then mergeLocals env (dcl.map (·.d)) else pure none
  dcl ← stableSortM (cmpstackvarlt mls) dcl
  if let some mls := mls then
    -- Reposition followers immediately after their leader.
    let byName : Std.HashMap Nat FEntry := dcl.foldl (fun m e => m.insert e.d.name e) {}
    let mut newdcl : Array FEntry := Array.mkEmpty dcl.size
    for e in dcl do
      if mls.subsumed e.d.name then continue
      newdcl := newdcl.push e
      if mls.isLeader e.d.name then
        for m in ← mls.followers env e.d.name do
          match byName[m]? with
          | some f => newdcl := newdcl.push f
          | none => throw s!"frame: follower n{m} not in Dcl"
    dcl := newdcl
  -- Reassign stack offsets of the locals that are used.
  let mut lastHasPtr := false
  let mut optDcl : Array FEntry := #[]
  let mut leaders : Std.HashMap Nat Int := {}
  let mut cut : Option Nat := none
  for i in [0:dcl.size] do
    let e := dcl[i]!
    if e.info.cls != "PAUTO" && !(e.info.cls == "PPARAMOUT" && e.d.flags.outregs) then continue
    if let some mls := mls then
      if mls.subsumed e.d.name then continue
    if !e.d.flags.used then
      cut := some i
      break
    let mut w ← e.info.size
    if w >= maxWidth || w < 0 then throw "bad width"
    if w == 0 && lastHasPtr then w := 1
    let al ← e.info.align
    stksize := stksize + w
    stksize ← roundUp stksize al
    if al > regSize then stkalign := al
    if ← e.info.hasPointers then
      stkptrsize := stksize
      lastHasPtr := true
    else
      lastHasPtr := false
    dcl := dcl.set! i { e with d.off := -stksize }
    if let some mls := mls then
      if mls.isLeader e.d.name then leaders := leaders.insert e.d.name (-stksize)
  if let some i := cut then
    optDcl := dcl.extract i dcl.size
    dcl := dcl.extract 0 i
  if let some mls := mls then
    for i in [0:dcl.size] do
      let e := dcl[i]!
      if !mls.subsumed e.d.name then continue
      let leader ← mls.leader e.d.name
      let some off := leaders[leader]? | throw "internal error missing leader"
      dcl := dcl.set! i { e with d.off := off }
  stksize ← roundUp stksize stkalign
  stkptrsize ← roundUp stkptrsize stkalign
  let mut merges : Array (Nat × Array Nat) := #[]
  if let some mls := mls then
    for e in dcl do
      if mls.isLeader e.d.name then merges := merges.push (e.d.name, ← mls.followers env e.d.name)
  return { dcl := dcl.map (·.d), optDcl := optDcl.map (·.d), merges, stksize, stkptrsize,
           stkalign }

/-! ## A3: `f.RegArgs` -/

/-- `ssa.ObjRegForAbiReg(r, config)` for arm64 (`intParamRegs` R0–R15, `floatParamRegs`
F0–F15). -/
def objRegForAbiReg (r : Nat) : Except String Int := do
  let ints := ARM64.paramIntReg.toArray
  let floats := ARM64.paramFloatReg.toArray
  let m ← if r < ints.size then pure ints[r]!
    else match floats[r - ints.size]? with
      | some m => pure m
      | none => throw s!"abi register index {r} out of range"
  Env.objReg m

/-- The `Config.Types` entries the synthesized slice/string/interface structs and
`FloatForComplex` reach (`typs` of the `.ssa` file's first section). -/
def regTypesOf (env : Env) : Except String RegTypes := do
  let typs := (env.file.sections[0]?.bind (·.typs)).getD #[]
  let typ (n : String) : Except String TypeRef :=
    match typs.find? (·.1 == n) with
    | some (_, t) => pure t
    | none => throw s!"typs: no {n}"
  return { bytePtr := ← typ "BytePtr", int := ← typ "Int", unsafePtr := ← typ "UnsafePtr",
           float32 := ← typ "Float32", float64 := ← typ "Float64" }

/-- `align(a, t)` (`abiutils.go:492`): `alignTo(a, int(uint8(t.Alignment())))`. -/
private def alignAt (a : Int) (al : Int) : Except String Int :=
  let t := al % 256
  if t == 0 then pure a else roundUp a t

/-- `appendParamOffsets(offsets, at, t)` (`abiutils.go:197`) for 64-bit registers without SIMD.
The synthesized slice/string/interface structs have pointer-sized fields at 0, 8, (16) and
alignment 8. -/
partial def appendParamOffsets (tabs : Tables) (offsets : Array Int) (at_ : Int) (t : TypeRef) :
    Except String (Array Int × Int) := do
  let some d := tabs.type? t | throw s!"appendParamOffsets: type t{t} not defined"
  let some w := d.size | throw s!"appendParamOffsets: type t{t}: size not calculated"
  if w == 0 then return (offsets, at_)
  let synth (nf : Nat) : Except String (Array Int × Int) := do
    let mut offs := offsets
    let mut a := at_
    for k in [0:nf] do
      a := at_ + 8 * k
      offs := offs.push a
      a := a + 8
    return (offs, ← alignAt a 8)
  match d.kind with
  | .BOOL | .INT8 | .UINT8 | .INT16 | .UINT16 | .INT32 | .UINT32 | .INT64 | .UINT64 | .INT
  | .UINT | .UINTPTR | .COMPLEX64 | .COMPLEX128 | .FLOAT32 | .FLOAT64
  | .PTR | .UNSAFEPTR | .MAP | .CHAN | .FUNC =>
    if d.kind == .COMPLEX64 || d.kind == .COMPLEX128 || w > regSize then
      let s := w.tdiv 2
      return (offsets.push at_ |>.push (at_ + s), at_ + w)
    else return (offsets.push at_, at_ + w)
  | .ARRAY =>
    let .array te n := d.tail | throw s!"appendParamOffsets: array t{t} without element"
    let some ted := tabs.type? te | throw s!"appendParamOffsets: type t{te} not defined"
    let some tal := ted.align | throw s!"appendParamOffsets: type t{te}: alignment not calculated"
    let mut offs := offsets
    let mut a := at_
    for _ in [0:n.toNat] do
      a ← alignAt a tal
      (offs, a) ← appendParamOffsets tabs offs a te
    return (offs, a)
  | .STRUCT =>
    let .struct fs := d.tail | throw s!"appendParamOffsets: struct t{t} without fields"
    let some tal := d.align | throw s!"appendParamOffsets: type t{t}: alignment not calculated"
    let at0 := at_
    let mut offs := offsets
    let mut a := at_
    for h : i in [0:fs.size] do
      let f := fs[i]
      let some fo := f.offset | throw s!"appendParamOffsets: field offset of t{t} not calculated"
      a := at0 + fo
      (offs, a) ← appendParamOffsets tabs offs a f.type
      let some fd := tabs.type? f.type | throw s!"appendParamOffsets: type t{f.type} not defined"
      if fd.size == some 0 && i == fs.size - 1 then a := a + 1
    return (offs, ← alignAt a tal)
  | .SLICE => synth 3
  | .STRING => synth 2
  | .INTER => synth 2
  | _ => return (offsets, at_)

/-- `(*ABIParamAssignment).RegisterTypesAndOffsets()` (`abiutils.go:137`): the register piece
types (`.ssa` types) and their offsets within the parameter. -/
def registerTypesAndOffsets (env : Env) (p : ABIParam) :
    Except String (Array TypeRef × Array Int) := do
  if p.regs.size == 0 then return (#[], #[])
  let (offs, _) ← appendParamOffsets env.tabs #[] 0 p.type
  let typs ← appendParamTypes env.tabs (← regTypesOf env) typeFuel #[] p.type
  return (typs, offs)

/-- The `abi.ABIConfig` of ABI `which` (`config abi0`/`abi1` of the `.ssa` file). -/
def abiConfigOf (env : Env) (which : Nat) : Except String ABIConfig := do
  let k := s!"abi{which}"
  match env.config? k with
  | some #[.word w] =>
    match ABIConfig.parse? w with
    | some c => pure c
    | none => throw s!"config {k}: not <int>:<float>:<offset>"
  | _ => throw s!"config {k}: missing"

/-- The `buildssa` tail (`ssa.go:606-617`): `f.RegArgs`, one `ssa.Spill` per register piece of
every input parameter of `f.OwnAux`. -/
def regArgsOf (env : Env) : Except String (Array RegSpill) := do
  let some a := env.f.ownAux | throw "regargs: no f.OwnAux"
  let .call _ (some info) := (← env.auxDef a).kind
    | throw s!"regargs: f.OwnAux a{a} is not an AuxCall with ABI info"
  let cfg ← abiConfigOf env info.abi
  let mut out : Array RegSpill := #[]
  for p in info.inParams do
    let (typs, offs) ← registerTypesAndOffsets env p
    if offs.size < typs.size then
      throw s!"regargs: len(offs)={offs.size} < len(typs)={typs.size}"
    for h : i in [0:typs.size] do
      let o := offs[i]!
      let fo ← p.frameOffset info cfg
      let some r := p.regs[i]? | throw s!"regargs: register index {i} out of range"
      let reg ← objRegForAbiReg r
      out := out.push { reg, off := fo + o, type := typs[i] }
  return out

/-! ## A3: open-coded defer info -/

/-- `objw.Uvarint(s, off, v)`: appends the unsigned LEB128 encoding of `v`. -/
def uvarintBytes (out : ByteArray) (v : Nat) : ByteArray := Id.run do
  let mut out := out
  let mut v := v
  for _ in [0:10] do
    if v < 0x80 then break
    out := out.push (UInt8.ofNat (v % 0x80 + 0x80))
    v := v / 0x80
  out.push (UInt8.ofNat v)

/-- `obj.AttrContentAddressable` (`cmd/internal/obj/link.go`: the 16th `1 << iota` bit). -/
def attrContentAddressable : Nat := 1 <<< 15

/-- `uint64(x)` of an `int64`. -/
private def u64 (x : Int) : Nat := (x % (2 ^ 64 : Int)).toNat

/-- `(*state).emitOpenDeferInfo()` (`ssa.go:270-290`): the `<fn>.opendefer` symbol (offsets of
`deferBits` and the first closure slot below varp) and `FuncInfo.OpenCodedDeferInfo`. A no-op
without open-coded defers (`buildssa` calls it only if `len(s.openDefers) != 0`). -/
def emitOpenDeferInfo : GenM Unit := do
  let env ← GenM.env
  let some (deferBits, closures) := env.genin.openDefer | return
  let some c0 := closures[0]? | return
  let firstOffset ← GenM.frameOffset c0
  for h : i in [0:closures.size] do
    let have_ ← GenM.frameOffset closures[i]
    let want := firstOffset + (i : Int) * 8
    if have_ != want then
      throw s!"unexpected frame offset for open-coded defer slot #{i}: have {have_}, want {want}"
  let some (fname, _) := env.inSyms[env.genin.text.sym]?
    | throw s!"opendefer: no text symbol y{env.genin.text.sym}"
  let x ← GenM.sym (fname ++ GoStr.ofString ".opendefer") 0
  let data := uvarintBytes .empty (u64 (-(← GenM.frameOffset deferBits)))
  let data := uvarintBytes data (u64 (-firstOffset))
  -- `objw.Uvarint` → `LSym.WriteInt` → `prepwrite`: `Sxxx` becomes `SDATA` (`setFIPSType`
  -- never applies to `.opendefer` symbols).
  modify fun s => { s with
    symData := s.symData.insert x
      { kind := "SDATA", size := data.size, align := 1, attr := attrContentAddressable, data }
    aux := { s.aux with openCodedDeferInfo := some x } }

end GoFV.Gen
