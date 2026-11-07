import GoFV.Gen.State
import GoFV.Gen.LiveCore
import GoFV.Util.Sha256
import GoFV.Util.PdqSort
import GoFV.Asm.Abi

/-!
# `liveness.Compute` (B1)

Port of the stack-map half of `cmd/compile/internal/liveness/plive.go` (go1.27.3) on top of the
dataflow core (`GoFV.Gen.LiveCore`): `getvariables`/`shouldTrack` (219-237), `epilogue`
(749-900), `compact` (918-941), `pointerMap` (458-490), `emit` (1330-1388),
`checkStackmapOverflow` (1600-1610), `Compute` (1395-1461) and `emitStackObjects` (1463-1515);
the deduplicating set `bvecSet` (`liveness/bvset.go`); `typebits.Set`/`SetNoCheck`
(`typebits/typebits.go`) over the exported pointer masks; the `objw` writers it uses
(`objw/objw.go`: `Uint32`, `Uintptr`, `BitVec`, `SymPtrOff`); `obj.(*Link).GCLocalsSym`
(`cmd/internal/obj/sym.go:241-250`) with `cmd/internal/hash.Sum32`; and the stack-object GC
mask symbol of `reflectdata.GCSym(t, false)` (`reflectdata/reflect.go:1239-1308`, `dgcptrmask`
without writing: the mask symbol is written after the compilation, only its name matters here).

`bvecSet` keeps the unique bit vectors in insertion order and returns the index of the first
equal one; its FNV-1 open-addressing table only decides how a duplicate is found, so a hash map
on the contents gives the same indices.

`Dcl` is `GenState.dcl` (after `AllocFrame`); the flags `Used`, `Addrtaken`, `Needzero`,
`OpenDeferSlot`, `Heapaddr != nil`, `IsOutputParamHeapAddr` are read from it (`OptDcl` names are
not in `Dcl` and are unused). `base.Flag.Live` is 0 (no diagnostics).
-/

namespace GoFV.Gen.Liveness

open GoFV.SSA
open GoFV.Asm
open GoFV.Gen.Live

/-- `obj.AttrContentAddressable`. -/
def attrContentAddressable : Nat := 0x8000

/-- `bvecSet` (`bvset.go`): unique bit vectors in insertion order. -/
structure BvecSet where
  uniq : Array Bv := #[]
  index : Std.HashMap Bv Nat := {}

/-- `m.add(bv)`: the index of the equal vector, appending `bv` if it is new. -/
def BvecSet.add (m : BvecSet) (bv : Bv) : Nat × BvecSet :=
  match m.index[bv]? with
  | some j => (j, m)
  | none => (m.uniq.size, { uniq := m.uniq.push bv, index := m.index.insert bv m.uniq.size })

/-- The result of `epilogue`: the unique stack maps, the liveness map, and the names whose
`Needzero` it sets. -/
structure Epilogue where
  stackMaps : Array Bv
  map : LiveMap
  needzero : Array Nat

/-- `epilogue` with `compact` (plive.go:749-941). `flags n` are the `Dcl` flags of name `n`. -/
def epilogue (lv : Lv) (flags : Nat → Asm.NameFlags) (hasDefer openDeferDisallowed : Bool) :
    Except String Epilogue := do
  let env := lv.env
  let f := env.f
  let nvars := lv.vars.size
  let mut livedefer := Bv.new nvars
  let mut needzero : Array Nat := #[]
  if hasDefer then
    for i in [0:nvars] do
      let n := lv.vars[i]!
      let x ← env.name n
      let fl := flags n
      if x.cls == "PPARAMOUT" then
        if fl.outheapaddr then
          throw s!"variable n{n} both output param and heap output param"
        if fl.heapaddr then continue
        livedefer ← livedefer.set i
      let mut nz := fl.needzero
      if fl.outheapaddr then
        needzero := needzero.push n
        nz := true
        livedefer ← livedefer.set i
      if fl.opendeferslot then
        livedefer ← livedefer.set i
        if !nz then throw "all pointer-containing defer arg slots should have Needzero set"
  if f.blocks[0]? != some f.entry then throw "entry block must be first"
  let mut sms : BvecSet := {}
  let mut m : LiveMap := {}
  -- Reserve an entry for function entry.
  let mut livevars : Array Bv := #[Bv.new nvars]
  for bid in f.blocks do
    let b ← env.block bid
    let vals ← b.values.mapM env.value
    let hs ← vals.mapM lv.hasStackMap
    for h in hs do
      if h then livevars := livevars.push (Bv.new nvars)
    -- Walk backward, construct maps at each safe point.
    let mut index : Int := livevars.size - 1
    let mut liveout := lv.be[bid]!.liveout
    let mut i := vals.size
    while i > 0 do
      i := i - 1
      let v := vals[i]!
      if hs[i]! then
        let k := index.toNat
        livevars := livevars.set! k ((livevars[k]!.or liveout).or livedefer)
        index := index - 1
      let (pos, e) ← lv.valueEffects v
      if e &&& varkill != 0 then liveout ← liveout.unset pos.toNat
      if e &&& uevar != 0 then liveout ← liveout.setI pos
    if bid == f.entry then
      if index != 0 then throw s!"bad index for entry point: {index}"
      -- Check to make sure only input variables are live.
      for j in [0:nvars] do
        if !(← liveout.get j) then continue
        if (← env.name lv.vars[j]!).cls == "PPARAM" then continue
        throw s!"bad live variable at entry: n{lv.vars[j]!}"
      livevars := livevars.set! 0 (livevars[0]!.or liveout)
    -- compact
    let mut pos := 0
    if bid == f.entry then
      sms := (sms.add livevars[0]!).2
      pos := pos + 1
    for k in [0:vals.size] do
      let v := vals[k]!
      if hs[k]! then
        let (idx, s) := sms.add livevars[pos]!
        sms := s
        pos := pos + 1
        m := { m with vals := m.vals.insert v.id idx }
      let unsafeV ← if lv.allUnsafe then pure true
        else if v.op == .Clobber then pure false else lv.unsafePoints.get v.id
      if unsafeV then
        m := { m with unsafeVals := m.unsafeVals.insert v.id }
    if ← (if lv.allUnsafe then pure true else lv.unsafeBlocks.get bid) then
      m := { m with unsafeBlocks := m.unsafeBlocks.insert bid }
    livevars := #[]
  -- If we have an open-coded deferreturn call, make a liveness map for it.
  if openDeferDisallowed then
    m := { m with deferReturn := stackMapDontCare }
  else
    let (idx, s) := sms.add livedefer
    sms := s
    m := { m with deferReturn := idx }
  let stackMaps := sms.uniq
  for j in [0:nvars] do
    let n := lv.vars[j]!
    if (← env.name n).cls != "PPARAM" then
      if ← stackMaps[0]!.get j then
        throw s!"n{n} recorded as live on entry"
  return { stackMaps, map := m, needzero }

/-- `typebits.Set` (`check`) / `SetNoCheck` of the type of name `x` at `off`, from the pointer
mask of `typebits.Set(t, 0, ·)` (bit `i` = word `i`). -/
def typeBits (x : NameInfo) (off : Int) (bv : Bv) (check : Bool) : Except String Bv := do
  let a := (← x.align) % 256
  if check && a > 0 && off % a != 0 then
    throw s!"typebits.Set: invalid initial alignment: type {x.ty.str} has alignment {a}, but offset is {off}"
  if !(← x.hasPointers) then return bv
  if off % 8 != 0 then throw s!"typebits.Set: invalid alignment, {x.ty.str}"
  let mask := x.ty.ptrMask.getD .empty
  let nw := ((← x.ptrdata) / 8).toNat
  let base := off / 8
  let mut bv := bv
  for i in [0:nw] do
    if (mask.get! (i / 8) >>> (i % 8).toUInt8) &&& 1 != 0 then
      bv ← bv.setI (base + i)
  return bv

/-- `objw.Uint32` appended at the end (`off` = current size, always 4-aligned here). -/
def putU32 (b : ByteArray) (v : Int) : ByteArray :=
  let u := (v % 4294967296).toNat
  b.push (u % 256).toUInt8 |>.push (u / 256 % 256).toUInt8 |>.push (u / 65536 % 256).toUInt8
    |>.push (u / 16777216 % 256).toUInt8

/-- `objw.Uintptr` appended at the end. -/
def putU64 (b : ByteArray) (v : Nat) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8] do b := b.push (v / 2 ^ (8 * i) % 256).toUInt8
  return b

/-- `objw.BitVec`: the bitmap's bytes, little-endian. -/
def putBitVec (b : ByteArray) (bv : Bv) : ByteArray := Id.run do
  let mut b := b
  let mut j := 0
  while j < bv.n do
    b := b.push (bv.b[j / 32]! >>> (j % 32).toUInt32).toUInt8
    j := j + 8
  return b

/-- `checkStackmapOverflow` (plive.go:1600-1610). -/
def checkStackmapOverflow (bv : Bv) (count : Nat) : Except String Unit := do
  if bv.n == 0 || count == 0 then return
  let total := (bv.n + 7) / 8 * count
  if total > 2147483647 then
    throw s!"liveness stackmaps are too large: nbit={bv.n} count={count} totalBytes={total} exceeds MaxInt32"

/-- `base.Ctxt.GCLocalsSym(data)`: `gclocals·` and the standard base64 of the first 16 bytes of
`hash.Sum32(data)` (SHA-256 with byte 0 inverted); content-addressable, alignment 4. -/
def gcLocalsSym (data : ByteArray) : GenM Nat := do
  let sum := GoFV.Util.Sha256.sum256 data
  let sum := sum.set! 0 (sum.get! 0 ^^^ 0xff)
  let name := "gclocals·" ++ GoFV.Util.Sha256.base64Std (sum.extract 0 16)
  let k ← GenM.sym (GoStr.ofString name) 0
  unless (← get).symData.contains k do
    let o : SymOut := { kind := "Sxxx", size := 0, align := 4, attr := attrContentAddressable, data }
    modify fun s => { s with symData := s.symData.insert k o }
  return k

/-- `AFUNCDATA` with constant `kind` and the symbol `sym` (`Compute`). -/
def funcdata (kind : Int) (sym : Nat) : GenM Unit := do
  let p ← GenM.prog .FUNCDATA
  GenM.modP p fun x => { x with from_ := GenM.constAddr kind,
                                to := { x.to with type := .MEM, name := .EXTERN, sym := some sym } }

/-- `shouldTrack(n)` (plive.go:219-221). -/
def shouldTrack (x : NameInfo) : Except String Bool := do
  let c := x.cls
  if (c == "PAUTO" && x.d.esc != 2) || c == "PPARAM" || c == "PPARAMOUT" then x.hasPointers
  else return false

/-- `pointerMap` (plive.go:458-490): the args and locals bitmaps of one stack map. -/
def pointerMap (lv : Lv) (live : Bv) (args locals : Bv) : GenM (Bv × Bv) := do
  let check := (← GenM.lift (← GenM.env).mergeLocals) != 0
  let mut seen : Std.HashMap Int Nat := {}
  let mut args := args
  let mut locals := locals
  for i in live.toList do
    let n := lv.vars[i]!
    let x ← GenM.nameInfo n
    let off ← GenM.frameOffset n
    let c := x.cls
    if (c == "PPARAM" || c == "PPARAMOUT") && !(← GenM.outRegs n) then
      if off < 0 then throw s!"Node n{n} has frameoffset {off}"
      args ← GenM.lift (typeBits x off args false)
    else if c == "PAUTO" || c == "PPARAMOUT" then
      if check then
        if let some prev := seen[off]? then
          throw s!"two vars live at pointerMap generation: n{prev} and n{n}"
        seen := seen.insert off n
      locals ← GenM.lift (typeBits x (off + lv.stkptrsize) locals true)
  return (args, locals)

/-- `emit` (plive.go:1330-1388): the args and locals `gclocals·` symbols. -/
def emit (lv : Lv) (stackMaps : Array Bv) : GenM (Nat × Nat) := do
  let mut maxArg : Option (Nat × Int) := none
  for n in lv.vars do
    let x ← GenM.nameInfo n
    if (x.cls == "PPARAM" || x.cls == "PPARAMOUT") && !(← GenM.outRegs n) then
      let off ← GenM.frameOffset n
      match maxArg with
      | some (_, o) => if off > o then maxArg := some (n, off)
      | none => maxArg := some (n, off)
  let mut maxArgs : Int := 0
  if let some (n, off) := maxArg then
    maxArgs := off + (← GenM.lift (← GenM.nameInfo n).ptrdata)
  let maxLocals := lv.stkptrsize
  if maxArgs < 0 || maxLocals < 0 then throw "liveness: negative bitmap size"
  let args0 := Bv.new (maxArgs / 8).toNat
  let locals0 := Bv.new (maxLocals / 8).toNat
  let mut a := putU32 (putU32 .empty stackMaps.size) args0.n
  let mut l := putU32 (putU32 .empty stackMaps.size) locals0.n
  GenM.lift (checkStackmapOverflow args0 stackMaps.size)
  GenM.lift (checkStackmapOverflow locals0 stackMaps.size)
  for live in stackMaps do
    let (args, locals) ← pointerMap lv live args0 locals0
    a := putBitVec a args
    l := putBitVec l locals
  return (← gcLocalsSym a, ← gcLocalsSym l)

/-- `reflectdata.GCSym(t, false)`'s symbol: `runtime.gcbits.<hex mask>`, the pointer mask
padded to a multiple of the pointer size (`dgcptrmask`). -/
def gcSymName (x : NameInfo) : Except String String := do
  let nptr := ((← x.ptrdata) / 8).toNat
  let n := ((nptr + 7) / 8 + 7) / 8 * 8
  let mask := x.ty.ptrMask.getD .empty
  let mut bytes := ByteArray.mk (Array.replicate n 0)
  if ← x.hasPointers then
    for i in [0:nptr] do
      if (mask.get! (i / 8) >>> (i % 8).toUInt8) &&& 1 != 0 then
        bytes := bytes.set! (i / 8) (bytes.get! (i / 8) ||| ((1 : UInt8) <<< (i % 8).toUInt8))
  return "runtime.gcbits." ++ GoFV.Util.Sha256.hex bytes

/-- `emitStackObjects` (plive.go:1463-1515). -/
def emitStackObjects (flags : Nat → Asm.NameFlags) : GenM (Option Nat) := do
  let env ← GenM.env
  let mut objs : Array (Nat × Int) := #[]
  for d in (← get).dcl do
    let x ← GenM.nameInfo d.name
    if (← GenM.lift (shouldTrack x)) && (flags d.name).addrtaken && x.d.esc != 2 then
      objs := objs.push (d.name, ← GenM.frameOffset d.name)
  if objs.isEmpty then return none
  -- Sort variables from lowest to highest address.
  let vars := GoFV.Util.PdqSort.sortFunc
    (fun a b => if a.2 < b.2 then -1 else if a.2 > b.2 then 1 else 0) objs
  let some (fnName, _) := env.inSyms[env.genin.text.sym]?
    | throw s!"liveness: no text symbol y{env.genin.text.sym}"
  let x ← GenM.sym (fnName ++ GoStr.ofString ".stkobj") 0
  let mut data := putU64 .empty vars.size
  let mut relocs : Array RelocOut := #[]
  for (n, off) in vars do
    if off < -2147483648 || off > 2147483647 then throw s!"frame offset too big: n{n} {off}"
    data := putU32 data off
    let xi ← GenM.nameInfo n
    let sz ← GenM.lift xi.size
    if sz > 2147483647 then throw s!"stack object too big: n{n} of type {xi.ty.str}, size {sz}"
    let g ← GenM.sym (GoStr.ofString (← GenM.lift (gcSymName xi))) 0
    data := putU32 data sz
    data := putU32 data (← GenM.lift xi.ptrdata)
    relocs := relocs.push { off := data.size, siz := 4, type := "R_ADDROFF", add := 0, sym := some g }
    data := putU32 data 0
  let o : SymOut :=
    { kind := "SDATA", size := data.size, align := 8, attr := attrContentAddressable, data, relocs }
  modify fun s => { s with symData := s.symData.insert x o,
                           aux := { s.aux with stackObjects := some x } }
  return some x

/-- B1: `liveness.Compute` (plive.go:1395-1461): sets `GenState.live` (with `partLiveArgs`)
and the `Needzero` flags of `Dcl`, emits FUNCDATA 0, 1 (and 2) and writes the `gclocals·` and
`.stkobj` symbols. -/
def compute : GenM Unit := do
  let env ← GenM.env
  let fr := (← read).frame
  let dcl := (← get).dcl
  let mut fm : Std.HashMap Nat Asm.NameFlags := {}
  for d in fr.optDcl do fm := fm.insert d.name d.flags
  for d in dcl do fm := fm.insert d.name d.flags
  let fl := fm
  let flags : Nat → Asm.NameFlags := fun n => fl.getD n {}
  -- getvariables
  let mut vars : Array Nat := #[]
  for d in dcl do
    if ← GenM.lift (shouldTrack (← GenM.nameInfo d.name)) then vars := vars.push d.name
  let mut idx : Std.HashMap Nat Nat := {}
  for i in [0:vars.size] do idx := idx.insert vars[i]! i
  let lv ← GenM.lift do
    let lv ← newliveness env vars idx fr.stkptrsize (fun n => (flags n).used)
    let lv ← lv.prologue
    lv.solve
  let ep ← GenM.lift (epilogue lv flags env.genin.hasDefer env.genin.openDeferDisallowed)
  modify fun s => { s with
    dcl := s.dcl.map fun d =>
      if ep.needzero.contains d.name then { d with flags := { d.flags with needzero := true } }
      else d,
    live := { ep.map with partLiveArgs := lv.partLiveArgs } }
  let (gcArgs, gcLocals) ← emit lv ep.stackMaps
  modify fun s => { s with aux := { s.aux with gcArgs := some gcArgs, gcLocals := some gcLocals } }
  funcdata Abi.FUNCDATA_ArgsPointerMaps gcArgs
  funcdata Abi.FUNCDATA_LocalsPointerMaps gcLocals
  -- The Needzero updates only touch PAUTOs, which emitStackObjects reads through `flags`'s
  -- addrtaken bit only.
  if let some x ← emitStackObjects flags then
    funcdata Abi.FUNCDATA_StackObjects x

end GoFV.Gen.Liveness
