import GoFV.Gen.Meta
import GoFV.SSA.Analysis.CfgCache

/-!
# Register argument spill slot liveness (B2)

Port of `liveness.ArgLiveness` (`liveness/arg.go`, all of it but the debug printer; go1.27.3
pin 2aae1000ea1d; `docs/PASSES3.md` B2) with the `bvecSet` it coalesces with
(`liveness/bvset.go`) and `objw.Uint8`/`objw.BitVec` (`objw/objw.go:17-19,93-101`).

The spill slots of the register-assigned input parameters of `f.OwnAux.ABIInfo()` (one per
register piece, `RegisterTypesAndOffsets`) with frame offset at most 255, the first 10, minus
the leading always-live ones (address-taken or not `ssa.CanSSA`), are tracked by a single
reverse-postorder pass (a slot is live at block entry iff live at the end of every
predecessor; `StoreReg` to the slot sets it). The live sets at each block entry and, after a
run of changes, at the next value that may fault or the block's last value, are coalesced (all
live: index −1) into `<fn>.argliveinfo` (ABI0, `ContentAddressable`, `Align` 1: the smallest
tracked offset, then each distinct bitmap in first-insertion order) and returned as byte
offsets into it; `FUNCDATA_ArgLiveInfo` points at the symbol.

Bit vectors (at most 10 bits) are natural-number masks: `bvecSet.add` returns the index of the
first equal vector in insertion order, so its hash table does not affect the result. Names are
identified by their `.ssa` aux number (equal iff the same `*ir.Name`).
-/

namespace GoFV.Gen

open GoFV.SSA
open GoFV.Asm
open ArgMeta

namespace ArgLive

/-- `allLiveIdx`. -/
def allLiveIdx : Int := -1

/-- The `*ir.Name` of an aux: class, type, `FrameOffset()`, `Addrtaken()`. -/
structure NameFacts where
  cls : NameClass
  type : TypeRef
  frameOffset : Int
  addrtaken : Bool

def nameFacts (env : Env) (a : AuxRef) : Except String NameFacts := do
  match (← env.auxDef a).kind with
  | .name _ cls t off _ flags _ =>
    pure { cls, type := t, frameOffset := off, addrtaken := flags.addrtaken }
  | _ => throw s!"aux a{a} is not an *ir.Name"

/-- `mayFault(v)`. -/
def mayFault (v : Value) : Bool :=
  match v.op with
  | .LoadReg | .StoreReg | .Copy | .Phi | .VarDef | .VarLive | .KeepAlive | .Select0 | .Select1
  | .SelectN | .MakeResult | .Convert | .InlMark | .GetG => false
  | _ => !v.args.isEmpty

/-- `bv.Count()`. -/
def popCount (m : Nat) : Nat := Id.run do
  let mut m := m
  let mut c := 0
  while m != 0 do
    c := c + m % 2
    m := m / 2
  return c

end ArgLive

open ArgLive

/-- `liveness.ArgLiveness(fn, f, pp)` (`liveness/arg.go:80`): the liveness map indices (byte
offsets into `<fn>.argliveinfo`, or −1 for all live) at each block entry and at the values where
they change; empty maps (Go: nil) without register arguments, with `-N`, or when every tracked
slot is always live. -/
def argLiveness : GenM (Std.HashMap ID Int × Std.HashMap ID Int) := do
  let env ← GenM.env
  let f := env.f
  let abi ← GenM.lift (ownABI env)
  if abi.inRegs == 0 || (← GenM.lift env.flagN) != 0 then return ({}, {})
  let ps ← GenM.lift (ptrSize env)
  -- Gather all register arg spill slots.
  let mut args : Array (AuxRef × Int) := #[]
  for a in abi.inParams do
    let some n := a.name | continue
    if a.regs.isEmpty then continue
    let nf ← GenM.lift (nameFacts env n)
    for off in ← GenM.lift (registerOffsets env.tabs a) do
      if nf.frameOffset + off > 0xff then continue
      args := args.push (n, off)
  if args.size > 10 then args := args.extract 0 10
  let alwaysLive (n : AuxRef) : Except String Bool := do
    let nf ← nameFacts env n
    return nf.addrtaken || !(← canSSA env.tabs ps typeFuel nf.type)
  -- Drop the leading always-live slots.
  let mut lead := 0
  while h : lead < args.size do
    if !(← GenM.lift (alwaysLive args[lead].1)) then break
    lead := lead + 1
  args := args.extract lead args.size
  if args.isEmpty then return ({}, {})
  let mut idx : Std.HashMap (AuxRef × Int) Nat := {}
  for h : i in [0:args.size] do
    idx := idx.insert args[i] i
  let nargs := args.size
  let allOnes := 2 ^ nargs - 1
  -- valueEffect: applies v to live; `none` if unchanged.
  let valueEffect (v : Value) (live : Nat) : Except String (Option Nat) := do
    if v.op != .StoreReg then return none
    let (n, off) ← match env.loc? v.id with
      | some (.slot k) => pure (k.name, k.off)
      | l => throw s!"v{v.id}: AutoVar of {repr l}"
    if (← nameFacts env n).cls != .PPARAM then return none
    match idx[(n, off)]? with
    | none => return none
    | some i =>
      if live.testBit i then return none
      return some (live ||| (1 <<< i))
  let applyBlock (b : Block) (live : Nat) : Except String Nat :=
    b.values.foldlM (init := live) fun live id => do
      let v ← env.value id
      return (← valueEffect v live).getD live
  -- Block effects: livein/liveout by block ID, all 1s so they can be ANDed.
  let mut livein : Std.HashMap ID Nat := {}
  let mut liveout : Std.HashMap ID Nat := {}
  for b in f.blocks do
    livein := livein.insert b allOnes
    liveout := liveout.insert b allOnes
  let mut entryIn := 0
  for h : i in [0:nargs] do
    if ← GenM.lift (alwaysLive args[i].1) then entryIn := entryIn ||| (1 <<< i)
  livein := livein.insert f.entry entryIn
  -- Visit blocks in reverse postorder.
  let po := (Func.postorder f).1
  for i in [0:po.size] do
    let bid := po[po.size - 1 - i]!
    let b ← GenM.lift (env.block bid)
    let mut lin := livein.getD bid 0
    for e in b.preds do
      lin := lin &&& liveout.getD e.b 0
    livein := livein.insert bid lin
    liveout := liveout.insert bid (← GenM.lift (applyBlock b lin))
  -- Coalesce identical live vectors; liveness indices where they change.
  let mut uniq : Array Nat := #[]
  let mut blockIdx : Std.HashMap ID Int := {}
  let mut valueIdx : Std.HashMap ID Int := {}
  for bid in f.blocks do
    let b ← GenM.lift (env.block bid)
    let lin := livein.getD bid 0
    let addToSet (u : Array Nat) (bv : Nat) : Int × Array Nat :=
      if popCount bv == nargs then (allLiveIdx, u)
      else match u.idxOf? bv with
        | some j => (j, u)
        | none => (u.size, u.push bv)
    let (k, u) := addToSet uniq lin
    uniq := u
    blockIdx := blockIdx.insert bid k
    let mut live := lin
    let mut lastv : Option ID := none
    for h : i in [0:b.values.size] do
      let v ← GenM.lift (env.value b.values[i])
      if let some l ← GenM.lift (valueEffect v live) then
        live := l
        lastv := some v.id
      if let some lv := lastv then
        if mayFault v || i == b.values.size - 1 then
          let (k, u) := addToSet uniq live
          uniq := u
          valueIdx := valueIdx.insert lv k
          lastv := none
    if live != liveout.getD bid 0 then throw "wrong arg liveness map at block end"
  -- emit: the symbol, indices to offsets.
  let mut argOffsets : Array Nat := #[]
  for (n, off) in args do
    let o := (← GenM.lift (nameFacts env n)).frameOffset + off
    if o > 0xff then throw "offset too large"
    argOffsets := argOffsets.push (o % 256).toNat
  let (fname, _) ← GenM.lift (textSym env)
  let lsym ← GenM.sym (fname ++ GoStr.ofString ".argliveinfo") 0
  let mut data : ByteArray := ByteArray.empty.push argOffsets[0]!.toUInt8
  let mut idx2off : Array Int := #[]
  for bv in uniq do
    idx2off := idx2off.push data.size
    let mut j := 0
    while j < nargs do
      data := data.push ((bv >>> j) % 256).toUInt8
      j := j + 8
  writeSym lsym { kind := "SDATA", size := data.size, align := 1,
                  attr := attrContentAddressable, data }
  let toOff (x : Int) : Int := if x == allLiveIdx then x else idx2off[x.toNat]!
  blockIdx := blockIdx.fold (init := {}) fun m k x => m.insert k (toOff x)
  valueIdx := valueIdx.fold (init := {}) fun m k x => m.insert k (toOff x)
  modify fun s => { s with aux := { s.aux with argLiveInfo := some lsym } }
  funcdata Abi.FUNCDATA_ArgLiveInfo lsym
  return (blockIdx, valueIdx)

end GoFV.Gen
