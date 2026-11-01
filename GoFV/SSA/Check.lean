import GoFV.SSA.Export
import GoFV.SSA.TypePred
import GoFV.SSA.Analysis.Postorder
import GoFV.SSA.Analysis.Dom
import GoFV.SSA.Analysis.LoopNest
import GoFV.SSA.DomCert
import GoFV.SSA.Sem.Layout

/-!
# `GoFV.SSA.check`: well-formedness checker (port of `ssa/check.go`, issue #8)

`check env f` performs the checks of Go's `checkFunc` (with `memCheck`) in the same order and
reports the first failure with Go's message (IDs in Go's `v<ID>`/`b<ID>` notation). The state
is that of the machine-independent passes: `f.RegAlloc == nil`, `f.scheduled == false`,
`f.pass != nil`, `Config.SoftFloat == false`, so the regalloc-, schedule- and soft-float-only
checks are skipped exactly as Go skips them.

Inputs beyond the `Func`: the definition tables (types, aux values) and the `Config.Types` of
the export (`typs`; `SP`/`SB` must be typed `Uintptr`, `StringLen` `Int`). Postorder, dominator
tree and loop nest are recomputed from the CFG (`GoFV.SSA.Analysis.{Postorder,Dom,SparseTree,
LoopNest}`), never read from the possibly stale `f.cache`.

Which of these facts the pass proofs need: `docs/contracts/check.md`.
-/

namespace GoFV.SSA

/-- The type a `typs` entry names. -/
def typsLookup (typs : Array (String × TypeRef)) (name : String) : Option TypeRef :=
  (typs.find? (·.1 == name)).map (·.2)

/-- What the checker reads besides the `Func`: the tables and the `Config.Types` / SSA
pseudo-types of the export (`typs` line of section 0); the types the checks compare against
are looked up once. `firstAny` relaxes Go's checks for validators' intermediate functions: a
`First` block may have any positive number of successors (sccp's intermediate turns a
`JumpTable` on a constant into a `First` block; no proof uses the successor counts). -/
structure CheckEnv where
  tabs : Tables
  typs : Array (String × TypeRef)
  mem : Option TypeRef := typsLookup typs "Mem"
  uintptr : Option TypeRef := typsLookup typs "Uintptr"
  int : Option TypeRef := typsLookup typs "Int"
  void : Option TypeRef := typsLookup typs "Void"
  firstAny : Bool := false

namespace CheckEnv

/-- `t.IsMemory()`: `mem`, a tuple whose second component is `mem`, a results type whose last
component is `mem`. -/
def isMemory (e : CheckEnv) (t : TypeRef) : Bool :=
  match e.mem with
  | some mem => e.tabs.isMemory mem t
  | none => false

def kind? (e : CheckEnv) (t : TypeRef) : Option TypeKind := (e.tabs.type? t).map (·.kind)

def isBoolean (e : CheckEnv) (t : TypeRef) : Bool := e.kind? t == some .BOOL
def isTuple (e : CheckEnv) (t : TypeRef) : Bool := e.kind? t == some .TUPLE
def isUintptr (e : CheckEnv) (t : TypeRef) : Bool := e.kind? t == some .UINTPTR
def isVoid (e : CheckEnv) (t : TypeRef) : Bool := e.void == some t

/-- `t.IsInteger()` (the untyped constant types never reach SSA). -/
def isInteger (e : CheckEnv) (t : TypeRef) : Bool :=
  match e.kind? t with
  | some k => [TypeKind.INT8, .UINT8, .INT16, .UINT16, .INT32, .UINT32, .INT64, .UINT64, .INT,
      .UINT, .UINTPTR].contains k
  | none => false

/-- `t.IsPtrShaped()`. -/
def isPtrShaped (e : CheckEnv) (t : TypeRef) : Bool :=
  match e.kind? t with
  | some k => [TypeKind.PTR, .UNSAFEPTR, .MAP, .CHAN, .FUNC].contains k
  | none => false

/-- `t.Size()` (`none` when the export has `?`). -/
def size? (e : CheckEnv) (t : TypeRef) : Option Int := (e.tabs.type? t).bind (·.size)

/-- First component type of a tuple. -/
def tupleFirst? (e : CheckEnv) (t : TypeRef) : Option TypeRef :=
  match e.tabs.type? t with
  | some { tail := .tuple a _, .. } => some a
  | _ => none

end CheckEnv

namespace Check

/-- Go's `isExactFloat32` on the bits of a float64: the value is a finite float32 value (or
±0, ±∞, NaN). -/
def isExactFloat32 (bits : UInt64) : Bool :=
  let mant : Nat := bits.toNat % 2 ^ 52
  let ex : Nat := (bits.toNat / 2 ^ 52) % 2048
  -- trailing zeros of the whole bit pattern ≥ 29 (Go's first test)
  if bits.toNat % 2 ^ 29 != 0 then false
  else if ex == 2047 then true                       -- ±∞ (NaN is rejected before)
  else if ex == 0 then mant == 0                     -- ±0; float64 subnormals are not float32
  else
    -- x = (2^52 + mant) · 2^(ex − 1075); exact iff it rounds to itself as a float32:
    -- unbiased exponent within the float32 range, subnormal float32 values included
    let e : Int := (ex : Int) - 1023
    if e > 127 then false
    else if e ≥ -126 then true
    else
      -- float32 subnormal: the value must be a multiple of 2^-149
      let sig : Nat := 2 ^ 52 + mant
      let shift := (-149 : Int) - (e - 52)          -- bits below 2^-149
      shift ≤ 0 || (shift ≤ 53 && sig % 2 ^ shift.toNat == 0)

/-- `math.IsNaN(math.Float64frombits(bits))`. -/
def isNaN64 (bits : UInt64) : Bool :=
  (bits.toNat / 2 ^ 52) % 2048 == 2047 && bits.toNat % 2 ^ 52 != 0

/-- Go's `checkFunc` op-size table: the size of every argument of `op`, if listed. -/
def argSize : Op → Option Int
  | .Add8 | .Sub8 | .Mul8 | .Div8 | .Div8u | .Mod8 | .Mod8u | .And8 | .Or8 | .Xor8
  | .Eq8 | .Neq8 | .Less8 | .Leq8 | .Neg8 | .Com8
  | .SignExt8to16 | .SignExt8to32 | .SignExt8to64
  | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64 => some 1
  | .Add16 | .Sub16 | .Mul16 | .Div16 | .Div16u | .Mod16 | .Mod16u | .And16 | .Or16 | .Xor16
  | .Eq16 | .Neq16 | .Less16 | .Leq16 | .Neg16 | .Com16
  | .SignExt16to32 | .SignExt16to64 | .ZeroExt16to32 | .ZeroExt16to64 | .Trunc16to8 => some 2
  | .Add32 | .Sub32 | .Mul32 | .Div32 | .Div32u | .Mod32 | .Mod32u | .And32 | .Or32 | .Xor32
  | .Eq32 | .Neq32 | .Less32 | .Leq32 | .Neg32 | .Com32
  | .SignExt32to64 | .ZeroExt32to64 | .Trunc32to8 | .Trunc32to16 => some 4
  | .Add64 | .Sub64 | .Mul64 | .Div64 | .Div64u | .Mod64 | .Mod64u | .And64 | .Or64 | .Xor64
  | .Eq64 | .Neq64 | .Less64 | .Leq64 | .Neg64 | .Com64
  | .Trunc64to8 | .Trunc64to16 | .Trunc64to32 => some 8
  | _ => none

/-- `IsMergeCandidate(n)` (`func.go`, `base.Debug.MergeLocals = 1`, optimizing). -/
def isMergeCandidate (e : CheckEnv) (n : AuxRef) : Bool :=
  match e.tabs.aux? n with
  | some { kind := .name _ cls t _ _ fl _, .. } =>
    cls == .PAUTO && (match e.size? t with | some s => s > 24 | none => false) &&
      !fl.addrtaken && !fl.nonmergeable && !fl.opendeferslot
  | _ => false

/-- `n.Type().HasPointers()` of an `*ir.Name` aux. -/
def nameHasPointers (e : CheckEnv) (n : AuxRef) : Bool :=
  match e.tabs.aux? n with
  | some { kind := .name _ _ t _ _ _ _, .. } =>
    match e.tabs.type? t with
    | some d => d.flags.hasptr
    | none => false
  | _ => false

/-- The aux kind of `a` (`none`: nil aux). -/
def auxKind? (e : CheckEnv) (a : Option AuxRef) : Option AuxKind :=
  a.bind fun a => (e.tabs.aux? a).map (·.kind)

/-- The per-op aux/auxint checks (`switch opcodeTable[v.Op].auxType`). -/
def checkAux (e : CheckEnv) (v : Value) : Except String Unit := do
  let ai := v.auxInt.toInt
  let inRange (lo hi : Int) := lo ≤ ai && ai ≤ hi
  let (canAux, canAuxInt) ← match v.op.auxType with
    | .None => pure (false, false)
    | .Bool =>
      if !inRange 0 1 then throw s!"bad bool AuxInt value for v{v.id}"
      pure (false, true)
    | .Int8 | .UInt8 =>
      if !inRange (-128) 127 then throw s!"bad int8 AuxInt value for v{v.id}"
      pure (false, true)
    | .Int16 =>
      if !inRange (-32768) 32767 then throw s!"bad int16 AuxInt value for v{v.id}"
      pure (false, true)
    | .Int32 =>
      if !inRange (-2147483648) 2147483647 then throw s!"bad int32 AuxInt value for v{v.id}"
      pure (false, true)
    | .Int64 | .ARM64BitField | .ARM64ConditionalParams => pure (false, true)
    | .Int128 => pure (false, false)
    | .Float32 =>
      if isNaN64 v.auxInt.toUInt64 then throw s!"value v{v.id} has an AuxInt that encodes a NaN"
      if !isExactFloat32 v.auxInt.toUInt64 then
        throw s!"value v{v.id} has an AuxInt value that is not an exact float32"
      pure (false, true)
    | .Float64 =>
      if isNaN64 v.auxInt.toUInt64 then throw s!"value v{v.id} has an AuxInt that encodes a NaN"
      pure (false, true)
    | .String =>
      match auxKind? e v.aux with
      | some (.str ..) => pure (true, false)
      | _ => throw s!"value v{v.id} has Aux type {v.aux}, want string"
    | .Call | .CallOff =>
      match auxKind? e v.aux with
      | some (.call fn _) =>
        if v.op == .StaticCall && fn.isNone then throw s!"value v{v.id} has *AuxCall with nil Fn"
        pure (true, v.op.auxType == .CallOff)
      | _ => throw s!"value v{v.id} has Aux type {v.aux}, want *AuxCall"
    | .NameOffsetInt8 =>
      match auxKind? e v.aux with
      | some (.nameOff ..) => pure (true, true)
      | _ => throw s!"value v{v.id} has Aux type {v.aux}, want *AuxNameOffset"
    | .Sym | .Typ => pure (true, false)
    | .SymOff | .SymValAndOff | .TypSize => pure (true, true)
    | .FlagConstant =>
      if !inRange 0 15 then throw s!"bad FlagConstant AuxInt value for v{v.id}"
      pure (false, true)
    | .PanicBoundsC | .PanicBoundsCC => pure (true, true)
    | .SizeAndAlign =>
      match auxKind? e v.aux with
      | some (.int _) => pure (true, true)
      | _ => throw s!"value v{v.id} has Aux type {v.aux}, want int64Aux"
    | t => throw s!"unknown aux type {repr t} for {v.op.name}"
  if !canAux && v.aux.isSome then
    throw s!"value v{v.id} has an Aux value {v.aux} but shouldn't"
  if !canAuxInt && v.auxInt != 0 then
    throw s!"value v{v.id} has an AuxInt value {v.auxInt.toInt} but shouldn't"

/-- The type of value `a` (missing values are reported later, as Go does). -/
@[inline] def typeOf? (f : Func) (a : ID) : Option TypeRef := (f.value? a).map (·.type)

/-- The per-op type checks (`switch c := f.Config; v.Op`). -/
def checkTypes (e : CheckEnv) (f : Func) (v : Value) : Except String Unit := do
  let argT (i : Nat) : Option TypeRef := (v.args[i]?).bind (typeOf? f)
  let isMemArg (i : Nat) := (argT i).any e.isMemory
  match v.op with
  | .SP | .SB =>
    if e.uintptr != some v.type then
      throw s!"bad {v.op.name} type: want uintptr, have t{v.type}"
  | .StringLen =>
    if e.int != some v.type then
      throw s!"bad {v.op.name} type: want int, have t{v.type}"
  | .Load =>
    if !isMemArg 1 then throw s!"bad arg 1 type to {v.op.name}: want mem"
  | .Store =>
    if !e.isMemory v.type then throw s!"bad {v.op.name} type: want mem, have t{v.type}"
    if !isMemArg 2 then throw s!"bad arg 2 type to {v.op.name}: want mem"
  | .CondSelect =>
    if !(argT 2).any e.isBoolean then throw s!"bad arg 2 type to {v.op.name}: want boolean"
  | .AddPtr =>
    if !(argT 0).any (fun t => e.isPtrShaped t || e.uintptr == some t) then
      throw s!"bad arg 0 type to {v.op.name}: want ptr"
    if !(argT 1).any e.isInteger then throw s!"bad arg 1 type to {v.op.name}: want integer"
  | .VarDef =>
    match v.aux with
    | some n =>
      if !nameHasPointers e n && !isMergeCandidate e n then
        throw s!"vardef must be merge candidate or have pointer type (v{v.id})"
    | none => throw s!"v{v.id}: VarDef without *ir.Name"
  | .NilCheck =>
    if !e.isPtrShaped v.type && !e.isUintptr v.type then
      throw s!"nilcheck must have pointer type t{v.type}"
    if !(argT 0).any (fun t => e.isPtrShaped t || e.isUintptr t) then
      throw s!"nilcheck must have argument of pointer type (v{v.id})"
    if !isMemArg 1 then throw s!"bad arg 1 type to {v.op.name}: want mem"
  | _ => pure ()
  if let some sz := argSize v.op then
    for h : i in [0:v.args.size] do
      if let some t := typeOf? f v.args[i] then
        if e.size? t != some sz then
          throw s!"arg {i} to {v.op.name} (v{v.id}) should be {sz} bytes in size, it is t{t}"

/-- The checks of one value inside the block loop. -/
def checkValue (e : CheckEnv) (f : Func) (b : Block) (v : Value) : Except String Unit := do
  let n := v.op.argLen
  if n != -1 && (v.args.size : Int) != n then
    throw s!"value v{v.id} has {v.args.size} args, expected {n}"
  checkAux e v
  if v.op != .Phi then
    for h : i in [0:v.args.size] do
      if (typeOf? f v.args[i]).any e.isMemory && i != v.args.size - 1 then
        throw s!"value v{v.id} has non-final memory arg ({i} < {v.args.size - 1})"
  if v.block != b.id then throw s!"v{v.id}.block != b{b.id}"
  if v.op == .Phi && v.args.size != b.preds.size then
    throw s!"phi length v{v.id} does not match pred length {b.preds.size} for block b{b.id}"
  if v.op == .Addr then
    match v.args[0]?.bind f.value? with
    | some a => if a.op != .SB then throw s!"bad arg to OpAddr v{v.id}"
    | none => if v.args.isEmpty then throw s!"no args for OpAddr v{v.id}"
  if v.op == .LocalAddr then
    if v.args.size != 2 then throw s!"wrong # of args for OpLocalAddr v{v.id}"
    if !((v.args[0]?.bind f.value?).any (·.op == .SP)) then
      throw s!"bad arg 0 to OpLocalAddr v{v.id}"
    if !((v.args[1]?.bind (typeOf? f)).any e.isMemory) then
      throw s!"bad arg 1 to OpLocalAddr v{v.id}"
  if (v.op == .StructMake || v.op == .ArrayMake1) && e.size? v.type == some 0 then
    throw s!"zero-sized Make; use Empty instead v{v.id}"
  checkTypes e f v

/-- The block-kind checks (`switch b.Kind`). -/
def checkKind (e : CheckEnv) (f : Func) (b : Block) : Except String Unit := do
  let ctlT : Option TypeRef := (b.controls[0]?).bind (typeOf? f)
  let memCtl := ctlT.any e.isMemory
  match b.kind with
  | .Exit | .Ret | .RetJmp | .Defer =>
    let name := match b.kind with
      | .Exit => "exit" | .Ret => "ret" | .RetJmp => "retjmp" | _ => "defer"
    let want := if b.kind == .Defer then 2 else 0
    if b.succs.size != want then
      throw s!"{name} block b{b.id} len(Succs)=={b.succs.size}, want {want}"
    if b.controls.size != 1 then throw s!"{name} block b{b.id} has no control value"
    if !memCtl then throw s!"{name} block b{b.id} has non-memory control value"
  | .Plain =>
    if b.succs.size != 1 then throw s!"plain block b{b.id} len(Succs)=={b.succs.size}, want 1"
    if b.controls.size != 0 then throw s!"plain block b{b.id} has non-nil control"
  | .If =>
    if b.succs.size != 2 then throw s!"if block b{b.id} len(Succs)=={b.succs.size}, want 2"
    if b.controls.size != 1 then throw s!"if block b{b.id} has no control value"
    if !ctlT.any e.isBoolean then throw s!"if block b{b.id} has non-bool control value"
  | .First =>
    if (if e.firstAny then b.succs.isEmpty else b.succs.size != 2) then
      throw s!"plain/dead block b{b.id} len(Succs)=={b.succs.size}, want 2"
    if b.controls.size != 0 then throw s!"plain/dead block b{b.id} has a control value"
  | .JumpTable =>
    if b.controls.size != 1 then throw s!"jumpTable block b{b.id} has no control value"
  | .Invalid => pure ()
  if b.succs.size != 2 && b.likely != .unknown then
    throw s!"likeliness prediction {b.likely.toInt} for block b{b.id} with {b.succs.size} successors"

/-- `memCheck(f)`. -/
def memCheck (e : CheckEnv) (f : Func) : Except String Unit := do
  let blocks := f.blocks.filterMap f.block?
  let values (b : Block) : Array Value := b.values.filterMap f.value?
  for b in blocks do
    for v in values b do
      if e.isTuple v.type && (e.tupleFirst? v.type).any e.isMemory then
        throw s!"memory is first in a tuple: v{v.id}"
  -- single live memory checks only without memory copies, unused memory values, or
  -- unreachable-by-preds blocks
  for b in blocks do
    for v in values b do
      if (v.op == .Copy || v.uses == 0) && e.isMemory v.type then return
    if b.id != f.entry && b.preds.isEmpty then return
  let memoryArg (v : Value) : Option ID :=
    match v.args.back? with
    | some m => if (typeOf? f m).any e.isMemory then some m else none
    | none => none
  let mut lastmem : Array (Option ID) := Array.replicate f.blockTab.size none
  for b in blocks do
    let vs := values b
    -- by value ID (an array, not a hash set: the kernel can evaluate `check`)
    let mut overwritten : Array Bool := Array.replicate f.valueTab.size false
    for v in vs do
      if v.op == .Phi || !e.isMemory v.type then continue
      if let some m := memoryArg v then overwritten := overwritten.set! m true
    for v in vs do
      if !e.isMemory v.type || overwritten.getD v.id false then continue
      if let some l := lastmem[b.id]! then
        throw s!"two live memory values in b{b.id}: v{l} and v{v.id}"
      lastmem := lastmem.set! b.id (some v.id)
    if lastmem[b.id]!.isNone then
      for v in vs do
        if v.op == .Phi then continue
        let some m := memoryArg v | continue
        if let some l := lastmem[b.id]! then
          if l != m then throw s!"two live memory values in b{b.id}: v{l} and v{m}"
        lastmem := lastmem.set! b.id (some m)
  -- propagate through storeless blocks
  for _ in [0:blocks.size + 1] do
    let mut changed := false
    for b in blocks do
      if lastmem[b.id]!.isSome then continue
      for p in b.preds do
        if let some m := lastmem[p.b]?.join then
          lastmem := lastmem.set! b.id (some m)
          changed := true
          break
    if !changed then break
  for b in blocks do
    for v in values b do
      if v.op == .Phi && e.isMemory v.type then
        for h : i in [0:v.args.size] do
          let want := (b.preds[i]?).bind fun p => lastmem[p.b]?.join
          if want != some v.args[i] then
            throw s!"inconsistent memory phi v{v.id} {i} v{v.args[i]} {want.map (s!"v{·}")}"

end Check

open Check in
/-- `checkFunc(f)` (`check.go`): `ok ()` iff every check passes, else Go's first failure. -/
def checkGo (e : CheckEnv) (f : Func) : Except String Unit := do
  let nb := f.blockTab.size
  let nv := f.valueTab.size
  let mut blockMark : Array Bool := Array.replicate nb false
  let mut valueMark : Array Bool := Array.replicate nv false
  for bid in f.blocks do
    let some b := f.block? bid | throw s!"block b{bid} of f.Blocks is not in the block table"
    if b.id != bid then throw s!"block table entry b{bid} has ID {b.id}"
    if blockMark[bid]! then throw s!"block b{bid} appears twice"
    blockMark := blockMark.set! bid true
    for h : i in [0:b.preds.size] do
      let e := b.preds[i]
      match (f.block? e.b).bind (·.succs[e.i]?) with
      | some se =>
        if se.b != bid || se.i != i then
          throw s!"block pred/succ not crosslinked correctly {i}:b{bid} {se.i}:b{se.b}"
      | none => throw s!"block pred/succ not crosslinked correctly {i}:b{bid} (b{e.b}.Succs[{e.i}] missing)"
    for h : i in [0:b.succs.size] do
      let e := b.succs[i]
      match (f.block? e.b).bind (·.preds[e.i]?) with
      | some pe =>
        if pe.b != bid || pe.i != i then
          throw s!"block succ/pred not crosslinked correctly {i}:b{bid} {pe.i}:b{pe.b}"
      | none => throw s!"block succ/pred not crosslinked correctly {i}:b{bid} (b{e.b}.Preds[{e.i}] missing)"
    checkKind e f b
    for vid in b.values do
      let some v := f.value? vid | throw s!"value v{vid} of b{bid} is not in the value table"
      if v.id != vid then throw s!"value table entry v{vid} has ID {v.id}"
      checkValue e f b v
      if valueMark[vid]! then throw s!"value v{vid} appears twice!"
      valueMark := valueMark.set! vid true
  if !(blockMark[f.entry]?.getD false) then throw s!"entry block b{f.entry} is missing"
  let blocks := f.blocks.filterMap f.block?
  for b in blocks do
    for c in b.preds do
      if !(blockMark[c.b]?.getD false) then throw s!"predecessor block b{c.b} for b{b.id} is missing"
    for c in b.succs do
      if !(blockMark[c.b]?.getD false) then throw s!"successor block b{c.b} for b{b.id} is missing"
  if (f.block? f.entry).any (!·.preds.isEmpty) then
    throw s!"entry block b{f.entry} has predecessor(s)"
  for b in blocks do
    for vid in b.values do
      let some v := f.value? vid | continue
      for h : i in [0:v.args.size] do
        if !(valueMark[v.args[i]]?.getD false) then
          throw s!"v{v.args[i]}, arg {i} of v{vid}, is missing"
    for c in b.controls do
      if !(valueMark[c]?.getD false) then throw s!"control value for b{b.id} is missing: v{c}"
  for x in f.freeBlocks do
    if blockMark[x]?.getD false then throw s!"used block b{x} in free list"
  for x in f.freeValues do
    if valueMark[x]?.getD false then throw s!"used value v{x} in free list"
  -- every argument dominates its use (a Phi argument the corresponding predecessor)
  let po := Analysis.postorder f
  let t := Analysis.newSparseTree (f.bidLast + 1) f.entry po (Analysis.dominators f)
  let domCheck (x y : ID) : Bool := !t.isAncestorEq f.entry y || t.isAncestorEq x y
  for b in blocks do
    for vid in b.values do
      let some v := f.value? vid | continue
      for h : i in [0:v.args.size] do
        let x := (f.value? v.args[i]).map (·.block) |>.getD 0
        let y := if v.op == .Phi then (b.preds[i]?.map (·.b)).getD b.id else b.id
        if !domCheck x y then
          throw s!"arg {i} of value v{vid} does not dominate, arg=v{v.args[i]}"
    for c in b.controls do
      let x := (f.value? c).map (·.block) |>.getD 0
      if !domCheck x b.id then throw s!"control value v{c} for b{b.id} doesn't dominate"
  -- loop construction
  let ln ← Analysis.loopnest f po t
  if !ln.hasIrreducible then
    for bid in po do
      for bb in Analysis.succIDs f bid do
        let lb := ln.b2l[bid]?.join
        let lbb := ln.b2l[bb]?.join
        let notHeader := match lbb with
          | some l => bb != ln.loops[l]!.header
          | none => false
        if lb.isNone && lbb.isSome && notHeader then
          throw s!"block b{bid} not in loop branches to non-header block b{bb} in loop"
        if lb.isSome && lbb.isSome && notHeader &&
            !Analysis.LoopNest.isWithinOrEq ln.loops lb lbb then
          throw s!"block b{bid} in loop branches to non-header block b{bb} in non-containing loop"
  -- use counts
  let mut uses : Array Nat := Array.replicate nv 0
  for b in blocks do
    for vid in b.values do
      let some v := f.value? vid | continue
      for a in v.args do
        uses := uses.modify a (· + 1)
    for c in b.controls do
      uses := uses.modify c (· + 1)
  for b in blocks do
    for vid in b.values do
      let some v := f.value? vid | continue
      if v.uses != uses[vid]! then
        throw s!"v{vid} has {uses[vid]!} uses, but has Uses={v.uses}"
  memCheck e f

/-- The shapes the pointer ops' arguments have (beyond Go's `checkFunc`, issue #69): `PtrIndex`
takes a pointer first; `OffPtr`, `AddPtr`, `IsNonNil`, `EqPtr`, `NeqPtr` pointer-sized words —
pointers or 64-bit integers (`SP` after `expand calls`, itab words after `decompose builtin`
are `uintptr`); `AddPtr`/`PtrIndex` a 64-bit integer second; `Convert` converts between
pointer-sized words. -/
def argShapeOK (e : CheckEnv) (f : Func) (v : Value) : Bool :=
  let sh (i : Nat) : Option Sem.Ty := (v.args[i]?.bind (Check.typeOf? f)).map e.tabs.ty
  let isP (i : Nat) := match sh i with | some (.ptr _) => true | _ => false
  let isI (i : Nat) := match sh i with | some (.int .w64) => true | _ => false
  let isW (i : Nat) := isP i || isI i
  match v.op with
  | .OffPtr | .IsNonNil => isW 0
  | .AddPtr => isW 0 && isI 1
  | .PtrIndex => isP 0 && isI 1
  | .EqPtr | .NeqPtr => isW 0 && isW 1
  | .Convert =>
    match e.tabs.ty v.type with
    | .ptr _ => isP 0 || isI 0
    | .int .w64 => isP 0 || isI 0
    | _ => false
  | _ => true

/-- `argShapeOK` of every listed value. -/
def checkArgShapes (e : CheckEnv) (f : Func) : Except String Unit := do
  for bid in f.blocks do
    let some b := f.block? bid | continue
    for vid in b.values do
      let some v := f.value? vid | continue
      if !argShapeOK e f v then throw s!"v{vid}: {v.op.name} argument shapes"

/-- The well-formedness checker: Go's `checkFunc` (`checkGo`), then the validation of the
dominator tree it relies on (`DomCert.check`), which the pass proofs use for dominance, then
the argument shapes of the pointer ops (`checkArgShapes`). -/
def check (e : CheckEnv) (f : Func) : Except String Unit := do
  checkGo e f
  DomCert.check f
  checkArgShapes e f

end GoFV.SSA
