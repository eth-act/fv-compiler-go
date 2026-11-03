import GoFV.Opt.LowTy
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache

/-!
# flagalloc (`flagalloc.go`)

Port of `flagalloc` (go1.27.3; docs/PASSES2.md, flagalloc, #409). Two backward rounds over the
cached postorder (`f.postorder()`) compute the flags value each block wants live at its end
(`end`, by block ID; a predecessor gets the last request); `Defer` blocks and blocks whose flags
control is not their `end` want none. A forward scan marks the flags values that must be
recomputed (`spill`). Each block's schedule is then rebuilt: a flags argument that is not the
current flags value is replaced by a recursive copy of its generator (`copyFlags`: flags- and
tuple-typed arguments first, in argument order, each copy appended to the block at a `NotStmt`
position), as are mismatched flags controls and a wanted end value that is not live (that last
copy is unlinked). `FlagsLiveAtEnd` records `end`. Replaced generators left without uses are
reset to `Invalid` and dropped from their blocks (not freed). arm64 has no `Config.splitLoad`:
a spilled flags generator with a memory argument is Go's nil-function panic.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace FlagAlloc

/-- `v.clobbersFlags()`. -/
def clobbersFlags (ty : LowTy) (v : Value) : Bool :=
  v.op.clobberFlags || (ty.tuple? v.type).any (fun (a, b) => ty.isFlags a || ty.isFlags b)

/-- `v.copyInto(b)` (`value.go:446-458`): a new value with `v`'s op, type, aux and arguments
appended to `b`, at `v.Pos.WithNotStmt()`; `Fatalf` if an argument has memory type. -/
def copyInto (ty : LowTy) (f : Func) (v b : ID) : Except String (Func × ID) := do
  let x := f.getV v
  let (f, c) := f.newValueArgs b x.pos.withNotStmt x.op x.type x.auxInt x.aux x.args
  if x.args.any fun a => ty.isMemory (f.getV a).type then
    throw s!"can't move a value with a memory arg v{v}"
  return (f, c)

/-- `copyFlags(v, b)`: copies of `v`'s flags- and tuple-typed arguments (recursively, in
argument order), then of `v`, with the copied arguments substituted. -/
def copyFlags (ty : LowTy) : Nat → Func → ID → ID → Except String (Func × ID)
  | 0, _, v, _ => throw s!"copyFlags: argument chain of v{v} too deep"
  | fuel + 1, f, v, b => do
    let mut f := f
    let mut flagsArgs : Array (Nat × ID) := #[]
    let args := (f.getV v).args
    for h : i in [0:args.size] do
      let t := (f.getV args[i]).type
      if ty.isFlags t || ty.isTuple t then
        let (f', c) ← copyFlags ty fuel f args[i] b
        f := f'
        flagsArgs := flagsArgs.push (i, c)
    let (f', c) ← copyInto ty f v b
    f := f'
    for (i, a) in flagsArgs do
      f := f.setArg c i a
    return (f, c)

/-- The block's flags-typed control, if any (Go panics on two). -/
def flagsControl (ty : LowTy) (f : Func) (blk : Block) : Except String (Option ID) := do
  let mut flag : Option ID := none
  for c in blk.controls do
    if ty.isFlags (f.getV c).type then
      if flag.isSome then throw "cannot have multiple controls using flags"
      flag := some c
  return flag

end FlagAlloc

open FlagAlloc in
/-- `flagalloc(f)`. -/
def flagalloc (env : PassEnv) (f : Func) : Except String Func := do
  let ty ← LowTy.ofEnv env
  let nb := max f.blockTab.size (f.bidLast + 1)
  let nv := max f.valueTab.size (f.vidLast + 1)
  let mut endv : Array (Option ID) := Array.replicate nb none
  let (po, f) := f.postorder
  for _ in [0:2] do
    for b in po do
      let blk := f.getB b
      let mut flag ← flagsControl ty f blk
      if flag.isNone then flag := endv[b]!
      for k in [0:blk.values.size] do
        let v := blk.values[blk.values.size - 1 - k]!
        let x := f.getV v
        if flag == some v then flag := none
        if clobbersFlags ty x then flag := none
        for a in x.args do
          if ty.isFlags (f.getV a).type then flag := some a
      if flag.isSome then
        for e in blk.preds do
          endv := endv.set! e.b flag
  for b in f.blocks do
    let blk := f.getB b
    if blk.kind == .Defer then
      endv := endv.set! b none
      continue
    for c in blk.controls do
      if ty.isFlags (f.getV c).type && endv[b]! != some c then endv := endv.set! b none
  -- the flags values that need to be recomputed
  let mut spill : Array Bool := Array.replicate nv false
  for b in f.blocks do
    let blk := f.getB b
    let mut flag : Option ID := (blk.preds[0]?).bind fun e => endv[e.b]!
    for v in blk.values do
      let x := f.getV v
      for a in x.args do
        if !ty.isFlags (f.getV a).type then continue
        if flag == some a then continue
        spill := spill.set! a true
        flag := some a
      if clobbersFlags ty x then flag := none
      if ty.isFlags x.type then flag := some v
    for c in blk.controls do
      if flag != some c && ty.isFlags (f.getV c).type then spill := spill.set! c true
    if let some v := endv[b]! then
      if flag != some v then spill := spill.set! v true
  -- recompute flags where needed
  let mut f := f
  let mut remove : Array ID := #[]
  let fuel := nv + 1
  for b in f.blocks do
    let blk := f.getB b
    let oldSched := blk.values
    f := f.modB b fun x => { x with values := #[] }
    let mut flag : Option ID := none
    if let some e := blk.preds[0]? then
      flag := endv[e.b]!
      for e in blk.preds.extract 1 blk.preds.size do
        if endv[e.b]! != flag then
          throw s!"live flag in b{b}'s predecessors not consistent"
    for v in oldSched do
      let x := f.getV v
      if x.op == .Phi && ty.isFlags x.type then throw s!"phi of flags not supported: v{v}"
      if spill[v]! && (ty.memoryArg f x).isSome then
        throw s!"can't split flag generator: v{v} (arm64 has no splitLoad)"
      for i in [0:x.args.size] do
        let a := (f.getV v).args[i]!
        if !ty.isFlags (f.getV a).type then continue
        if flag == some a then continue
        let (f', c) ← copyFlags ty fuel f a b
        f := f'.setArg v i c
        flag := some a
      f := f.modB b fun y => { y with values := y.values.push v }
      if clobbersFlags ty x then flag := none
      if ty.isFlags x.type then flag := some v
    for i in [0:(f.getB b).controls.size] do
      let v := (f.getB b).controls[i]!
      if flag != some v && ty.isFlags (f.getV v).type then
        remove := remove.push v
        let (f', c) ← copyFlags ty fuel f v b
        f := f'.replaceControl b i c
        flag := some v
    if let some v := endv[b]! then
      if flag != some v then
        remove := remove.push v
        let (f', _) ← copyFlags ty fuel f v b
        f := f'
  f := { f with low := { f.low with
    flagsLive := (f.blocks.filter fun b => endv[b]!.isSome).qsort (· < ·) } }
  -- reset the dead values among `remove`, keep the others out of the list
  let mut i := 0
  for _ in [0:remove.size + 1] do
    if i >= remove.size then break
    let v := remove[i]!
    if (f.getV v).uses == 0 then
      f := f.resetValue v .Invalid
      i := i + 1
      continue
    remove := (remove.set! i remove.back!).pop
  if remove.isEmpty then return f
  let removeBlocks := remove.map fun v => (f.getV v).block
  for b in f.blocks do
    if !removeBlocks.contains b then continue
    let vals := (f.getB b).values
    let mut keep : Array ID := #[]
    for v in vals do
      if (f.getV v).op == .Invalid then
        f := { f with valueTab := f.valueTab.set! v none }
      else keep := keep.push v
    f := f.modB b fun y => { y with values := keep }
  return f

/-- The `flagalloc` pass. -/
def flagallocPass : Pass := Pass.ofFunc flagalloc

end GoFV.Opt
