import GoFV.Gen.Env
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.TypePred
import Std.Data.HashSet.Basic

/-!
# The liveness core (`liveness/plive.go`, `bitvec/bv.go`)

The dataflow part of `liveness.Compute` that `MergeLocals` reuses (`docs/PASSES3.md` B1, A2),
as pure functions over `Env` (go1.27.3, `cmd/compile/internal/liveness/plive.go`):
`bitvec.BitVec` (`bitvec/bv.go:17-200`) as `Bv`; `affectedVar` (plive.go:336-386),
`valueEffects` (285-333), `isfat` (1530-1555), `newliveness` (396-449) with `markUnsafePoints`
(494-644, `IsUnsafe`) and `hasStackMap` (651-662), `initcache` (239-264), `prologue` (667-686)
and `solve` (689-745). `ssa.AutoVar` is `ssa/value.go:607-617`, `Value.MemoryArg` 556-568.

Names (`*ir.Name`) are `.prog` name numbers (`VarRef.dcl`) when they are `Dcl` names, which every
name `liveness` tracks is; an `*ir.Name` aux outside `Dcl` is `VarRef.other` with its `.ssa`
facts. `n.Used()` changes inside `AllocFrame`, so the caller passes it (`used`).
`lv.be` is indexed by block ID, as Go's (`lv.be[b.ID]`). The `ssa.Cache` reuse of `newliveness`
and `Compute` only recycles storage that `Compute` clears; it is not modelled. Go's
`base.Flag.ClobberDead` is off for the corpus (`enableClobber` is a no-op).
-/

namespace GoFV.Gen.Live

open GoFV.SSA

/-- `bitvec.BitVec`: `n` bits in 32-bit words. -/
structure Bv where
  n : Nat
  b : Array UInt32
  deriving DecidableEq, Inhabited, Hashable

namespace Bv

/-- `bitvec.New(n)`. -/
def new (n : Nat) : Bv := ⟨n, Array.replicate ((n + 31) / 32) 0⟩

/-- `bv.Get(i)`. -/
def get (bv : Bv) (i : Nat) : Except String Bool := do
  if i ≥ bv.n then throw s!"bvget: index {i} is out of bounds with length {bv.n}"
  return (bv.b[i / 32]! >>> (i % 32).toUInt32) &&& 1 != 0

/-- `bv.Set(i)`. -/
def set (bv : Bv) (i : Nat) : Except String Bv := do
  if i ≥ bv.n then throw s!"bvset: index {i} is out of bounds with length {bv.n}"
  return { bv with b := bv.b.modify (i / 32) (· ||| ((1 : UInt32) <<< (i % 32).toUInt32)) }

/-- `bv.Set(i)` for a Go `int32` index (negative indices are out of bounds). -/
def setI (bv : Bv) (i : Int) : Except String Bv := do
  if i < 0 then throw s!"bvset: index {i} is out of bounds with length {bv.n}"
  bv.set i.toNat

/-- `bv.Unset(i)`. -/
def unset (bv : Bv) (i : Nat) : Except String Bv := do
  if i ≥ bv.n then throw s!"bvunset: index {i} is out of bounds with length {bv.n}"
  return { bv with b := bv.b.modify (i / 32) (· &&& ~~~((1 : UInt32) <<< (i % 32).toUInt32)) }

/-- `bv1.Eq(bv2)`. -/
def eq (a c : Bv) : Except String Bool := do
  if a.n != c.n then throw s!"bvequal: lengths {a.n} and {c.n} are not equal"
  return a.b == c.b

/-- `dst.Or(src1, src2)` (the result; Go writes it into `dst`, which has the same length). -/
def or (a c : Bv) : Bv := { a with b := a.b.zipWith (· ||| ·) c.b }

/-- `dst.AndNot(src1, src2)`. -/
def andNot (a c : Bv) : Bv := { a with b := a.b.zipWith (fun x y => x &&& ~~~y) c.b }

/-- `bv.Clear()`. -/
def clear (bv : Bv) : Bv := { bv with b := bv.b.map fun _ => 0 }

/-- `bv.IsEmpty()`. -/
def isEmpty (bv : Bv) : Bool := bv.b.all (· == 0)

/-- The set bits in ascending order (`bv.Next` iteration). -/
def toList (bv : Bv) : List Nat :=
  (List.range bv.n).filter fun i => (bv.b[i / 32]! >>> (i % 32).toUInt32) &&& 1 != 0

end Bv

/-- `blockEffects`. -/
structure BlockEffects where
  uevar : Bv := ⟨0, #[]⟩
  varkill : Bv := ⟨0, #[]⟩
  livein : Bv := ⟨0, #[]⟩
  liveout : Bv := ⟨0, #[]⟩
  deriving Inhabited

/-- An `*ir.Name`: a `Dcl` name by `.prog` number, or a name aux outside `Dcl`. -/
inductive VarRef where
  | dcl (n : Nat)
  | other (a : AuxRef)
  deriving DecidableEq, Inhabited, Repr, Hashable

/-- The `liveEffect` bits. -/
def uevar : Nat := 1
def varkill : Nat := 2

/-- `ssa.SymEffect` constants. -/
def symRead : SymEffect := ⟨true, false, false⟩
def symWrite : SymEffect := ⟨false, true, false⟩
def symNone : SymEffect := ⟨false, false, false⟩

/-- `obj.ABI0`, `obj.ABIInternal`. -/
def abi0 : Nat := 0
def abiInternal : Nat := 1

/-- The `*ir.Name` of an aux, which must be a name. -/
def nameRef (env : Env) (a : AuxRef) : Except String VarRef := do
  match (← env.auxDef a).kind with
  | .name .. => return match env.nameOfAux? a with | some n => .dcl n | none => .other a
  | _ => throw s!"liveness: aux a{a} is not an *ir.Name"

/-- The type size of a `.ssa` type. -/
def typeSize (env : Env) (t : TypeRef) : Except String Int := do
  match (← env.typeDef t).size with
  | some s => pure s
  | none => throw s!"liveness: size of type t{t} not calculated"

/-- `ssa.AutoVar(v)` (name only): the `LocalSlot` home of `v`, else the `*AuxNameOffset` aux. -/
def autoVar (env : Env) (v : Value) : Except String VarRef := do
  match env.loc? v.id with
  | some (.slot k) =>
    if (← typeSize env v.type) > (← typeSize env k.type) then
      throw s!"v{v.id}: spill/restore type t{v.type} doesn't fit in slot type t{k.type}"
    nameRef env k.name
  | _ =>
    match v.aux with
    | some a =>
      match (← env.auxDef a).kind with
      | .nameOff n _ => nameRef env n
      | _ => throw s!"liveness: AutoVar of v{v.id}: aux is not *AuxNameOffset"
    | none => throw s!"liveness: AutoVar of v{v.id}: no aux"

/-- `affectedVar` (plive.go:336-386). -/
def affectedVar (env : Env) (v : Value) : Except String (Option VarRef × SymEffect) := do
  let auxName : Except String VarRef := match v.aux with
    | some a => nameRef env a
    | none => throw s!"liveness: v{v.id} has no aux name"
  let argV (i : Nat) : Except String Value := do
    match v.args[i]? with
    | some a => env.value a
    | none => throw s!"liveness: v{v.id} has no argument {i}"
  match v.op with
  | .LoadReg => return (some (← autoVar env (← argV 0)), symRead)
  | .StoreReg => return (some (← autoVar env v), symWrite)
  | .ArgIntReg => return (some (← autoVar env v), symRead)
  | .VarLive => return (some (← auxName), symRead)
  | .VarDef => return (some (← auxName), symWrite)
  | .KeepAlive => return (some (← autoVar env (← argV 0)), symRead)
  | op =>
    let e := op.symEffect
    if e == symNone then return (none, symNone)
    match v.aux with
    | none => return (none, e)
    | some a =>
      match (← env.auxDef a).kind with
      | .sym .. => return (none, e)
      | .name .. => return (some (← nameRef env a), e)
      | _ => throw s!"weird aux: v{v.id}"

/-- `isfat(t)` (plive.go:1530-1555; no SIMD types). -/
partial def isfat (env : Env) (t : TypeRef) : Except String Bool := do
  let d ← env.typeDef t
  match d.kind, d.tail with
  | .SLICE, _ | .STRING, _ | .INTER, _ => return true
  | .ARRAY, .array e n => if n == 1 then isfat env e else return true
  | .STRUCT, .struct fs =>
    if h : fs.size = 1 then isfat env fs[0].type else return true
  | .ARRAY, _ | .STRUCT, _ => throw s!"liveness: type t{t} without structure"
  | _, _ => return false

/-- The facts `valueEffects` reads of a name. -/
structure NameFacts where
  cls : String
  used : Bool
  addrtaken : Bool
  size : Except String Int
  ssaType : Option TypeRef

/-- A collection of global state used by the liveness analysis (`Liveness`). -/
structure Lv where
  env : Env
  /-- `lv.vars`: name numbers. -/
  vars : Array Nat
  /-- `lv.idx`: name number → position in `vars`. -/
  idx : Std.HashMap Nat Nat
  stkptrsize : Int
  /-- `n.Used()` at the time of the analysis. -/
  used : Nat → Bool
  conservativeWrites : Bool
  /-- `types.TypeMem`. -/
  mem : TypeRef
  /-- `lv.be`, by block ID. -/
  be : Array BlockEffects
  allUnsafe : Bool
  unsafePoints : Bv
  unsafeBlocks : Bv
  /-- `lv.cache`. -/
  retuevar : Array Nat := #[]
  tailuevar : Array Nat := #[]
  cacheInitialized : Bool := false
  /-- `lv.partLiveArgs` (name numbers). -/
  partLiveArgs : Std.HashSet Nat := {}

namespace Lv

def value (lv : Lv) (id : ID) : Except String Value := lv.env.value id
def block (lv : Lv) (id : ID) : Except String Block := lv.env.block id

/-- `v.MemoryArg()`. -/
def memoryArg (lv : Lv) (v : Value) : Except String (Option Value) := do
  if v.op == .Phi then throw s!"v{v.id}: MemoryArg on Phi"
  match v.args.back? with
  | none => return none
  | some m =>
    let mv ← lv.value m
    return if lv.env.tabs.isMemory lv.mem mv.type then some mv else none

def facts (lv : Lv) : VarRef → Except String NameFacts
  | .dcl n => do
    let x ← lv.env.name n
    let addrtaken ← match lv.env.inFlags[n]? with
      | some f => pure f.addrtaken
      | none =>
        match x.d.aux with
        | some a =>
          match (← lv.env.auxDef a).kind with
          | .name _ _ _ _ _ fl _ => pure fl.addrtaken
          | _ => throw s!"liveness: name n{n}: aux is not a name"
        | none => throw s!"liveness: name n{n}: no flags"
    return { cls := x.cls, used := lv.used n, addrtaken, size := x.size, ssaType := x.ssaType }
  | .other a => do
    match (← lv.env.auxDef a).kind with
    | .name _ cls t _ _ fl _ =>
      return { cls := cls.name, used := fl.used, addrtaken := fl.addrtaken,
               size := typeSize lv.env t, ssaType := some t }
    | _ => throw s!"liveness: aux a{a} is not a name"

/-- `valueEffects` (plive.go:285-333): the position of the affected tracked variable (−1 if
none) and the effect bits, plus the argument it marks partially live. -/
def valueEffectsP (lv : Lv) (v : Value) : Except String (Int × Nat × Option Nat) := do
  let (n?, e) ← affectedVar lv.env v
  let some n := n? | return (-1, 0, none)
  if e == symNone then return (-1, 0, none)
  let fx ← lv.facts n
  if v.op == .VarDef || v.op == .VarLive || v.op == .KeepAlive then
    if !fx.used then return (-1, 0, none)
  let mut part : Option Nat := none
  if fx.cls == "PPARAM" && !fx.addrtaken then
    if (← fx.size) > 8 then
      match n with
      | .dcl k => part := some k
      | .other a => throw s!"liveness: partially live argument a{a} is not a Dcl name"
  let mut effect := 0
  if e.read || e.addr then effect := effect ||| uevar
  if e.write then
    let fat ← match fx.ssaType with
      | some t => isfat lv.env t
      | none => throw "liveness: name without .ssa type"
    if !fat || v.op == .VarDef then effect := effect ||| varkill
    else if lv.conservativeWrites then effect := effect ||| uevar
  if effect == 0 then return (-1, 0, part)
  match n with
  | .dcl k =>
    match lv.idx[k]? with
    | some p => return (p, effect, part)
    | none => return (-1, 0, part)
  | .other _ => return (-1, 0, part)

/-- `lv.valueEffects(v)`: (position or −1, effect bits `uevar`/`varkill`). -/
def valueEffects (lv : Lv) (v : Value) : Except String (Int × Nat) := do
  let (p, e, _) ← lv.valueEffectsP v
  return (p, e)

/-- Whether an aux is the given `*obj.LSym`. -/
def auxIsSym (lv : Lv) (a : Option AuxRef) (name : String) (abi : Nat) : Except String Bool := do
  match a with
  | none => return false
  | some a =>
    match (← lv.env.auxDef a).kind with
    | .sym nm ab .. => return nm.toStringLossy == name && ab == abi
    | _ => return false

/-- `hasStackMap` (plive.go:651-662). -/
def hasStackMap (lv : Lv) (v : Value) : Except String Bool := do
  if !v.op.call then return false
  match v.aux with
  | some a =>
    match (← lv.env.auxDef a).kind with
    | .call (some fn) _ =>
      if (← lv.auxIsSym (some fn) "runtime.wbZero" abiInternal) ||
         (← lv.auxIsSym (some fn) "runtime.wbMove" abiInternal) then
        return false
      return true
    | _ => return true
  | none => return true

/-- `IsUnsafe(f)`: `base.Flag.CompilingRuntime || f.NoSplit`. -/
def isUnsafe (env : Env) : Except String Bool := do
  return (← env.compilingRuntime) || env.file.nosplit

/-- `markUnsafePoints` (plive.go:508-644). -/
def markUnsafePoints (lv : Lv) : Except String Lv := do
  if ← isUnsafe lv.env then return { lv with allUnsafe := true }
  let f := lv.env.f
  let mut up := Bv.new (f.vidLast + 1)
  let mut ub := Bv.new (f.bidLast + 1)
  for bid in f.blocks do
    let b ← lv.block bid
    for vid in b.values do
      if (← lv.value vid).op.unsafePoint then up ← up.set vid
  for bid in f.blocks do
    let b ← lv.block bid
    for wid in b.values do
      let w ← lv.value wid
      if w.op != .WBend then continue
      -- Find the first memory op in the block, which should be a Phi.
      let mut m := w
      repeat
        match ← lv.memoryArg m with
        | none => throw s!"liveness: v{m.id}: nil memory argument before write barrier end mark"
        | some x => m := x
        if m.block != b.id then throw s!"can't find Phi before write barrier end mark v{w.id}"
        if m.op == .Phi then break
      if m.args.size != 2 then
        throw s!"phi before write barrier end mark has {m.args.size} args, want 2"
      let some ce := b.preds[0]? | throw s!"liveness: b{b.id}: no predecessor 0"
      let some de := b.preds[1]? | throw s!"liveness: b{b.id}: no predecessor 1"
      let c ← lv.block ce.b
      let d ← lv.block de.b
      let decision ←
        if c.preds.size == 1 && c.preds[0]!.b == d.id then pure d
        else if d.preds.size == 1 && d.preds[0]!.b == c.id then pure c
        else if c.preds.size == 1 && d.preds.size == 1 && c.preds[0]!.b == d.preds[0]!.b then
          lv.block c.preds[0]!.b
        else throw s!"can't find write barrier pattern v{w.id}"
      if decision.succs.size != 2 then
        throw s!"common predecessor block the wrong type {repr decision.kind}"
      -- Flow backwards from the control value to find the flag load.
      let some c0 := decision.controls[0]? | throw s!"liveness: b{decision.id}: no control"
      let mut x ← lv.value c0
      let mut load : ID := 0
      repeat
        if (← lv.memoryArg x).isSome then
          if ← lv.auxIsSym x.aux "runtime.writeBarrier" abi0 then
            load := x.id
            break
          let some a0 := x.args[0]? | throw s!"liveness: v{x.id}: no argument 0"
          if ← lv.auxIsSym (← lv.value a0).aux "runtime.writeBarrier" abi0 then
            load := x.id
            break
          throw s!"load of write barrier flag not from correct global: v{x.id}"
        if x.args.size == 1 || x.args.size == 2 && x.args[0]! == x.args[1]! then
          x ← lv.value x.args[0]!
          continue
        throw s!"write barrier control value has more than one argument: v{x.id}"
      -- Mark everything after the load unsafe.
      let mut found := false
      for vid in decision.values do
        if found then up ← up.set vid
        found := found || vid == load
      ub ← ub.set decision.id
      -- Mark the write barrier on/off blocks as unsafe.
      for e in decision.succs do
        if e.b == b.id then continue
        let xb ← lv.block e.b
        for vid in xb.values do up ← up.set vid
        ub ← ub.set xb.id
      -- Mark from the join point up to the WBend as unsafe.
      for vid in b.values do
        if (← lv.value vid).op == .WBend then break
        up ← up.set vid
  return { lv with unsafePoints := up, unsafeBlocks := ub }

end Lv

/-- `newliveness(fn, f, vars, idx, stkptrsize)` (plive.go:396-449), with `lv.conservativeWrites`
set as MergeLocals does right after. `used n` is `n.Used()`. -/
def newliveness (env : Env) (vars : Array Nat) (idx : Std.HashMap Nat Nat) (stkptrsize : Int)
    (used : Nat → Bool) (conservativeWrites : Bool := false) : Except String Lv := do
  let f := env.f
  let mem ← match (env.file.sections[0]?.bind (·.typs)).bind fun ts => (ts.find? (·.1 == "Mem")).map (·.2) with
    | some t => pure t
    | none => throw "liveness: typs: no Mem"
  let nvars := vars.size
  let mut be : Array BlockEffects := Array.replicate (f.bidLast + 1) {}
  for bid in f.blocks do
    be := be.set! bid { uevar := Bv.new nvars, varkill := Bv.new nvars, livein := Bv.new nvars,
                        liveout := Bv.new nvars }
  let lv : Lv := { env, vars, idx, stkptrsize, used, conservativeWrites, mem, be,
                   allUnsafe := false, unsafePoints := ⟨0, #[]⟩, unsafeBlocks := ⟨0, #[]⟩ }
  lv.markUnsafePoints

namespace Lv

/-- `initcache` (plive.go:239-264). -/
def initcache (lv : Lv) : Except String Lv := do
  if lv.cacheInitialized then throw "liveness cache initialized twice"
  let mut ret := #[]
  let mut tail := #[]
  for i in [0:lv.vars.size] do
    match (← lv.env.name lv.vars[i]!).cls with
    | "PPARAM" => tail := tail.push i
    | "PPARAMOUT" => ret := ret.push i
    | _ => pure ()
  return { lv with cacheInitialized := true, retuevar := ret, tailuevar := tail }

/-- `prologue` (plive.go:667-686); also collects `partLiveArgs`. -/
def prologue (lv : Lv) : Except String Lv := do
  let mut lv ← lv.initcache
  for bid in lv.env.f.blocks do
    let b ← lv.block bid
    let mut be := lv.be[bid]!
    let mut j := b.values.size
    while j > 0 do
      j := j - 1
      let (pos, e, part) ← lv.valueEffectsP (← lv.value b.values[j]!)
      if let some k := part then lv := { lv with partLiveArgs := lv.partLiveArgs.insert k }
      if e &&& varkill != 0 then
        be := { be with varkill := ← be.varkill.setI pos, uevar := ← be.uevar.unset pos.toNat }
      if e &&& uevar != 0 then
        be := { be with uevar := ← be.uevar.setI pos }
    lv := { lv with be := lv.be.set! bid be }
  return lv

/-- `solve` (plive.go:689-745): the dataflow equations over `f.Postorder()` (the cached
postorder if the function has one). -/
partial def solve (lv : Lv) : Except String Lv := do
  let po := (Func.postorder lv.env.f).1
  let nvars := lv.vars.size
  let mut be := lv.be
  let mut change := true
  while change do
    change := false
    for bid in po do
      let b ← lv.block bid
      let mut newliveout := Bv.new nvars
      match b.kind with
      | .Ret => for p in lv.retuevar do newliveout ← newliveout.set p
      | .RetJmp => for p in lv.tailuevar do newliveout ← newliveout.set p
      | .Exit => pure ()
      | _ =>
        let some s0 := b.succs[0]? | throw s!"liveness: b{bid}: no successors"
        newliveout := be[s0.b]!.livein
        for s in b.succs[1:] do
          newliveout := newliveout.or be[s.b]!.livein
      let x := be[bid]!
      let mut liveout := x.liveout
      if !(← liveout.eq newliveout) then
        change := true
        liveout := newliveout
      let livein := (liveout.andNot x.varkill).or x.uevar
      be := be.set! bid { x with liveout, livein }
  return { lv with be }

end Lv

end GoFV.Gen.Live
