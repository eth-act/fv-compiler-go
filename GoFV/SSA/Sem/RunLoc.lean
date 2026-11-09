import GoFV.SSA.Sem.RunSched
import GoFV.SSA.RegARM64
import GoFV.SSA.OpARM64
import GoFV.SSA.RegMask

variable [GoFV.SSA.Sem.Addrs]

/-!
# `GoFV.SSA.runLoc`: allocated SSA (L2, `docs/plans/semantics2.md` §7)

From `regalloc` on, every value has a home (`f.RegAlloc`): a register, a stack slot, a register
pair or a list of result registers. Arguments no longer dominate their uses, so the function is
not evaluated as SSA: `runLoc` keeps a machine state and never reads data by value ID.

* **State** (`LocState`): the register file (Go's register numbers, `ARM64.registers`), the flags
  register, the stack slots written so far, and the current memory. The activation (arguments'
  images, closure context, initial memory) is Phase 1's `Frame`.
* **Values** run in `b.Values` order. A value reads each argument from the argument's home at the
  argument's shape and writes its result to its own home (`LocState.read`, `LocState.write`);
  its op is `runL`'s (`evalOpL`, with faulting memory ops as under `runSched`) and values take
  their shapes as under `runSched` (`LMode.loc f = LMode.sched f`: `Val.retypeL` in a lowered
  function, Phase 1's `Val.retype` in one with no arm64 op), so every op means what it means in
  L0/L1, and a register holding a wider value read at a narrower type gives its low bits. A
  tuple's components go to the home's registers in order (a result that is not a tuple writes
  `poison` to every component); a memory component is the current memory, a flags component the
  flags register; a value of type `mem` or `flags` has no home and is the current memory or the
  flags register.
* **Moves.** `Copy`, `LoadReg` (slot to register) and `StoreReg` (register to slot) move their
  argument. A slot write kills the slots of the same variable it overlaps. `MOVDreg`/`MOVDnop`
  copy the upper bits of their argument's register (`movdLoc`): a `LoadReg` sign-extends exactly
  the signed narrow types (`loadByType`), a `Copy` keeps its argument's bits, any other producer
  as under `runL` (`Arm64.signExtendsIn`).
* **`ZERO`** reads as the 0 of the reader's shape and ignores writes: regalloc homes zero
  constants of every type there (a `bool` `false` and an `int64` `0` share it).
* **Clobbers.** After a value, the registers its op clobbers (`regInfo.clobbers`: every
  caller-saved register for a call, the fixed temporaries of `DUFFZERO`, `LoweredMove`, the
  write barrier, …), its argument registers it clobbers (`clobbersArg0`/`clobbersArg1`), its
  temporary register (`f.tempRegs`) and, for an op with `clobberFlags`, the flags register hold
  `poison`; then its result is written.
* **Phis** do nothing: regalloc gives a phi and its arguments one home (the edge copies are in
  the predecessors). A phi whose argument has another home is `stuck`.
* **Terminators** are `runL`'s (`stepTermL`) on the controls read from their homes; a `Ret`'s
  `MakeResult` is its arguments read from their homes (the ABI result registers).
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- The context of `runLoc` for `f`: `runL`'s, each value's home and temporary register by ID,
and the size of each slot's type. -/
structure LocCtx where
  ctx : Ctx
  homes : Array (Option Location)
  temps : Array (Option Nat)

/-- The context of `runLoc` for `f` (its export section's tables `tabs`). -/
def LocCtx.make (tabs : Tables) (f : Func) : LocCtx :=
  let n := f.valueTab.size
  let none' : Array (Option Location) := Array.replicate n none
  let homes := match f.low.regAlloc with
    | some (_, es) => es.foldl (fun a (id, l) => if id < n then a.set! id (some l) else a) none'
    | none => none'
  let temps := match f.low.tempRegs with
    | some es => es.foldl (fun a (id, r) => if id < n then a.set! id (some r) else a)
      (Array.replicate n none)
    | none => Array.replicate n none
  { ctx := Ctx.makeL tabs f, homes, temps }

/-- The home of value `id`. -/
def LocCtx.home (lc : LocCtx) (id : ID) : Option Location := (lc.homes[id]?).join

/-- The shape of value `id`. -/
def LocCtx.ty (lc : LocCtx) (id : ID) : Ty := lc.ctx.tys[id]?.getD .other

/-- The flags shape (`Ty.flags`), which no other lowered value has: SSA-able structs are
decomposed before `lower`. -/
def Ty.isFlags : Ty → Bool
  | .agg [(0, .bool), (1, .bool), (2, .bool), (3, .bool), (4, .bool)] 5 => true
  | _ => false

/-- The machine state of `runLoc`. -/
structure LocState where
  /-- The activation (arguments' images, closure, initial memory); its `regs` only stage the
  block controls for `stepTermL`. -/
  fr : Frame
  /-- The register file, by Go's register number. -/
  regs : Array Val
  flags : Val
  /-- The stack slots written so far, latest first. -/
  slots : List (SlotKey × Val)
  mem : Val

/-- `ZERO` (`ZR`): the register number of the zero register, which reads 0 and ignores
writes. Values of every type are allocated to it (`MOVDconst [0]` of a `bool`, an `int64`, a
pointer: `ZERO`), so it holds no value of its own. -/
def zeroReg : Nat := 29

example : (ARM64.registers[zeroReg]?.map (·.name)) = some "ZERO" := by decide

/-- Register `r` read at shape `t` (`ZERO`: the 0 of shape `t`). -/
def LocState.reg (s : LocState) (t : Ty) (r : Nat) : Val :=
  if r == zeroReg then (Arm64.res t 0).retypeL t else s.regs[r]?.getD .poison

/-- The registers of a home, in component order (`none`: a component with no register). -/
def _root_.GoFV.SSA.Location.regList : Location → List (Option Nat)
  | .reg r => [some r]
  | .pair a b => [a, b]
  | .results rs => rs.toList
  | .slot _ => []

/-- The components of a tuple of shapes `ts` read from registers `rs` (memory and flags
components from the state). -/
def LocState.readParts (s : LocState) : List Ty → List (Option Nat) → List Val
  | [], _ => []
  | t :: ts, rs =>
    match t with
    | .mem => s.mem :: s.readParts ts rs
    | t =>
      if t.isFlags then s.flags :: s.readParts ts rs
      else match rs with
        | some r :: rs => s.reg t r :: s.readParts ts rs
        | none :: rs => .poison :: s.readParts ts rs
        | [] => .poison :: s.readParts ts []

/-- The mode of `runLoc` for `f`: `runSched`'s (memory ops fault; values of a lowered function
are read as registers, `Val.retypeL`, those of a function with no arm64 op as in Phase 1). -/
def LMode.loc (f : Func) : LMode := LMode.sched f

/-- The contents of the home of `id`, as stored. -/
def LocState.raw (lc : LocCtx) (s : LocState) (id : ID) : Res Val :=
  let t := lc.ty id
  match lc.home id, t with
  | some (.slot k), _ => .ok ((s.slots.lookup k).getD .poison)
  | some h, .tuple ts => .ok (.tuple (s.readParts ts h.regList))
  | some (.reg r), t => .ok (s.reg t r)
  | some _, _ => .ok .poison
  | none, .tuple ts => .ok (.tuple (s.readParts ts []))
  | none, .mem => .ok s.mem
  | none, t =>
    if t.isFlags then .ok s.flags else .stuck s!"v{id} has no home"

/-- The value of `id` read from its home at its shape (`LMode.retype`): a register holds 64
bits, and a value of a narrower type is its low bits, as under `runSched`, where a phi or a
move of a narrower type takes its argument at that type. -/
def LocState.read (lc : LocCtx) (s : LocState) (id : ID) : Res Val := do
  let x ← s.raw lc id
  pure ((LMode.loc lc.ctx.f).retype (lc.ty id) x)

/-- Register `r` set to `x`. -/
def LocState.setReg (s : LocState) (r : Nat) (x : Val) : LocState :=
  { s with regs := if r < s.regs.size && r != zeroReg then s.regs.set! r x else s.regs }

/-- The components `xs` of a tuple of shapes `ts` written to registers `rs` (memory and flags
components to the state). -/
def LocState.writeParts (s : LocState) : List Ty → List Val → List (Option Nat) → LocState
  | t :: ts, x :: xs, rs =>
    match t with
    | .mem => { s with mem := x }.writeParts ts xs rs
    | t =>
      if t.isFlags then { s with flags := x }.writeParts ts xs rs
      else match rs with
        | some r :: rs => (s.setReg r x).writeParts ts xs rs
        | none :: rs => s.writeParts ts xs rs
        | [] => s.writeParts ts xs []
  | _, _, _ => s

/-- Slot `k` set to `x`: the slots of the same variable that `k` overlaps are killed (a slot of
unknown size kills every slot of its variable). -/
def LocState.setSlot (tabs : Tables) (s : LocState) (k : SlotKey) (x : Val) : LocState :=
  let size (k : SlotKey) : Option Int := (typeSize? tabs k.type).map Int.ofNat
  let overlaps (k' : SlotKey) : Bool :=
    k'.name == k.name &&
      match size k, size k' with
      | some n, some n' => decide (k.off < k'.off + n') && decide (k'.off < k.off + n)
      | _, _ => true
  { s with slots := (k, x) :: s.slots.filter fun (k', _) => !overlaps k' }

/-- The components of a result `x` at a tuple of `n` shapes: a tuple's own, `poison` for any other
value (every result register is written). -/
def Val.partsOf (n : Nat) : Val → List Val
  | .tuple xs => xs
  | _ => List.replicate n .poison

/-- The result `x` of value `id` written to its home. -/
def LocState.write (lc : LocCtx) (s : LocState) (id : ID) (x : Val) : LocState :=
  let t := lc.ty id
  match lc.home id, t with
  | some (.slot k), _ => s.setSlot lc.ctx.tabs k x
  | h, .tuple ts => s.writeParts ts (x.partsOf ts.length) ((h.map Location.regList).getD [])
  | some (.reg r), _ => s.setReg r x
  | _, .mem => { s with mem := x }
  | _, t => if t.isFlags then { s with flags := x } else s

/-- The registers of mask `m` set to `poison`. -/
def LocState.clobberMask (s : LocState) (m : RegMask) : LocState :=
  if m.isEmpty then s else
  { s with regs := s.regs.mapIdx fun i x => if m.hasReg i then .poison else x }

/-- The register home of value `id`, if any. -/
def LocCtx.regOf (lc : LocCtx) (id : ID) : Option Nat :=
  match lc.home id with
  | some (.reg r) => some r
  | _ => none

/-- What value `v`'s op destroys besides its result (see the module comment). -/
def LocState.clobber (lc : LocCtx) (s : LocState) (v : Value) : LocState :=
  let ri := v.op.regInfo
  let s := s.clobberMask ri.clobbers
  let arg (b : Bool) (i : Nat) (s : LocState) : LocState :=
    if !b then s else
    match v.args[i]?.bind lc.regOf with
    | some r => s.setReg r .poison
    | none => s
  let s := arg ri.clobbersArg0 0 (arg ri.clobbersArg1 1 s)
  let s := match (lc.temps[v.id]?).join with
    | some r => s.setReg r .poison
    | none => s
  if v.op.clobberFlags then { s with flags := .poison } else s

/-- Type `t` is a signed integer type. -/
def typeSigned (tabs : Tables) (t : TypeRef) : Bool :=
  match tabs.type? t with
  | some d => d.kind == .INT8 || d.kind == .INT16 || d.kind == .INT32 || d.kind == .INT64 ||
    d.kind == .INT
  | none => false

/-- The register holding value `id` has the upper bits of a sign extension of its low bits
(`MOVDreg`/`MOVDnop` copy them, `arm64Op`): a `LoadReg` loads by its type (`loadByType`: a signed
narrow integer type sign-extends), a `Copy` is a register move (`MOVD`) and has its argument's
bits; any other value as under `runL` (`Arm64.signExtendsIn`: its op, or a selector of `LDPSW`). -/
def LocCtx.signOf (lc : LocCtx) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, id =>
    match lc.ctx.f.value? id with
    | some u =>
      match u.op with
      | .LoadReg => typeSigned lc.ctx.tabs u.type
      | .Copy => match u.args[0]? with
        | some a => lc.signOf n a
        | none => false
      | _ => Arm64.signExtendsIn lc.ctx.f.value? u
    | none => false

/-- `MOVDreg x`/`MOVDnop x` (`arm64Op`) with the upper bits of `x`'s register (`LocCtx.signOf`). -/
def movdLoc (lc : LocCtx) (v : Value) (argv : List Val) (ty : Ty) : Val :=
  match argv with
  | [a] =>
    let sx := (v.args[0]?.map (lc.signOf lc.ctx.f.valueTab.size)).getD false
    match a with
    | .int _ x => Arm64.res ty (if sx then x.signExtend 64 else x.setWidth 64)
    | a => Arm64.regVal ty a
  | _ => .poison

/-- Run value `v` on the state `s`. -/
def stepLoc (env : Env) (lc : LocCtx) (s : LocState) (v : Value) : Res LocState :=
  if v.op == .Phi then
    if v.args.all (lc.home · == lc.home v.id) then .ok s
    else .stuck s!"phi v{v.id}: an argument has another home"
  else do
    let argv ← v.args.toList.mapM (s.read lc)
    let ty := lc.ty v.id
    let md := LMode.loc lc.ctx.f
    let r ← match v.op, argv with
      | .LoadReg, [x] | .StoreReg, [x] => pure x
      | .LoadReg, _ | .StoreReg, _ => .stuck s!"v{v.id}: {v.op.name} without one argument"
      | .ARM64MOVDreg, _ | .ARM64MOVDnop, _ => pure (movdLoc lc v argv ty)
      | _, _ => evalOpL md.faulting env lc.ctx s.fr v argv ty
    pure ((s.clobber lc v).write lc v.id (md.retype ty r))

/-- Run the values of block `b` in order. -/
def enterBlockLoc (env : Env) (lc : LocCtx) (s : LocState) (b : Block) : Res LocState := do
  let mut s := s
  for id in b.values do
    match lc.ctx.f.value? id with
    | none => .stuck s!"v{id} is not in the function"
    | some v => s ← stepLoc env lc s v
  return s

/-- Control `c` read from its home; a `MakeResult` is its arguments read from their homes. -/
def LocState.control (lc : LocCtx) (s : LocState) (c : ID) : Res Val :=
  match lc.ctx.f.value? c with
  | some v =>
    if v.op == .MakeResult then do
      let xs ← v.args.toList.mapM (s.read lc)
      pure ((LMode.loc lc.ctx.f).retype (lc.ty c) (Val.tuple xs))
    else s.read lc c
  | none => .stuck s!"control v{c} is not in the function"

/-- The terminator of `b` on the state `s` (`stepTermL`, its controls staged in `s.fr.regs`). -/
def stepTermLoc (lc : LocCtx) (s : LocState) (b : Block) : Res (Next × LocState) := do
  let mut regs := s.fr.regs
  for c in b.controls do
    let x ← s.control lc c
    regs := if c < regs.size then regs.set! c (some x) else regs
  let s := { s with fr := { s.fr with regs } }
  let n ← stepTermL s.fr b
  pure (n, s)

/-- Run from the entry of block `bid` with at most `fuel` block entries. -/
def runLoopLoc (env : Env) (lc : LocCtx) : Nat → LocState → ID → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, s, bid =>
    match lc.ctx.f.block? bid with
    | none => .stuck s!"b{bid} is not in the function"
    | some b =>
      match enterBlockLoc env lc s b with
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
      | .ok s =>
        match stepTermLoc lc s b with
        | .ok (.goto e, s) => runLoopLoc env lc fuel s e.b
        | .ok (.ret rs m, _) => .returned rs m
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg

/-- `runCtx` for allocated code: the frame of `entryFrame`, every register `poison`. -/
def runCtxLoc (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem) (fuel : Nat) : Outcome :=
  let ctx := lc.ctx
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    let fr := entryFrame env ctx args mem
    let s : LocState := { fr, regs := Array.replicate ARM64.registers.size .poison,
                          flags := .poison, slots := [], mem := .mem fr.mem0 }
    finish env ctx.outs ctx.defers ctx.act (runLoopLoc env lc fuel s ctx.f.entry)

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.runLoc`: the outcome of running allocated `f` (L2: `regalloc`, `loop rotate`,
`trim`) on `args` from memory `mem` with at most `fuel` block entries. -/
def runLoc (env : Sem.Env) (tabs : Tables) (f : Func) (args : List Sem.Val) (mem : Sem.Mem)
    (fuel : Nat) : Sem.Outcome :=
  Sem.runCtxLoc env (Sem.LocCtx.make tabs f) args mem fuel

end GoFV.SSA
