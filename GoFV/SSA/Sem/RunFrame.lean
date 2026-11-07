import GoFV.SSA.Sem.RunLoc

/-!
# `GoFV.SSA.runFrame`: allocated SSA with a byte frame (L2f, `docs/plans/semantics3.md` §4.2)

`runLoc` (`GoFV/SSA/Sem/RunLoc.lean`, L2) keeps the stack slots abstract (`LocState.slots`, a
list of `SlotKey × Val`). `runFrame` is the same machine with the slots as **bytes of the
activation's frame**, laid out as on arm64 (CompCert's Linear → Mach "stacking" step):

* **The frame block** is Phase 1's `Blk.outargs act`. Phase 1's `SP` op is
  `.ptr ⟨.outargs act, 0⟩`, and the exported ABI offsets already include arm64's
  `FixedFrameSize` (8): a call's stack arguments are at `⟨.outargs act, p.offset⟩` and the
  machine stores them at `p.offset(RSP)` (e.g. `main.many`: offsets 8 and 16, `STP (R0, R16),
  8(RSP)`). So offsets into the block are **SP-relative offsets of the machine's SP after the
  prologue**, and the injection of §4.3 maps `outargs act` to that SP. `runFrame`'s entry
  allocates the block with `max (outargsSize tabs) lay.size` bytes, `poison` except the
  stack-assigned arguments' images (below).
* **Layout** (`FrameLayout`, an input: from the `.prog` file's frame section and TEXT Progs,
  `obj7.go` `preprocess`): `autosize` (the asm section's TEXT frame size), `extrasize`
  (`autosize - framesize - 8`, 0 for a frameless function), each variable's `FrameOffset` by
  SSA aux ref, and the frame size `autosize + 8 + argsize` (through the incoming arguments).
  A slot `k` of a `PAUTO` is at `autosize - extrasize + FrameOffset(k.name) + k.off` (the
  `NAME_AUTO` address), of a `PPARAM`/`PPARAMOUT` at `autosize + 8 + FrameOffset(k.name) +
  k.off` (`NAME_PARAM`: `+ 8` skips the caller's saved-LR word; a parameter's `FrameOffset`
  excludes `FixedFrameSize`, a register parameter's is its spill slot in the caller's spill
  area). `FrameLayout.slotOff`.
* **Disjointness from Phase 1's outgoing-argument bytes.** Phase 1 uses bytes `[0, e)` of the
  block, `e` the end of the furthest stack argument, result or register-spill area of a call
  the function makes (`callAreaEnd`; `callOp` poisons `[0, callFrame)` at each call). The locals
  lie in `[autosize - extrasize - stksize, autosize - extrasize)` with
  `autosize - extrasize - stksize = round(maxarg) + 8 ≥ e`, and parameter slots lie at or above
  `autosize + 8`: no slot overlaps those bytes. `FrameLayout.problems` checks this (and that
  every slot has an offset and fits the block) on a concrete function; the difftest reports any
  violation.
* **Slot moves.** A value whose home is slot `k` (`StoreReg`, an `Arg` of a stack-assigned
  parameter, …) **encodes** its result at the slot's type (`encode (tabs.ty k.type)`) into the
  frame block in the current memory (`storeSlot`); reading the home (`LoadReg`, …) **decodes**
  the bytes at the slot's type (`loadSlot`). A pointer is stored as its `Byte.frag`s and loads
  back as Phase 1's loads read a word (`Ptr.word`); an unwritten slot reads `poison`. Writes do
  not kill other slots: overlapping slots share bytes, where `runLoc` reads `poison` after a
  kill (a refinement of `runLoc`).
* **Stack-assigned arguments** start in the frame: the image of input parameter `i` assigned to
  the stack is at `autosize + p.offset` (entry SP + `p.offset`, where the caller stored it).
  This is the parameter's slot (`autosize + 8 + FrameOffset`: a stack parameter's
  `FrameOffset` is `p.offset - 8`), checked by `FrameLayout.problems`.
* **Memory.** The frame bytes are part of the current memory (`LocState.mem`), which every
  memory op reads and every memory result replaces; `InitMem` yields the current memory (not the
  activation's initial snapshot), so slot writes scheduled before it survive.
* **Named autos** stay Phase 1 frame blocks (`frameBlk`: `Blk.local act n`/`Blk.temp act n`), as
  in `runLoc`; their place in the frame is the injection's `frameOf`
  (`local act n ↦ (outargs act, autosize - extrasize + FrameOffset n)` for a `PAUTO`, the
  `NAME_PARAM` offset for a parameter, `outargs act ↦ (outargs act, 0)`).
* Everything else is `runLoc`'s: registers, flags, clobbers, ops, terminators, `finish`. The
  state is `LocState` with `slots` always empty.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-- The frame layout of one function (`docs/plans/semantics3.md` §5). -/
structure FrameLayout where
  /-- The asm section's TEXT frame size (`obj7.go`: `framesize + 8 + extrasize`; 0: frameless). -/
  autosize : Int
  /-- `autosize - framesize - 8` (0 when `autosize = 0`). -/
  extrasize : Int
  /-- `FrameOffset` of each variable, by SSA aux ref (`frame` section `out` lines). -/
  offsets : List (AuxRef × Int)
  /-- Bytes of the frame block the layout needs: `autosize + 8 + argsize`. -/
  size : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The class of `*ir.Name` aux `n`. -/
def nameClass? (tabs : Tables) (n : AuxRef) : Option NameClass :=
  match tabs.aux? n with
  | some { kind := .name _ cls .., .. } => some cls
  | _ => none

/-- The SP-relative offset of variable `n` of class `cls` (`NAME_AUTO`, `NAME_PARAM`). -/
def FrameLayout.varOff (lay : FrameLayout) (cls : NameClass) (n : AuxRef) : Option Int :=
  match cls, lay.offsets.lookup n with
  | .PAUTO, some o => some (lay.autosize - lay.extrasize + o)
  | .PPARAM, some o | .PPARAMOUT, some o => some (lay.autosize + 8 + o)
  | _, _ => none

/-- The SP-relative offset of slot `k` of a variable of class `cls`. -/
def FrameLayout.slotOffOf (lay : FrameLayout) (cls : NameClass) (k : SlotKey) : Option Int :=
  (lay.varOff cls k.name).map (· + k.off)

/-- The SP-relative offset of slot `k`. -/
def FrameLayout.slotOff (tabs : Tables) (lay : FrameLayout) (k : SlotKey) : Option Int :=
  (nameClass? tabs k.name).bind (lay.slotOffOf · k)

/-- The injection's placement of activation `act`'s Phase 1 frame blocks in its frame block
(§4.2, §4.3): a named variable at its `NAME_AUTO`/`NAME_PARAM` offset, the outgoing-arguments
area at 0 (it is the frame block). -/
def frameOf (tabs : Tables) (lay : FrameLayout) (act : Nat) : Blk → Option (Blk × Int)
  | .outargs a => if a == act then some (.outargs act, 0) else none
  | .local a n | .temp a n =>
    if a == act then ((nameClass? tabs n).bind (lay.varOff · n)).map (.outargs act, ·) else none
  | _ => none

/-- Value `x` stored at shape `t` at SP-relative offset `off` of activation `act`'s frame. -/
def storeSlot (act : Nat) (off : Int) (t : Ty) (x : Val) (m : Mem) : Option Mem :=
  if off < 0 then none else m.write ⟨.outargs act, BitVec.ofInt 64 off⟩ (encode t x)

/-- The value of shape `t` at SP-relative offset `off` of activation `act`'s frame (`poison`
outside the block). -/
def loadSlot (act : Nat) (off : Int) (t : Ty) (m : Mem) : Val :=
  if off < 0 then .poison else
  match m.read ⟨.outargs act, BitVec.ofInt 64 off⟩ t.size with
  | some bs => decode bs 0 t
  | none => .poison

/-- The context of `runFrame`: `runLoc`'s and the layout. -/
structure FrameCtx where
  lc : LocCtx
  lay : FrameLayout

/-- The context of `runFrame` for `f` (its export section's tables `tabs`). -/
def FrameCtx.make (tabs : Tables) (f : Func) (lay : FrameLayout) : FrameCtx :=
  { lc := LocCtx.make tabs f, lay }

/-- The offset of slot `k`, or `stuck`. -/
def FrameCtx.slotOff (fc : FrameCtx) (k : SlotKey) : Res Int :=
  match fc.lay.slotOff fc.lc.ctx.tabs k with
  | some o => .ok o
  | none => .stuck s!"slot of a{k.name}: no frame offset"

/-- The current memory. -/
def LocState.curMem (s : LocState) : Res Mem :=
  match s.mem with
  | .mem m => .ok m
  | _ => .stuck "no current memory"

/-- The contents of the home of `id`, as stored: a slot from the frame, any other home as in
`runLoc` (`LocState.raw`). -/
def LocState.rawF (fc : FrameCtx) (s : LocState) (id : ID) : Res Val :=
  match fc.lc.home id with
  | some (.slot k) => do
    let off ← fc.slotOff k
    let m ← s.curMem
    pure (loadSlot fc.lc.ctx.act off (fc.lc.ctx.tabs.ty k.type) m)
  | _ => s.raw fc.lc id

/-- The value of `id` read from its home at its shape (as `LocState.read`). -/
def LocState.readF (fc : FrameCtx) (s : LocState) (id : ID) : Res Val := do
  let x ← s.rawF fc id
  pure ((LMode.loc fc.lc.ctx.f).retype (fc.lc.ty id) x)

/-- The result `x` of value `id` written to its home: a slot into the frame, any other home as
in `runLoc` (`LocState.write`). -/
def LocState.writeF (fc : FrameCtx) (s : LocState) (id : ID) (x : Val) : Res LocState :=
  match fc.lc.home id with
  | some (.slot k) => do
    let off ← fc.slotOff k
    let m ← s.curMem
    match storeSlot fc.lc.ctx.act off (fc.lc.ctx.tabs.ty k.type) x m with
    | some m' => pure { s with mem := .mem m' }
    | none => .stuck s!"v{id}: slot of a{k.name} at {off} outside the frame"
  | _ => .ok (s.write fc.lc id x)

/-- Run value `v` on the state `s` (`stepLoc` with slots in the frame; `InitMem` is the current
memory). -/
def stepFrame (env : Env) (fc : FrameCtx) (s : LocState) (v : Value) : Res LocState :=
  let lc := fc.lc
  if v.op == .Phi then
    if v.args.all (lc.home · == lc.home v.id) then .ok s
    else .stuck s!"phi v{v.id}: an argument has another home"
  else do
    let argv ← v.args.toList.mapM (s.readF fc)
    let ty := lc.ty v.id
    let md := LMode.loc lc.ctx.f
    let r ← match v.op, argv with
      | .LoadReg, [x] | .StoreReg, [x] => pure x
      | .LoadReg, _ | .StoreReg, _ => .stuck s!"v{v.id}: {v.op.name} without one argument"
      | .ARM64MOVDreg, _ | .ARM64MOVDnop, _ => pure (movdLoc lc v argv ty)
      | .InitMem, _ => pure s.mem
      | _, _ => evalOpL md.faulting env lc.ctx s.fr v argv ty
    (s.clobber lc v).writeF fc v.id (md.retype ty r)

/-- Run the values of block `b` in order. -/
def enterBlockFrame (env : Env) (fc : FrameCtx) (s : LocState) (b : Block) : Res LocState := do
  let mut s := s
  for id in b.values do
    match fc.lc.ctx.f.value? id with
    | none => .stuck s!"v{id} is not in the function"
    | some v => s ← stepFrame env fc s v
  return s

/-- Control `c` read from its home; a `MakeResult` is its arguments read from their homes. -/
def LocState.controlF (fc : FrameCtx) (s : LocState) (c : ID) : Res Val :=
  match fc.lc.ctx.f.value? c with
  | some v =>
    if v.op == .MakeResult then do
      let xs ← v.args.toList.mapM (s.readF fc)
      pure ((LMode.loc fc.lc.ctx.f).retype (fc.lc.ty c) (Val.tuple xs))
    else s.readF fc c
  | none => .stuck s!"control v{c} is not in the function"

/-- The terminator of `b` on the state `s` (`stepTermL`, its controls staged in `s.fr.regs`). -/
def stepTermFrame (fc : FrameCtx) (s : LocState) (b : Block) : Res (Next × LocState) := do
  let mut regs := s.fr.regs
  for c in b.controls do
    let x ← s.controlF fc c
    regs := if c < regs.size then regs.set! c (some x) else regs
  let s := { s with fr := { s.fr with regs } }
  let n ← stepTermL s.fr b
  pure (n, s)

/-- Run from the entry of block `bid` with at most `fuel` block entries. -/
def runLoopFrame (env : Env) (fc : FrameCtx) : Nat → LocState → ID → Outcome
  | 0, _, _ => .outOfFuel
  | fuel + 1, s, bid =>
    match fc.lc.ctx.f.block? bid with
    | none => .stuck s!"b{bid} is not in the function"
    | some b =>
      match enterBlockFrame env fc s b with
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
      | .ok s =>
        match stepTermFrame fc s b with
        | .ok (.goto e, s) => runLoopFrame env fc fuel s e.b
        | .ok (.ret rs m, _) => .returned rs m
        | .panic e m => .panicked e m
        | .stuck msg => .stuck msg

/-- `m` with activation `ctx.act`'s frame block (`Blk.outargs`) covering the layout:
`max (outargsSize tabs) lay.size` bytes, `poison` except the image of each stack-assigned input
parameter at `autosize + p.offset` (entry SP + its ABI offset). -/
def frameAlloc (ctx : Ctx) (lay : FrameLayout) (images : Array (Array Byte)) (m : Mem) : Mem :=
  let ins := (abiParams ctx.tabs ctx.f).filter (!·.out)
  let data := (List.range ins.size).foldl (fun d i =>
      match ins[i]?, images[i]? with
      | some p, some img =>
        if p.regs.isEmpty && 0 ≤ lay.autosize + p.offset then
          putBytes d (lay.autosize + p.offset).toNat img
        else d
      | _, _ => d)
    (Array.replicate (max (outargsSize ctx.tabs) lay.size) Byte.poison)
  m.set (.outargs ctx.act) { data }

/-- `runCtxLoc` with the slots in the frame: the frame of `entryFrame` with its frame block
replaced by `frameAlloc`'s, every register `poison`. -/
def runCtxFrame (env : Env) (fc : FrameCtx) (args : List Val) (mem : Mem) (fuel : Nat) :
    Outcome :=
  let ctx := fc.lc.ctx
  if args.length != ctx.params.size then
    .stuck s!"{args.length} arguments for {ctx.params.size} parameters"
  else
    let fr0 := entryFrame env ctx args mem
    let fr := { fr0 with mem0 := frameAlloc ctx fc.lay fr0.images fr0.mem0 }
    let s : LocState := { fr, regs := Array.replicate ARM64.registers.size .poison,
                          flags := .poison, slots := [], mem := .mem fr.mem0 }
    finish env ctx.outs ctx.defers ctx.act (runLoopFrame env fc fuel s ctx.f.entry)

/-! ## Checking a layout against a function -/

/-- The end of the outgoing-argument bytes Phase 1 uses in `f`: over the calls `f` makes, the end
of each stack-assigned argument or result and of the register-spill area. -/
def callAreaEnd (tabs : Tables) (f : Func) : Int :=
  f.valueTab.foldl (fun e o =>
    match o.bind (fun v => callABI? tabs v.aux) with
    | some abi =>
      abi.params.foldl (fun e p =>
          if p.regs.isEmpty then max e (p.offset + (typeSize? tabs p.type).getD 0) else e)
        (max e (abi.spillOff + abi.spillSize))
    | none => e) 0

/-- What is wrong with layout `fc.lay` for `fc`'s function (empty: nothing): a slot home with no
offset, outside the frame block, or (a `PAUTO`'s) overlapping the outgoing-argument bytes or the
saved-FP word; a named `PAUTO` placed there by `frameOf`; a stack parameter whose `NAME_PARAM`
slot is not where its caller stores it. -/
def FrameLayout.problems (fc : FrameCtx) : List String := Id.run do
  let ctx := fc.lc.ctx
  let tabs := ctx.tabs
  let lay := fc.lay
  let lo := callAreaEnd tabs ctx.f
  let hiAuto := lay.autosize - lay.extrasize
  let size : Int := max (outargsSize tabs) lay.size
  let mut out := []
  for o in fc.lc.homes do
    match o with
    | some (.slot k) =>
      let sz : Int := (typeSize? tabs k.type).getD 0
      match lay.slotOff tabs k, nameClass? tabs k.name with
      | some off, some cls =>
        if off < 0 || size < off + sz then out := s!"slot a{k.name}+{k.off} at {off} outside [0, {size})" :: out
        if cls == .PAUTO && (off < lo || hiAuto < off + sz) then
          out := s!"auto slot a{k.name}+{k.off} at {off}+{sz} outside [{lo}, {hiAuto})" :: out
      | _, _ => out := s!"slot a{k.name}+{k.off}: no frame offset" :: out
    | _ => pure ()
  for (n, sz, _) in ctx.locals do
    if nameClass? tabs n == some .PAUTO then
      match lay.varOff .PAUTO n with
      | some off =>
        if off < lo || hiAuto < off + sz then
          out := s!"auto a{n} at {off}+{sz} outside [{lo}, {hiAuto})" :: out
      | none => pure ()
  for p in (abiParams tabs ctx.f).filter (!·.out) do
    if p.regs.isEmpty then
      match p.name.bind (lay.varOff .PPARAM ·) with
      | some off =>
        if off != lay.autosize + p.offset then
          out := s!"stack parameter at {off}, stored at {lay.autosize + p.offset}" :: out
      | none => pure ()
  return out.reverse

/-! ## Witnesses -/

/-- A layout: a 64-byte frame (`extrasize` 8), variable `a5` a `PAUTO` at `FrameOffset` −16. -/
private def exLay : FrameLayout := { autosize := 64, extrasize := 8, offsets := [(5, -16)], size := 96 }

/-- Slot `a5+8` of type `t1`. -/
private def exSlot : SlotKey := ⟨5, 1, 8, none, 0⟩

/-- `NAME_AUTO`: `autosize - extrasize + FrameOffset + off = 64 - 8 - 16 + 8`. -/
example : exLay.slotOffOf .PAUTO exSlot = some 48 := by decide

/-- A parameter's slot: `autosize + 8 + FrameOffset + off`. -/
example : exLay.slotOffOf .PPARAM exSlot = some 64 := by decide

/-- A memory holding activation 0's frame block of 64 `poison` bytes. -/
private def exMem : Mem := ({} : Mem).set (.outargs 0) { data := Array.replicate 64 .poison }

/-- Store/load round trip of an `int64` in a slot. -/
example : (storeSlot 0 48 (.int .w64) (.int .w64 0x1234) exMem).map (loadSlot 0 48 (.int .w64))
    = some (.int .w64 0x1234) := by with_unfolding_all rfl

/-- A pointer into an unforgeable frame variable is stored as its fragments and loads back. -/
example : (storeSlot 0 16 (.ptr none) (.ptr ⟨.temp 1 3, 4⟩) exMem).map (loadSlot 0 16 (.ptr none))
    = some (.ptr ⟨.temp 1 3, 4⟩) := by with_unfolding_all rfl

/-- An unwritten slot reads `poison`; a slot beyond the block cannot be written. -/
example : loadSlot 0 48 (.int .w64) exMem = .poison ∧
    storeSlot 0 60 (.int .w64) (.int .w64 1) exMem = none := ⟨by with_unfolding_all rfl, by with_unfolding_all rfl⟩

end GoFV.SSA.Sem

namespace GoFV.SSA

/-- `GoFV.SSA.runFrame`: the outcome of running allocated `f` (L2f: `runLoc` with the slots as
bytes of the frame laid out by `lay`) on `args` from memory `mem` with at most `fuel` block
entries. -/
def runFrame (env : Sem.Env) (tabs : Tables) (f : Func) (lay : Sem.FrameLayout)
    (args : List Sem.Val) (mem : Sem.Mem) (fuel : Nat) : Sem.Outcome :=
  Sem.runCtxFrame env (Sem.FrameCtx.make tabs f lay) args mem fuel

end GoFV.SSA
