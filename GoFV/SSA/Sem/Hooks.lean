import GoFV.SSA.Sem.Inject
import GoFV.SSA.Sem.Run

variable [GoFV.SSA.Sem.Addrs]

/-!
# Runtime hooks: the trusted runtime boundary of `runMach` (`docs/plans/semantics3.md` §6)

`runMach H` hands the machine to `H.call` whenever the PC is at an address with no code. This
module gives the hooks for the runtime entry points compiled Go code calls on linux/arm64. Their
behaviour is **trusted** (the runtime is not compiled by the pipeline); each is either Phase 1's
contract of the entry point lifted through the ABI, or the runtime's assembly behaviour stated on
the machine:

| Entry point | Hook |
| --- | --- |
| any entry point with a Phase 1 contract (`Env.runtime`: allocation, `memmove`, `memequal`, `concatstring*`, `convT*`, `growslice`, `panicdivide`, `panicshift`, `gopanic`, …) | `liftContract`: the Go-typed arguments read from their ABI registers and stack slots (`ABIParam.regs`: `abi.RegIndex`, integer `R0`–`R15` then floating `F0`–`F15`; stack slots at `SP + offset`, the offsets including arm64's fixed frame word), the memory pulled back through `ι` from the blocks the arguments reach (`Layout.pull`), the contract run, its memory pushed forward (`Layout.pushWrites`, new heap blocks recorded in the allocator table), every register a call clobbers (`R0`–`R17`, `R19`–`R27`, `V0`–`V31`) and the flags overwritten with garbage (`clobber`), the results written to their ABI locations, and the PC set to `X30`; a contract that panics is `panicked` with the contract's `Panic` |
| `runtime.morestack`, `runtime.morestack_noctxt` (prologue slow path) | `newstack` grows the stack in place (`δ = 0`: nothing moves): `stackguard0` (`16(g)`) lowered by `growBy` bytes, no lower than `stack.lo` (`0(g)`) + `StackGuard`; `gogo` resumes after the `BL` with `X30` = the `R3` the prologue saved, `SP`, `R26`, `R28`, `R29` as at the call; every other register and the flags garbage. Stuck when the stack cannot grow |
| `runtime.gcWriteBarrier<n>` | Phase 1's `WbPre` buffer: `R25` = the address of `8n` buffer bytes (`Layout`'s `wbuf`), `R27` and the flags garbage, other registers preserved |
| `runtime.panicBounds` | `panicBounds64` (`runtime/panic.go:211-236`): the caller's `PCDATA_PanicBounds` value at `X30 - 1` (`pcvalue`), `abi.BoundsDecode`, `x`/`y` from `R0`–`R15` or constants: `panicked (.bounds kind x y)` with `kind` the `ssa.BoundsKind` (`2·code`, `+1` when unsigned; 16 for `BoundsConvert`) (`boundsPanic`) |

A load or store in the nil page is handled by `runMach` itself (`sigpanic`: `panicked nilDeref`).
Not modelled (no hook: such a call is `stuck`): the defer machinery (`deferproc*`,
`deferreturn`, `gorecover`: they walk the goroutine's frames and run deferred closures),
calls of runtime entry points through function values, asynchronous preemption, stack moves
(`δ ≠ 0`), the garbage collector (heap objects are never freed or moved).

Hooks are functions of the machine state (`Hooks.call : MState → Option HookOut`): the allocator
state lives in machine memory (`Layout.rt`), and the program's static information (code ranges,
the callee ABIs each function's SSA records, its `PCDATA_PanicBounds` table) is `RtInfo`.
-/

namespace GoFV.Arm64

open GoFV.SSA GoFV.SSA.Sem

/-- A hook's effect before it is applied: the registers and PC (`s`) and the memory writes. -/
inductive HookRes where
  | ret (s : MState) (writes : Array (BitVec 64 × BitVec 8))
  | panicked (e : Panic) (s : MState) (writes : Array (BitVec 64 × BitVec 8))
  | stuck (msg : String)

/-- The hook outcome: the writes applied. -/
def HookRes.out : HookRes → HookOut
  | .ret s ws => .ret (s.withWrites ws)
  | .panicked e s ws => .panicked e (s.withWrites ws)
  | .stuck msg => .stuck msg

/-- Static information on a function of the program (its code and SSA). -/
structure CodeInfo where
  name : String
  entry : BitVec 64
  size : Nat
  /-- The tables and ABI assignments of the function's calls of a callee, by symbol name. -/
  callABI : String → Option (Tables × List ABIParam)
  /-- The function's `PCDATA_PanicBounds` table (`pcdata` 4), empty if none. -/
  panicBounds : ByteArray := ByteArray.empty

/-- The runtime's view of the program: the injection's layout, the functions' code, the
runtime entry points by address, Phase 1's contracts, the write-barrier buffer. -/
structure RtInfo where
  layout : Layout
  funcs : Array CodeInfo
  entry? : BitVec 64 → Option String
  env : Env
  wbuf : BitVec 64
  /-- Bytes the stack grows by at each `morestack`. -/
  growBy : Nat := 32768

/-- `StackGuard` on linux/arm64 (`internal/abi`: `928 · stackGuardMultiplier + stackSystem`). -/
def stackGuard : Nat := 928

/-- The garbage a clobbered register holds (distinct per register, never a mapped address). -/
def garbage (i : Nat) : BitVec 64 := 0xdeadbeef00000000 + BitVec.ofNat 64 i

/-- Every register a call clobbers (`R0`–`R17`, `R19`–`R27`, `V0`–`V31`) and the flags, set to
garbage; `SP`, `R18`, `R28`–`R30` kept. -/
def clobber (s : MState) : MState :=
  { s with
    x := fun i => if i.toNat ≤ 17 || (19 ≤ i.toNat && i.toNat ≤ 27) then garbage i.toNat else s.x i
    v := fun i => (garbage (32 + i.toNat)).setWidth 128
    nzcv := GoFV.SSA.Sem.Flags.ofNZCV 0b1010 }

/-- The 64-bit container of ABI register `r` (`abi.RegIndex`: below 16 integer, else floating). -/
def abiReg (s : MState) (r : Nat) : BitVec 64 :=
  if r < 16 then s.x (BitVec.ofNat 5 r) else (s.v (BitVec.ofNat 5 (r - 16))).setWidth 64

/-- `s` with ABI register `r` set to `x` (a floating register's upper bits zero). -/
def setAbiReg (s : MState) (r : Nat) (x : BitVec 64) : MState :=
  if r < 16 then s.wX (BitVec.ofNat 5 r) x else s.wV (BitVec.ofNat 5 (r - 16)) (x.setWidth 128)

/-- The Phase 1 bytes of a register piece of shape `t`: a pointer-shaped piece whose word is a
window address is that pointer's fragments (heap addresses are concrete bytes, as Phase 1
stores them); every other piece its low bytes. -/
def Layout.regBytes (L : Layout) (x : BitVec 64) (t : Ty) : Array Byte :=
  match t, L.windowPtr? x with
  | .ptr _, some p => ptrBytes p
  | t, _ => intBytes t.size x.toNat

/-- An ABI assignment of a parameter or result: its shape, its registers (`abi.RegIndex`, in
`leaves` order), its stack offset (from `SP` at the call, the fixed frame word included). -/
structure AbiSlot where
  ty : Ty
  regs : List Nat
  offset : Int

/-- The assignment of an exported `ABIParam` (its type in the tables `tabs`). -/
def AbiSlot.ofParam (tabs : Tables) (p : ABIParam) : AbiSlot :=
  ⟨tabs.ty p.type, p.regs.toList, p.offset⟩

/-- The inputs and outputs of exported ABI assignments. -/
def AbiSlot.ofParams (tabs : Tables) (ps : List ABIParam) : List AbiSlot × List AbiSlot :=
  ((ps.filter (!·.out)).map (.ofParam tabs), (ps.filter (·.out)).map (.ofParam tabs))

/-- The Go-typed arguments of a call (`ins`) read from the machine: their bytes and shapes. -/
def Layout.abiArgs (L : Layout) (s : MState) (ins : List AbiSlot) : List (Array Byte × Ty) :=
  ins.map fun p =>
    if p.regs.isEmpty then (L.pullBytes s (s.sp + BitVec.ofInt 64 p.offset) p.ty.size, p.ty)
    else
      let buf := ((leaves p.ty).zip p.regs).foldl
        (fun buf ((o, lt), r) => putBytes buf o (L.regBytes (abiReg s r) lt))
        (Array.replicate p.ty.size Byte.poison)
      (buf, p.ty)

/-- The machine word of Phase 1 bytes (`poison` and unmapped fragments: 0). -/
def Layout.wordOf (L : Layout) (s : MState) (bs : Array Byte) : BitVec 64 :=
  (List.range bs.size).foldl (fun acc i =>
    acc ||| (((L.pushByte s bs[i]!).getD 0).setWidth 64 <<< (8 * i))) 0

/-- The results `rs` (Go-typed) written to their ABI locations (`outs`): register pieces, and
stack slots at `SP + offset` as memory writes. An error if they do not match the assignments or
a result points into a block with no address. -/
def Layout.abiResults (L : Layout) (s : MState) :
    List AbiSlot → List Val → Except String (MState × Array (BitVec 64 × BitVec 8))
  | [], [] => pure (s, #[])
  | p :: ps, r :: rs => do
    let bs := encode p.ty (r.retype p.ty)
    if bs.any fun b => match b with | .frag q _ => (L.addr? s q).isNone | _ => false then
      throw "hook: a result points into a block with no address"
    if p.regs.isEmpty then
      let a := s.sp + BitVec.ofInt 64 p.offset
      let ws := (List.range bs.size).toArray.filterMap fun i =>
        (L.pushByte s bs[i]!).map fun x => (a + BitVec.ofNat 64 i, x)
      let (s', ws') ← L.abiResults s ps rs
      return (s', ws ++ ws')
    else
      let s := ((leaves p.ty).zip p.regs).foldl (fun s ((o, lt), reg) =>
        setAbiReg s reg (L.wordOf s (bs.extract o (o + lt.size)))) s
      L.abiResults s ps rs
  | _, _ => throw "hook: results do not match the ABI"

/-- Phase 1's contract `c` of a callee with ABI assignments `ins`, `outs`, lifted to the
machine (see the module comment). -/
def liftContract (L : Layout) (ins outs : List AbiSlot) (c : Contract) (s : MState) : HookRes :=
  let args := L.abiArgs s ins
  let roots := args.foldl (fun acc (bs, _) => L.pointees s bs ++ acc) []
  let m0 := L.pull s roots
  let vals := args.map fun (bs, t) => GoFV.SSA.Sem.decode bs 0 t
  let back (m : Mem) : Option (Array (BitVec 64 × BitVec 8) × MState) := do
    let ws ← L.pushWrites s m0 m
    -- the allocator table is in the writes: ι of new blocks in the state they are applied to
    return (ws, s.withWrites ws)
  match c vals none m0 with
  | .returned rs m =>
    match back m with
    | none => .stuck "hook: a block of the callee's memory has no address"
    | some (ws, s1) =>
      match L.abiResults (clobber s1) outs rs with
      | .ok (s2, ws2) => .ret { s2 with pc := s.x 30, mem := s.mem } (ws ++ ws2)
      | .error msg => .stuck msg
  | .panicked e m =>
    match back m with
    | some (ws, _) => .panicked e s ws
    | none => .panicked e s #[]
  | .stuck msg => .stuck msg

/-- Runtime entry points the compiler calls from a fixed-register op rather than an SSA call
with an `AuxCall` (`ARM64.rules`, `ARM64Ops.go`): their ABIInternal assignments.
`LoweredMemEq` (`R0`, `R1`, `R2` → `R0`) calls `runtime.memequal(a, b unsafe.Pointer, size
uintptr) bool`. -/
def fixedABI : String → Option (List AbiSlot × List AbiSlot)
  | "runtime.memequal" =>
    some ([⟨.ptr none, [0], 0⟩, ⟨.ptr none, [1], 0⟩, ⟨.int .w64, [2], 0⟩], [⟨.bool, [0], 0⟩])
  | _ => none

/-- `runtime.morestack`: grow the stack in place and resume after the call (module comment). -/
def morestackHook (R : RtInfo) (s : MState) : HookRes :=
  let g := s.x 28
  let lo := s.word g
  let guard := s.word (g + 16)
  let floor := lo + BitVec.ofNat 64 stackGuard
  if guard.toNat ≤ floor.toNat then .stuck "morestack: the stack cannot grow"
  else
    let guard' := if guard.toNat ≥ floor.toNat + R.growBy then guard - BitVec.ofNat 64 R.growBy
      else floor
    let ws := (List.range 8).toArray.map fun i =>
      (g + 16 + BitVec.ofNat 64 i, guard'.extractLsb' (8 * i) 8)
    let c := clobber s
    let keep := fun (i : Reg) => i = 26 ∨ i = 28 ∨ i = 29
    let x := fun i => if i = 30 then s.x 3 else if keep i then s.x i else c.x i
    .ret { c with x, pc := s.x 30 } ws

/-- `runtime.gcWriteBarrier<n>`: the buffer in `R25`. -/
def wbHook (R : RtInfo) (s : MState) : HookRes :=
  let x := fun (i : Reg) => if i = 25 then R.wbuf else if i = 27 then garbage 27 else s.x i
  .ret { s with x, nzcv := GoFV.SSA.Sem.Flags.ofNZCV 0b0110, pc := s.x 30 } #[]

/-- A `varint` of a pc-value table at `i`: the value and the next position. -/
def readVarint (p : ByteArray) (i : Nat) : Nat × Nat := go 10 i 0 0
where
  go : Nat → Nat → Nat → Nat → Nat × Nat
    | 0, j, v, _ => (v, j)
    | n + 1, j, v, shift =>
      let b := (p.get! j).toNat
      let v := v ||| ((b % 128) <<< shift)
      if b < 128 then (v, j + 1) else go n (j + 1) v (shift + 7)

/-- `pcvalue`: the value of pc-value table `p` at offset `target` from the function's entry
(`runtime/symtab.go` `step`; `PCQuantum` 4); `none` past the table. -/
def pcValue (p : ByteArray) (target : Nat) : Option Int := go (p.size + 1) (-1) 0 0 true
where
  go : Nat → Int → Nat → Nat → Bool → Option Int
    | 0, _, _, _, _ => none
    | n + 1, val, pc, i, first =>
      if i ≥ p.size then none else
      let (uv, j) := readVarint p i
      if uv == 0 && !first then none else
      let val := val + (if uv % 2 == 1 then -((uv / 2 : Nat) : Int) - 1 else ((uv / 2 : Nat) : Int))
      let (pcd, k) := readVarint p j
      let pc := pc + pcd * 4
      if target < pc then some val else go n val pc k false

/-- `abi.BoundsDecode` with `numBoundsCodes = 9`: code, signed, x in a register, y in a
register, x, y. -/
def boundsDecode (v : Nat) : Nat × Bool × Bool × Bool × Nat × Nat :=
  let code := v % 9
  let c := v / 9
  let xReg := c % 2 == 1
  let c := c / 2
  let yReg := c % 2 == 1
  let c := c / 2
  let (signed, x, c) := if xReg then (c % 2 == 1, (c / 2) % 16, c / 32) else (false, c % 32, c / 32)
  let y := if yReg then c % 16 else c % 32
  (code, signed, xReg, yReg, x, y)

/-- The panic of `panicBounds64` for the `PCDATA_PanicBounds` value `v` with the registers of `s`:
`abi.BoundsDecode`, `x`/`y` from `R0`–`R15` or constants, the `ssa.BoundsKind` of the code and
the signedness (`2·code`, `+1` when unsigned; `BoundsConvert`, code 8, is kind 16). -/
def boundsPanic (v : Nat) (s : MState) : Panic :=
  let (code, signed, xReg, yReg, xv, yv) := boundsDecode v
  let reg (r : Nat) := s.x (BitVec.ofNat 5 r)
  let x : Int := if xReg then (if signed then (reg xv).toInt else (reg xv).toNat) else xv
  let y : Int := if yReg then (reg yv).toInt else yv
  .bounds (if code = 8 then 16 else 2 * code + (if signed then 0 else 1)) x y

/-- `runtime.panicBounds` (module comment). -/
def panicBoundsHook (R : RtInfo) (s : MState) : HookRes :=
  let pc := s.x 30
  match R.funcs.find? fun f => f.entry.toNat < pc.toNat && pc.toNat ≤ f.entry.toNat + f.size with
  | none => .stuck "panicBounds: caller unknown"
  | some f =>
    match pcValue f.panicBounds (pc.toNat - 1 - f.entry.toNat) with
    | none => .stuck "panicBounds: no PCDATA_PanicBounds"
    | some v =>
      if v < 0 then .stuck "panicBounds: no PCDATA_PanicBounds" else
      .panicked (boundsPanic v.toNat s) s #[]

/-- The hook of runtime entry point `name` called from the state `s`. -/
def rtHookNamed (R : RtInfo) (name : String) (s : MState) : HookRes :=
  if name == "runtime.morestack" || name == "runtime.morestack_noctxt" then morestackHook R s
  else if name.startsWith "runtime.gcWriteBarrier" then wbHook R s
  else if name == "runtime.panicBounds" then panicBoundsHook R s
  else
    let ret := s.x 30
    match R.funcs.find? fun f => f.entry.toNat < ret.toNat && ret.toNat ≤ f.entry.toNat + f.size with
    | none => .stuck s!"{name}: caller unknown"
    | some f =>
      let abi := (f.callABI name).map (fun (tabs, ps) => AbiSlot.ofParams tabs ps) <|> fixedABI name
      match abi, R.env.extern name with
      | some (ins, outs), some c => liftContract R.layout ins outs c s
      | none, _ => .stuck s!"{name}: no ABI for the call in {f.name}"
      | _, none => .stuck s!"{name}: no contract"

/-- The hook at the PC of `s`, if it is a runtime entry point. -/
def rtHook (R : RtInfo) (s : MState) : Option HookRes :=
  (R.entry? s.pc).map fun name => rtHookNamed R name s

/-- The runtime hooks of a program. -/
def RtInfo.hooks (R : RtInfo) : Hooks := ⟨fun s => (rtHook R s).map HookRes.out⟩

/-! ## Witnesses -/

/-- `BoundsDecode(BoundsEncode(BoundsIndex, signed, x in R1, y in R2))`: `numBoundsCodes · c + code`
with `c = 1 | 2 | 4 | 1<<3 | 2<<7`. -/
example : boundsDecode (9 * (1 + 2 + 4 + 8 + 256) + 0) = (0, true, true, true, 1, 2) := by decide

/-- The pc-value table `02 05 00`: value 0 (`-1 + 1`) for the first 5 instructions. -/
example : pcValue ⟨#[2, 5, 0]⟩ 16 = some 0 ∧ pcValue ⟨#[2, 5, 0]⟩ 20 = none := by decide

end GoFV.Arm64
