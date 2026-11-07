import GoFV.Arm64.Exec
import GoFV.SSA.Sem.Val

/-!
# `runMach`: the machine with runtime hooks (`docs/plans/semantics3.md` §3, §5, §6)

`GoFV.Arm64.step` fetches, decodes and executes one word of the read-only `Code`. A function's
machine code also calls out of its code: `BL sym` to the runtime (`morestack`, the allocator,
the write barrier, the panicking entry points, …) and to other functions. `runMach H code ret`
runs the machine and, whenever the PC is at an address with no code, hands the state to the
runtime hooks `H` (clifv's `ArmStepX` idea): a hook returns a state to continue from (normally
at the return address in `X30`), panics, or is stuck. The hooks' behaviour is the trusted
runtime boundary of §6 (`GoFV/SSA/Sem/Hooks.lean`); everything that executes words is
`GoFV.Arm64.exec`.

* A run **returns** when the PC reaches `ret`, the caller's return address (`MachEntry`: the
  `X30` at entry, outside the code), before any fetch there.
* A load or store in the nil page (`Fault.nilPage`) is the kernel's `SIGSEGV`, which the
  runtime's `sigpanic` turns into a nil-dereference panic: `panicked .nilDeref` (trusted, §6).
* `BRK`/`UDF`, words outside the decoder's subset and PCs with neither code nor a hook are
  `stuck`; fuel counts executed words and hook calls.

The entry and exit predicates of §5 (`MachEntry`, `BodyEntry`, `MachRet`) are stated on the
machine state, in the style of clifv's `AbiEntry`/`BodyEntry`/`ArmRet`.
-/

namespace GoFV.Arm64

open GoFV.SSA.Sem (Panic)

/-- What a runtime hook does with the machine. -/
inductive HookOut where
  /-- The call returns: the machine continues from `s` (its PC normally the return address). -/
  | ret (s : MState)
  /-- The runtime panics (`runtime.panicBounds`, `gopanic`, …): the run ends. -/
  | panicked (e : Panic) (s : MState)
  /-- Outside the hook's contract. -/
  | stuck (msg : String)

/-- The runtime contract `H` of §6: the hook at a PC with no code (`none`: no hook there). The
state is the one at the call: PC the callee's address, `X30` the return address. -/
structure Hooks where
  call : MState → Option HookOut

/-- No hooks: every call out of the code is stuck. -/
def Hooks.none : Hooks := ⟨fun _ => Option.none⟩

/-- Outcome of a machine run. -/
inductive MOutcome where
  /-- The PC reached the return address. -/
  | returned (s : MState)
  | panicked (e : Panic) (s : MState)
  | stuck (msg : String)
  | outOfFuel

/-- The fault of a step as an outcome: the nil page panics (`sigpanic`), the rest is stuck. -/
def MOutcome.ofFault (s : MState) : Fault → MOutcome
  | .nilPage _ => .panicked .nilDeref s
  | .undefined w => .stuck s!"undefined instruction {w.toHex} at {s.pc.toHex}"
  | .noCode pc => .stuck s!"no code at {pc.toHex}"

def MOutcome.isReturned : MOutcome → Bool
  | .returned _ => true
  | _ => false

/-- `runMach H code ret fuel s`: run from `s` until the PC is `ret`, with at most `fuel` steps
(executed words and hook calls). -/
def runMach (H : Hooks) (code : Code) (ret : BitVec 64) : Nat → MState → MOutcome
  | 0, _ => .outOfFuel
  | n + 1, s =>
    if s.pc = ret then .returned s
    else match code s.pc with
      | some _ =>
        match step code s with
        | .ok s' => runMach H code ret n s'
        | .error f => .ofFault s f
      | none =>
        match H.call s with
        | some (.ret s') => runMach H code ret n s'
        | some (.panicked e s') => .panicked e s'
        | some (.stuck msg) => .stuck msg
        | none => .stuck s!"no code and no hook at {s.pc.toHex}"

/-! ## Entry and exit (§5) -/

/-- The 8 bytes at `a`. -/
def MState.word (s : MState) (a : BitVec 64) : BitVec 64 := (readMem s.mem a 8).cast (by omega)

/-- A call of the function at `entry` (§2, §5): the PC at the entry, `SP` 16-aligned with `room`
bytes mapped below it for the frame (outside the nil page), the return address `X30` outside
the code, and `R28` a `g` whose `stackguard0` (`16(g)`) lets the frame's stack check pass or
branch to `morestack`. Arguments and memory are related to the source by the injection
(`GoFV/SSA/Sem/LocMatch.lean`), not here. -/
structure MachEntry (code : Code) (entry : BitVec 64) (room : Nat) (s : MState) : Prop where
  pc : s.pc = entry
  spAlign : s.sp.toNat % 16 = 0
  room : 4096 + room ≤ s.sp.toNat
  lrOutside : code (s.x 30) = Option.none
  gOutside : 4096 ≤ (s.x 28).toNat

/-- After the prologue of a framed function with frame size `autosize` (`obj7.go`
`preprocess`): `SP` lowered by `autosize`, the caller's `LR` saved at `0(SP)` and its `FP` at
`-8(SP)`, `R29 = SP - 8`, `R28` unchanged. `s0` is the state at the entry. -/
structure BodyEntry (autosize : Nat) (s0 s : MState) : Prop where
  sp : s.sp = s0.sp - BitVec.ofNat 64 autosize
  lr : s.word s.sp = s0.x 30
  fp : s.word (s.sp - 8) = s0.x 29
  r29 : s.x 29 = s.sp - 8
  g : s.x 28 = s0.x 28

/-- A return to the caller of the run that started in `s0`: the PC at its return address, and
`SP`, `R28` (`g`) and `R29` (the frame pointer) as at entry. Results are in their ABI
locations, related by the value relation (`LocMatch.lean`). -/
structure MachRet (s0 s : MState) : Prop where
  pc : s.pc = s0.x 30
  sp : s.sp = s0.sp
  g : s.x 28 = s0.x 28
  fp : s.x 29 = s0.x 29

/-! ## Witnesses -/

/-- A state with every register `r`, `SP` = `sp`, PC = `pc`, zero memory. -/
def MState.const (r sp pc : BitVec 64) : MState :=
  { x := fun _ => r, sp, v := fun _ => 0, nzcv := GoFV.SSA.Sem.Flags.ofNZCV 0, pc,
    mem := fun _ => 0 }

/-- `MachEntry` is satisfiable: no code, SP = 2^20, LR = g = 2^16. -/
example : MachEntry (fun _ => Option.none) 0x1000 4096 (MState.const 0x10000 0x100000 0x1000) where
  pc := rfl
  spAlign := by decide
  room := by decide
  lrOutside := rfl
  gOutside := by decide

/-- A run of no code whose PC is already the return address returns. -/
example : (runMach Hooks.none (fun _ => Option.none) 0x2000 1
    (MState.const 0 0x100000 0x2000)).isReturned = true := rfl

/-- `MachRet` holds of the entry state with the PC at its own `X30`. -/
example : MachRet (MState.const 0x2000 0x100000 0x1000) (MState.const 0x2000 0x100000 0x2000) where
  pc := rfl
  sp := rfl
  g := rfl
  fp := rfl

/-- `RET` (`d65f03c0`) from the entry returns to `X30`: one step of `runMach`. -/
example : (runMach Hooks.none (fun a => if a = 0x1000 then some 0xd65f03c0 else Option.none)
    0x2000 2 (MState.const 0x2000 0x100000 0x1000)).isReturned = true := by decide

end GoFV.Arm64
