import GoFV.SSA.Sem.RunLoc
import GoFV.SSA.Sem.RunMach
import GoFV.Asm.Reg

/-!
# `LocMatch`: `runLoc` states and machine states (`docs/plans/semantics3.md` §4)

The relation of §4.1–§4.4 between a state of `runLoc` (L2, `GoFV/SSA/Sem/RunLoc.lean`) and a
state of the arm64 machine (`GoFV/Arm64/State.lean`) for one activation, and the simulation
obligations of milestone I7 stated as propositions (`ValueSim`, `TermSim`, `FaultSim`). Nothing
here is proved about the compiler; the witnesses at the end show the relations are neither empty
nor trivial.

* **Registers** (`objX?`, `objV?`): Go's dense register number `r` is the machine register
  `registers[r].objNum - REG_R0` (X0–X17, X19–X26, X28 = `g`, X29, X30) or `objNum - REG_F0`
  (V0–V31); `ZERO`, `SP` and `SB` hold no value. X18 (platform) and X27 (`REGTMP`) are not Go
  registers and are unconstrained. `objX?` is an explicit table, checked against `registers` by
  `objX?_eq_objXOf?`/`objV?_eq_objVOf?`.
* **Values** (`ValRel`): an integer is the low bits of its register; a 64-bit integer may also
  be Phase 1's encoding of a pointer (`Ptr.word`: a convertible pointer is held, loaded and
  offset as its Phase 1 address, `Ptr.ofAddr` reads it back), and then the register holds the
  pointer's injected address; a boolean is 0/1; a pointer is its injected address `ι blk + off`;
  `poison` (clobbered registers) is anything.
* **Flags** (`FlagsRel`): `runLoc`'s `.agg [n, z, c, v, g]` bitwise against `NZCV` (`g` is no
  machine state); `poison` (the initial flags, `clobberFlags`) is anything.
* **Memory** (`MemInj`): CompCert's `Mem.inject` with offsets for a flat memory. `ι` maps every
  live block, `nil` to 0, live blocks to disjoint windows above the nil page that do not wrap;
  each byte of a live block is the machine byte at `ι blk + o` (`ByteRel`: pointer fragments are
  bytes of the injected address), except the bytes of chosen concrete words that encode a
  Phase 1 pointer address (`ptrWordAt?`), which hold the injected address instead (`BytesRel`).
* **Slots**: a spill slot holds its value at `sp + E.slot k`, read back at the slot's shape
  (`SlotRel`: the bytes `StoreReg` writes, compared like a register).
* **Frame** (`FrameRel`): `SP` the body's `SP`, `R28 = g`; in a framed function the caller's
  `LR`/`FP` saved at `0(SP)`/`-8(SP)` and `R29 = SP - 8` (`BodyEntry`); in a frameless leaf
  `R29` and `X30` still hold the caller's `FP` and `LR`.
* **Control**: the PC is the linked address of the next value (`MatchEnv.pcOf`).

The machine runs between related states by `MStar` (steps of `runMach`: executed words and
returning hooks), which `MStar.runMach` relates to `runMach`; `MPanics` is the machine's panic
(nil-page fault or a panicking hook), which `MPanics.runMach` relates to `runMach`.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

/-! ## The environment of one activation -/

/-- What is fixed for one activation of `f` (§4.5). -/
structure MatchEnv where
  /-- `runLoc`'s context (homes, shapes, tables). -/
  lc : LocCtx
  /-- The injection (§4.3): `nil ↦ 0`, frame blocks of this activation ↦ `sp` + their frame
  offset, heap blocks ↦ the allocator's addresses, globals ↦ their linked addresses. -/
  ι : Blk → Option (BitVec 64)
  /-- `SP` in the body (after the prologue, `BodyEntry`; at entry for a frameless function). -/
  sp : BitVec 64
  /-- The `SP`-relative offset of a spill slot (`autosize + FrameOffset − extrasize` + the slot's
  offset, §5). -/
  slot : SlotKey → Option Int
  /-- `R28` (`g`) at entry. -/
  g : BitVec 64
  /-- The caller's return address and frame pointer. -/
  lr : BitVec 64
  fp : BitVec 64
  /-- The function has a frame (`autosize ≠ 0`): `LR`/`FP` are saved at `0(SP)`/`-8(SP)`. -/
  framed : Bool
  /-- The address of the first word of value `i` of block `b` (`bstart[b]` for `i = 0`, §4.4);
  the Prog ID on P0 (`runProg`), the linked address on M. -/
  pcOf : ID → Nat → BitVec 64

/-- `E'` is `E` with `ι` extended (blocks allocated since, e.g. by the allocator hook). -/
def MatchEnv.Extends (E E' : MatchEnv) : Prop :=
  E' = { E with ι := E'.ι } ∧ ∀ b a, E.ι b = some a → E'.ι b = some a

/-- The shape a spill slot is stored at: its type's lowered shape. -/
def LocCtx.slotTy (lc : LocCtx) (k : SlotKey) : Ty := tyOfL lc.ctx.tabs 32 k.type

/-! ## Registers -/

/-- Go dense register `r` ↦ its X register: `R0`–`R17` (0–17), `R19`–`R26` (18–25), `g` = X28
(26), `R29` (27), `R30` (28); `ZERO` (29), `SP` (30), the `F` registers and `SB` have none. -/
def objX? (r : Nat) : Option GoFV.Arm64.Reg :=
  if r < 18 then some (BitVec.ofNat 5 r)
  else if r < 26 then some (BitVec.ofNat 5 (r + 1))
  else if r < 29 then some (BitVec.ofNat 5 (r + 2))
  else none

/-- Go dense register `r` ↦ its V register: `F0`–`F31` (31–62). -/
def objV? (r : Nat) : Option GoFV.Arm64.Reg :=
  if 31 ≤ r ∧ r < 63 then some (BitVec.ofNat 5 (r - 31)) else none

/-- The X register of `registers[r]` by its obj number (`REG_R0` ≤ `objNum` < `REG_R31`:
`REGZERO` = `REG_R31` and `REGSP` = `REG_RSP` are not X registers). -/
def objXOf? (r : Nat) : Option GoFV.Arm64.Reg :=
  match ARM64.registers[r]? with
  | some g =>
    if GoFV.Asm.ARM64.REG_R0 ≤ g.objNum ∧ g.objNum < GoFV.Asm.ARM64.REG_R31 then
      some (BitVec.ofInt 5 (g.objNum - GoFV.Asm.ARM64.REG_R0))
    else none
  | none => none

/-- The V register of `registers[r]` by its obj number (`REG_F0` ≤ `objNum` < `REG_F0 + 32`). -/
def objVOf? (r : Nat) : Option GoFV.Arm64.Reg :=
  match ARM64.registers[r]? with
  | some g =>
    if GoFV.Asm.ARM64.REG_F0 ≤ g.objNum ∧ g.objNum < GoFV.Asm.ARM64.REG_F0 + 32 then
      some (BitVec.ofInt 5 (g.objNum - GoFV.Asm.ARM64.REG_F0))
    else none
  | none => none

private theorem registers_size : ARM64.registers.size = 64 := rfl

private theorem objX?_lt : ∀ r, r < 64 → objX? r = objXOf? r := by decide

private theorem objV?_lt : ∀ r, r < 64 → objV? r = objVOf? r := by decide

/-- The table `objX?` is `registers[r].objNum - REG_R0` (RegARM64.lean, Asm/Reg.lean). -/
theorem objX?_eq_objXOf? (r : Nat) : objX? r = objXOf? r := by
  if h : r < 64 then exact objX?_lt r h
  else
    have h1 : ARM64.registers[r]? = none := by
      rw [Array.getElem?_eq_none_iff, registers_size]; omega
    simp only [objXOf?, h1, objX?]
    split <;> first | omega | split <;> first | omega | split <;> first | omega | rfl

/-- The table `objV?` is `registers[r].objNum - REG_F0`. -/
theorem objV?_eq_objVOf? (r : Nat) : objV? r = objVOf? r := by
  if h : r < 64 then exact objV?_lt r h
  else
    have h1 : ARM64.registers[r]? = none := by
      rw [Array.getElem?_eq_none_iff, registers_size]; omega
    simp only [objVOf?, h1, objV?]
    split <;> first | omega | rfl

/-! ## Values -/

/-- A pointer and a machine word: the injected address of its block plus its offset. -/
def PtrRel (ι : Blk → Option (BitVec 64)) (p : Ptr) (r : BitVec 64) : Prop :=
  ∃ a, ι p.blk = some a ∧ r = a + p.off

/-- A value and the X register holding it (§4.1). A 64-bit integer is the register, or, when it
is Phase 1's address of a pointer into a block (`Ptr.word`, read back by `Ptr.ofAddr` as
`Val.asPtrWord` does), the register holds that pointer's injected address. Narrower integers
are the low bits (the upper bits are what `runLoc`'s typed reads observe, pinned down by the
`MOVDreg`/narrow-load cases of `ValueSim`); a boolean is 0/1 in the whole register. -/
def ValRel (ι : Blk → Option (BitVec 64)) : Val → BitVec 64 → Prop
  | .poison, _ => True
  | .int .w64 x, r => r = x ∨ ((Ptr.ofAddr x).blk ≠ .nil ∧ PtrRel ι (Ptr.ofAddr x) r)
  | .int w x, r => r.setWidth w.bits = x
  | .bool b, r => r = if b then 1 else 0
  | .ptr p, r => PtrRel ι p r
  | _, _ => False

/-- A value and the V register holding it: floats (`.int .w32`/`.w64` bit patterns) in the low
bits. -/
def FValRel : Val → BitVec 128 → Prop
  | .poison, _ => True
  | .int w x, q => q.setWidth w.bits = x
  | _, _ => False

/-- A flag of `runLoc`'s flags value and the machine's bit. -/
def BitRel : Val → Bool → Prop
  | .bool b, x => b = x
  | .poison, _ => True
  | _, _ => False

/-- `runLoc`'s flags value `.agg [n, z, c, v, g]` (`Flags.toVal`) and `NZCV`; `g` is no machine
state (Flags.lean). `poison` flags (initial, `clobberFlags`) are related to any `NZCV`. -/
def FlagsRel : Val → Flags → Prop
  | .poison, _ => True
  | .agg [n, z, c, v, _], f => BitRel n f.n ∧ BitRel z f.z ∧ BitRel c f.c ∧ BitRel v f.v
  | _, _ => False

/-! ## Memory -/

/-- The 8 bytes at `a` as a word (`MState.word` on a bare memory). -/
def memWord (mm : GoFV.Arm64.Memory) (a : BitVec 64) : BitVec 64 :=
  (GoFV.Arm64.readMem mm a 8).cast (by omega)

/-- A Phase 1 byte and a machine byte under `ι` (a pointer fragment is the byte of the injected
address). -/
def ByteRel (ι : Blk → Option (BitVec 64)) : Byte → BitVec 8 → Prop
  | .b x, y => x = y
  | .frag p i, y => ∃ a, ι p.blk = some a ∧ y = (a + p.off).extractLsb' (8 * i) 8
  | .poison, _ => True

/-- The pointer whose Phase 1 address the 8 concrete bytes at `o` of `bs` hold (as `decodePtr`
then `Val.asPtrWord` read them), if it points into a block (not `nil`). -/
def ptrWordAt? (bs : Array Byte) (o : Nat) : Option Ptr :=
  if o + 8 ≤ bs.size then
    match bytesNat? (bs.extract o (o + 8)) with
    | some n =>
      let p := Ptr.ofAddr (BitVec.ofNat 64 n)
      if p.blk = .nil then none else some p
    | none => none
  else none

/-- The bytes `bs` of a block and the machine memory from `a`: at each offset of `W` (disjoint
8-byte words), a concrete word encoding a Phase 1 pointer address whose machine word is that
pointer's injected address; every byte outside those words by `ByteRel`. -/
def BytesRel (ι : Blk → Option (BitVec 64)) (W : Nat → Prop) (bs : Array Byte)
    (mm : GoFV.Arm64.Memory) (a : BitVec 64) : Prop :=
  (∀ o, W o → ∃ p, ptrWordAt? bs o = some p ∧ PtrRel ι p (memWord mm (a + BitVec.ofNat 64 o))) ∧
  (∀ o o', W o → W o' → o ≠ o' → o + 8 ≤ o' ∨ o' + 8 ≤ o) ∧
  (∀ i (h : i < bs.size), (∀ o, W o → ¬ (o ≤ i ∧ i < o + 8)) →
    ByteRel ι bs[i] (mm (a + BitVec.ofNat 64 i)))

/-- `ι` is injective on the windows of the live blocks of `m`: distinct blocks have disjoint
address ranges. -/
def InjectiveOnLive (ι : Blk → Option (BitVec 64)) (m : Mem) : Prop :=
  ∀ b al b' al' a a', (b, al) ∈ m.blocks → (b', al') ∈ m.blocks → b ≠ b' →
    ι b = some a → ι b' = some a' →
    a.toNat + al.data.size ≤ a'.toNat ∨ a'.toNat + al'.data.size ≤ a.toNat

/-- §4.3: the block memory `m` injected into the flat memory `mm` by `ι`. -/
structure MemInj (ι : Blk → Option (BitVec 64)) (m : Mem) (mm : GoFV.Arm64.Memory) : Prop where
  nil : ι .nil = some 0
  /-- Every live block is mapped, its window above the nil page and below `2^64`. -/
  mapped : ∀ b al, (b, al) ∈ m.blocks → ∃ a, ι b = some a ∧
    (0 < al.data.size → 4096 ≤ a.toNat) ∧ a.toNat + al.data.size ≤ 2 ^ 64
  inj : InjectiveOnLive ι m
  /-- The bytes of every live block, with a choice of pointer words per block. -/
  bytes : ∃ W : Blk → Nat → Prop, ∀ b al a, (b, al) ∈ m.blocks → ι b = some a →
    BytesRel ι (W b) al.data mm a

/-! ## The relation -/

/-- A spill slot's value of shape `t` and the machine bytes at `a`: the `t.size` bytes
(`StoreReg`'s `storeByType`), zero-extended, related as a register. -/
def SlotRel (ι : Blk → Option (BitVec 64)) (t : Ty) (v : Val) (mm : GoFV.Arm64.Memory)
    (a : BitVec 64) : Prop :=
  ValRel ι v ((GoFV.Arm64.readMem mm a t.size).setWidth 64)

/-- The activation's frame (§4.4, §5). -/
def FrameRel (E : MatchEnv) (m : GoFV.Arm64.MState) : Prop :=
  m.sp = E.sp ∧ m.x 28 = E.g ∧
  (E.framed = true → m.x 29 = E.sp - 8 ∧ m.word E.sp = E.lr ∧ m.word (E.sp - 8) = E.fp) ∧
  (E.framed = false → m.x 29 = E.fp ∧ m.x 30 = E.lr)

/-- `runLoc` state `s` before value `i` of block `b` and machine state `m` (§4.5).
Unconstrained: X18, X27 (`REGTMP`), X30 in a framed function, the stack below the frame,
memory outside live blocks and slots, the V registers' upper bits beyond a value. -/
structure LocMatch (E : MatchEnv) (s : LocState) (b : ID) (i : Nat) (m : GoFV.Arm64.MState) :
    Prop where
  regs : ∀ r v, s.regs[r]? = some v →
    (∀ k, objX? r = some k → ValRel E.ι v (m.x k)) ∧ (∀ k, objV? r = some k → FValRel v (m.v k))
  flags : FlagsRel s.flags m.nzcv
  slots : ∀ k v, s.slots.lookup k = some v → ∃ off, E.slot k = some off ∧
    SlotRel E.ι (E.lc.slotTy k) v m.mem (E.sp + BitVec.ofInt 64 off)
  mem : ∃ mm, s.mem = .mem mm ∧ MemInj E.ι mm m.mem
  frame : FrameRel E m
  pc : m.pc = E.pcOf b i

/-! ## Machine runs between related states -/

/-- One step of `runMach H code ret` that continues: a word executed, or a hook that returns.
The PC is not yet `ret`. -/
inductive MStep (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64) :
    GoFV.Arm64.MState → GoFV.Arm64.MState → Prop where
  | exec {s s'} : s.pc ≠ ret → code s.pc ≠ none → GoFV.Arm64.step code s = .ok s' →
      MStep H code ret s s'
  | hook {s s'} : s.pc ≠ ret → code s.pc = none → H.call s = some (.ret s') →
      MStep H code ret s s'

/-- Zero or more `MStep`s. -/
inductive MStar (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64)
    (s : GoFV.Arm64.MState) : GoFV.Arm64.MState → Prop where
  | refl : MStar H code ret s s
  | tail {s' s''} : MStar H code ret s s' → MStep H code ret s' s'' → MStar H code ret s s''

/-- The machine panics with `e` from `m`: a word faulting in the nil page (`sigpanic`:
`nilDeref`), or a hook that panics. -/
def MPanics (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64)
    (m : GoFV.Arm64.MState) (e : Panic) : Prop :=
  m.pc ≠ ret ∧
    ((code m.pc ≠ none ∧ ∃ a, GoFV.Arm64.step code m = .error (.nilPage a) ∧ e = .nilDeref) ∨
     (code m.pc = none ∧ ∃ m', H.call m = some (.panicked e m')))

open GoFV.Arm64 (runMach) in
theorem MStep.runMach {H code ret s s'} (h : MStep H code ret s s') (k : Nat) :
    runMach H code ret (k + 1) s = runMach H code ret k s' := by
  cases h with
  | exec hpc hc hs =>
    cases hw : code s.pc with
    | none => exact absurd hw hc
    | some w => simp [GoFV.Arm64.runMach, hpc, hw, hs]
  | hook hpc hc hh => simp [GoFV.Arm64.runMach, hpc, hc, hh]

open GoFV.Arm64 (runMach) in
/-- `MStar` is a prefix of `runMach`. -/
theorem MStar.runMach {H code ret s s'} (h : MStar H code ret s s') :
    ∃ n, ∀ k, runMach H code ret (n + k) s = runMach H code ret k s' := by
  induction h with
  | refl => exact ⟨0, fun k => by simp⟩
  | tail _ hstep ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun k => by rw [show n + 1 + k = n + (k + 1) by omega, hn, hstep.runMach]⟩

open GoFV.Arm64 (runMach) in
/-- `MPanics` is a panicking `runMach`. -/
theorem MPanics.runMach {H code ret m e} (h : MPanics H code ret m e) (k : Nat) :
    ∃ m', runMach H code ret (k + 1) m = .panicked e m' := by
  obtain ⟨hpc, ⟨hc, a, hs, rfl⟩ | ⟨hc, m', hh⟩⟩ := h
  · cases hw : code m.pc with
    | none => exact absurd hw hc
    | some w => exact ⟨m, by simp [GoFV.Arm64.runMach, hpc, hw, hs, GoFV.Arm64.MOutcome.ofFault]⟩
  · exact ⟨m', by simp [GoFV.Arm64.runMach, hpc, hc, hh]⟩

/-! ## Simulation obligations (I7; stated, not proved) -/

/-- One value: from related states, `stepLoc` of value `i` of a block of `f` is matched by
machine steps (none for the stutter values of §4.4) to a state related before value `i + 1`,
with `ι` possibly extended. For every extension of the activation's `E₀`. -/
def ValueSim (env : Env) (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64)
    (E₀ : MatchEnv) : Prop :=
  ∀ E (blk : Block) (i : Nat) (id : ID) (v : Value) (s s' : LocState) (m : GoFV.Arm64.MState),
    E₀.Extends E → E.lc.ctx.f.block? blk.id = some blk → blk.values[i]? = some id →
    E.lc.ctx.f.value? id = some v → LocMatch E s blk.id i m → stepLoc env E.lc s v = .ok s' →
    ∃ E' m', E.Extends E' ∧ MStar H code ret m m' ∧ LocMatch E' s' blk.id (i + 1) m'

/-- Block end: `stepTermLoc`'s successor is reached by the branch or the fall-through, related
before its first value. -/
def TermSim (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64)
    (E₀ : MatchEnv) : Prop :=
  ∀ E (blk : Block) (s s' : LocState) (m : GoFV.Arm64.MState) (e : Edge),
    E₀.Extends E → E.lc.ctx.f.block? blk.id = some blk →
    LocMatch E s blk.id blk.values.size m → stepTermLoc E.lc s blk = .ok (.goto e, s') →
    ∃ m', MStar H code ret m m' ∧ LocMatch E s' e.b 0 m'

/-- Faults: a value or terminator of `runLoc` that panics with `e` (a nil dereference, a
bounds check, a runtime panic) is a machine run to a state that panics with `e` (`MPanics`:
the nil-page fault that `sigpanic` turns into `nilDeref`, or the panicking hook of §6). -/
def FaultSim (env : Env) (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64)
    (E₀ : MatchEnv) : Prop :=
  (∀ E (blk : Block) (i : Nat) (id : ID) (v : Value) (s : LocState) (m : GoFV.Arm64.MState)
      (e : Panic) (mem : Mem),
    E₀.Extends E → E.lc.ctx.f.block? blk.id = some blk → blk.values[i]? = some id →
    E.lc.ctx.f.value? id = some v → LocMatch E s blk.id i m → stepLoc env E.lc s v = .panic e mem →
    ∃ m', MStar H code ret m m' ∧ MPanics H code ret m' e) ∧
  (∀ E (blk : Block) (s : LocState) (m : GoFV.Arm64.MState) (e : Panic) (mem : Mem),
    E₀.Extends E → E.lc.ctx.f.block? blk.id = some blk →
    LocMatch E s blk.id blk.values.size m → stepTermLoc E.lc s blk = .panic e mem →
    ∃ m', MStar H code ret m m' ∧ MPanics H code ret m' e)

/-! ## Witnesses -/

namespace LocMatchWitness

/-- An `int64` type (type 0). -/
def tabs : Tables :=
  { types := #[some { kind := .INT64, size := some 8, align := some 8, ptrdata := none,
                      flags := default, str := default, symName := default, tail := default }] }

/-- A spill slot of type 0. -/
def slotK : SlotKey := { name := 0, type := 0, off := 0, splitOf := none, splitOffset := 0 }

/-- `nil ↦ 0`, `heap 0 ↦ 0x10000`. -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .heap 0 => some 0x10000
  | _ => none

/-- A framed activation with `SP = 0x8000`, the slot at `16(SP)`, `g = 0x9000`, `LR = 0x40`. -/
def E : MatchEnv :=
  { lc := { ctx := { (default : Ctx) with tabs }, homes := #[], temps := #[] }, ι,
    sp := 0x8000, slot := fun _ => some 16, g := 0x9000, lr := 0x40, fp := 0, framed := true,
    pcOf := fun _ _ => 0x400000 }

/-- One live block `heap 0` of two bytes: `0x2a` and `poison`. -/
def mem : Mem := { blocks := #[(.heap 0, { data := #[.b 0x2a, .poison] })], nextHeap := 1 }

/-- `R0` holds `int64 5`, `R1` a pointer to `heap 0` at offset 1, flags of `0 - 0`, slot
`slotK` holds `int64 9`. -/
def s : LocState :=
  { fr := { regs := #[], args := [], mem0 := mem }, regs := #[.i64 5, .ptr ⟨.heap 0, 1⟩],
    flags := Flags.toVal ⟨false, true, true, false⟩, slots := [(slotK, .i64 9)], mem := .mem mem }

/-- The machine memory: `heap 0` at `0x10000`, the slot (`9`) at `0x8010`, the saved `LR` at
`0x8000` and the saved `FP` (0) at `0x7ff8`. -/
def mm : GoFV.Arm64.Memory := fun a =>
  if a = 0x10000 then 0x2a else if a = 0x8010 then 9 else if a = 0x8000 then 0x40 else 0

/-- The machine registers: `X0 = x0`, `X1 = 0x10001`, `X28 = g`, `X29 = SP - 8`. -/
def xs (x0 : BitVec 64) : GoFV.Arm64.Reg → BitVec 64 := fun k =>
  if k = 0 then x0 else if k = 1 then 0x10001 else if k = 28 then 0x9000
  else if k = 29 then 0x7ff8 else 0

def m (x0 : BitVec 64) : GoFV.Arm64.MState :=
  { x := xs x0, sp := 0x8000, v := fun _ => 0, nzcv := ⟨false, true, true, false⟩,
    pc := 0x400000, mem := mm }

theorem memInj : MemInj ι mem mm where
  nil := rfl
  mapped := by
    intro b al h
    simp only [mem, List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0x10000, rfl, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne
    simp only [mem, List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at h h'
    exact absurd (h.1.trans h'.1.symm) hne
  bytes := by
    refine ⟨fun _ _ => False, ?_⟩
    intro b al a h ha
    simp only [mem, List.mem_toArray, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases ha
    refine ⟨fun _ h => h.elim, fun _ _ h => h.elim, ?_⟩
    intro i hi _
    match i, hi with
    | 0, _ => exact (by decide : (0x2a : BitVec 8) = mm (0x10000 + BitVec.ofNat 64 0))
    | 1, _ => trivial

/-- Witness (1): `LocMatch` holds with an `int` in `R0`, a pointer into the mapped block in
`R1`, a slot holding a value, flags, and the one-block memory related by `MemInj`. -/
theorem locMatch : LocMatch E s 3 0 (m 5) where
  regs := by
    intro r v h
    match r, h with
    | 0, h =>
      cases h
      refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk; cases hk
      exact Or.inl (by decide)
    | 1, h =>
      cases h
      refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk; cases hk
      exact ⟨0x10000, rfl, by decide⟩
    | r + 2, h => simp [s] at h
  flags := ⟨rfl, rfl, rfl, rfl⟩
  slots := by
    intro k v h
    by_cases hk : k = slotK
    · subst hk
      simp only [s, List.lookup, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact ⟨16, rfl, Or.inl (by decide)⟩
    · have hb : (k == slotK) = false := by simp [hk]
      simp only [s, List.lookup, hb] at h
      cases h
  mem := ⟨mem, rfl, memInj⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by decide, by decide⟩, fun h => nomatch h⟩
  pc := rfl

/-- Witness (2): with `X0 = 6` instead of 5, `LocMatch` fails (`R0`'s `int64 5`). -/
theorem not_locMatch : ¬ LocMatch E s 3 0 (m 6) := by
  intro h
  have h0 := (h.regs 0 (.i64 5) rfl).1 0 rfl
  rcases h0 with h1 | ⟨h2, _⟩
  · exact absurd h1 (by decide)
  · exact h2 (by decide)

theorem fValRel_float : FValRel (.int .w64 0x3ff0000000000000) 0x3ff0000000000000 :=
  (by decide : (0x3ff0000000000000 : BitVec 128).setWidth 64 = 0x3ff0000000000000)

theorem not_fValRel_bool : ¬ FValRel (.bool true) 1 := id

/-- A pointer word: Phase 1's address of `heap 0` + 1 (`2^40 + 1`) in a register holding the
injected address. -/
theorem valRel_ptrWord : ValRel ι (.i64 (0x10000000001 : BitVec 64)) 0x10001 :=
  Or.inr ⟨by decide, 0x10000, by decide, by decide⟩

/-- A flags value whose `N` disagrees with `NZCV`. -/
theorem not_flagsRel :
    ¬ FlagsRel (.agg [.bool true, .poison, .poison, .poison, .poison]) ⟨false, true, true, false⟩ :=
  fun h => nomatch h.1

/-- The concrete bytes of Phase 1's address of `heap 0` + 1, stored in some block. -/
def ptrWordBytes : Array Byte := intBytes 8 0x10000000001

/-- A pointer word (`W = {0}`): the machine word at the block's address `0x20000` is the
injected address `0x10001`. -/
theorem bytesRel_ptrWord :
    BytesRel ι (· = 0) ptrWordBytes
      (fun a => if a = 0x20000 ∨ a = 0x20002 then 1 else 0) 0x20000 := by
  have h8 : ptrWordBytes.size = 8 := by simp [ptrWordBytes, intBytes]
  refine ⟨fun o ho => ?_, fun o o' ho ho' hne => absurd (ho.trans ho'.symm) hne,
    fun i hi hW => absurd ⟨Nat.zero_le i, by omega⟩ (hW 0 rfl)⟩
  subst ho
  exact ⟨⟨.heap 0, 1⟩, by decide +kernel, 0x10000, rfl, by decide⟩

/-- A hook that returns to `X30`, and one that panics. -/
def Hret : GoFV.Arm64.Hooks := ⟨fun s => some (.ret { s with pc := s.x 30 })⟩
def Hpanic : GoFV.Arm64.Hooks := ⟨fun s => some (.panicked .divide s)⟩

theorem mStar_hook : MStar Hret (fun _ => none) 0x2000
    (GoFV.Arm64.MState.const 0x2000 0x100000 0x1000)
    { GoFV.Arm64.MState.const 0x2000 0x100000 0x1000 with pc := 0x2000 } :=
  .tail .refl (.hook (by decide) rfl rfl)

/-- `MStar.runMach` on `mStar_hook`: the hook's return reaches `ret`. -/
theorem mStar_hook_runMach : ∃ n, ∀ k,
    GoFV.Arm64.runMach Hret (fun _ => none) 0x2000 (n + k)
      (GoFV.Arm64.MState.const 0x2000 0x100000 0x1000) =
    GoFV.Arm64.runMach Hret (fun _ => none) 0x2000 k
      { GoFV.Arm64.MState.const 0x2000 0x100000 0x1000 with pc := 0x2000 } :=
  mStar_hook.runMach

theorem mPanics_hook : MPanics Hpanic (fun _ => none) 0x2000
    (GoFV.Arm64.MState.const 0 0x100000 0x1000) .divide :=
  ⟨by decide, .inr ⟨rfl, _, rfl⟩⟩

theorem mPanics_hook_runMach : ∃ m', GoFV.Arm64.runMach Hpanic (fun _ => none) 0x2000 1
    (GoFV.Arm64.MState.const 0 0x100000 0x1000) = .panicked .divide m' :=
  mPanics_hook.runMach 0

/-- The obligations hold of a function with no blocks (they are not `False`). -/
def E0 : MatchEnv :=
  { lc := { ctx := default, homes := #[], temps := #[] }, ι := fun _ => none, sp := 0,
    slot := fun _ => none, g := 0, lr := 0, fp := 0, framed := false, pcOf := fun _ _ => 0 }

private theorem E0_block (E : MatchEnv) (h : E0.Extends E) (b : ID) :
    E.lc.ctx.f.block? b = none := by
  obtain ⟨h1, -⟩ := h
  rw [h1]
  rfl

theorem valueSim_empty (env : Env) (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code)
    (ret : BitVec 64) :
    ValueSim env H code ret E0 := by
  intro E blk _ _ _ _ _ _ hE hb
  rw [E0_block E hE] at hb; cases hb

theorem termSim_empty (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code) (ret : BitVec 64) :
    TermSim H code ret E0 := by
  intro E blk _ _ _ _ hE hb
  rw [E0_block E hE] at hb; cases hb

theorem faultSim_empty (env : Env) (H : GoFV.Arm64.Hooks) (code : GoFV.Arm64.Code)
    (ret : BitVec 64) :
    FaultSim env H code ret E0 := by
  refine ⟨?_, ?_⟩
  · intro E blk _ _ _ _ _ _ _ hE hb
    rw [E0_block E hE] at hb; cases hb
  · intro E blk _ _ _ _ hE hb
    rw [E0_block E hE] at hb; cases hb

end LocMatchWitness

end GoFV.SSA.Sem
