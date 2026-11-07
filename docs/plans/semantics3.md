# Plan: machine-level semantics for Phase 3 (genssa, assembly, object code)

Status: plan (milestone I6 #552, tracking #546). Step survey: `docs/PASSES3.md`. Lowered SSA
semantics and its three forms: `docs/plans/semantics2.md` (`runL`, `runSched`, `runLoc`).
Source of truth for the machine side: what the pinned compiler emits
(`compile/internal/arm64/ssa.go`, `internal/obj/arm64/{obj7,asm7}.go`), the Arm ARM ASL of
those instructions, and the runtime that interprets the metadata (`runtime/*.go`,
`runtime/*_arm64.s`). Paths as in `docs/PASSES3.md`. clifv (eth-act/clifv,
`/home/kev/work/fv-compiler-rust`) is discussed as an option and a design reference from its
documentation only; no code from it is imported or copied while #415 (licence) is open.

## 1. Forms and their semantics

Phase 2 ends with **L2**, allocated SSA under `runLoc` (a register file by Go's dense register
number, the flags register, abstract stack slots `LocalSlot → Val`, Phase 1's block memory with
provenance). Phase 3 adds four forms:

| Form | Produced by (`docs/PASSES3.md`) | What changes | Semantics |
| --- | --- | --- | --- |
| **L2f**, framed SSA | A1–A3 (`AllocFrame`, MergeLocals) | every slot and every named auto has a byte range in one frame per activation; merged autos share ranges | `runFrame` (§4.2): `runLoc` with slots and autos as bytes of a single frame block |
| **P0–P2**, Prog lists | C1–C6 (`genssa`), D2 (`progedit`), D3 (`preprocess`) | instructions over obj registers; control by Prog identity; symbolic autos/params (P0, P1) or an explicit frame and prologue (P2); R27 scratch | `runProg` (§7): an ARM64 machine whose program counter is a Prog, with a flat memory |
| **M**, machine code | D4–D7 (`span7`, `MarkUnsafePoints`, `linkpcln`) | words, pools, veneers, relocations, pc tables | `runMach` (§3): the same machine fetching and decoding words |
| **D**, **O** | E1–E2, F1–F2 | debug information, object file | none: parity only (§6) |

Why two machine-level semantics: `runProg` lets `genssa` be proven without the encoder (a Prog's
meaning is given directly), and `runMach` lets the encoder be validated without porting its
case analysis into a proof (§3 (c)). Both share one instruction semantics, so the step between
them is a decoder check, not a second semantics.

## 2. Correctness criterion

As in Phases 1–2 (`docs/PLAN.md` §1): every returning or panicking run of the source is, up to
refinement, a run of the target; stuck and out-of-fuel source runs carry no obligation. Across
the machine boundary the target's outcome is read through the ABI:

- **returned**: the machine reaches the caller's return address with SP, R28 (`g`) and R29 (FP)
  as at entry; each result is in its ABI register (or result stack slot) and relates to the
  source result by the value relation (§4.1); memory relates through the injection (§4.3).
- **panicked**: the machine enters a panicking runtime entry through a call hook (§6):
  `panicBounds` with the PCDATA-decoded `(kind, x, y)`, `panicdivide`, `panicshift`,
  `gopanic(v)`, …, matching Phase 1's `Panic` (`GoFV/SSA/Sem/Val.lean:349`); a load or store in
  the nil page `[0, 4096)` is `panicked nilDeref` (the kernel's SIGSEGV, delivered to
  `sigpanic`, which panics with a nil dereference; trusted, §6).
- stuck, out of fuel: no claim.

Target theorem (I7), composing with Phase 2's `verifiedPipelineFull_refines`
(`docs/PASSES2.md` §0):

```
theorem objFull_refines
    (h : verifiedObj env f = .ok r) (hv : r.verified = true)
    (hP : VPre₃ …) (hE : MachEntry r.obj link s args mem) (hd : (run e env.tables f args mem fuel).Defined) :
    ∃ n, MachRefines (run e env.tables f args mem fuel) (runMach H r.obj link n s)
```

`VPre₃` is Phase 2's precondition plus the machine-level ones: `MachEntry` (the code of the
function and the read-only constant symbols at their linked addresses, SP 16-aligned with room
for the frame below it, LR outside the code, R28 a valid `g`, arguments in their ABI locations,
the injection of §4.3 relating the source's memory to the machine's), and the runtime contract
`H` of §6. A function the Phase 3 validators reject is reported unverified, as in Phase 2.

## 3. Machine semantics: options

The machine state, whichever option: X0–X30, SP, V0–V31 (128 bits), NZCV, PC, a flat
little-endian byte memory `BitVec 64 → BitVec 8`, code in a separate read-only map (Go code is
never written), FPCR fixed to 0 (round to nearest, no flush-to-zero, no default NaN: what Linux
gives a process; Go never writes FPCR), no FPSR (no Go code reads it; `asyncPreempt` saves and
restores it), one core. These are the same modelling choices clifv's `FV/Arm` makes
(`docs/decisions/arm-model.md` there), which keeps option (b) open.

### (a) Our own ARM64 instruction semantics over the emitted subset

`GoFV.Arm64`: a structured instruction type `Insn` covering what the compiler and the
assembler emit (I1's `oplook` histogram gives the list; the C3 family table of
`docs/PASSES3.md` gives the shapes: integer ALU with shifted/extended operands, bitfields,
MOVZ/MOVN/MOVK, conditional select/compare, scalar FP and conversions, loads/stores with all
addressing modes including pre/post-index and pairs of X/W/S/D/Q registers, `LDAR`/`STLR`,
`LDAXR`/`STLXR`, the LSE `SWPAL`/`LDADDAL`/`CASAL`/`LDCLRAL`/`LDORAL`, `CNT`/`UADDLV`, `DMB`,
`PRFM`, `HINT`, branches `B`/`BL`/`BR`/`BLR`/`RET`/`B.cond`/`CBZ`/`CBNZ`/`TBZ`/`TBNZ`, `ADR`/
`ADRP`), `exec : Insn → MState → MState`, and `decode : BitVec 32 → Option Insn` written from
the Arm ARM encoding diagrams. The data operations are **the Phase 2 definitions**:
`GoFV/SSA/Sem/Arm64/*` (`AddWithCarry`, `DecodeBitMasks`, `ConditionHolds`, the bitfield move)
and `GoFV.IEEE` already transcribe the ASL for `evalArm64`; `exec` calls them, so the per-op
agreement `evalArm64 op args = (exec (insnOf op) s).dest` is mostly unfolding.

- Checked by co-simulation under `qemu-aarch64-static`: the harness planned for H6 (#384,
  `docs/plans/semantics2.md` §4 (c.2), not built yet) extended from single ops to
  `decode`+`exec` on words assembled by Go's own assembler, every `Insn` form, random register,
  flag and memory states with edge-value bias; plus a native difftest that runs whole corpus
  functions' machine code under `runMach` and natively.
- For: no licence dependency; one set of `BitVec` definitions shared by `evalArm64` and `exec`;
  only the forms Go emits (the LSE atomics, `PRFM`, `HINT` included); proofs stay at `BitVec`
  cost.
- Against: the instruction semantics stays in the trusted base, checked only by co-simulation
  (as `evalArm64` is today); writing a decoder is new work (~150 forms).

### (b) clifv's `FV/Arm` (LNSym-derived), pending #415

clifv's `FV/Arm` is LNSym's `Arm/` ported to Lean `v4.34.1` (70 modules, ~14.8k lines,
Apache-2.0 with Amazon's copyright, clifv's additions released under Apache-2.0 per its
`third_party/NOTICE-lnsym.md`), with a decoder `decode_raw_inst`, `exec_inst`, `stepi`/`run`,
memory separation lemmas and the `sym_n` symbolic-execution tactic, co-simulated against qemu
(about 350 forms) on Cranelift's encodings. Its clifv users also offer design templates that
transfer to Go: the M5 encoder round trip `decode ∘ encode` with layout and branch-range proofs,
the register-level correctness statement `RegLevelCorrect` on a machine with call and
relocation hooks (`ArmStepX`), and the entry/exit predicates `AbiEntry`, `BodyEntry`,
`StackAvail`, `ArmRet` (clifv `docs/contracts/{arm,encoder,e2e}.md`).

- For: an ASL-derived model maintained by a third party; decoding and execution exist; the
  tactic exists.
- Against: blocked on #415 (this repository has no licence; vendoring needs it, and the Amazon
  and clifv notices); its coverage is Cranelift's: the LSE atomics Go emits for the `Variant`
  ops are missing, `PRFM` is `Unimplemented`, and every Go-specific form must be co-simulated
  again on Go's encodings; a pinned `require` would bring a second IEEE core (`FV.Float`) next
  to `GoFV.IEEE` (itself ported from `FV/Float`); proofs through LNSym-style decode/execute
  cost more per instruction than `BitVec` goals (`docs/plans/semantics2.md` §4 (b).3).

### (c) Translation validation of the object code against the Prog list

Independent of the choice between (a) and (b): instead of proving `span7` (D4–D5: ~550 optab
entries, 111 `asmout` cases, constant materialisation, pools, veneers) correct, the verified
pipeline runs a checker on each function's output:

```
checkObj (progs : P2) (obj : M) : Bool
```

It recomputes nothing of `span7`'s choices; it decodes the words at each Prog's PC range with
`decode`, and checks that executing them meets the Prog's specification `progSpec p` (§7) on a
symbolic state (a constant materialisation leaves the constant in the destination; a large
offset access computes its address in R27 and accesses it; …), that branches decode to the
target Prog's PC (directly or through a veneer that preserves the condition), that pool words
are never reached (preceded by an unconditional branch or `UNDEF` and not a branch target),
that relocations name the Prog's symbol and addend at the right offsets, and that jump-table
words are the targets' PCs. Soundness, proven once:

```
checkObj_sound : checkObj p m = true → MachRefinesProg (runMach H m link) (runProg H p link)
```

This is the regalloc method of Phase 2 (`docs/plans/regalloc-check.md`): the Lean port of
`span7` is exact (byte parity, I4) but untrusted; only `decode`, `exec` and the checker's
soundness carry the proof. The same pattern validates the runtime metadata (§6): pcsp, stack
maps, unsafe points, `PCDATA_PanicBounds`.

### Recommendation: (a) with (c) now, (b) as agreement after #415

(a) keeps one set of instruction definitions for Phases 2 and 3 and needs no licence; (c)
keeps the 8,795-line assembler out of the proof. When #415 is decided, the agreement theorems
`exec_agree : decode w = some i → exec i s ≈ Arm.stepi s` (on our subset, for every form) move
our instruction semantics out of the trusted base, exactly as Phase 2's deferred (c.5) does for
`evalArm64`; that is the only part blocked on #415. It is its own issue (I6b, #555).

## 4. Relating `runLoc` to machine states

### 4.1 Values and registers

| `runLoc` | machine | relation |
| --- | --- | --- |
| register `r` (dense number, `Config.registers`) | `objNum r` → X0–X17, X19–X26, X28 (`g`), X29, X30, XZR, SP, V0–V31 | `Val.int w x` ↔ low `w` bits of the register, upper bits as `runLoc` specifies them (`movdLoc`, `signOf`: a `LoadReg` sign-extends signed narrow types, `MOVDreg` copies upper bits; `docs/plans/semantics2.md` §7), `Val.bool b` ↔ 0/1 in the low 8 bits, floats ↔ the low 32/64 bits of V, `Val.ptr p` ↔ `ι p` (§4.3), `poison` ↔ anything; tuples through `LocPair` component by component |
| `ZERO` | XZR | reads 0 |
| flags register (`Flags` shape) | NZCV | bitwise (the `Flags` record is NZCV; `flagConstant`'s packing is a rewrite-rule encoding and never reaches the machine) |
| — | X18 | never touched by Go code (platform register) |
| — | X27 = REGTMP | **unconstrained** at every value boundary: emitter and assembler scratch (nil checks, atomics, jump tables, large immediates and offsets), clobbered by `asyncPreempt` |
| — | X16, X17 | allocatable in Go (`R16`, `R17`); X17 also the stack-check temporary in the prologue, before any value |

### 4.2 `runFrame`: slots become frame bytes (L2 → L2f)

`runLoc` keeps stack slots abstract (`LocState.slots : List (SlotKey × Val)`, a write kills
overlapping slots of the same name) and keeps named autos as Phase 1 frame blocks
(`Blk.local a k`, `Blk.temp a k`, `Blk.outargs a`). The machine has one frame. `runFrame`
is the intermediate (CompCert's Linear → Mach "stacking" step): one block `frame a` per
activation of size `stksize + maxarg`, slots and named autos stored as bytes at their
`FrameOffset` (A2), merged autos sharing bytes (A1), spill slots encoded at their types. The
proof `runFrame` ⊑ `runLoc` needs a block-level injection `frameOf : Blk → Option (Blk × Off)`
(`local a k ↦ (frame a, off k)`, `outargs a ↦ (frame a, 0)`) that is injective on live
storage: disjoint ranges for live slots (A2's checker) and non-overlapping lifetimes for merged
ones (A1's validator). Pointers into named autos become pointers into `frame a` at an offset;
`temp` blocks stay unforgeable (Phase 1's `FrameSafe` argument carries over).

### 4.3 Memory: the injection `ι`

`runFrame` memory is Phase 1's block memory; the machine's is flat. The relation is an
injection `ι : Blk → Option (BitVec 64)` (CompCert's `Mem.inject` with offsets): the frame
block `outargs a` (Phase 1's `SP`) `↦` the activation's SP after the prologue (the exported
`ABIParam.offset` of a stack argument includes arm64's fixed frame word: `main.many`'s stack
arguments have offsets 8 and 16 and are stored with `STP (R0, R16), 8(RSP)`, so the outgoing
arguments start at offset 8 in both), heap blocks `↦` the runtime's allocation addresses
(extended at each allocating call by the allocator hook), globals `↦` their linked addresses
(`link`), `nil ↦ 0`; bytes of live blocks equal machine bytes at `ι`, pointer bytes
(`Byte.frag`) equal the encoding of the injected address. `ι` must be injective on the windows
of live blocks.

**Concrete addresses (decided, I6).** Phase 1 gives every block a fixed address
(`Blk.base?`, `GoFV/SSA/Sem/Mem.lean`: heap at `(n+1)·2^40`, frames from `2^62`), observable
through `Convert` pointer → integer and back (#156), and through `Ptr.word`: a convertible
pointer loaded at pointer shape is its integer address even without `Convert`. Options were:

1. **Guard first**: the Phase 3 theorem covers functions without pointer→integer `Convert` of a
   non-nil pointer (a syntactic guard on the input; I1 measures how many corpus functions it
   excludes). Pointer comparison is by block and offset in Phase 1 and by address on the
   machine; they agree under an injective `ι`.
2. **Then parametrise**: make the address assignment a parameter of the semantics
   (`Env.addr : Blk → Option Nat` with the window and disjointness facts Phase 1 uses), prove
   the Phase 1/2 theorems for every admissible assignment, and instantiate it with `ι`. Cost:
   every lemma that unfolds `Blk.base?`/`Ptr.ofAddr` (#156's round trips).

Decision: **heap blocks keep Phase 1's addresses, frames take the guard.** The runtime hooks
(§6) allocate `heap n` at `(n+1)·2^40` (`ι .heap n = Blk.base? (.heap n)`), so a heap pointer
is the same 64-bit word in both semantics (`Ptr.word`, `Convert`, integer arithmetic within the
block) and no guard is needed for it. Frame blocks are the stack on the machine, at addresses
relative to `SP`; a function that converts a pointer to one of its frame variables to an
integer (`addrconv`) and observes the integer is excluded by option 1's guard; option 2 stays
the follow-up for frames. Globals have no Phase 1 address and sit at their linked addresses.
Stack moves (§6) change `ι` on frame blocks in the middle of a run; a `uintptr` taken earlier
is then stale on the machine, which Go permits and Phase 1 does not model, one more reason for
the guard on frames.

**Executable `ι`** (`GoFV/SSA/Sem/Inject.lean`, I6). A `Layout` of windows (globals, code
symbols, runtime entry points, the top of the stack) and the heap rule above; the allocator
table (`nextHeap`, each heap block's size) lives in the runtime's memory, so `ι` and the hooks
are functions of the machine state. `Layout.pull` reads the Phase 1 memory a runtime entry
point sees (the blocks reachable from its arguments; an aligned word holding a window address
is that pointer's fragments, heap addresses stay concrete bytes), `Layout.pushWrites` writes a
Phase 1 memory back (fragments as the injected address).

### 4.4 Control

A `runLoc` state at block `b`, before value `i`, relates to a machine state whose PC is the
first word of value `i`'s Progs (genssa's `valueToProgAfter` of value `i-1`, or `bstart[b]`),
in the activation's frame (SP = the frame base, R29 = SP − 8 saved-FP slot, X30 dead after the
prologue saved it), with every home related as in §4.1. Values that emit nothing (`Arg`,
`Select*`, `MakeResult`, `SP`, `SB`, `GetG`, `VarDef`, `VarLive`, `KeepAlive`, `WBend`,
`Copy` to the same register, …, `docs/PASSES3.md` C2/C3) are stutter steps. Block order
becomes semantic (fallthrough).

### 4.5 Sketch: the relation `LocMatch` (I6; no proof yet)

The relation of §4.1–4.4 written against the definitions that exist: `runLoc`'s state
(`GoFV/SSA/Sem/RunLoc.lean`: `LocState` with `regs : Array Val` by Go's dense register number,
`flags : Val`, `slots : List (SlotKey × Val)` latest first, `mem : Val` holding a Phase 1
`Mem`) and the machine state of §3 (a) (`GoFV/Arm64/State.lean`: `MState` with `x : Reg → BitVec
64`, `sp`, `v : Reg → BitVec 128`, `nzcv : Flags`, `pc`, `mem : BitVec 64 → BitVec 8`). It relates
L2 directly to the machine for one activation, composing the L2 → L2f step (§4.2) into the slot
clause; once `runFrame` exists the slot clause moves there and `LocMatch` becomes the composition
of `FrameMatch` (L2/L2f) and a frame-to-flat clause. Lean-style, not checked:

```
/-- What is fixed for one activation of `f`. -/
structure MatchEnv where
  lc    : LocCtx                      -- runLoc's context (homes, types, Tables)
  ι     : Blk → Option (BitVec 64)    -- §4.3; ι .nil = some 0; frame blocks of this activation ↦ sp + their offset
  sp    : BitVec 64                   -- SP after the prologue (BodyEntry); 16-aligned
  slot  : SlotKey → Option Int        -- SP-relative offset of a spill slot: autosize + FrameOffset − extrasize + slot offset (A2, §5)
  g     : BitVec 64                   -- R28 at entry
  lr fp : BitVec 64                   -- caller's return address and FP, saved at [sp] and [sp − 8]
  pcOf  : ID → Nat → BitVec 64        -- linked address of the first word of value i of block b (§4.4)

/-- Go dense register r ↦ machine register: `registers[r].objNum` (RegARM64.lean) minus REG_R0
for R0–R30 (X index), minus REG_F0 for F0–F31 (V index); ZERO and SP never hold values. -/
def objX? (r : Nat) : Option Reg
def objV? (r : Nat) : Option Reg

/-- A value and the register holding it (64-bit container). -/
def ValRel (ι) : Val → BitVec 64 → Prop
  | .poison, _        => True                              -- includes runLoc's clobbered registers
  | .int w x, r       => r.setWidth w.bits = x             -- upper bits: what runLoc's typed reads
                                                           -- (LoadReg sign, MOVDreg) observe, §4.1
  | .bool b, r        => r = (if b then 1 else 0)          -- CSET materialises 0/1 in the whole register
  | .ptr p, r         => ∃ a, ι p.blk = some a ∧ r = a + p.off
  | _, _              => False                             -- mem, tuples: never in one register

/-- Floats live in V registers as their bits (Phase 1: `.int .w32/.w64` bit patterns). -/
def FValRel : Val → BitVec 128 → Prop
  | .poison, _ => True
  | .int w x, q => q.setWidth w.bits = x
  | _, _ => False

/-- runLoc's flags value `.agg [n, z, c, v, g]` and NZCV; `g` is not machine state (Flags.lean). -/
def BitRel : Val → Bool → Prop
  | .bool b, x => b = x
  | .poison, _ => True
  | _, _ => False
def FlagsRel (f : Val) (m : Flags) : Prop :=
  ∃ n z c v g, f = .agg [n, z, c, v, g] ∧ BitRel n m.n ∧ BitRel z m.z ∧ BitRel c m.c ∧ BitRel v m.v

/-- Phase 1 bytes and machine bytes under ι (pointer fragments are bytes of the injected address). -/
def ByteRel (ι) : Byte → BitVec 8 → Prop
  | .b x, y => x = y
  | .frag p i, y => ∃ a, ι p.blk = some a ∧ y = (a + p.off).extractLsb' (8 * i) 8
  | .poison, _ => True

/-- §4.3: every byte of every live block that ι maps equals the machine byte; ι injective on the
windows of live blocks; nothing is said about machine memory outside them. -/
def MemInj (ι) (m : Mem) (mm : Memory) : Prop :=
  (∀ blk a al o, (blk, al) ∈ m.blocks → ι blk = some a → o < al.data.size →
     ByteRel ι al.data[o] (mm (a + o))) ∧ InjectiveOnLive ι m

structure LocMatch (E : MatchEnv) (s : LocState) (b : ID) (i : Nat) (m : MState) : Prop where
  regs  : ∀ r v, r ≠ zeroReg → s.regs[r]? = some v →
            (∀ k, objX? r = some k → ValRel E.ι v (m.x k)) ∧ (∀ k, objV? r = some k → FValRel v (m.v k))
  flags : FlagsRel s.flags m.nzcv
  slots : ∀ k v, s.slots.lookup k = some v → ∃ off, E.slot k = some off ∧
            BytesRel E.ι (encodeAt (E.lc.slotTy k) v) (readBytes m.mem (E.sp + off) (slotSize k))
  mem   : ∃ mm, s.mem = .mem mm ∧ MemInj E.ι mm m.mem
  frame : m.sp = E.sp ∧ m.x 29 = E.sp − 8 ∧ m.x 28 = E.g ∧
          readMem m.mem E.sp 8 = E.lr ∧ readMem m.mem (E.sp − 8) 8 = E.fp
  pc    : m.pc = E.pcOf b i
  -- unconstrained: X27 (REGTMP), X18, X30 after the prologue, the dead stack below sp − 8, FPSR
```

The simulation steps the proofs of I7 need, stated on `GoFV.Arm64.run` over the linked code
(`code : Code`, the words of the function at their addresses) and the hooks of §6:

```
-- one value: its words (none for the stutter values of §4.4)
theorem value_sim (hm : LocMatch E s b i m) (hv : stepLoc env E.lc s (b.values[i]) = .ok s')
    (hc : CodeOf code E (b, i)) :
    ∃ n m', runMach H code n m = .ok m' ∧ LocMatch E s' b (i + 1) m'
-- block end: stepTermLoc's successor is the branch target or the fall-through
theorem term_sim (hm : LocMatch E s b b.values.size m) (ht : stepTermLoc E.lc s b = .ok (.goto b', s')) … :
    ∃ n m', runMach H code n m = .ok m' ∧ LocMatch E s' b' 0 m'
-- faults: a runLoc nil dereference is the machine's nil-page fault (Fault.nilPage), which the
-- hook of §6 turns into panicked nilDeref
```

Open points for I7: the `.bool` clause asks for the whole register to be 0 or 1, which is what
Phase 2's `reg` reads a boolean as; Phase 2's `res` keeps only bit 0 at the `bool` shape, so a
producer that leaves upper bits (none known; `CSET`, `MOVBU` loads and the logical ops of two
booleans keep 0/1) would need the clause weakened to bit 0 for values that are only branched on.
The `.int` clause leaves the upper bits to `runLoc`'s typed reads, as §4.1 says; the proof of
`value_sim` for `MOVDreg` and narrow loads is where they are pinned down.

At a call, `runLoc`'s `clobber` writes `poison` into the call's clobbered registers, so the
`regs` clause holds for any values the callee hook leaves there; `slots`, `frame` and `mem`
(through the callee contract, with ι extended by the allocator hook) carry over. `pcOf` is
where P0 and M differ: on P0 it is the Prog's ID (`runProg`), on M the linked address after
`span7`, so the same `LocMatch` serves both layers of §7.

**Implemented** in `GoFV/SSA/Sem/LocMatch.lean` (I6: definitions, the I7 obligations stated as
`ValueSim`/`TermSim`/`FaultSim : Prop`, non-vacuity witnesses; no simulation proof). Changes
against the sketch, forced by the real definitions:

- `ValRel` at `.int .w64`: the register is `x`, or `x` is Phase 1's address of a pointer
  (`Ptr.word`: a convertible pointer loaded at pointer shape is its integer address) and the
  register is its injected address; `BytesRel` takes a set of 8-byte pointer words in memory for
  the same reason. With §4.3's decision (`ι .heap n = Blk.base? (.heap n)`) both coincide for
  heap pointers; they differ for frame blocks.
- `FlagsRel` accepts `poison` (`runLoc` starts with poison flags, `clobberFlags` writes poison).
- `MemInj` is a structure (`nil`, `mapped`: every live block mapped above the nil page,
  `inj`: disjoint windows, `bytes`); slots compare like registers read back at the slot's shape
  (`SlotRel`); a frameless leaf keeps LR/FP in `X30`/`X29` (`MatchEnv.framed`).
- `objX?`/`objV?` are explicit tables with lemmas equating them to `registers[r].objNum - REG_R0`
  (`REG_F0`) for every `r`: dense 0–17 → X0–X17, 18–25 → X19–X26, 26 (`g`) → X28, 27 → X29,
  28 → X30, 31–62 → V0–V31; `ZERO`, `SP`, `SB` hold no values.
- The obligations are stated over `MStar` (continuing `runMach` steps: executed words or
  returning hooks, with `MStar.runMach` relating it back to `runMach`) and `MPanics`; `ι` may
  grow (`MatchEnv.Extends`). Not stated yet: the return (`MachRet` with results in place), the
  memory of a panic, stack moves (`Extends` only grows `ι`).

## 5. ABI and frame layout (linux/arm64, ABIInternal)

Facts the proofs use, all from the pin; ABI0 (assembly functions) is reached only through the
compiler's ABI wrappers, which are ordinary compiled functions.

- **Registers.** Integer arguments and results R0–R15, floating F0–F15 (`intParamRegs`,
  `floatParamRegs`); closure context R26; `g` in R28; R29 frame pointer, R30 link register.
  **No callee-saved registers** besides SP, R28 and the FP chain (R29 is saved by every framed
  callee and restored): a call clobbers every allocatable register and the flags (the call op's
  `regInfo.clobbers`, already used by `runLoc`). Register arguments have **spill slots in the
  caller's outgoing area** (`f.RegArgs` offsets, `ssagen/ssa.go:601-617`); the callee spills
  there only on the `morestack` path and for partially live arguments (`defframe`).
- **Frame** (`internal/obj/arm64/obj7.go:520-700`, `docs/PASSES3.md` §1.3). With
  `framesize = padframe(round(maxarg) + stksize)` from `defframe`:
  `autosize = framesize + 8 + extrasize`, `extrasize ∈ {8, 16}` so that `autosize` is a multiple
  of 16 and the top of every frame is reserved for the FP its caller saved just below the
  caller's SP. The prologue stores LR at the new `0(SP)` and the caller's FP at `-8(SP)`
  (`MOVD.W R30, -autosize(RSP)`, `MOVD R29, -8(RSP)`; large frames `STP (R29, R30), -8(R20)`).
  After the prologue, addresses from high to low:

  ```
  caller SP + 8 + …        incoming stack arguments, results, register-argument spill area (caller's)
  caller SP                caller's saved LR (0(SP) of the caller's frame)
  caller SP − 8            FP saved by the caller's prologue (inside this frame's reserved extrasize)
  …                        locals (NAME_AUTO at autosize + FrameOffset − extrasize from SP)
  SP + 8 …                 outgoing arguments and spill areas for callees (maxarg)
  SP                       this function's saved LR
  SP − 8                   the caller's FP, saved by this prologue; R29 points here
  ```

  `R29 = SP − 8` after the prologue (`SUB $8, RSP, R29`), so `[R29]` is the previous FP (the FP
  chain); `NAME_PARAM` is `autosize + offset + 8` from SP, i.e. `caller SP + 8 + offset`.
  Frameless leaves (`NOFRAME`, no locals, no calls) keep LR in R30 and SP unchanged. **Below SP
  only `SP − 8` is live**: callees reserve it (their `extrasize`), the async-preemption entry
  writes at `SP − 16` and below (`runtime/preempt_arm64.s`; the signal handler's injected call
  pushes LR there); everything else below SP is dead stack, written by callees and
  `asyncPreempt`, and the relation must leave it unconstrained (clifv found its first callee
  contract unsatisfiable for exactly this reason, clifv `docs/contracts/e2e.md` "Callee contract
  with a dead stack").
- **Stack check** (D3): `stackguard0` at `16(g)`; `SP ≤ stackguard0` (or the medium/large
  variants) branches to the slow path, which spills the register arguments (`FuncInfo` spill
  records, forward order), calls `runtime.morestack_noctxt` (or `morestack` with a closure
  context), unspills and retries. The runtime also sets `stackguard0 = stackPreempt` to request
  a synchronous preemption, so this path is taken even when the stack is large enough.
- **Entry/exit predicates** (I6, `GoFV/SSA/Sem/RunMach.lean`): `MachEntry` (§2), `BodyEntry`
  (after the prologue: the frame above, saved LR/FP) and `MachRet` (PC = entry LR, SP/R28/R29
  restored), in the style of clifv's `AbiEntry`/`BodyEntry`/`ArmRet`; arguments and results in
  place are `LocMatch`'s (§4.5). `MachEntry` includes the frame-pointer chain `R29 = SP − 8`:
  epilogues do not reload the caller's FP, they recompute it from `SP`
  (`ADD $(autosize − 8), RSP, R29` before `ADD $autosize, RSP`), so a call that starts with
  another `R29` returns without `MachRet` (the machine difftest found this).

## 6. Calls, the runtime and GC metadata: trusted and proven

`runMach H` runs the machine and, at fixed points, a runtime hook from `H` (clifv's `ArmStepX`
idea). The hooks' contracts are the trusted runtime; what the compiled code must satisfy for
them to be sound is proven, mostly by validators.

| Event | Hook contract (trusted) | Obligation on the compiled code (proven / validated) |
| --- | --- | --- |
| `BL sym` / `BLR` to a Go function (calls) | Phase 1's `Contract` of the callee (`Env.runtime`, `Env.p1`) lifted through the ABI: arguments read from registers and `SP+8…` per `AuxCall`, results in registers, memory updated through `ι`, all allocatable registers, flags, R27 and the dead stack below SP havocked, SP/R28/R29 and memory above the callee's frame preserved except as the contract says; may move the stack (below) | C3 call lemmas: arguments in place; `maxarg` covers the outgoing area; only dead values in caller-saved registers |
| `BL runtime.morestack_noctxt` (prologue slow path) | returns to the function entry with registers as spilled/unspilled, the stack possibly moved and enlarged, `g` preserved | D3: spills cover every register argument; unspill restores them; the retry re-runs the check |
| stack move (inside morestack or any callee) | `copystack`: frame bytes copied verbatim to `old + δ`, **words the locals/args maps mark as pointers into the old stack adjusted by `δ`**, saved FP chain adjusted, `ι` of the goroutine's frame blocks shifted by `δ` | B1 **coverage**: every frame word that holds a live pointer into the stack at a call is in the map; pcsp (D7) gives the frame size at every return address |
| GC at a synchronous safe point (call) | heap objects unreachable from the roots (maps, stack objects, globals, registers saved by `asyncPreempt`) may be freed and reused; heap is never moved | B1 **coverage** (every live heap pointer in the frame is a root) and **validity** (every word the map lists holds nil or a valid pointer: `Needzero` zeroing, C6 spills) |
| async preemption (signal at any PC whose `PCDATA_UnsafePoint` is safe) | `asyncPreempt` saves R0–R17, R19–R26, NZCV, FPSR, F/V registers, scans this frame **conservatively**, may run other goroutines and the GC (no stack shrink while async-preempted), returns through R27 | D6: R27 dead at every safe PC; every restartable sequence (−3/−4) idempotent from its first word; write-barrier diamonds unsafe (B1) |
| `panicBounds` with `PCDATA_PanicBounds` | decodes `(code, signed, x, y)` from the PCDATA and the saved registers (`runtime/panic.go:211-236`) and panics | C3: the encoded PCDATA names the registers/constants holding the source's `x` and `y` (fails for #541's shape) |
| other panicking calls (`panicdivide`, `panicshift`, `gopanic`, …) | do not return; outcome `panicked` with Phase 1's `Panic` | C3 call lemmas |
| load/store in `[0, 4096)` | kernel SIGSEGV → `sigpanic` → `panicked nilDeref` (the nil page is unmapped: `VPre₂`) | C3: `LoweredNilCheck` is `MOVB (Rp), R27`; faulting ops fault exactly on nil bases (`runSched`'s faulting memory, `docs/plans/semantics2.md` §6) |
| write barrier (`gcWriteBarrier<n>`, `wbZero`, `wbMove`) | Phase 1's `WbPre` protocol (the buffer and flag) | B1: the barrier diamond is unsafe |
| atomics, `LDAXR`/`STLXR`, `DMB` | single core: exclusive stores succeed, barriers advance the PC (as Phase 2 §8 and clifv's trusted single-thread assumption) | C3 atomic lemmas (the LL/SC loop runs its body once) |
| open-coded defers, `deferreturn`, recover | Phase 1's contracts; re-entry for `recover` is outside the model, as in Phase 1 | parity only (A3, C2) |

Not modelled, trusted: the linker's relocation application and symbol layout, the read-only
constant symbols (`$f64.<bits>` hold their bits), the loader (code mapped read-only, nil page
unmapped), pclntab construction, DWARF and tracebacks (pcfile, pcline, pcinline, ArgInfo,
ArgLiveInfo, WrapInfo, `FuncID`/`FuncFlag` beyond what the stack walker needs), the object
writer (F1–F2).

Proven or validated: every per-function step that produces code (A1–A2 validators, C1–C6
simulation, D2–D3 refinements, D4–D5 object validator), and the metadata the hooks read: pcsp,
stack maps and stack objects, unsafe and restartable points, `PCDATA_PanicBounds`, the
morestack spill records.

**Implemented (I6).** `GoFV/SSA/Sem/RunMach.lean`: `Hooks` (`call : MState → Option HookOut`,
consulted at a PC with no code), `runMach H code ret` (returns at `ret`; a nil-page access is
`panicked nilDeref`; `BRK`/`UDF`, undecodable words and PCs with neither code nor hook are
`stuck`). `GoFV/SSA/Sem/Hooks.lean`, the trusted hooks: a runtime entry point with a Phase 1
contract (`Env.runtime`) is that contract lifted through the ABI (`liftContract`: arguments from
the call's `ABIParam` registers and stack slots, or the fixed registers of an op without
`AuxCall` such as `LoweredMemEq` → `runtime.memequal`; memory pulled back through `ι` from the
blocks the arguments reach; the contract's memory pushed forward, new heap blocks recorded in
the allocator table; every caller-saved register, `R27` and the flags overwritten with garbage;
the results written to their ABI locations; a panicking contract is `panicked` with its
`Panic`); `morestack`/`morestack_noctxt` grows the stack in place (`δ = 0`: `stackguard0`
lowered, no lower than `stack.lo + StackGuard`) and resumes after the call with `X30` = the
saved `R3`; `gcWriteBarrier<n>` returns the buffer in `R25`; `panicBounds` decodes the caller's
`PCDATA_PanicBounds` (`pcvalue` at `X30 − 1`, `abi.BoundsDecode`) and panics with
`.bounds kind x y`. Not modelled (a call is `stuck`): the defer machinery (`deferproc*`,
`deferreturn`, `gorecover`), runtime entry points called through function values, asynchronous
preemption, stack moves with `δ ≠ 0`, the collector.

## 7. `runProg` and the proof layers

`runProg H p link`: the machine of §3 with PC a Prog ID. Each Prog has a relational
specification `progSpec p : MState → MState → Prop`: its architectural effect, with R27 (and,
for calls, the hook's havoc) left free when its class may use REGTMP. `TEXT`, `PCDATA`,
`FUNCDATA`, `NOP`/`ANOP`, `HINT` are skips; P0/P1's symbolic `NAME_AUTO`/`NAME_PARAM` operands
are interpreted through the frame of §5 as `aclass` resolves them; P0's implicit prologue is a
single step establishing `BodyEntry`, P2's explicit prologue replaces it.

**Implemented (I6)** in `GoFV/SSA/Sem/RunProg.lean`: `Link` (symbol addresses, text base, Prog
ID → offset and fall-through offset, `autosize`/`extrasize`; `Link.ofProgs` for P2 with `Pc`,
`Link.byId` for P0/P1: Prog `n` at `text + 4n`), `progEffect` (an `Eff`: registers, `SP`, `V`,
flags, stores, loads, next PC, in Go's operand conventions), `Eff.apply`, the deterministic
`progStep`, the relation `progSpec` (R27 free unless the Prog names it in an operand) with
`progStep_spec : progStep L p s = .ok s' → progSpec L p s s'`, and `runProg H L ps ret` with
`runMach`'s hooks and outcomes. The PC is an address under the `Link`: the Prog executed at a
PC is the first one occupying that address; zero-size Progs never run. P0's implicit prologue
step is not modelled yet (the ID layout only makes `runProg` usable on P0/P1 lists).

| Layer | Relation | Method | Difficulty |
| --- | --- | --- | --- |
| L2 → L2f | `runFrame` ⊑ `runLoc` | A1/A2 checkers (disjoint live ranges) + injection lemma | L |
| L2f → P0 | `runProg` ⊑ `runFrame` | simulation over C2–C6: one lemma per C3 family and C4 block kind, stutter steps for no-code values; or a per-value validator of the port's output if a family resists | XL |
| P0 → P1 | `runProg` ⊑ `runProg` | D2: constant symbols, `$0 → ZR`, jump chains | M |
| P1 → P2 | `runProg` ⊑ `runProg` | D3: implicit frame step = explicit prologue; `RET` = epilogue; stack check and slow path = morestack hook | L |
| P2 → M | `runMach` ⊑ `runProg` | §3 (c) `checkObj_sound` | L |
| metadata | hook obligations | validators: pcsp, stack maps (coverage + validity), unsafe points, PanicBounds, spill records | L–XL |

`MachRefines` composes with `LayerRefines` of Phase 2 (`GoFV/Proof/Pass/PipelineFull.lean`)
through the outcome relation of §2.

## 8. Modules (proposed)

| Module | Content | Milestone |
| --- | --- | --- |
| `GoFV/Obj/{As,Reg,Addr,Prog,LSym,Parse,Print}.lean` | the Prog IR; `As` and register constants generated from `a.out.go`/`anames.go` | I2 |
| `GoFV/Gen/{MergeLocals,Frame,Liveness,ArgLive,Meta,Progs,Genssa,Arm64Value,Arm64Block,Defframe}.lean` | ports of A1–C7 | I3 |
| `GoFV/Asm/{Linkpatch,Progedit,Preprocess,Optab,Span,Encode,Unsafe,Pcln}.lean` | ports of D1–D7 (`Optab` generated) | I4 |
| `GoFV/Debug/{LocLists,Dwarf,Inline,Lines}.lean` | ports of E1–E2 | I5 |
| `GoFV/Arm64/{State,Insn,Decode,Exec}.lean` | §3 (a); **done** (#552): `MState`, `Insn` (one constructor per encoding class), `decode`, `exec`, `step`, `run` | I6 |
| `GoFV/SSA/Sem/{RunFrame,RunProg,RunMach,Inject,Hooks}.lean` | §4, §6, §7 | I6 |
| `GoFVTest/Arm64Cosim.lean`, `GoFVTest/Arm64Decode.lean`, `tools/arm64cosim`, `scripts/arm64-cosim.sh` | co-simulation under qemu and the decoder round trip on the asm sections; **done** (#552) | I6 |
| `GoFV/Proof/{Frame,Gen,Asm,ObjCheck,Meta}/*.lean` | §7 | I7 |
| (blocked on #415) `GoFV/Arm/**`, `GoFV/Proof/ArmAgree/*.lean` | §3 (b) agreement | I6b #555 |

## 9. Phasing (I6)

1. `GoFV.Arm64` state, `Insn`, `exec` for the integer and branch forms on the Phase 2
   definitions; `decode`; co-simulation on Go-assembled words.
2. Memory forms, pairs, pre/post-index, atomics (single core), FP and SIMD forms used by the
   compiler; co-simulation of every form in the I1 histogram.

   Steps 1–2 are done (#552). `scripts/arm64-cosim.sh` runs both checks on the quick corpus:
   `arm64-decode` cuts each asm section at the Progs' PCs, decodes every word and executes it
   from random states, comparing with the Prog's effect in Go's operand conventions (relocations
   applied as the linker would, `R27` free): on quick-v9, 429,386 of 429,386 Progs with code
   match, pseudo-ops cover no bytes, `WORD`/`DWORD` are their constants and the bytes after the
   last Prog are zero. `arm64-cosim` runs every distinct word (38,611; branches patched to a
   landing, memory steered into a window) at least 4 times and every form at least 256 times
   under `qemu-aarch64-static` (`tools/arm64cosim`) and through `GoFV.Arm64.step`: all 212
   instruction forms of the corpus' words (the remaining words are `UDF #0` alignment padding,
   which traps and is never executed, and 3 jump-table data words that decode to nothing), plus
   20,000 random decodable words (uniform, and corpus words with bits flipped) reaching 229
   further forms of `decode`'s domain; 287,919 cases, 0 mismatches. The corpus words found a
   decoder bug (the pair class's `opc` field); the random words found two more no corpus word
   exercises (the literal class's `opc` field, `SMULH`'s should-be-one `Ra`) and a wrong `CLS`.
3. `runMach` with hooks (calls, morestack, faults, panics); native difftest of whole corpus
   functions (Lean machine on the stock object's words vs qemu).
4. `progSpec`, `runProg`; difftest of `runProg` on P0/P1/P2 exports against `runMach`.
5. `runFrame` and the injection; semantic difftest from `runLoc` (Phase 2's sections) through
   `runFrame` and `runMach`.
6. After #415 only: agreement with an ASL-derived model (I6b).

## 10. Open questions and risks

- **Licence (#415)**: blocks only §3 (b) (I6b). Until decided, the instruction semantics is
  trusted and co-simulated, as `evalArm64` is.
- **Concrete addresses** (§4.3): guard first, parametrise later; measure the guard's cost on
  the corpus in I1.
- **Stack moves**: the stack-map coverage obligation is semantic even without GC (§6); the
  first theorem may assume no stack move (a hook premise) and discharge it with B1's validator
  later.
- **Liveness is not minimal**: the validator checks coverage and validity, not equality with
  Go's maps, so it accepts what Go emits whenever Go is right.
- **Async preemption granularity**: `runLoc` steps are whole values; preemption can happen
  between the words of one value. The R27-dead and restartable obligations are stated on M
  words, so the `runProg`/`runMach` relation must be per word, not per Prog.
- **Concurrency**: one core, exclusive stores always succeed (as Phase 2 and clifv); a
  multi-threaded statement is out of scope.
- **Floating point**: FPCR = 0 assumed; FMA contraction stays Phase 2's `Contract` (§2.1 there).
- **Package-level parity**: symbol indices, hashes and the object layout are compared
  whole-package by the driver; the Lean side stops at per-function symbol contents (I8).
- **#541**: the arm64 bounds-panic value bug makes some call sites fail the PanicBounds check
  (`docs/PASSES3.md` §3); those functions stay unverified unless the compiler is patched.
