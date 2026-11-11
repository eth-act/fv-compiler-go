# Design review: spill slots of another size (genssa, #553)

Status: **P3 approved** (integrator on #553, 2026-11-11: `StkAt` per slot size, with the lemma
`StkAt_eq_of_slots8` and a STATUS line on each contract row and on `G3Inv`). Slice G66a (the
narrow spills and reloads, `FMOVS`, narrow stack arguments; `checkFrame`/`StkAt` per slot size)
is implemented (`GoFV/Gen/Check66.lean`, `GoFV/Proof/Gen/G66a.lean`, `G66.lean`; STATUS slice
G66); G66b (the elided extensions and the reloads' upper-bit entries) and the lift follow. The
class was ranked in #553 comment 6790861163, where it was marked out of scope as needing the
blob-register design of `blob-regs.md`, #689. Phase 3: `docs/plans/proofs3.md`,
`docs/plans/semantics3.md`. Probe branch `agent/slot-size-probe` (81fcb100 on main a6c37a47, not
for merge).

## 0. Summary

- **The class is narrow spill slots, nothing else.** Every slot behind `slot …: frame operand,
  size or alignment` on quick-v10 is a spill slot (or an incoming stack argument's slot) of 1, 2
  or 4 bytes holding a value of exactly its own type: `bool`/`int8`/`uint8`, `int16`/`uint16`,
  `int32`/`uint32`, `float32`. The `load shape`/`store shape` in the same functions are the
  `LoadReg`/`StoreReg` of those slots. No slot holds a value of another width (0 of 1,356 slots),
  none lacks a frame operand, none is misaligned.
- **It does not need the blob-register design.** `LocMatch`'s slot relation is already generic
  in the slot's size (`SlotRel`: the slot type's `t.size` bytes, zero-extended, related as a
  register), `runLoc` already models a narrow reload's sign or zero extension (`signOf`), and
  `EntryMatch.stack`/`ArgOK` already read a stack argument at its slot's size. What blocks is
  G2's fixed 8 bytes, threaded through the validator (`slotOK`, the spill/reload kinds) and four
  slot lemmas, and two consequences of narrow reloads in genssa (§2). `Sem.Refines`,
  `Mem.Refines`, Phase 1 and Phase 2 do not change, and neither does `LocMatch`.
- **Gain** (probe, §3): `checkG64` on quick-v10 accepts **8,914** (+653 over main's 8,261, 0
  lost); end to end **7,057** (+383 over 6,674, 0 lost; stock column 8,159, +602); full-v11
  about **+4,000 to +4,300** end to end (estimate).
- **Recommendation: P3** (§4), a Phase 3-only slice in three PRs, ≈ 4.5–6 agent-days, no new run
  premise, no new trusted contract; `StkAt`'s per-slot window becomes the slot's size, which is
  the same set for every function accepted today.

## 1. The class

### 1.1 Reasons

On main a6c37a47, `lake exe gen-check --jobs 2 --sets` on quick-v10 (9,297 functions): `checkG64`
accepts 8,261 and rejects 1,036 (as in the ranking). The class's reasons and the functions they
occur in:

| reason (`gen-check` class) | functions | where |
|---|---:|---|
| `slot n#+#: frame operand, size or alignment` | 717 | `checkFrame`'s `slotOK` (`Check2.lean`): a home slot of another size than 8 |
| `v#: load shape` | 710 | `vkind2`'s `LoadReg` of a slot whose value is not of class 64 |
| `v#: store shape` | 674 | `vkind2`'s `StoreReg` of a value not of class 64 |
| `v#: Arg width` | 37 | `argKind62`: an incoming stack argument of class < 64 |
| `v#: float spill shape`, `v#: float reload shape` | 11, 12 | `fspill63`/`freload63`: `float32` |

666 functions are rejected for these reasons only (627 for the ranking's three; with `Arg width`
and the `float32` shapes, which the ranking listed apart, 666); 717 have at least one.

### 1.2 Sub-shapes

The probe's `gen-check` writes every home slot main's `slotOK` rejects (`slotInfo`, its type's
size, its `runLoc` shape's size, operand, the values homed in it, and every `LoadReg` of it whose
type has another size). Over the 717 functions:

| slot | operand | homed value | slots | functions |
|---|---|---|---:|---:|
| 1 byte (`bool`, `uint8`, `int8`) | `NAME_AUTO` | `StoreReg` | 462 | 270 |
| 4 bytes (`int32`, `uint32`, `rune`) | `NAME_AUTO` | `StoreReg` | 416 | 249 |
| 1 byte | `NAME_PARAM` (a register argument's spill slot) | `StoreReg` | 160 | 135 |
| 4 bytes | `NAME_PARAM` | `StoreReg` | 150 | 132 |
| 2 bytes (`int16`, `uint16`) | `NAME_AUTO` | `StoreReg` | 44 | 25 |
| 2 bytes | `NAME_PARAM` | `StoreReg` | 35 | 22 |
| 4 bytes | `NAME_PARAM` (stack argument) | `Arg` | 21 | 19 |
| 1 byte | `NAME_PARAM` (stack argument) | `Arg` | 18 | 17 |
| 4 bytes, field of a struct variable (`k.off ≠ 0` or split) | `NAME_AUTO` | `StoreReg` | 16 | 7 |
| `float32` | `NAME_AUTO` | `StoreReg` | 14 | 10 |
| `float32`, field | `NAME_AUTO` | `StoreReg` | 9 | 4 |
| 1 byte, field | `NAME_AUTO` | `StoreReg` | 8 | 6 |
| `float32` | `NAME_PARAM` | `Arg` / `StoreReg` / field | 1 / 1 / 1 | 1 / 1 / 1 |

- **Size mismatches: none.** In every one of the 1,356 slots the type's size equals its `runLoc`
  shape's size (`tyOfL`), and every `LoadReg` of it has the slot's type (`mism = 0`). Go makes it
  so: `stackalloc` reuses a named slot only for a value of
  an identical type (`ssa/stackalloc.go:261`) and otherwise allocates by `v.Type`;
  `storeByType`/`loadByType` (`arm64/ssa.go:23-90`, port `Gen/Arm64Value.lean:73-105`) pick the
  instruction from the value's type. So the hypothesis "a lowered register value is a typed `Val`
  of width w while the slot holds bytes of another width" does not occur: the slot holds the
  value's own `w / 8` bytes.
- **Signedness** (slots of the gained functions): 1 byte unsigned 539, signed 18; 2 bytes 50 / 20;
  4 bytes 249 / 265; `float32` 4.
- **Operands.** No slot lacks its frame operand, none is misaligned for its size, and every
  `NAME_AUTO` slot's own bytes lie in the locals.

Samples (quick-v10 paths under `plain/`, `std/std/` written `std/`; every one is accepted by the
probe), at least two per sub-shape:

| sub-shape | functions |
|---|---|
| 1-byte spill (`NAME_AUTO`) | `std/bufio/(*Writer).WriteString`, `std/bytes/FieldsFunc`, `std/bytes/Index`, `std/bytes/ToValidUTF8` |
| 4-byte spill (`NAME_AUTO`) | `examples/floats/main/main`, `examples/structs/main/main`, `std/bytes/EqualFold`, `std/runtime/(*consistentHeapStats).acquire` |
| 1-byte spill of a register argument (`NAME_PARAM`) | `std/bufio/(*Reader).ReadSlice`, `std/bufio/(*Writer).WriteByte`, `std/bufio/ScanLines`, `std/bufio/ScanRunes` |
| 4-byte spill of a register argument | `std/bufio/(*Writer).WriteRune`, `std/bytes/(*Buffer).WriteRune`, `std/bytes/Title.func1`, `std/bytes/containsRune` |
| 2-byte spill | `std/regexp/syntax/(*parser).factor`, `std/regexp/syntax/(*parser).repeat`, `std/encoding/binary/bigEndian.AppendUint16`, `std/encoding/binary/(*littleEndian).AppendUint16` |
| narrow stack argument (`Arg`) | `std/runtime/args`, `std/runtime/fcntl`, `std/runtime/cgoNoCallback`, `std/runtime/getitab`, `std/math/Float32bits` (`float32`) |
| field slot of a struct variable | `std/runtime/(*Frames).Next`, `std/runtime/FuncForPC`, `std/runtime/fpunwindExpand` |
| `float32` spill | `test/map/main/testfloat`, `test/ken_cplx1/main/booltest` |
| extension of a narrow reload elided (§2.3) | `std/bufio/(*Writer).WriteRune`, `std/fmt/(*ss).scanBool`, `std/fmt/(*ss).scanInt`, `std/regexp/syntax/escape`, `test/ken_divconst/main/i64rand` |
| `MOVDreg`/`MOVDnop` of a narrow reload (§2.4) | `std/runtime/(*mcache).allocLarge`, `std/runtime/(*p).destroy`, `std/runtime/(*scavChunkData).alloc` |

### 1.3 The Progs

genssa (`arm64/ssa.go:615-632`) emits `storeByType` (`MOVB`, `MOVH`, `MOVW`, `FMOVS`) for a
`StoreReg` and `loadByType` for a `LoadReg` (`MOVBU`/`MOVB`, `MOVHU`/`MOVH`, `MOVWU`/`MOVW` by the
type's signedness, `bool` as `MOVBU`; `FMOVS`), at the slot's `NAME_AUTO`/`NAME_PARAM` operand,
e.g. `(*consistentHeapStats).acquire`: `MOVW R3, n-4(SP)` and `MOVWU n-4(SP), R0`. An incoming
narrow stack argument has no code (G62).

## 2. What blocks the proof at the genssa layer

### 2.1 Not the value model

- `LocMatch.slots` (`SSA/Sem/LocMatch.lean:288`) relates slot `k`'s value by
  `SlotRel E.ι (E.lc.slotTy k) v m.mem (E.sp + off)`, which is
  `ValRel ι v ((readMem mm a t.size).setWidth 64)`: the slot type's `t.size` bytes,
  zero-extended, related as a register. For a narrow integer that is `ValRel (.int w x) r ↔
  r.setWidth w.bits = x` (the low bits), for a `bool` `r ∈ {0, 1}` (one byte, zero-extended), for
  a `float32` (`.int .w32`, a bit pattern) the same as a 32-bit integer. The relation a narrow
  slot needs is already the one in `LocMatch`; only `checkFrame` keeps every slot at 8 bytes.
- `runLoc` (`RunLoc.lean:264`) moves the value (`StoreReg`, `LoadReg`) and retypes it at the
  value's type; a narrow-typed value is `.int w x` (or `.bool`, `poison`), never a pointer, so
  `SlotRel`'s pointer-word case does not arise and no `FReloadPre`-like premise is needed. A
  narrow reload's upper bits are already part of `runLoc`'s semantics: `LocCtx.signOf`
  (`RunLoc.lean:232`) makes a `LoadReg` sign-extend exactly the signed types, as
  `loadByType` does, and `MOVDreg`/`MOVDnop` read them (`movdLoc`).
- `EntryMatch.stack` (`Obj/Whole.lean:1047`) and `ArgOK` (`Gen/G62a.lean:28`) state the caller's
  bytes of a stack argument by `SlotRel` at `slotTy k`, with the bound at
  `(E.lc.slotTy k).size`: already generic.
- Phase 2 verifies these functions today (they are among the 7,895 fully verified; `store shape`
  is `checkG64`'s first reason for 382 of them, STATUS), so nothing upstream of `runLoc` is
  involved.

So the class can be solved purely inside Phase 3, without touching `Sem.Refines`,
`Mem.Refines`, Phase 1/2 semantics or `LocMatch`. A byte-level slot relation or a `SlotRel` of
"the low bytes of a register's `ValRel`" is what `SlotRel` already is.

### 2.2 What blocks: G2's 8 bytes

| place | today | needed |
|---|---|---|
| `slotOK`, `checkFrame` (`Gen/Check2.lean:229`) | type and shape of 8 bytes, 8-aligned, distinct operands | 1, 2, 4 or 8 bytes, type size = shape size, aligned to the size, the slot's own window in the locals (`NAME_AUTO`), windows of distinct slots disjoint |
| `vkind2` `StoreReg`/`LoadReg` | `MOVD`, class 64 | `storeByType`/`loadByType` of the value's type at classes 1, 8, 16, 32 |
| `fspill63`/`freload63` | `FMOVD`, class 64 | `FMOVS` at class 32 |
| `argKind62` | class 64 | any class (`cls` some) |
| `checkVars`, `checkVars49` | slot window `(o, o + 8)` | `(o, o + size)` |
| `home_slot`, `slot_sizes`, `checkFrame_spec` (`Proof/Gen/G2.lean:733`, `788`) | `(slotTy k).size = 8` | `size ∈ {1, 2, 4, 8}` |
| `slot_apart`, `slot_windows_apart` (`G2.lean:693`, `720`) | `o + 8 ≤ o' ∨ o' + 8 ≤ o` | the two slots' own sizes |
| `StkAt`, `stk_slot`, `stk_keeps` (`Proof/Gen/Stack.lean:89-171`) | each slot's window 8 bytes | each slot's window its size (§2.5) |
| `SlotInv` (`G2.lean:63`) | `Fits 64 v` | `Fits (cls (slotTy k)) v` |
| `g2_spill`/`g2_reload` (`G2.lean:833`, `940`), `g63_fspill`/`g63_freload` | 8-byte `progStep_slotStore`/`progStep_slotLoad` | `progStep_slotStoreN`/`progStep_slotLoadN` (exist, G6's frame variables), `FMOVS` |

`StkAt`'s definition is used in `Stack.lean` only (`stk_slot`, `stk_slots_frame`, `stk_keeps`);
everywhere else it is passed as a set (`SepFrom`/`SepAt`, `CoreInv`, the callee contracts). The
~25 callers of `stk_keeps` pass `slot_sizes` along (`hsz`); with a slot-size `StkAt` that argument
goes away.

### 2.3 Extensions of a narrow reload (genssa elides them)

`ssa.go:1353-1383` (port `Gen/Arm64Value.lean:337`): `MOV{B,H,W}{,U}reg x`, where `x` through
`Copy`/`MOVDreg` is a `LoadReg` of the same size and signedness, emits **no code** if the two
values share a register and `MOVD Rx, Rv` otherwise (the reload already extended). The
validator expects `MOVWU Rx, Rv` (`extOp?`, `Check3.lean:318`); this is the
`Prog #: CALL, expected MOVWU`/`MOVD, expected MOVW` the first probe (narrow spills and reloads
only, +513) left in 104 functions; with the elision 102 of them pass.
`runLoc` computes the extension of the reloaded value, the machine keeps the register, which
holds that extension by §2.4: no premise.

### 2.4 The upper-bit table across a narrow reload

`MOVDreg`/`MOVDnop` of a narrow value need the register's upper bits (`movdOK35`, G35's table
`uL35`, entry `(r, c, sg)`: `r` holds the sign or zero extension of its low `c` bits). A narrow
reload is that by `loadByType`, and `signOf` already says so; the table needs the entry
(`ldEntry35` for a `LoadReg` of a narrow type), and G35's invariant its proof (`progStep_slotLoadN`
gives the extended word). 49 functions of the first probe stopped at `MOVDnop/MOVDreg: upper bits
unknown`; with the entry 38 pass, and the elided extension (§2.3) checks against the same entry
(the validator should require the argument register's entry rather than chase the SSA chain as
`ssa.go` does, so the soundness proof reads it off the table).

### 2.5 Why each slot's window must be its own size

`StkAt E` (the bytes the activation owns besides Phase 1's blocks: the saved `LR`/`FP` and every
spill slot) gives each slot 8 bytes. It enters `CoreInv` (`SepFrom (StkAt E)`: no live block
overlaps it) and the callee contracts (`CallSpec*`: the callee keeps `StkAt E`). With narrow
slots packed by the frame layout, 8-byte windows are too coarse. Probe variants on quick-v10
(`checkG64`, same base):

| windows | slot vs. slot | slot vs. locals bound and frame variables (`StkAt`) | accepted | gain |
|---|---|---|---:|---:|
| main | 8 bytes | 8 bytes | 8,261 | — |
| W8 | 8 | 8 | 8,456 | +195 |
| W8/n | own size | 8 | 8,779 | +518 |
| Wn | own size | own size | **8,914** | **+653** |

Under W8, 346 of Wn's gains fail `slot windows overlap` (two 4-byte or 1-byte slots in one
word), 80 a `NAME_AUTO` slot at the top of the locals (`off + 8 > 0`) and 32 a frame variable next
to a narrow slot; under W8/n, 80 and 55 (`frame variable over a spill slot`). The slot-vs-slot
disjointness is internal to the proofs (`slot_apart`); the other two go through `StkAt`, so W8/n
keeps `StkAt` as it is and Wn changes its per-slot window to `(E.lc.slotTy k).size`.

## 3. Gain (probe)

`agent/slot-size-probe` (validator only, as if the slices held): Wn (§2.5), the kinds of §2.2,
the elision of §2.3 and the table entry of §2.4.

- **`gen-check`, quick-v10** (`--jobs 2`, 13 min): `checkG64` accepts **8,914 of 9,297**
  (95.88%; main 8,261, **+653**, 0 lost). All 653 are among the 666 class-only functions; the
  other 13 stop at `MOVDnop/MOVDreg: upper bits unknown` (11: the table at block edges and across
  narrow loads, the pre-existing G35 limit, `fmt.(*pp).doPrintf`, `path.Clean`,
  `runtime.mallocgcSmallNoscan` …) and `two frame variables overlap` (2, a separate class,
  masked until now). G62 8,805 and G63 8,844 (main 8,175 and 8,206).
- **End to end, quick-v10** (`gofv-ssa-opt --check --verified --e2e --jobs 2`, the probe's
  validator in the driver; main a6c37a47 measured in the same session: 7,221 premises hold, 547
  vacuous, 6,674 end to end, stock 7,557, as STATUS):

| quick-v10 (9,297 functions, `--jobs 2`, 8–9 min each) | main | probe | gain | main, stock `trim` | probe, stock `trim` | gain |
|---|---:|---:|---:|---:|---:|---:|
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` (premises hold) | 7,221 | 7,622 | +401 | 8,157 | 8,786 | +629 |
| … of them vacuous (closure context, `entryVacuous`) | 547 | 565 | +18 | 600 | 627 | +27 |
| **end to end** | **6,674** | **7,057** | **+383** | 7,557 | 8,159 | +602 |
| … `verified_mach` (`needs48 = false`) | 6,471 | 6,822 | +351 | 7,324 | 7,864 | +540 |
| … `verified_mach_S` (`needs48 = true`) | 203 | 235 | +32 | 233 | 295 | +62 |
| … pipeline output identical to stock after `trim` | 5,636 | 5,880 | +244 | | | |

  The accepted lists (`--accepted`) differ by 383 added and 0 lost. `store shape` and `load
  shape` no longer occur among `checkG64`'s first reasons on the fully verified (382 and 9 on
  main). `checkObj` rejects 8 more of the functions `checkG64`, `entryStoresOK`, `argsOK` and
  `retRegsOK` accept (12 against 4), none at a slot access: branch targets (`JMP` +3, `TBZ` +2),
  the stack check of a huge frame +2, `SBFIZ` +1; it already models the narrow stores and loads
  and `FMOVS` at frame operands. `argsOK` rejects none.

- **full-v11** (estimate): on the composition on G61, `store shape` was `checkG61`'s first reason
  for 4,286 fully verified functions against 382 on quick-v10 (×11.2), and the end-to-end counts
  scale ×10.4 (75,229 / 7,221); ×10.4–11.2 of quick-v10's +383 is **+4,000 to +4,300** end to end
  (about 4.1–4.4% of 96,674 functions), of which about 190–200 closures counted vacuous until
  #705. A full-v11 probe run (≈ 11 h at `--jobs 2`) was not made.

## 4. Options

### P3 (recommended): a Phase 3-only slice, windows of the slot's size

- **Validator**: §2.2's rows, §2.3's elision against §2.4's entry; a new slice G66 on G65 (or
  G64), `checkG66`.
- **Proofs**: the slot lemmas of §2.2 generalised (`home_slot`, `slot_sizes` dropped,
  `slot_apart`, `slot_windows_apart`, `stk_slot`, `stk_keeps`, `SlotInv`'s `Fits`), narrow
  `g2_spill`/`g2_reload` (`progStep_slotStoreN`/`LoadN`, `ValRel` of the low bits, a `bool` 0/1),
  `FMOVS` in `g63_fspill`/`g63_freload`, a narrow `Arg` in G62's step (`ArgOK` unchanged), the
  table entry in G35's invariant, the elided extension (no code / `MOVD`) from the entry; witness
  per new kind.
- **Statements**: `LocMatch`, `SlotRel`, `ValRel`, `EntryMatch`, `RunPre*`: unchanged.
  `verified_mach`, `verified_mach_S`, `verified_mach_M`, the `_fixed`/`_atSP` variants and
  `obj_whole_ret`/`obj_whole_panic`: `checkG64` → `checkG66` in the hypothesis, as at every lift
  (#702). The G-slice statements `g66_*`: G64's with `checkG66`. `StkAt`'s definition: each slot's
  window `(E.lc.slotTy k).size` instead of 8. `StkAt` is a set inside two kinds of statement
  text, which stays as it is:
  - `G3Inv`'s `CoreInv` (`SepFrom (StkAt E0)`: no live block over the frame), a hypothesis of
    `verified_mach*`: a smaller set, so a weaker hypothesis (a frame variable may sit next to a
    narrow slot);
  - the trusted callee contracts (`CallSpec`, `CallSpecS`, `CallSpecM`, through them `CallOK*`,
    `CallOKZ*`, `ICallOK*`, `WbOK*`, `MemEqOK*`): their premise asks the live blocks to avoid
    fewer bytes and their conclusion keeps fewer bytes. A callee never writes its caller's spill
    slots, which is today's justification of the row, so the contract stays faithful.

  For a function whose slots are all 8 bytes, which is every function accepted today, `StkAt E`
  is the same set, so these statements are literally unchanged there. Likewise `SlotInv` (the
  other field of `G3Inv`): `Fits (cls (slotTy k))` is `Fits 64` at every 8-byte slot. STATUS: one
  line on the contract rows and on `G3Inv`.
- **New run premise / trusted contract**: none. (`FReloadPre` holds of every `float32` reload: a
  value retyped at `.int .w32` is no pointer.)
- **Cost** (agent-days of the kind spent on G63/G64 and the lift #702):

| PR | content | days |
|---|---|---|
| G66a | `StkAt` per size; `slotOK`/`checkFrame`/`checkVars*`; slot lemmas; narrow and `FMOVS` spill/reload; narrow `Arg`; witnesses | 2.5–3 |
| G66b | reload entries in G35's table; elided extensions; witness | 1–1.5 |
| lift | the composition on G66 (`verified_mach*`, pins, e2e on quick-v10, STATUS) | 1–1.5 |
| **total** | | **≈ 4.5–6** |

- **Gain**: §3 (+653 at `checkG64`, +383 end to end on quick-v10; full-v11 about +4,000 to
  +4,300).

### P3' : the same, `StkAt` unchanged (W8/n)

Slot-vs-slot disjointness by the slots' sizes inside the proofs, `StkAt` and therefore the
contracts' frame set untouched (8-byte windows, which then must stay in the locals and off the
frame variables). Same statements as P3 minus the `StkAt` line; cost about the same (half a day
less in `Stack.lean`). Gain 518 of the 653 at `checkG64` (§2.5). Not recommended: the `StkAt` change
is local (`Stack.lean`) and is no change for any function accepted today.

### B: the blob-register design (`blob-regs.md`, #689)

Not applicable: it changes the lowered integer loads of `Move` copies (`loadB`, `Refines.blobInt`,
B2 `fragAddr`) so that bytes that do not decode survive an 8-byte integer copy. A spill slot holds
a typed value in `runLoc` (`LocState.slots`), never undecodable bytes, and its relation is already
size-generic (§2.1). B adds nothing to this class (gain 0) at 6–8 agent-days and B2's
`Mem.Refines` decision. The ranking's "out of scope (#689)" for this class should be dropped.

### Others

- **Bytes in the frame for Phase 3 (`runFrame`, L2f, `SSA/Sem/RunFrame.lean`)**: slots as bytes of
  the `outargs` block. Would also cover narrow slots, but moves Phase 3 off `runLoc`: weeks, for
  nothing §2 needs.
- **Widen narrow spills to 8 bytes at the validator**: not possible; the Progs are Go's.

## 5. Interaction with ClosureCtx1 (#705 `Env.closure`, #708)

- **Disjoint files for G66a/G66b.** They touch the validator (`Gen/Check*.lean`) and Phase 3's
  value proofs (`Proof/Gen/*`, `Stack.lean`). #705's PR1 (design E, `closure-ctx.md` §8) touches
  `SSA/Sem` (`Env.closure`, `runLoc`, `locInit`) and the Phase 1/2 statements; PR2 the
  composition (`entryLen`, `EntryMatch`'s `R26` row, `CloOK` at the top activation); #708 the
  morestack hook and `MorestackOK`. G66a/G66b can run in parallel with all three.
- **The lift conflicts textually with #705 PR2** (`Obj/EndToEnd.lean`, `Obj/Whole.lean`, the
  `ObjEndToEnd*` witnesses and `e2e_facts` pins): sequence the G66 lift after PR2, or PR2 after the
  lift; either way a mechanical rebase, no design dependency (neither changes `RunPre`'s
  conjunction for the other).
- **Counts compose.** Closures with narrow slots that G66 accepts are counted vacuous until #705's
  PR2 (18 of §3's additions on quick-v10, 27 in the stock column); after both, they count end to
  end.
- **Narrow slots of closures and `R26`.** None of G66's kinds reads `R26`; the morestack tail's
  narrow register spills (`spillArgReg`, `storeByType`) are already in `MoreEntry`'s `ValFits`.

## 6. Questions for the integrator

1. **P3 (Wn, `StkAt` per slot size)**, P3' (`StkAt` kept, 135 fewer on quick-v10), or defer?
2. Accept that `StkAt`'s definition changes under the trusted callee contracts' unchanged text
   (the same set for every function with 8-byte slots), with a STATUS line?
3. Order relative to #705: G66a/G66b now, the lift after #705 PR2?
