# Plan: the Phase 3 proofs (I7, #553)

Status: slice G1 of the genssa validator is implemented (`GoFV/Gen/Check.lean`, probe
`gen-check`) and proven sound (`GoFV/Proof/Gen/G1.lean`: `g1_value`, `g1_term`; §3, §5), with a
witness on a corpus function (`GoFV/Proof/Witness/GenG1.lean`). Slice G2 (calls, global
addresses, spills, `Exit`) is implemented as a validator (`GoFV/Gen/Check2.lean`, §4); its proof
is open. Context:
`docs/plans/semantics3.md` (§4 `LocMatch`, §6 hooks, §7 layers), `docs/PASSES3.md` (the steps
A1–F2), `docs/plans/regalloc-check.md` (the Phase 2 pattern this plan follows: an untrusted port
with 100% parity, a checker, and a soundness proof of the checker only).

## 1. The end-to-end statement

Phase 2 ends at `verifiedPipelineFull_refines` (`GoFV/Proof/Pass/PipelineFull.lean`): every
outcome of the source is an outcome of `runLoc` on the output of `trim`. Phase 3 adds

```
MachRefines f code := ∀ inputs, VPre … → MachEntry code entry room s₀ → ι-related inputs →
  runLoc of `trim`'s output returns/panics with o  →
  ∃ n, runMach H code ret n s₀ returns/panics with o' ∧ o ≈ o' (results in ABI registers, memory under ι)
```

and composes the two through the outcome relation of semantics3 §2. `MachRefines` is the
composition of one relation per layer:

```
runLoc (L2) ──LocMatch, P0 pcOf──▶ runProg P0 ──Prog map──▶ runProg P1 ──▶ runProg P2 ──words──▶ runMach M
```

`LocMatch E s b i m` (`GoFV/SSA/Sem/LocMatch.lean`) is the relation of the first arrow; its
`pcOf` is a Prog address under `Link.byId` for P0 and a byte address on M, so the same relation
states both ends. The obligations of every layer are simulation diagrams over `PStar`/`PPanics`
(`runProg`, `GoFV/Proof/Gen/Basic.lean`) or `MStar`/`MPanics` (`runMach`).

## 2. Per step: proof or checked validator

Every port of I3/I4 is untrusted and stays so: each has 100% parity on the corpus
(`gen-parity`, `asm-parity`), and its output is checked. A direct proof of a port is chosen only
where the port is small and functional; everywhere else a validator with a soundness theorem,
as `checkRA` did for regalloc in Phase 2. The ports use `partial def`, `GenM`/state monads,
mutable arrays and Go's control flow (`genssa`'s body, `span7`), which makes direct proofs
about them expensive and brittle under port changes, while their outputs have simple local
shapes.

| Step (PASSES3) | Layer | Choice | Why | Statement shape |
| --- | --- | --- | --- | --- |
| A1 merge locals, A2 frame layout (`MergeLocals`, `AllocFrame`), spill slots | L2 → frame | **validator** `checkFrame tabs f lay` (extends `FrameLayout.problems`): every spill slot and named auto at `autosize − extrasize + FrameOffset`, in the frame, aligned; slots live at the same time (from the allocated function's slot lifetimes) disjoint; merged autos with disjoint lifetimes; nothing overlaps the saved LR/FP words or the outgoing area | the ports are imperative (interval construction, sort); the property is a disjointness fact | `checkFrame … = .ok () → FrameOK E` with `E.slot k = some (slotOff lay k)` and the disjointness facts `LocMatch.slots` preservation needs at `StoreReg`, `LoadReg` and calls |
| C2–C5 genssa: value emission (C3 families), blocks (C4), branch resolution (C5) | L2 → P0 | **validator** `checkGen lc ps bstart` (`GoFV/Gen/Check.lean`), slice by slice: one Prog template per op family, block shapes of `ssaGenBlock`, the fall-through layout; returns the `pcOf` table | ~1,700 lines of port over `GenM`; the templates are what the families emit, so the validator is complete on every family it covers | `checkGen … = .ok tab → GenEnv E tab → (value step) LocMatch E s b i m → stepLoc env lc s v = .ok s' → ∃ m', PStar H L ps ret m m' ∧ LocMatch E s' b (i+1) m'`, the same for terminators (`.goto e`: `LocMatch E s' e.b 0 m'`) and faults (`PPanics`); §3 is the first slice |
| C6 defframe, D3 prologue/epilogue | entry/exit | **validator** on the fixed templates (zeroing ranges from `Needzero`, `STP`/`SUB` prologue of `autosize`, stack check, `RET` epilogue) | short fixed shapes parametrised by `autosize`, the stack-check class and the zeroed ranges | entry: `MachEntry code entry room s₀ → ∃ m, PStar … s₀ m ∧ LocMatch E s_entry entry k m` (after the entry values, `k` = their number); exit: `LocMatch` at a `Ret` block's `RET` → `MachRet s₀ m'` with the results in their ABI registers |
| D2 linkpatch/progedit, D3 preprocess | P0 → P1 → P2 | **validator** `checkEdit ps0 ps2`: a Prog map (ID → IDs) where every Prog is unchanged except the documented rewrites (constant symbols, `$0 → ZR`, jump chains, `RET` → epilogue, the frame step → prologue, morestack slow path) | the rewrites are local; a per-Prog map makes the simulation one-to-many and lock-step | `checkEdit … = true → ∀ s s', PStar H L0 ps0 ret s s' → related t → ∃ t', PStar H L2 ps2 ret t t' ∧ related t'` (the relation: same registers/memory, PC through the map, R27 free) |
| D4/D5 span7: classes, sizes, pools, veneers, encoding | P2 → M | **validator** `checkObj L ps2 code`: each Prog's words decode (`GoFV.Arm64.decode`) to the instructions `insnOf p` predicts, literal-pool words hold their constants, branch offsets reach their targets; one lemma per encoding family proves `exec (insnOf p)` meets `progSpec p` symbolically in registers and offsets | `asmout` alone is 111 cases and ~4,000 lines; decoding is already trusted and co-simulated (`arm64-cosim`), and `arm64-decode` already checks every Prog of quick-v9 (429,386/429,386) and every basic block (122,770/122,770) as a test | `checkObj … = true → PStar H L ps2 ret s s' → ∃ n, MStar H code ret s s'` on the same state (P2's `Link.ofProgs` addresses are M's), and `PPanics → MPanics` |
| D6 unsafe/restartable points, D7 pc tables (pcsp, pcdata incl. `PanicBounds`), B1 stack maps | metadata | **validators** that decode each table (`pcValue`) and compare with the value recomputed from the Progs (SP delta per PC from the `spadj` of P2, the PCDATA Prog in force, liveness at each safe point: coverage and validity) | the encoders are bit-level (varints, deltas); recomputing and comparing is simple and complete | `checkPcsp ps2 tab = true → ∀ pc, pcValue tab pc = spDelta ps2 pc`, similarly for each PCDATA; these discharge the premises of the hooks (`panicBoundsHook` reads `PCDATA_PanicBounds`; morestack and tracebacks read pcsp) |
| B2, B3, E1–E2, F1–F2 | — | none (tracebacks, debug info, object writer) | not observable by `runMach` (semantics3 §6: trusted, not modelled) | — |

The hook obligations of semantics3 §6 (arguments in place, only dead values in caller-saved
registers at a call, R27 dead at safe points) are discharged inside the genssa validator's call
templates (slice with calls) and the metadata validators.

## 3. Slice G1: genssa on straight-line blocks of simple ops

**Validator** (`GoFV/Gen/Check.lean`, `checkG1 lc ps bstart : Except String PcTab`). Input: `lc
= LocCtx.make tabs f` for the function `f` after `trim` (`runLoc`'s context), `ps` genssa's P0
Prog list in list order, `bstart` the Prog ID where each block starts (genssa's
`GenState.bstart`). Accepted functions: see the module doc — values `Phi` (same home), `ZERO`
(at a register shape), `InlMark` (no home, a shape `write` drops), `MakeResult` (results in their
registers; its shape a tuple of one component per argument with memory only where the argument
is the memory, so its write changes nothing), `Copy`, `MOVDconst`, `ADD`, `SUB`, `ADDconst`,
`SUBconst`, `CMP`, `CMPconst`, `MOVDload`, `MOVDstore` (no symbol), the entry values (`InitMem`,
`SP`, `SB`, `ArgIntReg`, `ArgFloatReg`) at the head of the entry block; blocks `Plain`, `Ret`, the
ten flags branches and `Z`/`NZ`, every successor laid out; no stack slot, register pair or
temporary; each register holds values of one width class; destinations not `g`, `R29`, `R30`. The
output table gives `pcOf b i` = the address of the first Prog of value `i` of block `b` under
`Link.byId`.

**Statement** (`GoFV/Proof/Gen/G1.lean`). Premises on the activation (`G1Env lc L ps ret tab E`):

- `E.lc = lc`, `L = Link.byId L.sym L.text L.autosize L.extrasize ps.toList`,
  `E.pcOf = pcOfTab L.text ps.toList tab` (`pcAt`: the address of the Prog at an index of `ps`),
  `ret` not a Prog address;
- `AddrAgree E.ι`: `ι` maps every block with a Phase 1 address (`Blk.base?`: nil, heap, frame
  blocks) to that address. This is semantics3 §4.3's decision for heap blocks; for frame blocks it
  is the guard of option 1 there in its strongest form (a frame block sits at its Phase 1 address),
  which G1 can afford because its functions never address their own frame;
- `E.framed = false`: G1's functions have no frame (no call, no slot), so `LocMatch` pins `X29`
  and `X30` to the caller's FP and LR.

Invariant on `runLoc` states (`G1Inv lc s`): no stack slot is live (`s.slots = []`), every
register other than `ZERO` holds a value of its width class (`Fits (regCls lc r)`: poison, an
integer of that width, a pointer for class 64, a boolean for class 1), and the memory's block keys
are distinct (`KeysNodup`: a store changes the machine bytes of its block's window, and a second
entry with the same key would keep the old bytes). G1's steps keep it.

Per-step premises (`G1Pre lc s v`, `G1TermPre lc s blk`), the dynamic restrictions of the slice,
each Go-level (a Go program satisfies them) and each the place where a later slice must do better:

- a `CMP`/`CMPconst` argument and a `Z`/`NZ` control do not read as a pointer without an integer
  form (`NoBarePtr`: `Arm64.ptrReg p` defined; a global or out-of-window pointer: Phase 2's `cmp`
  compares those by offset within one block, the machine by address, and the carry and overflow
  flags can differ when the block's addresses straddle `2^63`);
- a `MOVDload` reads 8 valid bytes (Phase 1's load of an invalid access is `poison` without a
  fault, while the machine's address could wrap into the nil page; Go programs do not perform
  invalid loads).

Theorems (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`):

```
theorem g1_value (hc : checkG1 lc ps bstart = .ok tab) (hE : G1Env lc L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp v.op = false) (hm : LocMatch E s bid i m) (hinv : G1Inv lc s)
    (hpre : G1Pre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' bid (i + 1) m' ∧ G1Inv lc s'

theorem g1_term (hc …) (hE …) (hbid …) (hb …) (hm : LocMatch E s bid blk.values.size m)
    (hinv : G1Inv lc s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G1Inv lc s' ∧
      e.b ∈ lc.ctx.f.blocks.toList
```

**Witness** (`GoFV/Proof/Witness/GenG1.lean`): `test/copy/main/clamp,1.ssa` and `.prog` of
quick-v9 embedded verbatim, parsed, run through `Env.load` and `genssa` (`load`, as `gen-check`)
and accepted by `checkG1` (compiled evaluation, `native_decide` `clamp_facts`, allowlisted with
its pin); on a frameless activation with `G1Env` (`g1Env`) and the state after the entry values
(`locMatch0`, `g1Inv0`), `g1_value` on the compare `CMPconst [40]` and `g1_term` on the `GT` block
give machine runs to `b3` for `x = 50` (fall-through) and to `b2` for `x = 30` (`BLE` taken)
related by `LocMatch` (`genG1_witness_50`, `genG1_witness_30`).

**Coverage** (`lake exe gen-check`, quick-v9, 9,297 functions): see §5.

## 4. Next slices (G2 …) and their obligations

**Slice G2** (`GoFV/Gen/Check2.lean`, `checkG2 lc ps bstart g`; validator implemented, soundness
proof open): G1 plus the most frequent blockers of §5 — `CALLstatic` of a symbol with an ABI
(every argument homed in its `abi.RegIndex` register, the `CALL` target the callee's symbol, the
`results` home the ABI's result registers), `SelectN` of such a call (no code), `MOVDaddr` of a
global (`MOVD $sym+off(SB), Rd`), 64-bit spills and reloads (`StoreReg`/`LoadReg`, `MOVD` to/from
the slot's operand in Go's frame layout) with **checkFrame** for the spill slots (8 bytes,
aligned, `NAME_AUTO` inside the locals, distinct slots disjoint), `Exit` blocks, and entry values
after the entry block's spills. Its inputs beyond G1's (`G2In`): the Prog list's symbols and the
exported frame's slot operands. Obligations of its proof:

- **Calls**: the hook of semantics3 §6 (`liftContract`), `MatchEnv.Extends` for the allocator,
  registers clobbered by the call (`LocState.clobber` of `CALLstatic`) against the hook's
  clobbers; `runProg` must run P0's `CALL` form (`TYPE_MEM`, `NAME_EXTERN` target, which
  `progEffect` leaves stuck today: `ProgCtx.target` reads only `TYPE_BRANCH`) or the proof moves to
  P1 after `linkpatch`.
- **Frames and spills**: `framed = true` with the prologue and epilogue validators (C6/D3);
  `LocMatch.slots` kept by stores (slot windows disjoint from live blocks' windows) and calls (the
  callee's frame below `SP`); `E.slot k` from the slot's operand (`NAME_AUTO`: `autosize +
  offset − extrasize`, `NAME_PARAM`: `autosize + offset + 8`).
- **Addresses of globals**: `ι` of a global is its linked symbol address (`Link.sym`), which
  `AddrAgree` leaves free.

Later slices:

1. **Narrow and mixed registers**: a forward dataflow table of the width of each register's last
   writer replaces the one-class-per-register rule; `MOVB…/MOVW…` loads and stores, extensions,
   `CMPW`, `ZW`/`NZW`, `TBZ`/`TBNZ`, `CSET`, logical ops.
2. **Nil checks** (`LoweredNilCheck` = `MOVB (Rp), R27`): `FaultSim` on the nil page.
3. **Register pairs and tuples**: `Select0`/`Select1`, `LDP`/`STP`, interface and closure calls.
4. **Addresses of frame blocks**: replace `AddrAgree`'s frame part by option 2 of semantics3 §4.3
   (addresses as a parameter of the semantics), needed once a function takes its own frame's
   addresses (`MOVDaddr` of an auto).

## 5. Results

**Coverage** (`lake exe gen-check --jobs 4 <corpus>/quick-v9`, genssa run on the exported frame
as in `gen-parity`; 9,297 functions, 426,323 values, 0 parse, env or genssa errors):

| Slice | Functions accepted | Values in accepted functions |
| --- | --: | --: |
| G1 | 268 (2.88%) | 1,500 |
| G2 | 1,211 (13.02%) | 11,012 |

Before G2, the most frequent reasons functions were outside G1 (functions each occurs in):
`SelectN` 6,909, call results homes 6,364, `CALLstatic` 6,028, `MOVDaddr` 3,637, stack slots 3,298
(`LoadReg`/`StoreReg`), register pairs 3,058, `Exit` blocks 2,631. Outside G2: registers holding
two width classes 4,453, `Select0`/`Select1` and register pairs 3,058, `LDP` 1,922, `STP` 1,765,
`TBNZ` 1,683, narrow loads (`MOVWUload` 1,440, `MOVBUload` 1,419), `NZW` 1,261, `MOVDaddr` of a
frame variable 1,261, other results homes (interface and closure calls) 1,215, `LoweredNilCheck`
1,200: the later slices of §4.

**Proof** (`GoFV/Proof/Gen/`):

- `Basic.lean`: `PStep`/`PStar`, `PStar.runProg`; `Link.byId` with distinct IDs below `2^32`:
  `off_byId`, `addr_byId`, `nextAddr_byId`, `progAt?_byId`.
- `Progs.lean`, `Branch.lean`: `progStep` of every G1 shape with symbolic registers and offsets:
  no-ops (pseudo-ops, `HINT $0`), `MOVD Rs, Rd`, `MOVD $k, Rd`, `ADD`/`SUB` register and constant,
  `CMP`, `MOVD` load and store (outside the nil page), `B<cond>`, `JMP`, `CBZ`/`CBNZ`;
  `onVal_holds` (a condition defined on flags related to `NZCV` is the machine's
  `ConditionHolds`), `condBr_spec`/`zeroBr_spec` (the opcodes of each block kind).
- `Rel.lean`, `Value.lean`: `AddrAgree`, `Fits`, `valRel_retypeL`, `locMatch_setReg`; `Lo` (a
  register result and the machine word on the low bits of a class) and the value lemmas of
  `Arm64.add`/`sub`/`addK`/`res`/`cmp`/`isZero` under `AddrAgree`.
- `Mem.lean`: under `AddrAgree` every byte of a live block is `ByteRel` (`memInj_byteRel`); the
  address of an access (`addr_rel`), the 8-byte load (`lo_load`) and store (`memInj_store`, which
  keeps `MemInj` with no pointer words and `KeysNodup`).
- `Spec.lean`: what `checkG1` accepted (`checkG1_spec`, `Cx.blocks_spec`, `Cx.values_spec`,
  `Cx.term_spec`, `vkind_spec` with the per-op facts `VK`).
- `Loc.lean`, `Step.lean`: `stepLoc` per op (`stepLoc_pure`, `stepLoc_copy`,
  `stepLoc_makeResult`, `stepLoc_load`, `stepLoc_store`, …).
- `G1.lean`: the steps on the ID layout (`pstar_noops`, `pstar_oneAt`), one lemma per value kind
  (`op_none`, `op_reg`, `op_flags`, `op_mem`, `value_core`), the terminators (`fall_path`,
  `two_path`), `g1_value`, `g1_term`.
