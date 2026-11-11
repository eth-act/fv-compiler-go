# Plan: the Phase 3 proofs (I7, #553)

Status: slices G1–G12 of the genssa validator are implemented (`GoFV/Gen/Check.lean`,
`GoFV/Gen/Check2.lean`, …, `GoFV/Gen/Check12.lean`, probe `gen-check`) and proven sound
(`GoFV/Proof/Gen/G1.lean`: `g1_value`, `g1_term`; `GoFV/Proof/Gen/G2.lean`: `g2_value`, `g2_term`;
`GoFV/Proof/Gen/G3.lean`: `g3_value`, `g3_term`; `GoFV/Proof/Gen/G4.lean`: `g4_value`, `g4_term`;
`GoFV/Proof/Gen/G5.lean`: `g5_value`, `g5_term`; `GoFV/Proof/Gen/G6.lean`: `g6_value`, `g6_term`;
`GoFV/Proof/Gen/G7.lean`: `g7_value`, `g7_term`, `g7_nilPanic`; `GoFV/Proof/Gen/G8.lean`:
`g8_value`, `g8_term`, `g8_nilPanic`; `GoFV/Proof/Gen/G9.lean`: `g9_value`, `g9_term`,
`g9_nilPanic`; `GoFV/Proof/Gen/G10.lean`: `g10_value`, `g10_term`, `g10_nilPanic`;
`GoFV/Proof/Gen/G11.lean`: `g11_value`, `g11_term`, `g11_nilPanic`; `GoFV/Proof/Gen/G12.lean`:
`g12_value`, `g12_term`, `g12_nilPanic`; §3–§5), with witnesses on corpus functions
(`GoFV/Proof/Witness/GenG1.lean`, …, `GenG12.lean`).
G2–G12 rest on the trusted callee contract `CallOK`, G8–G12 also on the write-barrier hook
contract `WbOK`, G10–G12 also on the indirect callee contract `ICallOK`, G11 and G12 also on the
closure context premise `CloOK` (§4, `docs/proofs/STATUS.md` Assumptions); §6 lists future work
on these premises.
The assembler validator `checkObj` (P0 against the assembled words, D2–D5, probe `obj-check`) is
implemented and proven sound (`GoFV/Proof/Obj/`: `obj_star`, the templates `obj_entry`/`obj_exit`;
`g7_obj_value`/`g7_obj_term` and `g62_obj_value`/`g62_obj_term`/`g62_obj_nilPanic`/
`g62_obj_boundsPanic` compose it with G7 and G62: `runLoc` to the machine words; §7). Whole
functions: `obj_whole_ret` (a returning `runLoc` body of a G62 function, from the machine's entry
through the prologue, the entry stores of the register parameters in `Blk.local` blocks, the
blocks and the epilogue to the caller's return address, the results in
their ABI registers), `obj_whole_panic` (a panicking body: nil checks, loads, stores, acquire
loads and atomics that fault, bounds checks, calls whose callee panics), and the end-to-end
statement `verified_mach` on slice G62 (G61 with the incoming stack arguments, on P0'; per
function, at G48's mode
`verified_mach_S` for a function that needs it, `needs48`; generic SSA `run` refined by `runLoc`, whose body is matched by `runMach` of the
assembled words; `checkG62`'s `checkG62L` on `liveCtx`, `runLoopLoc_live`, `entryStoresOK`,
`argsOK` and `EntryMatch`'s stack clause; §9),
with a witness on `pallocSum.start` from its generic SSA.
Context:
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
| D2 linkpatch/progedit, D3 preprocess, D4/D5 span7 (classes, sizes, pools, veneers, encoding) | P0 → M | **validator** `checkObj ps spills obj` (`GoFV/Asm/CheckObj.lean`, §7; probe `obj-check`): the P0 Progs against the assembled words directly, without P1/P2 in between. Each Prog's words are decoded (`GoFV.Arm64.decode`) and executed symbolically (`symWords`; relocated pairs and calls as the linker patches them, `CheckObjLink.lean`), and compared with the Prog's symbolic effect (`progSym`, which mirrors `progEffect`): every register but `X27`, `SP`, the flags, the stores in order, loads only the Prog's, branch offsets at the target Prog's words. The prologue (stack check, frame), the epilogue at P0's `RET` and the morestack tail are checked as templates | `asmout` alone is 111 cases and ~4,000 lines; decoding is already trusted and co-simulated (`arm64-cosim`), and `arm64-decode` already checks every Prog of quick-v9 (429,386/429,386) and every basic block (122,770/122,770) as a test; comparing P0 with the words skips `checkEdit`, because the rewrites of D2/D3 (constant symbols, `$0 → ZR`, jump chains, `RET` → epilogue) all meet the same symbolic effect | `checkObj … = .ok tab → ObjEnv … → PStar H L ps (endP) s s' → ObjRel f s t → ∃ t', MStar H code retM t t' ∧ ObjRel f s' t'` (`ObjRel`: registers but `X27`/`X30` equal, `X30` and the PC through the address map `f`: P0 Prog address ↦ its words), and the templates `obj_entry`/`obj_exit` |
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
`Link.byId`. A block falls through to the successor laid out next (no `JMP`) when only no-ops
(`noop`: pseudo-ops, `HINT $0`) lie between its last Prog and the successor's start (`Cx.falls`,
`FallAt`; the skip stops at that start, so no-ops leading the successor stay its own); under
`Link.byId` each no-op has its own address, so `fall_path` runs them (`pstar_noops`).

**Statement** (`GoFV/Proof/Gen/G1.lean`). Premises on the activation (`G1Env lc L ps ret tab E`):

- `E.lc = lc`, `L = Link.byId L.sym L.text L.autosize L.extrasize ps.toList`,
  `E.pcOf = pcOfTab L.text ps.toList tab` (`pcAt`: the address of the Prog at an index of `ps`),
  `ret` not a Prog address;
- `AddrAgree E.ι`: `ι` maps every block with a Phase 1 address (`Blk.base?`: nil, heap, frame
  blocks) other than a frame temporary (`Blk.temp`, a `PAUTO` whose address is never converted to
  an integer) to that address. This is semantics3 §4.3's decision for heap blocks; for frame
  blocks an integer can convert back to (`Blk.local`, `Blk.outargs`) it is the guard of option 1
  there in its strongest form (such a block sits at its Phase 1 address). A frame temporary is free:
  no integer is its address (`Ptr.ofAddr_ne_temp`), and slice G6 puts the current activation's at
  their frame operands (§4);
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
  invalid loads);
- the pointer operands of a `SUB` are in one block or in no frame temporaries (`SubPre`,
  `SubOK`): Phase 2 subtracts the Phase 1 addresses of two pointers into different blocks, the
  machine their injected ones, which differ for frame temporaries. Go code subtracts pointers only
  after converting them to `uintptr`, which makes a variable of the function `Blk.local`; the
  premise excludes subtracting pointers into two different stack variables of other activations.

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

**Coverage** (`lake exe gen-check`, quick-v10, 9,297 functions): see §5.

## 4. Slices G2–G14, and the next slices

**Slice G2** (`GoFV/Gen/Check2.lean`, `checkG2 lc ps bstart g`; proven sound, `g2_value`,
`g2_term`): G1 plus the most frequent blockers of §5 — `CALLstatic` of a symbol with an ABI
(every argument homed in its integer `abi.RegIndex` register `R0`–`R15`, the `CALL` target the
callee's symbol, the `results` home the ABI's result registers, each result's shape of the class
of its register: `callTy`, `resultReg`), `SelectN` of such a call (no code; the memory, or result
`i` homed in the call's result register `i` below `R16`), `MOVDaddr` of a global
(`MOVD $sym+off(SB), Rd`, 64-bit destination), 64-bit spills and reloads (`StoreReg`/`LoadReg`,
`MOVD` to/from the slot's operand in Go's frame layout) with **checkFrame** for the home slots
(`slotOK`: 8 bytes, aligned, `NAME_AUTO` inside the locals or `NAME_PARAM`; distinct home slots at
distinct operands), `Exit` blocks, and entry values after the entry block's spills. Its inputs
beyond G1's (`G2In`): the Prog list's symbols and the exported frame's slot operands.

How the proof discharges G2's obligations:

- **P0's `CALL`**: `runProg` runs P0's form. In `progEffect`, `CALL sym(SB)` (`TYPE_MEM`,
  `NAME_EXTERN`/`STATIC`) goes to `L.sym n + off`, the target progedit's `TYPE_BRANCH` rewrite
  gives (`GoFV/SSA/Sem/RunProg.lean`, witness `runProg_callMem_witness`); the step lemma is
  `progStep_callSym` (`X30` the fall-through, the PC the symbol). The symbol has no Prog, so the
  next step is the hook (`PStep.hook`; `G2Env.syms`: no Prog and not `ret` at a symbol).
- **The callee**: the trusted contract `CallOK`/`CallSpec` (semantics3 §6, the hook lifting the
  callee's Phase 1 contract through ABIInternal), taken as a premise of `g2_value` at each call:
  from the state at the callee's symbol with the arguments in their ABI registers and the memory
  injected, the hook returns to `X30` with `SP`, `R28`, `R29` and the frame (`StkAt`: the saved
  `LR`/`FP` words and the spill slots) kept, `runLoc`'s memory after the call injected by an
  extension of `ι` (`MatchEnv.Extends`), and `runLoc`'s results in the result registers.
  `g2_call` proves the rest: the arguments read from their homes (`arg_rel`), the registers after
  `LocState.clobber` of `CALLstatic` (all but `R29`, `ZERO`, `SP` and those past the F registers
  are `poison`: `call_keeps`, by `decide` on the clobber mask), the results written by
  `writeParts` (`write_call`, `writeParts_call`), the flags `poison`, the slots and the frame under
  the larger injection (`stk_slots_frame`).
- **Frames and spills**: `framed = true` when the function calls (`G2Env.calls`); the frame
  layout `FrameOK` (`SP` above the nil page, each home slot above the saved `LR` without wrapping
  around); each home slot at its operand (`G2Env.slot`, `frameOff`: `NAME_AUTO` at `autosize +
  offset − extrasize`, `NAME_PARAM` at `autosize + offset + 8`); the live blocks away from `StkAt`
  (`CoreInv … (StkAt E)`), so a store of G1 keeps the slots and the frame (`stk_keeps`) and a spill
  keeps the live blocks and the other slots (`slot_apart`, from `checkFrame`).
- **Addresses of globals**: `G2Env.glob`, `ι` of a global is its linked symbol address
  (`Link.sym`), which `AddrAgree` leaves free.

The prologue and epilogue (C6/D3) are not part of `g2_value`/`g2_term`: they start from a state at
the body entry (`E.sp` after the prologue).

**Slice G3: widths** (`GoFV/Gen/Check3.lean`, `checkG3 lc ps bstart g`, returning G2's PC table
and the class table; proven sound, `g3_value`, `g3_term`):

- **Classes by dataflow.** G1 and G2 let each register hold values of one class (`regCls`). G3
  tracks the class of each register's last writer (`kStep`: a register home sets its register, a
  static call each result register, a `Phi` nothing), forward from the entry block (`kFlow`, a
  meet at joins); `checkK` checks the table it returns: every register a value reads holds the
  class it is read at (`kReads`: register arguments, the call result a `SelectN` reads, the
  control of a register test), and each successor's start is implied by its predecessor's end
  (`kLe`). Static calls must have distinct result registers.
- **Values** beyond G2's (`vkind3`, `VK3`): the loads `MOV{D,B,BU,H,HU,W,WU}load` and stores
  `MOV{D,B,H,W}store` through a 64-bit register or of a global (`sym+off(SB)`, `AccessOK`),
  boolean `MOVBU` loads; the extensions `MOV{B,BU,H,HU,W,WU}reg`; `AND`/`LSL`/`LSR $k`; `UBFX`;
  `CMPW`/`CMPWconst`; `SB` of a register shape anywhere (no code).
- **Blocks** beyond G2's (`Cx.termG3`, `TermOK3`): `ZW`/`NZW` (`CBZW`/`CBNZW`) on a register of at
  least 32 bits or a boolean, `TBZ`/`TBNZ` on a register holding the tested bit or a boolean.

How the proof discharges G3's obligations: the invariant `G3Inv E lc K s` is G2's with the class
map `K` of the table before the value (`kAt lc kt b blk i`, `kAt_succ`) instead of `regCls`, so
G1's and G2's value lemmas (`value_core`, `g2_*`) are generic in the class map (`KRead`, `KNext`,
`KCall`) and G3 instantiates them (`kread_of_reads`, `knext_kStep`, `kcall_kStep`,
`ksel_of_reads`); at a terminator the end's map implies the successor's (`checkK_spec`,
`CoreInv.mono`). Narrow accesses: `MemN.lean` generalises `Mem.lean`'s 8-byte load and store to
`n ∈ {1, 2, 4, 8}` bytes (`lo_loadN`, `valRel_loadBool`, `memInj_storeN`, `access_nil`); the
per-value premise `G3Pre` asks that a load read valid bytes (and a boolean byte 0 or 1, as Go
stores booleans). The narrow ALU ops, compares and tests relate on the low bits of the classes
(`Value3.lean`: `valRel_ext`, `valRel_andK`, `valRel_lslK`, `valRel_lsrK`, `valRel_ubfx`,
`flagsRel_cmpw`, `taken_zw`, `taken_tbz`, …). One lemma per G3 value kind (`g3_load`,
`g3_store`, `g3_ext`, `g3_aluK`, `g3_ubfx`, `g3_cmpw`, `g3_cmpwK`, `g3_sb`) and the register and
bit tests (`term_test`).

**Slice G4: register pairs** (`GoFV/Gen/Check4.lean`, `checkG4 lc ps bstart g`, returning G3's
tables; proven sound, `g4_value`, `g4_term`):

- **Values** beyond G3's (`vkind4`, `VK4`): the pair load `LDP [off] a mem` homed in a register
  pair `(Ra, Rb)` of two distinct registers G1 may write, each component of an integer class of at
  least 8 bits, through a 64-bit register without symbol (emitted `LDP off(Rn), (Ra, Rb)`,
  `pairA`: `TYPE_REGREG`); the pair store `STP [off] a x y mem` of two 64-bit registers (`STP (Rx,
  Ry), off(Rn)`); `Select0`/`Select1` of an `LDP` of two classed components, homed in the register
  of its component (no code).
- **Classes**: `kStep` treats a pair home as a call's `results` (each register takes its
  component's class), `kReads` adds the register a `Select0`/`Select1` reads. Pair homes are
  accepted (`homeOK4`).

How the proof discharges G4's obligations: the invariant is G3's (`G3Inv`); the per-value premise
`G4Pre` adds to `G3Pre` that a pair load read valid bytes at both of its addresses (`pairAddr`).
G3's values go through `vk3_step` (the body of `g3_value` after the validator's facts, shared by
both theorems). `Step4.lean` gives `stepLoc` of `LDP` (`ldPair 8`: two `loadN` at `pairAddr`),
`STP` (`stPair 8`: two writes in order, both succeeded) and the selects; `Progs4.lean` gives
`progStep` of `LDP` (both loads read before either register is written, as on the machine, so a
base register that is also `Ra` is sound) and `STP` (the stores applied in order). `pairAddr`'s
second address is the offset plus 8 (`ofInt_add8`, both modulo `2^64`). `g4_ldp` writes the two
registers by `finish_reg` twice (`write_pair`, `kpair_kStep`), `g4_stp` stores twice
(`memInj_storeN`, the frame kept by `SepFrom` across both), `g4_sel` reads the pair's register
(`read_pair`, `ksel4_of_reads`) and changes nothing on the machine.

**Slice G5: memory markers** (`GoFV/Gen/Check5.lean`, `checkG5 lc ps bstart g`, returning G4's
tables; proven sound, `g5_value`, `g5_term`): G4 plus the memory ops genssa emits no code for, each
of the memory shape with no home, its memory argument last (`markOp?`, `VK5.mark`): `VarDef {x}`
(Phase 1 poisons `x`'s block, `Mem.poisonBlock`), `VarLive` and `KeepAlive` (the memory unchanged)
and `WBend` (the write-barrier buffer freed, `Mem.free .wbuf`).

How the proof discharges G5's obligations: the activation, the invariant and the premises are G4's
(`G2Env`, `G3Inv`, `G4Pre`); G4's values go through `vk4_step` (the body of `g4_value`, shared), the
terminators through `termK_step` (the body of `g3_term`, shared by `g3_term`, `g4_term` and
`g5_term`). `Step5.lean` gives `stepLoc` of a marker (`stepLoc_mark`: the memory stays, is
`poisonBlock b` or `free .wbuf`). A marker changes no machine state (`g5_mark`, `m' = m`): the new
memory has a subset of the old blocks with their sizes and each byte unchanged or poison
(`MemSub`: `memSub_poison`, `memSub_free`, which also keep the keys distinct), so `MemInj` holds
with no pointer words (`memInj_sub`, through `memInj_byteRel` under `AddrAgree`) and `SepFrom`
holds (`sepFrom_sub`).

**Slice G6: frame variables** (`GoFV/Gen/Check6.lean`, `checkG6 lc ps bstart g`, returning G4's
tables; proven sound, `g6_value`, `g6_term`): G5 plus the accesses of frame variables. A frame
variable G6 handles is a `PAUTO` whose address the function never converts to an integer
(`Tables.forgeable x = false`: its block is `Blk.temp`), with a `NAME_AUTO` operand in Go's frame
layout (`varOp g x = g.slotOp (varKey x)`, at `FrameOffset + off`, `slotA`); the access's address
argument is `SP` (`frameVar?`, `FrameVarOK`). Values (`vkindVar`, `VKVar`): `MOVDaddr {x}` into a
64-bit register (`MOVD $off'(RSP), Rd`, `addrA`), G3's loads and stores, G4's `LDP`/`STP`, each at
the operand. `checkVars`: the windows of the accessed variables (`accessedVars`, sizes from
`Ctx.locals`) lie inside the locals, pairwise disjoint (merged locals share an operand) and away
from the home slots, so that the activation below is satisfiable together with `MemInj` and
`SepFrom (StkAt E)`.

How the proof discharges G6's obligations ("frames take the guard", semantics3 §4.3):

- **`AddrAgree` without frame temporaries** (`Rel.lean`): `AddrAgree ι` constrains every block
  with a Phase 1 address but `Blk.temp`. Its consumer `ptrRel_addr` now takes `NotTemp p.blk`,
  which each call site has: a convertible pointer (`Ptr.word`, `notTemp_of_convertible`), an
  `Arm64.ptrReg` pointer (`ptrReg_notTemp`) or a `Ptr.ofAddr` result (`notTemp_ofAddr`). The one
  place that needs more is `Arm64.sub` of two pointers with Phase 1 addresses (`lo_sub`): the new
  per-value premise `SubPre` (in `G1Pre` and `G3Pre`) asks the operands to be in one block or in no
  frame temporaries (`SubOK`). G1–G5 keep their statements otherwise.
- **The activation** (`G6Env`): `G2Env`, and `VarsAt`: each accessed variable of `NAME_AUTO`
  operand `o` not converted to an integer has its block `Blk.temp act x` at `E.sp + frameOff L
  .AUTO o` under `ι` (`VarsAt.extend`: kept when a call extends `ι`).
- **The values**: `symAddr` of a frame access is the variable's block at the access's offset (the
  `SP` argument is ignored, `symAddr_var`, `pairAddr_var`); its injected address plus the offset is
  `SP + frameOff off` (`var_addr`, `frameOff_add`). `g6_addr`: `MOVDaddr` gives `ptrRes ⟨temp,
  off⟩`, a pointer (a `temp` pointer has no integer word) related by `PtrRel`; `g6_load`,
  `g6_store`, `g6_ldp`, `g6_stp` follow G3's global and G4's pair cases at the variable's injected
  address (`lo_loadN`, `memInj_storeN`, `access_nil`; the frame's saved words and slots are kept by
  `SepFrom`). `progStep` of the `slotA` shapes of every width (`progStep_slotLoadN`,
  `progStep_slotStoreN`), `LDP`/`STP` at a frame operand (`progStep_slotLdp`, `progStep_slotStp`)
  and `MOVD $off(RSP), Rd` (`progStep_slotAddr`). G5's values go through `vk5_step`.

**Slice G7: nil checks** (`GoFV/Gen/Check7.lean`, `checkG7 lc ps bstart g`, returning G4's tables;
proven sound, `g7_value`, `g7_term`, `g7_nilPanic`): G6 plus `LoweredNilCheck p mem`
(`VK7.nil`): no home and a shape `LocState.write` drops (`dropTy`; lowering gives the check the
`void` shape), `p` in a 64-bit register `Rp`, the memory last; genssa emits `MOVB (Rp), R27`
(`nilShape`, a one-byte load into `REGTMP`).

How the proof discharges G7's obligations (`G7.lean`, `Progs7.lean`):

- **`runLoc`'s nil check** (`stepLoc_nilCheck`, `stepLoc_nilCheck_panic`): `arm64Op` panics with
  `nilDeref` when the pointer's base is nil (`nilFaults`, `nilFaults_nilCheck`), is `stuck` on a
  wild pointer (`wildNil`) and otherwise runs `memRoot`'s `NilCheck`, which panics on a pointer
  into the nil block and else returns the pointer (`evalOpL_nilCheck_ok`,
  `evalOpL_nilCheck_panic`). A successful check changes nothing (`write_drop`); a panicking one
  has the nil pointer as its argument.
- **No panic** (`g7_nil`): the per-value premise `G7Pre` adds to `G4Pre` that a nil-checked
  pointer outside the nil block points to a byte of a live block (`NilPre`; Go nil-checks pointers
  that are nil or point into an object), so the machine address is outside the nil page
  (`addr_rel`) and the `MOVB` loads (`progStep_nilCheck`, `progStep_loadN` into `X27`); `X27` is no
  Go register (`objX?_ne27`), so `LocMatch` holds with only the PC moved (`locMatch_tmp`).
- **Panic** (`g7_nilFault`, `g7_nilPanic`): the nil pointer, as a pointer or as the integer 0, is
  the machine word 0 (`nil_word`, from `MemInj.nil`); the `MOVB` at it faults
  (`progStep_nilCheck_nil`), which is `runProg`'s panic `nilDeref` (`PPanics`, the counterpart of
  `runMach`'s `MPanics`; `PPanics.runProg`), the panic `runLoc` takes.

**Slice G8: write barriers** (`GoFV/Gen/Check8.lean`, `checkG8 lc ps bstart g`, returning G4's
tables; proven sound, `g8_value`, `g8_term`, `g8_nilPanic`): G7 plus the write-barrier buffer
requests (`VK8.wb`): `LoweredWB [n] mem`, `1 ≤ n ≤ 8`, of the shape `(pointer, mem)` (`wbTy`) homed
in the pair `(R25, -)`, emitted `CALL runtime.gcWriteBarrier<n>(SB)` (`wbPat`, ABIInternal);
`Select0` of a request homed in `R25` at a 64-bit shape and `Select1` of it, the memory with no
home (`VK8.sel0`, `VK8.sel1`): no code.

How the proof discharges G8's obligations (`G8.lean`):

- **`runLoc`'s request** (`stepLoc_wb`): not a root, so `Arm64.evalPure`'s `wbOp`: a fresh buffer
  block `wbuf` of `8n` poison bytes (`Mem.wbAlloc`) and the pointer to it, written to `(R25, -)`
  after the op's clobbers (`clobber_wb`: `R16`, `R17`, `R30`, `F0`–`F31` and the flags `poison`;
  `wb_keeps`). The class table sets `R25` to 64 (`kwb_kStep`).
- **The hook** (`g8_wb`): the `CALL` puts the return address in `X30` (`progStep_callSym`); the
  activation has a frame (`G8Env`: no write barrier in a frameless function), so `LocMatch` leaves
  `X30` free. The runtime's `wbHook` is the trusted contract `WbOK`/`WbSpec` (STATUS
  Assumptions), from the state at the symbol `runtime.gcWriteBarrier<n>`: the hook returns to `X30`
  with `SP`, the memory and every register but `X25`/`X27` kept, and an extension of `ι` maps
  `wbuf` to `X25` and injects the memory with the fresh buffer, away from the frame. The kept Go
  registers are none of `X25`, `X27`, `X30` (`objX?_kept`) and no `F` register (`objV?_kept`); the
  slots and the frame hold under the larger injection (`stk_slots_frame`).
- **The selections** (`g8_sel0`, `g8_sel1`): `Select0` rereads `R25` (`read_wb`, the class from
  `kReads`: `ksel8_of_reads`); `Select1` writes the memory it reads (no change, `op_none`).

**Slice G9: call results** (`GoFV/Gen/Check9.lean`, `checkG9 lc ps bstart g`, returning G4's
tables; proven sound, `g9_value`, `g9_term`, `g9_nilPanic`): G8 with G2's static-call check
(`vkind2`) relaxed (`vkind9`, `VK9.call`): the result registers need no longer hold one class in
the whole function (G2's `resultReg`, from `regCls`); they are distinct (`outs.Nodup`, G3's) and
the results have register shapes (`callTy`). The emitted Prog is `CALL sym(SB)` (`callPat`).

How the proof discharges G9's obligations (`G9.lean`): `g2_call` never used `resultReg`; it needs
of the class map after the call only `KCall`, which the class table gives for distinct result
registers (`kcall_kStep`). G8's other values go through `vk8_step`.

**Slice G10: interface and closure calls** (`GoFV/Gen/Check10.lean`, `checkG10 lc ps bstart g`,
returning G4's tables; proven sound, `g10_value`, `g10_term`, `g10_nilPanic`): G9 with
`ssa.go`'s indirect calls (`vkind10`, `VK10`):

- `CALLinter code args… mem` and `CALLclosure code ctx args… mem` (`icallLead`: 1 or 2 leading
  arguments that are no register pieces): the code pointer in a register `Rn` (`R0`–`R26`) at a
  register shape, the closure context in `R26` (`ctxReg`, Go register 25: the context register
  of Go's internal ABI), the remaining register arguments in their ABI registers and the results
  in distinct ABI result registers `R0`–`R15` at register shapes then the memory, as a static call
  (`icallErr`); `CALL (Rn)` (`TYPE_MEM`, `NAME_NONE`, register `Rn`: `State.Call` without an
  `AuxCall` symbol; `icallPat`);
- `SelectN` of such a call: G2's selects of a static call (`selKind`);
- their `results` homes (`homeOK10`).

How the proof discharges G10's obligations (`G10.lean`):

- **`runLoc`'s call** (`stepLoc_icall`, `clobber_icall`): the same writes as a static call's (the
  ops clobber the same registers and the flags, `icall_regInfo`), whatever callee `callOp` runs.
- **The machine** (`g10_icall`): `CALL (Rn)` puts the return address in `X30` and the content of
  `Rn` in the PC (`progStep_callReg`); `Rn` is no `X30` (`objX?_ne30`). The code register is
  related to `runLoc`'s code pointer and `R26` to the closure context (`arg_rel` under the class
  table); the callee is the trusted contract `ICallOK` (STATUS Assumptions): the code register's
  address is no Prog of the caller and not its return address, and the hook there satisfies
  `CallSpec`, the static callee's contract. The rest is `g2_call`'s argument: the results in the
  result registers, the kept registers, the frame and the slots under the larger injection.
- **The selects** go through `g2_selMem`/`g2_selReg`, which need of the call only that its home is
  no slot (`icallNotSlot10`). `G10Env` adds to `G8Env` that a frameless function has no indirect
  call. G9's values go through `vk9_step`, which now takes what it used of the homes
  (`CallsNotSlot`: no static call homed in a slot) instead of `homeOK4` for every value.

**Slice G11: the closure context** (`GoFV/Gen/Check11.lean`, `checkG11 lc ps bstart g`, returning
G4's tables; proven sound, `g11_value`, `g11_term`, `g11_nilPanic`): G10 with
`LoweredGetClosurePtr` (`vkind11`, `VK11.clo`): no argument, homed in `R26` (`ctxReg`, its
`regInfo` output) at a 64-bit shape, no code; every such value in the entry block after register
arguments only (`cloFirst`, genssa's `CheckLoweredGetClosurePtr`). Entry values may follow it
(`Cx2.values`: it emits no code, like a spill), as `ArgIntReg`s and `InitMem` do in most closures.

How the proof discharges G11's obligations (`G11.lean`): `runLoc` writes the activation's closure
context `fr.closure` to `R26` (`stepLoc_clo`); the machine does not move, and `X26` holds the
context by the trusted premise `CloOK` (STATUS Assumptions: Go's internal ABI passes it in `R26`,
and no code but the prologue runs before the value), a 64-bit word, so `R26` is related at its
class (`g11_clo`). The activation is G10's (`G10Env`); G10's values go through `vk10_step`.

**Slice G12: pointer conversions** (`GoFV/Gen/Check12.lean`, `checkG12 lc ps bstart g`, returning
G4's tables; proven sound, `g12_value`, `g12_term`, `g12_nilPanic`): G11 with `Convert x mem`
(`vkind12`, `VK12.conv`; `unsafe.Pointer(u)`, `uintptr(p)`): no temporary, `x` and the value
homed in one register G1 may write (`argObj`, `resObj` with the same obj register), both of
class 64, the memory last; no code (genssa's `OpConvert` case checks the shared register).

How the proof discharges G12's obligations (`G12.lean`): `runLoc` runs Phase 1's
`PtrOps.convert` on the arguments read from their homes and writes it at the value's shape
(`stepLoc_conv`). The machine does not move and the register keeps its word (`valRel_convert`): a
pointer converted to `uintptr` is its Phase 1 address when it has one and is convertible, else
`poison`; a convertible pointer is no frame temporary (`notTemp_of_convertible`), so under
`AddrAgree` its injected address is that address (`ptrRel_addr`); anything else is unchanged and
takes the value's shape as a register read does (`valRel_retypeL`). G11's values go through
`vk11_step`. No new premise.

**Slice G13: zeroing** (`GoFV/Gen/Check13.lean`, `checkG13 lc ps bstart g`, returning G4's
tables; proven sound, `g13_value`, `g13_term`, `g13_nilPanic`): G12 with `LoweredZero [n] p mem`
(`vkind13`, `VK13.zero`; `n ≥ 16`, larger blocks are `LoweredZeroLoop`'s): no temporary, `p` in a
register of class 64, the memory last, a memory with no home; genssa's `zeroTail` stores
(`ssa.go:1503-1523`): an `STP (ZR, ZR), off(Rp)` per 16 bytes, then of the `r = n mod 16` bytes
left an `MOVD ZR, off(Rp)` of 8 when `r > 8` and an `MOVD ZR` of the last 8 bytes (overlapping the
previous store) when bytes remain (`zeroOffs`, `zeroPat`). `checkG13` decides per value that the
stores lie inside the `n` bytes and cover each of them (`zeroCovers`). A value now emits several
Progs in order, each after no-ops (`VKind2.progs`, `Cx2.many`, `ManyAt2`); G2–G12 never do.

How the proof discharges G13's obligations (`G13.lean`):

- **`runLoc`** writes `n` zero bytes at `p`'s address (`Arm64.zero`, `stepLoc_zero`), `poison`
  when the write is invalid. The new per-value premise `G13Pre` adds to `G7Pre` that the write is
  valid (`ZeroPre`: Go zeroes memory it owns, as `G4Pre` and `NilPre` ask a load or a nil check to
  touch valid bytes).
- **The machine** runs the stores in order (`zero_run`, `progStep_zero`): every byte a store covers
  is 0 (`zeroMem_cov`), every other byte unchanged (`zeroMem_out`). By `zeroCovers` the bytes at the
  write's injected address are exactly the `n` zeros `runLoc` wrote and every other byte is the old
  one, which keeps `MemInj` (`memInj_writeAny`, `MemN.lean`: `memInj_write` for any machine memory
  that holds the written bytes and agrees elsewhere). The zeroed bytes lie inside a live block
  (`write_inside`), so away from the frame (`SepFrom`): the saved words and the spill slots keep
  their bytes (`g13_zero`). G12's values go through `vk12_step`.

**Slice G14: register-index loads** (`GoFV/Gen/Check14.lean`, `checkG14 lc ps bstart g`,
returning G4's tables; proven sound, `g14_value`, `g14_term`, `g14_nilPanic`): G13 with the integer
register-index loads `MOV{D,W,WU,H,HU,B,BU}loadidx ptr idx mem` and the scaled
`MOV{H,HU}loadidx2`, `MOV{W,WU}loadidx4`, `MOVDloadidx8` (`vkind14`, `VK14.idx`, `loadIdxOp?`: the
opcode, `n` bytes, the index shift `sh`, the sign): no temporary, `ptr` and `idx` in registers of
class 64, the memory last, the destination as a load's (`vkind3`). Genssa emits one load from
`genIndexedOperand`'s operand (`ssa.go:155`): base `Rp`, index `Ri` unscaled or shifted,
`REG_LSL ||| sh <<< 5 ||| (Ri & 31)`, which `idxA` writes as the sum `REG_LSL + 32·sh + k` for
`Ri = REG_R0 + k`. Every register-index load of quick-v10 is accepted.

How the proof discharges G14's obligations (`G14.lean`):

- **`runLoc`** runs Phase 1's `Arm64.loadIdx` on the arguments read from their homes
  (`stepLoc_loadIdx`; a pure op, no nil check): the `n` bytes at the address of `idxSum`, `ADD`
  of `ptr` and `idx · 2^sh` with `ADD`'s pointer cases, `poison` when there is none
  (`loadIdx_eq`). The new per-value premise `G14Pre` adds to `G13Pre` that the access reads valid
  bytes, and a boolean destination 0 or 1 (`IdxPre`, as `G3Pre` asks of a plain load).
- **The machine**: `ProgCtx.mem` decodes `idxA` as `X[p] + (X[i] <<< sh)` (`ctx_mem_idx`), and the
  load is G3's at that address (`progStep_loadAt`, `Progs3.lean`, now public). Both registers are
  related to the arguments at class 64, so the sum is related to `idxSum` as an `ADD` result
  (`lo_idxSum`: `lo_add`; a scaled index register is the integer itself, `reg_low`, and
  `k · 2^sh = k <<< sh`, `mul_twoPow_eq_shl`), hence to the machine word (`lo64_rel`); a valid
  access's address is the injected address of its bytes, outside the nil page (`addr_rel`), and the
  loaded register is G3's (`lo_loadN`, `valRel_loadBool`; `g14_idx`). G13's values go through
  `vk13_step`.

**Slice G15: zero-sized stack arguments** (`GoFV/Gen/Check15.lean`, `checkG15 lc ps bstart g`,
returning G4's tables; proven sound, `g15_value`, `g15_term`, `g15_nilPanic`): G14 with the static
calls whose ABI assigns inputs of size 0 to the stack (`zeroStack`: no register piece, no byte in
the outgoing area, such as an empty-struct receiver). `callRegs` rejects every stack input;
`checkG15` checks a static call as G9 does on the ABI without its zero-sized stack inputs
(`callRegsZ`, `callKind15`, `VK15.call`). Genssa emits no store for them. The proof is
`g2_call`'s, which now factors through `g2_callAt` (the callee contract for one call, `CallAt`,
whatever check gave its registers); the contract at such a call is the trusted premise `CallOKZ`
(`CallOK` with `callRegsZ` in place of `callRegs`; STATUS Assumptions). Of the 317 functions with
a stack argument, 9 have zero-sized ones only; the other 308 store nonempty arguments to the
outgoing area and wait for option 2 (§8).

**Slice G16: shifted adds** (`GoFV/Gen/Check16.lean`, `checkG16 lc ps bstart g`, returning G4's
tables; proven sound, `g16_value`, `g16_term`, `g16_nilPanic`): G15 with `ADDshiftLL [k] x y`
(`addShKind`, `VK16.addSh`), accepted as G1 accepts `ADD`: no temporary, both arguments and the
result in registers, the result of at least 8 bits and no wider than either argument, `0 ≤ k <
64`. Genssa emits `ADD Rm<<k, Rn, Rd` (`genshift`, `ssa.go:141`), the source operand `makeshift`'s
`TYPE_SHIFT` with offset `(Rm & 31) << 16 | SHIFT_LL | k << 10` (`shiftLLA`). Every
`ADDshiftLL` of quick-v10 is accepted.

How the proof discharges G16's obligations (`G16.lean`): `runLoc` runs Phase 1's `Arm64.addSh …
.ll k`, `addP` of `x` and `y`'s register shifted left by `k` (`stepLoc_addSh`); the machine's
shifted operand reads `X[m] <<< k` (`ctx_src_shiftLL`), so the `ADD` writes `X[n] + (X[m] <<< k)`
(`progStep_addShiftLL`). A left shift keeps agreement on the low bits (`sw_shl`), so the sum is
related on the low bits of the result's class, with `ADD`'s pointer case (`Value.lean`: `lo_addP`,
`addP` of an addend related on the low bits; `lo_addSh`; `g16_addSh`). G15's values go through
`vk15_step`. No new premise.

**Slice G17: the goroutine** (`GoFV/Gen/Check17.lean`, `checkG17 lc ps bstart g`, returning G4's
tables; proven sound, `g17_value`, `g17_term`, `g17_nilPanic`): G16 with `GetG mem` (`getGKind`,
`VK17.getG`): no temporary, the memory its only argument, homed in the `g` register (`gReg`, Go
register 26, `R28`; regalloc's `hasGReg` case) at a 64-bit shape; no code (`ssagen`'s
`OpGetG`). Every `GetG` of quick-v10 is accepted.

How the proof discharges G17's obligations (`G17.lean`): `runLoc` runs Phase 1's `evalPure`, the
pointer to the start of the opaque global `runtime.g` (`stepLoc_getG`), and writes it to `g`. The
machine does not move; `X28` holds the activation's goroutine `E.g` (`FrameRel`), and the new
premise `GetGOK` asks that `ι` put `runtime.g` there (a property of the injection, kept by
`E.Extends`; STATUS Assumptions), so the pointer is related to `X28` and `LocMatch` holds with only
`runLoc`'s register written (`locMatch_setReg_keep`, `g17_getG`; `finish_reg` would write `X28`,
which `destOK` excludes). G16's values go through `vk16_step`; a nil check of G17's kinds is
G7's (`vk16_nil`, `vk17_nil`), so later slices extend `g17_nilPanic` by one case each.

**Slice G18: register-index stores** (`GoFV/Gen/Check18.lean`, `checkG18 lc ps bstart g`,
returning G4's tables; proven sound, `g18_value`, `g18_term`, `g18_nilPanic`): G17 with the integer
register-index stores `MOV{D,W,H,B}storeidx ptr idx val mem` and the scaled `MOVHstoreidx2`,
`MOVWstoreidx4`, `MOVDstoreidx8` (`storeIdxOp?`, `stIdxKind`, `VK18.stIdx`): no temporary, the
memory shape and no home, `ptr` and `idx` in registers of class 64, `val` in a register as a
store's (`8n` bits, or a boolean byte), the memory last; one store to `idxA` (`(Rp)(Ri<<sh)`).
Every integer register-index store of quick-v10 is accepted.

How the proof discharges G18's obligations (`G18.lean`): `runLoc` runs `arm64Op`'s `stIdx`, the
`n`-byte store of `val` at the address of G14's `idxSum` (`stepLoc_storeIdx`, from a four-argument
`storeIdx_core`); it is `stuck` when there is no address or the write is invalid, so a successful
step wrote valid bytes and there is no new premise. The address is related to the machine's
`X[p] + (X[i] <<< sh)` as G14's (`lo_idxSum`, `lo64_rel`, `addr_rel`, `ctx_mem_idx`), and the write
keeps `MemInj`, `SepFrom` and the frame as G3's stores (`memInj_storeN`, `op_mem2`,
`progStep_storeAt`; `g18_stIdx`). G17's values go through `vk17_step`; nil checks through
`vk18_nil`.

**Slice G19: bounds panics** (`GoFV/Gen/Check19.lean`, `checkG19 lc ps bstart g`, returning G4's
tables; proven sound, `g19_value`, `g19_term`, `g19_nilPanic`, `g19_boundsPanic`): G18 with
`LoweredPanicBounds{RR,RC,CR,CC} [kind] … mem` (`pbOp`, `pbKind`, `VK19.pb`): no temporary, the
memory shape and no home, register operands of class 64 in `R0`–`R15`, the memory last. Genssa
(`ssa.go:1752-1835`) moves a constant outside `0..31` into `R0` or `R1` (`MOVD $c, Rk`), then emits
`PCDATA $PCDATA_PanicBounds, $c` with `c` the `abi.BoundsEncode` of the kind's code, its
signedness and the operands (`pbEnc`), then `CALL runtime.panicBounds(SB)` (`pbPats`, `pbInfo`);
`pbOK` checks that the `PCDATA_PanicBounds` in force at that `CALL` (`pbData`) is `c`. A `CR` whose
constant index is outside `0..31` is rejected (#541: genssa, as Go, moves it without marking it in
the encoding, so the runtime reports the index 0 or 1; 2 functions of quick-v10). Every other
bounds panic of quick-v10 is accepted.

How the proof discharges G19's obligations (`G19.lean`): `runLoc` runs Phase 1's `panicBounds`
(`stepLoc_pb_panic`), which never steps to a state (`stepLoc_pb_ne_ok`), so `g19_value`,
`g19_term` and `g19_nilPanic` are G18's with one more impossible case and no new premise. The new
theorem `g19_boundsPanic` runs the `MOVD`s (`pstar_pbMovs`), the `PCDATA` no-op and the `CALL`
(`progStep_callSym`) to the symbol of `runtime.panicBounds` with `X30` the return address; there
the premise `BoundsOK` (the hook panics with `boundsPanic` of the `PCDATA_PanicBounds` value in
force at that `CALL`; STATUS Assumptions) gives the machine's panic. `boundsDecode_pbEnc` inverts
the encoding, a register operand of class 64 is its machine word (`pb_reg`), a moved constant the
word `MOVD` wrote, an encoded constant itself; `boundsPanic_agree` gives `BoundsAgree`: the same
panic, or, for a constant index of a signed kind `k` (the encoding records signedness only for a
register index), the unsigned kind `k + 1` of the same nonnegative index, which Go reports with
the same message. `Hooks.lean`'s `boundsPanic` (factored out of `panicBoundsHook`) maps
`BoundsConvert` (code 8) to kind 16, `ssa.BoundsConvert` (`cmd/compile/internal/ssa/op.go`:
`BoundsIndex` = 0 … `BoundsConvert` = 16, `BoundsKindCount` = 17).

**Slice G20: `MOVDnop` after its narrow load** (`GoFV/Gen/Check20.lean`, `checkG20 lc ps bstart
g`, returning G4's tables; proven sound, `g20_value`, `g20_term`, `g20_nilPanic`,
`g20_boundsPanic`): G19 with `MOVDnop x` (`nopKind`, `VK20`): no temporary, `x` its only
argument, homed in `x`'s register (one G1 may write) at an integer class, `x` of class 8, 16 or
32, no code. `runLoc` runs it as `movdLoc`, the 64-bit zero or sign extension of `x`'s low bits
that `LocCtx.signOf` names from `x`'s producer; the machine register holds that word only if the
instruction that wrote it extended so. The upper-bit table `uAt lc blk i` is the entry `uEntry`
of the value before `i`: after a narrow load of `n` bytes (`narrowLd?`: `MOV{B,H,W}{,U}load` of a
register address or a global, as G3; `MOV{B,H,W}{,U}loadidx*`, as G14) homed in register `r` at
class `c ∈ {8, 16, 32}`, `8n ≤ c`, `(r, c, sg)` with the load's signedness; nothing after any
other value or at a block's start. `movdOK` requires each `MOVDnop x` (and, from G21, each
`MOVDreg x`) to find `(x`'s register, `x`'s class, `signOf x)` there. This is narrower than §8's
dataflow table, which needs every slice to say which registers it keeps: on quick-v10, 1,300 of
the 1,520 `MOVDnop`s follow their load directly, and 607 of the 750 functions with a `MOVDnop`
have only such ones.

How the proof discharges G20's obligations (`G20.lean`): `UOK m (r, c, sg)` says the machine's
`X` register of `r` is the extension of its low `c` bits (`ExtOK`). The narrow loads establish it:
`g3_loadW` and `g14_idxW` (beside `g3_load` and `g14_idx`, on `op_reg2W`) expose the register file
the load writes, the extension of the `n` loaded bytes (`extOK_load`, `sext_bit`). `vk13_narrow`,
`vk19_narrow` and `vk3_idx_false` peel the narrow loads out of G19's cases, and `uEntry_spec`
names them. `g20_value` has `g19_value`'s statement with the premise `UOK m (uAt lc blk i)` and
the conclusion `UOK m' (uAt lc blk (i + 1))`; every value other than a narrow load concludes
`UOK m' none`, which is `True`. For `MOVDnop` (`stepLoc_nop`, `g20_nop`) the machine does not
move: `movdOK_spec` puts `x`'s entry in the table before it, so the register is the extension of
its low bits, which `LocMatch` relates to `x`, and `lo_movd` gives `ValRel` of `movdLoc`'s
64-bit result. One value is `vk20_step` (`vk19_step`'s statement, with the table's entry for a
`MOVDnop`/`MOVDreg` argument as a premise and `UOK m' (uEntry lc v)` as a conclusion), which
`g20_value` applies. G19's bounds-panic core is shared as `vk19_boundsPanic`. No new trusted
premise.

**Slice G21: `MOVDreg` after its narrow load** (`GoFV/Gen/Check21.lean`, `checkG21 lc ps bstart
g`, returning G4's tables; proven sound, `g21_value`, `g21_term`, `g21_nilPanic`,
`g21_boundsPanic`): G20 with `MOVDreg x` (`movRegKind`, `VK21`): no temporary, one argument in a
register other than `ZERO` at class 8, 16 or 32, the value in a register G1 may write at class 8,
16, 32 or 64. Genssa emits it as `Copy` (`ssa.go:579`): nothing when the registers agree
(`regSame`), else `MOVD Rx, Rv` (`regMov`). `runLoc` runs it as `MOVDnop` (`movdLoc`), and
`movdOK` asks the same table entry. The proof (`G21.lean`): `regSame` is `g20_nop`; `regMov`
(`g21_mov`) runs the `MOVD` (`progStep_movReg`, `op_reg2W`), which copies the whole register
that `UOK` says is the extension `movdLoc` writes (`lo_movd`); `vk21_step` and `g21_value` as
G20's. Of the 27 functions `MOVDreg` alone kept out of G20, the 14 whose every `MOVDreg` follows
its load directly are in G21 (4,342 functions); the other 13 need §8's register-frame lemmas.

**Slice G22: pair loads and stores of globals** (`GoFV/Gen/Check22.lean`, `checkG22 lc ps bstart
g`, returning G4's tables; proven sound, `g22_value`, `g22_term`, `g22_nilPanic`,
`g22_boundsPanic`): G21 with `LDP` and `STP` whose aux names a global and whose address argument
is `SB` (`globPair`, `globPairKind`, `VK22`), with G4's operand conditions. Genssa emits `LDP
sym+off(SB), (Ra, Rb)` and `STP (Rx, Ry), sym+off(SB)` (`ssagen.AddAux`); every `pair load shape`
rejection after G21 was one (748 `LDP`s of globals in 347 functions, 124 with no other blocker).
The proof (`G22.lean`): `runLoc`'s `pairAddr` names the global's block at the offset and 8 bytes
above (`pairAddr_glob`), the machine accesses the linked symbol address plus the offset and 8
bytes above (`progStep_globLdp`, `progStep_globStp`), where `G2Env.glob` injects the block; the
rest is G4's pair load and store at that address (`g22_ldp`, `g22_stp`). No new trusted premise.
G22 accepts 4,472 functions.

**Slice G23: flags to a register** (`GoFV/Gen/Check23.lean`, `checkG23 lc ps bstart g`, returning
G4's tables; proven sound, `g23_value`, `g23_term`, `g23_nilPanic`, `g23_boundsPanic`): G22 with
the comparison pseudo-ops `Equal`, `NotEqual`, `LessThan`, …, `GreaterEqualU` and their
floating-point and `Noov` forms (`Cond.ofOp`; `csetKind`, `VK23`): no temporary, one argument of
the flags shape with no home, a boolean result in a register G1 may write. Genssa emits `CSET cond,
Rd` with `cond` the `SPECIAL` operand `condBits` names. The proof (`G23.lean`): `runLoc` runs
`Arm64.cset`, the boolean the condition gives on the flags register (`stepLoc_cset`); the machine
writes 1 or 0 by `ConditionHolds` on `NZCV` (`progStep_cset`), for the same condition (`cset_cond`,
decided per op); `FlagsRel` makes the two agree (`onVal_holds`, `valRel_cset`, `g23_cset`). No new
trusted premise. G23 accepts 4,624 functions.

**Slice G24: `SP` anywhere** (`GoFV/Gen/Check24.lean`, `checkG24 lc ps bstart g`, returning G4's
tables; proven sound, `g24_value`, `g24_term`, `g24_nilPanic`, `g24_boundsPanic`): G23 with `SP`
after the entry values (`vkind24`, `VK24`), where the register allocator rematerializes it next to
its users (in a later block, or after code in the entry block). Up to G23, `SP` is an activation
value (`entryOp3`), which only the entry block's head may hold. G24 runs it as a value without
code anywhere, as G3 runs `SB`: no temporary, no argument, a register shape, no home or the home
`SP` (`spReg`, 30), which has no X or V register (`objX? 30 = none`), so `LocMatch` does not
relate it. Its users are the accesses of frame variables (G6), whose `symAddr` ignores the base.
`g24_value`'s premise that `v` is no activation value becomes `entryOp24` (G3's but `SP`), which
`entryOp3` implies (`entryOp24_of_3`). The proof (`G24.lean`): `runLoc` writes `SP`'s value to its
home (`stepLoc_sp`); no code runs and the machine state stays related (`g24_sp`, as `g3_sb`). No
new trusted premise. G24 accepts 4,718 functions.

**Slice G25: conditional selects and bit tests** (`GoFV/Gen/Check25.lean`, `checkG25 lc ps bstart
g`, returning G4's tables; proven sound, `g25_value`, `g25_term`, `g25_nilPanic`,
`g25_boundsPanic`): G24 with `CSEL [cc] x y f` and `CSEL0 [cc] x f` (`CSEL cond, Rx, Ry|ZR, Rd`,
`cselKind`) and `TSTconst [k] x`/`TSTWconst [k] x` (`TST`/`TSTW $k, Rn`, `tstKind`; `VK25`). A
select has no temporary, an auxint naming a condition (`ccOp?`, `Cond.ofOp`; `cond` is
`condBits`), the flags argument last with no home, and register arguments of classes at least the
result's class `c ≥ 8`. A bit test has no temporary, a flags result with no home, and its
argument's class covers the test's datasize or `0 ≤ k < 2^class` (`tstOK`: `k` then reads none of
the unknown upper bits). The proof (`G25.lean`): the machine step (`progStep_csel`,
`progStep_tst`, `progStep_tstw`) picks `Rx` or `Ry`/`ZR` by `ConditionHolds` on `NZCV`, which
`FlagsRel` makes agree with `runLoc`'s `condOn` (G23's `cset_cond`/`onVal_holds`; `valRel_csel`,
`valRel_csel0` via `lo_regVal`), and the bit tests' `ANDS` flags are `logicFlags` of the low bits
(`flagsRel_tst`, `flagsRel_tstw` via `and_low`, `tst_mask`). The statements are G24's over
`checkG25`, with the same premises. No new trusted premise. G25 accepts 4,925 functions.

**Slice G26: functions with no arm64 op** (`GoFV/Gen/Check26.lean`, `checkG26 lc ps bstart g`,
returning G4's tables; proven sound, `g26_value`, `g26_term`, `g26_nilPanic`, `g26_boundsPanic`):
G25 on a function that holds an arm64 op or block kind (`Func.lowered`), and `checkNL` on one that
holds none. G1–G25 reject such a function (`not lowered`: 254 on quick-v10 after G25), although it
went through `lower`. All 254 are empty bodies (209: `InitMem`, `MakeResult`, `Ret`) or return
their register arguments (`ArgIntReg`), possibly after a `Copy` (10), `Convert` (6) or `InlMark`
(1); one has a `Plain` block. `runLoc` runs them in Phase 1's mode: values are read with
`Val.retype`, not as registers (`Val.retypeL`), and every G-slice lemma assumes `lowered`.
`checkNL` is G25's check with the value check `vkindNL` (G1's `MakeResult`, `InlMark` and `Copy`;
the activation values as before) and `Ret` blocks only (`allRet`). The proof (`G26.lean`): at a
register's shape, `Val.retype` is `Val.retypeL`'s value or `poison` (`retype_cases`), so reads stay
related and of their class (`valRel_retype`, `fits_retype`, `arg_relP`). `InlMark` and
`MakeResult` change nothing (`write_result_noopP`). `Copy` writes its argument through a `MOVD` or
within one register (`stepLoc_copyP`, `op_regN`, `nl_core`). A `Ret` block goes to no
successor, and no value is a nil check or bounds panic (`nl_ops`). The statements are G25's over
`checkG26`, with the same premises. No new trusted premise. Composing a whole function from them
also needs a Phase-1-mode result mapping at `Ret`. G26 accepts 5,172 functions. The 7 rejected
for having no arm64 op have a `Convert` or a `Plain` block (G30 takes the `Convert`s).

**Slice G27: shifted logic ops** (`GoFV/Gen/Check27.lean`, `checkG27 lc ps bstart g`, returning
G4's tables; proven sound, `g27_value`, `g27_term`, `g27_nilPanic`, `g27_boundsPanic`): G26 with
`ANDshiftXX`, `ORshiftXX`, `XORshiftXX` and `BICshiftXX [k] x y` (`XX` one of `LL`, `RL`, `RA`:
`x op (y SHIFT k)`). genssa emits one `AND`/`ORR`/`EOR`/`BIC Rm SHIFT k, Rn, Rd` (`genshift`), whose
source operand is `makeshift`'s `TYPE_SHIFT` with offset `(Rm & 31) << 16 | typ << 22 | k << 10`
(`shiftA`). G27 accepts such a value with no temporary, two register arguments, a result of at
least 8 bits no wider than `x`, and `0 ≤ k < 64`; `y` must be at least as wide as the result for
`LL`, and of class 64 for `RL` and `RA`, whose result reads `y`'s upper bits. The proof
(`G27.lean`): `runLoc` computes `Arm64.opSh` of the shift kind (`shK`) and the bitwise op (`logF`)
(`stepLoc_logSh`); the machine reads `X[m]` shifted by the same `Shift.apply` (`ctx_src_shift`)
and writes `X[n] op (X[m] SHIFT k)` (`progStep_logSh`). A bitwise op's low bits depend only on its
operands' low bits (`logF_low`), and so do a left shift's (`shl_low`); a class-64 register equals
its machine word, so the result is related on its class (`lo_logSh`, `g27_logSh`). On a function
with no arm64 op, `checkG27` is `checkG26` (`checkG26_of_27`). The statements are G26's over
`checkG27`, with the same premises. No new trusted premise. G27 accepts 5,261 functions; in 26
others a shifted logic op fails the width rule (`shifted logic widths`).

**Slice G28: `LoweredMemEq`** (`GoFV/Gen/Check28.lean`, `checkG28 lc ps bstart g`, returning G4's
tables; proven sound, `g28_value`, `g28_term`, `g28_nilPanic`, `g28_boundsPanic`): G27 with
`LoweredMemEq p q n mem`, which genssa emits as `CALL runtime.memequal(SB)` (ABIInternal). Its
register constraints put `p`, `q`, `n` in `R0`, `R1`, `R2` and the result in `R0`, and it clobbers
what a call does. G28 accepts it with no temporary, `p`, `q`, `n` homed in `R0`–`R2` at class 64,
the memory last and the boolean result in `R0` (`memEqKind`). The statements are G27's over
`checkG28`, under `G28Env` (`G10Env`, and a function with `LoweredMemEq` has a frame, since the
`CALL` overwrites `X30`), with a new trusted premise for values, `MemEqOK` (`MemEqSpec`, STATUS
Assumptions): from `runtime.memequal`'s symbol, with `X0`–`X2` related to the arguments and the
memory injected, the hook returns to `X30` with `SP`, `R28`, `R29` and the memory kept and `X0`
related to `memEq [p, q, n, mem]`. The proof (`G28.lean`): `runLoc` clobbers what a static call
does and writes `memEq` of the arguments to `R0` (`clobber_memEq`, `evalOpL_memEq`); the machine
runs the `CALL` (`progStep_callSym`) and the hook (`g28_memEq`); every other register is `poison`
or one a call keeps (`clobber_memEq_reg`). G28 accepts 5,332 functions; 9 others blocked only by
`LoweredMemEq` after G27 are now blocked by `MOVDnop/MOVDreg: upper bits unknown`.

**Slice G29: the upper-bit table within a block** (`GoFV/Gen/Check29.lean`, `checkG29 lc ps
bstart g`, returning G4's tables; proven sound, `g29_value`, `g29_term`, `g29_nilPanic`,
`g29_boundsPanic`): G28 with a table of several entries in place of G20's `uAt`, which names only
the previous value's load. The table `uL lc blk i` is a list of entries `(r, c, sg)` (Go register
`r` is the zero or sign extension of its low `c` bits) built value by value (`uStepL`): a narrow
load puts its `uEntry` in place of its register's entry, `MOVDnop` keeps the table, `MOVDreg x`
copies the entry of `x`'s register to its own (`movdRegStep`), and every other value empties it.
`movdOK29` asks that each `MOVDnop`/`MOVDreg` find its argument's entry in the list. The
statements are G28's over `checkG29`, with the same premises, except that `g29_value` takes the
invariant `UOKL m (uL lc blk i)` (every entry's `UOK`) in place of `UOK m (uAt lc blk i)` and
concludes `UOKL m' (uL lc blk (i + 1))`; the table is empty at a block's entry, so the premise is
trivial there. No new trusted premise. The proof (`G29.lean`): the table changes only across
values that write at most one X register, a narrow load its own (`vk19_narrowW`), `MOVDnop` none
(`g20_nop`, `m' = m`), `MOVDreg` a copy of another (`g21_mov`); the entries of the registers a
value does not write stay true (`KeepsX`, `uokl_filter`). G29 accepts 5,361 functions; 46 still
have `upper bits unknown` as their only reason and need the table across blocks.

**Slice G30: `Convert` in functions with no arm64 op** (`GoFV/Gen/Check30.lean`, `checkG30 lc ps
bstart g`, returning G4's tables; proven sound, `g30_value`, `g30_term`, `g30_nilPanic`,
`g30_boundsPanic`): G29 on a function with an arm64 op, and on one without, G26's `checkNL` that
also accepts `Convert x mem` as G12 does in lowered functions (`convKind`: `x` and the value in one
register of class 64, the memory last; no code). The 6 such functions on quick-v10 are pointer
methods such as `runtime.guintptr.ptr`. The statements are G29's over `checkG30`, with the same
premises. No new trusted premise. The proof (`G30.lean`): in Phase 1's mode `Convert` writes
`PtrOps.convert` of its argument read with `Val.retype`, again retyped (`stepLoc_convP`); a register
content of class 64 converts to one of class 64 related to the same machine word (`convert_rel`,
factored out of G12's `valRel_convert`), which `Val.retype` keeps (`valRel_retype`), so the shared
register needs no code (`nl_conv`). G30 accepts 5,367 functions. The one function with a `Plain`
block (test/decl `main`) is also blocked by `InitMem after the entry values`, so G30 leaves
`Plain` blocks out.

**Slice G32: simple ops** (`GoFV/Gen/Check32.lean`, `checkG32 lc ps bstart g`, returning G4's
tables; proven sound, `g32_value`, `g32_term`, `g32_nilPanic`, `g32_boundsPanic`): G30 with, in a
function with an arm64 op, the register ops `MUL`, `MNEG`, `AND`, `OR`, `XOR`, `BIC`, `EON`,
`ORN x y` (`op Rm, Rn, Rd`, `bin32?`), the constant ops `ORconst`, `XORconst [k] x` (`ORR`/`EOR $k,
Rn, Rd`, `binK32?`), the unary ops `NEG`, `MVN x` (`op Rm, Rd`, `un32?`), `CSINC [cc] x y f`
(`CSINC cond, Rx, Ry, Rd`, `csincOK`) and the store-release ops `STLR`, `STLRW`, `STLRB p x mem`
(`STLR{,W,B} Rx, (Rp)`, `stlr?`; `VK32`). An ALU op has no temporary and register arguments of
classes at least the result's class `c ≥ 8`; `AND`, `OR`, `XOR` of two booleans and `XORconst
[1]` of a boolean (Go's `!`) are accepted at class 1. `CSINC` is G25's `CSEL` with `y + 1`. A
store-release has no symbol, offset 0, a 64-bit address register and a value register of exactly
the access's width: `runLoc` runs it as the generic `AtomicStore{64,32,8}` (`Atomic.rmw` of
`fitPiece`), whose bytes are then the register's low bytes. The statements are G30's over
`checkG32`, with the same premises. No new trusted premise. The proof (`G32.lean`): `runLoc` runs
the ALU ops as `Arm64.op2`/`op1` of a word function (`binF`, `binKF`, `unF`; `stepLoc_alu32`,
`evalPure_bin32`, …), which the machine computes on the registers (`progStep_bin32`,
`progStep_binK32`, `progStep_un32`); each function's low `c` bits depend only on its operands' low
`c` bits (`binF_low`, `binKF_low`, `unF_low`, `lo_bin32`, …), and on 0/1 registers the boolean ops
give 0/1 (`valRel_binBool`, `valRel_xorBool`). `CSINC`'s `y + 1` is `Arm64.addP`'s, as
`ADDconst`'s (`regVal_addP`, `valRel_csinc`, `progStep_csinc`). A store-release is the generic
store of `fitPiece` of the value at its `asPtrWord` address (`stepLoc_stlr`), the same bytes as
G3's `n`-byte store when the value has the access's width (`encode_storeBytes`, `addr_asPtrWord`),
and the machine stores the register's low `n` bytes (`progStep_stlr`), so G3's store argument
applies (`g32_stlr`). The G32 ops empty the upper-bit table (`uStepL`), as every value outside
G29's does. G32 accepts 5,678 functions (+311 over G30).

**Slice G31: the upper-bit table across values and blocks** (`GoFV/Gen/Check31.lean`, `checkG31 lc
ps bstart g`, returning G4's tables; proven sound, `g31_value`, `g31_term`, `g31_nilPanic`,
`g31_boundsPanic`): G32 with a larger upper-bit table `uL31` in place of G29's `uL` on a function
with an arm64 op. Across a value of G1's kinds or G3's `CMPW`/`CMPWconst` (`keep31`: `Phi`, `ZERO`,
`InlMark`, `Copy`, `MakeResult`, `MOVDconst`, `ADD`, `SUB`, `ADDconst`, `SUBconst`, `CMP`,
`CMPconst`, `CMPW`, `CMPWconst`, and `MOVDload`/`MOVDstore` without symbol) the table keeps the
entries of the registers other than the value's register home (`uStep31`); every other value steps
as in G29 (`uStepL`). Each block starts with `uIn`: nothing at the entry block, elsewhere the
entries every reached predecessor ends with (`uFlow`, a forward dataflow to a fixed point), which
`uEdgesOK` checks (the entry starts empty, every successor's start is in its predecessor's end).
`movdOK31` asks each `MOVDnop`/`MOVDreg` to find its argument's entry in the table before it. The
statements are G32's over `checkG31`, with the same premises, except that `g31_value` takes `UOKL
m (uL31 lc (uIn lc bid) blk i)` and concludes `UOKL m' (uL31 lc (uIn lc bid) blk (i + 1))`, and
`g31_term` takes `UOKL m (uL31 lc (uIn lc bid) blk blk.values.size)` and concludes `UOKL m' (uIn lc
e.b)` at the successor; `uIn lc entry = []` (`uEdgesOK_entry`), so the premise is trivial at the
function's entry. No new trusted premise. The proof (`G31.lean`, `Keep31.lean`): a `keep31` value
is G3's (`vk32_vk3`, peeling `VK32` to `VK3`), and its step writes at most its register home's X
register (`XW`, now concluded by G1's `value_core` and G2's `g2_g1`; `g3_cmpw`, `g3_cmpwK` keep
every X register; `vk3_keep`), so the other registers' entries stay true (`uokl_keep`); every other
value steps as in G32 (`vk32_stepU`). A terminator keeps every X register (G1's `term_core`, G3's
`term_test`, `termK_stepX`), and each successor's start is in its predecessor's end
(`uEdgesOK_edge`). G31 accepts 5,703 functions (+25 over G32); 26 still have `upper bits unknown`
as their only reason, whose tables need frames for spills and reloads, `LDP`/`Select`, bounds
panics or `MOVBreg` to keep the entries.

**Slice G33: more single-instruction ops** (`GoFV/Gen/Check33.lean`, `checkG33 lc ps bstart g`,
returning G4's tables; proven sound, `g33_value`, `g33_term`, `g33_nilPanic`, `g33_boundsPanic`):
G31 with, in a function with an arm64 op, `CLZ`, `REV x` (`CLZ`/`REV Rm, Rd`, `un33?`) and
`SRAconst [k] x` (`ASR $k, Rn, Rd`, `0 ≤ k < 64`) of a 64-bit argument, `UBFIZ [k] x` (`UBFIZ $lsb,
Rn, $width, Rd`, `k = lsb · 256 + width < 2 ^ 16`) of an argument of class `ca` with `width ≤ ca` or
`c ≤ ca`, and `CMNWconst [k] x` (`CMNW $k, Rn`) of an argument of class at least 32 (`VK33`). An ALU
op has no temporary and a result of class `c ≥ 8`. The statements are G31's over `checkG33`, with
the same premises. No new trusted premise. The proof (`G33.lean`): `runLoc` runs the ops as
`Arm64.evalPure` (`stepLoc_alu33`); on a 64-bit argument the register is the machine word, so
`CLZ`/`REV` (`Arm64.clz`, `Arm64.rev`, the machine's `dp1Op`; `progStep_un33`) and `ASR`
(`Shift.ra`, `dp2Op`'s `ASRV`; `progStep_asrK`) agree with the machine (`lo_op1_64`). The machine's
`UBFIZ` is `Arm64.ubfiz` of the auxint `lsb · 256 + width` (`ubfiz_ofNat`, `progStep_ubfiz`); bit
`i < c` of the result is bit `i - lsb < width` of the argument, below its class (`lo_ubfiz`). `CMNW
$k, Rn` sets the flags of the 32-bit `ADDS` of the low words (`addSub_addFlags32`,
`progStep_cmnwConst`), which `CMNWconst`'s are (`flagsRel_cmnwK`). The G33 ops are outside `keep31`
and empty the upper-bit table (`keep31_alu33`). G33 accepts 5,812 functions (+109 over G31).
`CMNconst` (22 sole after G33) stays out: on a pointer without an integer form `runLoc` gives `Z`
clear (`Arm64.cmp1P`'s `zClear`), which only G1's `NoBarePtr` premise for `CMP`/`CMPconst` relates
to the machine; `LoweredGetCallerPC` (25) emits the pseudo-instruction `GETCALLERPC`, which the
machine model of P0 does not run (`obj7`'s `preprocess` makes it `MOVD LR` or `MOVD (RSP)`).

**Slice G34: the upper-bit table across more values** (`GoFV/Gen/Check34.lean`, `checkG34 lc ps
bstart g`, returning G4's tables; proven sound, `g34_value`, `g34_term`, `g34_nilPanic`,
`g34_boundsPanic`): G33 with a larger upper-bit table `uL34` in place of G31's `uL31` on a function
with an arm64 op. Besides `keep31`'s values, the table keeps the entries of the registers other
than the value's register home across the single-register ops of G3 (the extensions `MOV*reg`,
`ANDconst`, `SLLconst`, `SRLconst`, `UBFX`), G16 (`ADDshiftLL`), G23 (the condition values
`Equal` …), G25 (`CSEL`, `CSEL0`, `TSTconst`, `TSTWconst`), G32 and G33, the spills and reloads
(`StoreReg`, `LoadReg`) and `MOVDaddr` (`keep34`, `uStep34`). The dataflow (`uFlow34`, `uIn34`),
its check (`uEdgesOK34`) and `movdOK34` are G31's over `uStep34`. The statements are G33's over
`checkG34` with `uL34 lc (uIn34 lc bid)` in place of `uL31 lc (uIn lc bid)`, and `g34_term`
concludes `UOKL m' (uIn34 lc e.b)`; `uIn34 lc entry = []` (`uEdgesOK34_entry`). No new trusted
premise. The proof (`G34.lean`, `Keep34.lean`): the case lemmas of the kept kinds now conclude
`XW` (`g2_addr`, `g2_spill`, `g2_reload`, `g3_ext`, `g3_aluK`, `g3_ubfx`, `g6_addr`, `g16_addSh`,
`g23_cset`, `g25_csel`, `g25_csel0`, `g25_tst`, `g25_tstw`, `g32_bin`, `g32_binK`, `g32_un`,
`g32_csinc`, and G33's); `vk33_keep` peels `VK33` down to `VK2` and refutes every kind outside
`keepOps34` by its op (`keep34_mem`, `keep34_aux`), so a `keep34` value writes at most its home's X
register and the other entries stay true (`uokl_keep`); every other value steps as in G33
(`vk33_step`). G34 accepts 5,825 functions (+13 over G33); 16 still have `upper bits unknown` as
their only reason. `LDP` with `Select0`/`Select1` (a pair write) in the keep set would take 18 of
G33's 29.

**Slice G35: the upper-bit table across pair loads, and loads of frame variables**
(`GoFV/Gen/Check35.lean`, `checkG35 lc ps bstart g`, returning G4's tables; proven sound,
`g35_value`, `g35_term`, `g35_nilPanic`, `g35_boundsPanic`): G34 with a larger upper-bit table
`uL35` in place of `uL34` on a function with an arm64 op. Across the pair load `LDP` (G4's, G6's of
a frame variable, G22's of a global) and `Select0`/`Select1` of an `LDP` (`pairOp35`) the table
keeps the entries of the registers other than those of the value's home (`homeRegs`: the pair's
two, or the select's one); a narrow load at any operand, also G6's of a frame variable, puts its
entry in place of its register's (`ldEntry35`; G20's `uEntry` names only loads through a register
or of a global); every other value steps as in G34 (`uStep35`). The dataflow (`uFlow35`, `uIn35`),
its check (`uEdgesOK35`) and `movdOK35` are G34's over `uStep35`. The statements are G34's over
`checkG35` with `uL35 lc (uIn35 lc bid)` in place of `uL34 lc (uIn34 lc bid)`, and `g35_term`
concludes `UOKL m' (uIn35 lc e.b)`; `uIn35 lc entry = []` (`uEdgesOK35_entry`). No new trusted
premise. The proof (`G35.lean`, `Keep35.lean`): the pair loads now conclude that they write the X
registers of their pair (`PairW`; `g4_ldp`, `g6_ldp`, `g22_ldp`), a select of one that it keeps
every X register (`g4_sel`), and G6's load the extension of its bytes in its register (`g6_load`,
as G3's `g3_loadW`); `vk33_keep35` peels `VK33` down to `VK2` and refutes every other kind by its
op (`ops35`, `ops35_mem`) or, for a select of a write-barrier request, by its argument
(`sel_wb_pair`), so the entries of the other registers stay true (`uokl_pair`, `uokl_filter_x`)
and a load's entry holds (`uok_ldW`, `uokl_ld`); every other value steps as in G34 (`vk34_step`).
G35 accepts 5,838 functions (+13 over G34: 5 by the pair loads, 8 by the loads of frame
variables); 3 still have `upper bits unknown` as their only reason. The stores, the markers and
`Convert`, which write no X register, in the keep set would take 2 of them (`bytes.(*Buffer).ReadRune`
across a `MOVBstore`, `regexp/syntax.(*Prog).Prefix` across a `Convert`); the third
(`strings.(*stringFinder).next`) needs a `Copy` of a narrow load to copy its entry.

**Slice G36: register shifts, shifted adds and subtracts, `TST`** (`GoFV/Gen/Check36.lean`,
`checkG36 lc ps bstart g`, returning G4's tables; proven sound, `g36_value`, `g36_term`,
`g36_nilPanic`, `g36_boundsPanic`): G35 with, in a function with an arm64 op, `SLL`, `SRL`, `SRA x
y` (`LSL`/`LSR`/`ASR Rm, Rn, Rd`, `sh36?`) with `y` of at least 8 bits and `x` of at least the
result's class (`SLL`) or of 64 bits; `ADDshiftRL`, `ADDshiftRA`, `SUBshiftLL`, `SUBshiftRL`,
`SUBshiftRA [k] x y` (`ADD`/`SUB Rm SHIFT k, Rn, Rd`, G27's shifted operand `shiftA`, `shOp36?`,
`0 ≤ k < 64`) with `x` of at least the result's class and `y` too (`SUBshiftLL`) or of 64 bits; and
`TST x y` (`TST Rm, Rn`) of two 64-bit arguments (`VK36`). An ALU op has no temporary and a result
of class `c ≥ 8`. The statements are G35's over `checkG36`, with the same premises and G35's table.
No new trusted premise. The proof (`G36.lean`): `runLoc` runs the ops as `Arm64.evalPure`
(`stepLoc_alu36`); a register shift is `Arm64.op2` of a shift by `y` modulo 64 (`shF36`), which the
machine's `dp2Op` computes (`progStep_sh36`), and the amount reads only `y`'s low 6 bits
(`mod64_low`), a left shift only `x`'s low bits (G27's `shl_low`; `lo_sh36`). The shifted adds and
subtracts are Phase 1's `addSh`/`subSh`, `addP` of `x` and the shifted (negated) register of `y`
(`lo_shOp36`, with `ADD`'s pointer case), which the machine computes through the shifted operand
(`progStep_shOp36`). `TST`'s flags are `ANDS`' of the two registers (`progStep_tst36`,
`flagsRel_tst36`). The G36 ops empty the upper-bit table (`uStep35_alu36`). G36 accepts 5,967
functions (+129 over G35). `CMPshiftLL`/`CMPshiftRL` (13 and 28 sole after G36) stay out: as
`CMNconst`'s, their flags on a pointer without an integer form are Phase 1's `zClear` (`cmpSh`),
which only G1's `NoBarePtr` premise for `CMP`/`CMPconst` relates to the machine.

**Slice G37: multiplies, divides, byte and bit reversals, `SBFX`** (`GoFV/Gen/Check37.lean`,
`checkG37 lc ps bstart g`, returning G4's tables; proven sound, `g37_value`, `g37_term`,
`g37_nilPanic`, `g37_boundsPanic`): G36 with, in a function with an arm64 op, `UMULH`, `MULH`,
`UDIV`, `DIV x y` (`UMULH`/`SMULH`/`UDIV`/`SDIV Rm, Rn, Rd`, `full37?`) of two 64-bit arguments;
`MULW`, `UDIVW`, `DIVW`, `UMULL x y` (`MULW`/`UDIVW`/`SDIVW`/`UMULL Rm, Rn, Rd`, `w37?`), which read
the low words, of two arguments of at least 32 bits; `RBIT x` of a 64-bit argument and `REVW`,
`REV16W x` of one of at least 32 bits (`un37?`); `MADD`, `MSUB a x y` (`MADD`/`MSUB Rm, Ra, Rn,
Rd`, `a ± x · y`, `madd37?`) of arguments of classes at least the result's, and `MADDW`, `MSUBW` of
arguments of at least 32 bits; and `SBFX [k] x` (`SBFX $lsb, Rn, $width, Rd`, `k = lsb · 256 +
width`, `0 < width`, `lsb + width ≤` the argument's class) (`VK37`). An ALU op has no temporary and
a result of class `c ≥ 8`. The statements are G36's over `checkG37`, with the same premises and
G35's table. No new trusted premise. The proof (`G37.lean`): `runLoc` runs the ops as
`Arm64.evalPure` (`stepLoc_alu37`); on 64-bit arguments a register is the machine word, so `UMULH`,
`SMULH`, `UDIV`, `SDIV` (`binF37`) and `RBIT` agree with the machine (`progStep_bin37`,
`progStep_un37`); on arguments of at least 32 bits the low words are the machine's, which the `W`
ops and `UMULL` read, zero-extending their 32-bit results as the machine does. `MADD`/`MSUB` are
Phase 1's `madd`, `addP` of `a` and the product (or its negation), whose low bits read only the
factors' low bits (`lo_madd37`, with `ADD`'s pointer case); the machine computes `Ra ± Rn · Rm`
(`dp3Op`, `progStep_madd37`). `SBFX` sign-extends bits `lsb … lsb + width - 1`, all below the
argument's class (`lo_sbfx37`, `progStep_sbfx37`). The G37 ops empty the upper-bit table
(`uStep35_alu37`). G37 accepts 6,099 functions (+132 over G36).

**Slice G38: the acquire loads** (`GoFV/Gen/Check38.lean`, `checkG38 lc ps bstart g`, returning
G4's tables; proven sound, `g38_value`, `g38_term`, `g38_nilPanic`, `g38_boundsPanic`): G37 with,
in a function with an arm64 op, `LDAR`, `LDARW`, `LDARB p mem` (`LDAR`/`LDARW`/`LDARB (Rn), Rd`,
`ldar?`, offset 0, no symbol) of an address of 64 bits, a tuple of a component of class `8n` (an
integer of `n` bytes, or a pointer for `n = 8`) and the memory, homed in `(Rd;-)` with `Rd` a
register G1 may write and no temporary; `Select0` of one, homed in its register, and `Select1`,
the memory without a home, both without code (`VK38`). The statements are G37's over `checkG38`,
with G35's table; `g38_value`'s per-value premise `G38Pre` adds to `G14Pre` that an acquire load
reads valid bytes (`LdarPre`: Phase 1's `Mem.read` of its `n` bytes at the address in its register
succeeds), a run premise as G3's for the loads. No new trusted premise. The proof (`G38.lean`):
`runLoc` runs an acquire load as Phase 1's `atomicLoad` (`stepLoc_ldar`), the value at the
component's shape (`poison` if not naturally aligned) and the memory unchanged, which it writes to
`Rd` and the state's memory (`write_ldar`); at the component's shape that value is G3's `n`-byte
load (`ldar_val`; a pointer and a 64-bit integer decode 8 bytes alike, `decodePtr_eq`), related to
the zero extension of the `n` bytes the machine's `LDAR*` loads (`valRel_ldar`, `progStep_ldar`).
A component reads the tuple from `(Rd;-)` (`read_ldar`): `Select0` is `Rd`, which the machine
already holds (`g38_sel0`), `Select1` the memory (`g38_sel1`). The G38 values empty the upper-bit
table (`uStep35_ldar`, `uStep35_selLdar`). G38 accepts 6,380 functions (+281 over G37). An acquire
load whose step faults (`nilFaults`) faults on the machine too (`g51_obj_ldarPanic`, §9).

**Slice G39: the homes of removed values** (`GoFV/Gen/Check39.lean`, `checkG39 lc ps bstart g`,
returning G4's tables; proven sound, `g39_value`, `g39_term`, `g39_nilPanic`, `g39_boundsPanic`):
`regalloc` records a home for every value it allocated, and the export keeps the homes of the
values `trim` removes afterwards (the `Phi`s of a block it merges), of shape `Ty.other`, which
G1's `homeOK` rejects. `checkG39` checks `refsLive lc` (every value of the function is at an ID
that is a value of the function, and so are its arguments), then is `checkG38` on `liveCtx lc`,
`lc` with the homes of the IDs that are no value of the function dropped. The statements are
G38's on `liveCtx lc`; no new premise. The proof (`G39.lean`): `runLoc` reads homes only of the
values it runs, their arguments, the blocks' controls and the arguments of a `MakeResult` control,
all values of the function under `refsLive`, so it runs alike under `lc` and `liveCtx lc`
(`stepLoc_live`, `enterListLoc_live`, `stepTermLoc_live`, `runLoopLoc_live`, `runCtxLoc_live`,
`runLoc_live`: `runLoc` is `runCtxLoc` on `liveCtx`). G39 accepts 6,447 functions (+67 over G38).

**Slice G40: `InitMem` after the entry values** (`GoFV/Gen/Check40.lean`, `checkG40 lc ps bstart
g`, returning G4's tables; proven sound, `g40_value`, `g40_initMem`, `g40_term`, `g40_nilPanic`,
`g40_boundsPanic`): G39 with, in a function with an arm64 op whose values keep the memory
(`memPure`: every value a `Phi`, an `InitMem` without temporary or home, a `MakeResult` whose
write changes nothing (G1's conditions), or of a shape without a memory component, `memInert`),
`InitMem` anywhere (`schedule` places it next to its only use, e.g. in the return block): no
temporary, no argument, no home, shape `mem`, no code. `runLoc` runs `InitMem` as the
activation's initial memory. Every step of such a function keeps the state's memory at the
initial memory (`MemInit`; `memInit_stepLoc`: a `Phi` changes nothing, a value of a
memory-free shape writes no memory, `stepLoc_shape`, `clobber_memfr`, `write_memfr`; `InitMem`
writes the initial memory, `stepLoc_initMem`; `MakeResult` changes nothing, `write_result_noop`;
`memInit_stepTermLoc`: a terminator only stages its controls), and the run starts with it; so
`InitMem` changes nothing (`g40_initMem`, under `MemInit`, which the run discharges with these
lemmas). `g40_value`, `g40_term`, `g40_nilPanic`, `g40_boundsPanic` are G39's statements over
`checkG40`. G40 accepts 6,472 functions (+25 over G39); `InitMem` after the entry values remains
the sole blocker of 13 functions, whose memory a call or store changes before the return block.

**Slice G41: `CMNconst`, `CMPshiftLL`, `CMPshiftRL`** (`GoFV/Gen/Check41.lean`, `checkG41 lc ps
bstart g`, returning G4's tables; proven sound, `g41_value`, `g41_initMem`, `g41_term`,
`g41_nilPanic`, `g41_boundsPanic`): G40 with, in a function with an arm64 op, the compares
`CMNconst [k] x` (`CMN $k, Rn`) and `CMPshiftLL`/`CMPshiftRL [k] x y` (`CMP Rm SHIFT k, Rn`, G27's
shifted operand, `0 ≤ k < 64`) of 64-bit arguments, of the flags shape, without home or temporary.
`runLoc` runs them as Phase 1's `cmp1P`/`cmpSh` (`stepLoc_alu41`): on registers, the flags of the
64-bit `ADDS`/`SUBS`, which the machine computes (`progStep_cmnConst`, `progStep_cmpShift`,
`flagsRel_cmnK`, `flagsRel_cmpSh41`); on a pointer without an integer form as first argument, `Z`
clear (`Arm64.zClear`), which the machine does not compute. `g41_value`'s per-value premise
`G41Pre` is `G38Pre` and the run premise `CmpPre` (the first argument of a G41 compare is no such
pointer, G1's `NoBarePtr`, as G1's premise for `CMP`/`CMPconst`): a property of the run state, not
a trusted hook. `g41_initMem`, `g41_term`, `g41_nilPanic`, `g41_boundsPanic` are G40's statements
over `checkG41`. G41 accepts 6,570 functions (+98 over G40).

**Slice G42: `ANDconst` widening a narrow argument** (`GoFV/Gen/Check42.lean`, `checkG42 lc ps
bstart g`, returning G4's tables; proven sound, `g42_value`, `g42_initMem`, `g42_term`,
`g42_nilPanic`, `g42_boundsPanic`): G41 with, in a function with an arm64 op, `ANDconst [k] x`
(`AND $k, Rn, Rd`) whose result class `c ≥ 8` exceeds the class `ca` of `x` (G3 asks `c ≤ ca`),
when `0 ≤ k < 2^ca`: Go's rules emit it for `x & k` of a narrow `x`, mostly a narrow load, at a
wider type. Only the low `ca` bits of `x`'s register are known, but the mask clears every bit at or
above `ca` both in `runLoc`'s result (`x` zero-extended, `Arm64.reg`) and on the machine, so the
machine's whole word is the result (`imm_bit_false`, `lo_andW`, `valRel_andW`), read back at any
class. The op writes only its register, so G35's table keeps the other entries (`uStep35_andK`,
`uokl_keep`). No new premise: `g42_value`'s per-value premise is G41's `G41Pre`; `g42_initMem`,
`g42_term`, `g42_nilPanic`, `g42_boundsPanic` are G41's statements over `checkG42`. G42 accepts
6,609 functions (+39 over G41; every `shift or mask widths` sole blocker after G41 was such an
`ANDconst`, and one of their 40 functions is now blocked only by G35's upper-bit check).

**Slice G43: `InitMem` where the memory is still the initial one** (`GoFV/Gen/Check43.lean`,
`checkG43 lc ps bstart g`, returning G4's tables; proven sound, `g43_value`, `g43_initMem`,
`g43_term`, `g43_nilPanic`, `g43_boundsPanic`): G42 with `InitMem` at clean positions also in a
function that calls or stores. The clean blocks `C` (`cleanBlocks`) are those that no block with a
value that changes the memory (`memKeep` false) reaches in one step or more; the check asks that
`C` be closed backwards (`cleanOK`: a block with a successor in `C` is in `C` and all its values
keep the memory), and that every position `(b, i)` of an `InitMem` be clean (`cleanAt`: `b ∈ C`,
the values of `b` before `i` keep the memory; `initMemClean`, which finds the `InitMem`s by the
op of the value at each position, so the composition needs no `v.id = id`). In a function whose
values all keep the memory every position is clean, so G43 contains G40's case. At a clean
position the state
holds the activation's initial memory (`MemInit`): the run starts with it, a value that keeps the
memory keeps it (`memInit_stepLoc_keep`), a step to the next clean position keeps the implication
`cleanAt → MemInit` (`memInit_clean_step`, `cleanAt_succ`), and a terminator to a block of `C`
leaves a block whose end is clean (`cleanOK_edge`, `memInit_clean_term`). So `InitMem` changes
nothing there (`g43_initMem`: G41's statement without `memPure`, under `MemInit`, which the run
discharges with these lemmas). In the 13 functions G40 left, the stores and calls sit after the
`InitMem` in its block, in blocks reached only through it, or in blocks that end in a panic.
G43 accepts 6,622 functions (+13 over G42).

**Slice G44: floating-point moves, loads and stores** (`GoFV/Gen/Check44.lean`,
`checkG44 lc ps bstart g`; proven sound, `g44_value`, `g44_initMem`, `g44_term`, `g44_nilPanic`,
`g44_boundsPanic`, `GoFV/Proof/Gen/G44.lean`; machine side `GoFV/Proof/Gen/FMove.lean`): stage (a)
of the float slice. G43 with the values that move a float's bit pattern (`.int .w32`/`.int .w64`,
`fTy`) through the V registers (`objV?`, obj register `REG_F0 + k`): `Copy` between `F` registers
(`FMOVS`/`FMOVD Fs, Fd` or nothing), `FMOVSload`/`FMOVDload` and `FMOVSstore`/`FMOVDstore` at G3's
accesses, `FMOVSgpfp`/`FMOVDgpfp` (`Rn → Fd`, an X register of at least the result's class),
`FMOVSfpgp`/`FMOVDfpgp` (`Fn → Rd`) and `FMOVSconst`/`FMOVDconst` (`FMOVS`/`FMOVD $c, Fd`, the
`FCONST` bits of `auxInt`; `FMOVS` rounds them to single precision as Phase 1's `Const32F`).
`LocMatch` already relates a V register to the low bits of its value (`FValRel`); the new pieces are
`locMatch_setRegV`/`op_regV` (a V register write), `arg_relV` (a float argument read at its shape),
`fvalRel_of_valRel`/`valRel_of_fvalRel` (between the X and V relations, under `AddrAgree`), and the
`progStep` lemmas of the `FMOV` forms. New run premise `FLoadPre` (`G44Pre := G41Pre ∧ FLoadPre`): a
float load reads valid bytes (G3's clause for `loadOp?`), and what it reads at its float shape is no
pointer without an integer form (`Ptr.word` of a global or a frame temporary; a pointer has no V
register form under `FValRel`). No trusted premise. Witness `genG44_witness`
(`math.Float64frombits`: `FMOVD R0, F0` of `1.0`'s bits). G44 accepts 6,652 functions (+30 over
G43).

**Slice G45: register-index float loads and stores** (`GoFV/Gen/Check45.lean`,
`checkG45 lc ps bstart g`; proven sound, `g45_value`, `g45_initMem`, `g45_term`, `g45_nilPanic`,
`g45_boundsPanic`, `GoFV/Proof/Gen/G45.lean`): G44 with `FMOV{S,D}loadidx{,4,8} ptr idx mem` and
`FMOV{S,D}storeidx{,4,8} ptr idx val mem` (`fLoadIdxOp?`, `fStoreIdxOp?`). Phase 1 runs them as
the integer ones (`Arm64.loadIdx`, `stIdx`: the `n` bytes at `idxSum (2^sh)`); genssa emits one
`FMOVS`/`FMOVD` from or to `(Rp)(Ri<<sh)` (`idxA`, G14 and G18), with `ptr` and `idx` in X
registers of class 64 and the float in an `F` register at a float shape of `8n` bits. The address
is G14's (`lo_idxSum`, `ctx_mem_idx`), the value G44's (`fvalRel_of_valRel` for a load,
`valRel_of_fvalRel` and `memInj_storeN` for a store). New run premise `FIdxPre` (`G45Pre := G44Pre
∧ FIdxPre`): a float register-index load reads valid bytes at its address (G14's `IdxPre`) and
what it reads at its float shape is no pointer (as `FLoadPre`). No trusted premise. Witness
`genG45_witness` (`sort.Float64Slice.Swap`: `FMOVD (R0)(R3<<3), F0` of `x[1] = 1.5`). G45 accepts
6,657 functions (+5 over G44: `sort.Float64Slice.Swap` and its pointer method,
`breakPatternsOrdered`, `heapSortOrdered`, `reverseRangeOrdered` at `float64`).

**Slice G46: float arithmetic, conversions and compares** (`GoFV/Gen/Check46.lean`,
`checkG46 lc ps bstart g`; proven sound, `g46_value`, `g46_initMem`, `g46_term`, `g46_nilPanic`,
`g46_boundsPanic`, `GoFV/Proof/Gen/G46.lean`; value lemmas and machine steps
`GoFV/Proof/Gen/FArith.lean`): stage (b) of the float slice. G45 with one Prog each, opcode
`opAsm op`, on registers of the op's classes (tables `fp2Of`, `fp1Of`, `cvtfOf`, `fcvtzOf`,
`fcmpOf`, `fp3Of`, which give the operands of `Exec.lean`'s `fp2Op`/`fp1Op`/`fcmpOp`/`fp3Op`):
`FADD`/`FSUB`/`FMUL`/`FDIV` (`op Fm, Fn, Fd`), `FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS`,
`SCVTF`/`UCVTF` of an X register of at least the input's width, `FCVTZS`/`FCVTZU` into an X
register of the output's width, `FCMP Fm, Fn` and `FCMP $(0.0), Fn` of a flags value with no
home, and the fused `FMADD`/`FNMSUB` (`op Fm, Fa, Fn, Fd` with `Fn` the rest operand). The float
blocks `FLT`/`FLE`/`FGT`/`FGE` (and `LTnoov`/`GEnoov`) are `condBr` kinds (`BMI`/`BPL`,
`BLS`/`BHI`, `BGT`/`BLE`, `BGE`/`BLT`, `condAs`), so G1's terminator proof covers them; `FCMP`'s
flags are `fcmpFlags` on both sides. Phase 1 and the machine call the same `GoFV.IEEE` functions;
they disagree only on NaN operands (`FArith.lean`, each with an `#eval`-checked bit pattern):

* `FADD`/`FMUL`: Phase 1 orders the operands by encoding (`FOps.ordered`), the machine takes
  `Rn, Rm` = `arg0, arg1`; `FPAdd`/`FPMul` commute unless both operands are NaNs of one kind
  (`add_comm_of`, `mul_comm_of`), so the results differ exactly on `FNaNSwap arg0 arg1`
  (`FADDS 0x7FC00001, 0x7FC00000`: Phase 1 `0x7FC00000`, machine `0x7FC00001`);
* fused ops: genssa's operands make the machine compute `FPMulAdd(±arg0, ±arg2, arg1)`, Phase 1
  `FPMulAdd(±arg0, ±arg1, arg2)`. For `FMADD`/`FNMSUB` they differ only on multiplicands that are
  NaNs of one kind (`FSameNaN`, `mulAdd_comm_of`); for `FMSUB`/`FNMADD` the negated multiplicand
  differs, so a NaN multiplicand comes out with the other sign (`FMSUBD 1.0, qNaN, 2.0`: Phase 1
  `0xFFF8000000000000`, machine `0x7FF8000000000000`). G46 does not accept `FMSUB`/`FNMADD`.

New run premise `FArithPre` (`G46Pre := G45Pre ∧ FArithPre`): no `FADD`/`FMUL` of a `FNaNSwap`
pair and no `FMADD`/`FNMSUB` of `FSameNaN` multiplicands. No trusted premise. The fused ops in the
lowered function are `lower`'s contractions (Phase 2's `Contract`, the 12 `useFMA` shapes); G46
relates the machine's fused instruction to Phase 1's fused op, not to the separate multiply and
add. Witness `genG46_witness` (`sq.area`: `FMULD F0, F0, F0` of `1.5`, `V0` then holds `2.25`'s
bits). G46 accepts 6,775 functions (+118 over G45).

**Slice G47: calls with float arguments or results** (`GoFV/Gen/Check47.lean`,
`checkG47 lc ps bstart g`; proven sound, `g47_value`, `g47_initMem`, `g47_term`, `g47_nilPanic`,
`g47_boundsPanic`, `GoFV/Proof/Gen/G47.lean`): stage (c) of the float slice. G46 with the calls
whose ABI registers include `F0`–`F15` (Go registers 31–46, `abiReg`), which G9, G10 and G15
rejected (`floating-point argument or result`, the `< 16` check): a static call as G15 checks it
(`callKind47`, on `callRegsZ`), an interface or closure call as G10 checks it (`icallKind47`), each
with its ABI registers in `R0`–`R15` or `F0`–`F15` (`abiRegOK`) and an argument or result in an
`F` register at a float shape (`fTy`, `fArgsOK`/`fOutsOK`), and `SelectN [i]` of such a call homed
in its `F` result register `i` at a float shape (`selKind47`; selects in `R0`–`R15` stay G2's and
G10's). Nothing new is trusted: the callee contracts `CallOKZ` and `ICallOK` state `CallSpec`,
whose `RegRel` relates every ABI register, X or V, to its value. G2's `g2_callAt` and G10's
`g10_icall` now take ABI registers below 16 or in 31–46 and, for an argument in an `F` register,
its read value related to the V register (`hV`; `argsV` discharges it by `arg_relV`); the kept and
clobbered registers and the class table are unchanged. The select is G2's with the V register
(`g47_selF`: `LocMatch`'s V clause, `fvalRel_retypeL` at the select's shape, `locMatch_setRegV`).
No new premise: `g47_value` takes G46's `G46Pre`. Witness `genG47_witness` (`math.Sin`: `CALL
math.sin(SB)` with `x = 1.5` in `F0` and a callee that returns its argument; `V0` then holds `1.5`'s
bits). G47 accepts 6,856 functions (+81 over G46).

**Slice G50: the narrow and float pair loads** (`GoFV/Gen/Check50.lean`, `checkG50 lc ps bstart g`;
proven sound, `g50_value`, `g50_initMem`, `g50_term`, `g50_nilPanic`, `g50_boundsPanic`,
`GoFV/Proof/Gen/G50.lean`; G48 and G49 are reserved for the frame variables). G47 with the pair
loads genssa emits through `LDP`'s case besides `LDP` (`pairOp50`): `LDPW` and `LDPSW` into two
distinct X registers G1 may write (components of integer classes of at least 8 bits, as G4's
`LDP`), `FLDPD` and `FLDPS` into two distinct V registers (components float shapes of the element's
width, `fpairTys`), each at a 64-bit register plus the offset, and `Select0`/`Select1` of them homed
in the register of their component. Each is `arm64Op`'s `ldPair n sg` (`stepLoc_ldPair`), the two
`n`-byte loads at `pairAddr` (`pairAddr_noAuxN`, `ofInt_addN`); on the machine `progStep_ldpw`
(`Progs50.lean`: 4-byte loads, `sextTo64 4` for `LDPSW`) and `progStep_fldp` (`n`-byte loads into
V registers). `LDPW`/`LDPSW` is G4's `LDP` at `n = 4` (`g50_ldpX`, `lo_loadN`); `FLDPD`/`FLDPS`
relates each component to its V register by `fvalRel_of_valRel` (`g50_ldpF`); a select of an X pair
is G4's `g4_sel`, of a V pair `g50_selF` (as `g47_selF`, with `read_pair`). The upper-bit table is
empty after each (`uStep35_pair50`, `uStep35_sel50`; a select of `LDPSW` stays outside the
`MOVDreg` tables). New run premise `PairPre50` (`G50Pre := G46Pre ∧ PairPre50`): a pair load reads
valid bytes at both addresses and, for `FLDPD`/`FLDPS`, what it reads at each component shape is no
pointer (`FLoadPre`'s condition, a pointer has no V register form). Witness `genG50_witness`
(`runtime.c128equal`: `FLDPD (R0), (F0, F1)` of `1.5 + 2.5i`; `V0` and `V1` then hold `1.5`'s and
`2.5`'s bits). G50 accepts 6,911 functions (+55 over G47).

**Slice G51: cheap single-instruction ops** (`GoFV/Gen/Check51.lean`, `checkG51 lc ps bstart g`;
proven sound, `g51_value`, `g51_initMem`, `g51_term`, `g51_nilPanic`, `g51_boundsPanic`,
`GoFV/Proof/Gen/G51.lean`). G50 with three groups of one-Prog values, each a module triple
(`Check51X`/`Spec51X`/`G51X`, `vkind51X`, `VK51X`, `vk51X_step`) tried when G50 rejects a value:

* (a) flags and conditional ops: `CSNEG` (as G32's `CSINC`), `TSTW` and `CMNW` (arguments of
  class at least 32), `CMN` and `CMPshiftRA` (64-bit arguments, as G41's compares);
* (b) ALU ops: `MVNshiftLL`/`RL`/`RA` (as G27's shifted operand with G32's `MVN`), `SBFIZ` (as
  G33's `UBFIZ`), `RORconst`, `RORWconst`, `ROR`, `RORW` (64-bit, or the low 32 bits, rotated);
* (c) boolean operands: `ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` and the shifted adds,
  subtracts and logic ops with an argument of class 1, which the earlier slices reject by its width
  (`arithmetic widths`, `shifted logic widths`): a boolean is 0 or 1 in the whole register
  (`ValRel`), so its register agrees with Phase 1's on all 64 bits (`reg_full51c`).

The kept ops of (c) keep the upper-bit table as before (`uokl_keep`); after the others it is empty.
New run premise `Pre51a` (`G51Pre := G50Pre ∧ Pre51a`): the first argument of a `CMN` or
`CMPshiftRA`, and the second of a `CMN`, is no pointer without an integer form (Phase 1's
`cmpP`/`cmpSh` give `Z` clear there, as for G41's `CmpPre`). `MVNshiftRO` stays outside (G27's
`shiftA` has no `ROR` kind). Witness `genG51_witness` (`math/bits.RotateLeft64`: `ROR R1, R0, R0`
of `0x0123456789abcdef` by 8; `X0` then holds `0xef0123456789abcd`). G51 accepts 6,982 functions
(+71 over G50).

**Slice G49: frame variables in `Blk.local` blocks** (`GoFV/Gen/Check49.lean`, `checkG49 lc ps
bstart g`; proven sound, `g49_value`, `g49_initMem`, `g49_term`, `g49_nilPanic`,
`g49_boundsPanic`, `GoFV/Proof/Gen/G49.lean`; §8 item 8, and the `PAUTO`s of item 5 whose address
becomes an integer). G51 with G6's accesses (`MOVDaddr`, the loads and stores of G3, `LDP`, `STP`)
of a frame variable whose block is `Blk.local` (`Tables.forgeable`): a parameter or result at its
`NAME_PARAM` operand, or a `PAUTO` whose address the function converts to an integer at its
`NAME_AUTO` operand (`frameVar49?`, `vkindVar49`, tried when G51 rejects a value). Frame check
`checkVars49` in place of G6's `checkVars`: a `NAME_AUTO` window lies in the locals, a
`NAME_PARAM` window in the function's argument area (`argEnd`: the end of its ABI's spill area,
without the fixed frame word); windows of one operand class are pairwise disjoint and away from
that class's home slots. Proof: `AddrAgree` pins a `Blk.local` block that has an address to it,
so the variables' places are a premise of the activation, `G49Env := G28Env ∧ VarsAt49`
(`VarsAt49`: `E.ι (.local act x) = some (E.sp + frameOff L nc o)` for each accessed variable `x`
at operand `(nc, o)`), which the machine instance (item 4) meets with these bases; each access is
G6's case lemma at that address (`var49_addr`, `g49_addr`, `g49_load`, `g49_store`, `g49_ldp`,
`g49_stp`), an address a `Ptr.word` related to `SP + frameOff` by `valRel_word` whatever the
assignment. `g49_value` takes G51's `G51Pre`. Witness `genG49_witness` (`runtime.getm`'s ABI0
wrapper: `MOVD R0, ~r0+0(FP)` stores the result into its `NAME_PARAM` operand, which G51 rejects;
at `Addrs.fixed`, with `SP` chosen so that the operand is the block's fixed address). G49
accepts 7,142 functions (+160 over G51). Composed in §9 (option (a)): `EntryMatch` leaves the
windows of the register-assigned parameters it accesses out (`pendWins`), the entry stores run
from that relaxed relation to the full one (`sim_entryStores`), under the checked
`entryStoresOK`.

**Slice G52: remainders** (`GoFV/Gen/Check52.lean`, `checkG52 lc ps bstart g`; proven sound,
`g52_value`, `g52_initMem`, `g52_term`, `g52_nilPanic`, `g52_boundsPanic`,
`GoFV/Proof/Gen/G52.lean`). G49 with one group of one-Prog values (`Check52b`/`Spec52b`/`G52b`,
`vkind52b`, `VK52b`, `vk52b_step`) tried when G49 rejects a value: `MOD`, `UMOD` (`REM`/`UREM Rm,
Rn, Rd` of two 64-bit arguments) and `MODW`, `UMODW` (`REMW`/`UREMW`, of arguments of at least 32
bits), as G37's divides (`bin37Kind`). `runLoc` runs each as `Arm64.evalPure`: `srem`/`urem` on the
registers, or on their low words zero-extended, which the machine's `REM`/`REMW` compute
(`progStep_rem52b`); a register without an integer form gives `poison`, so no run premise
(`g52_value` takes G51's `G51Pre`, under `G49Env`). The upper-bit table is empty after each.
Witness `genG52_witness` (`test/ken_chan`'s `main.nrand`, `return randx % n`: `REM R0, R1, R0` of
`-17` by `5`; `X0` then holds `-2`). G52 accepts 7,163 functions (+21 over G49).

**Slice G53: `LoweredMove`** (`GoFV/Gen/Check53.lean`, `checkG53 lc ps bstart g`; proven sound,
`g53_value`, `g53_initMem`, `g53_term`, `g53_nilPanic`, `g53_boundsPanic`,
`GoFV/Proof/Gen/G53.lean`). G52 with one group (`Check53a`/`Spec53a`/`G53a`, `vkind53a`, `VK53a`,
`vk53a_step`) tried when G52 rejects a value: `LoweredMove [n] dst src mem` (`16 ≤ n`, `dst` and
`src` in 64-bit registers other than `R25`, no temporary), which genssa emits as nothing when
`dst` and `src` share their register, else as `moveTail`'s chunks (`moveOffs`, `movePats`): a
`FLDPQ`/`FSTPQ` pair through `V16`, `V17` per 32 bytes, an `FMOVQ` pair through `V16` for 16 of
the rest, then one or two `MOVD` pairs through `X25` (the last overlapping), checked per value to
lie inside the `n` bytes and cover them (`moveCovers`). The machine copies chunk by chunk
(`move_run`) while `Arm64.move` reads all `n` bytes first; they agree when the two ranges are the
same or disjoint. New run premise `Pre53a` (`G53Pre := G51Pre ∧ Pre53a`): the move reads `n`
valid bytes at `src`, writes them at `dst`, and the two ranges are equal or disjoint (Go's `Move`
never copies between partially overlapping ones). The clobbered `R25`, `F16`, `F17` are `poison`
in `runLoc`; the upper-bit table is empty after the move. Witness `genG53_witness`
(`runtime.(*cpuStatsAggregate).compute`, `a.cpuStats = work.cpuStats`: an 88-byte move, two
`FLDPQ`/`FSTPQ`, one `FMOVQ` and one `MOVD R25` pair, from one heap block to another; the
destination's first machine byte is then the source's). G53 accepts 7,260 functions (+97 over
G52).

**Slice G54: `LoweredZeroLoop`, `LoweredMoveLoop`** (`GoFV/Gen/Check54.lean`,
`checkG54 lc ps bstart g`; proven sound, `g54_value`, `g54_initMem`, `g54_term`, `g54_nilPanic`,
`g54_boundsPanic`, `GoFV/Proof/Gen/G54.lean`). G53 with one group (`Check54a`/`Spec54a`, proofs
`G54L`, `G54a`, `G54b`) tried when G53 rejects a value, and a whole-function check `loopOK`.
Genssa emits `MOVD $n/64, Rc`, a body of four post-indexed `STP.P (ZR, ZR), 16(Rp)` (`ZeroLoop`,
`Rc` its temporary) or two `FLDPQ.P 32(Rsrc), (F16, F17)`; `FSTPQ.P (F16, F17), 32(Rdst)` pairs
(`MoveLoop`, `Rc = R24`; nothing when `dst` and `src` share their register), `SUB $1, Rc`,
`CBNZ Rc, <head>`, then `zeroTail`'s stores or `moveTail`'s chunks of the `n mod 64` bytes left
off the advanced pointers. No new `VKind2` constructor: the value emits `.progs` (`loopPats`)
whose `CBNZ` pattern takes any target, and `loopOK` fixes, at each loop value's start in the PC
table, the target of its `CBNZ` (the seventh Prog after no-ops, `nextIdx`) to the Prog after its
`MOVD` (`loopTgt`, `loopTgt_spec`). The checker requires `64 ≤ n`, the pointers in registers a
value may write (Go 0–25, `argDest`), the counter another (`ZeroLoop`: distinct from `p`;
`MoveLoop`: neither pointer `R24` or `R25`), and the tail inside and covering the `n mod 64`
bytes (`zeroCovers`/`moveCovers`; `n mod 64` in 1–7 would need negative offsets and is rejected).
The machine side (`G54L.lean`): step lemmas for the post-indexed pair accesses
(`progStep_stpP`, `progStep_fldpqP`, `progStep_fstpqP`) and `SUB $1` (`progStep_subOne`), the
counter and branch (`count_run`), and `loop_run`, an induction over the iterations left from a
per-iteration step keeping an invariant. `zloop_run` (invariant after `i` iterations: `Rp = p +
64 i`, `Rc = n/64 - i`, the memory `zeroMem` of `zloopStores i`) and `mloop_run` (both pointers
advanced by `64 i`, `R24 = n/64 - i`, the memory `cpMem` of `mloopChunks i`, a pair being
`cpW` at the pointers' offset, `cpP_one`, `cpW_shift`) end with G13's `zero_run` or G53a's
`move_run` of the tail at the advanced pointers (`zeroMem_shift`, `cpMem_shift`). Phase 1 writes
or copies all `n` bytes at once; the clobbered argument registers, the temporary and `R24`,
`R25`, `F16`, `F17` are `poison` in `runLoc` (`clobber_get54`), the only registers the machine
changes. New run premises `Pre54a` (the zeroing writes `n` bytes at a valid address) and
`Pre54b` (`Pre53a` for `MoveLoop`): `G54Pre := G53Pre ∧ Pre54a ∧ Pre54b`. Witness
`genG54_witness` (`runtime.(*consistentHeapStats).unsafeClear`, `clear(m.stats[:])`: a 3504-byte
zeroing, 54 iterations and a tail of three `STP`s, counter the temporary `R1`; the machine's byte
at the end of the block, 1 before, is then 0). G54 accepts 7,308 functions (+48 over G53).

**Fall-through over no-ops** (2026-11-10, shared by every slice: `GoFV/Gen/Check.lean`,
`GoFV/Proof/Gen/Spec.lean`, `G1.lean`). A block whose successor is laid out next fell through
only when its last Prog ended exactly at the successor's start (`next = some (s, k)`); 14
functions (sole reason `Prog N: …, expected JMP`) leave no-ops a value did not consume in
between: argument-liveness `PCDATA $3` (7), inline-mark `NOP` (3) or `HINT $0` (4), e.g.
`sync/atomic.(*Value).Store`, `runtime.runqempty`, `test/literal main.main`. `Cx.falls` (used by
`Cx.two` and `Cx.term`'s `Plain` and two-way cases) now accepts `next = some (s, n)` with
`k ≤ n` and `skipFrom ps k (n - k) = n`: bounded by the successor's start, since a skip to the
end of the no-ops would run over `PCDATA`/`HINT` leading the successor (`runqempty`,
`memoryLimitHeapGoal`, `literal`). `TwoAt` and `TermOK.plain` take `FallAt cx next k f` (`next =
some (f, n)`, `k ≤ n`, every Prog in `[k, n)` a `noop`; `Cx.falls_spec`), and `fall_path` runs
those Progs by `pstar_noops` (each has its own address `text + 4 id` under `Link.byId`) instead
of `.refl`. No other statement changed; no run premise. All 14 are accepted (G54: 7,322, §5).

**Slice G55: `VCNT`, `VUADDLV`, `FRINT*`; shifted `NEG`, `CLZW`, `MULL`, `EXTR`**
(`GoFV/Gen/Check55.lean`, `checkG55 lc ps bstart g`; proven sound, `g55_value`, `g55_initMem`,
`g55_term`, `g55_nilPanic`, `g55_boundsPanic`, `GoFV/Proof/Gen/G55.lean`). G54 with two groups
tried when G54 rejects a value, each value one Prog with no temporary.

- Group A (`Check55a`/`Spec55a`, proof `G55a`), on V registers: `PopCount*`'s `VCNT x`
  (`VCNT Va.B8, Vd.B8`) and `VUADDLV x` (`VUADDLV Va.B8, Vd`) of 64-bit values (`simd55`,
  `simdShape`; `arng8B r` is genssa's `simdRegArng r ARNG_8B`, `vOfF r` the `V` register of `F`
  register `r`), and the rounds `FRINTN`/`FRINTP`/`FRINTM`/`FRINTZ`/`FRINTA` `D`/`S` (`frintOf`,
  `op Fa, Fd` as G46's `fun46`). Phase 1 runs `VCNT`/`VUADDLV` as `op1` of `Arm64.vcnt`/
  `Arm64.vuaddlv` on the 64-bit register and the rounds as `FOps.roundInt` of the float; the
  machine (`progStep_simd55`, `progStep_frint55`) reads the `ARNG` and `V` operands as the V
  register's number (`fpIdx?_arng`, `fpIdx?_vOfF`), applies the same function to the low 64 bits
  and zero-extends it, and runs the rounds as `fp1Op` with `frintOf`'s `opc` (`IEEE.roundInt` on
  both sides, a NaN's processing included). No mismatch, so no run premise: each round's mode is
  fixed by its opcode (`8`–`12`: `rne`/`rpi`/`rmi`/`rz`/`rna`, the ARM ARM's `FRINTN`/`P`/`M`/`Z`/
  `A`, which ignore `FPCR.RMode`) and is the mode Phase 1's `Floor`/`Ceil`/`Trunc`/`Round`/
  `RoundToEven` use; a NaN is quietened with its payload and sign kept and a zero result keeps the
  operand's sign on both sides. The machine's `FZ = DN = 0` is the model's standing `FPCR = 0`
  (`docs/plans/semantics3.md` §3), not a G55 premise; `FRINTX`/`FRINTI` (which read
  `FPCR.RMode`) are not taken.
- Group B (`Check55b`/`Spec55b`, proof `G55b`), on X registers: `NEGshiftLL`/`RL`/`RA [k] x` as
  `NEG Rm SHIFT k, Rd` (G51b's shifted `MVN` with G32's `unF .NEG`: `LL` of an `x` of at least the
  result's class, `RL`/`RA` of a 64-bit `x`), `CLZW x` as `CLZW Rm, Rd` and `MULL x y` as
  `SMULL Rm, Rn, Rd` (arguments of at least 32 bits, which the machine reads the low words of, as
  G37's `REVW` and `UMULL`), and `EXTRconst`/`EXTRWconst [k] x y` as `EXTR`/`EXTRW $k, Rx, Ry, Rd`
  (`extrOK`: `x`, the high half, the one `RestArgs` source; arguments of at least the width,
  `0 ≤ k <` the width; `extrF55b`, `sized`).

No new premise: `g55_value` takes `G54Pre`. Witnesses `genG55_witness` (`math/bits.OnesCount`: from
`x = 0x103` in `F0`, `VCNT` gives `0x102` and `VUADDLV` 3, in `V0`'s low 64 bits after each Prog)
and, for group B, `genG55b_witness` (`math/bits.LeadingZeros32`: from the 32-bit `x = 0x10000` in
`R0`, `CLZW` gives 15, `X0 = 15` after its Prog).
G55 accepts 7,331 functions (+23 over G54: 16 by group A, 7 by group B).

Blockers recorded and not taken after G55 (counts among G54's 1,989 rejected functions, `--sets`):

- **Tail calls** (`CALLtail`/`RetJmp`, 71 functions with no other blocker): Phase 1 has no
  tail-call semantics. `TailLECall*` is a root that `evalOp` leaves `stuck` (`ECTyped.lean`,
  `evalOp_tail`), so Phase 2 counts these functions vacuous and an end-to-end theorem would hold
  only vacuously for them. They wait for Phase 1 tail-call semantics (#385's `TailCall` note);
  the genssa slice and `checkObj`'s epilogue follow it.
- **`FMSUB`/`FNMADD`** (`op FMSUBD: negated multiplicand`, 14 functions, 5 sole): rejected since
  G46. Phase 1 negates the other multiplicand than the machine, and the results differ in a NaN's
  sign (`FArith.lean`). Taking them needs an `FArithPre`-style run premise excluding a NaN
  multiplicand (as `FSameNaN` for `FMADD`), not a checker change.

**Slice G57, group A: `STPW`; narrow pair loads of a global or a frame variable**
(`Check57a`/`Spec57a`, proof `G57a`, `vkind57a lc g v`, `VK57a`, `vk57a_step`; tried when G55
rejects a value). The word pair accesses of `ssaGenValue`'s `LDP*`/`STP*` case the earlier
slices reject, each one Prog with no temporary:

- `STPW [off] p x y mem` (`stpw57`) as `STPW (Rx, Ry), off(Rn)`: G4's `STP` at `n = 4` (`p` in a
  64-bit register, no aux; sources of classes of at least 32 bits, `ZR` included:
  `runtime.(*fixalloc).init`'s `STPW (ZR, R1), 40(R0)` stores a `uintptr` source's low word).
  `runLoc` runs `stPair 4` (`stepLoc_stpw`): `storeBytes 4`, the low word of an integer, at
  `pairAddr` (`pairAddr_noAuxN`); the machine (`progStep_stpw`, `RunProg`'s pair case with `STPW`'s
  `n = 4`) stores the low 32 bits of `X kx` at `X kn + off` and of `X ky` 4 bytes above, related by
  `storeBytes_relN`/`memInj_storeN` at `n = 4` (`g57_stpw`). Sole functions:
  `examples/structs/main.grow`, `runtime.(*fixalloc).init`.
- `LDPW`/`LDPSW {x} [off] base mem` with an aux (`ldpw57`), into two distinct X registers G1 may
  write (`pairTys`), which G50's `ldp50` rejects (`pair load shape`: it asks `v.aux = none`): of a
  global (`symOf?`, as `LDPW sym+off(SB), (Ra, Rb)`: `runtime.bootstrapRand`'s
  `runtime.globalRand+328(SB)`, `runtime.vgetrandomGetState`'s `LDPSW
  runtime.vgetrandomAlloc+40(SB)`) or of a frame variable whose block is `Blk.temp` (G6's
  `frameVar?`, as `LDPW off'(RSP), (Ra, Rb)` at its `NAME_AUTO` operand: `regexp.makeOnePass`'s
  `.autotmp_35`, `runtime.(*scavengeIndex).alloc`/`.free`'s `sc`; all three are `Blk.temp`, none
  takes G49's `Blk.local` path). Proof: G50's `LDPW` (`stepLoc_ldPair`, `lo_loadN` at `n = 4`) at
  G22's address of the global's block (`pairAddr_globN`, `G2Env.glob`; `g57_ldpwGlob`) or at G6's
  address of the variable's `temp` block (`pairAddr_varN`, `var_addr`; `g57_ldpwVar`); the machine
  (`step_ldpw57`) loads at the operand's address (`ctx_mem_glob`, `ctx_mem_slot`).

`vk57a_step` is in `vk55_step`'s form (`G49Env` gives the globals' addresses, the variables'
places and `FrameOK`). No new run premise: the pair loads read valid bytes at both addresses by
G50's `PairPre50`, which already states it for every `pairOp50` op, with or without an aux (part
of `G54Pre`); `STPW` needs none (`runLoc`'s store succeeded). The upper-bit table is empty after
each (`uStep35_57a`); `ops57a_facts` (no `Phi`, nil check, bounds check or entry value) and
`vkind57a_none` (off `op57a`) serve the composition. Witness `genG57a_witness`
(`examples/structs/main.grow`: `v12 = STPW [8] v7 v37 v44 v31`, `STPW (R2, R3), 8(R0)`; from
`x = 0x11223344` in `R2` with a nonzero upper half on the machine, `vk57a_step` relates the run to
a machine memory holding `0x44` at `heap 1 + 8`; `checkG55` rejects the function, and the block
walk with `vkind57a` tried after `vkind55` places `v12` at Prog 15) and `genG57a2_witness`
(`runtime.bootstrapRand`: `v46 = LDPW {runtime.globalRand} [328] v3 v76`, `LDPW
runtime.globalRand+328(SB), (R1, R2)`; from the global's bytes 328 to 335 `1, …, 8`, `R1 =
0x04030201` and `X1`'s low word the same after Prog 17, under an activation with the function's
home slot at its frame operand; `PairPre50` holds there).

**Slice G57, group B: `DMB`, `PRFM`, float stores to frame variables** (`Check57b`/`Spec57b`, proof
`G57b`, `vkind57b`, `VK57b`, `vk57b_step`; tried when G55 rejects a value, composed into G57 with
group A). Each value is one Prog with no temporary:

- `DMB [k] mem` (`PubBarrier`) as `DMB $k` (`dmbShape`), and `PRFM [k] addr mem`
  (`PrefetchCache*`) as `PRFM 0(Rn), $k` (`prfmShape`, `Rn` the register of `addr`), a memory with
  no home. Phase 1 (`arm64Op`) returns the memory unchanged and ignores `PRFM`'s address, so the
  state stays (`stepLoc_dmb57`, `stepLoc_prfm57`); `progEffect`'s `DMB`/`PRFM` arm has no effect
  (`progStep_barrier57`), and the machine of `GoFV/Arm64/Exec.lean` runs barriers and `PRFM` as
  no-ops. `checkObj` models both Progs as no-ops (§7, **Barriers**): `progSym` has `DMB`/`PRFM`
  arms, and `symAccess` runs a `PRFM` word with no effect. `checkObj` accepts
  `mallocgcSmallNoscanReuse` and `(*mspan).userArenaNextFree`; it rejects `scanObject` (`SBFIZ`)
  and `scanObjectSmall` (`VCNT`) for other opcodes. None of the four is end to end: the
  composition (`verified_mach`) is on G56, which rejects `DMB`/`PRFM`, and Phase 2 does not fully
  verify any of them (`lower`: checked variant incomplete).
- `FMOVSstore`/`FMOVDstore [off] {x} SP val mem` as `FMOVS`/`FMOVD Fs, off(<nc>)` and
  `FSTPS`/`FSTPD [off] {x} SP a b mem` as `FSTPS`/`FSTPD (Fa, Fb), off(<nc>)` (`fstpOf`,
  `fstpAs`), floats of the op's width, of a frame variable `x` at its operand (`fvar57?`: G49's
  `frameVar49?`, a `Blk.local` block at `NAME_PARAM` or `NAME_AUTO`, else G6's `frameVar?`, a
  `Blk.temp` block at `NAME_AUTO`; `FVar57`). Both blocks are at `SP + frameOff` under the
  injection (`VarsAt49` or G6's `VarsAt`, `varAt57`, `VarAt57`); `runLoc` writes the floats' raw
  bits (`stepLoc_fstore`, `stPair` in `stepLoc_fstp57`), the machine the low bytes of the V
  registers at the frame operand (`progStep_fstoreAt`, `progStep_fstp57`), related as G44's float
  stores (`g57_fstore`, `g57_fstp` after `g49_store`/`g49_stp`).

No run premise (a `poison` float stores `poison` bytes on both sides); the upper-bit table is empty
after each value (`uStep35_57b`). `vk57b_step` has `vk55_step`'s form (under `G49Env`, the same
activation after the value). The witnesses use `vk57b_step` directly (a hand PC table, `G49Env`
built from compiled facts, written before `checkG57`): `genG57b_witness` (`test/gcgort`'s
`main.init.func95.1`: `FSTPS (F0, F0), .autotmp_1-8(AUTO)` of `float32(1.5)` into a `temp`
block, which `vkind55` rejects; G55 also rejects the function's `LoweredRound32F`) and
`genG57b2_witness` (`runtime.mallocgcSmallNoscanReuse`: `DMB $14`, its only value G55 rejects;
`stepLoc` returns the same state). The frame-variable witness is a `temp` block. Under
`Addrs.fixed` two accessed `Blk.local` variables at distinct operands cannot both sit at
`SP + frameOff` (`AddrAgree` pins them a multiple of `2^24` apart), so `VarsAt49` has no instance
there for such a function (21 of G57's, `docs/proofs/STATUS.md` § slice G49, e.g. the ABI0 wrapper
`runtime.time_now` with three stack results). `fandbits` is not one: after `trim` it accesses
only `x` (`FMOVSstore {x}`), so at `Addrs.fixed` `VarsAt49` only fixes its `SP`.

**Slice G57: groups A and B composed** (`GoFV/Gen/Check57.lean`, `checkG57 lc ps bstart g`; proven
sound, `g57_value`, `g57_initMem`, `g57_term`, `g57_nilPanic`, `g57_boundsPanic`,
`GoFV/Proof/Gen/G57.lean`). G55 with group A (`vkind57a lc g v`) and then group B
(`vkind57b lc g v`) tried when G55 rejects a value (`vkind57`; G55's reason is kept for the other
values). `VK57` (`Spec57.lean`) has a case for G55's kinds and one for each group, each with no
temporary; `vk57_step` is `vk55_step`'s statement, by `vk55_step`, `vk57a_step` (with `G54Pre`'s
`PairPre50` component) and `vk57b_step`; `vk57_nil`/`vk57_pb` use `ops57a_facts`/`ops57b_facts`,
and `g57L_*` are `g55L_*` with `checkG57L_spec`, `vkind57_spec` and `vkind57_initMem`. No new
premise: `g57_value` takes `G54Pre`. Witness `genG57_witness` (`GenG57.lean`, on `GenG57a`'s
`main.grow` and states): `checkG55` rejects the function and `checkG57` accepts it with the block
walk's tables, and `g57_value` relates `v12`'s run to a machine memory holding `0x44` at `A + 8`.
G57 accepts 7,378 functions (+33 over G55's 7,345 with the fall-through over no-ops, §5): 4 with
group A's ops (`main.grow`, `runtime.(*fixalloc).init`, `runtime.bootstrapRand`,
`runtime.vgetrandomGetState`) and 29 with group B's (12 `fmin`/`fmax` instances and
`fandbits`/`forbits`' 4, `FMOVS`/`FMOVDstore` to a parameter; 6 `test/gcgort` closures,
`ken_cplx4`'s `doprint`, `generics`' and `complit`'s `main`; `DMB` in
`mallocgcSmallNoscanReuse` and `(*mspan).userArenaNextFree`, `PRFM` in `scanObject` and
`scanObjectSmall`). As group B notes, under `Addrs.fixed` a function that accesses two or more
`Blk.local` variables at distinct operands has no `VarsAt49` instance, so `g57_value` holds of it
only vacuously there (21 functions, all also accepted by G49). The sole reasons left are led by
`op LoweredGetCallerPC` (26), `MOVDnop/MOVDreg: upper bits unknown` (25), `block kind JUMPTABLE`
(19) and `block kind Defer` (13); 6 functions are left with `pair load shape` alone and 1 with
`pair store shape` alone.

**Slice G56: float constants in read-only symbols** (`GoFV/Gen/Check56.lean`,
`checkG56 lc ps bstart g`; proven sound, `g56_value`, `g56_initMem`, `g56_term`, `g56_nilPanic`,
`g56_boundsPanic`, `GoFV/Proof/Gen/G56.lean`; §10 item 4). G55 with the float constants
(`vkind56` falls back to `vkind55`; `vkind56_eq55`, `vkind56_eq49` with G55's `vkind55_eq54`). It
runs on P0' (`GoFV.Asm.p0PrimeSyms`, §7): P0 with `progedit`'s float
constant loads, the constant symbols added to `G2In.syms` as the assembler's `lookup` adds them.
`vkind56a`, tried before G55's kinds, accepts `FMOVSconst`/`FMOVDconst` (no temporary, no
argument, homed in an `F` register of class `8 · fBytes`) with one pattern (`fconstPat56`): G44's
`FMOVS`/`FMOVD $c, Fd`, or the load `FMOVS`/`FMOVD sym(SB), Fd` (`plain`, `constSymA`: `MEM`,
`EXTERN`, offset 0, a symbol `y` with `g.syms[y]? = some (name, _)` and
`constSymAlloc? name = some (roAlloc (leBytesU8 (fconstNat n c) n))`, the name parsed, not
formatted: `fconstNat` is `float32(c)`'s bits for `FMOVS`, `c`'s for `FMOVD`, the bits `FCONST`
writes). The proof (`g56_fconst`): the `FCONST` branch is `g44_fconst`'s; the load branch takes
the symbol's address from `G2Env.glob` (`L.sym y`), its allocation from `constRo_mem` and the
premise `RoPre56 g s` (the `LocMatch`ed state's memory has `RoMem (constRo (symNames g))`, as
`lreach_roMem` gives along the run), the address above the nil page from `ro_addr`, each byte
from `ro_byte` (both moved to `GoFV/Proof/Gen/RoByte.lean` so that `Proof/Gen` can import them),
and `readMem_fconst` (`readMem_of_bytes`) turns the `n` bytes into `fconstBits n c`, what
`FCONST` writes, so both branches end in the same V register value (`op_regV`). `g56_value`
takes `G54Pre` (G55 adds none) and `RoPre56`; the other theorems are G55's over `checkG56`.
Witness `genG56_witness` (`runtime.float64Inf`, `v8: FMOVDconst [+Inf]` in `F0`: +Inf is no
`FMOV` immediate, so P0' loads it from `$f64.7ff0000000000000`, which `checkG55` rejects and
`checkG56` accepts; from a machine whose `V0` is 0 and whose memory holds the symbol's bytes at
its linked address, `g56_value` ends with +Inf's bits in `V0`'s low word). G56 accepts 7,331
functions on P0' (G55 on P0 accepts 7,331; 61 of them load a float constant, which G55 would
reject on P0', where `checkObj` now accepts them).

**Slice G48: stack arguments and stack results** (`GoFV/Gen/Check48.lean`, `checkG48 lc ps
bstart g`; proven sound, `g48_value`, `g48_initMem`, `g48_term`, `g48_nilPanic`,
`g48_boundsPanic`, `GoFV/Proof/Gen/G48.lean`; §8 item 7). G57 with two groups tried when G57
rejects a value: the static calls whose ABI assigns inputs or outputs to the stack
(`callKind48`: G47's call check on `callRegsS`, the ABI without its stack-assigned parameters),
and the accesses off `SP` without an aux (`spKind48`: G3's stores and loads, `STP`, `STPW`,
`FSTPD`, `FMOVS`/`FMOVD` stores and loads at `o(RSP)`). An access's window `[o, o + n)` lies in
`[8, outargsSize)` (`outWin48`) and its base is an `SP` value homed in the Go register `SP` at a
64-bit shape (`spBase48`); the function homes nothing but `SP` values and `Phi`s in that register
(`spHomes48`, the checker's form of G48b's `SPHomes`). The theorems hold in an activation whose
`outargs` block sits at `SP` (`hosp : E.outSP = true`; G48b's separation `SepFromW` and `SPInv`):
an access's base reads as `SP`'s pointer (`sp_base48`, from `SPInv` and the base register's class
in the class table), its machine address is `m.sp + o`, and G48a's step lemmas (`g48_spStore` …
`g48_spFLoad`) keep `SepFromW`, a Phase 1 write lying at or above `Blk.writableFrom`
(`sepW_out`). A call is G2's (`g2_callAt`) under the new trusted contract `CallOKStk`
(`CallAtM true` at the registers `callRegsS` gives; STATUS Assumptions): the caller has stored
the stack arguments at `8(RSP)` and up, where the callee reads them and writes its stack
results. The upper-bit table: a store or a float access keeps the X registers (`uokl_x48`), an
integer load gives G35's entry or drops its register's (`uokl_spLoad48`). `g48_value` takes
`G54Pre` (G57's premise) and the contracts of the mode `true` through `E.outSP`; it and
`g48_initMem`, `g48_term` keep `SPInv` (`spInv_step` under `spHomes48`); `g48_value` and
`g48_initMem` take a lowered function (on one with no arm64 op `checkG48` is `checkNL30`, which
G53S covers). Witness
`genG48_witness` (`runtime.exit`'s ABI wrapper, `MOVW R0, 8(RSP)` then `CALL runtime.exit(SB)` of
the `ABI0` `exit`, which G57 rejects (`v10: argument v3 in register 30`): in an activation with
`outargs 0` at `SP = 2^62`, its `Addrs.fixed` address, `g48_value` runs the store of `code = 7`,
after which the machine's byte at `SP + 8` is 7); `genG48_call_witness` then steps the `CALL`
(`v6`) by `g48_value` with that byte at `SP + 8`, under `CallOKStk` for a callee that returns at
once (`callOKStkC`); Phase 1's call consumes the argument (`outargs` `poison` again), and the
activation stays a `G49Env` with `G3Inv` of the mode and `SPInv`. On quick-v10 no store reaches
`outargs[0, 8)`:
298 functions store off `SP` without an aux, 664 stores, the lowest at offset 8 (3 of them
`FSTPQ`, outside G48). G48 accepts 7,595 functions (+217 over G57; re-measured on main 977d0814
with G56 merged; 7,607 with G58's group B). G48 is chained on G57 (G56 is not chained after G57
but beside it, on G55, and runs on P0' (`p0PrimeSyms`), while G57 and G48 check P0), and G58 on
G48: G57 → G48 → G58.

**Slice G58, group A: narrow and boolean operands, wider store-release sources,
`LoweredRound*F`** (`Check58a`/`Spec58a`, proof `G58a`, `vkind58a lc g v`, `VK58a`,
`vk58a_step`; tried when G57 rejects a value). The earlier checks ask more of an argument's class
than the op reads; G58a accepts these values, each emitting the earlier check's Prog (no
temporary; a result of class `c ≥ 8` where it has one):

- `REV16W x` (`rev16w58`) of an `x` of at least 16 bits for a result of at most 16 (G37 asks 32):
  the low halfword of `REV16W`'s word swaps the bytes of the low halfword only (`rev16_low58`,
  `lo_rev16w58`). Sole functions: `encoding/binary`'s `bigEndian.Uint16`/`PutUint16` and their
  `(*bigEndian)` wrappers, `(*base64.Encoding).Encode`, `math/bits.ReverseBytes16`.
- `MADDW`, `MSUBW a x y` (`maddw58`) for a result of class `c ≤ 32` of arguments of at least `c`
  bits (G37 asks 32): the low `c` bits of the low word's `a ± x · y` read only the low `c` bits
  of `a`, `x`, `y` (`lo_maddw58`; `uint16(x) % 26` in `test/copy`'s `u16`, `reset`, `verify16`).
- A boolean (class 1) operand of G32's register ops (`bin58`: `math.shrcompress`'s `OR` of a
  `NotEqual`), G32's constant ops (`binK58`), G36's register shifts as the amount (`sh58`:
  `math.sqrt`, `runtime.(*pinState).set`), G33's `UBFIZ` (`ubfiz58`:
  `runtime.doubleCheckHeapType`) and G32's `CSINC` (`csinc58`: `test/ken_chan`'s `sel`): a
  boolean's register is 0 or 1 on all 64 bits (`ValRel` of `.bool`), as G51c's arithmetic
  (`wid51c`, `reg_bool51c`, `lo_op2_51c`; `lo_op1B58`, `lo_sh58`, `valRel_csinc58`).
- `STLRW`, `STLRB p x mem` (`stlr58`) of a source of at least `8 n` bits (G32 asks exactly them):
  Phase 1's generic atomic store fits the operand to the location (`fitPiece`, an integer's
  `retypeL` truncates), whose bytes are those of `Arm64.storeBytes` of the source, or `poison` for
  a pointer stored narrower (`encode_fit58`, `intBytes_mod58`), which G32's store argument
  relates (`g58_stlr`). Sole functions: `runtime.(*timers).unlock`/`.take`,
  `runtime.gcPrepareMarkRoots`, `runtime.parsegodebug` (`ts.len.Store(uint32(len(ts.heap)))`
  and the like, whose conversion lowering drops).
- `LoweredRound32F`, `LoweredRound64F x` (`round58`): no code (`ssaGenValue`'s `nop` case;
  `regalloc`'s `resultInArg0` puts the result in `x`'s `F` register, which the check asks), Phase 1's
  `Round32F`/`Round64F` is the identity on the float read at its width (`round_id58`), so the
  match moves the register's value to the result as G44's `Copy` to itself (`g58_round`). Sole
  functions: `test/gcgort`'s `main.init.func95.1`, `main.init.func103.1`.

No run premise. `vk58a_step` is in `vk57a_step`'s form (`G49Env`: the store-release needs
`FrameOK`) without a premise, plus G51c's `hL : UOKL m L`: G32's register and constant ops,
`UBFIZ` and `CSINC` keep the upper-bit table's entries of the other registers (`keepOp34`),
`REV16W`, `MADDW`/`MSUBW` and G36's shifts those of the registers other than the home's (group
B's `keepOps35`, `uokl_xw`), the others empty it (`uStep35_58a`); `ops58a_facts` and
`vkind58a_none` (off `op58a`) serve the composition. A probe of `checkG57` with `vkind58a` tried
after `vkind57` accepts 19 of the 20 functions whose sole reason these were;
`runtime.checkFinalizersAndCleanups.func1` (`ORconst` of
a boolean) then fails at `b32: control read at another class` (a `Phi` of the boolean and the
`ORconst` result). Witnesses (each on `vk58a_step` directly, a hand PC table and `G49Env` from
compiled facts, G57's `vkind57` rejecting the value): `genG58a_witness`
(`math/bits.ReverseBytes16`: `REV16W R0, R0` of `0x1234` gives `0x3412`), `genG58a2_witness`
(`test/copy` `main.u16`: `MSUBW R1, R0, R2, R1` of `1000 - 38·26` with a 16-bit `v14` gives 12),
`genG58a3_witness` (`runtime.(*pinState).set`: `LSL R2, R3, R2` of the `uint8` 5 by the boolean
`true` gives 10), `genG58a4_witness` (`runtime.(*timers).unlock`: `STLRW R1, (R2)` of
`0x1122334455667788` leaves `0x88` at the `heap` block's address) and `genG58a5_witness` (on
`GenG57b`'s `main.init.func95.1`: `LoweredRound32F` of `float32(1.5)` in `F0`, no Prog runs). As
G51c, the boolean kinds rest on `ValRel`'s 0-or-1 register for every boolean, including a boolean
argument's register at entry (`pinState.set`'s `multipin`).

**Slice G58, group B: G35's upper-bit table across more writes** (`GoFV/Gen/Check35.lean`,
`GoFV/Proof/Gen/Keep35.lean`; no new group function, the statements of every slice from G35 on
unchanged). Of the 25 functions G57 rejects only for `MOVDnop/MOVDreg: upper bits unknown`, the
source's entry was dropped by: a word pair load and its select, which recorded nothing (`LDPW`,
9 functions, 4 also needing `ORshiftLL`/`MOVWstore`); a G36/G37/G51b op writing only its register
(`SLL` 1, `MULW` 1, `UMULH`+`MADD` 1, `SBFX`+`SBFIZ` 2); an acquire load (`LDAR`, 2); a narrow
store (`MOVBstore`/`MOVHstore`, 2); G27's shifted logic ops (`ORshiftLL`, `ANDshiftRA`, 2); a `Copy`
of a narrow load (3); a `Convert` (1); `runtime.sigdisable` (a join of blocks, not analysed further).
`pairOp35` now also covers `LDPW`/`LDPSW` (G50, G57a), whose pair registers get the entries of a
zero- or sign-extended word (`wEntries35`, `uStep35_ldpX`, `WPairW`, `uokl_wpair`), `LDAR`/`LDARW`/
`LDARB` with home `(Rd;-)` (`homeRegs` gives `[Rd]`; `uStep35_ldar`, `uokl_one`), the selects of
these and of `LDP` (no code: the table stays, `uStep35_sel`), and `SLL`, `SRL`, `SRA`, the G37 ops and
`SBFIZ` (`keepOps35`, `uStep35_keepOps`, `uokl_xw`). Their case lemmas now conclude what the machine
writes (`XW`: `g36_sh`, `g37_bin`/`un`/`madd`/`sbfx`, `g51b_sbfiz`; `g38_ldar`; `WPairW`:
`g50_ldpX`, `g57_ldpwGlob`, `g57_ldpwVar`); `vk51b_step` and `vk57a_step` now take the table before
the value (`hL`). No new premise. 12 of the 25 functions are accepted by `checkG57` with the new
table (checked with the checker on the corpus files: `errors.as`, `hash/fnv.(*sum32).Write`,
`(*sum128).Write`, `regexp.(*machine).add`, `makeOnePass`, `onePassPrefix`,
`runtime.(*fixalloc).alloc`, `preprintpanics`, `runGCProg`, `vdsoFindVersion`,
`unicode/utf8.decodeRuneSlow`, `decodeRuneInStringSlow`). The stores, G27's ops, `Copy` and
`Convert` are VK33 kinds: keeping them needs their G1/G3/G12/G27 case lemmas to conclude `XW` and a
case in `vk33_keep35` (8 more functions with the 3 `LDPW`+`ORshiftLL` ones).

**Slice G58: groups A and B composed** (`GoFV/Gen/Check58.lean`, `checkG58 lc ps bstart g`; proven
sound, `g58_value`, `g58_initMem`, `g58_term`, `g58_nilPanic`, `g58_boundsPanic`,
`GoFV/Proof/Gen/G58.lean`). G48 (on G57) with group A (`vkind58a lc g v`) tried when G48 rejects a
value (`vkind58`; G48's reason is kept for the other values); group B is G35's table, which
`checkG58L` checks as G48 does (`movdOK35`, `uEdgesOK35`), with G48's `spHomes48`. `VK58`
(`Spec58.lean`) has a case for G48's kinds and one for group A, with no temporary; `vk58_step` is
`vk48_step`'s statement, by `vk48_step` and `vk58a_step` (`hL`; no premise, in either mode);
`vk58_nil`/`vk58_pb` use `ops58a_facts`, and `g58L_*` are `g48L_*` with `checkG58L_spec`,
`vkind58_spec` and `vkind58_initMem`. With group B, `uStep35_58a` has a third case, the `homeRegs`
filter of `keepOps35` (`REV16W`, `MADDW`/`MSUBW`, the shifts), closed in `vk58a_step` by
`uokl_xw`. The theorems are G48's: in the mode `outSP` (`hosp`, `SPInv`, kept), `g58_value` under
`G54Pre`, the contracts of the mode `E.outSP` and `CallOKStk`; group A adds no premise (the store
`g58_stlr` keeps `SepAt` by `SepAt.write`/`not_mem`). Witness `genG58_witness` (`GenG58.lean`, on
`GenG58a`'s `math/bits.ReverseBytes16` and state, in an activation whose `outargs` block sits at
`SP`, `GenG48`'s `ι48` and `spO`): `checkG48` rejects the function and `checkG58` accepts it with
the block walk's tables (`v11` starting at the no-op Prog before its `REV16W`), and `g58_value`
relates `v11`'s run to a machine state whose `X0` has the low halfword `0x3412`, `SPInv` kept. G58
accepts 7,626 functions (§5, `--jobs 1`; G58 is gen-check's last slice): G48's 7,607 and group A's
19 (the 20 of its probe less `runtime.checkFinalizersAndCleanups.func1`). Group B's 12 are accepted
by earlier slices too (G37 the two `hash/fnv` `Write`s, G38 `runtime.preprintpanics`, G42
`runtime.runGCProg`, G50 four, G51 three, G57 `regexp.makeOnePass`; G57 7,390, G48 7,607). No
slice's count drops, and every function G58 rejects G48 rejected. The sole reasons left (120
functions) are led by `op LoweredGetCallerPC` (29), `block kind JUMPTABLE` (19), `MOVDnop/MOVDreg:
upper bits unknown` (14), `block kind Defer` (13), `a register read at another class` (7),
`FMSUBD: negated multiplicand` (7) and `pair load shape` (6).

**Slice G59, group P: float pair loads of a global or a frame variable** (`Check59p`/`Spec59p`,
proof `G59p`, `vkind59p lc g v`, `VK59p`, `vk59p_step`; tried when G58 rejects a value). The 6
functions G58 rejects only for `pair load shape` are `test/zerodivide`'s `main.init.func33` to
`func38` (`use(d / c)` of `complex128` and `complex64` globals): genssa loads each global's two
parts with `FLDPD main.d(SB), (F2, F3)` or `FLDPS`, which G50's `ldp50` rejects (it asks
`v.aux = none`). Group P is G57's group A (`ldpw57`) for the float pair loads:

- `FLDPD`/`FLDPS {x} [off] base mem` with an aux (`fldp59`, `FldpOp`: 8- and 4-byte elements)
  into two distinct V registers, each component a float shape of the element's width (G50's
  `fpairTys`: Phase 1's `float64`/`float32` components are `.int .w64`/`.int .w32`), of a global
  (`symOf?`, `op sym+off(SB), (Fa, Fb)`, `VK59p.glob`) or of a frame variable whose block is
  `Blk.temp` (G6's `frameVar?`, `op off'(RSP), (Fa, Fb)` at its `NAME_AUTO` operand,
  `VK59p.var`; none of the 6 functions has one, it is G57a's case for floats). Proof: G50's
  `FLDPD` (`stepLoc_ldPair`, `lo_loadN` at `n = 8` or `4`, `fvalRel_of_valRel`) at G22's address of
  the global's block (`pairAddr_globN`, `G2Env.glob`; `g59_fldpGlob`) or at G6's address of the
  variable's `temp` block (`pairAddr_varN`, `var_addr`; `g59_fldpVar`); the machine
  (`step_fldp59`) loads the two elements at the operand's address (`ctx_mem_glob`,
  `ctx_mem_slot`) into `V ka`, `V kb`.

Their `Select0`/`Select1` are G50's `sel50` (it reads the op, not the aux). `vk59p_step` is
`vk57a_step`'s statement (`G49Env`, `hL`, G50's `PairPre50`, which already states the valid bytes
and the no-pointer components for every `pairOp50` op with or without an aux; part of `G54Pre`): no
new premise. The upper-bit table is empty after each (`uStep35_ldpF`); `ops59p_facts` (no `Phi`,
nil check, bounds check or entry value) and `vkind59p_none` (off `op59p`) serve the composition.
No shared analysis changes. A probe of `checkG58` with `vkind59p` tried after `vkind58` accepts
all 6 functions. Witness `genG59p_witness` (`GenG59p.lean`, on `vk59p_step` directly, a hand PC
table, `G49Env` with `.autotmp_1`'s `temp` block, `vkind58` rejecting the value):
`main.init.func33`'s `v24 = FLDPD {main.d} [0] v3 v1`, `FLDPD main.d(SB), (F2, F3)`; from
`main.d = complex(1.5, 2.5)`, `F2` (Go register 33) holds `0x3ff8000000000000` and `F3`
`0x4004000000000000` after the run, and the machine's `V2`, `V3` the same in their low 64 bits after
Prog 3; `checkG58` rejects the function.

**Slice G59, group D: `Defer` blocks** (`GoFV/Gen/Check.lean`'s `Cx.term`, `GoFV/Proof/Gen/Spec.lean`,
`GoFV/Proof/Gen/G1.lean`; no new group function, the statements of every slice unchanged). The 13
functions G58 rejects only for `block kind Defer` (`examples/defers` `main.withCleanup`,
`test/defer` `main.test1helper`/`test2helper`, `test/print` `main.main`, `test/range4`'s `func7`,
`func7-range1`, `func8`, `func8-range1`, `func8-range1-range1`, `func8-range2`, `func9` and the two
`func9-range1-range1`) end a block in a `deferproc` call. Go's arm64 `ssaGenBlock` (`arm64/ssa.go:2009`,
`case ssa.BlockPlain, ssa.BlockDefer`) emits `Plain`'s `JMP Succs[0]` unless `Succs[0]` is next:
`deferproc` returns no result and there is no `CBNZ R0` (older Go's recovery test); `Succs[1]`,
`f.DeferReturn`, is reached only by the runtime's recovery. Phase 1's `stepTerm` (`Run.lean`) takes
successor 0 (semantics §9.7: a recovery returns through `finish`), and the `deferproc` call before
it is a static call of the existing call slices. `Cx.term`, which every slice reaches through
`Cx.termG3`/`Cx.termG2`, now has a `Defer` arm (two successors, one control, then `Plain`'s
fall-through or `JMP`); `TermOK` gains `defer` (successor 0, `FallAt` or a `JMP` there) and
`branch` takes `b.kind ≠ .Defer`; `Cx.term_spec` proves the arm, and `term_core` handles `Defer`
as `Plain` with `stepTermL_defer` (`stepTermL` of a `Defer` block is `succ b 0`). Shared
definitions changed: `Cx.term` and `TermOK`, so every `checkGN` from G1 on accepts these blocks
(checks of earlier slices whose sole reason was the `Defer` block may now pass too). No new
premise. A probe of `checkG58` with the new `Cx.term` accepts all 13. Witness `genG59d_witness`
(`GenG59d.lean`, `test/defer` `main.test1helper` embedded): `checkG58` accepts it, block `b3`
(`v24 = CALLstatic {runtime.deferproc}`; successors `b4`, `b7`) is a `Defer` block, and from a
state at its end `stepTermLoc` goes to `b4` and `g58_term` relates it to a machine run of its
`JMP` (Prog 19) to `b4`'s start (`G49Env` with the function's home slot at its frame operand).

**Slice G59, group K: narrower register classes** (G3's class table, `GoFV/Gen/Check.lean`,
`GoFV/Gen/Check3.lean`, `GoFV/Proof/Gen/Rel.lean`, `G1.lean`, `Spec3.lean`, `G3.lean`; no new
group function, every `gN_*`/`gNL_*` statement unchanged, no new premise). Seven functions G58
rejects only for `a register read at another class` and one only for `control read at another
class` read a `Phi` homed in a register whose last writers had another class: a 32-bit `Phi` of
64-bit values (`math.lz`, `runtime.(*moduledata).textOff`, `(**moduledata).runtime.textOff`,
`findfunc`: `R0`/`R6` at 64 bits at every predecessor's end), a loop `Phi` joining a 64-bit `Copy`
with a 32-bit value (`hash/crc32.init`, `init.func1`, `simplePopulateTable`: the join was `none`),
and a 64-bit `Phi` of booleans (`runtime.checkFinalizersAndCleanups.func1`: `R1` at class 1 from two
predecessors, 64 from the third). A class in the table now is a class the register's content *can
be read at*: `kNarrow c c'` (`Check.lean`) holds when `c = c'`, or `c ≥ 8` and the content has an
integer or pointer class `c' ≥ c` (its low bits) or is a boolean (`c' = 1`, 0 or 1 in the whole
register). The invariant follows it: `CoreInv.regs` and `G1Inv.regs` give `FitsW c v` (`Rel.lean`:
`kNarrow c` of the content's class, `fitsW_of_fits`, `FitsW.narrow`) instead of `Fits c v`, and
`valRel_retypeLW` (`retypeL_int_low`, through `valRel_i64` for a 64-bit content), `valRel_retypeW`
(G26, Phase 1 functions) and `fvalRel_retypeLW` (`FMove.lean`) relate a content read at any class
it allows; `arg_rel`, `arg_relP`, `arg_relV`, `arg_relVL` and the reads of a selected or reloaded
register (G2, G4, G8, G38, G47, G50) use them, and the writes conclude `FitsW` by `fitsW_of_fits`
(`core_setReg`, the call results of G2/G10, G8, G28). Reads stay exact (`kOK`, `KRead`); the edges
allow narrowing: `kLe K' K` asks `(K.get r).any (kNarrow c)` (`kLe_spec`, `checkK_spec`'s edge
part), which `termK_stepX` closes with `CoreInv.monoW` (`KLeW`). The dataflow, unverified, uses it:
`kJoin` keeps the class both predecessors allow (the narrower integer class, the integer class over
a boolean) and `kPhis` sets the home register of a successor's `Phi` to the `Phi`'s class where the
content allows it. Changed shared definitions: `KMap`-level `kLe`, `kMeet` (by `kJoin`), `kPass`
(by `kPhis`), hence `kFlow` and every `checkGN`'s class table; `CoreInv`, `G1Inv`; new `kNarrow`,
`kJoin`, `kPhis`, `FitsW`, `KLeW`. Witness `genG59k_witness` (`GenG59k.lean`, `math.lz`):
`checkG58` accepts it with `R0` at 64 bits at `b5`'s end and at 32 at `b3`'s start, where `v29`
reads it at 32; from a state with `0xffffffff00000045` in `R0`, `g58_term` runs `b5`'s jump to a
state related at `b3`'s table, and `arg_rel` relates `v27`'s read `0x45` to `X0`, which keeps the
64-bit word. `GenG8`'s table changes at `b3` (`R1` now joined at 32 bits). All 8 functions are
accepted by `checkG58` with the new table (probe on the corpus files); on every fifth file of
quick-v10 (1,859 functions) no function G58 accepted is rejected by the new class check.

**Slice G59, group U: G35's upper-bit table across narrow stores, shifted logic ops, `Convert`,
boolean loads and `Copy`** (`GoFV/Gen/Check35.lean`, `GoFV/Proof/Gen/Keep35.lean`; no new group
function, the statements of every slice from G35 on unchanged, no new premise). Of the 13
functions G58 rejects only for `MOVDnop/MOVDreg: upper bits unknown`, the source's entry was
dropped by: a narrow store through a register (`bytes.(*Buffer).ReadRune` `MOVBstore`,
`runtime.(*semaRoot).queue` `MOVHstore`, `runtime.vdsoInitFromSysinfoEhdr` `MOVWstore`); G27's
shifted logic ops (`ORshiftLL`: `encoding/base64.(*Encoding).Decode`,
`runtime.(*scavChunkData).pack`, `(*scavengeIndex).alloc`, `(*scavengeIndex).free`; `ANDshiftRA`:
`runtime.gostringw`); a `Copy` of a narrow load (`strings.(*singleStringReplacer).Replace`,
`WriteString`, `(*stringFinder).next`), whose step dropped the destination's entry instead of
copying the source's; `regexp/syntax.(*Prog).Prefix`, where a `Convert` (`b54`) between the byte
load (`b30`) and the `MOVDreg` (`b60`) emptied the table; and `runtime.sigdisable`, where a
`MOVBUload` of a boolean into `R2` (`b10`, class 1, so no entry) emptied it and the join `b22`
(from `b20` and `b10`) lost `R0`'s word entry. `pairOp35` now also covers `MOVBstore`,
`MOVHstore`, `MOVWstore` with no symbol (a store of a frame variable, G54's entry stores among
them, still empties the table, so `g54L_entryStore` keeps its statement), the twelve ops of
`logSh?`, `Convert` and the narrow loads (`ldEntry35` is tried first: here only those with no
entry); `uStep35` gives a `Copy` between registers the source's entry (`copyStep35`, `MOVDreg`'s
`movdRegStep`). Their case lemmas now conclude what the machine writes (`XW`: `g3_store`,
`g6_store`, `g49_store` through `op_mem2X`; `g12_conv`; `g27_logSh`, `g51c_logSh` through
`op_reg2W`); `Keep35.lean` adds `uStep35_copy`, `uokl_keepOps`, `uokl_xw35`, `st_uokl`,
`extOK_zero`, `uokl_copyKeep`, `uokl_copyMov` and the copy case lemmas `g2_copySame` (no code,
`X` kept) and `g2_copyMov` (`X[kd]` gets `rX ka`, zero for `ZR`); `ld_uokl` covers a load with no
entry and no longer takes `hk`; `keepOps35` gains the shifted logic ops and `Convert`, `ops35`
these, the stores and `Copy`; `vk33_keep35` takes `checkFrame` and a `Copy` (cases for G3's and
G6's stores, G27's `logSh`, G12's `conv`, G1's `copyMem`/`copySame`/`copyMov`), and
`uStep35_other` takes `v.op ≠ .Copy`. G44's float copies keep the table (`uokl_fcopy`: a V
register has no X register), G49 uses `ld_uokl`/`st_uokl` (`narrowLd?_var49` is gone) and G51c
`logSh_keep35` (`uStep35_logSh51c` is gone). Shared definitions changed: `pairOp35`, `uStep35`
(new `copyStep35`), hence `uL35`, `uPass35`, `uFlow35`, `uIn35`, `uEdgesOK35`, `movdOK35` and
every check from `checkG35` to `checkG58` (`checkG57` accepts the 13 functions too); the pins of
witness `*_facts` that reach them may move. All 13 are accepted by `checkG58` with the new table
(checked with the checker on the corpus files). Witness `genG59u_witness` (`GenG59u.lean`, on
`runtime.(*scavChunkData).pack`): `checkG58` accepts it; before `v29 = ORshiftLL` (`ORR R3<<26,
R1, R1`) the table holds `R3`, `R1`, `R2`, G34's step (G35's across `ORshiftLL` before this group)
empties it, the new one keeps `R3` and `R2` for `v31 = MOVDnop v5`; from `R1 = 5`, `R2 = 7`,
`R3 = 3`, `g58_value` relates `v29`'s run (`0xC000005` in `R1`) to the machine's `ORR`, after
which `X2` is still a zero-extended 32-bit word (`ExtOK (m1.x 2) 32 false`).

**Slice G59: groups P, D, K and U composed** (`GoFV/Gen/Check59.lean`, `checkG59 lc ps bstart g`;
proven sound, `g59_value`, `g59_initMem`, `g59_term`, `g59_nilPanic`, `g59_boundsPanic`,
`GoFV/Proof/Gen/G59.lean`). G58 (on G48, on G57) with group P (`vkind59p lc g v`) tried when G58
rejects a value (`vkind59`; G58's reason is kept for the other values), with G48's `spHomes48`.
Groups D, K and U change shared checks that `checkG59L` reads as every slice does: the `Defer` arm
of `Cx.term` (through `Cx.termG3`), G3's class table (`kNarrow`) and G35's upper-bit table. `VK59`
(`Spec59.lean`) has a case for G58's kinds and one for group P, with no temporary; `vk59_step` is
`vk58_step`'s statement, by `vk58_step` and `vk59p_step` (with `G54Pre`'s `PairPre50` component,
as G57's group A); `vk59_nil`/`vk59_pb` use `ops59p_facts`, and `g59L_*` are `g58L_*` with
`checkG59L_spec`, `vkind59_spec` and `vkind59_initMem`; `g59L_term` is `g58L_term` over
`checkG59L` (`termK_stepX`, which group D's `term_core` case covers). The theorems are G58's, so
G48's: in the mode `outSP` (`hosp`, `SPInv`, kept), `g59_value` under `G54Pre`, the contracts of
the mode `E.outSP` and `CallOKStk`; group P adds no premise. Group U's stores (`op_mem2X`) and
group K's `CoreInv.monoW` hold in either mode; group K's `FitsW` and G48b's `SepAt` are separate
fields of `CoreInv` (G48's access lemmas take `FitsW`; G48's `uokl_x48` closes by `uokl_xw35` and
its integer loads by G35's `ld_uokl`, now that narrow stores and loads are `pairOp35`'s). Witness
`genG59_witness` (`GenG59.lean`, on `GenG59p`'s `test/zerodivide` `main.init.func33` and state, in
an activation whose `outargs` block sits at `SP`, `.autotmp_1` at `SP + 40`): `checkG58` rejects
the function and `checkG59` accepts it with the block walk's tables (`v24` at Prog 3), and
`g59_value` relates `v24`'s `FLDPD main.d(SB), (F2, F3)` to a machine state whose `V2` and `V3`
hold the bits of `1.5` and `2.5` in their low 64 bits. G59 accepts 7,667 functions (82.46%, +41
over G58's 7,626, §5, `--jobs 1`; G59 is gen-check's last slice): the 6 of group P and 35 by
groups D, K and U, which earlier slices accept now too (G4 1,834 to G58 7,661; G58 itself +35). No
slice's count drops, and every function G59 rejects G58 rejected (1,630 of 1,671). The sole
reasons left are led by `op LoweredGetCallerPC` (29), `block kind JUMPTABLE` (19), `FMSUBD:
negated multiplicand` (10), `access of a frame variable` (7), `SP access MOVDaddr` (4) and `stack
argument` (3).

**Slice G60: G59 with G56's float constants** (`GoFV/Gen/Check60.lean`, `checkG60 lc ps bstart g`;
proven sound, `g60_value`, `g60_initMem`, `g60_term`, `g60_nilPanic`, `g60_boundsPanic`,
`GoFV/Proof/Gen/G60.lean`). G57–G59 are stacked on G55, so no slice had both G56's float
constants and G57+'s ops; the composition (§9) needs one. `vkind60` tries G56's `vkind56a` first
(`FMOVSconst`/`FMOVDconst` homed by `FCONST` or, on P0', by the load of its constant symbol), as
`vkind56` does before G55's kinds, then G59's `vkind59`; `checkG60L` is `checkG59L` with it
(G48's `spHomes48` included). `VK60` (`Spec60.lean`) has a case for G59's kinds of a value that is
no float constant and G56's `fconst` case; `vk60_step` is `vk59_step`'s statement (at a mode `osp`;
`SPInv`, `CallOKStk` at the mode `true`) with `RoPre56`, by `vk59_step` and `g56_fconst`; `g60L_*` are
`g59L_*` with `checkG60L_spec`, `vkind60_spec` and `vkind60_initMem`. `vkind60_eq48`: on an op of
none of G56's (`op56`), G58's (`op58a`) and G59's (`op59p`) groups `vkind60` is `vkind48`, which
accepts what `vkind57` or G48's `kind48` accepts (`vkind48_ok`, `kind48_cases`: a static call on
`callRegsS`, or an access off `SP`), and `vkind57` is `vkind55` off G57's groups
(`vkind57_eq55`); so `vkind60_ok49`: off G52–G59's groups, `vkind49` or `kind48` (what the
composition's accesses, calls and entry stores read). Premises: `g60_value` takes G59's and
`RoPre56`. Witness `genG60_witness` (`GenG60.lean`, `math.sqrt` on P0', in an activation whose
`outargs` block sits at `SP`: `v56: FMOVDconst [MaxFloat64]` in `F1`, the load of
`$f64.7fefffffffffffff`; `checkG59` rejects the function (the load), `checkG56` rejects it
(`v96: SLL widths`, G58's group A), `checkG60` accepts it with its tables, and `g60_value` relates
`v56` to a machine state whose `V1` holds `math.MaxFloat64`'s bits in its low 64 bits). G60 on
P0' accepts 7,667 functions (82.46%, as G59 on P0, §5), of which 69 load a float constant (61 by
G56). **The mode, per function.** G58's and G59's theorems (and G60's) take
the mode `osp` as a parameter: G48's own kinds (`take48`, `GoFV/Gen/Check58.lean`: a static call
whose `callRegsS` differs from `callRegsZ`, i.e. with stack arguments or results, or an aux-less
access off `SP` with its base homed in `SP`) need the mode `true` (`vk48_stepM`), every other value
runs at either (`vk48_stepM` at `false`: a G48 call is one on `callRegsZ`, `CallOKZ`'s contract,
`take48_call`, and `g2_callAt` runs in either mode). `needs48 lc` (checked, Addrs-free) is the
function-level flag; with it false a function runs at the mode `false`, as G57 and before.

**Slice G61: the atomic read-modify-writes** (`GoFV/Gen/Check61.lean`, `checkG61 lc ps bstart g`,
group A in `Check61a.lean`; proven sound, `g61_value`, `g61_initMem`, `g61_term`, `g61_nilPanic`,
`g61_boundsPanic`, `GoFV/Proof/Gen/G61.lean`). `vkind61` is G60's `vkind60`, then, on a value G60
rejects, `vkind61a`: `LoweredAtomic{Exchange,Add,Cas,And,Or}*`, their `*Variant` forms, and
their `Select0`/`Select1` (no code, homed as an acquire load's). Genssa emits a
load-exclusive/store-exclusive loop (`LDAXR (Rp), Rd`; the op; `STLXR Rs, (Rp), R27`;
`CBNZ R27` back to the `LDAXR`; the compare-and-swap with `CMP Ro, R27; BNE` to its `CSET EQ, Rd`
before the store) or one LSE instruction (`SWPAL`; `LDADDAL` and `ADD`; `MVN` and `LDCLRAL`;
`LDORAL`; `MOV`, `CASAL`, `CMP` and `CSET`). `runLoc` runs the lowered op as the generic atomic
it lowers (`Arm64.atomicOf`; `Atomic.rmw`/`Atomic.cas` with the operand fitted to the location,
`fitPiece`). On one core a store-exclusive succeeds (`progEffect`, `GoFV.Arm64`'s single-core
row): `R27 = 0` after it, so the loop runs once. `atomOK` checks on the whole function that each
`CBNZ R27` branches to its `LDAXR` and each compare-and-swap's `BNE` to its `CSET` (`atomTgt`,
`atomOK_spec`). The case lemmas, from `runLoc`'s step (`Step61.lean`: `stepLoc_rmw61`,
`stepLoc_cas61`) and the machine's run of the Progs (`Progs61.lean`) to `LocMatch` and the
invariants by `atom_finish` (`G61V.lean`, at either mode): `g61_xchg` (`G61a.lean`), `g61_add`
and `g61_logic` (`G61b.lean`, the and/or loop through the value's temporary), `g61_cas`
(`G61c.lean`, the `BNE` taken when the location does not hold `old`), `g61_lse` and `g61_casV`
(`G61d.lean`); the components by G38's `g38_sel0`/`g38_sel1`; `vk61a_step` (`G61e.lean`), the
upper-bit table empty after each value (`uStep35_atom61`, `uStep35_selAtom61`). `vk61_step` is
`vk60_step`'s statement with the targets at the value's start (`hatom`); `g61L_*` are `g60L_*`
with `checkG61L_spec` (`atomOK` included), `vkind61_spec` and `vkind61_initMem`. `vkind61` tries
`vkind61a` first (`vkind61_atom`: what it accepts of an atomic is `vkind61a`'s; off `op61a` it is
`vkind60`, `vkind61_eq60`). No new premise:
a `stepLoc` that succeeds gives the aligned, valid location, and `addr_rel` its machine address
outside the nil page. An atomic's own nil fault (`nilFaults`) is the composition's
(`g61_atomPanic`, §9). Witness `genG61_witness` (`GenG61.lean`, `sync/atomic.SwapInt64` on P0',
at the mode `false`): `checkG60` rejects it and `checkG61` accepts it, and `g61_value` runs
`v17 = LoweredAtomicExchange64` (`LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27`) from `addr`
the pointer to the word 7 of `GenG14`'s `heap 1` and `new = 9`, after which the machine's
`X2 = 7`. G61 on P0' accepts 7,983 functions (85.86%, +316 over G60's 7,667: 218 of std/runtime,
84 of std/sync, 10 of std/encoding, 4 tests; std/sync/atomic is now accepted whole, 91 of 91),
269,353 values (`--jobs 2`); G60 and every earlier slice are unchanged.

**Slice G62: incoming stack arguments** (`GoFV/Gen/Check62.lean`, `checkG62 lc ps bstart g`;
proven sound, `g62_value`, `g62_initMem`, `g62_term`, `g62_nilPanic`, `g62_boundsPanic`,
`GoFV/Proof/Gen/G62.lean`). The 192 functions whose whole reason set was `frame variable off
another base` with `stack slot` (mostly `ABI0` wrappers, `abigen_*` and `…,0`) read a parameter
the ABI assigns to the stack: `Arg {x} [off]`, homed by `stackalloc` in the slot of its own piece
(`argKey x type off`), whose `NAME_PARAM` operand `x+off(FP)` is where the caller stored the
argument; genssa emits no code for it, and a later `LoadReg` reloads it (G2's `MOVD x+off(FP),
Rd`). This is the incoming side of G48's `outargs`; G48's mode is not involved (the slot is
`E.slot`'s, at `SP + autosize + 8 + off`, and the `Arg` runs at either mode `osp`). `vkind62` is
G61's `vkind61`, then, on an `Arg` G61 rejects, `argKind62`: no temporary, no argument, `x` an
input parameter without registers in the function's ABI (`stackParam`), a 64-bit class, the home
`argKey`'s slot with a `NAME_PARAM` operand; `.none`. `homeOK10` (G10 on) accepts the slot home of
an `Arg` (earlier slices still reject the `Arg` by its value check; `slot_spill10`: a slot home is
a spill's or an `Arg`'s, so `callsNotSlot10`/`icallNotSlot10` hold as before). `g62_arg`
(`G62a.lean`): `stepLoc_arg` (`argVal`'s piece at the value's shape written to the slot), the
machine does not step, `LocMatch` gains the slot by the new run premise `ArgOK` (at an `Arg`, the
machine's bytes at the slot hold the piece, `SlotRel`: the caller's stack argument), every other
slot, register and the memory are unchanged; `kStep_arg`, `uStep35_arg` (the table empty after
it). `vk62_step` is `vk61_step`'s statement with `ArgOK`; `g62L_*` are `g61L_*` with
`checkG62L_spec`, `vkind62_spec` and `vkind62_initMem`. Witness `genG62_witness` (`GenG62.lean`,
`runtime.syscall_Exit`'s ABI0 wrapper on P0', at the mode `false`): `checkG61` rejects it and
`checkG62` accepts it, and `g62_value` runs `v5 = Arg {code}` from the first state of an
activation on `code = 7`, with the caller's word 7 at `SP + 24` (`argOK0`), after which the slot
of `code` holds 7 and the machine's word there is 7. G62 on P0' accepts 8,175 functions (87.93%,
+192 over G61's 7,983, exactly that reason set), 271,361 values (`--jobs 2`); G61 and every earlier
slice are unchanged, and the rejected set is a subset of G61's. The 37 functions with the same
pair and a narrow stack parameter stay rejected (`Arg width`; 8-byte slots only, `slotOK`).
`ArgOK` is trusted at the slices (STATUS Assumptions); the lift to G62 discharges it from the
entry condition (§9 *The lift to G62*).

**Slice G63: float spills and reloads** (`GoFV/Gen/Check63.lean`, `checkG63 lc ps bstart g`;
proven sound, `g63_value`, `g63_initMem`, `g63_term`, `g63_nilPanic`, `g63_boundsPanic`,
`GoFV/Proof/Gen/G63.lean`). The 32 functions whose whole reason set was `argument v# in register
#` with `writes register #` spill a `float64` homed in an `F` register (`StoreReg` of `F0`–`F31`)
and reload it into one (`LoadReg`); G2's spill and reload (`vkind2`) take X registers only
(`argObj`, `resObj`). Genssa emits them by `storeByType`/`loadByType` of the value's type
(`cmd/compile/internal/arm64/ssa.go`, `ssa.OpStoreReg`/`ssa.OpLoadReg`): `FMOVD Fs, off(RSP)` and
`FMOVD off(RSP), Fd` at the slot's frame operand (`AddrAuto`, G2's `slotOp`). `vkind63` is G62's
`vkind62`, then, on a `StoreReg` or `LoadReg` G62 rejects, `vkind63a`: `fspill63` (no temporary,
the argument in an `F` register at a float shape of class 64, `fargObj`, the value of a float shape
of class 64 homed in a slot with a frame operand: `plain .FMOVD (· == regA rs) (slotA · nc off)`)
or `freload63` (no temporary, the argument of class 64 homed in such a slot, the value in an `F`
register at a float shape of class 64, `fresObj`: `plain .FMOVD (slotA · nc off) (· == regA
rd)`); a `StoreReg` whose argument, or a `LoadReg` whose home, is no `F` register keeps G62's
reason. The slots are `checkFrame`'s 8-byte slots, as G2's. `g63_fspill` (`G63a.lean`) is
`g2_spill` with the V register: `arg_relV` relates the argument to the V register's low bits
(`FValRel`), `progStep_fstoreAt` with `ctx_mem_slot` stores its low 64 bits at the slot, which
relate as a register (`valRel_of_fvalRel`, `SlotRel`); the other slots, the blocks and the frame
words lie outside the written window, as for G2's spill. `g63_freload` is `g2_reload` with the V
register: `progStep_floadAt` loads the slot's 8 bytes into its low 64 bits; the slot relates the
value to them as a register, and `fvalRel_of_valRel` relates it to the V register when it is no
pointer (a V register relates only integers and `poison`; the value is no boolean at a float
shape, `retypeL_int_ne_bool`). That is the new run premise `FReloadPre` (as G44's `FLoadPre`, a
fact of the run, not trusted): a float reload reads, at its float shape, no pointer without an
integer form. Neither writes an X register, so G35's table keeps the other registers' entries
(`uokl_f63`); the class table follows `kStep`. `vk63_step` is `vk62_step`'s statement with
`FReloadPre`; `g63L_*` are `g62L_*` with `checkG63L_spec`, `vkind63_spec` and `vkind63_initMem`.
Witness `genG63_witness` (`GenG63.lean`, `doprint` of `test/ken_cplx0` on P0', at the mode
`false`): `checkG62` rejects it and `checkG63` accepts it, and `g63_value` runs `v2 = StoreReg
v15` (`FMOVD F0, c+0(FP)`) from a state with `1.5` in `F0`, after which the slot of `c`'s first
piece holds `0x3FF8000000000000` and the machine's word at `SP + 24` is the same. G63 on P0'
accepts 8,206 functions (88.26%, +31 over G62's 8,175: 31 of the 32; the 32nd, `test/ken_convert`
`main`, then fails G35's `MOVDnop/MOVDreg: upper bits unknown`), 274,435 values (`--jobs 2`); G62
and every earlier slice are unchanged, and the rejected set is a subset of G62's. The 11 `float
spill shape` and 12 `float reload shape` functions spill `float32` values (4-byte slots, which
`slotOK` rejects). The lift to G63 adds `FReloadPre` to `RunPre`'s per-step premises.

**Slice G64: 128-bit moves of blobs** (`GoFV/Gen/Check64.lean`, `checkG64 lc ps bstart g`;
proven sound, `g64_value`, `g64_initMem`, `g64_term`, `g64_nilPanic`, `g64_boundsPanic`,
`GoFV/Proof/Gen/G64.lean`). The 61 functions whose whole reason set was the blob moves (`op
FMOVQload`, `op FLDPQ`, `select of FLDPQ`, `op FSTPQ`, `op FMOVQstore`, their frame-variable forms,
`register value of shape blob 16`) copy a `Move` of 16 to 64 bytes through V registers
(`ARM64.rules` 420–428). `vkind64` is G63's `vkind63`, then, on one of these ops G63 rejects,
`qkind64`: `FMOVQload` into an `F` register at `blob 16` (`FMOVQ src, Fd`), `FMOVQstore` of such a
blob (`FMOVQ Fs, dst`), `FLDPQ` into two distinct `F` registers, `FSTPQ`, and a select of an
`FLDPQ` component homed in its register (no code), at `qaccessA`'s operand: G3's (`accessA`:
`off(Rn)`, `sym+off(SB)`) or a frame variable's (`fvar57?`). `homeOK10` accepts a blob's V register
home (`blobHome`: an `FMOVQload`'s or a select's, every earlier slice rejecting those values by its
value check, so its rows are unchanged). **Design: the register relation.** `runLoc` holds a blob
as its 16 raw bytes (`Arm64.load16`), pointer fragments included (a copied string header), so a V
register holding one needs the injection; `FValRel` has none and stays as it was. `LocMatch` relates
a V register by `VRel ι`, by cases on the value: a blob by `BlobRel ι` (each byte `ByteRel ι` to
the register's byte at its position, as memory bytes are), every other value by `FValRel` by
definition. The earlier slices' proofs keep their statements; the ones that read a V register
convert (`vrel_fvalW`: a content of a class is no blob), the ones that write one wrap
(`VRel.of_fval`, `locMatch_setRegV` over `locMatch_setRegVR`), and the callee contracts' `RegRel`
keeps `FValRel` (`RegRel.loc`); `ExitRel` relates V registers by `VRel`. `Facts.clsReg` admits a
blob in a V register (`clsReg_of_home10`, `Facts.clsLow` for X registers). `G64a.lean`: a load
reads 16 valid bytes of a live block (the run premise `QLoadPre`, as G3's loads), related to the
128 bits `LDR Q`/`LDP Q` load (`blobRel_load`, `progStep_floadAt`, `progStep_fldpqAt`); a store
writes the bytes of the register's content read at `blob 16` (`poison` or a 16-byte blob,
`store16_rel`) and keeps `MemInj` with the machine's 16-byte writes (`memInj_write16`,
`progStep_fstoreAt`, `progStep_fstpqAt`); the operand's machine address and its relation to the
Phase 1 address are `qbase64`'s (`QBase`, `OpAt`; `addr_rel`, `symAddr_global`, `varAt57`); a
blob has no class (`core_setRegN`, `knext_setN`, `kpairB_kStep`), and no X register is written
(the upper-bit table is empty after each, `uStep35_q64`, `uStep35_qsel64`). `vk64_step` is
`vk63_step`'s statement with `QLoadPre`; `g64L_*` are `g63L_*` with `checkG64L_spec`,
`vkind64_spec` and `vkind64_initMem`. G64 on P0' accepts 8,261 functions (88.85%, +55 over G63's
8,206), 281,544 values (`--jobs 2`); G63 and every earlier slice are unchanged, and the rejected set
is a subset of G63's. The 3 of the 61 that store off `SP` into the outgoing area (G48's mode) stay
rejected. Witness `genG64_witness` (`GenG64.lean`, `makearray` of `test/range` on P0', at the mode
`false`): `checkG63` rejects it (`v10: op FLDPQ`) and `checkG64` accepts it, and `g64_value` runs
`v10 = FLDPQ {main..stmp_16}` (`FLDPQ main..stmp_16(SB), (F0, F1)`) from a memory holding the
literal `[5]int{1, 2, 3, 4, 5}`, after which `F0`/`F1` hold the blobs of its first two 16-byte
halves and the machine's `V0`/`V1` their 128 bits. The lift to G64 adds `QLoadPre` to `RunPre`'s
per-step premises.

**Slice G65: float loads of frame variables, float pair stores through a register or to a
global** (`GoFV/Gen/Check65.lean`, `checkG65 lc ps bstart g`; on P0'). Each of these float accesses
was handled at one operand form only: G44 loads a float through a register or of a global
(`accessA`) and rejects a frame variable (`access of a frame variable`, G49's `frame variable aux on
FMOVDload`), while G57 stores one to it; G57 stores a float pair (`FSTPS`/`FSTPD`) to a frame
variable, and no slice stores one through a register or to a global (`op FSTPD`), as G4 and G22 do
`STP`. `vkind65a`, tried when G64 rejects a value: an `FMOVSload`/`FMOVDload` of a frame variable
(`fvar57?`, G49's `Blk.local` or G6's `Blk.temp`) into an `F` register at the op's width
(`fvload65`: `FMOVS`/`FMOVD off(<nc>), Fd`), and an `FSTPS`/`FSTPD` at G3's operands (`fstp65`:
`FSTPS`/`FSTPD (Fa, Fb), dst`, `dst` `off(Rn)` or `sym+off(SB)`). `GoFV/Proof/Gen/G65a.lean`:
`g65_fvload` is `g44_fload` at the variable's block (`VarAt57`, the frame operand by
`ctx_mem_slot`); `g65_fstpReg` is `g57_stpw` and `g65_fstpGlob` is `g22_stp` with V registers
(`arg_relV`, `valRel_of_fvalRel`) and the machine's pair store at an operand address
(`progStep_fstpAt`). The theorems `g65_*` (`G65.lean`) are G64's statements over `checkG65` with
G64's premises: the loads take `FLoadPre`, already among `G54Pre`'s, so no run premise is added and
the lift changes only `checkG64` to `checkG65`. G65 on P0' accepts 8,274 functions (88.99%, +13
over G64's 8,261, every function whose whole reason set was these accesses), 284,888 values
(`--jobs 2`); G64 and every earlier slice are unchanged, and the rejected set is a subset of G64's.
Witness `genG65_witness` (`GenG65.lean`, `init.func82` of `test/gcgort` on P0', at the mode
`false`): `checkG64` rejects it (`v21: access of a frame variable`) and `checkG65` accepts it, and
`g65_value` runs `v21 = FMOVDload {u} [0] v2 v36` (`FMOVD u-8(SP), F1`) from a memory holding
`u = 1.01` (a `temp` block at `SP + 16`), after which `F1` holds `1.01`'s bits and the machine's
`V1` holds them in its low word.

Later slices, by how many functions outside G18 each blocker occurs in (quick-v10, §5; sole
reason in parentheses):

1. **Calls** with nonempty stack arguments (`stack argument` 308; §8) are done in G48 for static
   calls (after G48: 6 (3), from the calls other than static ones, whose check is `callRegs`).
   Floating-point arguments or results (153 (33)) are done in G47.
2. **Frame variables beyond G6**: parameters and results (`NAME_PARAM`, `Blk.local`: `frame
   variable operand class`, 294 (113 after G41)) and variables whose address is converted to an
   integer (`frame variable with an integer address`, 197 (50)) are done in G49 for G6's accesses
   (option 2 of semantics3 §4.3: addresses as a parameter of the semantics); slots of other
   sizes (`slot … frame operand, size or alignment`, 717).
3. **Other values**: `LoweredGetCallerPC` (26; `runLoc` has no value for it, `Arm64.evalPure`'s
   `poison`, and `progEffect` no `GETCALLERPC`); `REV16W` of narrow arguments (`REV#W widths` 6),
   the other narrow and boolean widths and `LoweredRound*F` are done in G58a; `MOD` (6) and
   `UMOD` (5) are done in G52, `CMN`, `CMNW`, `CMPshiftRA` in G51, the
   acquire loads in G38, the homes of removed values in G39, `InitMem` in G40 and G43, `CMNconst`,
   `CMPshiftLL` and `CMPshiftRL` in G41, `ANDconst` widening a narrow argument in G42; `MOVDnop`
   750 (91) and
   `MOVDreg` (27 sole) are done in G20, G21, G29, G31, G34 and G35 but for 10 functions with no
   other blocker after G43, whose tables need stores, `Convert` or `Copy` to keep or copy their
   entries (§4, G35). Bounds panics (`LoweredPanicBoundsRR` 616 (68), `RC` 332 (46), `CR` 76
   (33), `CC` 170 (22)) are done in G19 but for #541's 2 functions.
4. **Loops and indirect jumps** (counts after G53, among the 2,037 rejected functions):
   - `LoweredZeroLoop` (in 75 functions; rejected as `temporary register`, sole reason in 31) and
     `LoweredMoveLoop` (33 (9)): 48 functions have no other blocker; done in G54 (all 48).
   - `JUMPTABLE` (38 (19)): `MOVD (Rtab)(Ridx<<3), R27; JMP (R27)`. Blocked on the object side:
     `checkObj` rejects `JMP` to a register and `ObjIn` has no data symbols; the table's words are
     `R_ADDR` relocations to the function symbol plus each target's PC (`span7`), which P0
     (`Link.byId`, Prog addresses `text + 4 id`) would read as P0 addresses, while `ObjRel` keeps
     memory identical across the PC remapping; and nothing keeps the table's bytes across stores
     and callee hooks. Deferred with `checkObj`'s float constants (rodata read through `ADRP`) to
     one design: a rodata clause in `ObjRel` (table words related through the PC map) with a
     no-store invariant from `MemInj`'s block separation and the hook contracts. Slice side:
     `termK_stepX` keeps every X register, which `R27` breaks (a variant up to `R27`, which no
     value lives in), and `kControl` reads control 0 only.

## 5. Results

**Coverage** (`lake exe gen-check --jobs 4 <corpus>/quick-v10`, genssa run on the exported frame
as in `gen-parity`; 9,297 functions, 426,323 values, 0 parse, env or genssa errors):

| Slice | Functions accepted | Values in accepted functions |
| --- | --: | --: |
| G1 | 268 (2.88%) | 1,500 |
| G2 | 1,171 (12.59%) | 10,665 |
| G3 | 1,611 (17.32%) | 17,270 |
| G4 | 1,832 (19.70%) | 21,243 |
| G5 | 1,833 (19.71%) | 21,252 |
| G6 | 1,946 (20.93%) | 24,819 |
| G7 | 2,109 (22.68%) | 26,795 |
| G8 | 2,323 (24.98%) | 39,922 |
| G9 | 2,551 (27.43%) | 44,756 |
| G10 | 3,149 (33.87%) | 52,418 |
| G11 | 3,514 (37.79%) | 59,565 |
| G12 | 3,679 (39.57%) | 64,013 |
| G13 | 3,755 (40.38%) | 69,470 |
| G14 | 3,815 (41.03%) | 71,548 |
| G15 | 3,824 (41.13%) | 71,645 |
| G16 | 3,874 (41.66%) | 73,708 |
| G17 | 3,962 (42.61%) | 75,809 |
| G18 | 4,052 (43.58%) | 80,626 |
| G19 | 4,221 (45.40%) | 85,558 |
| G20 | 4,328 (46.55%) | 89,297 |
| G21 | 4,342 (46.70%) | 89,745 |
| G22 | 4,472 (48.10%) | 98,947 |
| G23 | 4,624 (49.73%) | 101,638 |
| G24 | 4,718 (50.74%) | 106,958 |
| G25 | 4,925 (52.97%) | 111,247 |
| G26 | 5,172 (55.63%) | 111,802 |
| G27 | 5,261 (56.58%) | 117,659 |
| G28 | 5,332 (57.35%) | 120,012 |
| G29 | 5,361 (57.66%) | 121,036 |
| G30 | 5,367 (57.72%) | 121,060 |
| G32 | 5,678 (61.07%) | 143,647 |
| G31 | 5,703 (61.34%) | 145,016 |
| G33 | 5,812 (62.51%) | 151,700 |
| G34 | 5,825 (62.65%) | 152,495 |
| G35 | 5,838 (62.79%) | 152,883 |
| G36 | 5,967 (64.18%) | 159,085 |
| G37 | 6,099 (65.60%) | 165,436 |
| G38 | 6,380 (68.62%) | 177,277 |
| G39 | 6,447 (69.34%) | 182,395 |
| G40 | 6,472 (69.61%) | 182,705 |
| G41 | 6,570 (70.66%) | 192,225 |
| G42 | 6,609 (71.08%) | 194,759 |
| G43 | 6,622 (71.22%) | 195,711 |
| G44 | 6,652 (71.54%) | 196,069 |
| G45 | 6,657 (71.60%) | 196,234 |
| G46 | 6,775 (72.87%) | 202,352 |
| G47 | 6,856 (73.74%) | 204,468 |
| G50 | 6,911 (74.33%) | 206,743 |
| G51 | 6,982 (75.09%) | 212,374 |
| G49 | 7,142 (76.82%) | 220,164 |
| G52 | 7,163 (77.04%) | 221,257 |
| G53 | 7,260 (78.08%) | 227,056 |
| G54 | 7,308 (78.60%) | 231,647 |
| G55 | 7,331 (78.85%) | 232,869 |
| G56 (on G55, P0') | 7,331 (78.85%) | 232,869 |
| G57 | 7,378 (79.35%) | 235,204 |
| G48 | 7,595 (81.69%) | 242,306 |
| G58 (on G48) | 7,626 (82.02%) | 245,347 |
| G59 (on G58) | 7,667 (82.46%) | 249,111 |
| G60 (G59 with G56's float constants, P0') | 7,667 (82.46%) | 249,111 |
| G61 (G60 with the atomics, P0') | 7,983 (85.86%) | 269,353 |
| G62 (G61 with the incoming stack arguments, P0') | 8,175 (87.93%) | 271,361 |
| G63 (G62 with the float spills and reloads, P0') | 8,206 (88.26%) | 274,435 |
| G64 (G63 with the 128-bit moves of blobs, P0') | 8,261 (88.85%) | 281,544 |
| G65 (G64 with the float frame-variable loads and pair stores, P0') | 8,274 (88.99%) | 284,888 |

(Before G6 was restricted to frame temporaries for the proof — parameters and variables whose
address is converted to an integer were accepted — its validator accepted 2,022.)

(The rows G1 to G55 were measured before the fall-through over no-ops (§4, after G54;
`Cx.falls`), which every slice shares: re-measured with it, G3 accepts 1,612, G10 3,150, G20
4,330, G30 5,369, G40 6,482, G50 6,921, G53 7,274, G54 7,322 (78.75%, +14; 232,417 values) and
G55 7,345 (79.00%; 233,639 values).)

(G58's group B changes G35's upper-bit table, which every slice from G35 on reads: re-measured
with it (`--jobs 1`), G35 and G36 are unchanged, G37 accepts 6,107 (2 more than with G57's
table), G38 6,391, G42 6,623, G50 6,929, G51 7,004, G49 7,167, G55 7,356, G57 7,390 (79.48%,
+12; 236,767 values) and G48 7,607 (81.82%, +12; 243,869 values); no slice drops.)

(G59's groups D, K and U change shared checks (the `Defer` arm of `Cx.term`, G3's class table,
G35's upper-bit table): re-measured with them (`--jobs 1`), G3 is unchanged, G4 accepts 1,834,
G10 3,154, G20 4,334, G30 5,374, G35 5,854, G40 6,501, G50 6,948, G49 7,198, G54 7,364, G55
7,387, G57 7,423, G48 7,641 and G58 7,661 (82.40%, +35; 248,907 values); no slice drops.)

(On quick-v9, before the G2 validator was tightened for the proof — call arguments and results in
`R0`–`R15`, `SelectN`'s component class, 64-bit `MOVDaddr` and spill shapes — G2 accepted 1,211.)
Before G2, the most frequent reasons functions were outside G1 (functions each occurs in):
`SelectN` 6,909, call results homes 6,364, `CALLstatic` 6,028, `MOVDaddr` 3,637, stack slots 3,298
(`LoadReg`/`StoreReg`), register pairs 3,058, `Exit` blocks 2,631. Outside G2: registers holding
two width classes 4,453, `Select0`/`Select1` and register pairs 3,058, `LDP` 1,922, `STP` 1,765,
`TBNZ` 1,683, load and store shapes 1,680 and 1,675, narrow loads (`MOVWUload` 1,440,
`MOVBUload` 1,419), `NZW` 1,261, `MOVDaddr` of a frame variable 1,261, other results homes
(interface and closure calls) 1,215, `LoweredNilCheck` 1,200, call result shapes 1,121: the later
slices of §4. Sole blockers: not lowered 248, `LoweredNilCheck` 120, `LoweredGetClosurePtr` 104,
`SB` after the entry values 64, two width classes 50.

**Proof** (`GoFV/Proof/Gen/`; G1's modules, then G2's, G3's, G4's and G5's):

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
  `Cx.term_spec` with `TermOK`/`TwoAt`/`FallAt`, `Cx.falls_spec`, `vkind_spec` with the per-op
  facts `VK`).
- `Loc.lean`, `Step.lean`: `stepLoc` per op (`stepLoc_pure`, `stepLoc_copy`,
  `stepLoc_makeResult`, `stepLoc_load`, `stepLoc_store`, …).
- `G1.lean`: the steps on the ID layout (`pstar_noops`, `pstar_oneAt`), one lemma per value kind
  (`op_none`, `op_reg`, `op_flags`, `op_mem`, `value_core`), the terminators (`fall_path`,
  `two_path`), `g1_value`, `g1_term`.
- `Spec2.lean`: what `checkG2` accepted (`checkG2_spec`, `Cx2.blocks_spec`, `Cx2.values_spec`,
  `Cx2.term_spec`, `checkFrame_spec`, `vkind2_spec` with the per-op facts `VK2`).
- `Progs2.lean`: `progStep` of the slot store and load (`frameOff`), `MOVD $sym(SB), Rd` and P0's
  `CALL sym(SB)`.
- `Stack.lean`: `StkAt`, `FrameOK`, `stk_slots_frame`, `stk_keeps`, `memInj_congr`, `valRel_mono`.
- `G2.lean`: `G2Env`, `G2Inv`, `CallSpec`/`CallOK`; one lemma per G2 value kind (`g2_g1`,
  `g2_spill`, `g2_reload`, `g2_addr`, `g2_selMem`, `g2_selReg`, `g2_call`), `g2_value`, `g2_term`.
- `Spec3.lean`: what `checkG3` accepted (`checkG3_spec`, `vkind3_spec` with the per-op facts
  `VK3`, `AccessOK`, `Cx.termG3_spec`/`TermOK3`, `checkK_spec`) and the class-map algebra
  (`kStep_get`, `kResults_get_of_mem`, `kAt_zero`, `kAt_succ`).
- `MemN.lean`, `Progs3.lean`, `Value3.lean`, `Step3.lean`: the `n`-byte load and store under
  `MemInj`; `progStep` of every G3 shape (`MOV…` loads and stores through a register or of a
  global, extensions, `AND`/`LSL`/`LSR`, `UBFX`, `CMPW`, `CBZW`/`CBNZW`, `TBZ`/`TBNZ`); the value,
  flags and branch relations on the low bits of the classes; `stepLoc` of the new ops.
- `G3.lean`: `G3Inv`, `G3Pre`; the class table as `KRead`/`KNext`/`KCall`; one lemma per G3 value
  kind (`g3_load`, `g3_store`, `g3_ext`, `g3_aluK`, `g3_ubfx`, `g3_cmpw`, `g3_cmpwK`, `g3_sb`),
  `term_test`, `vk3_step` (one value of G3's kinds from the validator's facts), `g3_value`,
  `g3_term`.
- `Spec4.lean`: what `checkG4` accepted (`checkG4_spec`, `vkind4_spec` with the per-op facts `VK4`,
  `pairTys_spec`).
- `Step4.lean`, `Progs4.lean`: `stepLoc` of `LDP`, `STP`, `Select0`/`Select1`; `progStep` of
  `LDP off(Rn), (Ra, Rb)` and `STP (Rx, Ry), off(Rn)`.
- `G4.lean`: `G4Pre`; `pairAddr_noAux`, `write_pair`, `read_pair`, `kpair_kStep`,
  `ksel4_of_reads`; `g4_ldp`, `g4_stp`, `g4_sel`, `vk4_step`, `g4_value`, `g4_term`.
- `Spec5.lean`, `Step5.lean`: what `checkG5` accepted (`checkG5_spec`, `vkind5_spec` with `VK5`);
  `stepLoc` of the markers (`stepLoc_mark`).
- `G5.lean`: `MemSub`, `memInj_sub`, `sepFrom_sub`, `memSub_poison`, `memSub_free`; `g5_mark`,
  `vk5_step`, `g5_value`, `g5_term`.
- `Spec6.lean`: what `checkG6` accepted (`checkG6_spec`, `vkind6_spec` with `VK6`, `FrameVarOK`,
  `VKVar`, `plain_spec`).
- `G6.lean`: `VarsAt`, `G6Env`, `symAddr_var`, `pairAddr_var`, `var_addr`, `stepLoc_addrVar`;
  `g6_addr`, `g6_load`, `g6_store`, `g6_ldp`, `g6_stp`, `vk6_step`, `g6_value`, `g6_term`.
- `Spec7.lean`: what `checkG7` accepted (`checkG7_spec`, `vkind7_spec` with `VK7`).
- `Progs7.lean`: `PPanics`, `PPanics.runProg`; `progEffect_nilCheck`, `progStep_nilCheck`,
  `progStep_nilCheck_nil` (`MOVB (Rn), R27` outside and in the nil page).
- `G7.lean`: `objX?_ne27`, `locMatch_tmp`; `nilFaults_nilCheck`, `evalOpL_nilCheck_ok`,
  `evalOpL_nilCheck_panic`, `stepLoc_nilCheck`, `stepLoc_nilCheck_panic`, `write_drop`; `NilPre`,
  `G7Pre`, `nil_word`; `g7_nil`, `g7_nilFault`, `vk7_step`, `g7_value`, `g7_nilPanic`, `g7_term`.
- `Spec8.lean`: what `checkG8` accepted (`checkG8_spec`, `vkind8_spec` with `VK8`, `wbPat_spec`).
- `G8.lean`: `WbSpec`, `WbOK`, `G8Env`; `clobber_wb`, `wb_keeps`, `clobberMask_wb`, `setReg_get`,
  `stepLoc_wb`, `read_wb`, `objX?_kept`, `objV?_kept`, `kwb_kStep`, `ksel8_of_reads`; `g8_wb`,
  `g8_sel0`, `g8_sel1`, `vk8_step`, `g8_value`, `g8_nilPanic`, `g8_term`.
- `Spec9.lean`: what `checkG9` accepted (`checkG9_spec`, `vkind9_spec` with `VK9`,
  `callPat_spec`).
- `G9.lean`: `vk9_step`, `g9_value`, `g9_nilPanic`, `g9_term`.
- `Spec10.lean`: what `checkG10` accepted (`checkG10_spec`, `vkind10_spec` with `VK10`,
  `icallKind_spec`, `icallErr_spec`, `selKind_spec`, `icallPat_spec`, `homeOK4_of_10`).
- `G10.lean`: `ICallOK`, `G10Env`; `stepLoc_icall`, `icall_regInfo`, `clobber_icall`,
  `clobber_icall_reg`, `progStep_callReg`, `objX?_ne30`; `g10_icall`, `clsReg_of_home10`,
  `callsNotSlot10`, `icallNotSlot10`, `vk10_step`, `g10_value`, `g10_nilPanic`, `g10_term`.
- `Spec11.lean`: what `checkG11` accepted (`checkG11_spec`, `vkind11_spec` with `VK11`,
  `cloKind_spec`).
- `G11.lean`: `CloOK`; `stepLoc_clo`, `g11_clo`, `vk11_step`, `g11_value`, `g11_nilPanic`,
  `g11_term`.
- `Spec12.lean`: what `checkG12` accepted (`checkG12_spec`, `vkind12_spec` with `VK12`,
  `convKind_spec`).
- `G12.lean`: `stepLoc_conv`, `convert_rel`, `valRel_convert`, `g12_conv`, `vk12_step`,
  `g12_value`, `g12_nilPanic`, `g12_term`.
- `Spec13.lean`: what `checkG13` accepted (`checkG13_spec`, `vkind13_spec` with `VK13`,
  `zeroKind_spec`, `zeroCovers_spec`); `Spec2.lean`: `Cx2.many_spec` with `ManyAt2`.
- `MemN.lean`: `memInj_writeAny`, `write_inside`.
- `G13.lean`: `stepLoc_zero`, `zeroStore`/`zeroMem` (`zeroMem_cov`, `zeroMem_out`),
  `progStep_zero`, `zero_run`, `ZeroPre`, `G13Pre`, `g13_zero`, `vk13_step`, `g13_value`,
  `g13_nilPanic`, `g13_term`.
- `Spec14.lean`: what `checkG14` accepted (`checkG14_spec`, `vkind14_spec` with `VK14`,
  `idxKind_spec`); `Progs3.lean`: `progStep_loadAt` (a load at any memory operand's address).
- `G14.lean`: `loadIdxOp?_op`, `loadIdxOp?_facts`, `stepLoc_loadIdx`, `idxSum`, `loadIdx_eq`,
  `mul_twoPow_eq_shl`, `lo_idxSum`, `lo64_rel`, `IdxPre`, `G14Pre`, `ctx_mem_idx`, `g14_idx`,
  `vk14_step`, `g14_value`, `g14_nilPanic`, `g14_term`.
- `Spec15.lean`: what `checkG15` accepted (`checkG15_spec`, `vkind15_spec` with `VK15`,
  `callKind15_spec`); `G2.lean`: `CallAt`, `g2_callAt` (`g2_call` through it).
- `G15.lean`: `CallOKZ`, `vk15_step`, `g15_value`, `g15_nilPanic`, `g15_term`.
- `Spec16.lean`: what `checkG16` accepted (`checkG16_spec`, `vkind16_spec` with `VK16`,
  `addShKind_spec`); `Value.lean`: `lo_addP`, `lo_addSh`.
- `G16.lean`: `stepLoc_addSh`, `ctx_src_shiftLL`, `progStep_addShiftLL`, `g16_addSh`, `vk16_step`,
  `g16_value`, `g16_nilPanic`, `g16_term`.
- `Spec17.lean`: what `checkG17` accepted (`checkG17_spec`, `vkind17_spec` with `VK17`,
  `getGKind_spec`).
- `G17.lean`: `GetGOK`, `stepLoc_getG`, `locMatch_setReg_keep`, `g17_getG`, `vk17_step`,
  `vk16_nil`, `vk17_nil`, `g17_value`, `g17_nilPanic`, `g17_term`.
- `Spec18.lean`: what `checkG18` accepted (`checkG18_spec`, `vkind18_spec` with `VK18`,
  `stIdxKind_spec`); `Progs3.lean`: `progStep_storeAt` (public).
- `G18.lean`: `storeIdxOp?_op`, `storeIdxOp?_facts`, `stepLoc_storeIdx`, `g18_stIdx`, `vk18_step`,
  `vk18_nil`, `g18_value`, `g18_nilPanic`, `g18_term`.
- `Spec19.lean`: what `checkG19` accepted (`checkG19_spec`, `vkind19_spec` with `VK19`,
  `pbKind_spec`, `pbInfo_spec`, `pbOK_spec`); `Hooks.lean`: `boundsPanic`.
- `G19.lean`: `BoundsOK`, `BoundsAgree`, `boundsDecode_pbEnc`, `boundsPanic_agree`,
  `stepLoc_pb_panic`, `stepLoc_pb_ne_ok`, `pstar_pbMovs`, `pb_reg`, `pb_phase1`, `vk19_step`,
  `vk19_nil`, `g19_value`, `g19_nilPanic`, `g19_boundsPanic`, `g19_term`.
- `Spec20.lean`: what `checkG20` accepted (`checkG20_spec`, `vkind20_spec` with `VK20`,
  `nopKind_spec`, `movdOK_spec`); `G2.lean`: `op_reg2W`; `G3.lean`: `g3_loadW`; `G14.lean`:
  `g14_idxW`.
- `G20.lean`: `ExtOK`, `UOK`, `sext_bit`, `extOK_load`, `stepLoc_nop`, `lo_movd`, `g20_nop`,
  `NarrowOp`, `narrowLd?_spec`, `vk13_narrow`, `vk19_narrow`, `vk3_idx_false`, `uEntry_spec`,
  `vk19_narrowW`, `vk20_step`, `g20_value`, `vk20_nil`, `g20_nilPanic`, `g20_boundsPanic`,
  `g20_term`;
  `G19.lean`: `vk19_boundsPanic`.
- `Spec21.lean`: what `checkG21` accepted (`checkG21_spec`, `vkind21_spec` with `VK21`,
  `movRegKind_spec`).
- `G21.lean`: `g21_mov`, `vk21_step`, `g21_value`, `vk21_nil`, `g21_nilPanic`, `g21_boundsPanic`,
  `g21_term`.
- `Spec22.lean`: what `checkG22` accepted (`checkG22_spec`, `vkind22_spec` with `VK22`,
  `globPair_spec`, `globPairKind_spec`).
- `G22.lean`: `progStep_globLdp`, `progStep_globStp`, `pairAddr_glob`, `g22_ldp`, `g22_stp`,
  `vk22_step`, `g22_value`, `vk22_nil`, `g22_nilPanic`, `g22_boundsPanic`, `g22_term`.
- `Spec23.lean`: what `checkG23` accepted (`checkG23_spec`, `vkind23_spec` with `VK23`,
  `csetKind_spec`).
- `G23.lean`: `csetOps`, `csetOps_of`, `cset_cond`, `stepLoc_cset`, `narrowLd?_cset`,
  `progStep_cset`, `valRel_cset`, `g23_cset`, `vk23_step`, `g23_value`, `vk23_nil`,
  `g23_nilPanic`, `g23_boundsPanic`, `g23_term`.
- `Spec24.lean`: what `checkG24` accepted (`checkG24_spec`, `vkind24_spec` with `VK24`,
  `entryOp3_of_24`, `entryOp24_of_3`).
- `G24.lean`: `stepLoc_sp`, `g24_sp`, `vk24_step`, `g24_value`, `vk24_nil`, `g24_nilPanic`,
  `g24_boundsPanic`, `g24_term`.
- `Spec25.lean`: what `checkG25` accepted (`checkG25_spec`, `vkind25_spec` with `VK25`,
  `cselKind_spec`, `tstKind_spec`).
- `G25.lean`: `ccOp?_ofAux`, `cselOK_spec`, `stepLoc_g25`, `narrowLd?_g25`, `logical_flags`,
  `logical_flags32`, `progStep_tst`, `progStep_tstw`, `progStep_csel`, `lo_regVal`, `valRel_csel`,
  `valRel_csel0`, `flagsRel_tst`, `flagsRel_tstw`, `g25_csel`, `g25_csel0`, `g25_tst`, `g25_tstw`,
  `vk25_step`, `g25_value`, `vk25_nil`, `g25_nilPanic`, `g25_boundsPanic`, `g25_term`.
- `Spec26.lean`: what `checkG26` accepted (`checkG26_lowered`, `checkG26_nl`, `vkindNL_spec`,
  `allRet_spec`, `checkNL_spec`).
- `G26.lean`: `lmode_retypeP`, `retype_cases`, `retype_poison`, `valRel_retype`, `fits_retype`,
  `read_regP`, `read_memP`, `stepLoc_noclobberP`, `stepLoc_copyP`, `stepLoc_makeResultP`,
  `retypePre_zip`, `write_result_noopP`, `arg_relP`, `op_regN`, `nl_core`, `nl_homes`,
  `narrowLd?_nl`, `nl_ops`, `g26_value`, `g26_nilPanic`, `g26_boundsPanic`, `g26_term`.
- `Spec27.lean`: what `checkG27` accepted (`VK27`, `logShKind_spec`, `vkind27_spec`,
  `checkG26_of_27`, `checkG27_spec`).
- `G27.lean`: `shK`, `logF`, `logSh?_some`, `logSh?_typ`, `evalOpL_logSh`, `logSh_noclobber`,
  `narrowLd?_logSh`, `stepLoc_logSh`, `shiftOf_shK`, `ctx_src_shift`, `logical_orr`,
  `logical_eor`, `binOp_logF`, `progStep_logSh`, `logF_low`, `shl_low`, `lo_logSh`, `g27_logSh`,
  `vk27_step`, `g27_value`, `vk27_nil`, `g27_nilPanic`, `g27_boundsPanic`, `g27_term`.
- `Spec28.lean`: what `checkG28` accepted (`VK28`, `boolTy_spec`, `memEqArg_spec`,
  `memEqKind_spec`, `vkind28_spec`, `checkG27_of_28`, `checkG28_spec`, `memEqPat_spec`).
- `G28.lean`: `MemEqSpec`, `MemEqOK`, `G28Env`, `memEq_clobbers`, `clobber_memEq`,
  `clobber_memEq_reg`, `clobber_memEq_slots`, `clobber_memEq_mem`, `evalOpL_memEq`, `fits_memEq`,
  `g28_memEq`, `G28Env.extend`, `narrowLd?_memEq`, `vk28_step`, `g28_value`, `vk28_nil`,
  `g28_nilPanic`, `vk28_boundsPanic`, `g28_boundsPanic`, `g28_term`.
- `Spec29.lean`: what `checkG29` accepted (`uL_succ`, `movdOK29_spec`, `checkG28_of_29`,
  `checkG29_spec`).
- `G29.lean`: `UOKL`, `KeepsX`, `keepsX_wX`, `uokl_filter`, `find?_entry`, `uok_of_uokl`,
  `uStepL_movdReg`, `uokl_movdReg`, `uStepL_other`, `vk28_vk21`, `vk21_stepL`, `vk29_step`,
  `g29_value`, `g29_nilPanic`, `g29_boundsPanic`, `g29_term`.
- `Spec30.lean`: what `checkG30` accepted (`checkG30_lowered`, `checkG30_nl`, `vkindNL30_spec`,
  `checkNL30_spec`).
- `G30.lean`: `stepLoc_convP`, `nl_conv`, `nl30_ops`, `g30_value`, `g30_nilPanic`,
  `g30_boundsPanic`, `g30_term`.
- `Spec32.lean`: what `checkG32` accepted (`VK32`, `bin32Kind_spec`, `binK32Kind_spec`,
  `un32Kind_spec`, `csincKind_spec`, `stlrKind_spec`, `vkind32_spec`, `checkG30_of_32`,
  `checkG32_spec`).
- `G32.lean`: `binF`, `binKF`, `unF`, `AluOp32`, `stepLoc_alu32`, `evalPure_bin32`,
  `evalPure_binK32`, `evalPure_un32`, `progStep_bin32`, `progStep_binK32`, `progStep_un32`,
  `progStep_csinc`, `binF_low`, `binKF_low`, `unF_low`, `lo_bin32`, `lo_binK32`, `lo_un32`,
  `valRel_binBool`, `valRel_xorBool`, `valRel_csinc`, `stepLoc_stlr`, `encode_storeBytes`,
  `addr_asPtrWord`, `progStep_stlr`, `g32_bin`, `g32_binK`, `g32_un`, `g32_csinc`, `g32_stlr`,
  `vk32_step`, `vk32_stepU`, `g32_value`, `vk32_nil`, `g32_nilPanic`, `g32_boundsPanic`,
  `g32_term`.
- `Spec31.lean`: what `checkG31` accepted (`uL31_succ`, `uIn_nl`, `uL31_nl`, `movdOK31_spec`,
  `uEdgesOK_entry`, `uEdgesOK_edge`, `checkG31_nl`, `checkG31_spec`).
- `Keep31.lean`: `VK32` of a `keep31` value is `VK3` (`vk32_vk3`, through `vk4_vk3` … `vk32_vk28`).
- `G31.lean`: `uok_of_x`, `uokl_of_x`, `uStep31_keep`, `uStep31_other`, `uokl_keep`, `vk3_keep`,
  `vk31_step`, `uL_nl30`, `g31_value`, `g31_nilPanic`, `g31_boundsPanic`, `g31_term`.
- `Spec33.lean`: what `checkG33` accepted (`VK33`, `ubfizOK_spec`, `un33Kind_spec`,
  `ubfizKind_spec`, `sraKind_spec`, `cmnwKind_spec`, `vkind33_spec`, `checkG31_of_33`,
  `checkG33_spec`).
- `G33.lean`: `unF33`, `AluOp33`, `evalPure_un33`, `keep31_alu33`, `stepLoc_alu33`,
  `progStep_un33`, `dp2Op_asr`, `progStep_asrK`, `ubfiz_ofNat`, `progStep_ubfiz`,
  `addSub_addFlags32`, `progStep_cmnwConst`, `lo_op1_64`, `lo_ubfiz`, `flagsRel_cmnwK`, `g33_un`,
  `g33_sra`, `g33_ubfiz`, `g33_cmnw`, `vk33_step`, `g33_value`, `vk33_nil`, `g33_nilPanic`,
  `g33_boundsPanic`, `g33_term`.
- `Spec34.lean`: what `checkG34` accepted (`uL34_succ`, `uIn34_nl`, `uL34_nl`, `movdOK34_spec`,
  `uEdgesOK34_entry`, `uEdgesOK34_edge`, `checkG33_of_34`, `checkG34_spec`).
- `Keep34.lean`: a `VK33` value `keep34` accepts writes at most its home's X register
  (`keepOps34`, `keep34_mem`, `keep34_aux`, `keep34_all`, `vk33_keep`).
- `G34.lean`: `uStep34_keep`, `uStep34_other`, `vk34_step`, `g34_value`, `g34_nilPanic`,
  `g34_boundsPanic`, `g34_term`.
- `Spec35.lean`: what `checkG35` accepted (`uL35_succ`, `uIn35_nl`, `uL35_nl`, `movdOK35_spec`,
  `uEdgesOK35_entry`, `uEdgesOK35_edge`, `checkG33_of_35`, `checkG35_spec`).
- `Keep35.lean`: G35's table across a pair load, a select of one or a narrow load
  (`ldEntry35_spec`, `uStep35_ld`, `uStep35_pair`, `uStep35_other`, `ops35`, `ops35_mem`,
  `sel_wb_pair`, `uok_ldW`, `uokl_ld`, `uokl_pair`, `uokl_filter_x`, `ld_uokl`, `vk33_keep35`).
- `G35.lean`: `vk35_step`, `g35_value`, `g35_nilPanic`, `g35_boundsPanic`, `g35_term`.
- `Spec36.lean`: what `checkG36` accepted (`VK36`, `sh36Kind_spec`, `shOp36Kind_spec`,
  `tst36Kind_spec`, `vkind36_spec`, `checkG33_of_36`, `checkG36_spec`).
- `G36.lean`: `shF36`, `shOpF36`, `shOpV36`, `evalPure_sh36`, `evalPure_shOp36`, `AluOp36`,
  `uStep35_alu36`, `stepLoc_alu36`, `progStep_sh36`, `progStep_shOp36`, `progStep_tst36`,
  `mod64_low`, `lo_sh36`, `lo_shOp36`, `flagsRel_tst36`, `g36_sh`, `g36_shOp`, `g36_tst`,
  `vk36_step`, `g36_value`, `vk36_nil`, `g36_nilPanic`, `g36_boundsPanic`, `g36_term`.
- `Spec37.lean`: what `checkG37` accepted (`VK37`, `maddOK_spec`, `sbfxOK_spec`,
  `bin37Kind_spec`, `un37Kind_spec`, `madd37Kind_spec`, `sbfxKind_spec`, `vkind37_spec`,
  `checkG33_of_37`, `checkG37_spec`).
- `G37.lean`: `binF37`, `unF37`, `maddF37`, `AluOp37`, `uStep35_alu37`, `stepLoc_alu37`,
  `progStep_bin37`, `progStep_un37`, `progStep_madd37`, `progStep_sbfx37`, `lo_bin37`, `lo_un37`,
  `lo_madd37`, `lo_sbfx37`, `g37_bin`, `g37_un`, `g37_madd`, `g37_sbfx`, `vk37_step`, `g37_value`,
  `vk37_nil`, `g37_nilPanic`, `g37_boundsPanic`, `g37_term`.
- `Spec38.lean`: what `checkG38` accepted (`VK38`, `ldarHome?_some`, `ldarTy_spec`,
  `ldarSelTy_spec`, `ldarKind_spec`, `selLdarKind_spec`, `vkind38_spec`, `checkG33_of_38`,
  `checkG38_spec`).
- `G38.lean`: `LdarPre`, `G38Pre`, `ldar?_some`, `ldar_ne`, `uStep35_ldar`, `uStep35_selLdar`,
  `stepLoc_ldar`, `write_ldar`, `read_ldar`, `asPtrWord_of_addr`, `decodePtr_eq`, `ldar_val`,
  `valRel_ldar`, `progStep_ldar`, `kldar_kStep`, `ksel38_of_reads`, `g38_ldar`, `g38_sel0`,
  `g38_sel1`, `vk38_step`, `g38_value`, `vk38_nil`, `g38_nilPanic`, `g38_boundsPanic`, `g38_term`.
- `G39.lean`: `checkG39_spec`, `refsLive_spec`, `liveCtx_ctx`, `liveCtx_temps`, `liveCtx_ty`,
  `home_live`, `read_live`, `write_live`, `clobber_live`, `signOf_live`, `movdLoc_live`,
  `stepLoc_live`, `enterListLoc_live`, `control_live`, `stepTermLoc_live`, `runLoopLoc_live`,
  `runCtxLoc_live`, `runLoc_live`, `g39_value`, `g39_nilPanic`, `g39_boundsPanic`, `g39_term`.
- `Spec40.lean`: what `checkG40` accepted (`memKeep_spec`, `memPure_spec`, `initMemKind_spec`,
  `vkind40_spec`, `vkind40_initMem`, `checkG33_of_40L`, `checkG40L_spec`, `checkG40_spec`).
- `G40.lean`: `MemInit`, `clobberMask_memfr`, `clobber_memfr`, `writeParts_memfr`, `write_memfr`,
  `stepLoc_shape`, `stepLoc_initMem`, `memInit_stepLoc`, `memInit_stepTermLoc`, `uStep35_initMem`,
  `g40L_initMem`, `g40L_value`, `g40L_nilPanic`, `g40L_boundsPanic`, `g40L_term`, `g40_value`,
  `g40_initMem`, `g40_nilPanic`, `g40_boundsPanic`, `g40_term`.
- `Spec41.lean`: what `checkG41` accepted (`cmpSh41?_some`, `cmnKind_spec`, `cmpShKind_spec`,
  `vkind41_spec`, `vkind41_initMem`, `checkG33_of_41L`, `checkG41L_spec`, `checkG41_spec`).
- `G41.lean`: `CmpPre`, `G41Pre`, `AluOp41`, `uStep35_alu41`, `stepLoc_alu41`, `addSub_addFlags`,
  `progStep_cmnConst`, `progStep_cmpShift`, `flagsRel_cmnK`, `flagsRel_cmpSh41`, `g41_cmn`,
  `g41_cmpSh`, `vk41_step`, `g41L_value`, `g41L_initMem`, `g41L_nilPanic`, `g41L_boundsPanic`,
  `g41L_term`, `g41_value`, `g41_initMem`, `g41_nilPanic`, `g41_boundsPanic`, `g41_term`.
- `Spec42.lean`: what `checkG42` accepted (`VK42`, `andWKind_spec`, `vkind42_spec`,
  `vkind42_initMem`, `checkG33_of_42L`, `checkG42L_spec`, `checkG42_spec`).
- `G42.lean`: `imm_bit_false`, `lo_andW`, `valRel_andW`, `g42_andW`, `uStep35_andK`, `vk42_step`,
  `vk42_nil`, `vk42_pb`, `g42L_value`, `g42L_initMem`, `g42L_nilPanic`, `g42L_boundsPanic`,
  `g42L_term`, `g42_value`, `g42_initMem`, `g42_nilPanic`, `g42_boundsPanic`, `g42_term`.
- `Spec43.lean`: what `checkG43` accepted (`keepsTo_succ`, `cleanAt_succ`, `initMemClean_spec`,
  `cleanOK_edge`, `vkind43_spec`, `vkind43_initMem`, `vkind43_eq42`, `checkG33_of_43L`,
  `checkG43L_spec`, `checkG43_spec`).
- `G43.lean`: `memInit_stepLoc_keep`, `cleanAt_zero`, `memInit_clean_step`, `memInit_clean_term`,
  `g43L_value`, `g43L_initMem`, `g43L_nilPanic`, `g43L_boundsPanic`, `g43L_term`, `g43_value`,
  `g43_initMem`, `g43_nilPanic`, `g43_boundsPanic`, `g43_term`.
- `Spec44.lean`: what `checkG44` accepted (`fobjOf?_some`, `fargObj_spec`, `fresObj_spec`,
  `fTy_spec`, `VK44`, `fkind44_spec`, `vkind44_spec`, `vkind44_initMem`, `vkind44_eq43`,
  `checkG33_of_44L`,
  `checkG44L_spec`, `checkG44_spec`).
- `FMove.lean`: `maskN_low`, `fpIdx?_f0`, `progStep_fmovVV`, `progStep_fmovXV`, `progStep_fmovVX`,
  `progStep_fconst`, `progStep_floadAt`, `progStep_fstoreAt`, `objV?_some`, `objV?_inj`,
  `locMatch_setRegV`, `fvalRel_retypeL`, `fval_cases`, `fvalRel_low`, `valRel_of_fvalRel`,
  `fvalRel_of_valRel`, `op_regV`, `arg_relV`.
- `G44.lean`: `FLoadPre`, `G44Pre`, `stepLoc_pureF`, `stepLoc_fload`, `stepLoc_fstore`,
  `fvalRel_gpfp`, `lo_fmovVX`, `fvalRel_fconst`, `g44_fcopy`, `g44_fcopyNone`, `g44_gpfp`,
  `g44_fpgp`, `g44_fconst`, `g44_fload`, `g44_fstore`, `uokl_fcopy`, `uStep35_f44`,
  `vk44_step`, `vk44_nil`, `vk44_pb`, `g44L_value` … `g44L_term`, `g44_value`, `g44_initMem`,
  `g44_nilPanic`, `g44_boundsPanic`, `g44_term`.
- `Spec45.lean`: what `checkG45` accepted (`VK45`, `fkind45_spec`, `vkind45_spec`,
  `vkind45_initMem`, `checkG33_of_45L`, `checkG45L_spec`, `checkG45_spec`).
- `G45.lean`: `fLoadIdxOp?_op`, `fStoreIdxOp?_op`, `FIdxPre`, `G45Pre`, `stepLoc_fLoadIdx`,
  `stepLoc_fStoreIdx`, `g45_fldIdx`, `g45_fstIdx`, `uStep35_f45`, `vk45_step`, `vk45_nil`,
  `vk45_pb`, `g45L_value` … `g45L_term`, `g45_value`, `g45_initMem`, `g45_nilPanic`,
  `g45_boundsPanic`, `g45_term`.
- `FArith.lean`: the inversions `fp2Of_some` … `fp3Of_some`, `cvtfBits`, `fcvtzBits`,
  `progStep_fp2`, `progStep_fp1`, `progStep_cvtf`, `progStep_fcvtz`, `progStep_fcmp`,
  `progStep_fcmp0`, `progStep_fp3`, `SameNaN`, `add_comm_of`, `mul_comm_of`, `NaNSwap`,
  `FNaNSwap`, `ordered_of`, `fvalRel_fp2`, `fvalRel_fsubdiv`, `fvalRel_fp1`, `fvalRel_cvtf`,
  `lo_fcvtz`, `flagsRel_fcmp`, `flagsRel_fcmp0`, `mulAdd_comm_of`, `FSameNaN`, `fvalRel_fma`.
- `Spec46.lean`: what `checkG46` accepted (`VK46`, `fbin46_spec` … `fma46_spec`, `fkind46_spec`,
  `vkind46_spec`, `vkind46_initMem`, `checkG33_of_46L`, `checkG46L_spec`, `checkG46_spec`).
- `G46.lean`: `FArithPre`, `G46Pre`, `fops46`, `fops46_facts`, `fops46_eval`, `stepLoc_pure46`,
  `g46_fbin`, `g46_fun`, `g46_cvtf`, `g46_fcvtz`, `g46_fcmp`, `g46_fcmp0`, `fmaPat_ok`,
  `g46_fma`, `uStep35_f46`, `vk46_step`, `vk46_nil`, `vk46_pb`, `g46L_value` … `g46L_term`,
  `g46_value`, `g46_initMem`, `g46_nilPanic`, `g46_boundsPanic`, `g46_term`.
- `Spec47.lean`: what `checkG47` accepted (`VK47`, `abiRegOK_spec`, `fArgsOK_spec`,
  `callKind47_spec`, `icallErr47_spec`, `icallKind47_spec`, `selKind47_spec`, `fcall47_spec`,
  `vkind47_spec`, `vkind47_initMem`, `checkG33_of_47L`, `checkG47L_spec`, `checkG47_spec`).
- `G47.lean`: `argsV`, `g47_selF`, `uStep35_call47`, `vk47_ops`, `vk47_step`, `vk47_nil`,
  `vk47_pb`, `g47L_value` … `g47L_term`, `g47_value`, `g47_initMem`, `g47_nilPanic`,
  `g47_boundsPanic`, `g47_term`.
- `Progs50.lean`: `progStep_ldpw` (`LDPW`, `LDPSW`), `progStep_fldp` (`FLDPD`, `FLDPS`).
- `Spec50.lean`: what `checkG50` accepted (`VK50`, `pairOp50_cases`, `fpairTys_spec`,
  `ldp50_spec`, `sel50_spec`, `pair50_spec`, `vkind50_spec`, `vkind50_initMem`,
  `checkG33_of_50L`, `checkG50L_spec`, `checkG50_spec`).
- `G50.lean`: `PairPre50`, `G50Pre`, `stepLoc_ldPair`, `ofInt_addN`, `pairAddr_noAuxN`,
  `loadPair_tupleN`, `g50_ldpX`, `g50_ldpF`, `g50_selF`, `uStep35_pair50`, `uStep35_sel50`,
  `vk50_ops`, `vk50_step`, `vk50_nil`, `vk50_pb`, `g50L_value` … `g50L_term`, `g50_value`,
  `g50_initMem`, `g50_nilPanic`, `g50_boundsPanic`, `g50_term`.
- `Spec51a.lean`, `Spec51b.lean`, `Spec51c.lean`: what each group of `checkG51` accepted (`VK51a`,
  `VK51b`, `VK51c`; `vkind51X_spec`, `vkind51X_none`, `vk51X_op`); `Spec51.lean`: `VK51`,
  `vkind51_spec`, `vkind51_initMem`, `checkG33_of_51L`, `checkG51L_spec`, `checkG51_spec`.
- `G51a.lean`: `Pre51a`, `progStep_csneg`, `progStep_cmnReg`, `progStep_cmnwReg`,
  `progStep_tstwReg`, `vk51a_step`; `G51b.lean`: `progStep_mvnSh51b`, `progStep_sbfiz51b`,
  `progStep_rorK51b`, `progStep_ror51b`, `vk51b_step`; `G51c.lean`: `reg_full51c`, `lo_add51c` …,
  `vk51c_step`.
- `G51.lean`: `G51Pre`, `vk51_step`, `vk51_nil`, `vk51_pb`, `g51L_value` … `g51L_term`,
  `g51_value`, `g51_initMem`, `g51_nilPanic`, `g51_boundsPanic`, `g51_term`.
- `Spec49.lean`: what `checkG49` accepted (`FrameVar49OK`, `frameVar49?_spec`,
  `vkindVar49_spec`, `vkind49_spec`, `vkind49_initMem`, `checkG33_of_49L`, `checkG49L_spec`,
  `checkG49_spec`).
- `G49.lean`: `VarsAt49`, `G49Env`, `VarsAt49.extend`, `symAddr_local`, `pairAddr_local`,
  `frameOffN_add`, `var49_addr`, `stepLoc_addrLocal`, `g49_addr`, `g49_load`, `g49_store`,
  `g49_ldp`, `g49_stp`, `uStep35_nil`, `vk49_ops`, `vk49_step`, `vk49_nil`,
  `vk49_pb`, `g49L_value` … `g49L_term`, `g49_value`, `g49_initMem`, `g49_nilPanic`,
  `g49_boundsPanic`, `g49_term`.
- `Spec52b.lean`: what `vkind52b` accepted (`VK52b`, `vkind52b_spec`, `vkind52b_none`,
  `vk52b_op`); `Spec52.lean`: `VK52`, `vkind52_spec`, `vkind52_initMem`, `vkind52_eq49`,
  `checkG33_of_52L`, `checkG52L_spec`, `checkG52_spec`.
- `G52b.lean`: `remF52b`, `rem52b?_some`, `stepLoc_rem52b`, `progStep_rem52b`, `lo_rem52b`,
  `g52b_rem`, `vk52b_step`; `G52.lean`:
  `vk52_step`, `vk52_nil`, `vk52_pb`, `g52L_value` … `g52L_term`, `g52_value`, `g52_initMem`,
  `g52_nilPanic`, `g52_boundsPanic`, `g52_term`.
- `Spec53a.lean`: what `vkind53a` accepted (`VK53a`, `moveKind_spec`, `vkind53a_spec`,
  `vkind53a_none`, `vk53a_op`, `moveCovers_spec`); `Spec53.lean`: `VK53`, `vkind53_spec`,
  `vkind53_initMem`, `vkind53_eq52`, `checkG33_of_53L`, `checkG53L_spec`, `checkG53_spec`.
- `G53a.lean`: `Pre53a`, `vk53a_step`; `G53.lean`: `G53Pre`, `vk53_step`, `vk53_nil`, `vk53_pb`,
  `g53L_value` … `g53L_term`, `g53_value`, `g53_initMem`, `g53_nilPanic`, `g53_boundsPanic`,
  `g53_term`.
- `Spec54a.lean`: what `vkind54a` accepted (`VK54a`, `zeroLoopKind_spec`, `moveLoopKind_spec`,
  `vkind54a_spec`, `vkind54a_none`, `vk54a_op`, `argDest_spec`), `loopOK_spec`, `skipFrom_eq`,
  `oneAt2_next`, `manyAt2_append`, `loopTgt_spec`; `Spec54.lean`: `VK54`, `vkind54_spec`,
  `vkind54_initMem`, `vkind54_eq53`, `vkind54_eq49`, `checkG33_of_54L`, `checkG54L_spec`,
  `checkG54_spec`.
- `G54L.lean`: `Keeps54`, `ctx_mem_post`, `progStep_stpP`, `progStep_fldpqP`,
  `progStep_fstpqP`, `progStep_subOne`, `pstar_one54`, `count_run`, `loop_run`, `clobber_get54`,
  `clobber_keeps54`; `G54a.lean`: `Pre54a`, `stepLoc_zloop`, `zloopStores`, `stpP_run`,
  `zloop_run`, `g54a_zero`; `G54b.lean`: `Pre54b`, `stepLoc_mloop`, `mloopChunks`, `cpW_shift`,
  `cpMem_shift`, `cpP_one`, `mloop_run`, `g54b_move`; `G54.lean`: `G54Pre`, `vk54_step`,
  `vk54_nil`, `vk54_pb`, `g54L_value` … `g54L_term`, `g54_value`, `g54_initMem`,
  `g54_nilPanic`, `g54_boundsPanic`, `g54_term`.
- `Spec55a.lean`: what `vkind55a` accepted (`VK55a`, `frintOf_some`, `vkind55a_spec`,
  `vkind55a_none`, `vk55a_op`); `Spec55.lean`: `VK55`, `vkind55_spec`, `vkind55_initMem`,
  `checkG33_of_55L`, `checkG55L_spec`, `checkG55_spec`.
- `G55a.lean`: `ops55a`, `ops55a_facts`, `stepLoc_pure55`, `fpIdx?_arng`, `fpIdx?_vOfF`,
  `progStep_simd55`, `progStep_frint55`, `fvalRel_simd55`, `fvalRel_frint55`, `g55_simd`,
  `g55_frint`, `vk55a_step`; `G55.lean`: `vk55_step`, `vk55_nil`, `vk55_pb`, `g55L_value` …
  `g55L_term`, `g55_value`, `g55_initMem`, `g55_nilPanic`, `g55_boundsPanic`, `g55_term`.
- `Spec55b.lean`: what `vkind55b` accepted (`VK55b`, `extrOK_spec`, `negSh55bKind_spec`,
  `clzw55bKind_spec`, `mull55bKind_spec`, `extr55bKind_spec`, `vkind55b_spec`, `vkind55b_none`,
  `vk55b_op`); `G55b.lean`: `AluOp55b`, `aluOp55b_facts`, `stepLoc_alu55b`, `progStep_negSh55b`,
  `progStep_clzw55b`, `progStep_smull55b`, `progStep_extr55b`, `lo_negSh55b`, `lo_clzw55b`,
  `lo_mull55b`, `lo_extr55b`, `g55b_negSh`, `g55b_clzw`, `g55b_mull`, `g55b_extr`, `vk55b_step`.
- `Spec57a.lean`/`G57a.lean` (group A: `VK57a`, `vkind57a_spec`, `ops57a_facts`, `vk57a_step`),
  `Spec57b.lean`/`G57b.lean` (group B: `VK57b`, `vkind57b_spec`, `ops57b_facts`, `vk57b_step`);
  `Spec57.lean`: `VK57`, `vkind57_spec`, `vkind57_initMem`, `checkG33_of_57L`, `checkG57L_spec`,
  `checkG57_spec`; `G57.lean`: `vk57_step`, `vk57_nil`, `vk57_pb`, `g57L_value` … `g57L_term`,
  `g57_value`, `g57_initMem`, `g57_nilPanic`, `g57_boundsPanic`, `g57_term`.
- `Spec56.lean`: `VK56`, `vkind56a_none`, `vkind56_spec`, `vkind56_initMem`, `constSymA_spec`,
  `checkG33_of_56L`, `checkG56L_spec`, `checkG56_spec`; `RoByte.lean`: `ro_byte`, `ro_addr`;
  `G56.lean`: `RoPre56`, `roAlloc_byte`, `constRo_mem`, `readMem_fconst`, `g56_fconst`,
  `vk56_step`, `vk56_nil`, `vk56_pb`, `g56L_value` … `g56L_term`, `g56_value`, `g56_initMem`,
  `g56_nilPanic`, `g56_boundsPanic`, `g56_term`.
- `Spec48.lean`: what `checkG48` accepted (`VKsp48`, `VK48`, `callKind48_spec`, `spKind48_spec`,
  `kind48_spec`, `vkind48_spec`, `vkind48_initMem`, `checkG33_of_48L`, `checkG48L_spec`,
  `checkG48_spec`, `spHomes48_spec`, `spBase48_spec`).
- `G48a.lean`: `ctx_mem_sp`, `progStep_stpAt`, `stepLoc_fstpd`, `progStep_stpwAt`,
  `progStep_fstpdAt`, `wf_of_canWrite`, `sepW_out`, `g48_spStore`, `g48_spLoad`, `g48_spStp`,
  `g48_spStpw` (on `G57a.lean`'s `stepLoc_stpw`), `g48_spFstpd`, `g48_spFStore`, `g48_spFLoad`;
  `G48.lean`: `CallOKStk`,
  `sp_base48`, `opsX48`, `uokl_x48`, `uokl_spLoad48`, `vk48_sp`, `vk48_step`, `VKsp48.ops`,
  `vk48_nil`, `vk48_pb`, `g48L_value` … `g48L_term`, `g48_value`, `g48_initMem`,
  `g48_nilPanic`, `g48_boundsPanic`, `g48_term`.
- `Spec58a.lean`/`G58a.lean` (G58's group A: `VK58a`, `vkind58a_spec`, `vkind58a_none`,
  `vk58a_op`, `ops58a_facts`; `rev16_low58`, `intBytes_mod58`, `encode_fit58`, `round_id58`,
  `lo_rev16w58`, `lo_maddw58`, `lo_op1B58`, `lo_sh58`, `valRel_csinc58`, `g58_rev16w`,
  `g58_maddw`, `g58_bin`, `g58_binK`, `g58_sh`, `g58_ubfiz`, `g58_csinc`, `g58_stlr`,
  `g58_round`, `uStep35_58a`, `vk58a_step`); `Spec58.lean`: `VK58`, `vkind58_spec`,
  `vkind58_initMem`, `checkG33_of_58L`, `checkG58L_spec`, `checkG58_spec`; `G58.lean`:
  `vk58_step`, `vk58_nil`, `vk58_pb`, `g58L_value` … `g58L_term`, `g58_value`, `g58_initMem`,
  `g58_nilPanic`, `g58_boundsPanic`, `g58_term`.
- `Spec60.lean` (G60, G59 with G56's float constants: `VK60`, `vkind60_spec`, `vkind60_initMem`,
  `vkind57_eq55`, `vkind60_eq48`, `vkind48_ok`, `kind48_cases`, `vkind60_ok49`,
  `checkG33_of_60L`, `checkG60L_spec`, `checkG60_spec`); `G60.lean`: `vk60_step`, `vk60_nil`,
  `vk60_pb`, `g60L_value` … `g60L_term`, `g60_value`, `g60_initMem`, `g60_nilPanic`,
  `g60_boundsPanic`, `g60_term`.
- `Spec61a.lean`/`Step61.lean`/`Progs61.lean`/`G61V.lean` (G61's group A: `VK61a`,
  `vkind61a_spec`, `vkind61a_none`, `vk61a_op`, `atomOK_spec`; `atom61?_facts`, `stepLoc_rmw61`,
  `stepLoc_cas61`, `write_atom61`; `progStep_ldaxr`, `progStep_stlxr`, `progStep_casal`,
  `progStep_lse`, `progStep_addTo`; `old_rel61`, `res_rel61`, `valRel_int2`, `fit_asInt61`,
  `maskN_store`, `subFlags_z64`/`_z32`, `atom_finish`); `G61a.lean`: `xchg_run`, `atom_store61`,
  `g61_xchg`; `G61b.lean`: `add_run`, `logic_run`, `g61_add`, `g61_logic`; `G61c.lean`:
  `cas_run`, `g61_cas`; `G61d.lean`: `g61_lse`, `g61_casV`; `G61e.lean`: `uStep35_atom61`,
  `uStep35_selAtom61`, `vk61a_step`; `Spec61.lean`: `VK61`, `vkind61_spec`, `vkind61_initMem`,
  `checkG33_of_61L`, `checkG61L_spec`, `checkG61_spec`; `G61.lean`: `vk61_step`, `vk61_nil`,
  `vk61_pb`, `g61L_value` … `g61L_term`, `g61_value`, `g61_initMem`, `g61_nilPanic`,
  `g61_boundsPanic`, `g61_term`.
- `Spec62.lean`: `VK62`, `argKind62_spec`, `vkind62_spec`, `vkind62_initMem`, `checkG33_of_62L`,
  `checkG62L_spec`, `checkG62_spec`; `G62a.lean`: `ArgOK`, `stepLoc_arg`, `kStep_arg`,
  `uStep35_arg`, `g62_arg`; `G62.lean`: `vk62_step`, `vk62_nil`, `vk62_pb`, `g62L_value` …
  `g62L_term`, `g62_value`, `g62_initMem`, `g62_nilPanic`, `g62_boundsPanic`, `g62_term`.
- `Spec63.lean`: `VK63`, `fspill63_spec`, `freload63_spec`, `vkind63_spec`, `vkind63_initMem`,
  `checkG33_of_63L`, `checkG63L_spec`, `checkG63_spec`; `G63a.lean`: `FReloadPre`, `g63_fspill`,
  `g63_freload`, `uokl_f63`; `G63.lean`: `vk63_step`, `vk63_nil`, `vk63_pb`, `g63L_value` …
  `g63L_term`, `g63_value`, `g63_initMem`, `g63_nilPanic`, `g63_boundsPanic`, `g63_term`.
- `Spec64.lean`: `QAccessOK`, `qaccessA_spec`, `qresObj_spec`, `qargObj_spec`, `qpairTy_spec`,
  `VK64`, `qkind64_spec`, `vkind64_spec`, `vkind64_initMem`, `checkG33_of_64L`, `checkG64L_spec`,
  `checkG64_spec`; `G64a.lean`: `QLoadPre`, `stepLoc_qload`/`qstore`/`qldp`/`qstp`, `read_regB`,
  `write_regB`, `read_pairB`, `write_pairB`, `retypeB_cases`, `vrel_retypeB`, `store16_rel`,
  `arg_relB`, `core_setRegN`, `knext_setN`, `kpairB_kStep`, `blobRel_load`, `memInj_write16`,
  `progStep_fldpqAt`, `progStep_fstpqAt`, `OpAt`, `QBase`, `qbase64`, `op_regVB`, `g64_qload`,
  `g64_qstore`, `g64_qldp`, `g64_qstp`, `g64_qsel`, `uStep35_q64`, `uStep35_qsel64`; `G64.lean`:
  `vk64_step`, `vk64_nil`, `vk64_pb`, `g64L_value` … `g64L_term`, `g64_value`, `g64_initMem`,
  `g64_nilPanic`, `g64_boundsPanic`, `g64_term`. `LocMatch.lean`: `BlobRel`, `VRel`,
  `VRel.of_fval`, `VRel.fval`.

**Witnesses** (`GoFV/Proof/Witness/`): `GenG1.lean` (`clamp`: `g1_value`, `g1_term`),
`GenG2.lean` (`testInts`: `g2_value` on a spill, a static call, its memory and a reload, with a
callee that returns at once; `clamp`: `g2_value` on a G1 value and `g2_term`), `GenG3.lean`
(`pallocSum.start`, which G2 rejects: `g3_term` on the bit test `TBNZ [63]` both ways and
`g3_value` on `ANDconst`), `GenG4.lean` (`(*errorString).Error`, which G3 rejects: `g4_value` on
the pair load `LDP (R0), (R0, R1)` from a global's 16 bytes and its `Select1`/`Select0`;
`pallocSum.start`: `g4_term` on `TBNZ [63]`), `GenG5.lean` (`g` of `test/stackobj`, which G4
rejects: `g5_value` on a spill, a static call, its memory and the marker `KeepAlive` of the
spilled argument; `pallocSum.start`: `g5_term` on `TBNZ [63]`), `GenG6.lean` (`SChan.Send` of
`test/closedchan`, which G5 rejects: `g6_value` on the store of an argument to a frame temporary
(`MOVD R1, -8(RSP)`) and its address (`MOVD $-8(RSP), R1`), the variable at `SP + 16` under the
injection; `pallocSum.start`: `g6_term` on `TBNZ [63]`), `GenG7.lean` (`(*A).g` of `test/method`,
which G6 rejects: `g7_value` on the receiver's nil check `MOVB (R0), R27` with the receiver
pointing to a global, `g7_nilPanic` with a nil receiver, where `runProg` panics with `nilDeref`),
`GenG8.lean` (`sync_runtime_registerPoolCleanup` of std/runtime, which G7 rejects: `g8_value` on
the request `LoweredWB [2]` (`CALL runtime.gcWriteBarrier2(SB)`), its `Select0` and `Select1`,
under a hook that is `wbHook` with the buffer at `2^41`, which satisfies `WbOK`), `GenG9.lean`
(`runtime.fint64to32`, which G8 rejects (`R0` holds its 64-bit argument and its call's 32-bit
result): `g9_value` on the static call `CALL runtime.fintto32(SB)` with a callee that returns 7 in
`R0` (`CallOK`: `callOKc`), its result and its memory), `GenG10.lean` (`sync.Locker.Lock`, which
G9 rejects: `g10_value` on the interface call `CALL (R2)` through the code pointer of a global
function, with a callee hook at that address that returns at once (`ICallOK`: `icallOKc`), and
its memory), `GenG11.lean` (`adder.func1` of `examples/closures`, which G10 rejects: `g11_value` on
the closure pointer `LoweredGetClosurePtr` from the entry of a closure call whose context, a
pointer to a global, is in `X26` (`CloOK`: `cloOK0`)), `GenG12.lean` (`runtime.subtractb`, which
G11 rejects: `g12_value` on `uintptr(unsafe.Pointer(p))` of a pointer 16 bytes into the heap object
`heap 1`, injected at its Phase 1 address `2^41`, so `R0` holds the integer `2^41 + 16` that is the
machine word), `GenG13.lean` (`(*pageBits).clearAll`, which G12 rejects: `g13_value` on
`LoweredZero [64]`, the four `STP (ZR, ZR)` off `R0`, of the heap object `heap 1` holding 64 bytes
7 at `2^41`, after which `runLoc`'s memory holds 64 zero bytes there and so do the machine's),
`GenG14.lean` (`runtime.argv_index`, which G13 rejects: `g14_value` on `MOVDloadidx8`, `MOVD
(R0)(R1<<3), R0` with `R0` the start of `heap 1` at `2^41` and `R1` 2, loading the word 7 at
offset 16, after which `X0` is 7), `GenG15.lean` (`(*T3).M` of `test/recover`, which G14 rejects:
`g15_value` on `CALL main.T3.M(SB)`, whose empty-struct receiver the ABI assigns to the stack, with
a callee hook that returns at once, which satisfies `CallOKZ`: `callOKZ0`), `GenG16.lean`
(`spanSetSpinePointer.lookup` of std/runtime, which G15 rejects: `g16_value` on `ADDshiftLL [3]`,
`ADD R1<<3, R0, R0` with `R0` the start of `heap 1` at `2^41` and `R1` 2, after which `R0` holds
the integer `2^41 + 16` and so does `X0`), `GenG17.lean` (`runtime.getm`, which G16 rejects:
`g17_value` on `GetG` with an injection putting `runtime.g` at the goroutine in `X28`, which
satisfies `GetGOK`, after which the `g` register holds the pointer to `runtime.g`), `GenG18.lean`
(`setpf` of `test/ken_array`, which G17 rejects: `g18_value` on `MOVDstoreidx8`, `MOVD R1,
(R0)(R1<<3)` with `R0` the start of an 8-byte `heap 1` holding 7s at `2^41` and `R1` 0, after
which `runLoc`'s memory holds the word 0 there and the machine's 8 bytes at `2^41` are 0),
`GenG19.lean` (`main.func1` of `test/convert4`, which G18 rejects: `g19_boundsPanic` on
`LoweredPanicBoundsCR [16] {9}`, `[9]byte(s)` with `len(s) = 5` in `R0`: `PCDATA
$PCDATA_PanicBounds, $350` and `CALL runtime.panicBounds(SB)` under a hook that panics with
`boundsPanic 350`, which satisfies `BoundsOK` (`boundsOK_of`), after which `runProg` panics with
`.bounds 16 9 5`, as `runLoc`), `GenG20.lean` (`runtime.NumCPU`, which G19 rejects: `g20_value` on
`MOVW runtime.numCPUStartup(SB), R0` with `numCPUStartup = -2`, after which `UOK` makes `X0`
`0xffff_ffff_ffff_fffe`, and on `MOVDnop`, after which `runLoc`'s `R0` holds the 64-bit integer
`-2`, matched by the machine), `GenG21.lean` (`(*queueOnePass).next` of std/regexp, which G20
rejects: `g21_value` on `MOVWU 52(R0), R3` with `q.nextIndex = 0xffff_fffe`, after which `UOK`
makes `X3` its zero extension, and on `MOVDreg`, `MOVD R3, R4`, after which `runLoc`'s `R4` holds
the 64-bit integer `0xffff_fffe` and the machine's `X4` is `0x0000_0000_ffff_fffe`),
`GenG22.lean` (`runtime.Version`, which G21 rejects: `g22_value` on `LDP
runtime.buildVersion(SB), (R0, R1)` with `buildVersion = (nil, 7)`, after which `runLoc`'s `R1`
and the machine's `X1` hold 7), `GenG23.lean` (`bytes.shouldUseASCIISet`, which G22 rejects:
`g23_value` on `CMP $8, R0` with `len(chars) = 10` and on `GreaterThan`, `CSET GT, R0`, after
which `runLoc`'s `R0` holds `true` and the machine's `X0` is 1), `GenG24.lean` (`(*SChan).Recv` of
`test/closedchan`, which G23 rejects: `g24_value` on `SP` at the head of the receiving block, after
which `runLoc`'s Go register `SP` holds `SP`'s value and the related machine state is at the same
PC), `GenG25.lean` (the struct wrapper of `reflect.flag.ro` in `encoding/binary`, which G24
rejects: `g25_value` on `CSEL NE, R1, ZR, R0` with `R1 = 32` and the flags of `CMP $0` on 32,
after which `runLoc`'s `R0` holds 32 and the machine's `X0` is 32), `GenG26.lean` (`main.func1` of
examples/generics, which holds no arm64 op and which G25 rejects: `g26_value` on its `Copy`,
`MOVD R2, R0`, in Phase 1's mode with `x = 7` in `R2`, after which `runLoc`'s `R0` holds 7 and the
machine's `X0` is 7), `GenG27.lean` (`regexp.newLazyFlag`, which G26 rejects: `g27_value` on
`ORR R2<<32, R1, R0` with `uint32(r2) = 2` in `R1` and `r1 = 1` in `R2`, after which `runLoc`'s
`R0` holds `0x100000002` and the machine's `X0` is `0x100000002`), `GenG28.lean`
(`runtime.envKeyEqual`, which G27 rejects: `g28_value` on `CALL runtime.memequal(SB)` with two
strings of 8 equal bytes in `heap 1`, under the hook `Hm` that implements `memequal` on the machine
and satisfies `MemEqOK`, after which `runLoc`'s `R0` holds `true` and the machine's `X0` is 1),
`GenG29.lean` (the generated equality `.eq.M1K1M2` of test/genmeth1, which G28 rejects:
`g29_value` on `v33 = MOVDnop v31` in block `b5`, whose entry `(1, 16, false)` comes from the
`MOVHU` load two values earlier, across `v21 = MOVDnop v26`; with `0xbeef` in `R1` and `X1`
zero-extended from 16 bits, `runLoc`'s `R1` then holds the 32-bit `0xbeef` and the table after
`v33` gives the whole `X1 = 0xbeef`), `GenG30.lean` (`runtime.gclinkptr.ptr`, which holds no arm64
op and which G29 rejects: `g30_value` on its `Convert` in `R0`, no code, in Phase 1's mode with
`p = 0x1234` in `R0`, after which `runLoc`'s `R0` holds `0x1234` and the machine's `X0` is
`0x1234`), `GenG32.lean` (`or64` of test/armimm and `runtime.funpack64`, which G30 rejects:
`g32_value` on `v9 = OR v6 v3`, `ORR R1, R0, R0`, with `0x1234` and `0xaa00dd55000066`, after
which the machine's `X0` is their `OR`, and on `v56 = ORconst [1 << 52] v17`, `ORR
$0x10000000000000, R1, R1`, with the mantissa `0x123456789abcd`, after which `X1` has bit 52 set),
`GenG32b.lean` (`runtime.(*atomicOffAddr).StoreMarked`: `g32_value` on `v13 = NEG v7`, `NEG R1,
R1`, from `0xffffffeeddccbbab`, after which `X1 = 0x1122334455`, and on `v17 = STLR v6 v13 v1`,
`STLR R1, (R0)`, with `R0` pointing to an 8-byte heap block injected at `2^41`, after which
`runLoc`'s memory holds the word's bytes and the machine's 8 bytes at `2^41` read
`0x1122334455`), `GenG32c.lean` (`internal/bytealg.countGeneric`: `g32_value` on `v32 = CSINC
[NotEqual] v31 v31 v40`, `CSINC NE, R4, R4, R4`, with the flags of an equal `CMPW` and `R4 = 5`,
after which the machine's `X4 = 6`), `GenG31.lean` (`runtime.(*hexdumper).close`, which G32
rejects: `b1` loads the byte `h.nbuf` into `R4` and copies it to `R5`, and `b3`'s `v22 = MOVDreg
v8`, `MOVD R4, R2`, finds `R4`'s entry only in `uIn lc 3 = [(5, 8, false), (4, 8, false)]`, the end
of `b1`; `g31_value` on `v22` from a machine whose `X4`, `X5` are zero-extended from 8 bits, after
which the machine's whole `X2 = 0x2a`, and `g31_term` on `b1`'s `CBZW R5` to `b3` with `UOKL` of
`uIn lc 3`, which gives the whole `X5 = 0x2a`), `GenG33.lean` (`math/bits.ReverseBytes` and
`internal/bytealg.Cutover`, which G31 rejects: `g33_value` on `v9 = REV v6`, `REV R0, R0`, from
`0x0102030405060708`, after which the machine's `X0 = 0x0807060504030201`, and on `v10 = SRAconst [4]
v6`, `ASR $4, R0, R1`, from `-256`, after which `X1 = 0xfffffffffffffff0`), `GenG33b.lean`
(`runtime.(*mspan).pinnerBitSize` and `runtime.(*_func).isInlined`: `g33_value` on `v13 = UBFIZ
[272] v10`, `UBFIZ $1, R1, $16, R1`, from the 16-bit `0xbeef` with G31's table holding `R1`, after
which `X1 = 0x17dde`, and on `v3 = CMNWconst [1] v10`, `CMNW $1, R1`, from the 32-bit `0xffffffff`,
after which the machine's `Z` flag is set), `GenG34.lean` (`test/atomicload`'s `f`, which G33
rejects: `v11 = MOVBreg v9`, `MOVB R1, R2`, writes only `R2`, so G34's table keeps `R1`'s entry for
`v13 = MOVDreg v9`, where G31's is empty; `g34_value` on `v11` from the byte `0xbe` in `R1`, after
which the machine's `X2 = 0xffffffffffffffbe` and the table gives the whole `X1 = 0xbe`),
`GenG35.lean` (`regexp/syntax.(*InstOp).String`, which G34 rejects: the pair load `v44 = LDP
instOpNames(SB)` into `(R4, R5)` and its selects write neither `R2` nor `R3`, so G35's table keeps
their entries `[(3, 8, false), (2, 8, false)]` for `b7`'s `v29 = MOVDreg v16`, where G34's is empty;
`g35_value` on `v4 = Select1 v44` with the byte `0x2a` in `R2`, after which the table gives the
whole `X2 = 0x2a`), `GenG36.lean` (`encoding/hex.DecodedLen`, `x / 2`, which G35 rejects:
`g36_value` on `v7 = ADDshiftRL [63] v6 v6`, `ADD R0>>63, R0, R1`, from `x = -7`, after which the
machine's `X1 = -6`), `GenG37.lean` (`math/bits.Reverse`, which G36 rejects: `g37_value` on
`v9 = RBIT v6`, `RBIT R0, R0`, from `x = 0x0f`, after which the machine's
`X0 = 0xf000000000000000`), `GenG38.lean` (`sync/atomic.LoadInt64`, which G37 rejects:
`g38_value` on `v8 = LDAR v6 v1`, `LDAR (R0), R0`, from `addr` the pointer to the word 7 of
`GenG14`'s `heap 1`, `LdarPre` holding, after which the machine's `X0 = 7`), `GenG39.lean`
(`strings.HasSuffix`, which G38 rejects for the home `R0` of the removed `v47`: `v34 = ADD v17 v26`
runs alike under `lc0` and `liveCtx lc0`, and `g39_value` runs `ADD R3, R1, R4` from `len(s) = 5`,
`len(suffix) = 2`, after which the machine's `X4 = 7`), `GenG40.lean` (`unicode/utf16.IsSurrogate`,
whose `InitMem` `v1` sits in the return block `b2`, which G39 rejects: from a state holding the
initial memory, `stepLoc` runs `v1` to a state that holds it again (`memInit_stepLoc`), and
`g40_initMem` relates it to the machine after no code), `GenG41.lean` (`runtime.traceNextGen`,
whose `CMN $1, R0` (`v5`, `CMNconst`) G40 rejects: `CmpPre` holds for `gen = -1`, an integer, and
`g41_value` runs `v5` to flags with `Z` set, after which the machine's `Z` is set), `GenG42.lean`
(`unicode/utf8.RuneStart`, whose `AND $192, R0, R1` (`v4`, `ANDconst` of the byte `b` at type
`uint32`) G41 rejects: from `b = 0xc5` with ones above the low byte of `X0`, `g42_value` runs `v4`
to `R1 = 0xc0`, after which the low 32 bits of the machine's `X1` are `0xc0`), `GenG43.lean`
(`runtime.(*debugLogWriter).varint`, whose `InitMem` `v1` sits in the return block `b2` before a
call, which G42 rejects: `b2` is clean and `(b2, 1)` a clean position, `stepLoc` runs `v1` from a
state holding the initial memory to one holding it at the clean `(b2, 2)` (`memInit_clean_step`),
and `g43_initMem` relates it to the machine after no code).
Each decides its inputs by compiled evaluation (`native_decide`, pinned in
`scripts/axioms-allowlist.txt`).

## 6. Future work: recursion through function values

`ICallOK` (G10) asks that the address in an interface or closure call's code register be no Prog
address of the caller: `runProg` runs one function's Prog list (`Link.byId … ps`) and hands every
other address to the hook `H.call`, whose contract `CallSpec` stands for the callee. A call
through a function value back into the caller's own code — `f := func(n int) int { … f(n-1) … }`,
a method that calls itself through an interface — breaks the premise, so `g10_value` to
`g12_value` say nothing about such a run (sound, but incomplete). `G2Env.syms` excludes direct
self-calls the same way. Lifting the restriction needs the callee's contract to be proven per
function instead of trusted per call:

1. **One image for the program.** `runProg`/`runMach` run the linked program: the Progs of every
   Go function at their linked addresses (the P0 lists composed by the linker's layout; `Link`
   over the image), hooks only for code outside it (runtime assembly such as
   `gcWriteBarrier<n>`, `morestack`, the runtime entry points of semantics3 §6).
2. **A function contract indexed by call depth.** Phase 1 runs a call through the environment
   (`Env.extern`, `callOp`); for the whole program, the environment `envₙ` runs each callee's own
   `runLoc` under `envₙ₋₁`, and `env₀` makes every call `stuck`. `FunSpec n f`: for every run of
   `runLoc` on `f` under `envₙ` that returns (or panics) with outcome `o`, and every machine state
   at `f`'s entry related to that activation (`MachEntry`: arguments in their ABI registers under
   `ι`, the return address in `X30`, room for the frame, the closure context in `R26`), the image
   runs to the return address in a state that `CallSpec` describes for `o` (results in the ABI
   result registers, `SP`/`R28`/`R29` and the caller's frame kept, the memory injected by an
   extension of `ι`), or panics as `o` does. `CallSpec` becomes the conclusion of `FunSpec`
   instead of a premise.
3. **Per function:** `MachRefines` for `f` (§1: the value and terminator theorems composed along
   a run, with the entry and exit of C6/D3) proven under `∀ g, FunSpec n g` for the functions of
   the image gives `FunSpec (n + 1) f`. At a call (`CALL sym(SB)` or `CALL (Rn)`) under
   `envₙ₊₁`, `runLoc`'s callee outcome is a run of the callee under `envₙ`, so `FunSpec n g`
   applies for every callee `g` the code pointer enters — `g = f` (recursion through a function
   value, or a direct self-call) and mutually recursive functions included. The step lemma at a
   call relates the state at the `CALL` to the state at the return address through the callee's
   whole run (a `PStar` over the image) instead of one `PStep.hook`.
4. **Induction on `n`** gives `∀ n f, FunSpec n f` for every function of the image at once (the
   base case is the per-function theorem with no callee: under `env₀` a run that reaches a call is
   `stuck` and carries no obligation). A returning or panicking run of the program is one under
   some `envₙ`, so every `CallOK`/`ICallOK` premise whose callee is in the image is discharged.
   What stays trusted: the hooks' contracts for code outside the image (`WbOK`, the runtime entry
   points), and that an indirect call's code word (a funcval's first word, an itab's `fun` entry)
   is the linked entry of the function Phase 1's `callTarget` names — a fact about the program's
   data relocations (`R_ADDR`) that a validator of the linked data, as D2's `checkEdit` is for the
   code, can check.

The contract is partial, as the refinement of §1 is: a run that neither returns nor panics is no
outcome to match.

## 7. `checkObj`: P0 against the assembled words (D2–D5)

`checkObj ps spills obj` (`GoFV/Asm/CheckObj.lean`, symbolic states in `CheckObjSym.lean`, the
linker model in `CheckObjLink.lean`) checks the assembler's output `obj` (text bytes, relocations,
and the assembler's final Prog list, used only as a hint for each Prog's PC) against the P0 list
`ps` that `runProg` runs under `Link.byId`. It recomputes none of the assembler's choices
(`progedit`, `preprocess`, `span7`).

- **Layout.** Each P0 Prog owns the words from its PC to the next P0 Prog's PC; every word is
  checked. Pseudo-ops own none.
- **Per Prog.** The words are decoded and executed symbolically (`symWords`). The two words of
  `R_ADDRARM64` and `R_ARM64_PCREL_LDST*` and the `BL` of `R_CALLARM64` run as linked. The result
  is compared with the Prog's own symbolic effect (`progSym`):
  - every general register but `X27` (the scratch) and `X30` (calls only);
  - `SP`, the flags, and the stores in order;
  - every machine load must be one the Prog performs;
  - the Prog must not read `X27`/`X30`;
  - branches go to the target Prog's offset, and calls go to the same symbol with addend 0.
- **Templates.**
  - The prologue (`checkPrologue`): the stack check, which loads `stackguard0` (`16(g)`) and
    compares it with `SP` or `SP − (autosize − 128)`, with `BLS` to the morestack tail; then the
    frame (`frameOK`: `SP − autosize`, the caller's `LR` at `0(SP)` and `FP` at `−8(SP)`,
    `R29 = SP − 8`, no load).
  - The epilogue at a P0 `RET` (`retOK`).
  - The morestack tail (`checkTail`: the register-argument spills, the call, the reloads, the jump
    back). The spills are planned by `tailPlan` (`off(RSP)` of argument registers `R0`–`R15`,
    `1`–`8` bytes, and `F0`–`F15`, `4` or `8` bytes (`FMOVS`/`FMOVD`, `FSTPS`/`FSTPD`: the
    `vStoreEx` of `V n`, `TailSlot.fp`), disjoint slots); before the call `SP` is kept and nothing
    loaded, after it `SP` and `R30` are kept, nothing stored and only slots loaded, every general
    register is its reload (`reloadOf sl false`) or kept, and every reloaded vector register is
    its slot's load (`TailSlot.vreload`, `VEx.ld`; the other vector registers are unconstrained,
    as the hook clobbers them). These are what the proof needs (the tightening to them kept
    obj-check's 7,741 functions on quick-v10). The `F` spills took quick-v10 from 8,464 to 8,544
    accepted: the 80 rejections `tail: spill register` are gone and no `tail:` reason is left.
- **Out of scope.** Words after the tail (literal pools, padding) are never executed by the
  checked ranges.

P0's `RET` (without operand, or of a symbol) is stuck in `runProg`, because its meaning is the
epilogue, stated on the machine. `arm64-decode` on quick-v10 after this change: 429,386/429,386
Progs and 122,770/122,770 blocks match.

**Coverage** (`lake exe obj-check --jobs 8 [--accept <gen-check table>] <corpus>/quick-v10`; the
assembler port `GoFV.Asm.flush` on each `prog0` section, as `asm-parity`, and `checkObj` on P0',
below; 0 parse or port errors):

| Functions | Accepted | P0 Progs in accepted functions |
| --: | --: | --: |
| 9,297 | 9,124 (98.13%) | 395,421 of 429,130 |
| G7 slice: 2,109 | 2,108 (99.95%) | |
| G8 slice: 2,323 | 2,322 (99.95%) | |
| G9 slice: 2,551 | 2,550 (99.96%) | 51,122 of 51,143 |

(Before the opcodes below: 5,533, 59.51%, 157,472 Progs.) Modelled since: the conditional selects
`CSEL`/`CSINC`/`CSINV`/`CSNEG` (`condSel` on the flags before the Prog; `Ex.csel`) and
`CSET`/`CSETM` (`CSINC`/`CSINV` of `ZR` on the inverted condition, not `AL`/`NV`); `MUL`/`MNEG`/
`MADD`/`MSUB` (and `W`) and `UMULH`/`SMULH` (`dp3`; `Ex.mkDp3` reads the `MADD` forms' operands at
the datasize); `CLZ`/`RBIT`/`REV`/`REV16`/`REV32` (`dp1`); the acquire loads `LDAR`/`LDARW`/`LDARH`/
`LDARB` and the release stores `STLR*` (`exclOp`; `execExcl`'s plain access); and `CALL (Rn)` as
`BLR` (`MCtl.callReg`/`PCtl.callReg`, matched register to register). `progSym` also checks that
calls come from `CALL`, register jumps from `RET` and branches go to the Prog of the operand `To`
(`ctlOp`), and `sameEffect` that every load of the Prog is a load of the words (the converse of the
earlier check, for `obj_panic`).

The one slice function that is rejected is `init.func47` of `test/nilptr2`: its `LDP` is
assembled with a literal-pool load (`LDR literal`), which is not modelled.

**SIMD&FP** (7,741 → 7,920; STATUS, `checkObj`): `Sym.v` (vector registers written, `VEx`),
`Ex.vlo`/`Ex.fcvtz` (the low part of a vector register, `FCVTZ*`), `Fl.fcmp`; `HoldsCore.v` is
`Sym.evalV`, `sameEffect` compares `V0`–`V31`. `symInsn` models `LDR`/`STR` `S`/`D`(/`Q` loads),
`LDP`/`STP` (`Q` loads), `fp1`/`fp2`/`fp3`, `FCMP`, `FMOV` immediate, `FCSEL` and `fcvtInt`;
`progSym` the `FMOV{S,D,Q}`, `FLDP*`/`FSTP{S,D}` and the `fpOp?` opcodes. The two sides meet on one
form per value (`VEx.mkOfX`: `FMOV ZR, Fd` is the constant 0). Most frequent reasons now:
`FSTPQ` 179 (`Q` stores), `LSL` by a register 176, `FMOVD` from the literal pool 126, `LDADDALW`
87, `CASALW` 81, morestack tail spill registers 79, `CASALD` 76, `LSR` by a register 69,
`LDADDALD` 65, `GETCALLERPC` 44, `UDIV` 41, `JMP` to a register 37, `MVN` 37.

**`Q` stores** (8,263 → 8,464; was 7,920 → 8,263 for the variable shifts, divisions, `REM`/`UREM`
and `BIC`/`ORN`/`EON`/`MVN`): `STR Q`/`STP Q` (`symVAccess`, `symVPair`) and `FMOVQ` stores/`FSTPQ`
(`fmovP`, `fpairP`) store `vStoreEx` of the register, `Ex.vq r` for 16 bytes (its 64-bit `eval`
the low half). `storesMem` (`HoldsCore.mem`) and `progSym`'s relation to `progEffect` (`ERel`)
write the low `8 n` bits of `Ex.eval128` (`vq r` all of `V r`, any other value zero-extended);
`Ex.eval128_setWidth` reduces it to `eval` for at most 8 bytes, which the integer stores and the
templates use. `exec` (`store`, `storeVal`) and `progEffect` (`Eff.apply`) both write a `Q`
register as one 16-byte little-endian `writeMem` with one nil-page check, so the store stays one
entry: two 8-byte entries would add the second half's address to `NoNil`, which neither side
checks (it differs from the first's near the top of the address space). Witnesses
`objOps_stpq_witness`, `objOps_strq_witness`, `objOps_eval128_witness`. Most frequent reasons
now: `FMOVD` 133 and `FMOVS` 30 of a constant that is not an `FMOV` immediate (`PCREL_LDST:
access`), `CASALW` 90, `LDADDALW` 89, morestack tail spill registers 80 (now accepted, below),
`CASALD` 79, `LDADDALD` 66, `GETCALLERPC` 44, `JMP` to a register 38, `DMB` 26, `UMULL` 19,
`LDORALB` 17.

The float constants are not a literal pool in the text: `progedit` rewrites `FMOVD $c, Fd` (not an
`FMOV` immediate) to a load of the read-only data symbol `$f64.<bits>` (`$f32.` for `FMOVS`), which
the assembler encodes as `ADRP` + `LDR D`/`S` with `R_ARM64_PCREL_LDST64`/`32` (e.g. `math.Ilogb`:
`reloc 20 8 R_ARM64_PCREL_LDST64 0 y10`, `y10 = "$f64.7fefffffffffffff"`). The machine reads the
symbol's bytes from `MState.mem` (`exec`'s `load`; `Code` is fetch-only), P0's `FCONST` is the
constant itself, and nothing in `ObjEnv` or `ObjRel` says that memory at `L.sym y` holds the
bits named by the symbol in every state of the run, nor that it is outside the nil page. A run
premise of `obj_star` cannot be discharged (the composition knows the memory only where
`LocMatch` holds); the design is in §10: the symbol is a Phase 1 read-only allocation, and the
composition runs `P0'`, P0 with `progedit`'s rewrite of the float constants, so that `checkObj`
compares a load with a load.

**P0'** (8,544 → 8,703, +159 of the 163 float-constant rejections; the other 4 now stop at a later
reason, `CASALW` 2, `LDADDALD` 1, `ADCS` 1): `obj-check` gives `checkObj` P0' (`GoFV.Asm.p0Prime`,
`GoFV/Asm/ConstLoad.lean`: each Prog `fconstSym?` names, `progedit`'s `FMOVS`/`FMOVD` cases, gets
`progedit`'s `From`, `MEM`/`EXTERN` of the constant symbol at offset 0, numbered as the port's
`flush` numbers it, `symIdx` at `(name, ABI0)`); `progSym`'s `fmovP` already models the load. On
the machine side the `R_ARM64_PCREL_LDST*` pair now admits a SIMD&FP access (`ldstLo?` returns
`vec`, `B`/`H`/`S`/`D` only; `symLdstAcc`: `symVAccess` for a vector access, `symAccess` for an
integer one). Proof: `decode_ldstLo` for either kind of access (bit 26 is `vec`),
`accessBytes_vec` (a non-`Q` vector access moves `2 ^ size` bytes, the relocation's scale),
`symVAccess_exec` (`insn_vaccess`) and the now public `symVAccess_fault` in `symUnit_sound` and
`symUnit_fault`. `ObjRel`, `ObjEnv` and the theorem statements are unchanged.

**Barriers** (8,703 → 8,729, +26: 26 of the 31 quick-v10 functions with a `DMB` or `PRFM`; the
other 5 stop at `LDORALB` 2, `VCNT` 2, `SBFIZ` 1): `DMB $k` and `PRFM 0(Rn), $k` (G57 group B, §4)
are no-ops on both sides. `progSymCore` has a `DMB` arm (`From` a constant, no `To`) and a `PRFM`
arm (`From` `MEM`, name `NONE`, offset 0, no index; `To` a constant), each `({}, .fall)`. Both
mirror `progEffect`'s `DMB`/`PRFM` arm (`fam_rest`, `eff_barrier`). On the machine side
`symInsn` already ran `.barrier` as a no-op. `symAccess` now returns `σ` for `PRFM` (`size = 3`,
`opc = 2`), as `execLdSt` does: no access, so no nil-page check, and no write-back for the
unsigned-offset form the assembler emits. The proof extends `insn_access` (the machine state
unchanged, PC moved on), `symAccess_mono` and `symAccess_fault` (a `PRFM` adds no access, so it
cannot reach the nil page). `ObjRel`, `ObjEnv` and the theorem statements are unchanged.
Witnesses `objBarrier_dmb_witness` (`GoFV/Proof/Witness/ObjBarrier.lean`: `checkObj` accepts
`runtime.mallocgcSmallNoscanReuse`; its `DMB $14` decodes to `.barrier 5 14`; `progSym_sound` on
that Prog) and `objBarrier_prfm_witness` (`PRFM PLDL1KEEP, [X0]` with `X0 = 0` runs through
`symInsn_sound` and keeps the memory; `PRFM (R0), $0` has the same effect).

**Atomics, per Prog** (8,729 → 8,729: no function gained yet, none lost; the obstacle moved from
the atomics' opcodes to their `R27` reads, below): the exclusive accesses and the LSE single
instructions genssa emits (`GoFV/Gen/Arm64ValueRt.lean` `atomic`) are modelled on both sides,
mirroring `progEffect`'s atomics arms. `exclOp` has `LDAXR{,W,H,B}` (an acquire load; on one core
the exclusive monitor has no effect). `atomOp`/`atomP` have `STLXR{,W,H,B} Rs, (Rn), Rstatus`
(the store, the status register 0: the exclusive store succeeds, the single-core row of
`docs/proofs/STATUS.md`), `CASAL{D,W,H,B} Rs, (Rn), Rt` (the old value to `Rs`; the store of
`Ex.eqsel n old Rs Rt old`, a new `Ex` form: `Rt` if the low `8 n` bits of the old value and
`Rs` agree, else the old value, whose store leaves the memory as it was) and the
read-modify-writes `LDADDAL*`/`LDCLRAL*`/`LDEORAL*`/`LDORAL*`/`SWPAL*` (the old value to `Rt`, the
store of `rmwEx o3 opc old Rs`, by `execAtomic`'s encoding: `LDADD`, `LDCLR`, `LDEOR`, `LDSET`,
`SWP`). On the machine side `symExcl` now runs `STXR`/`STLXR` (store, then `Rs ← 0`, as
`execExcl`), and `symInsn` has `.cas` and `.atomic` arms (`symRmw`: load, store, old value to the
destination). Proof: `insn_excl`, `insn_cas`, `insn_atomic` (`insn_rmw`; a `CAS` mismatch stores
the bytes read back, `writeMem_readMem`), their `_fault` cases (`insn_rmw_nil`: the load faults
first) and `symInsn_mono`; on the Prog side `fam_excl` (`LDAXR*`) and `fam_atom` (`eff_atom`:
`progEffect` of an `atomOp` name is its atomics branch `atomEff`). `progEffect` of a `CASAL`
mismatch stores nothing while the symbolic effect stores the old value, so the family result
`Out` has a fourth case: the relation for an effect with the same accesses and the same meaning
(`apply_store_same`), which `progSym_sound`/`progSym_fault` use as the first (`sound_rel`,
`fault_rel`). `ObjRel`, `ObjEnv` and the theorem statements are unchanged. Co-simulation
(`scripts/arm64-cosim.sh --fuzz 0 --words`, the 483 distinct quick-v10 words of these classes):
19 forms (`LDAXR`/`STLXR` B/W/X, `CASAL` W/X, `LDADDAL` W/X, `LDCLRAL`, `LDSETAL`, `SWPAL`
B/W/X), 4,864 cases, 0 mismatches. All 417 quick-v10 functions with these words come from
`goarm64 v8.0`, which pairs each LSE instruction with an LL/SC fallback; each still fails on a
Prog that reads `R27` set by the previous Prog (`STLXR …, R27; CBNZ R27` 215, `MOVW R1, R27;
CASAL R27, …` 171, `MVN R1, R27; LDCLRAL R27, …` 21), which `sameEffect`/`sameCtl` reject because
`ObjRel` does not relate `X27`. Accepting them needs an `X27` agreement invariant at such
readers in `obj_star` (next paragraph). Witnesses `objAtomic_prog_witness`
(`GoFV/Proof/Witness/ObjAtomic.lean`: `checkProg` accepts `sync/atomic.AddInt32`'s `LDADDALW`,
`LDAXRW`, `STLXRW` against their words; `progSym` and `symInsn` give the same effects, and
`CASALW R27, (R0), R2` and its word too), `objAtomic_ldadd_run`, `objAtomic_stlxr_run`,
`objAtomic_cas_hit`, `objAtomic_cas_miss` (`symInsn_sound` on the decoded words from concrete
states), `objAtomic_rmwEx`.

**Atomics across Progs: `X27`** (8,729 → 9,124, +395, none lost function by function; of the 407
functions that stopped at a Prog reading `R27`, 395 are accepted, 12 stop at a later Prog):
`checkObj` relates `X27` before a body Prog (`Tab.ok27`, one entry per Prog, `checkBody`) when
the Prog before it in the list is compared (not a skip, not `RET`), its words leave `X27` as the
Prog leaves `R27` (`est27 k m p mc`: the same `Ex`, over registers related before that Prog,
`Ex.regsOKK k`) and are no call (`MCtl.links`: a callee returns with any `X27`), and no Prog
branches to it (`branchTargets`: the `BRANCH` operands of the list, `branchTo`), so that it is
reached only by falling through from its predecessor. Such a Prog may read `X27`
(`sameEffectK k`, `sameCtl k`, `Sym.readsTmpK k`: `regsOK30`, `X30` still excluded).
`progSym`'s `ctlOp` now checks that a branch control's target is the Prog of the operand
`To` (`branchTo p = some id`), which `obj_step` needs to see that a taken branch lands on a
`branchTargets` member; every `progSymCore` branch already took its target from `To`
(`targetP`), so no function is lost. The invariant (`Sim.lean`) is
`X27At tab L ps s t`: at a Prog with `ok27`, `t.x 27 = s.x 27` (`at27`); at a symbol (after a
call), the return address `X30` names no Prog with `ok27` (`ret27`). `obj_step`, `obj_star`,
`obj_star_leaf` and `obj_panic` take it with `ObjRel` and `obj_step`/`obj_star` return it:
after the words of a Prog at index `k`, the next state is at the fall-through (then
`ok27[k+1]` needs `est27`, and the words' `X27` is `(m.getX 27).eval t = (p.getX 27).eval s`,
`eval_rel` over `regsOKK`; `ok27_next`), at a branch target (`ok27` false there, `ok27_tgt`) or,
for a call, at a symbol with the fall-through in `X30` (`est27` false for a call, so `ret27`);
a hook returns to `X30` (`HookMap`, strengthened: `s'.pc = s.x 30`), a Prog without `ok27` by
`ret27`. The `TEXT` and the first body Prog have no `ok27` (`ok27_spec`), so a run from the
entry starts with `X27At` from `x27At_of_eq` (`sim_entry`: the P0 state is the machine's); the
per-value theorems (`g7_obj_value`/`_term`, `g61_obj_value`/`_term`, the `g61_obj_*Panic`) and
`Whole.lean`'s `SimAt`/`SimAtW` carry it next to `ObjRel`, and the end-to-end statements are
unchanged. The recovery path is outside the model (no hook for `deferproc*`, `deferreturn`,
`gorecover`: such a call is `stuck`), and every modelled hook that returns (`liftContract`,
`morestackHook`, `wbHook`) sets `pc := s.x 30`, so the stronger `HookMap` is the arm64 `BL`/`RET`
ABI (STATUS Assumptions, "`HookMap` returns to `LR`"); `MorestackOK` already returns to `X30`
and is outside `obj_star` (the tail is no P0 Prog, and the body's first Prog has no `ok27`).
Witness `objAtomic_whole_witness`: `checkObj` accepts the whole of `sync/atomic.AddInt32` (its
LSE path and its LL/SC loop) with `ok27` exactly at the `CBNZ R27` after `STLXRW`, where `X27At`
holds iff the machine's `X27` is P0's. End to end the atomics still stop at genssa
(`LoweredAtomic*`, slice G61).

**Proof** (`GoFV/Proof/Obj/`):

- `Ex.lean`, `Bitfield.lean`: the smart constructors keep `eval`; the bitfield moves that the
  assembler encodes shifts, extracts and extensions as are P0's operations.
- `Insn.lean`, `Link.lean`, `Words.lean`: `symInsn_sound` (one decoded word); the linker
  model's relocated pairs and calls (`decode_adrp`, `decode_addLo`, `decode_ldstLo`,
  `decode_call`); `symWords_sound` (the words run as `symWords` says, one `MStep` each).
- `Prog.lean`: `progSym_sound`. A successful `progStep` of a Prog `progSym` describes performs
  no access in the nil page and ends where the symbolic effect and control say. There is one
  lemma per family (shifts, ADD-type, compares, `NEG`, bitfield extracts, moves, loads, stores,
  constants, addresses, pairs, `B.cond`, `JMP`, `CBZ`, `TBZ`, `CALL` and `CALL (Rn)`, `MUL`-type,
  `MADD`-type, `CLZ`-type, conditional selects, `LDAR`/`STLR`). `progSym_ctl`: calls come from
  `CALL`, register jumps from `RET`. `progSym_fault`: a step that faults in the nil page has a
  symbolic access there. String opcodes in the families are reduced by `decide` on concrete
  names; unifying a lemma against an unreduced `"CSET" == "CSET"` hung elaboration (normalise
  with `beq_self_eq_true` first).
- `Spec.lean`: the validator's checks as propositions (`checkObj_spec`, …).
- `Sim.lean`: `ObjRel f` (registers but `X27`/`X30` equal; `X30` and the PC through `f`, which
  maps a P0 Prog's address to `base +` its offset and the end to `base + endOff`; `SP`, `V`,
  flags, memory equal), `ObjEnv` (accepted, `Link.byId` with the validated frame, linked code),
  `obj_step` and `obj_star`. Every `PStar` run of P0 to `endP` is matched by `MStar` of the
  words, under the trusted `HookMap` (hooks treat related states alike) and `ICallOut` (at a
  `CALL (Rn)` the register holds a symbol's address, so the callee is outside the code; a run
  premise of `obj_star`; `iCallOut_of_none` for lists without it); STATUS Assumptions.
  `obj_panic`: a `PPanics` state is matched by machine steps to an `MPanics` state (a word that
  faults: `symInsn_fault`, `symWords_fault`; or a hook that panics, `HookPanicMap`).
- `Morestack.lean`: `symUntil_sound` (the chunks of `symUntil`, from `symWords_sound`),
  `stackCheck_run` (the stack check to its end when it passes, to the tail when it fails),
  `checkTail_spec`/`tailPlan_spec`/`checkObj_tail` (`Spec.lean`), the trusted contract
  `MorestackOK` of `runtime.morestack` at the tail's call (`tailCall`; unchanged by the `F`
  spills: it says nothing of the vector registers, and the tail reloads them from slots it keeps),
  and `more_loop`: round trips through the tail (the spills `storesMem_slot`, `TailSlot.store_eval`
  for a general register's low bytes or a vector register's `S`/`D` part, the hook, the reloads
  `reloadVal`, and `vreloadVal` for a vector register: the slot's bytes zero-extended to 128 bits)
  by induction on the guard, which the hook lowers, until the check passes (`MoreStep`: each
  reloaded general or vector register its own value or its reload).
- `MorestackHook.lean`: `morestackHook_ok`: the runtime model `morestackHook` (at
  `runtime.morestack`/`morestack_noctxt` of `RtInfo.hooks`) meets `MorestackOK` for a check of
  `stackguard0` when the stack can grow (`growBy > 0`, `stack.lo + StackGuard` below the limit).
- `Frame.lean`: `obj_entry` (from `MachEntry`, the stack check through the morestack path
  (`MoreRel`), then the frame `BodyEntry`) and `obj_exit` (the epilogue at a P0 `RET` pops the
  frame and returns through the saved `LR`).
- `G7.lean`: `g7_obj_value`, `g7_obj_term`. `g7_value`/`g7_term` with P0's return address
  `endP`, composed with `obj_star`, take a `runLoc` step to machine steps of the linked words.

Witnesses: `Witness/ObjFrame.lean` (`testInts`, framed, with the small stack check: `obj_entry`
and `obj_exit`; `objFrame_morestack_witness` enters with a failing check and a hook that clears
the guard), `Witness/ObjMoreF.lean` (`math.Tan`, whose tail spills `F0` with `FMOVD`:
`objMoreF_witness` enters with `F0 = π` and a failing check under a hook that clears the guard
and clobbers every vector register, and `F0` is `π` again at the body) and `Witness/ObjG7.lean`
(`(*A).g`: `g7_obj_value` on its nil check; `pallocSum.start`: `g7_obj_term` on `TBNZ [63]`).
Each decides `checkObj` and `linkCode` by compiled evaluation (pinned).

## 8. Plans: frame addresses (option 2), nonempty stack arguments, frame parameters, `MOVDnop`

Status after G15 (quick-v10). These blockers occur in many functions and are the sole reason in
few:

| Blocker | Occurs in | Sole reason in |
| --- | --: | --: |
| `stack argument` | 308 | 10 |
| `frame variable operand class` | 294 | 89 |
| `frame variable with an integer address` | 197 | 11 |
| `MOVDnop` | 750 | 85 |

**Why stack arguments and parameters wait for option 2 (semantics3 §4.3).**

- Phase 1 gives `outargs a` (the value `SP`) and `local a k` (every `PPARAM`/`PPARAMOUT`:
  `frameBlk`, `Tables.forgeable`) fixed addresses (`Blk.base?`, from `2^62`). Both are
  `Ptr.convertible`, so `OffPtr [off] SP` and `&param` become integer words (`ptrRes` →
  `Ptr.word`).
- `AddrAgree` pins every non-`temp` block to its Phase 1 address. That is what lets integer
  arithmetic on words (`lo_add`) relate register to register. The machine, however, puts these
  blocks at `SP + frameOff`, so no `MatchEnv` injects them there.
- Exempting them as `temp` is unsound while their words exist.
- The `outargs` window starts at offset 0, which overlaps the saved `LR` word that
  `StkAt`/`SepFrom` protect. Arguments start at offset 8: `ABIParam.offset` includes the fixed
  frame word.

**Option 2: design (revised after #607, design review of #553/#385).**

0. **What #607 changed, and a correction.** #607 made `Ptr.convertible` exactly the `ofAddr`
   round trip, `Ptr.word` `poison` outside the window, and `hasTy` at the word shapes
   `Ptr.held`. So convertibility is a consequence of the address assignment, not a second
   table. The first version of this design asked for frame blocks "anywhere, injective on the
   windows of live blocks". That cannot hold at `SP + frameOff`: Phase 1's windows are fixed
   (`Blk.window?`, frame blocks `2^24`), and pointer arithmetic on words needs the decoded
   windows to tile the address space (`Ptr.ofAddr_add_of_inWindow`, which `wordRes`, `offPtr`,
   the `OffPtr` folds and `AddrFold` rely on). Two frame variables 16 bytes apart cannot both own
   a `2^24` window. The parameter is therefore the assignment **and its decoder**: a frame block
   need not be decoded at all. The machine instance leaves the running activation's frame blocks
   undecoded, so they are held pointers like `temp`, and `ι` puts them at `SP + frameOff`. The
   windows stay fixed. Parametric windows, which would give frame variables machine integer
   addresses, are a later step (see 5).
1. **Parameter.** It is an instance-implicit class `Addrs` (`GoFV/SSA/Sem/Val.lean`), not an
   `Env` field. The readers (`Ptr.word`, `Val.retype`, `hasTy`, `decode`, `Mem.load`, `ptrRes`,
   …) are pure helpers that take no `Env`. A class keeps every statement's text: modules declare
   `variable [Addrs]`, and executables use `open scoped GoFV.SSA.Sem.Fixed`. There is no global
   instance, so a checker cannot depend on the assignment by accident: its build fails. Fields:
   - data: `baseOf : Blk → Option Nat`, `decode : BitVec 64 → Ptr`, `callerSP : Nat → BitVec 64`
     (`GetCallerSP`);
   - admissibility, proved once per instance:
     - `baseOf_nil`/`_heap`/`_global`/`_wbuf`: `nil ↦ 0`, `heap n ↦ (n+1)·2^40`, globals and
       the write-barrier buffer `none`;
     - `decode_low`: below `2^62` the decoder is #156's (nil page, heap);
     - `decode_high`: from `2^62` up it gives `outargs`/`local` blocks (no `temp`);
     - `decode_addr`: the decoded pointer has that address;
     - `decode_inWindow`: the decoded pointer is inside its window;
     - `decode_add`: arithmetic inside a decoded window is integer arithmetic.

   `Blk.base?`, `Ptr.addr?` and `Ptr.ofAddr` keep their names (they read the instance).
   `Ptr.convertible p := (p.addr?.map ofAddr) = some p`, as in #607, so `held`, `word`, `retype`
   and `asPtrWord` follow. `Addrs.fixed` (`Sem/Addrs.lean`) is #156's assignment.
   `Ptr.convertible_fixed` proves that at `Addrs.fixed` it is #607's bounds condition
   (`Ptr.fixedConvertible`), so every executable computes what it computes today.
2. **Statements that change.**
   - Every Phase 1/2/3 theorem gains `[Addrs]`. That is a generalisation with no new premise,
     because admissibility is in the class. `verifiedPipeline_refines`,
     `verifiedPipelineFull_refines` and `verified_mach` keep their text. Their old forms
     are the instances at `Addrs.fixed`: `verifiedPipeline_refines_fixed`,
     `verifiedPipelineFull_refines_fixed` and `verified_mach_fixed` state them without the
     parameter.
   - Internal lemmas that compute a fixed address become generic, or move to the
     fixed-instance witnesses:
     - `Ptr.word_outargs` → `Witness/ExpandCalls`;
     - the `ecsSlot` words in `ECStack`/`ECStackRes`;
     - `MoveLPairMem.ofAddr_adj`, `CSEMemChain.addr_ofAddr`, `NilLateLEval.ofAddr_nil`,
       `G7.ofAddr_off_nil`;
     - `Ptr.convertible_add` and `Ptr.convertible_eq_of_blk` now follow from `decode_add`.
   - Phase 3: `AddrAgree ι` keeps its text, and `Blk.base?` now reads the instance. Every
     non-`temp` block with an address sits at its address. A narrower version that pinned only
     decoded blocks would have strengthened `SubOK`, a premise of `verified_mach`, at
     `Addrs.fixed`, so it is not used. The machine instance satisfies `AddrAgree` because its
     bases for the running frame are `SP + frameOff` themselves.
   - **Correction:** the checkers do read the assignment. `RewriteCheck.termConst` evaluates
     term nodes on constants (`opVal` → `evalPure`: `OffPtr`, `Convert`, `EqPtr`, …, then
     `retype`), and the checker modules that call it (`RewriteCheck`, `LowerCheck`,
     `SccpCheck`, `ProveCheck`, … about 35) declare `variable [Addrs]`. The executables run them
     at `Addrs.fixed`, so their verdicts are today's. Relating a verdict at `Addrs.fixed` to
     the machine instance is item 6.
3. **Migration and staging.** The class sits at the root of the import graph, so one PR: the
   specialisation lemma, `SSA/Sem`, `Proof/PtrAddr`/`Retype`, the Phase 1 passes and rules,
   Phase 2, Phase 3 (`Rel`, `Value`, `Mem`, `G*`, `Obj`), then the witnesses and tests at
   `Addrs.fixed`. Splitting it would leave a main that does not build.
4. **The machine instance (follow-up slices, not this PR).** `Addrs.mach a base callerSP`
   for the running activation `a`:
   - its `local`/`temp`/`outargs` blocks at `base` (`SP + frameOff`, `outargs ↦ SP`);
   - the fixed region of `a` decoded as activation `a + 2^22`, which `Addrs.fixed` never decodes;
     those fictitious blocks keep the fixed bases;
   - every other block and address as in `Addrs.fixed`;
   - `callerSP a` genssa's `LoweredGetCallerSP`.

   It is admissible by the fixed proofs plus the renaming. Under it, `outargs a` and every
   `PPARAM`/`PPARAMOUT` `local a k` are held pointers, `ι` is free on them, and `Convert` of
   one is `poison`: option 1's guard, now semantic.

   **Done for activation 0's `local` blocks and its `outargs` block** (#672, `G49Mach.lean`;
   `outargs 0` with the lift to G60): `Addrs.atSPM base osp` puts activation 0's `local` blocks at
   `base k` and, with `osp = some o`, its `outargs` block at `o` (`Addrs.atSP base` without,
   `Addrs.atSPO base o` with), undecoded, decodes their fixed regions as activation
   `actM = 2^22` (`fixedOfAddr_act_lt`, `fixedOfAddr_out_lt`: `Ptr.fixedOfAddr` never decodes it),
   and is `Addrs.fixed` elsewhere; every class law is proven. With `base = baseSP g L sp` (each
   variable's frame operand from `sp`, the fixed base for one without an operand), `osp = sp`
   and the activation `envAtSP g L E` (`ιSP`: activation 0's `local` blocks at those bases,
   activation `actM`'s at theirs, the rest as `E.ι`; `envAtSPO`/`ιSPO` also the `outargs` block at
   `sp`), every `G28Env` at `Addrs.fixed` of activation 0 is a `G49Env` there (`g49Env_atSP`,
   `g49Env_atSPO`), and at `Addrs.atSPO` `SPInv`'s `outargs` part holds (`envAtSPO_out`). That is needed: at `Addrs.fixed` two `local` blocks of one
   activation are a multiple of `2^24` apart, so a function that accesses two at distinct
   operands has no `G49Env` (`g49Env_fixed_apart`; 18 end-to-end functions on quick-v10), and in
   G48's mode `SPInv` pins `SP` to `outargs 0`'s fixed base, so a function that accesses any
   `local` block has none (`g49Env_fixed_outSP`). `verified_mach_atSP` and `verified_mach_S_atSP`
   (§9) are the end-to-end statements there. `outargs a` of the other activations, the `temp` blocks and `callerSP` stay
   as in `Addrs.fixed`; item 7 (`SPAt`) extends the instance to them.
5. **Slices it unlocks, and coverage.** Phase 1/2 counts do not move: executables run
   `Addrs.fixed`, so sem-difftest and full-v9 are identical.
   - **G16+, stack arguments.**
     - `SP` as a no-code value outside the entry prefix.
     - SP-relative stores and pair stores at the checked outgoing offsets, and `outargs ↦ SP`
       with the poison prefix `[0, 8)` exempted from `SepFrom`.
     - `CallSpec` relating the stack arguments by `MemInj`; the callee's `decodeArgs` reads
       them there.
     - Expected: the 10 sole functions, and up to 308 together with other slices.
   - **Frame parameters and results.**
     - `frameVar?` for `.PARAM` operands, and `varWin` in the caller's argument area.
     - Disjointness from `PARAM` home slots, with a checked entry-store prefix materialising
       register parameters whose address is taken (`XChan.Send`: `MOVD R1, x+8(FP)`).
     - Expected: 89 sole, 294 occurs.
   - **Integer frame addresses** (11 sole, 197 occurs) stay partly blocked. Under `Addrs.mach`
     their `Convert` is `poison`, which covers a function whose integer is not branched on.
     Full coverage needs per-block windows in `Addrs`.
6. **Independence of the checkers from the assignment (`verifiedPipelineFull_indep`).** The
   executables compute `@verifiedPipelineFull Addrs.fixed`; `verified_mach` at the machine
   instance (item 4) needs the verdict at that instance. The goal is
   `@verifiedPipelineFull A env f s zv dcl = @verifiedPipelineFull Addrs.fixed env f s zv dcl`
   for every `A`. It is **not provable as the checkers stand**: on an integer word
   `x ≥ 2^62`, `Ptr.ofAddr x` depends on the instance (`decode_high` fixes only the block kind),
   so `wordRes x k` of `OffPtr [k] (Const64 [x])` can be `poison` under one instance and an
   integer under another, and `Convert`/`EqPtr` likewise. A rewrite on such a constant can be
   accepted under one instance and rejected under the other. Plan:
   1. **Guard (the one checker change).** In `termConst`, a 64-bit integer that an op reads as
      a pointer (`OffPtr`, `AddPtr`, `Convert`, `EqPtr`/`NeqPtr`, `IsNonNil`, the loads) is a
      constant only below `2^62`; above, `termConst` gives `none` and the checker treats the
      value symbolically. Constants that high come only from frame addresses, which no
      constant names (`termOp` excludes `SP` and `LocalAddr`), so Phase 1 and through-trim
      counts on the full corpus should not move; measure them.
   2. **Agreement lemma.** `LowVal v`: `v` holds no pointer into a frame block (`local`,
      `temp`, `outargs`), and its pointer-read integers are below `2^62`. On `LowVal`
      arguments, `evalPure`, `retype`, `hasTy`, `Ptr.word`, `Mem.load` agree between any `A`
      and `Addrs.fixed`, and the result is `LowVal`. Ingredients: the `baseOf_*` fields
      (nil, heap, globals, the write-barrier buffer) are the same in every instance,
      `decode_low`, and `Ptr.convertible_eq_fixed` (nil and heap pointers convert under every
      instance exactly when they do under `Addrs.fixed`; a heap pointer whose address would
      reach `2^62` converts under none, by `decode_high`).
   3. **Congruence.** `termConst_indep` by induction on the fuel, from 2: SSA constants
      (`Const*`, `ConstNil`, `ConstString`, `Addr` of a global) are `LowVal`. Then one
      `*_indep` lemma per checker module that reads the instance, by rewriting with
      `termConst_indep` and the agreement lemma at its other uses (first list them: a module
      whose only instance use is through `termConst` gets its lemma by `simp only`), then
      `verifiedPipelineFull_indep` by unfolding `runPasses`/`runPassesL` over the pass tables.
   4. **Use.** `verified_mach_ofFixed`: a verdict at `Addrs.fixed` (what `gofv-ssa-opt`
      computes) gives `verified_mach` at `Addrs.mach`.

   The alternative, checkers that evaluate at `@… Addrs.fixed` with the guard (so
   independence is `rfl` and the agreement lemma moves into each checker's soundness proof
   where its constant meets the semantics' value), is the fallback if step 3 needs more than a
   few modules with uses outside `termConst`.

   **Done (the fallback).** The frontier from `verifiedPipelineFull` into code that reads the
   assignment was 14 checker definitions (in `RewriteCheck`, Sccp's among them, and
   `LowerCheck`), most of them outside `termConst`, so step 3 was not a few `simp only`s. The
   checkers now evaluate at `Addrs.fixed` behind step 1's guard (`opGuard`), with step 2's
   agreement lemmas (`GoFV/SSA/Sem/Agree.lean`: `Val.lowB`, `Ptr.*_agree`, `Mem.load_agree`,
   `Val.retype_agree`, `evalPure_agree` over every op) used in their soundness proofs
   (`binds(L)_erase`/`sigma(L)_erase` take two instances; `opVal_agree`). `verifiedPipeline`,
   `verifiedPipelineFull` and every `checkG*` take no `Addrs` instance (`GoFVTest/AddrsFree.lean`),
   so independence holds by construction and step 4 needs no lemma: `verified_mach` at any
   instance takes the verdict `gofv-ssa-opt` computes. `gofv-ssa-opt --check --verified` counts
   on quick-v10 and full-v11 are identical to main's (full-v11 on main 06837b1e: 93,683 through
   `rewrite tern`, 84,123 through `trim`, the same verdict for every function).
7. **Slice plan: calls with stack arguments and stack results.** Rejected today by `callRegs`
   (`Gen/Check2.lean:104-112`: `stack argument`, `stack result`; G15's `callRegsZ` drops only
   zero-sized stack inputs). After G15: 308 functions, 10 where it is the only reason. Phase
   1: the caller stores each stack argument into its `outargs a` block at `ABIParam.offset`
   (which includes the fixed frame word, so `≥ 8`) through `OffPtr [o] SP`; the callee reads it
   there (`decodeArgs`, `Sem/Run.lean:613-625`), and `encodeResults` writes stack results there.
   - **Instance and environment.** At `Addrs.mach a E.sp …`, `Blk.base? (.outargs a) =
     some E.sp` and `outargs a` is undecoded (held, `Convert` of it `poison`). New
     `MatchEnv` invariant `SPAt E`: `E.ι (.outargs E.act) = some E.sp`, which with `AddrAgree`
     is the instance's base. `outargs a` is live with size `outargsSize`.
   - **`SP`.** A no-code value anywhere, holding `.ptr ⟨outargs a, 0⟩` with no X register
     (the `SP after the entry values` slice, G24, which needs no option 2).
   - **SP-based accesses.** `MOVDstore [o] SP x` (and the narrow, pair and float forms)
     store through `⟨outargs a, o⟩`; the machine address `m.sp + o = E.sp + o` by `FrameRel` and
     `SPAt`. G3's store lemma with this base, as G6 does for frame variables. Loads of stack
     results after the call likewise. The checker requires `8 ≤ o` and
     `o + size ≤ outargsSize`.
   - **The `[0, 8)` prefix.** The `outargs` block starts at `SP`, where the saved `LR` lies
     (`StkAt`), so `SepFrom` fails as stated (`Proof/Gen/G1.lean:62-64` excludes whole
     blocks). Change `SepFrom` to exempt the bytes `[0, 8)` of `outargs E.act`, with the
     invariant `OutPoison`: those bytes are `poison` in Phase 1 (`frameAllocs` allocates
     `outargs` as poison; every store to it is at `o ≥ 8`, by the check above and by
     `ABIParam.offset ≥ 8` for the callee's `encodeResults`). `BytesRel` relates poison to any
     machine byte, so `MemInj` holds with the saved `LR` there.
     **Done (stage A):** `Mem.write`/`Mem.canWrite` require `Blk.writableFrom ≤ off` for a
     nonempty access (`writableFrom (.outargs _) = 8`, else 0; `GoFV/SSA/Sem/Mem.lean`, with the
     Go sources in `docs/plans/semantics.md` §3.4's access rule), so no Phase 1 write reaches
     `outargs[0, 8)`. `SepFrom` and the trusted call premises (`CallSpec`, `CallPanicOK`,
     `ICallPanicOK`) are unchanged: their full-block separation still holds in every existing
     slice (no `outargs` at `SP`). The weaker form is `SepFromW` (`Proof/Gen/G1.lean`): a live
     block's byte at an address of `P` lies below `writableFrom` and is `poison` (the poison
     invariant folded into the separation, since contracts and the entry memory are arbitrary
     and a global `OutPoison` is not derivable). `SepFrom.w`, `SepFromW.write` (Phase 1 writes
     keep it, from `write_back`) and `memInj_of_sepW` (a machine memory changed only at `P`
     keeps `MemInj`: spills, `Proof/Gen/Stack.lean`) are ready for the slice, whose functions
     use a `SepFromW` invariant and a separate contract `CallOKS` for all their calls (old
     `CallOK` needs the full `SepFrom`, false once `outargs` sits at `SP`).
     **Finding (stage B, G48b):** every existing slice (G1–G57) was unusable at `Addrs.mach` for
     a function with nonempty `outargs` until G48b: `CoreInv.mem` held
     `SepFrom E.ι (StkAt E) mm`, and `StkAt E` contains the saved-`LR` word `[SP, SP + 8)`, which
     is `outargs act [0, 8)`, a byte of a live block; so `G3Inv` was false and no `gN_value`
     applied. **Now fixed (G48b):**
     `MatchEnv.outSP : Bool := false`; `SepAt w` (`false` ↦ `SepFrom`, `true` ↦ `SepFromW`,
     `Proof/Gen/G1.lean`); `CoreInv`/`G3Inv` take a trailing mode `(w : Bool := false)`, so every
     existing statement that names them without a mode means today's invariant. The value steps
     and the slices' layers are generalised over the mode `osp` (stores keep `SepAt` by
     `SepAt.write`/`not_mem` from `write_back`/`write_wf`: a store's bytes lie at or above
     `writableFrom`; spills by `memInj_of_sepW`; `MemSub` by `sepFrom_sub`), with the calls by
     the selectors `CallOKAt`/`CallOKZAt`/`ICallOKAt`/`WbOKAt`/`MemEqOKAt` of mode `osp`
     (`false`: the existing contracts verbatim; `true`: the new trusted `CallOKS` family, STATUS
     Assumptions). G53, G54 (`G54.lean`, `G54a.lean`, `G54b.lean`: `g54_value` and the loop
     steps `g54a_zero`/`g54b_move`), G55 (`G55.lean`, `G55a.lean`, `G55b.lean`), G56 (`G56.lean`,
     with `g56_fconst`) and G57 (`G57.lean`, `G57a.lean`, `G57b.lean`, with the stores
     `g57_stpw`/`g57_fstore`/`g57_fstp`) are generalised over the mode; at `osp = false` every
     statement is the one before G48b (the statement dump in the G48b PR), so the composition
     (`Obj/G56.lean`, `EndToEnd`, `EndToEndFixed`) is unchanged.
     `G53S.lean`: `g53_valueS`/`g53_initMemS`/
     `g53_termS` (and `L` forms) in the mode `E.outSP`, keeping `SPInv` (`SP`'s block at `SP`
     under `ι`, the Go register `SP` related to `SP`) by `spInv_step` under the static premise
     `SPHomes`; the panic theorems `g53_nilPanic`/`g53_boundsPanic` already take any mode. Witness
     `Witness/OutSP.lean`.
   - **Layout check.** `[SP + 8, SP + outargsSize)` is disjoint from the spill slots and the
     `AUTO` windows (`frameOff .AUTO`), from `Link.autosize`/`extrasize`.
   - **Call contract.** `CallSpec` (`Proof/Gen/G2.lean:90-100`) keeps its text: the callee's
     stack arguments are bytes of `mm` that `MemInj` already relates to `m.mem` at
     `E.sp + offset`, and its conclusion `MemInj ι' mm' m'.mem` covers stack results. The
     trusted premise gains a variant `CallOKS` (as G15's `CallOKZ`) over `callRegsS`, which
     accepts stack inputs and outputs: the hook reads stack arguments at `m.sp + offset` and
     writes stack results there, as `decodeArgs`/`encodeResults` do at `outargs a`.
   - **Theorems.** `gN_value`/`gN_term`/`gN_nilPanic`/`gN_boundsPanic` over `checkGN` with
     `CallOKS` and `SPAt`, generic in `[Addrs]` with the premise
     `Blk.base? (.outargs E.act) = some E.sp.toNat`; witness at `Addrs.mach` once it exists,
     else on a function whose stack arguments are written and read at the decoded addresses
     of `Addrs.fixed`.
   - **Done (G48, §4).** `checkG48` is G57 (G53–G57 mode-generalized by G48b) with the
     static calls of `callRegsS` and the accesses off `SP` at `[8, outargsSize)`; gen-check 7,595
     (+217 over G57), and no store on quick-v10 reaches `outargs[0, 8)` (664 stores off `SP`
     without an aux in 298 functions, the lowest at offset 8). Differences from this plan: `SPAt`
     is G48b's
     `SPInv` (with `hosp : E.outSP = true`), not a `Blk.base?` premise (`AddrAgree` gives the
     base; the witness is at `Addrs.fixed` with `SP` at `outargs 0`'s address `2^62`); the
     callee contract is a separate trusted `CallOKStk` (`CallAtM true` over `callRegsS`), the
     `CallOKS` family keeping `callRegs`; the layout check is not in the checker: the
     separation `SepFromW` of the activation (`G3Inv … true`) already keeps every live block,
     the `outargs` block included, off the spill slots, and `sepW_out` places each store; two
     static checks are new, `spBase48` (an access's base homed in the Go register `SP`) and
     `spHomes48` (`SPHomes`); the theorems are `g48_*` only (G53S keeps the older slices in the
     mode), and `g48_value`/`g48_initMem` take a lowered function. Not covered: interface and
     closure calls with stack arguments (`callRegs`), `FSTPQ`/`LDP`/`MOVDaddr` off `SP`.
8. **Slice plan: frame parameters and results (`.PARAM` operands).** Rejected today by
   `frameVar?` (`Gen/Check6.lean:57-68`: `frame variable operand class`; after G23 95
   functions where it is the only reason, 294 where it occurs). Phase 1 gives every
   `PPARAM`/`PPARAMOUT` a `local a k` block (`Tables.forgeable`, `frameBlk`), initialised from
   the input argument (`frameAllocs`). Genssa addresses them at the caller's argument area,
   `SP + autosize + 8 + off` (`frameOff .PARAM`, `Proof/Gen/Progs2.lean:21-24`).
   - **Instance.** At `Addrs.mach`, `Blk.base? (.local a k) = some (E.sp + autosize + 8 + off_k)`
     for each parameter `k`, undecoded. `MatchEnv` invariant `ParamAt E`: `E.ι` agrees.
   - **Checker.** `frameVar?` accepts `(.PARAM, off)` for a parameter without `addrconv` (one
     whose address becomes an integer stays blocked, as item 5's integer frame addresses);
     `varWin` returns `(off, off + sz)` for `.PARAM` too, inside the function's
     own argument area (`[0, argsize)` from its ABI) and disjoint from every home slot,
     including the `.PARAM` homes `checkFrame` already accepts (`checkVars` compares only
     with `.AUTO` homes today).
   - **Entry.** Stack-assigned parameters are already at their address when the function is
     entered: the caller stored them (the stack part of `CallOKS`, from the callee's side).
     A register parameter whose address is taken is materialised by genssa's entry stores
     (`MOVD R1, x+8(FP)`, `XChan.Send`). The checker requires a prefix of the entry block that
     stores each such parameter's register to its window before any other access to it.
     `EntryMatch` (`Proof/Obj/Whole.lean:613-619`) gains `ParamMem`: `MemInj` over the
     parameter blocks, for the stack-assigned ones at entry, for the register ones after the
     prefix; the prefix lemma turns the second into the first.
   - **Results.** `PPARAMOUT` blocks are read by `MakeResult` into the result registers
     (register results) or written to the caller's `outargs` (stack results, item 7's
     `encodeResults`); a result variable accessed through its `.PARAM` operand is covered by
     the same window, its `MakeResult` load by G6's load lemma at that base.
   - **Theorems.** As item 7, with `ParamAt` and `ParamMem` as premises at entry, discharged
     at `Addrs.mach` by `verified_mach`'s composition; witness on `XChan.Send`.
   - **Done in G49 (§4)**, the slice part. Differences from this plan: `ParamAt` is `VarsAt49`
     (also covering the `PAUTO`s with an integer address, at their `NAME_AUTO` operand), an
     activation premise of `G49Env`; `checkVars49` keeps windows of one operand class apart
     from that class's home slots, with no checked entry-store prefix; the witness is
     `runtime.getm`'s ABI0 wrapper (a stack result), at `Addrs.fixed`. **Composed in §9** with
     the first option: `EntryMatch` excludes the windows of the accessed register parameters
     (`pendWins`) until the entry stores, which `sim_entryStores` runs; the entry-store prefix
     check is `entryStoresOK` (`GoFV/Gen/Entry49.lean`, a premise of `verified_mach`), not a part
     of `checkVars49`; `ParamMem` is not needed (§9 records why).

**Plan for `MOVDnop`, which needs no option 2.** G20 and G21 (§4) are the first step: their table
`uAt` has an entry only directly after a narrow load, so no slice has to say which registers it
keeps (1,300 of 1,520 `MOVDnop`s; 25 `MOVDreg`s in 14 functions). The table below and the
register-frame lemmas carry entries across values that keep the register, for the rest. Measured
on quick-v10 after G21, that would add only 3 functions that have no other blocker (gaps
`LDP`+`Select`s, a `MOVDload`, a `Copy`) and 13 that have only `MOVDreg`: the other `MOVDnop`s sit
in functions with further blockers.

**Deferred** (after G22, #553): carrying the table across values. It was worth about 16 functions
(the 3 and 13 above) and needs a register-frame conclusion in every slice's value lemma, so the
slices that remove other blockers (§4's list) come first; this plan is kept for when they have
freed more of the 220 `MOVDnop`s. After G23, 46 functions have `upper bits unknown` as their only
reason; in 24 of them every such `MOVDnop`/`MOVDreg` follows its load in the same block with only
narrow loads, `MOVDnop`s and `MOVDreg`s between (each writes at most its own register, which
`g3_loadW`, `g14_idxW`, `g20_nop` and `op_reg2W` already state), so a table of several entries
carried across just those values would take them; the other 22 need the cross-block table. G29
(§4) is that in-block table; it took 29 functions, and 46 still have `upper bits unknown` as
their only reason. G31 (§4) carries it across G1's and G3's ops (`XW`) and blocks (`uIn`, `uFlow`);
it took 25 functions, and 26 still have `upper bits unknown` as their only reason. A wider keep set
(frames for spills and reloads, `LDP`/`Select`, bounds panics, `MOVBreg`) measured 38 of the 46.
G34 (§4) widens it to G3's, G16's, G23's, G25's, G32's and G33's single-register ops, spills,
reloads and `MOVDaddr`; it took 13, and 16 remain. G35 (§4) adds `LDP` and its selects to the
keep set and gives loads of frame variables an entry; it took 13, and 3 remain.

- **The obstacle.** `MOVDnop x` emits no code. `runLoc` gives it the full 64-bit register:
  `movdLoc` takes the zero or sign extension of `x`'s low bits, as `LocCtx.signOf` decides from
  `x`'s producer. `LocMatch` only relates the low `w` bits of a narrow integer.
- **The upper-bit table.** Add a dataflow table beside the class table: `UTab`, per block, each
  register ↦ `zext w | sext w | ⊤`. Its `uStep` follows `kStep`:
  - narrow loads `MOV{B,H,W}Uload` and their idx forms give `zext`, and `MOV{B,H,W}load` give
    `sext`; the extensions `MOV*reg` likewise;
  - `LoadReg` of a narrow type gives `sext`/`zext` by its signedness (`loadByType`);
  - 32-bit ops (`*W`) give `zext 32` only for 32-bit results;
  - `CSET` and the boolean producers give `zext 1`;
  - `Copy` and `MOVDreg` copy their argument's entry;
  - calls, `SelectN` of calls, and every other writer give `⊤`;
  - a value that writes no register keeps the table.

  The meet at block entries goes as `kFlow`. `checkU` requires, at each `MOVDnop`/`MOVDreg x`,
  that `x`'s register entry is the extension `signOf x` names at `x`'s width.
- **The invariant.** `UInv E K U s m`: every register `r ≠ ZERO` with `U r = zext w`/`sext w` and
  `s.regs[r] = .int w x` (`w < 64`) has `m.x r = x.zeroExtend 64`/`x.signExtend 64`. It becomes
  part of `G3Inv`.
- **Register-frame lemmas.** Each value lemma of G1–G15 gains the conclusion that every X
  register other than the value's home register(s) and the op's clobbers is unchanged:
  `∀ k, k ∉ writes v → m'.x k = m.x k`. For the code-emitting ones this follows from the Prog
  lemmas: `progStep_*` writes only `wX kd`. For calls, `CallSpec` only keeps `R28`/`R29`, and
  `UInv` is reset to `⊤` there. The no-code values keep `m`. Every slice's `vkN_step` then
  carries `UInv` across: unchanged registers keep it, and the written register gets the entry
  its producer's lemma establishes. The narrow-load lemmas (`lo_loadN`) already compute the
  exact zero/sign extension, and `op_reg2`'s `val` is that word.
- **The slice.** `MOVDnop x` is `stepLoc` = `movdLoc`, with no Prog. Its proof is
  `UInv` → `ValRel` of the 64-bit result (`lo_movd`, `g20_nop` in G20). Expected: 85 sole, 750
  occurs; G20 accepts 4,328 functions with its narrower table. `MOVDreg` (310 occurs) is the same
  with a `MOVD` Prog (`g21_mov` in G21, 4,342 functions).

**Other slices that need no option 2.** Each is listed with the functions it occurs in (sole
reason in parentheses):

- register-index stores, `MOVDstoreidx8`/`MOVBstoreidx`: 245/187 (39/23); G14's addresses with
  G3's stores; done in G18 (§4);
- `GetG`: 430 (89); `R28` = `E.g`, already in `FrameRel`; done in G17 (§4);
- `ADDshiftLL`: 678 (57); `lo_add` with `shifted`; done in G16 (§4);
- bounds panics `LoweredPanicBounds*`: 616 (40+); a `CALL runtime.panicBounds*` hook that
  panics, as `g7_nilPanic`; done in G19 (§4), but for #541's constant indices outside `0..31`;
- `TSTconst`, `CSEL`: 110 (53), 324+285 (41+55) after G23; flags producers and readers as G1's
  `CMP`/`B<cond>`;
- `Equal`/`NotEqual`/`Less*`/`Greater*`: 332/294 (95/44); `CSET`; done in G23 (§4);
- `LDP`/`STP` of globals: 347 (124); G4's pair accesses at G3's global address; done in G22 (§4).

## 9. Whole functions and the end-to-end statement

**Whole functions** (`GoFV/Proof/Obj/Whole.lean`). The value and terminator theorems of the latest
slice, composed with `obj_star` (`g62_obj_value`/`g62_obj_term`, `GoFV/Proof/Obj/G62.lean`), are
chained along a run of `runLoc`'s body. The invariant `SimAt` before value `i` of block `b`: a P0
state `m` `LocMatch`ed to `runLoc`'s state under an activation `E` extending the entry's `E0`
(`G49Env`: `G28Env` and `VarsAt49`, kept along `Extends` by `VarsAt49.extend`; `G3Inv` at the
class map `kAt`, G49's upper-bit table (G35's) `UOKL m (uL35 lc (uIn35 lc b)
blk i)`: `g61_value` carries it from value to value, `g61_term` hands the successor's start
`uIn35 lc e.b` on, `uEdgesOK35`), and `ObjRel`-related to the machine state; in a leaf
(`checkObj`'s `leaf`, `leafOf`: no `CALL`), `m`'s `X30` is still the caller's return address
`E0.lr`, which is no P0 address and not `endP`; at a clean position `runLoc`'s state holds the
initial memory (`MemAt`: in a lowered function under `cleanOK`, `cleanAt → MemInit`). The
composition is over a mode `osp` (`SimAt … osp`, `RunPreM osp`, `RunPanicPreM osp`): `SimAt`
carries `G3Inv` at the mode (`SepAt`: `SepFromW` at `true`) and, at the mode `true` in a lowered
function, `SPInv` (`outargs` at `SP`, the Go register `SP` holding `SP`), which `g61_value` keeps.
The mode is `true` for a function that needs G48's mode (`hn48 : needs48 lc = true → osp = true`;
then `hosp : osp = true → E0.outSP = true`, the activation's `outargs` block at `SP`, the saved-`LR`
word its first, `poison` word); a function with no arm64 op runs G33's mode-generic lemmas in
either. `verified_mach` is the mode `false` (`needs48 lc = false`), `verified_mach_S` the mode
`true`, both `verified_mach_M`.

- **Entry** (`sim_entry`). From `MachEntry s0`, `obj_entry` runs the stack check, looping through
  the morestack tail while it fails (`more_loop`, under the trusted `MorestackOK` and the caller's
  `TailSep`), to a state `s0'` (`MoreRel`), and builds the frame (`BodyEntry`). On the morestack
  path `s0'` is `s0` but for the reloaded registers (a narrow reload zero- or sign-extends the
  slot's low bytes: `ValRel` of a narrow integer reads only them, a boolean is 0/1 either way,
  `valRel_reloadVal`; a reloaded vector register is the slot's `S`/`D` bytes zero-extended,
  `vreloadVal`, and `FValRel` reads only the value's low `w` bits, `fvalRel_vreloadVal`), the
  other registers but `R26`, `R28`–`R30`, the vector registers not reloaded, the slots and the
  guard word; the caller-side premise `MoreEntry` (every live register but `R26` reloaded from a
  slot it fits, `ValFits`, a live vector register from a slot of its `F` register,
  `reloadOf sl true`; the live blocks apart from the slots and the guard word) carries
  `EntryMatch E0 g W sI s0` to `s0'` (`EntryMatch.more`, `EntryEnv.more`; the stack clause
  survives since a function with a slot at the entry has no tail spill, `argsOK`, and the guard
  word is among `g`'s first 32 bytes, `checkObj_gOff`).
  The P0 state is the machine's with the PC of the entry block's value
  `k`, the first after the entry values and the `Arg`s (`InitMem`, `SP`, `ArgIntReg`,
  `ArgFloatReg`, G62's `Arg`, which emit
  nothing and are not `g*_value`'s). It is related to the state `sI` after them with its memory
  replaced (`SimAtW`, below): `EntryMatch E0 g W sI s0'` and `EntryEnv E0 … s0'` give the argument
  registers, no flags, the slots (the `Arg`s', at their frame operands: the caller's bytes at
  `8 + off` above the entry `SP`, outside `W` and above the saved words), the memory injected into
  a memory that is the machine's but for
  the bytes `W` (the prologue writes only the saved `LR`/`FP` words, outside the live blocks by
  `G3Inv`'s `SepAt`: in G48's mode the saved `LR` word is the `outargs` block's first, `poison`
  byte, `memInj_of_sepW`; the replaced memory takes the machine's bytes there), the frame;
  `SPInv` of `sI` (`hspI`; the entry stores keep it, `spInv_step`, as stores to `Blk.local`
  blocks off no `SP` home, `spHomes48_spec`);
  `uL35 lc [] … k = []` (no upper-bit fact on entry; the entry
  block's start `uIn35` is empty, `checkG62L_uIn_entry`). The premise
  `ObjEnv.map … (E0.pcOf entry k) = base + offs[0]` places value `k` at the body's start (the
  Progs before it are pseudo-ops).
- **Entry stores** (`sim_entryStores`, `GoFV/Proof/Obj/Entry49.lean`; `docs/plans/proofs3.md` §8
  item 8). Phase 1 initialises the `Blk.local` block of every `PPARAM` with its argument's image
  (`frameAllocs`), and `VarsAt49` places the block of an accessed one at its `NAME_PARAM` operand,
  in the caller's spill area: for a register-assigned parameter that area holds garbage until
  genssa's entry store (`MOVD R1, x+8(FP)`, `STP (R0, R1), x+0(FP)`), so `MemInj` at the entry
  would make `EntryMatch` unsatisfiable for such functions. `EntryMatch E0 W` relates `sI`'s
  memory to a memory `M` that is `s0`'s but for the bytes `W`; the end-to-end statement takes
  `W = InWins L E0.sp (pendWins lc g)`, the windows of the register-assigned parameters in
  `Blk.local` blocks the function accesses (`GoFV/Gen/Entry49.lean`). The entry stores
  (`entryStore?`: a store of `MOV{D,W,H,B}store` or `STP` to a frame variable at its `NAME_PARAM`
  operand that `vkind51` rejects, so G49's frame-variable path, no op of G52–G59's groups, `vkind60_ok49`;
  `entryStores lc g k`, those at the
  head of the entry block from value `k`) are run against the relaxed relation: `SimAtW` is
  `SimAt` with the P0 state's memory replaced by one agreeing with it outside `W`; an entry store's
  Prog writes its window alike in both memories (`g61L_entryStore`: `entryStore?_spec`,
  `op_mem2W`, `g49_storeW`, `g49_stpW`, `writeMem_agree`/`writeMem_agree2`), so after it the
  memories agree outside `W` minus that window (`sim_entryStore`); no entry store panics (it has a
  symbol, `stepLoc_mem_panic_aux`); the run continues alike (`runFromLoc_val`). The checked
  boolean `entryStoresOK lc g k` (a premise of `verified_mach` as `retRegsOK` is; the driver
  checks it at `k = entryLen`) says the entry stores cover every byte of every pending window
  (`entryStoresOK_cover`), so after them nothing is left out and `SimAtW` is `SimAt`
  (`SimAtW.simAt`): `LocMatch`, the slice lemmas and `SimAt` are unchanged. On quick-v10, 100
  functions' entry blocks store a `PPARAM` (`STP` 109 times, `MOVDstore` 43, narrower stores 14,
  float stores 4); in 50 the stores follow the entry values directly, in the other 50 spills
  (`StoreReg`) or `SP`/`InitMem` come first.
  The choice (option (a)) over (b), a `ParamMem` clause in `SimAt` saying which parameter windows
  are still pending: (b) weakens `LocMatch` (or adds a side condition) at every value, terminator
  and panic lemma of every slice, all of which would have to carry and discharge it; (a) keeps the
  relaxation inside the entry (`EntryMatch`, `SimAtW`, the entry stores) and needs only the entry
  stores' Progs, at the cost of a check on their position (`entryStoresOK`), which rejects
  functions whose entry stores are not at the head of the entry block.
- **Values, terminators** (`sim_value`, `sim_goto`, `sim_values`): `g61_obj_value`/`g61_obj_term`
  under the per-step premises `RunPre`, stated at the states `runLoc` reaches (`LReach`) from
  `(entry, k, sI)`: `G54Pre`, that is `G53Pre` and G54's `Pre54a` (a `LoweredZeroLoop` writes
  valid bytes) and `Pre54b` (a `LoweredMoveLoop` reads and writes valid bytes, its two ranges the
  same or disjoint); `G53Pre`: `G51Pre` (G49 and G52 adding none) and G53's `Pre53a` (the same of
  `LoweredMove`); `G51Pre`: `G50Pre`, `G46Pre` (`G45Pre`: `G44Pre`, that is `G14Pre`, an acquire
  load's valid bytes `LdarPre`, `CmpPre`, the first argument of a G41 compare no pointer without an
  integer form,
  and `FLoadPre`, a float load's valid bytes at no bare pointer; and `FIdxPre`, the same of a
  float register-index load; and `FArithPre`, no `FADD`/`FMUL` of an `FNaNSwap` pair and no
  `FMADD`/`FNMSUB` multiplying an `FSameNaN` pair) and G50's `PairPre50` (a pair load reads valid
  bytes at both addresses, no pointer into a V register) and G51's `Pre51a` (the compared
  arguments of `CMN` and `CMPshiftRA` no pointer without an integer form), `G1TermPre`,
  no entry value (`entryOp24`) but an `InitMem` in a lowered function, `GetGOK`, and the callee
  contracts of the mode `osp` (`CallOKAt`, `CallOKZAt`, `ICallOKAt`, `WbOKAt`, `MemEqOKAt`:
  `CallOK` … at `false`, `RunPre`; the `CallOKS` family with `SepFromW` and G48's `CallOKStk`, a
  static call with stack arguments or results, at `true`, `RunPreS`), `CloOK` at every
  `LocMatch`ed machine state. `checkG61L_cx` gives the context of both modes (lowered, and G26's functions with
  no arm64 op). `checkG61L` accepted such an `InitMem` only at a clean position of a function
  whose clean blocks are closed backwards (`g61L_clean`: `vkind60_initMem`, `vkind59_initMem`, `vkind58_initMem`, `vkind48_initMem`,
  `vkind57_initMem`, `vkind55_initMem`,
  `vkind54_initMem`, `vkind53_initMem`,
  `vkind52_initMem`, `vkind49_initMem`, `vkind51_initMem`,
  `vkind50_initMem`,
  `vkind47_initMem`, `vkind46_initMem`,
  `vkind45_initMem`, `vkind44_initMem`, `vkind43_initMem`, `initMemClean_spec`),
  where it runs no code and changes nothing from a state holding the initial memory (`MemInit`,
  `g61L_initMem`). `SimAt` carries `MemAt`: from `runLoc`'s first state (`locInit` holds `MemInit`
  by `rfl`) through the entry values before `k` (`memAt_enter`: a clean `k` means they keep the
  memory, `memInit_enterKeep`), along a value (`memInit_clean_step`) and along an edge
  (`memInit_clean_term`, `cleanAt_zero`: `SimAt`'s `b ∈ blocks` gives `cleanOK_edge`), so
  `obj_whole_ret` and `obj_whole_panic` take `MemInit` of the first state only.
- **Return** (`sim_ret`): only a `Ret` block returns (`stepTermL_ret_kind`); its terminator is a
  P0 `RET` after no-ops (`termG3_ret`); the no-ops run (`pstar_oneAt`, `obj_star`), then the
  epilogue (`obj_exit`) returns to `s0.x 30`: through the saved `LR` in a framed function
  (`FrameRel`: `m.word E.sp = E.lr`), through `X30` in a frameless one (`FrameRel`: `X30 = E.lr`,
  outside the P0 addresses so `ObjRel` maps it to itself). A framed leaf returns through `X30`
  too (and recomputes `R29 = SP + autosize - 8`, the caller's `SP - 8`, `EntryEnv.fp0`):
  `SimAt`'s leaf clause holds at the entry (the prologue keeps `X30`) and every P0 run of a value
  or terminator keeps it (`obj_star_leaf`, `GoFV/Proof/Obj/Sim.lean`): from a state at a Prog with
  `X30` outside the Progs and the end, every state of the run is at a Prog (`ObjInv`: a symbol is
  reached only with a P0 return address in `X30`), so no hook runs, and each step keeps `X30`
  (`leaf_step_x30`: the skips do not touch it, P0's `RET` does not step, a compared Prog's effect
  does not write it, `sameEffect`, and its control is no call, `progSym_ctl` with `leafOf`, nor a
  register jump, which no `CtlMatch` admits).
  The results (`ret_results`, `GoFV/Proof/Obj/Results.lean`): `retRegsOK` (`GoFV/Gen/Results.lean`)
  asks of every `Ret` block a `MakeResult` control with one tuple component per argument, the last
  the memory, each result homed in its ABI register (`ownOutRegs`) at a class no wider than the
  register's at the `Ret`, a result in an `F` register (`F0`–`F15`, Go registers 31–46) at a float
  shape (`fTy`) read at a float shape of its class; `runLoc` retypes the arguments to the
  components (`Val.retypeL` in the lowered mode, `Val.retype` in Phase 1's), which keeps the
  register relation (`valRel_retypeL_le`, `lmode_valRel_le`) and, for a result in `F0`–`F15`, the
  V register relation (`FValRel`: `fvalRel_retypeL`, `lmode_fvalRel`; `ResultRel` relates it to
  the V register). `expand calls` types the components as the results'
  register types (`abi.RegisterTypes`), e.g. a `uintptr` itab word for an `*itab` result. A
  result the ABI puts on the stack, or a zero-sized one, has no register (`ownOutRegs` skips it)
  and no `MakeResult` argument: `expand calls` (`rewriteFuncResults`) stores it to its
  `PPARAMOUT` variable, whose bytes `goResults` reads from the memory at the return; that memory
  is `mm`, which `ResultRel` injects into the machine's.
- **Run** (`sim_from_ret`, induction on the fuel), **function** (`obj_whole_ret`): `runLoopLoc`
  from `runLoc`'s state at the entry block, the first `k` values run to `sI` (`runLoopLoc_entry`),
  the entry stores to the first related state (`sim_entryStores`);
  a run that returns `(rs, mm)` is matched by `runMach` returning to `s0.x 30` (`mstar_returned`)
  in a state `t'` with `MachRet s0 t'` and `ResultRel E outs rs mm t'` (`rs` in the result
  registers: `R0`–`R15` related to the X registers, `F0`–`F15` to the V registers; `mm` injected).
- **Panics** (`sim_valuePanic`, `sim_from_panic`, `obj_whole_panic`): a step that panics is a nil
  check (`g61_obj_nilPanic`: the `MOVB` faults in the nil page), a load or store that faults
  (`g61_obj_memPanic`, `GoFV/Proof/Obj/MemPanic.lean`: `MOV{D,W,WU,H,HU,B,BU}load`, `LDP`,
  `MOV{D,W,H,B}store` and `STP`, `memFaultOp`; `nilFaults` found a nil base and an address in the
  nil page, so the access has no symbol, hence no G49 frame-variable access, `frameVar49?_none`,
  `vkind49_eq51` (and no op of G61's group A or G52–G59's groups: `vkind61_eq60`, `vkind60_eq48`,
  `vkind48_ok`, `vkind56_eq55`,
  `vkind55_eq54`, `vkind54_eq53`, `vkind53_eq52`, `vkind52_eq49`; an access off `SP`, G48's
  `kind48`, does not fault: it takes G48's mode (`take48`), where `SPInv` relates its base to
  `SP`, above the nil page,
  `sp_base48`), its base register holds the machine word 0 and
  `X[n] + off` is in the nil page, `nil_fault_page`; no premise), an acquire load that faults
  (`g61_obj_ldarPanic`: `LDAR`, `LDARW`, `LDARB`, `ldar?`; its address, argument 0 at offset 0, is
  nil, `stepLoc_ldar_panic`, so `LDAR* (Rn)` faults at address 0, `progStep_ldar_nil`; no
  premise), an atomic of G61's group A that faults (`g61_obj_atomPanic`,
  `GoFV/Proof/Obj/AtomPanic.lean`, `atom61?`: the generic atomic never panics,
  `atomicRoot_ne_panic`, so the panic is `nilFaults`' on its pointer, argument 0 with no symbol,
  `nilFaults_atom61`, `stepLoc_atom61_panic`; what `vkind61` accepts of it is `vkind61a`'s,
  `vkind61_atom`, and its Progs reach their first access, `LDAXR*`, the LSE instruction, or it
  after `MVN Rv, R27`/`MOV Rold, R27`, which faults at address 0, `atom_nil_run`; no premise), a
  bounds check
  (`g61_obj_boundsPanic`, under the trusted `BoundsOK`: `runtime.panicBounds` reports the same
  failure, `BoundsAgree`), a static call whose
  callee panics (`g61_obj_callPanic`, `GoFV/Proof/Obj/CallPanic.lean`, under the trusted
  `CallPanicOKAt osp`: `CallPanicOK`, or at G48's mode `CallPanicOKS` with `SepFromW` and the
  ABI registers of `callRegsZ` or `callRegsS`, a call with stack arguments, G48's `callKind48`: the
  callee's hook panics alike from every state with the call's arguments in their
  registers and the memory injected), or an interface or closure call whose callee panics
  (`g61_obj_icallPanic`, under the trusted `ICallPanicOKAt osp`, `ICallPanicOK` or
  `ICallPanicOKS`: the hook at the code pointer in `Rn`
  panics alike; `vkind28` of such a call is `vkind10`'s `icallKind`, `vkind28_icall`; `vkind54`
  of an acquire load or a call is `vkind49`'s, `vkind56_eq49`, and what
  `vkind49` accepts of it `vkind51` accepts, `vkind49_ok51` (no G49
  frame-variable access); `vkind51` of
  a load, store or call is `vkind47`'s, `vkind51_eq50` (no G51 op), `vkind50_eq47` (no G50 pair
  load or select), and `vkind47`
  of a load or store is `vkind28`'s, `vkind47_eq46`, `vkind46_eq45`, `vkind45_eq44`, `vkind44_eq43`,
  `vkind43_eq42`, `vkind42_eq41`, `vkind41_eq40`, `vkind40_eq38`, `vkind38_eq28`; `vkind47` of a
  call is that chain's (its ABI registers in `R0`–`R15`) or G47's `callKind47`/`icallKind47`
  (`vkind47_call`, `vkind47_icall`: `callKind47_facts`, `icallKind47_facts`, with `F0`–`F15`
  admitted, an argument there read at its float shape from its V register, `argsV`, as
  `g2_callAt`/`g10_icall` do); terminators
  do not panic (`stepTermLoc_ne_panic`). The premise `RunPanicPre` says that every panicking step
  the run reaches is of these kinds; the machine run panics with `e'`, `BoundsAgree e e'`.
  `RunPre` asks `G54Pre` (a load, a float load, a pair load or an acquire load reads valid bytes,
  a `LoweredMove` or loop accesses valid bytes, a nil check's
  pointer is not nil, a G41 compare's first argument is no bare pointer) only of the
  steps that succeed, so the faulting ones are `RunPanicPre`'s alone. The register-index loads and
  stores are not among them: `runLoc` faults on their nil base whatever the index (`nilAccesses`
  takes the base as the address of a non-`SymOff` op), the machine only when the index keeps the
  address in the nil page. Nor are G50's pair loads (`LDPW`, `LDPSW`, `FLDPD`, `FLDPS`): a
  run whose pair load faults is outside `RunPanicPre`; `simpleOp` excludes them, G51's
  `CMN`/`CMPshiftRA` (`g51Pre_simple`), G53's `LoweredMove` and G54's loops (`g54Pre_simple`).
  Nor are G53's `LoweredMove` and G54's loops: their faults are outside `RunPanicPre`.

**End to end** (`GoFV/Proof/Obj/EndToEnd.lean`, `verified_mach`): `verifiedPipelineFull_refines`
gives a `runLoc` of the allocated function refining the generic `run`; `runLoc` is `finish` of its
body (`runLoc_eq`, from `locInit`), whose outcome is defined (`finish_defined`). The slice is G62
(G61 with the incoming stack arguments, §4) on P0' (§10 item 4): `checkG62` accepts `LocCtx.make`
of the output when `refsLive` holds of it and `checkG62L` accepts
`lc = liveCtx` of it; the body runs alike on `lc` (`runLoopLoc_live`), and the whole-function
theorems apply on `lc`: a returning body is `obj_whole_ret`'s, a panicking one
`obj_whole_panic`'s (under its panic premises), both with `entryStoresOK lc g k`,
`argsOK lc g spills.toList k`,
`EntryMatch E0 g (InWins L E0.sp (pendWins lc g)) sI s0` and `RoRun` (the float constant symbols
in every reached state's memory: `lreach_roMem` from `hmt`/`hro`, or `roRun_nil`). `checkG62L`
includes `loopOK` (each loop's `CBNZ` branches to its head), which `g62L_value` reads off
`checkG62L_spec`; it is no separate premise. `verified_mach` asks `needs48 lc = false` (checked)
and is main's statement otherwise (`RunPre`, `RunPanicPre`: `CallOK` …, `CallPanicOK`,
`ICallPanicOK`; `G3Inv` at the mode `false`). `verified_mach_S` is the same in G48's mode, for any
function `checkG62` accepts: `hinv : G3Inv … sI true`, `hosp : E0.outSP = true`,
`hspI : lc.ctx.f.lowered = true → SPInv E0 sI`, `RunPreS`, `RunPanicPreS`. `verified_mach_fixed`
and `verified_mach_S_fixed` restate them at `Addrs.fixed`. The statements list every premise
(STATUS, Assumptions).

**At the machine layout** (`GoFV/Proof/Obj/EndToEndAtSP.lean`, `verified_mach_atSP`, #672):
`verified_mach` at `Addrs.atSP (baseSP g L E0.sp)` (§8 item 4) for the activation `envAtSP g L E0`
(and `verified_mach_S_atSP`: `verified_mach_S` at `Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat`,
activation 0's `outargs` block at `SP` too, for `envAtSPO g L E0`, `ιSPO_out0`, `envAtSPO_out`),
with `G28Env` of `E0` at `Addrs.fixed` in place of `G49Env` (`g49Env_atSP`; `lc.ctx.act = 0`,
`liveCtx_make_act`). By item 6 the checks take no instance (`GoFVTest/AddrsFree.lean` also scans
`liveCtx`, `retRegsOK`, `entryStoresOK`, `pendWins`, `memTyL`, `checkObj`), so the premise is the
executables' verdict. It holds non-vacuously of the functions with two or more `Blk.local`
variables, of which `verified_mach_fixed` holds only vacuously (18 of quick-v10's 6,494 end to
end on main ae9b2124); `verified_mach_S_atSP` of every function in G48's mode that accesses a
`Blk.local`
variable: at `Addrs.fixed` `SPInv` pins `SP` to `outargs 0`'s fixed base `2^62`, and `AddrAgree`
the variable to `2^62 + x·2^24`, which no frame operand reaches (`g49Env_fixed_outSP`; witness
`fixed_outSP_none`). `gofv-ssa-opt --e2e` counts those functions (STATUS). `ιSP` places activation `actM`'s blocks (at the fixed bases of activation
0's) so that an activation extending `envAtSP` can meet `CallSpec`'s `AddrAgree`.

**Coverage** (quick-v10, `gofv-ssa-opt --check --verified --e2e`, STATUS End-to-end coverage): on
G61, per function at either mode (`agent/lift61` on main 0f930080, with `checkObj`'s `X27At`),
7,003 of 9,297 functions end to end (75.32%): 6,792 under `verified_mach` and 211 under
`verified_mach_S`; 258 more than on G60 and none fewer (170 of std/runtime, 78 of std/sync, 6 of
std/encoding, 4 tests); `checkG61` ∧ `entryStoresOK` accepts 7,007, `checkObj` rejects 4 of them;
stock column 7,897; vacuous at `Addrs.fixed` 20 of the 6,792 and 7 of the 211. On
G60, per function at either mode (`agent/lift60b` on main 70f8f2ec, with G59, objbar, Zero2,
ZeroIdx and objatom), 6,745 of 9,297 functions end to end (72.55%): 6,550 under `verified_mach`
(`needs48 = false`, the mode `false`) and 195 under `verified_mach_S` (G48's mode); 261 more than
on G56 (6,484, main cdf73c37) and none fewer; of the 210 a tree before objbar and Zero2 gained over
the first lift to G60 without G48's mode (6,524), 194 need G48's stack arguments and results; Zero2
adds 11. `checkG60` ∧ `entryStoresOK` accepts 6,748, `checkObj` rejects 3 of them. Stock column
7,281 → 7,597. Vacuous at `Addrs.fixed`: 20 of the 6,550 (two or more `Blk.local` operands) and 7
of the 195 (any `Blk.local` access in G48's mode); the `_atSP` variants cover all.

**Witnesses.** `objWhole_ret_witness` (`pallocSum.start`, `p = 7`, `plRunEnv`): `runLoc`'s run
from `locInit` and `runMach` from the entry to the caller's `0x40`, through `b1`'s `TBNZ` and
`b2`'s `ANDconst`/`MakeResult`/`RET`, with 7 in `X0`. `objWholeNL_ret_witness`
(`runtime.gclinkptr.ptr`, no arm64 op: `ret_results` in Phase 1's mode). `objWhole_panic_witness`
(`(*A).g` on a nil receiver: the nil check faults). `g64_callPanic_witness` (`fint64to32`, a callee
that panics), `g64_icallPanic_witness` (`Locker.Lock`'s interface call), `g64_storePanic_witness`
and `g64_loadPanic_witness` (`(*queueOnePass).next`'s `MOVW R2, 52(R0)` and `MOVWU 52(R0), R3`
with a nil `q`), `g64_ldarPanic_witness` (`sync/atomic.LoadInt64`'s `LDAR (R0), R0` with a nil
`addr`), `g64_atomPanic_witness` (`sync/atomic.SwapInt64`'s `LDAXR`). `objStarLeaf_witness`
(`(*A).g`, a leaf: the P0 run of its nil check keeps the
caller's `0x40` in `X30`). `entryStore_witness` (`GoFV/Proof/Witness/ObjEntry49.lean`:
`g64L_entryStore` on `runtime.getm`'s ABI0 wrapper's `MOVD R0, ~r0+0(FP)` (`checkG64` accepts the
wrapper with `checkG49`'s tables) from a machine whose
`~r0` window holds `0xAB`, to a full `LocMatch`). `verified_mach_witness`:
`pallocSum.start` from its generic SSA (the export's first
section, in the whole-file environment of `gofv-ssa-opt --verified`) through
`verifiedPipelineFull` (`fullyVerified`), with every premise of `verified_mach` discharged;
`checkG64` accepts genssa's Progs against the pipeline's own output, `entryStoresOK` holds (no
pending window). `RunPre` there is `runPre_simple`. The witnesses' facts check `checkG64L` (or
`checkG64`) and `constRo (symNames g) = []` on the same functions with the same tables as before
(none of them has a remainder, `LoweredMove` or loop); they run at the mode `false` (`needs48`
false, checked), as on main. Their G48-mode versions: `ObjWholeS.objWhole_ret_witness` and
`verified_mach_S_witness` (`ObjEndToEndS`: `SP` at `outargs 0`'s fixed base `0x4000000000000000`,
`SepFromW`, `SPInv`, `RunPreS`), `g64_callPanicS_witness` (`CallPanicOKS`).
`verified_mach_atSP_witness` (`GoFV/Proof/Witness/ObjEndToEndAtSP.lean`): `secret_getStack`'s
ABI0 wrapper, with every premise of `verified_mach_atSP` discharged (a callee contract returning
`0x11`, `0x22`; its hook; the results' blocks at `SP + 24`/`SP + 32`), returning with them at the
caller's `SP + 8`/`SP + 16`; at `Addrs.fixed` it has no `G49Env` (`fixed_none`).
`verified_mach_S_atSP_witness` (`ObjEndToEndAtSPS`): the same in G48's mode (`CallOKS`,
`CallOKZS`, `CallOKStk`; the `outargs` block at `SP`, its saved-`LR` word `poison`, `SepFromW`;
the Go register `SP` holding the held pointer to `outargs 0`, `SPInv`).

**Next.** The lift to each new slice as it merges. Panics of the other kinds
(register-index loads and stores; write barriers, `memequal`). A witness of `sim_entryStores`
through a whole function with a real entry store of a register parameter (none of the e2e
functions with a pending window is small enough for the native-decide witnesses yet). Entry
stores after spills (`StoreReg`) in the entry block (`entryStoresOK` rejects them).

*The lift to G62* (done; G62's run premise `ArgOK` is discharged from the entry condition, not
added to `RunPre`):

1. The `Arg`s run with the entry values before the start `k` (`entryLen` counts entry values and
   `Arg`s, in any order), on `runLoc`'s side only: neither emits code, so the machine at `k` is
   the entry's after the prologue.
2. `EntryMatch E0 g W sI s0` has a clause `stack` in place of `slots = []` (the ABI0 caller's
   side, `cmd/compile/internal/abi/abiutils.go:108,270-318`, `offsetForLocals` = `FixedFrameSize`
   = 8): every slot of `sI` is the home of an `Arg` with a `NAME_PARAM` operand `x+off(FP)`,
   `off ≥ 0`, whose bytes at `s0.sp + 8 + off` hold the slot's value (`SlotRel`), below `2^64` and
   apart from `g`'s first 32 bytes. For a function with no `Arg` it is `slots = []`:
   `EntryMatch_stack_nil` (`noArg E.lc = true →` `EntryMatch` iff G61's four fields).
3. The checked boolean `argsOK lc g spills k` (`GoFV/Gen/Entry62.lean`): `argsBefore` (every `Arg`
   in the entry block before `k`, no edge to the entry block), and a function with an `Arg` has no
   pending window (`pendWins`) and no morestack spill. `EntryMatch.more` keeps the clause (no
   tail spill slot when a slot exists; the guard word at `gOff` 16 or 24, `checkObj_gOff`, apart
   from the bytes), and `sim_entry` builds `LocMatch.slots` from it: `frameOff .PARAM off` =
   `autosize + 8 + off` makes the slot's address `E0.sp + o` the caller's bytes, which the
   prologue (below the entry `SP`) and `W` (empty when a slot exists) leave alone.
4. `noArgRun_of_argsBefore`: no state the run reaches from `(entry, k)` is at an `Arg`
   (`NoArgRun`), so `sim_value` passes `g62_obj_value` an `ArgOK` that holds vacuously.
   `verified_mach`, `verified_mach_S` (and `_fixed`, `_atSP`) take `checkG62`, `argsOK lc g
   spills.toList k` and `EntryMatch E0 g …`, otherwise their statements on G61. STATUS lists the
   clause in the entry condition with the ABI0 citations and marks `ArgOK` discharged.

*The lift to G64* (done; G63's and G64's run premises join `RunPre`'s per-step conjunction):
`Obj/G62.lean` → `Obj/G64.lean` (`g64_obj_*` over `g64L_*`; `g64_obj_value` takes `FReloadPre`
and `QLoadPre`). `RunPre`, `RunPreS` and `RunPreM` ask, at a value whose step succeeds,
`G54Pre lc s v ∧ FReloadPre lc s v ∧ QLoadPre lc s v` in place of `G54Pre lc s v`, and nothing
else; `sim_value` passes the two to `g64_obj_value`. The panics' `vkind64` is read through
`vkind64_eq63` (no access, call, atomic or entry store is an op of G64's, `qop64`) and
`vkind63_eq62` (none is a `StoreReg` or `LoadReg`), then `vkind62_eq61` as before. `simpleOp`
excludes `LoadReg`, `FMOVQload` and `FLDPQ`, so `runPre_simple` discharges the two
(`pre64_simple`). `verified_mach`, `verified_mach_S` (and `_fixed`, `_atSP`) take
`checkG64 (LocCtx.make …) ps bstart g`, otherwise their statements on G62. A G64 128-bit load or
store whose step panics (a nil base) is outside `RunPanicPre`, as G50's pair loads are.

## 10. Read-only data: float constants and jump tables

**The gap.** Two kinds of machine loads read data that the assembler or genssa put in read-only
symbols, which the SSA program never writes:

- *Float constants.* `progedit` rewrites `FMOVD $c, Fd` (`FMOVS`) to a load of `$f64.<bits>`
  (`$f32.<bits>`) when `c` is no `FMOV` immediate and not 0: `ADRP` + `LDR D` with
  `R_ARM64_PCREL_LDST64` (§7). P0's `FMOVD $c` is the constant (`FCONST`). This is 163 of
  `checkObj`'s rejections on quick-v10.
- *Jump tables.* `JUMPTABLE`'s `MOVD (Rtab)(Ridx<<3), R27; JMP (R27)` loads the target from the
  table genssa makes. `span7` fills the table with `R_ADDR` relocations to the function plus each
  target's PC.

Nothing in `ObjEnv`, `ObjRel` or `LocMatch` said that memory holds those bytes, or that stores and
calls keep them.

**Why not on the object side.** One option is a premise of `obj_star`: in every state of the P0
run, the read-only bytes are in memory. The composition cannot discharge it. It knows the memory
only in the states `LocMatch` relates (value and terminator boundaries), but `obj_star` steps
through the P0 states inside a value's run (`PStar`), and the slice lemmas say nothing about
those. An invariant of `obj_step` would need every P0 store to miss the read-only bytes, which
only the slices know.

**Design.** Read-only symbols are Phase 1 read-only allocations, and the read happens where
`LocMatch` holds.

1. *Image.* A read-only symbol is a global allocation with `writable := false`.
   - Its bytes come from the export's data and `R_ADDR` fragments for an `SRODATA` symbol
     (`rodataAlloc`, already in Phase 1's global image).
   - For the constant symbols they come from the name (`constSymAlloc?`, `constRo names`,
     `GoFV/SSA/Sem/ConstSym.lean`). `asm-parity` checks the port's constant symbols, bytes
     included, against Go's (`Cmp.data`).
   - The premise is an input property, like `RoImage`'s image part: the input memory with the
     global image has the allocations, `RoMem ro (addGlobals env mem)`.
2. *Run invariant* (`GoFV/Proof/Obj/RoLoc.lean`, `RoReach.lean`). Every memory `runLoc` holds
   keeps those allocations (`lreach_roMem`):
   - Stores: `Mem.write` needs a writable allocation (`Mem.keepsRo_write`), and frame
     allocations and the write-barrier buffer are no globals.
   - Calls: `Env.KeepsRo`, already a Phase 1 premise (`RoImage` in `VPre`, STATUS Assumptions).
   The proof is `MemInv`'s, for `runLoc`. `LocMems P s` says that every memory in the state (its
   memory, flags, registers, slots, staged controls, activation) is `P`.
   - `stepLoc` keeps it (`stepLoc_locMems`). A copy (`LoadReg`/`StoreReg`) and a `MOVDreg` are
     immediate. Otherwise the result comes from `evalOpL_mems`: Phase 1's memory ops by
     `MemInv.evalOp_mems`, and the arm64 ops by `arm64Op_mems` (stores and the bulk ops write,
     `LoweredWB` allocates the buffer, calls are contracts, nil checks are `memRoot`, atomics are
     `atomicRoot`).
   - This needs every value whose shape may hold a memory to have an op of `memOpL`. The
     driver checks this as `memTyL`, `GoFV/Gen/MemTyL.lean`; a value of any other shape holds
     none once `runLoc` shapes it.
   - `stepTermLoc` stages controls, which are reads (`stepTermLoc_locMems`).
3. *Machine side.* In a state `LocMatch` relates, `MemInj` puts each concrete byte of the
   allocation at the global's injected address (`ro_byte`, under `AddrAgree`; above the nil
   page, `ro_addr`). `G2Env.glob` puts that global at `L.sym y`. After a call, `CallSpec` already
   gives `MemInj` of the post-call memory, which keeps the allocation, so no trusted clause is
   added: the read-only data rests on the callee contracts and `Env.KeepsRo`.
4. *Float constants* (done, composed; agent/fconst).
   - P0' (`GoFV/Asm/ConstLoad.lean`): `p0Prime idx ps` applies `progedit`'s rewrite to each Prog
     `fconstSym?` names (`GoFV/Asm/Obj7.lean`, the `FMOVS`/`FMOVD` cases of `progedit`, sharing
     `float32SymName`/`float64SymName` with `float32Sym`/`float64Sym`): `From` becomes
     `MEM`/`EXTERN` of the constant symbol, offset 0, numbered `idx name` (`obj-check`: the port's
     `flush`, `symIdx` at `(name, ABI0)`); `internConsts`/`p0PrimeSyms` add the symbols to a table
     as `lookup` does (`gen-check`'s `G2In.syms`).
   - `checkObj` on P0' compares a load with a load; `ObjRel` is unchanged. Its machine side now
     admits a SIMD&FP access in an `R_ARM64_PCREL_LDST*` pair (§7, **P0'**). quick-v10: 8,544 →
     8,703 functions.
   - Slice G56 (§4) accepts `FMOVSconst`/`FMOVDconst` homed by `FCONST` or by the load of a
     constant symbol of `G2In.syms` whose name holds the bits (`constSymA`); proved in the value's
     `LocMatch`ed state by `ro_byte`/`ro_addr` (now `GoFV/Proof/Gen/RoByte.lean`) under
     `RoPre56 g s` (`RoMem (constRo (symNames g))` of the state's memory). gen-check on P0':
     7,331 (on G55), of which 61 load a float constant. Witness `genG56_witness`
     (`runtime.float64Inf`).
   - **The composition** (on the lift to G54, main e53604fc; on G55, cdf73c37): `Obj/G54.lean` → `Obj/G56.lean`
     (`g56_obj_value` … from `g56L_*`; `checkNL30_of_56L`, `g56L_clean`), `MemPanic`,
     `CallPanic`, `Entry49` (`g56_memPanic`, `g56_ldarPanic`, `g56_callPanic`,
     `g56_icallPanic`, `g56L_entryStore`: an access, call or entry store is no G56 op,
     `vkind56_eq49`, `op56`), `Whole.lean` on `checkG56L` (`checkG56L_cx`,
     `checkG56L_uIn_entry`). The read-only premise is `RoRun g env lc b0 i0 s0` (`RoPre56` at
     every state the run reaches), a premise of `sim_values`, `sim_from_ret`, `sim_valuesPanic`,
     `sim_from_panic`, `obj_whole_ret`, `obj_whole_panic` next to `RunPre` (`RunPre` itself is
     unchanged, so `runPre_simple` still discharges it); `verified_mach` discharges it by
     `lreach_roMem` (the entry values' run `hpre`, `Env.KeepsRo` from `VPre`'s `RoImage`).
     `verified_mach` takes `checkG56 (LocCtx.make …) ps bstart g` on P0' `ps` (with `g` the
     symbols with the constants) and `checkObj` on the same `ps`, and gains exactly two premises:
     `(hmt : constRo (symNames g) ≠ [] → memTyL lc = true)` (executable, the driver checks it
     when the function loads a float constant; without one `RoRun` is `roRun_nil`; `memTyL` itself
     rejects `WBend` and `CALLtail`, 733 and about 160 quick-v10 functions; sound by `memTyL_val`) and
     `(hro : RoMem (constRo (symNames g)) (addGlobals e mem))`; `verified_mach_fixed` restates
     it. Witnesses: `ObjWhole`, `ObjWholeNL`, `ObjPanic` check `constRo (symNames g) = []`
     (`roRun_nil`), `ObjWhole.lcFacts` also `memTyL` (`lc_ro`), which `verified_mach_witness`
     uses. The driver (`E2E.back`): P0' numbered by `internConsts` for `checkG56` and by
     `Flushplist`'s `symIdx` for `checkObj`, a function whose two numberings differ rejected,
     `memTyL` on `liveCtx`, `checkG56`, `checkObj` on P0'.
   - **The lift to G60** (G57–G59 are stacked on G55, so the composition needs a slice with both
     G56's float constants and G57+'s ops, §4 G60; G48's own kinds need G48's mode, per
     function, `needs48`): `Obj/G56.lean` → `Obj/G60.lean` (`g60_obj_*` from
     `g60L_valueX`/`g60L_termX` at a mode `osp`: a lowered function by `g60L_*`, with `hn48`, and
     `hosp`/`SPInv` at the mode `true`, one with no arm64 op by G33's mode-generic lemmas;
     `g60L_clean` through `vkind60_initMem` … `vkind48_initMem`), `MemPanic` (`g60_memPanic`: an
     access off `SP`, `kind48`, takes G48's mode and does not fault under `SPInv`), `CallPanic`
     (`g60_callPanic` under `CallPanicOKAt`, `callKind48` among the calls, on `callRegsZ` at the
     mode `false`, the new trusted `CallPanicOKS`/`ICallPanicOKS` at `true`), `Entry49`
     (`g60L_entryStore` in either mode), `Whole.lean` on `checkG60L` (`SimAt` at the mode, with
     `SPInv` at `true`; `RunPreM`/`RunPanicPreM` with the contracts of the mode; `sim_entry` by
     `memInj_of_sepW`). `verified_mach` takes `checkG60 (LocCtx.make …) ps bstart g` on P0' and
     `needs48 lc = false`, otherwise main's statement; `verified_mach_S` is G48's mode (`hinv` at
     `true`, `hosp`, `hspI`, `RunPreS`, `RunPanicPreS`); `verified_mach_fixed`/`_S_fixed` restate
     them, `verified_mach_atSP`/`_S_atSP` at `Addrs.atSP`/`Addrs.atSPO`.
   - **The lift to G61** (the atomics, §4 G61; `checkObj`'s `X27` across Progs, `X27At`, #692):
     `Obj/G60.lean` → `Obj/G61.lean` (`g61_obj_*` over `g61L_*`, statements unchanged), the
     panics' `vkind61` read through `vkind61_eq60` (no access, call or entry store is an op of
     group A), `Whole.lean` on `checkG61L`; `vkind61` tries `vkind61a` first, so of an atomic it
     accepts `vkind61a`'s (`vkind61_atom`; `gen-check` unchanged), which `g61_atomPanic`
     (`Obj/AtomPanic.lean`) reads: an atomic's nil fault is a fifth no-premise disjunct of
     `RunPanicPre`/`RunPanicPreS`/`RunPanicPreM` (`(atom61? v.op).isSome`), matched in
     `sim_valuePanic` by `g61_obj_atomPanic`. `verified_mach` and `verified_mach_S` (and
     `_fixed`, `_atSP`) take `checkG61 (LocCtx.make …) ps bstart g`, otherwise their statements
     on G60.
   - **The lift to G62** (the incoming stack arguments, §4 G62; §9 *The lift to G62*):
     `Obj/G61.lean` → `Obj/G62.lean` (`g62_obj_*` over `g62L_*`; `g62_obj_value` takes `ArgOK`),
     the panics' `vkind62` read through `vkind62_eq61` (no access, call, atomic or entry store is
     an `Arg`), `Whole.lean` on `checkG62L` with `NoArgRun`; `EntryMatch` with the stack clause
     and `argsOK` in the statements.
   - **The lift to G64** (the float spills and reloads, §4 G63, and the 128-bit blob moves, §4
     G64; §9 *The lift to G64*): `Obj/G62.lean` → `Obj/G64.lean`, `FReloadPre` and `QLoadPre` in
     `RunPre`'s per-step conjunction, `checkG64` in the statements.
   - The `RoMem` premise is about the input memory: Phase 1's export image (`globalImage`) has no
     assembler symbols, so `addGlobals` adds none and the input `mem` must hold the constant
     symbols' allocations. With `EntryMatch`'s `MemInj` and `G2Env.glob` it says that the loaded
     image holds the bits at the symbol's linked address: an assumption about the linker and
     loader (STATUS Assumptions, `RoMem` of the constant symbols), not about the compiled code.
5. *Jump tables* (with the JUMPTABLE slice).
   - The table is a Phase 1 read-only allocation of code-pointer fragments (the targets' Prog
     IDs). `MemInj` resolves them through the link: `L.addr id` on P0, `base + pc` on the
     machine.
   - P0 reads the table in the terminator's `LocMatch`ed state, as in 2–3.
   - `ObjRel.mem` stays equality outside the table and relates the table's words through the PC
     map.

Witness: `objRo_witness` (`GoFV/Proof/Witness/ObjRo.lean`). It runs `pallocSum.start` in
`plRunEnv`, whose image has the read-only `runtime.writeBarrier` flag. `memTyL` accepts the
function (`ro_facts`), the flag is in the memory after the entry values (`lreach_roMem`), and its
byte is in the machine's memory at its linked address (`ro_byte`). `constSym_witness` checks the
symbol of 1.0.
