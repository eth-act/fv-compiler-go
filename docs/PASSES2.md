# Pass survey: arm64 passes from `lower` to `trim` (go1.27.3, linux/arm64)

Scope: `cmd/compile/internal/ssa/compile.go` `passes` (lines 494-519) from `lower` (index 35,
counting `number lines` as 0) through `trim` (index 58), and the `passOrder` constraints among
them (lines 530-614). Paths are relative to `third_party/go/src/cmd/compile/internal/ssa`
unless prefixed. Companion of `docs/PASSES.md` (Phase 1, passes 0-34), whose §1 (ID allocation
and free lists, constant cache, cached CFG analyses and their staleness, sparse sets, sorting,
positions, names/slots, pass name) applies unchanged to every pass here. Semantics plan:
`docs/plans/semantics2.md`. Export: `docs/contracts/export.md` (format 5, #379).
Tracking issue: #387; milestones H1-H8: `docs/PLAN.md` §6.

Written by the Phase2Survey agent from the source only (no builds). Section 4 was compiled per
pass by survey agents reading the source; function start lines were spot-checked, ranges at the
ends of functions can be off by a few lines. Every "parity trap" is something an exact port
(same IDs, same `b.Values`/`f.Blocks` order, same aux, same positions, same homes) must
replicate.

## 0. Pipeline

Same driver test as Phase 1: a pass runs unless `(!f.Config.optimize && !p.required) ||
p.disabled` (`compile.go:68-70`). Code lines are non-blank, non-comment lines of the pass's
own code. "Form" is the lowered-SSA form the pass consumes/produces (`docs/plans/semantics2.md`
§1): **L0** unscheduled lowered SSA (semantics: Phase 1 `run` extended), **L1** scheduled SSA
(`runSched`), **L2** allocated SSA (`runLoc`). Difficulty: parity / proof (S, M, L, XL).

| idx | pass | fn | req | linux/arm64 default | under -N | issue | code lines | form | parity / proof |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 35 | lower | `lower` | ✓ | runs | runs | #388 | 35 + 24,547 generated (1,233 rules) | L0 | L / XL |
| 36 | addressing modes | `addressingModes` |  | **no-op** (arm64 not in its arch switch) | skipped | #389 | 425 (guard only) | L0 | S / S |
| 37 | late lower | `lateLower` | ✓ | runs | runs | #390 | 921 generated (69 rules) | L0 | M / M |
| 38 | pair | `pair` |  | runs (arm64 only) | skipped | #391 | 318 | L0 | L / L |
| 39 | lowered deadcode for cse | `deadcode` |  | runs | skipped | #392 | 249 (Phase 1) | L0 | S / M |
| 40 | lowered cse | `cse` |  | runs | skipped | #393 | 407 (Phase 1) | L0 | M / L |
| 41 | elim unread autos | `elimUnreadAutos` |  | runs | skipped | #394 | ~40 | L0 | S / M |
| 42 | tighten tuple selectors | `tightenTupleSelectors` | ✓ | runs | runs | #395 | 48 | L0 | S / M |
| 43 | lowered deadcode | `deadcode` | ✓ | runs | runs | #396 | 249 (Phase 1) | L0 | S / M |
| 44 | checkLower | `checkLower` | ✓ | runs (identity unless it fails) | runs | #397 | ~26 | L0 | S / S |
| 45 | loop invariant | `licm` |  | runs (reducible leaf loops with 2-pred headers) | skipped | #398 | 96 + loop nest | L0 | M / L |
| 46 | late phielim and copyelim | `copyelim` |  | runs | skipped (still inside every deadcode) | #399 | 93 (Phase 1) | L0 | S / M |
| 47 | tighten | `tighten` | ✓ | runs | **no-op** below 10,000 blocks (`tighten.go:15`) | #400 | ~150 + `lca.go` 85 | L0 | M / L |
| — | merge conditional branches | `mergeConditionalBranches` | | **not in `passes`** (commented out, `compile.go:507-508`) | — | #401 (closed) | 590 | — | — |
| 48 | late deadcode | `deadcode` |  | runs | skipped | #402 | 249 (Phase 1) | L0 | S / M |
| 49 | critical | `critical` | ✓ | runs | runs | #403 | 68 | L0 | M / M |
| 50 | phi tighten | `phiTighten` |  | runs | skipped | #404 | ~17 | L0 | S / M |
| 51 | likelyadjust | `likelyadjust` |  | runs | skipped | #405 | 314 (with loop nest) | L0 | M / S |
| 52 | layout | `layout` | ✓ | runs | runs | #406 | 126 | L0 | M / S |
| 53 | schedule | `schedule` | ✓ | runs | runs (`optimize` off changes the heap key) | #407 | 421 (with `storeOrder`) | L0 → L1 | L / L |
| 54 | late nilcheck | `nilcheckelim2` |  | runs | skipped | #408 | ~100 | L1 | M / L |
| 55 | flagalloc | `flagalloc` | ✓ | runs | runs | #409 | 203 | L1 | L / M |
| 56 | regalloc | `regalloc` | ✓ | runs | runs | #410 | 2,582 + `stackalloc` 355 | L1 → L2 | XL / XL (validator) |
| 57 | loop rotate | `loopRotate` |  | runs | skipped | #411 | 112 | L2 | M / S |
| 58 | trim | `trim` |  | runs | skipped | #412 | 116 | L2 | M / L |

Under `-N` the Phase 2 pipeline is: lower, late lower, tighten tuple selectors, lowered deadcode,
checkLower, tighten (a no-op below 10,000 blocks), critical, layout, schedule, flagalloc,
regalloc. `addressing modes` and `pair` dispatch on `f.Config.arch` (`addressingmodes.go:11-18`,
`pair.go:18-23`): on arm64 the first returns at once, the second runs.

### `passOrder` constraints within scope (`compile.go:530-614`)

`lower` < `late lower` < `lowered cse`; `lower`, `late lower`, `lowered deadcode` <
`checkLower`; `tighten tuple selectors` < `schedule`; `critical` < `phi tighten`, `layout`,
`regalloc`; `schedule` < `late nilcheck`, `flagalloc`, `regalloc`; `flagalloc` < `regalloc` <
`loop rotate`, `trim`. Constraints into scope from Phase 1: `insert resched checks`,
`memcombine`, `branchelim`, `known bits`, `cpufeatures` < `lower`; `generic deadcode`,
`generic cse`, `insert resched checks` < `tighten`.

## 1. Shared infrastructure new in Phase 2

### 1.1 Op metadata and registers
Lowered passes decide by `opcodeTable` attributes, never by op names: `generic` (`checkLower`),
`call`/`hasSideEffects`/`nilCheck` (deadcode roots, `likelyadjust`), `commutative` (cse,
regalloc), `earlyOk` (LICM; an explicit whitelist, not "pure"), `rematerializeable` and
`fixedReg` (`phi tighten`, regalloc), `faultOnNilArg0/1` and `auxType` (`late nilcheck`),
`clobberFlags` (`flagalloc`, regalloc), `resultInArg0`, `resultNotInArgs`, `needIntTemp`, `reg`
(inputs in regspec order, outputs, clobbers; regalloc), `symEffect` (`elim unread autos`),
`unsafePoint`, `zeroWidth`. All come from `_gen/ARM64Ops.go` through `_gen/main.go` into
`opGen.go`; generate them (H2, #380) with `tools/opsgen` and cross-check field by field.
`usesScratch` (`op.go:44`) is set by nothing and read by nothing in this pin.
Registers: `Config.registers` has 64 entries with **dense** numbers that are not hardware
numbers (0-17 R0-R17, 18-25 R19-R26, 26 g, 27 R29, 28 R30, 29 ZERO, 30 SP, 31-62 F0-F31,
63 SB; `opGen.go:116371-116444`); `gpRegMask = 335544319` (dense 0-25 and 28), R18 and R27 are
not in the table, `FPReg = -1`, `LinkReg = 28` (R30 allocatable only in non-leaf functions),
`intParamRegs` R0-R15, `floatParamRegs` F0-F15, `hasGReg`.

### 1.2 The rewrite engine with ARM64 rules
`lower` and `late lower` reuse Phase 1's `applyRewrite` in `removeDeadValues` mode
(`docs/contracts/rules.md`) with `_gen/ARM64.rules` and `_gen/ARM64latelower.rules`. New
encodings: `flagConstant` packs **N=bit0, Z=bit1, C=bit2, V=bit3** and its subtraction carry
means "no borrow" (`rewrite.go:2318-2348`), whereas `arm64ConditionalParams` (CCMP) packs
architectural NZCV (N=bit3); `armBFAuxInt` is `width | lsb<<8` (`rewrite.go:1952-1971`); the
AuxInt of `CCop` ops (`CSEL`, `CSINC`, `CSINV`, `CSNEG`, `CSETM`, `CCMP`, …) is a raw **Go opcode
number** (`op.go:366`, `auxIntToOp`), which depends on `opGen.go`'s enum order (all arches,
including the 306 appended ARM64 SIMD ops), so the Lean side needs `Op.goNum`/`Op.ofGoNum`.
`makeJumpTableSym` creates the symbol `<fn LSym>.jump<bid>` (`rewrite.go:2486-2491`).

### 1.3 The loop nest
`loopnestfor` (`likelyadjust.go:245-415`) is the second cached CFG analysis that matters:
`f.loopnest()` caches it in `f.cachedLoopnest` (`func.go:795-801`) and `likelyadjust`,
`tighten`, regalloc and `loop rotate` read the cache, which can be **stale** exactly as the
postorder (PASSES.md §1.3); LICM builds a fresh one and does not cache it (`licm.go:38`).
Loops are kept in discovery order (postorder × successor order), not sorted; regalloc and
`loop rotate` sort loop indices by depth only (ties, unstable sort). Regalloc **mutates** the
cached loops (`containsUnavoidableCall`, `regalloc.go:3557-3610`), and `loop rotate` reuses
that cache.

### 1.4 Clones and positions
`Value.copyInto` (`value.go:446-458`) clones a value into another block with
`Pos.WithNotStmt()` (`tighten tuple selectors`, `phi tighten`, `flagalloc`), and refuses memory
arguments; regalloc's `copyIntoWithXPos` can restore a same-line statement mark. Every clone
allocates from the LIFO free list (PASSES.md §1.1), so the free list each deadcode leaves is
observable in the next pass that clones.

### 1.5 Post-schedule and post-regalloc state
`schedule` sets `f.scheduled` and from then on `b.Values` is the execution order; `layout` sets
`f.laidout` and `f.Blocks` is the emission order; `flagalloc` writes `b.FlagsLiveAtEnd`;
`loop rotate` ORs `b.Hotness`. Regalloc writes `f.RegAlloc` (a `[]Location` indexed by value
ID: nil, `*Register`, `LocalSlot{N, Type, Off, SplitOf, SplitOffset}`, `LocPair`, `LocResults`;
freed values keep their stale entries) and `f.tempRegs`, and its output is **not SSA**:
arguments need not dominate their uses (`check.go:451-454`, `regalloc.go:91-113`), and edge
copies can have no SSA uses but be needed. No deadcode runs after regalloc
(`deadcode.go:166-168` is fatal on `f.RegAlloc != nil`).

### 1.6 New autos
`stackalloc` and the regalloc shuffle create stack slots with `f.NewLocal` →
`typecheck.TempAt`, which names the auto from `len(curfn.Dcl)` and appends it to the frontend
function's declarations (`func.go:858-861`, `typecheck/dcl.go:51-73`). Their names and order are
part of parity and must be reproduced by the driver import (H8).

### 1.7 Sorting
New unstable sorts with possible ties, to port exactly with the shared `GoFV.Util.PdqSort`: the
schedule edge list by source ID (`schedule.go:282-285`); loop indices by depth in regalloc
(`regalloc.go:3133-3136`) and `loop rotate`; `pair`'s load sort, whose comparator **assigns aux
ranks while it runs** (`pair.go:125-180`), so even the comparator calls must be reproduced; it
also orders by Go opcode number (`int(x.Op - y.Op)`, so by `Op.goNum`) and by wrapping
`AuxInt` subtraction, as `schedule`'s heap does (`schedule.go:53-89`). Total
orders (any correct sort): regalloc's live lists by `(dist, ID)`, `pair`'s store flush by
offset.

## 2. What the export must add (consolidated; posted on #379)

- **Ops, aux, blocks**: ARM64 op names; `CCop` AuxInts as Go opcode numbers (mapped by
  `Op.ofGoNum`); raw AuxInt for `ARM64BitField`, `ARM64ConditionalParams`, `FlagConstant`,
  `SymValAndOff`; the 25 ARM64 block kinds with their aux/auxint (`TBZ`/`TBNZ` bit,
  `JUMPTABLE`'s two controls and Sym).
- **Cached loop nest contents** (ordered loops, `b2l`, header, outer, depth, `nBlocks`, `isInner`,
  `hasIrreducible`, `containsUnavoidableCall`), as for the other caches: what is cached, possibly
  stale.
- **Per-block and per-function flags**: `f.scheduled`, `f.laidout`, `b.FlagsLiveAtEnd`,
  `b.Hotness`, `f.IsPgoHot`.
- **Register allocation**: `f.RegAlloc` with nil holes and stale entries; `f.tempRegs` (by value
  ID); the `AuxCall.Reg`/`OwnAux.ResultReg` caches regalloc fills lazily (`op.go:137-204`) as an
  oracle for the port's derivation from `abiparam`; new autos (name, type, class, flags) on first
  use.
- **Config**: the register table and masks (§1.1), `intParamRegs`/`floatParamRegs`, `FPReg`,
  `LinkReg`, `hasGReg`, `buildcfg.FramePointerEnabled`, `base.Flag.ClobberDeadReg`,
  `base.Flag.N` (read directly by `tighten.go:15`), `ctxt.Flag_dynlink` (42 rules),
  `ctxt.Arch.ByteOrder` (5 rules), `base.FmaHash == nil` (`useFMA`), `GOOS` (`faultOnLoad`).
- **Free list after regalloc**: written in a canonical order (sorted) from the `regalloc`
  section on, because Go's own order is not reproducible (§3).
- **Not needed** in this scope: `f.RegArgs`, `f.CloSlot`, `Flag_locationlists` (ssagen and
  `genssa`, Phase 3); `opcodeTable` attributes (static, H2).

## 3. Nondeterminism and other global hazards

- **Regalloc frees unused copies in Go map order.** `regalloc.go:2276-2290` ranges over the map
  `s.copies` and calls `f.freeValue` on each unused opportunistic copy until a fixpoint. The
  surviving values, their homes and the emitted code are the same on every run, but the order
  of `f.freeValues` differs (and with it the IDs any later allocation would get; no pass in scope
  allocates after regalloc). The export writes the free list sorted from `regalloc` on and
  parity compares that form. Like `sccp`'s map order (#87) it is a reproducibility wart, not a
  miscompile; it changes no object code, so it is not an upstream candidate.
- No other pass in scope ranges over a Go map in an order-observable way: `stackalloc`'s
  `locations` (keyed by `Type.LinkString`), `tighten tuple selectors`' and `pair`'s maps,
  `loop rotate`'s maps and regalloc's edge maps are only looked up or traversed through ordered
  slices (`cachedVals`); `flagalloc`'s `copyFlags` map writes distinct argument slots.
- **Floating-point contraction.** `useFMA` rules (`_gen/ARM64.rules:1798-1809`) fuse
  multiply-add, which rounds once; Phase 1's `evalPure` rounds twice. Decided on #384: the Go
  spec permits it, and the `lower` theorem holds up to a contraction of the source at exactly
  those 12 rule shapes (`docs/plans/semantics2.md` §2.1); Phase 1's semantics is unchanged.
- **Ready-root order at `schedule`.** Phase 1's `run` orders ready roots NilCheck first, then by
  ID; Go's `schedule` orders by its score heap. Where two panicking roots are ready together the
  outcomes can differ (#96; `docs/plans/semantics2.md` §6). Deferred to the schedule proof
  (#384); the default is a validator that rejects reordered panicking roots.
- **Debug flags are not inert here**: regalloc's debug printing sorts the live slice in place
  (`regalloc.go:3392-3396`). The export runs with all debug levels 0.

## 4. Per-pass sections

### lower — issue #388

**Function / files:** `lower` calls `applyRewrite(f, f.Config.lowerBlock, f.Config.lowerValue, removeDeadValues)`; ARM64 configuration selects `rewriteBlockARM64` and `rewriteValueARM64` (`lower.go:8-11`; `config.go:228-234`). Generated implementation: `rewriteARM64.go:1-28098`, from `_gen/ARM64.rules:1-1858`; block rewriter starts at `rewriteARM64.go:24493`.

**Position & ordering:** index **35**, required; immediately precedes `addressing modes` and `late lower` (`compile.go:493-495`). Explicit constraints: `insert resched checks`, `memcombine`, `branchelim`, `cpufeatures`, and `known bits` precede `lower`; `lower` precedes `late lower` and `checkLower` (`compile.go:533-534,581-589,603-610`).

**Enabled (linux/arm64, default build):** yes, including `-N`: required passes bypass the optimize gate (`compile.go:70-73,493`). Architecture selects the rule functions, not whether the required pass runs (`config.go:228-234`). SIMD-specific operations exist in the architecture table even though the SIMD experiment-dependent passes are disabled in the requested configuration (`compile.go:491-492`; `_gen/ARM64Ops.go:838-843`).

**Size:** `lower.go` wrapper 4 lines; rules `_gen/ARM64.rules` 1,858 lines / 1,233 source rules (`=>` lines, before commutative expansion); generated `rewriteARM64.go` 28,098 lines / 24,547 code lines (block rewriter from `rewriteARM64.go:24493`); shared driver `rewrite.go:41-235` (Phase 1). Ops: 354 non-SIMD ARM64 opcodes (`opGen.go:4648-5001`) plus 306 SIMD opcodes appended by `_gen/ARM64Ops.go:847` (`simdARM64Ops`, unused without `GOEXPERIMENT=simd`); 25 ARM64 block kinds (`_gen/ARM64Ops.go:795-839`).

**What it does:**
1. Reuse the Phase 1 rewrite driver: clear pending statement marks; repeatedly traverse `f.Blocks` in order, chase Copy controls, rewrite the block, then traverse its current `b.Values` range (`rewrite.go:41-94`).
2. Before matching a value, invalidate unused removable values, eliminate trivial phis, replace Copy inputs, and recursively invalidate newly unused Copy chains. These actions immediately change `Uses`; dead-only iterations also continue the fixpoint (`rewrite.go:94-155,177-181`).
3. Dispatch by opcode, trying generated rules in their generated order. Lower arithmetic, comparisons, conversions, addresses, loads/stores, calls, nil checks, atomic operations, bounds checks, and runtime pseudo-operations into ARM64 forms. Simple ellipsis rules change the opcode; compound rules allocate intermediate values and rewrite the original value (`rewriteARM64.go:7-2370`; `_gen/ARM64.rules:5-28,300-340,440-478`).
4. Lower `Zero` sizes 1–16 into scalar stores/STP; sizes 17–191 into `LoweredZero`; sizes ≥192 into `LoweredZeroLoop`. Lower `Move` through size 64 into scalar/vector loads and stores, including overlapping endpoints; sizes 65–191 become `LoweredMove`, ≥192 become `LoweredMoveLoop`. Preserve the rule’s explicit memory arguments and load-before-store structure, rather than synthesizing an equivalent serial copy (`_gen/ARM64.rules:342-438`).
5. Lower boolean `If` controls to ARM64 condition blocks; the fallback is `TBNZ [0]`. Lower `JumpTable` to `JUMPTABLE` with index and table-address controls, obtaining the same symbol twice through `makeJumpTableSym` (`_gen/ARM64.rules:460-478`; `rewrite.go:2486-2491`).
6. Continue machine-dependent optimization: folded constants/flags, address and symbol absorption, shifted operands, bitfields, conditional selects, read-only global loads, FMA, and small/disjoint `runtime.memmove` inlining. The latter can reintroduce generic `Move`, which the same fixpoint subsequently lowers (`_gen/ARM64.rules:657-914,1263-1371,1798-1817,1823-1839`).
7. At fixpoint, free `OpInvalid` values in block/value traversal order, compact surviving values stably, and restore pending statement marks to eligible values or block positions (`rewrite.go:208-235`).

**Data structures:** ordered SSA blocks/values/arguments/controls; shared `cachedLineStarts` pending-line map; persistent value allocator/free lists and constant cache through shared value operations; rule-local bindings and generated commutation loops; `arm64BitField`, `flagConstant`, and opcode-valued `AuxInt` for `CCop` (`rewrite.go:41-44,208-235,1952-1971,2329-2420`; `op.go:365-366`; `rewriteARM64.go:2423-2442,4744-4754`).

**Parity traps (order dependence / nondeterminism):**
- Preserve driver order, first-successful-rule order, generated operand-commutation order, result construction order, and Go range semantics: appending values does not extend the already-started value range. Immediate `Uses` updates enable later single-use rules; replacing this driver with a worklist or generic DCE changes observable results and allocation history (`rewrite.go:65-181`; `rewriteARM64.go:2423-2463`).
- `clobberIfDead` always returns true, but resets its argument to `Invalid` when `Uses == 1`; it deliberately preserves `Block`. It is a mutation in a condition, not a pure predicate (`rewrite.go:1069-1079`). Preserve short-circuit evaluation and operand capture before mutation.
- `removeDeadValues` is not whole-function deadcode: it does not eliminate cycles; invalid values are freed only during final compaction. It must not be replaced by an equivalent live-value computation (`rewrite.go:94-105,208-235`).
- ARM64 block rewrites can swap successors and produce `BlockFirst`; use the shared exact successor/cache behavior, not a fresh CFG analysis after every rewrite (`rewriteARM64.go:28086-28098`).
- `armBFAuxInt` encodes `width | lsb<<8`, rejects `lsb∉[0,63]` or invalid widths; do not substitute the hardware instruction encoding (`rewrite.go:1952-1971`).
- `flagConstant` uses **N=bit0, Z=bit1, C=bit2, V=bit3**, not architectural NZCV bit order. Subtraction carry means **no borrow** (`rewrite.go:2318-2348`). `ccARM64Eval` returns −1/0/+1 and handles `InvertFlags` by negating its recursive result—port the implementation exactly rather than “correcting” it to another condition algebra (`rewrite.go:1233-1273`).
- `canMergeSym` accepts only cases with at least one nil symbol; `mergeSym` chooses the non-nil symbol, not a symbolic sum (`rewrite.go:277-291`).
- Read-only folds require SRODATA with no relocations. Byte readers zero-fill unavailable bytes, including wholly invalid offsets, rather than rejecting the fold (`rewrite.go:2088-2091,2239-2288`).
- Default FMA fusion is allowed and can differ from separately rounded multiply/add; semantic refinement must use Go’s permitted floating-point contraction model, not naïve equality of separate IEEE operations (`func.go:848-855`; `_gen/ARM64.rules:1798-1809`).

**External state read:** ARM64 config/rule functions and type table; exact type identity, size, signedness, pointer shape and pointee pointer content; symbol identity/data/relocations; call aux; function symbol name and global symbol lookup for jump tables; `base.FmaHash`/positions for optional FMA selection; shared positions, names/cache/free-list state and `Uses` (`config.go:228-250`; `_gen/ARM64.rules:305-340,478,1811-1839`; `rewrite.go:2088-2091,2239-2288,2486-2491`; `func.go:850-855`).

Direct `config.ctxt.Flag_dynlink` reads occur at `_gen/ARM64.rules:658,661,664,667,670,673,676,679,682,685,688,691,758,761,764,767,770,773,776,779,782,832,836,840,844,848,852,856,860,864,868,872,876,881,885,889,893,897,901,905,909,913`; they prohibit the affected SB address absorptions under dynamic linking. `config.ctxt.Arch.ByteOrder` is read at `_gen/ARM64.rules:1812-1814,1816-1817`. `config` is passed to `isInlinableMemmove` at `_gen/ARM64.rules:1828,1837`; ARM64 accepts size ≤64, or size ≤1024 with proven disjointness (`rewrite.go:1505-1525`). These wrappers do not consult allocated register homes, frame layout, or loopnest (`lower.go:8-18`).

**Depends on:** Phase 1 rewriting infrastructure, exact mutation/allocation/position behavior, ARM64 value/block/aux definitions, target-width arithmetic, symbol and call models. ARM64 flag/bitfield helpers supplement—not replace—the existing generic helper interpreter (`rewrite.go:41-235,1115-1273,1952-1985,2329-2557`).

**Proof strategy & difficulty:** **parity L (the Phase 1 engine and rules2lean exist; new: rules, helpers, metadata); refinement XL (1,233 rules).** Reuse the established driver simulation and validate generated rule data against the pinned generated Go; prove local rewrite lemmas over ARM64 bitvectors, flags, memory and control flow, composed by the driver. Memory expansion, atomics, speculative fault behavior, runtime-call substitution and FMA require explicit semantic contracts; a translation validator can reduce trust in the complete rule library but must still validate these effects (`_gen/ARM64.rules:342-438,478-480,1798-1839`).

**Proof status (#385):** `GoFV.Proof.Low.lower_refines`: the checked lower (`GoFV.Opt.lowerChecked`: the input with its `useFMA` shapes contracted, `GoFV.Opt.FmaContract.contractAll`, then `applyRewrite` with the proven rules `GoFV.Rules.ProvenARM64.lower` and its log, kept only if `GoFV.Opt.LowerCheck.validateL` accepts it) refines, under `runL`, a contraction (`GoFV.Proof.Low.Contract`) of its generic input; `lower_refines_run` relates it to Phase 1's `run` when there is no FMA shape; witness `GoFV.Proof.Witness.la_lower`. Obligations: `ArmRule.Sound` (value rules over `opValL`/`retypeL`, every commutation choice), `SetOpSound` (ellipsis rules), `ArmRule.Rename` (atom renames: `NilCheck`, calls, `GetClosurePtr`), `BlockRuleL.Sound` (`GoFV/Proof/Low/RuleL.lean`); validator soundness `validateL_termRef` (`GoFV/Proof/Low/Val*.lean`), atom simulation over `runL` `atomSimL_refines` (`GoFV/Proof/Low/Sim*.lean`). Coverage (`lower-probe`, quick-v7): with 105 proven rules the checked lower equals stock on 1,264 / 9,297 functions (with every rule, the validator's ceiling, 1,889); the rest is blocked by memory atoms (`Load`/`Store`/`LocalAddr` lowering with address folding), `InvertFlags` (no semantics) and unproven rule families.

**Issue summary:** Port required index-35 ARM64 lowering using the existing exact rewrite engine in `removeDeadValues` mode, adding the ARM64 rule set, architecture metadata and helper semantics. Preserve rule/commutation/allocation order, immediate `Uses` mutations, statement redistribution, flag and bitfield encodings, successor swaps, symbol identities, and dynlink/byte-order/FMA inputs. Scope: 354 non-SIMD ARM64 ops, 25 block kinds, 1,233 source rules. Parity L (the engine exists), refinement XL (`lower.go:8-11`; `rewrite.go:41-235`; `_gen/ARM64Ops.go:795-843`; `opGen.go:4648-5307`).

### addressing modes — issue #389

**Function / files:** `addressingModes`, `addressingmodes.go:9-101`; global `combineFirst`, `needSplit`, and `combine` tables follow (`addressingmodes.go:103-518`).

**Position & ordering:** index **36**, optional, between `lower` and `late lower`; no explicit `passOrder` constraint names this pass (`compile.go:493-495,530-614`).

**Enabled (linux/arm64, default build):** the pass is invoked, but **immediately returns without changing anything**. The architecture switch admits only amd64, 386 and s390x; there is **no ARM64 addressing-mode table or ARM64 splitLoad path** here. Under `-N`, the optional pass is skipped (`addressingmodes.go:9-18`; `compile.go:70-73,494`; `config.go:228-250`).

**Size:** `addressingmodes.go` 518 lines / 425 code lines, of which only the architecture guard (`addressingmodes.go:9-18`) executes on arm64.

**What it does:**
1. Initialize the immediate-range predicate.
2. Read `f.Config.arch`; ARM64 takes `default: return`.
3. Do not traverse blocks, consult maps, or call `splitLoad` (`addressingmodes.go:9-20`).

For comparison only, supported architectures combine the pointer expression into a memory operation, adjust aux/offsets, account for `resultInArg0`, and optionally invoke `f.Config.splitLoad`; `needSplit` contains AMD64 compare-load forms (`addressingmodes.go:22-98,113-131`).

**Data structures:** none accessed on ARM64 beyond Config; the global maps are irrelevant to the target execution (`addressingmodes.go:9-20,103-131`).

**Parity traps (order dependence / nondeterminism):** implementing a plausible ARM64 address-combining pass here would be a parity bug. ARM64 address absorption is already performed by its rewrite rules (`addressingmodes.go:11-18`; `_gen/ARM64.rules:657-914`). Global map initialization order does not affect the ARM64 identity result (`addressingmodes.go:103-111`).

**External state read:** `f.Config.arch` only; no register, stack, frame, loopnest, type or position input (`addressingmodes.go:9-18`).

**Depends on:** pass dispatch and target configuration only (`compile.go:70-74`; `addressingmodes.go:11-18`).

**Proof strategy & difficulty:** **parity S; refinement S.** Prove identity under `Config.arch = "arm64"` directly from the architecture switch (`addressingmodes.go:11-18`).

**Issue summary:** Represent index-36 `addressing modes` as an ARM64 identity pass, skipped under `-N`. Do not port other architectures’ combination tables or introduce an ARM64 splitLoad hook; the target’s relevant address rewrites belong to `lower` (`compile.go:494`; `addressingmodes.go:9-18`; `_gen/ARM64.rules:657-914`).

### late lower — issue #390

**Function / files:** `lateLower`, `lower.go:14-18`; ARM64 uses `rewriteValueARM64latelower` and the always-false `rewriteBlockARM64latelower`, generated from `_gen/ARM64latelower.rules` (`config.go:233-234`; `rewriteARM64latelower.go:1-1102`).

**Position & ordering:** index **37**, required; follows `addressing modes`, precedes `pair`. Explicit constraints: `lower → late lower`, `late lower → lowered cse`, `late lower → checkLower` (`compile.go:495-496,580-589`).

**Enabled (linux/arm64, default build):** yes, also under `-N`. Other architectures with nil `lateLowerValue` do nothing; ARM64 supplies both callbacks (`compile.go:70-73,495`; `lower.go:14-18`; `config.go:233-234`).

**Size:** `lower.go:14-18` (5 lines); `_gen/ARM64latelower.rules` 103 lines / 69 source rules (81 after expanding the 14-way boolean alternative); generated `rewriteARM64latelower.go` 1,102 lines / 921 code lines.

**What it does:**
1. Run the same `applyRewrite(..., removeDeadValues)` fixpoint and final invalid-value compaction as `lower`; the block callback itself never rewrites a block (`lower.go:14-18`; `rewrite.go:41-235`; `rewriteARM64latelower.go:1100-1102`).
2. Replace non-encodable add/sub/compare/test/logical immediates with register forms and freshly constructed `MOVDconst` arguments; include `ADDSconstflags` and 32-bit immediate widening/replication rules (`_gen/ARM64latelower.rules:8-22`).
3. Remove `MOVBUreg` after the enumerated boolean-producing operations; remove `MOVWUreg` when `ZeroUpper32Bits(x, 3)` succeeds (`_gen/ARM64latelower.rules:24-33`).
4. Replace redundant extension-after-load and extension-after-extension forms by `MOVDreg`, preserving the outer value/type rather than indiscriminately replacing every case with a Copy (`_gen/ARM64latelower.rules:35-90`).
5. Turn `MOVDreg x` into `MOVDnop x` when `x.Uses == 1`; collapse `MOVDnop(MOVDconst)`; replace constant zero by the fixed zero-register operation; prefer `ADD x x` to shift-left-by-one (`_gen/ARM64latelower.rules:92-106`).

**Data structures:** shared rewrite-engine state; target-width immediates; opcode-based recursive upper-bit predicate, with depth 3 and no visited set (`rewrite.go:41-235,1383-1426`; `_gen/ARM64latelower.rules:33`).

**Parity traps (order dependence / nondeterminism):** these rules intentionally invert some early lowering choices; combining the two rule sets into one fixpoint would be incorrect. Preserve shared `Uses`, allocation/freeing and statement behavior; newly allocated nonzero constants remain explicit materializations, while zero becomes `ZERO` in later iterations (`_gen/ARM64latelower.rules:5-22,92-106`; `rewrite.go:94-181`). `ZeroUpper32Bits` first rejects signed types narrower than 64 bits because spilling may re-sign-extend them; recursively checks all arguments of Phi/Select0/Select1 only while depth remains, and does not treat ARM64 `Arg` as zero-extending (`rewrite.go:1383-1426`).

**External state read:** Config callback/type table; operand type signedness/size and opcode; exact `Uses`; shared positions/allocator state. No allocated home, actual spill layout or loopnest is queried—the spill concern is encoded in the conservative type guard (`lower.go:14-18`; `rewrite.go:1383-1426`; `_gen/ARM64latelower.rules:8-106`).

**Depends on:** completed general lowering; shared exact rewrite engine; `isARM64addcon`, `isARM64bitcon`, `ZeroUpper32Bits`; subsequent CSE and deadcode clean up generated materializations/copies (`compile.go:580-589`; `rewrite.go:1383-1426,2511-2557`).

**Proof strategy & difficulty:** **parity M; refinement M.** Direct local simulation for immediate materialization and redundant extensions; prove the upper-bit predicate sound with signed spill/reload semantics and bounded recursion. Model `MOVDnop` as a type-preserving register constraint and `ZERO` as the fixed zero register (`_gen/ARM64latelower.rules:24-106`; `_gen/ARM64Ops.go:790`).

**Issue summary:** Port required index-37 late lowering as a separate ARM64 rule set over the shared `removeDeadValues` engine: 81 expanded rules covering immediate legality, extensions, no-op register moves, zero-register selection and shift-by-one preference. Preserve the depth-3 upper-bit test and signed narrow-type rejection, exact single-use decisions and allocation order. Parity/refinement M (`lower.go:14-18`; `_gen/ARM64latelower.rules:8-106`; `rewrite.go:1383-1426`).

### pair — issue #391

**Function / files:** `pair`, `pairLoads`, `pairStores`, `offsetOk`, `memoryBarrierTest`, and load/store tables, all in `pair.go:16-488`.

**Position & ordering:** index **38**, optional; after `late lower`, before `lowered deadcode for cse`. No explicit `passOrder` entry names `pair` (`compile.go:495-498,530-614`).

**Enabled (linux/arm64, default build):** yes; only ARM64 enters the implementation. Skipped under `-N` (`pair.go:16-25`; `compile.go:70-73,496`).

**Size:** `pair.go` 488 lines / 318 code lines: load pairing `pair.go:122-306`, store pairing `pair.go:328-488`.

**What it does:**
1. Pair loads before stores. Eligible load mappings are MOVD→LDP, MOVWU→LDPW, MOVW→LDPSW, FMOVD→FLDPD, FMOVS→FLDPS; eligible stores are MOVD→STP, MOVW→STPW, FMOVD→FSTPD, FMOVS→FSTPS. `offsetOk` currently returns true unconditionally (`pair.go:23-56,64-90`).
2. Within each block collect eligible loads in `b.Values` order. Sort by opcode, pointer ID, memory ID, nil/non-nil aux, comparator-assigned aux rank, then offset. Pair adjacent equal-op/base/memory/aux loads separated by one element width. Append one tuple load at the lower-offset load’s position and reset the original loads to Select0/Select1, retaining their IDs and types; skip the consumed second element (`pair.go:122-210`).
3. Perform a second cross-block load sweep. Skip ARM64NZW blocks controlled by a MOVWUload of symbol named `runtime.writeBarrier`. Build a lookup from eligible loads in successors with at most one predecessor; later successor/value insertions overwrite equal keys (`pair.go:213-257,308-321`).
4. Scan current-block values backwards, moving at most **four** successor loads into pairs. Try `current offset + width` before `current offset − width`. Append the tuple load, reset the current load to its selector, and reset the successor load to Copy of a newly appended selector in the tuple-load’s block. Preserve the selector’s specified position from the successor load (`pair.go:258-304`).
5. For stores, find the first terminal memory value in block value order by marking memory results and clearing marks on same-block predecessor memory arguments. Walk its memory chain backwards, stopping at InitMem/Phi or a cross-block memory edge (`pair.go:389-399,422-449`).
6. Accumulate up to **100** understood nonoverlapping stores sharing base pointer and aux. Flush before unknown memory operations; also flush for a non-latest store with `Uses != 1`, changed base/aux, full buffer, or any overlapping write range. Byte/halfword stores participate in overlap checks even though they cannot form pairs (`pair.go:401-419,450-485`).
7. A flush sorts by offset and pairs adjacent equal-op stores exactly one element width apart. Rewrite the lower-offset store in place to the paired store, preserving its old memory input/position/aux; rewrite the second to Copy of **its own saved old memory input**. Do not rebuild the entire chain in offset order (`pair.go:343-387`).

**Data structures:** load vector; per-block `map[Aux]int` assigned inside the comparator; cross-block lookup keyed by `(op, pointer ID, memory ID, offset, aux)`; ID-indexed terminal-memory bool slice; bounded store vector; static opcode tables accessed by lookup (`pair.go:34-56,122-180,213-257,328-341`).

**Parity traps (order dependence / nondeterminism):**
- Load sorting is especially sensitive: aux ranks are created **during comparator calls**, not in original encounter order. Reproduce Go’s exact sort/comparator-call behavior, not merely an equivalent final comparator using preassigned ranks. Equal full keys have no ID tiebreaker (`pair.go:125-135,155-180`).
- Cross-block maps are not iterated: lookup results are deterministic, but duplicate keys use last insertion in successor/value order. Reverse scanning, positive-offset preference, the four-load cap and append order determine the exact paired values and new IDs (`pair.go:240-304`).
- `offsetOk`’s global/stack-offset and alignment heuristics below its unconditional return are dead behavior. Frame size is not actually read (`pair.go:64-120`).
- Store buffer order, first-terminal selection, live `Uses` changes and exact flush boundaries matter. Store sort keys are distinct for a well-formed nonoverlapping positive-width buffer, unlike duplicate-load keys (`pair.go:349-387,422-488`).
- No values are freed here; paired loads allocate new values, while old loads/stores survive as selectors/Copies for subsequent cleanup (`pair.go:198-207,277-302,366-378`).

**External state read:** Config architecture; opcode numbers and value IDs; types for tuple construction; memory arguments and `Uses`; exact aux identity and `*obj.LSym.Name` for the barrier guard; positions. No actual register allocation, frame layout, loopnest, new autos or stack slots (`pair.go:16-25,155-207,308-321,328-488`).

**Depends on:** lowered ARM64 load/store forms, tuple types/selectors, exact deterministic sorting, memory-SSA chain invariants, interval overlap helper and standard mutation/allocation operations. Later tuple tightening and deadcode process the introduced selectors/Copies (`pair.go:198-207,277-302,475-488`; `compile.go:497-502`).

**Proof strategy & difficulty:** **parity L; refinement L.** Direct simulation plus local memory lemmas: adjacent paired load/store semantics; commuting disjoint stores while preserving all memory users; cross-block load speculation with identical memory arguments, including fault behavior and write-barrier restrictions. A translation validator could certify individual pairings while leaving the heuristic untrusted (`pair.go:213-237,328-488`).

**Issue summary:** Port optional ARM64-only index-38 pairing, including both local and cross-block loads and bounded backwards memory-chain store grouping. Exact parity requires comparator-time aux ranking under Go sort, last-wins successor maps, reverse scan/+offset-first/four-load cap, 100-store flush thresholds, and the precise selector/Copy rewrites and allocation order. `offsetOk` is always true; no frame-layout dependency exists. Parity/refinement L (`pair.go:16-488`; `compile.go:496`).

### lowered deadcode for cse — issue #392

**Function / files:** `deadcode`, `deadcode.go:161-313`, with `ReachableBlocks` and `liveValues` (`deadcode.go:22-158`), shared `copyelim` (`copyelim.go:10-157`). This is the Phase 1 implementation, not a lowered-specific algorithm (`compile.go:498`).

**Position & ordering:** Index **39**, optional, immediately after `pair` and before `lowered cse`; the adjacency deliberately prevents CSE from resurrecting dead expressions. No explicit `passOrder` pair names this instance (`compile.go:497-499,530-614`).

**Enabled (linux/arm64, default build):** Yes; skipped under `-N` through the optional-pass gate. No architecture switch. `f.RegAlloc != nil` is fatal—not a request to conservatively retain everything (`compile.go:70-73,498`; `deadcode.go:161-168`). The separate `liveValues` helper does conservatively mark everything live after allocation, but that branch is unreachable from `deadcode` because of the preceding fatal check (`deadcode.go:61-68,166-168`).

**Size:** shared `deadcode.go` 360 lines / 249 code lines (Phase 1, no new code).

**What it does:**
1. Reuse Phase 1 reachability, dead-edge removal, embedded copy/phi elimination, liveness closure, named-value pruning, statement-mark preservation, and ordered freeing without modification (`deadcode.go:170-313`).
2. Evaluate liveness roots using **lowered opcode metadata**: controls plus `call`, `hasSideEffects`, and `nilCheck`; ordinary lowered computations, flags producers, and unused tuple selectors are not automatically roots (`deadcode.go:98-135`). ARM64 calls and nil checks carry the appropriate metadata (`_gen/ARM64Ops.go:543-551`).
3. Supply a cleaned graph to lowered CSE; survivors retain stable block/value order, while freed IDs affect subsequent allocations (`compile.go:498-499`; `deadcode.go:281-313`).

**Data structures:** Same Phase 1 reachable/live arrays, LIFO worklist, statement-discovery list, inline-index membership map, sparse name-dedup set, and cached line map (`deadcode.go:22-158,216-279`).

**Parity traps (order dependence / nondeterminism):** Preserve lowered-op metadata, traversal/argument order, reverse statement-discovery replay, and value-then-block freeing order. `freeValue` and `freeBlock` push LIFO free lists; this pass therefore influences selector-copy and preheader IDs downstream (`deadcode.go:137-155,261-313`; `func.go:397-454`). No new nondeterminism relative to Phase 1; named values are traversed through ordered `f.Names` (`deadcode.go:220-245`).

**External state read:** `f.RegAlloc` nilness, ARM64 opcode effects, position-table inline indices, `Names`/`NamedValues`, and `cachedLineStarts`; no physical register or frame-layout inspection (`deadcode.go:61-91,110-135,166-168,216-249`).

**Depends on:** Phase 1 deadcode infrastructure and ARM64 effect metadata; placement immediately before CSE is intentional (`compile.go:498`; `deadcode.go:110-135`).

**Proof strategy & difficulty:** **Parity S incremental / proof M incremental:** instantiate the existing reachability/liveness proof with sound ARM64 effect classifications; prove discarded flag/tuple computations have no observable effect. The new obligation is the opcode interpretation, not a different graph algorithm (`deadcode.go:110-155`).

**Issue summary:** Reuse Phase 1 deadcode at index 39; optional and off under `-N`. Extend liveness-root metadata to ARM64, retain the fatal nonnil-`RegAlloc` precondition, and preserve all existing ordered pruning, positions, names, and LIFO freeing behavior. Its purpose is to remove dead candidates immediately before lowered CSE (`compile.go:498-499`; `deadcode.go:161-313`).

### lowered cse — issue #393

**Function / files:** `cse` and its partition/comparison helpers in `cse.go:18-546`; same implementation as generic CSE (`compile.go:467,499`).

**Position & ordering:** Index **40**, optional; follows `lowered deadcode for cse`, precedes `elim unread autos`. Explicit constraint: `late lower → lowered cse` (`compile.go:498-500,581-582`).

**Enabled (linux/arm64, default build):** Yes; skipped under `-N`. No architecture or lowered-pass-name switch inside CSE (`compile.go:70-73,499`; `cse.go:18-324`).

**Size:** shared `cse.go` 546 lines / 407 code lines (Phase 1, no new code).

**What it does:**
1. Collect all values except directly memory-typed values. **Reuse** `f.auxmap`; assign ranks only to unseen aux identities in block/value encounter order (`cse.go:35-55`).
2. Partition by op, auxint, argument count, phi block, type comparison except selectors, and aux identity/rank; initial ordering ends with value ID (`cse.go:379-405,418-458`).
3. Refine classes by argument equivalence; canonicalize the first two operands of commutative ops, sort, split, discard singleton classes, and process newly appended classes in the same sweep (`cse.go:94-199`).
4. Sort each surviving class by sparse-dominator order, then applicable memory ordering and statement preference. Select dominating representatives and rewrite argument/control uses; retain duplicate definitions for deadcode (`cse.go:201-324`).
5. **Lowered differences:** flags and tuples are eligible because only `Type.IsMemory()` is excluded; selectors ignore type comparison. There is no special flags exclusion or blanket “tuple containing memory” exclusion (`cse.go:44-46,438-445`). ARM64 compare and arithmetic-with-flags ops therefore participate according to ordinary argument/type equivalence (`_gen/ARM64Ops.go:198-207,303-306`).
6. The cross-disjoint-store optimization recognizes only generic `OpLoad`/`OpNilCheck`, not ARM64 loads/nil checks: lowered memory operands normally compare by their actual equivalence class. Do not extend the helper to lowered ops during the parity port (`cse.go:115-138,462-487`).

**Data structures:** Persistent `auxmap map[Aux]int32`; candidate slices and equivalence-class slices; ID→class array, rewrite array, memory-remap table, store-order cache; cached sparse dominator tree (`cse.go:35-93,201-207,416`).

**Parity traps (order dependence / nondeterminism):** Never rebuild aux ranks at this pass boundary. Initial sort has an ID tie-break; refinement and representative sorts can tie and must reproduce Go’s unstable deterministic ordering. Class removal swaps with the final class; commutative swapping changes argument order even without a substitution (`cse.go:40-51,105-115,174-193,209-260,379-390`). Selector CSE intentionally ignores result type (`cse.go:438-445`). Statement transfer compares line numbers, not file+line, and the `OpNilCheck` exceptions are literal generic-op checks, not metadata checks (`cse.go:291-316`). `SetArg`/`ReplaceControl` update Uses; no values are allocated or freed (`cse.go:286-318`). Aux maps are looked up, not ranged over (`cse.go:40-51,447-455`).

**External state read:** Persistent aux identities/ranks, type ordering, opcode commutativity, cached dominator/postorder state, positions, and debug/stats; no register homes, frame layout, or ABI decisions (`cse.go:40-51,105,201-260,291-324,418-458`; `func.go:766-793`).

**Depends on:** Phase 1 CSE/sort/dominator implementation; ARM64 opcode/type/aux vocabulary; late lowering and preceding deadcode. Tuple placement/deduplication is repaired afterward rather than guaranteed by CSE alone (`compile.go:498-502,581-582`; `tuple.go:7-11`).

**Proof strategy & difficulty:** **Parity M incremental / proof L:** reuse equivalence refinement and dominance-substitution proofs, extend expression semantics to flags/tuples, and justify selector type-insensitive equality. A translation validator can check each substitution’s dominance and lowered-expression equivalence while the executable port reproduces exact ordering (`cse.go:201-318,438-445`).

**Issue summary:** Reuse generic CSE at index 40, preserving `f.auxmap` across both invocations and exact unstable-sort/class-splitting behavior. Include lowered flags and tuple values; selector types remain ignored. Do not accidentally enable generic load-alias skipping for ARM64 loads. Leave duplicates for subsequent deadcode and preserve statement/Uses mutations exactly (`cse.go:35-55,94-199,286-318,438-487`).

### elim unread autos — issue #394

**Function / files:** `elimUnreadAutos`, `deadstore.go:433-487`; shared ABI predicate `isABIInternalParam`, `deadstore.go:499-501`.

**Position & ordering:** Index **41**, optional, after lowered CSE and before tuple-selector tightening. No explicit `passOrder` constraint (`compile.go:499-501,530-614`).

**Enabled (linux/arm64, default build):** Yes; skipped under `-N`. Architecture-independent algorithm using architecture-specific `SymEffect` metadata; ABIInternal parameters are included, ABI0 parameters are not (`compile.go:70-73,500`; `deadstore.go:441-449,499-501`).

**Size:** `deadstore.go:433-501`, about 55 lines; `deadstore.go` as a whole 497 / 353 code lines (the rest is Phase 1's `dse` and `dead auto elim`).

**What it does:**
1. Scan blocks/values, selecting `Aux.(*ir.Name)` objects that are `PAUTO` or ABIInternal `PPARAM` (`deadstore.go:439-446,499-501`).
2. For exactly `SymNone` or `SymWrite`, queue the value only if its name has not yet been seen. For every other effect—including address-taking and combined effects—mark the name seen only if `v.Uses > 0` (`deadstore.go:448-467`).
3. Revisit queued stores in encounter order. If their name is still unseen, replace the value with a memory copy: `SetArgs1(MemoryArg())`, clear aux/auxint, set `OpCopy`. Do not delete the definition or change its type/position (`deadstore.go:471-486`).

**Data structures:** `ir.NameSet` membership set and ordered `[]*Value` candidate list (`deadstore.go:437-438`).

**Parity traps (order dependence / nondeterminism):** This is symbol-wide unread-auto elimination, not byte-range DSE. Dead loads/address computations with zero Uses do not protect an auto. Only exact `SymNone`/`SymWrite` effects enter the candidate branch. The second phase sees the completed set, so later reads protect earlier stores. Rewrites happen in candidate order and update argument Uses; no map iteration, allocation, or freeing (`deadstore.go:448-486`).

**External state read:** Aux `*ir.Name` identity/Class, `f.ABISelf.Which()`, op `SymEffect`, current Uses, and last memory argument. No offsets, frame sizing, new autos, or register homes (`deadstore.go:441-484,499-501`; `value.go:556-570`).

**Depends on:** Lowered symbol-effect metadata and valid explicit memory chains; subsequent deadcode/copyelim removes the introduced copies (`deadstore.go:480-485`; `compile.go:500-502`; `deadcode.go:209-212`).

**Proof strategy & difficulty:** **Parity S / proof M:** direct simulation modulo unobservable stores to unread, unexposed local/ABIInternal parameter objects. Prove effect classification conservatively captures all reads/address exposure; preserve the ABI0 exclusion (`deadstore.go:448-467,489-501`).

**Issue summary:** Implement the small two-scan lowered unread-auto pass at index 41. Respect exact `SymEffect` cases, Uses-sensitive read detection, and ABIInternal parameter eligibility; rewrite stores/bookkeeping to memory copies without changing IDs, types, positions, or list order. No new stack objects are created (`deadstore.go:433-501`).

### tighten tuple selectors — issue #395

**Function / files:** `tightenTupleSelectors`, `tuple.go:14-71`; `copyOf` and `copyInto`, `value.go:429-458`.

**Position & ordering:** Index **42**, required, between unread-auto elimination and required lowered deadcode. Explicit constraint: `tighten tuple selectors → schedule` (`compile.go:500-502,569-570`).

**Enabled (linux/arm64, default build):** Yes, also under `-N`; no architecture switch (`compile.go:70-73,501`; `tuple.go:14-71`).

**Size:** `tuple.go` 71 lines / 48 code lines; `copyOf`/`copyInto` (`value.go:429-458`).

**What it does:**
1. Scan blocks and selectors in stored order. Recognize `Select0`, `Select1`, and `SelectN`; validate tuple versus results type and derive selector index (`tuple.go:19-41`).
2. Look up `(generator.ID,index)`. If already present, turn a different selector into a Copy of the representative (`tuple.go:47-56`).
3. Otherwise, if in the wrong block, append a cloned selector to the generator’s block, turn the original into a Copy, and record the clone. If already colocated, record the original (`tuple.go:58-69`).

**Data structures:** Lookup-only map from `(ID,int)` to selector value (`tuple.go:15-18,47-69`).

**Parity traps (order dependence / nondeterminism):** First encountered selector wins—not necessarily an existing selector already in the generator’s block. Wrong-block selectors are **copied, not moved**; originals keep their IDs and positions as Copies. Clones append, consume free-list IDs, and use `Pos.WithNotStmt()`. `copyOf` adopts representative type, clears aux, and uncaches if needed (`tuple.go:43-69`; `value.go:429-458`). Go range captures the current slice length: appends to a later block can be visited when that block is reached, while appends to the current/already visited block do not create a new sweep (`tuple.go:19-20,60-64`). No map iteration (`tuple.go:50-69`).

**External state read:** Tuple/results types, `SelectN.AuxInt`, generator identity/block, allocator/constant-cache state, positions, and argument Uses. No ABI/frame/register-home reads (`tuple.go:27-41,50-69`; `value.go:429-458`).

**Depends on:** Exact value allocation and copy helpers; subsequent lowered deadcode cleans Copies; scheduler requires unique colocated selectors (`tuple.go:7-11`; `compile.go:501-502,569-570`).

**Proof strategy & difficulty:** **Parity S / proof M:** prove selector duplication/replacement preserves projection semantics and that moving projection to its generator block does not move the generator or its effects. Preserve the invariant of one non-Copy selector per `(generator,index)` (`tuple.go:43-69`).

**Issue summary:** Implement required index-42 selector repair using encounter-ordered `(generator,index)` canonicalization. Clone misplaced selectors into producer blocks, retain originals as Copies, clear clone statement marks, and reproduce ID/append/Uses effects. Follow with the existing required deadcode pass (`tuple.go:14-71`; `value.go:429-458`; `compile.go:501-502`).

**Proof (#385):** `GoFV.Proof.MoveL.tightenTupleSelectors_refinesL`
(`GoFV/Proof/Pass/TupleSelL.lean`): `tightenTupleSelectorsPass penv f = .ok out`,
`check ce f = .ok ()`, `check ce' out.func = .ok ()` and `moveB f out.func = true` give
`RefinesL out.tables out.func penv.tables f` (`runL`), through `refinesL_of_move` (see tighten):
the clone in the tuple's block is a total op (`Select0`/`Select1`/`SelectN`) with the selector's
op, type, aux, auxint and argument; the original, now `Copy clone`, and a later duplicate,
`Copy first`, stand for the source selector through `relB`'s copy case. The port's
`(generator, index)` map is a `Std.TreeMap` (lookup only, so parity is unchanged: quick-v7
9,297/9,297, full-v9 96,560/96,560) so that the kernel evaluates the pass. Witness
`GoFV.Proof.Witness.tupleSelL_witness` (`tupL`: `Select0 (ADDSflags x lo)` in the block after
the tuple's; the selector is cloned into the tuple's block, the output returns `5 + 3 = 8`).
Coverage (`lake exe move-probe`): quick-v7 9,297 sections, 8,643 checked, 7 changed, `moveB`
accepts 8,643 (0 rejections); full-v9 96,560 sections, 90,656 checked, 67 changed, accepted
90,656 (0 rejections); not counted: inputs failing `check` (654 and 5,904).

### lowered deadcode — issue #396

**Function / files:** Same `deadcode` implementation as Phase 1 and index 39 (`deadcode.go:161-313`; `compile.go:502`).

**Position & ordering:** Index **43**, **required**, immediately after tuple-selector tightening and before `checkLower`. Explicit constraint: `lowered deadcode → checkLower` (`compile.go:501-503,583-586`).

**Enabled (linux/arm64, default build):** Yes, including `-N`; fatal if `f.RegAlloc != nil`. No architecture branch (`compile.go:70-73,502`; `deadcode.go:161-168`).

**Size:** shared `deadcode.go` 360 / 249 code lines (Phase 1).

**What it does:**
1. Run the unchanged Phase 1 reachability, copy/phi elimination, liveness, names/positions, and freeing algorithm on lowered IR (`deadcode.go:170-313`).
2. Specifically clean duplicate definitions/Copies left by lowered CSE, unread-auto elimination, and tuple-selector repair before lower-validation (`compile.go:499-503`; `deadstore.go:480-485`; `tuple.go:50-64`).
3. Root ARM64 effects through opcode metadata, not a generic-op whitelist (`deadcode.go:110-135`).

**Data structures:** Same Phase 1 arrays, worklists, sparse set, inline-index map, and cached line map (`deadcode.go:22-158,216-279`).

**Parity traps (order dependence / nondeterminism):** All index-39 deadcode traps apply, especially freeing the original selector Copies in block/value order while retaining cloned selectors. The resulting free-list order is observable in LICM/critical block allocation and phi-tighten value allocation (`deadcode.go:281-313`; `func.go:397-454`; `tuple.go:60-64`). Embedded copyelim still executes under `-N` (`deadcode.go:209-212`; `compile.go:502`).

**External state read:** Same Phase 1 state plus lowered opcode effects and explicit RegAlloc nilness; no actual homes/frame allocation (`deadcode.go:61-135,166-168,216-249`).

**Depends on:** Shared deadcode/copyelim implementation, ARM64 effect metadata, preceding selector repair, and required cleanup before `checkLower` (`compile.go:501-503,585`).

**Proof strategy & difficulty:** **Parity S incremental / proof M incremental:** reuse the Phase 1 proof with ARM64 effects and tuple/CSE cleanup instantiated; maintain reachability, effect retention, and use-closed live sets (`deadcode.go:98-155,170-313`).

**Issue summary:** Wire the unchanged deadcode algorithm at required index 43, including under `-N`, to remove lowered duplicates and selector/unread-auto Copies before `checkLower`. Preserve ordered freeing, named values, statement relocation, and the nonnil-RegAlloc fatal check (`compile.go:501-503,585`; `deadcode.go:161-313`).

### checkLower — issue #397

**Function / files:** `checkLower`, `lower.go:22-53`.

**Position & ordering:** index **44**, required; immediately after required `lowered deadcode`, before `loop invariant`. Explicit predecessors are `lower`, `late lower` and `lowered deadcode` (`compile.go:501-503,585-589`).

**Enabled (linux/arm64, default build):** yes, including `-N`; independent of `checkEnabled`. ARM64 sets `hasGReg = true`, affecting the GetG exception (`compile.go:70-73,502`; `config.go:244`; `lower.go:39-43`).

**Size:** `lower.go:22-53`, 32 lines.

**What it does:**
1. Scan every block/value in stored order; accept every opcode whose table entry is not generic (`lower.go:26-30`).
2. Accept the explicit generic whitelist: SP, SPanchored, SB, InitMem, Arg, ArgIntReg, ArgFloatReg, Phi, VarDef, VarLive, KeepAlive, Select0, Select1, SelectN, Convert, InlMark, WBend (`lower.go:31-34`).
3. Accept MakeResult **only if it is `b.Controls[0]`**. Accept GetG only when `Config.hasGReg` is true (`lower.go:35-43`).
4. Otherwise fail on the first offending value, including its printed value/op/type and argument types in the diagnostic. Do not rewrite anything (`lower.go:45-50`).

**Data structures:** opcode metadata and ordered SSA slices only (`lower.go:26-50`).

**Parity traps (order dependence / nondeterminism):** not a claim that all generic opcodes disappeared; not a block-kind checker; not generic `check`. Earlier dead generic remnants must be removed before this phase. Preserve the exact whitelist and MakeResult control-identity check; first-error behavior is traversal-order dependent (`lower.go:23-50`; `compile.go:585-589`).

**External state read:** `opcodeTable[].generic`, `Config.hasGReg`; types and value printing only for failures. No register homes, frames, slots, loopnest or new autos (`lower.go:26-50`).

**Depends on:** lowering and subsequent deadcode; machine-op metadata generated with `generic` set only for generic architecture operations (`compile.go:585-589`; `_gen/main.go:418-424`).

**Proof strategy & difficulty:** **parity S; proof S.** Prove identity on accepted inputs and characterize acceptance exactly; separately prove the producer pipeline establishes this predicate. Acceptance alone does not prove machine-level semantic correctness (`lower.go:26-50`).

**Issue summary:** Implement required index-44 validation independently of debug checking: accept lowered ops plus the exact residual-generic whitelist, conditional MakeResult and ARM64 GetG exceptions; preserve first-error order and leave successful states unchanged. Parity/proof S (`compile.go:502`; `lower.go:22-53`).

### loop invariant — issue #398

**Function / files:** `licm`, `licm.go:36-159`; shared loop discovery `loopnestfor`, `likelyadjust.go:245-415`; reverse-use construction `uses.go:40-101`.

**Position & ordering:** Index **45**, optional, after `checkLower`, before late phi/copy elimination. No explicit `passOrder` constraint names LICM (`compile.go:503-505,530-614`).

**Enabled (linux/arm64, default build):** **Yes.** Its pass entry has no disabled/experiment guard; the implementation has no architecture or enable flag. It returns for no loops or any irreducible loop; skips non-leaf loops and headers without exactly two predecessors. Skipped under `-N` as an optional pass (`compile.go:70-73,504`; `licm.go:36-41,53-57,101-111`). The commented-out pass nearby is **merge conditional branches**, not LICM (`compile.go:507-508`).

**Size:** `licm.go` 159 lines / 96 code lines; shared `loopnestfor` (`likelyadjust.go:245-415`) and `uses.go` (109 / 51).

**What it does:**
1. Construct a **fresh** loop nest via `loopnestfor(f)`, using cached postorder/sparse dominators; reject irreducibility/no loops (`licm.go:36-41`; `likelyadjust.go:245-252`).
2. In leaf-loop blocks, seed dependent values except non-pointer `earlyOk` ops and `Select0`/`Select1`. For an `earlyOk` op, assert no memory result, nilcheck, side effect, or memory argument. Pointer-typed operations remain dependent even when marked early-safe (`licm.go:52-78`).
3. Propagate dependence through value users with a LIFO queue, restricted to leaf-loop blocks; block-control uses are not part of `uses` (`licm.go:81-98`; `uses.go:14-17,62-79`).
4. For each leaf-loop block with a two-predecessor header, move every unmarked value. Select header predecessor 0 if it lies outside the loop or its ID exceeds the original `b2l` array; otherwise select predecessor 1 (`licm.go:100-125`).
5. If the selected predecessor is not `BlockPlain`, append a Plain preheader, copy predecessor position, and splice reciprocal edge indices without changing header phi argument order. Append moved values to destination; nil old entries and compact each source stably (`licm.go:126-158`).

**Data structures:** Fresh `loopnest` containing ordered loops, `b2l`, postorder/sdom, headers/outer relationships/depth/inner flags; reverse-use arrays; dependent bool array; LIFO queue (`likelyadjust.go:15-60,245-252,375`; `licm.go:43-50`; `uses.go:33-36`).

**Parity traps (order dependence / nondeterminism):** `earlyOk` is an explicit opcode whitelist, **not** “all pure ops”; ARM64 ADD/division ops have it, while shown CMP and ADDSflags entries do not (`_gen/ARM64Ops.go:198-219,303-306`). Only `Select0/1` receive selector exemption, not `SelectN` (`licm.go:73-76`). Preserve source block/value order, stable compaction, first moved value’s preheader allocation, inherited block Pos, and original loop map throughout mutation. NewBlock invalidates Func caches, but LICM continues using its local old nest; newly appended blocks are outside the original range scan (`licm.go:100-158`; `func.go:419-443`). No value IDs are allocated, and moving values does not change argument Uses (`licm.go:142-145`).

**External state read:** Opcode `earlyOk`/effects, pointer/memory types, memory argument, current Uses for reverse-use construction, CFG/positions and cached postorder/dominators. No RegAlloc/Home, frame layout, ABI, or new autos (`licm.go:36-145`; `uses.go:40-59`; `likelyadjust.go:245-247`).

**Depends on:** Sound lowered early-execution metadata, shared loop discovery/dominators, reverse uses, and exact NewBlock/edge splice behavior. Unlike `tighten`, LICM does not store its fresh result in `f.cachedLoopnest` (`licm.go:38`; `func.go:795-809`).

**Proof strategy & difficulty:** **Parity M / proof L:** direct loop-invariant code-motion proof or validator checking each hoisted operation’s invariance and speculation safety, plus a stuttering simulation for inserted Plain preheaders. Crucial obligations are early-safe ARM64 semantics, pointer exclusion across safepoints, and selector movement with producers (`licm.go:59-76,100-158`).

**Issue summary:** Implement **enabled-by-default** index-45 LICM, limited to reducible leaf loops with two-predecessor headers. Port the exact earlyOk/non-pointer dependence closure, first-eligible-predecessor selection, lazy preheader creation, stable source compaction, and local-nest/cache behavior. Do not confuse its availability with the separately disabled merge-conditional-branches pass (`compile.go:504-508`; `licm.go:36-159`).

**Proof (#385):** `GoFV.Proof.MoveL.licm_refinesL` (`GoFV/Proof/Pass/LicmL.lean`):
`licmPass penv f = .ok out`, `check ce f = .ok ()`, `check ce' out.func = .ok ()`,
`check ce' (unhoist f out.func) = .ok ()`, `Crit.critRelB f (unhoist f out.func) = true` and
`moveB (unhoist f out.func) out.func = true` give `RefinesL out.tables out.func penv.tables f`
(`runL`). `unhoist f g` is `g`'s CFG with `f`'s value table and placement (the new preheaders
empty), so the pass splits into two validated steps composed by `RefinesL.trans`: preheader
insertion, an edge split by an empty `Plain` block (`GoFV.Proof.Crit.refinesL_of_critRel`, see
critical), then hoisting on a fixed CFG (`refinesL_of_move`, see tighten; hoisted values are
total ops). Witness `GoFV.Proof.Witness.licmL_witness` (`licmLoop`: a counting loop whose body
computes the invariant step `x + 1`; licm splits the non-`Plain` entry edge with a preheader
`b6`, hoists the step there, and the output returns 12 for `x = 2, n = 10`). Coverage (`lake exe
move-probe`, all three checked hypotheses): quick-v7 9,297 sections, 8,643 checked, 193
changed, accepted 8,643 (0 rejections); full-v9 96,560 sections, 90,656 checked, 3,300 changed,
accepted 90,656 (0 rejections); not counted: inputs failing `check`
(654 and 5,904).

### late phielim and copyelim — issue #399

**Function / files:** `copyelim`, `copyelim.go:10-32`; `copySource`, `copyelimValue`, `phielim`, `phielimValue` in `copyelim.go:36-157`. Identical to Phase 1 (`compile.go:459,505`).

**Position & ordering:** Index **46**, optional, after LICM and before tighten; no explicit `passOrder` constraint (`compile.go:504-506,530-614`).

**Enabled (linux/arm64, default build):** Yes; standalone instance skipped under `-N`, although required deadcode still invokes the same helper. No architecture switch (`compile.go:70-73,502,505`; `deadcode.go:209-212`).

**Size:** shared `copyelim.go` 157 / 93 code lines (Phase 1).

**What it does:**
1. Repeat block/value scans until no phi collapses: reset zero-sized struct/array values to Empty, bypass Copy arguments, and turn phis with one distinct non-self operand into Copies (`copyelim.go:100-155`).
2. Resolve copy chains with tortoise/hare cycle detection, resetting the meeting value to Unknown on a cycle, then path-compress (`copyelim.go:36-70`).
3. Replace Copy controls and ordered named-value entries by their immediate source; leave definitions for deadcode (`copyelim.go:10-32`).

**Data structures:** No new persistent structure; ordered IR traversal and local chain/fixpoint variables (`copyelim.go:10-32,36-70,100-155`).

**Parity traps (order dependence / nondeterminism):** Exactly the Phase 1 zero-size rewrite, cycle meeting-point dependence, fixpoint order, one-step control/name update, and Uses/uncache effects. No allocation/freeing or map iteration; names are processed through `f.Names` (`copyelim.go:24-31,49-68,100-155`).

**External state read:** Struct/array classification and size, names/named values, and debug flag; no lowered-op metadata, ABI, frame state, or register homes (`copyelim.go:24-31,107-108,150-152`).

**Depends on:** Phase 1 implementation and existing reset/argument/control mutators; later deadcode physically removes redundant definitions (`copyelim.go:9-21,74-80`).

**Proof strategy & difficulty:** **Parity S / proof M, reusable from Phase 1:** copy identity, redundant-phi semantics, zero-size value erasure, and unobservable unreachable copy cycles (`copyelim.go:36-70,100-155`).

**Issue summary:** Reuse Phase 1 copy/phi elimination unchanged at optional index 46; no separate ARM64 implementation is needed. Preserve zero-size resets, copy-cycle handling, fixpoint traversal, names/controls, Uses, and retained definitions (`compile.go:505`; `copyelim.go:10-157`).

### tighten — issue #400

**Function / files:** `tighten`, `tighten.go:14-176`; `memState`, `tighten.go:226-277`; LCA machinery `lca.go:36-134`; loopnest cache accessor `func.go:795-801`; `needRegister`, `regalloc.go:742-744`.

**Position & ordering:** Index **47**, required, before late deadcode. Explicit predecessors: `insert resched checks`, `generic deadcode`, and `generic cse` (`compile.go:506-509,536,558-560`).

**Enabled (linux/arm64, default build):** Yes. Required under `-N`, but returns immediately when `base.Flag.N != 0 && len(f.Blocks) < 10000`; at **10,000 blocks or more it still executes**. No architecture switch (`compile.go:70-73,506`; `tighten.go:14-20`).

**Size:** `tighten.go:14-176` plus `memState` (`tighten.go:225-277`); `tighten.go` 277 / 185 code lines including `phiTighten`; `lca.go` 127 / 85; shared loop nest.

**What it does:**
1. Compute block start/end memory states. Seed memory phis, InitMem, and incoming memory arguments; propagate backward FIFO through predecessors, selecting phi arguments by predecessor index. Reject conflicting starting memories (`tighten.go:25-32,226-277`).
2. Precompute movable values, excluding lowered closure-pointer retrieval, Phi/Arg/register Args/all selectors, and metadata nil checks. Count **distinct** register-needing args excluding SB/SP; reject ≥2 except when the result is flags (`tighten.go:34-73`).
3. Build dominator LCA support and get cached loopnest. Repeatedly compute each movable value’s use-block LCA; phi operand uses occur in the corresponding predecessor, controls in their own block (`tighten.go:76-123`).
4. Unless the CFG has irreducible loops, lift targets out of loops deeper than the value’s original loop by using the target loop header’s immediate dominator (`tighten.go:125-144`).
5. Move to a different nonnil target only if any memory argument equals target `startMem`. Append to destination, update `Value.Block`, swap-remove from source, re-examine the swapped slot; repeat to a fixpoint (`tighten.go:146-175`).

**Data structures:** `canMove`/`target` arrays keyed by value ID, start/end memory arrays by block ID, sparse distinct-argument set, LCA range-min structure, idom and cached loopnest (`tighten.go:22-32,76-86`; `lca.go:19-34`).

**Parity traps (order dependence / nondeterminism):** Movability and memory states are computed **once**, not recomputed after moves. `needRegister` excludes Memory/Void/Flags/Tuple exactly; do not substitute hardware allocation results (`tighten.go:22-86`; `regalloc.go:742-744`). Flags get the multi-input exception; flags-containing tuples do not. Memory-using values are not categorically excluded—target-start-memory equality governs movement. `tighten` does **not** call `rematerializeable`; that predicate belongs to phi tightening (`tighten.go:63-71,155-161,188`). Preserve append/swap-remove order and repeated scans; a value appended to a later block can be processed in that scan. For irreducible CFGs, only loop-depth target correction is skipped, not tightening itself (`tighten.go:127-175`). No IDs are allocated/freed and no Uses change (`tighten.go:166-174`).

**External state read:** `base.Flag.N`, opcode closure/nilcheck classifications, type register/flags/memory predicates, CFG/idom/loopnest contents, and debug flag. No RegAlloc/Home, physical register assignment, frame layout, stack slots, or new autos (`tighten.go:14-86,125-174`; `regalloc.go:742-744`).

**Depends on:** Phase 1 dominators/cache discipline, new cached loopnest support, LCA, sparse sets, memory-SSA interpretation. `memState` documents its limitation for infinite loops without memory operations; preserve its nil states rather than synthesizing memory (`tighten.go:203-225`; `func.go:795-809`).

**Proof strategy & difficulty:** **Parity M / proof L:** code-motion simulation or validator with definition-dominates-use, phi-edge use placement, memory-token equality, and unchanged effects. Loop-depth checks are profitability constraints; flags remain SSA values before flag allocation. Exact parity additionally requires fixpoint/list-order simulation (`tighten.go:94-175`).

**Issue summary:** Implement required index-47 tightening, including the precise `-N`/10,000-block guard. Port one-time movability/memory analysis, distinct-register-argument heuristic with flags exception, phi-edge LCA targets, reducible-loop depth correction, and append/swap-remove fixpoint movement. Reuse actual loopnest cache state; do not confuse this pass with rematerialization-based phi tightening (`tighten.go:14-176`).

**Proof (#385):** `GoFV.Proof.MoveL.tighten_refinesL` (`GoFV/Proof/Pass/TightenL.lean`):
`tightenPass penv f = .ok out`, `check ce f = .ok ()`, `check ce' out.func = .ok ()` and
`moveB f out.func = true` give `RefinesL out.tables out.func penv.tables f` (`runL`). Checked
wrapper over the fixed-CFG value-motion validator `moveB` (`GoFV/Proof/Pass/MoveLCheck.lean`,
shared with phi tighten, tighten tuple selectors and loop invariant):
`refinesL_of_move (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) (hm : moveB f g = true)
: RefinesL tabs g tabs f` (`GoFV/Proof/Pass/MoveL.lean`). `moveB` checks same entry, block list,
`ownAux` and `lowered`; per block the same kind, `auxInt`, edges and controls; a certificate of
related values (`okCert`, the greatest fixed point of `okLocal`, validated by `certValid`: an
in-place value of `g` has the source's op, type, aux, auxint, first-argument sign extension and
related arguments; a `Phi` stays in its block) and a relation `relB` (identity in the
certificate, a clone of a total op with the same arguments, or a `Copy` of a related value);
every value of a `g` block is a `Phi` or non-total value in place in the `f` block, or total
(`totalOp`: non-root ops whose non-faulting lowered evaluation is `.ok` for every argument list
and ignores the value's ID, `totalOp_ok`); and the panic order (`orderOK`: every call or nil check
of `f`'s schedule is in `g`'s, with every non-total value `g` evaluates before it evaluated
before it by `f`). The proof is a lock-step simulation on the same blocks and edges: per block
the source's schedule runs with the target fixed, then the target's (`phaseS`, `phaseT`), keeping
lemma (D) by IDs and agreement of related registers on the values placed in the dominators of
both sides. Witness `GoFV.Proof.Witness.tightenL_witness` (`clampTL`: lowered clamp with its
second `CMP` in the entry block; tighten moves it into `b2`, the output returns
`clamp(12, 0, 10) = 10`). Coverage (`lake exe move-probe`): quick-v7 9,297 sections, 8,643 with
input and output checked, 3,118 changed, `moveB` accepts 8,643 (0 rejections); full-v9 96,560
sections, 90,656 checked, 41,995 changed, accepted 90,656 (0 rejections). The sections not
counted have an input that fails `check` (654 and 5,904).

### merge conditional branches — issue #401

**Function / files:** `mergeConditionalBranches` and its private CFG/condition-conversion helpers, `merge_conditional_branches.go:59-890`.

**Position & ordering:** **not in the active `passes` array; no pass index**. Its commented entry sits between `tighten` and `late deadcode`, with “fix 80102 and re-enable”; it imposes no active ordering or execution obligation (`compile.go:505-508`). It must not shift the subsequent active pass indices.

**Enabled (linux/arm64, default build):** **no**, also not under `-N`; it is commented out, not merely debug-disabled. If called directly, its implementation returns for non-ARM64 (`compile.go:506-507`; `merge_conditional_branches.go:59-62`).

**Size:** `merge_conditional_branches.go` 890 lines / 590 code lines (not run).

**What it does:**
1. If explicitly invoked, traverse cached postorder and detect nested conditional diamonds or special cycle patterns, skipping chains of empty single-predecessor Plain blocks (`merge_conditional_branches.go:64-102,137-269`).
2. Prefer a movable true successor before a movable false successor. Require the inner condition to have one predecessor, admissible block/control forms, no phi/memory/side-effect/nil-check values, and matching phi arguments at the common successor (`merge_conditional_branches.go:164-179,271-395`).
3. Bypass empty Plain chains, marking removed blocks Invalid rather than immediately freeing them (`merge_conditional_branches.go:108-130,422-429`).
4. Normalize outer zero tests to CMP/CMPW against zero; normalize inner comparisons, materializing constants through the function constant cache as necessary (`merge_conditional_branches.go:492-553`).
5. Convert the inner comparison into CCMP/CCMN, possibly negate the outer block kind and swap successors; encode the outer condition and a false-case NZCV pattern. Prefer a representable second constant operand before the first when converting to a 5-bit immediate form (`merge_conditional_branches.go:600-738`).
6. Install the new control/likelihood, append inner values to the outer block while updating each `Value.Block`, remove the obsolete common-successor edge and corresponding phi arguments, invalidate CFG analyses, and leave the inner block Plain (`merge_conditional_branches.go:401-419,434-479`).

**Data structures:** cached postorder; ordered CFG edges/phis/values; constant cache; `arm64ConditionalParams` containing condition, NZCV, immediate flag/value (`merge_conditional_branches.go:70-80,434-465,530-553,615-648,691-738`).

**Parity traps (order dependence / nondeterminism):** **do not run this code in the requested pipeline**. For a separate future port, preserve cached postorder, true-before-false matching, constant-cache allocation, appended value order, edge/phi swap-removal, successor swaps and exact likelihood updates. Conditional NZCV uses architectural packing **N=bit3, Z=bit2, C=bit1, V=bit0**, unlike `flagConstant` (`merge_conditional_branches.go:70-80,164-179,434-479,807-825`; `rewrite.go:2331-2348`).

**External state read:** architecture, cached postorder, types, constant cache, opcode side-effect/nil-check properties, `Uses`, memory arguments, CFG and likelihoods. No register homes/frame layout are read by this pass (`merge_conditional_branches.go:59-80,324-395,470-553`).

**Depends on:** for direct invocation only: ARM64 conditional control forms, exact phi/edge operations, cached postorder, conditional-parameter encoding and constant materialization. It is not a dependency of the active Phase 2 pipeline (`compile.go:506-507`; `merge_conditional_branches.go:348-419`).

**Proof strategy & difficulty:** **active-pipeline parity S/proof S**: demonstrate absence from the pass list. **If separately enabled: parity L/refinement L**, requiring a CFG simulation for if-conversion/speculation, phi correspondence and conditional-flags truth tables. The source’s disabled status must not be presented as evidence that enabling it is sound (`compile.go:506-507`; `merge_conditional_branches.go:271-338,691-825`).

**Issue summary:** Document but do not implement or execute `merge conditional branches` as an active Phase 2 pass: the pinned compiler comments it out pending issue 80102. Its 890-line implementation performs ARM64 CCMP/CCMN if-conversion with cached-postorder matching, phi checks, value movement, conditional NZCV encoding and edge cleanup; any future enablement is a separate correctness/parity task (`compile.go:506-507`; `merge_conditional_branches.go:59-890`).

### late deadcode — issue #402

**Function / files:** Same Phase 1 `deadcode`, `deadcode.go:161-313`, with lowered metadata (`compile.go:509`).

**Position & ordering:** Index **48**, optional, after tighten and before critical-edge splitting. The commented merge-conditional-branches entry contributes **no index**. No explicit `passOrder` constraint names this deadcode instance (`compile.go:506-510,530-614`).

**Enabled (linux/arm64, default build):** Yes; skipped under `-N`; no architecture switch; nonnil RegAlloc is fatal. This instance still precedes flagalloc/regalloc (`compile.go:70-73,509-517`; `deadcode.go:161-168`).

**Size:** shared `deadcode.go` 360 / 249 code lines (Phase 1).

**What it does:**
1. Run the unchanged Phase 1 algorithm on the post-LICM/copyelim/tighten graph (`compile.go:504-509`; `deadcode.go:170-313`).
2. Apply lowered effect metadata to liveness and remove dead values/blocks while preserving statement boundaries and named values (`deadcode.go:110-155,216-313`).
3. Leave free-list state that the immediately following critical-edge splitter and later phi-tightener consume (`deadcode.go:281-313`; `critical.go:64,76`; `tighten.go:196`).

**Data structures:** Same Phase 1 liveness/reachability arrays, LIFO stack, sparse name set, inline-index set and cached line map (`deadcode.go:22-158,216-279`).

**Parity traps (order dependence / nondeterminism):** Incoming `b.Values` order now reflects tighten’s swap-removal and LICM’s append/stable compaction; do not normalize it before deadcode. This changes statement-discovery and freeing order even though the algorithm is unchanged (`tighten.go:166-174`; `licm.go:142-158`; `deadcode.go:98-155,261-313`).

**External state read:** Same lowered deadcode inputs: opcode effects, RegAlloc nilness, inline-position table, names and cached lines; no allocated register/stack locations (`deadcode.go:61-135,166-168,216-249`).

**Depends on:** Phase 1 deadcode plus exact incoming code-motion ordering; follows tighten and precedes critical (`compile.go:506-510`).

**Proof strategy & difficulty:** **Parity S incremental / proof M incremental:** reuse lowered deadcode obligations and prove preceding code motion still satisfies SSA/liveness assumptions (`deadcode.go:137-155,170-313`).

**Issue summary:** Reuse deadcode at optional index 48, off under `-N`, with ARM64 root metadata and unchanged fatal post-regalloc guard. Preserve the code-motion-produced value order because it controls statement relocation and the free-list state consumed by subsequent block/value creation (`compile.go:509-511`; `deadcode.go:161-313`).

### critical — issue #403

**Function / files:** `critical`, `critical.go:10-112`; shared `NewBlock`, `func.go:419-443`; predecessor/phi removal helpers invoked at `critical.go:93-96`.

**Position & ordering:** Index **49**, required, after late deadcode and before phi tighten. Explicit constraints: `critical → phi tighten`, `critical → layout`, `critical → regalloc` (`compile.go:509-514,571-576`).

**Enabled (linux/arm64, default build):** Yes, also under `-N`; no architecture switch (`compile.go:70-73,510`; `critical.go:10-112`).

**Size:** `critical.go` 111 lines / 68 code lines.

**What it does:**
1. Iterate by numeric index while `j < len(f.Blocks)`, including appended blocks. Skip blocks with ≤1 predecessor (`critical.go:14-20`).
2. Detect **exactly one** phi. If found, clear the per-argument-ID block table for its args; zero/multiple phis use ordinary independent splitting (`critical.go:22-41`).
3. Scan predecessors. Skip `p.Kind == BlockPlain`—the implementation tests kind, not successor count (`critical.go:44-51`).
4. Allocate a Plain splitter with predecessor Pos, or reuse the splitter recorded for the sole phi’s argument ID (`critical.go:54-81`).
5. First use splices `p→d→b`. Reuse adds `p→d`, removes `p` from `b.Preds`, removes the corresponding phi argument, and does not increment the predecessor index because removal swaps in an unprocessed edge (`critical.go:83-110`).
6. Continue through appended splitter blocks: a reused splitter may have multiple incoming edges and therefore itself needs splitting (`critical.go:14-16,61-64`).

**Data structures:** Scratch `[]*Block` indexed by phi-argument value ID; dynamically growing `f.Blocks`; existing reciprocal indexed edges and phi args (`critical.go:11-16,38-41,89-108`).

**Parity traps (order dependence / nondeterminism):** Same-argument grouping happens only with exactly one phi, and first predecessor encounter determines splitter ID/Pos. Preserve dynamic block-loop length, predecessor swap-removal, no-increment reuse branch, phi simplification side effects, and LIFO block allocation (`critical.go:22-41,54-110`; `func.go:419-443`). Do not replace the algorithm with one-new-block-per-edge: that produces different CFG/IDs/order. NewBlock clears CFG caches; no new values or autos are created by this pass (`func.go:419-443,803-809`; `critical.go:54-110`).

**External state read:** Block kinds, ordered preds/succs, exact phi count/argument IDs, predecessor positions, block allocator/free list, debug flag. No type/register/frame/ABI inspection (`critical.go:17-110`).

**Depends on:** Exact block allocation, indexed reciprocal-edge invariants, predecessor/phi swap-removal and phi simplification; establishes regalloc’s required critical-edge-free CFG (`critical.go:7-9,89-108`; `compile.go:575-576`).

**Proof strategy & difficulty:** **Parity M / proof M:** CFG stuttering simulation for Plain splitters; grouping proof uses equality of the sole phi’s incoming argument. Maintain phi-argument/predecessor alignment and reciprocal indices; prove all appended blocks are eventually processed (`critical.go:14-16,54-110`).

**Issue summary:** Implement required index-49 critical-edge elimination with its single-phi/equal-argument splitter reuse optimization, not naive per-edge splitting. Reproduce dynamic block iteration, allocation/Pos order, swap-removal and phi simplification, and cache invalidation; establish the no-critical-edge invariant needed by regalloc (`critical.go:7-112`; `compile.go:571-576`).

**Proof (#385):** `GoFV.Proof.Crit.critical_refinesL` (`GoFV/Proof/Pass/CriticalL.lean`):
`criticalPass penv f = .ok out`, `check ce f = .ok ()` and `critRelB f out.func = true` give
`RefinesL out.tables out.func penv.tables f` (`runL`). Checked wrapper: `critRelB` decides
`CritRel` (`critRelB_sound`): same entry, `ownAux`, `lowered` and value table up to positions,
use counts and `Phi` arguments (`eraseA`); every input block keeps kind, controls, values,
`auxInt` and ID, and its successor `k` reaches, through a chain of splitters (empty `Plain`
blocks, `SplitReach`; a shared splitter is itself split, so chains are longer than one), an edge
to the same block whose `Phi`s read the argument the source edge's read (`PhiArgs`).
`refinesL_of_critRel (hwf : WF ce f) (R : CritRel f g) : RefinesL tabs g tabs f` is a
macro-step simulation (`runLoopL_simIH`, equal frames at related block entries, the splitters
adding block entries that change nothing); licm composes it for its preheaders. Witness
`GoFV.Proof.Witness.criticalL_witness` (`maxL`, lowered `max(x, lo)` with a `Phi`: the edge
`b1 → b3` is split, the output returns `max(-3, 0) = 0` through the splitter). Coverage
(`lake exe critical-probe`): quick-v7 9,297 sections, 8,643 with input and output checked, 2,306
changed, `critRelB` accepts 8,643 (0 rejections); full-v9 96,560 sections, 90,656 checked,
30,193 changed, accepted 90,656 (0 rejections). The sections not counted have an input that
fails `check` (654 and 5,904).

### phi tighten — issue #404

**Function / files:** `phiTighten`, `tighten.go:181-200`; `Value.rematerializeable`, `regalloc.go:2923-2935`; `copyInto`, `value.go:446-458`.

**Position & ordering:** Index **50**, optional, immediately after critical and before likelyadjust. Explicit constraint: `critical → phi tighten`, so clones can be placed on split predecessor edges (`compile.go:510-512,571-572`).

**Enabled (linux/arm64, default build):** Yes; skipped under `-N`; no local `base.Flag.N` or architecture guard. Unlike `tighten`, it has no large-function `-N` exception (`compile.go:70-73,511`; `tighten.go:181-200`).

**Size:** `tighten.go:181-200` (20 lines), `Value.rematerializeable` (`regalloc.go:2923-2935`), `copyInto` (`value.go:446-458`).

**What it does:**
1. Scan blocks, phi values, and phi arguments in stored order (`tighten.go:182-187`).
2. Require the op’s rematerializeable bit and **every argument’s opcode fixedReg bit**; this is broader than literal constants and narrower than the op bit alone (`tighten.go:188-190`; `regalloc.go:2923-2935`).
3. If the argument is not already in the corresponding predecessor block, clone it into that block and replace only that phi argument (`tighten.go:191-196`).

**Data structures:** No worklist or deduplication table; existing phi/predecessor arrays and value allocator (`tighten.go:181-200`; `value.go:446-451`).

**Parity traps (order dependence / nondeterminism):** Clone separately for each eligible occurrence; do not memoize by predecessor/source or move the original. New clone appends, retains op/type/aux/auxint/args, but gets `Pos.WithNotStmt()`. Preserve clone-allocation and Uses-update order (`tighten.go:187-196`; `value.go:446-458`). ARM64 rematerializable ops include integer/float constants, MOVDaddr, and caller-PC; caller-SP’s op bit alone is insufficient when its memory argument is not fixedReg (`_gen/ARM64Ops.go:385-389,655-662`; `regalloc.go:2923-2935`). Original values are not deleted (`tighten.go:181-200`).

**External state read:** Opcode `rematerializeable`/`fixedReg`, source block, predecessor order, types/aux/positions, allocator state. Despite helper location in `regalloc.go`, it reads **no `f.RegAlloc` or Home** and creates no autos/stack slots (`regalloc.go:2923-2935`; `value.go:446-458`).

**Depends on:** Critical-edge splitting, lowered opcode metadata, and exact cloning/allocation. The helper rejects cloning values with memory-typed arguments (`compile.go:571-572`; `value.go:452-456`).

**Proof strategy & difficulty:** **Parity S / proof M:** prove eligible expressions can be recomputed from universally available fixed-register arguments; relate each clone to its source along the phi predecessor edge. Include symbolic-address and caller-PC semantics rather than proving only literal constants (`regalloc.go:2923-2935`; `_gen/ARM64Ops.go:385-389,655-662`).

**Issue summary:** Implement optional index-50 phi argument cloning after critical-edge splitting. Use exact rematerializeable-plus-fixedReg eligibility, clone per occurrence without deduplication, preserve appended value/ID order and cleared statement marks, and update only the selected phi edge. No physical allocation or frame changes occur (`tighten.go:181-200`; `regalloc.go:2923-2935`; `value.go:446-458`).

**Proof (#385):** `GoFV.Proof.MoveL.phiTighten_refinesL` (`GoFV/Proof/Pass/PhiTightenL.lean`):
`phiTightenPass penv f = .ok out`, `check ce f = .ok ()`, `check ce' out.func = .ok ()` and
`moveB f out.func = true` give `RefinesL out.tables out.func penv.tables f` (`runL`), through
`refinesL_of_move` (the value-motion validator, see tighten): a clone in the predecessor is a
total op with the source value's op, type, aux, auxint and arguments, and the `Phi` reading it
is related to the source `Phi` edge-wise. Witness `GoFV.Proof.Witness.phiTightenL_witness`
(`phiTL`: `Phi (MOVDconst [7]) x` after an `EQ` split into two `Plain` predecessors; the
constant is cloned into `b2`, the output returns 7 for `x = 0`). Coverage (`lake exe
move-probe`): quick-v7 9,297 sections, 8,643 checked, 280 changed, `moveB` accepts 8,643 (0
rejections); full-v9 96,560 sections, 90,656 checked, 6,018 changed, accepted 90,656 (0
rejections); not counted: inputs failing `check` (654 and 5,904).

### likelyadjust — issue #405

**Function / files:** `likelyadjust` (`likelyadjust.go:83-209`); shared loop representation and construction: `loop`, `loopnest`, `SparseTree.outerinner`, `nearestOuterLoop`, `loopnestfor`, `loopnest.depth` (`likelyadjust.go:11-56,225-424`). `f.loopnest()` lazily stores the result in `f.cachedLoopnest` (`func.go:795-801`).

**Position & ordering:** index **51**, optional, after `phi tighten` and before `layout`; no explicit `passOrder` constraint naming this pass (`compile.go:511-513,530-614`).

**Enabled (linux/arm64, default build):** yes; skipped under `-N` because not required. No architecture switch; debug/stats affect reporting, not branch choices (`compile.go:70-74,512`; `likelyadjust.go:151-186,203-205,377-414`).

**Size:** `likelyadjust.go` 424 lines / 314 code lines: the pass `likelyadjust.go:83-209`, loop nest construction `likelyadjust.go:225-424` (shared with LICM, tighten, regalloc, loop rotate).

**What it does:**
1. Obtain cached postorder and loopnest; allocate zero-filled `certain` and `local` block-ID arrays. Costs are default=0, call=1, return=2, exit=3 (`likelyadjust.go:58-64,83-97`).
2. Construct loopnest if absent: walk cached postorder and each block’s successors in stored order. A successor dominating the current block is a loop header; create its loop on first discovery. A nondominating, unvisited successor marks the function irreducible. For visited successors already in a loop, climb outward until a header dominates the current block. Link candidate loops by header dominance, choose the innermost, assign `b2l[b.ID]`, and increment that loop’s exclusive `nBlocks` (`likelyadjust.go:245-332`).
3. Compute `int16` depths by walking outer links, memoizing depths along each chain; verify parent-depth consistency. Preserve loops in **discovery order**: construction does not sort them. `isInner` becomes false when an inner loop is linked; `containsUnavoidableCall` is initially false and is computed later by regalloc, not here (`likelyadjust.go:17-23,27-47,334-375`; `regalloc.go:3556-3609`).
4. Walk postorder once. Exit gets local/certain=3; Ret/RetJmp get 2; Defer gets local=1 and certain=`max(1,certain[succ0])`. Other one-successor blocks inherit successor certainty; two-successor blocks take the minimum certainty (`likelyadjust.go:99-132`).
5. For two-successor blocks, prefer staying in a loop: if source is in a loop and destination loops differ, prefer a nonnil destination loop over no loop, then the destination in the source’s exact loop. This branch can produce **no prediction without falling back** to cost heuristics. Otherwise prefer lower `certain`, then lower `local`; ties retain the old prediction. Only overwrite `BranchUnknown`, never an existing prediction (`likelyadjust.go:134-193`).
6. In the default block-kind case, scan values for the first opcode marked `call`; set local=1 and overwrite certainty with `max(1,certain[succ0])`. Panic detection is structural (`BlockExit`), not symbol-name classification; the source explicitly leaves name-sensitive call heuristics unimplemented (`likelyadjust.go:100-116,195-201`).

**Data structures:** cached postorder/sparse dominator tree; ordered loop slice; block-ID→innermost-loop array; loop outer links, header, exclusive block count, depth, inner flag and unavoidable-call flag; scratch visited/certain/local arrays (`likelyadjust.go:11-64,89-97,245-253`).

**Parity traps (order dependence / nondeterminism):** loop discovery and prediction depend on cached postorder, successor order and zero defaults for unvisited backedges. Do not recompute an already cached analysis merely because a different traversal looks preferable. No loop sort occurs here; later rotation sorts a separate index slice. Calls overwrite certainty using **successor 0**, not the previously calculated minimum. Existing likelihoods are authoritative. No SSA value/block allocation or freeing, no Uses mutation, and no observable map iteration occurs in this pass (`likelyadjust.go:99-209,245-375`; `func.go:766-809`; `looprotate.go:83-101`).

**External state read:** block kinds, successors, existing likelihoods, opcode `call` metadata, cached postorder/idom/sdom/loopnest, pass debug/stats. No register allocation, stack layout, ABI or new-auto access (`likelyadjust.go:83-209,245-414`; `func.go:766-801`).

**Depends on:** postorder, dominance/sparse-tree ancestry and exact cache policy; downstream layout reads `b.Likely`, while regalloc and rotation consume loopnest (`likelyadjust.go:95-97,245-247`; `layout.go:130-141`; `regalloc.go:3556-3609`; `looprotate.go:29-35`).

**Proof strategy & difficulty:** parity **M**, proof **S** for the pass’s semantic effect: direct simulation of metadata changes, with an erasure theorem that branch prediction does not change CFG execution. Prove loop construction separately if later proofs rely on its structural meaning; for parity, preserve its actual treatment of irreducible loops rather than substituting an ideal loop algorithm (`likelyadjust.go:49-56,134-201,245-375`).

**Issue summary:** Port optional pass #51 and its cached loopnest support; implement postorder/successor-order loop discovery, exact outer-link/depth construction, and one-pass likelihood costs with existing predictions preserved. Loop construction is unsorted, panic detection uses Exit blocks, and calls use opcode metadata rather than names. Export cached loopnest contents because downstream passes consume them; unavoidable-call analysis belongs to regalloc. Difficulty M parity/S semantic preservation (`compile.go:512`; `likelyadjust.go:83-209,245-375`; `regalloc.go:3556-3609`).

### layout — issue #406

**Function / files:** `layout`, `layoutOrder`; `layoutRegallocOrder` returns the existing `f.Blocks` unchanged (`layout.go:10-21`). Sparse-set operations are shared (`sparseset.go:34-79`).

**Position & ordering:** index **52**, required, between likelyadjust and schedule. Explicit constraint: `critical`→`layout` (`compile.go:512-514,574-575`).

**Enabled (linux/arm64, default build):** yes, including `-N`; no architecture or optimize branch in the algorithm (`compile.go:70-74,513`; `layout.go:21-188`).

**Size:** `layout.go` 185 lines / 126 code lines; shared sparse set.

**What it does:**
1. Build ID→block mapping and an insertion-ordered sparse set of `BlockExit` blocks, scanning `f.Blocks`. Repeatedly add predecessors all of whose successors are already in this set; each range over `exit.contents()` sees that range’s initial slice length, so newly appended entries are fully processed on subsequent iterations (`layout.go:41-75`).
2. For non-exit-set blocks, initialize indegree from predecessor count; append zero-degree IDs to a LIFO slice, positive-degree IDs to a sparse set. Start unconditionally at `f.Entry.ID` (`layout.go:77-92`).
3. Append the chosen block and mark it scheduled. Unless all blocks have now been emitted, walk its successors **backwards**, decrementing indegrees; a newly zero-degree target is removed from `posdegree` and pushed onto `zerodegree`, otherwise pushed onto `succs` (`layout.go:93-124`).
4. Choose the next unscheduled block in this priority order: predicted successor; pop zero-degree stack; pop most-recently-encountered successor stack; pop positive-degree sparse set; pop exit sparse set. Ignore already scheduled entries. In particular, predicted/successor-stack choices are not filtered by exit membership, despite the “exit blocks … last” initialization comment (`layout.go:78-89,126-182`).
5. Set `f.laidout=true`; return order, then assign it to `f.Blocks`. Do not change successors, block IDs or value schedules (`layout.go:10-12,183-188`).

**Data structures:** ordered result, ID→block, scheduled bools and indegree arrays; two LIFO ID slices; insertion-ordered/swap-remove sparse sets `posdegree` and `exit` (`layout.go:21-39`; `sparseset.go:34-79`).

**Parity traps (order dependence / nondeterminism):** original `f.Blocks`, predecessor order during exit expansion, reverse successor traversal, stack order, sparse-set swap-remove/pop, and stale stack entries all matter. This is not “pick minimum indegree,” ID sorting, or arbitrary topological sorting. The last scheduled block does not run successor updates. No Go map, sort, SSA allocation/freeing or Uses changes (`layout.go:41-184`; `sparseset.go:55-70`).

**External state read:** Entry, block/pred/succ order and kinds, `b.Likely`; no types, ABI, registers, stack layout, loopnest or frontend queries. It writes the persistent `laidout` bit (`layout.go:21-184`; `func.go:46-47`).

**Depends on:** critical-edge removal by declared ordering, likelyadjust’s predictions when enabled, shared sparse-set behavior; resulting order is also regalloc’s layout order (`compile.go:574-575`; `layout.go:14-18,130-141`).

**Proof strategy & difficulty:** parity **M**, proof **S**: exact worklist simulation plus a permutation/uniqueness invariant; block-order changes preserve explicit-edge CFG semantics. Assembly fallthrough correctness is a separate consumer obligation (`layout.go:7-18,93-184`).

**Issue summary:** Port required pass #52 as its exact multi-worklist algorithm, not an abstract topological sort. Preserve reverse successor processing, likely-edge priority, exit-set closure and sparse-set swap/pop ordering; replace only `f.Blocks` and set `laidout`. No new IDs or ABI dependencies. M parity/S proof (`compile.go:513`; `layout.go:21-188`).

### schedule — issue #407

**Function / files:** `schedule` (`schedule.go:107-373`); score constants, `ValHeap`, closure-pointer classification (`schedule.go:16-100`); shared `storeOrder`, flag classifiers and position comparator (`schedule.go:397-599`). **`schedule` does not call `storeOrder`**; it constructs its own scheduling edges (`schedule.go:107-373,397-559`).

**Position & ordering:** index **53**, required, after layout. Explicit constraints: tighten tuple selectors→schedule; schedule→regalloc, late nilcheck and flagalloc (`compile.go:514,570-571,578-579,588-591`).

**Enabled (linux/arm64, default build):** yes, also under `-N`. `Config.optimize` only enables precomputation of `inBlockUses`; under `-N` all those bits remain false, changing the heap heuristic. ARM64 closure-pointer recognition is included; PPC64-specific carry classifications do not apply to ARM64 (`schedule.go:92-100,124-136,562-589`; `compile.go:70-74,514`).

**Size:** `schedule.go` 599 lines / 421 code lines: the pass `schedule.go:107-373`, scores and `ValHeap` `schedule.go:16-100`, `storeOrder` (Phase 1, shared) from `schedule.go:397`.

**What it does:**
1. With optimization enabled, mark arguments used by values in their own block; block controls do not count. Phi arguments are included in this heuristic scan even though phi edges are excluded from the scheduling graph (`schedule.go:120-136,244-258`).
2. Assign ordered scores 0–10: Phi, Arg, InitMem, ReadTuple, NilCheck, Memory, ReadFlags, Default, Flags, InductionInc, Control. Classification priority is closure pointer→nilcheck→Phi→register args→Arg/SP/SB→InitMem→memory result→tuple selector→flag input→flag output→induction increment→default. Closure pointers and register args receive **Phi score**, not Arg score, and must be in Entry (`schedule.go:16-28,138-215`).
3. Recognize an induction increment as a unary value whose argument is a multiply-used phi, with a sole successor equal to the phi’s block and the corresponding phi edge argument equal to the increment. Give eligible local controls Control score, except earlier special classes; for a tuple-selector control, score its generator Control instead (`schedule.go:190-228`).
4. Build local argument→user edges, excluding phi users. Build memory-input→next-memory-result lookup from non-Phi/non-InitMem memory values. For each nonmemory/non-Phi value with a memory argument, add value→next-store when that store is local. Sort edges by source ID and count incoming edges (`schedule.go:231-286`).
5. Push initially ready values in original `b.Values` order. Repeatedly pop minimum priority, append it, find its outgoing edge interval by two binary searches, decrement incoming counts and push newly ready values. Fatal if not all original values were scheduled (`schedule.go:288-325`).
6. Heap priority is score ascending; in-block-used before not; raw XPos order; for non-Phi ties, argument count descending; Uses descending; **signed `AuxInt` subtraction** ascending; `Type.Compare`; finally ID ascending. Preserve Go arithmetic behavior rather than replacing subtraction with an overflow-free mathematical comparison (`schedule.go:53-89`).
7. Across all blocks, repeatedly bypass SPanchored and nilcheck arguments in value args and controls. Then scan schedules: SPanchored must have zero Uses, is resetArgs/freeValue’d and removed; nilchecks must have zero Uses and become `TypeVoid`, but remain in the schedule. Compact and set `f.scheduled=true` (`schedule.go:327-373`).
8. Shared `storeOrder`: identify the unique final memory store, number its chain backwards in multiples of three, DFS-number other values by latest local store dependency (Phi=2; generic NilCheck=`3n+1`, other=`3n+2`), and stable-bin original values by number. Sort each contiguous generic-NilCheck run by position. Early return for no stores, or no generic NilCheck when pass name is `"nilcheckelim"`; scratch store numbers must have the caller’s expected zero state (`schedule.go:397-559`).

**Data structures:** reusable `ValHeap`, per-value score/in-block-use/in-edge-count/next-memory arrays; ordered edge slice; `storeOrder` additionally uses sparse set, store list, DFS stack, store-number array and counting bins (`schedule.go:30-35,107-136,231-242,397-537`).

**Parity traps (order dependence / nondeterminism):** heap comparator and Go integer subtraction are part of parity. `Pos !=` followed by `Before` is the actual comparator branch. Equal-source edge sorting is unstable; preserve the upstream sort rather than assuming stable edge order. `nextMem` persists between block iterations but uses a destination-block check. SPanchored free-list pushes follow **scheduled** block/value order, after the whole-function bypass stage. Nilchecks are retained with changed types. `storeOrder`’s position sort permits ties and needs Go’s deterministic unstable-sort behavior; its name-sensitive shortcut is not part of `schedule` itself (`schedule.go:53-89,260-285,327-373,424-427,538-555`).

**External state read:** `Config.optimize`, opcode nilcheck metadata, ARM64 closure op identity, flag/tuple/memory types, `Type.Compare`, full positions, AuxInt, Uses, CFG phi edge indices, and allocator/free-list state. It does not inspect register assignments, frame layout, ABI, or loopnest. Debug-info ordering motivates Arg/InitMem scores but is not a debug-info query (`schedule.go:124-228,327-373`; `value.go:446-455`).

**Depends on:** lowered operations and tightened tuple selectors; typed memory-chain correctness; generic heap/sort primitives; argument/control setters, freeValue and truncateValues. It supplies the ordered instruction lists required by late nilcheck, flagalloc and regalloc (`compile.go:570-571,578-591`; `schedule.go:244-325,327-373`; `block.go:269-272`).

**Proof strategy & difficulty:** parity **L**, proof **L**: direct simulation for exact heap/list state; a validator can separately check the resulting order against data and memory precedence constraints. The semantic proof needs operation commutation, phi-edge treatment, tuple/flag scheduling constraints and correct preservation of fault order; SPanchored/nilcheck result bypass needs an identity-on-success lemma and retained nilcheck execution (`schedule.go:150-187,244-279,327-373`). Plan (`docs/plans/semantics2.md` §6): this is the L0 → L1 boundary; prove `Refines (runSched f') (run f)` from a validator (topological, memory-linear order of each block), after settling the ready-root order (#96).

**Issue summary:** Port required pass #53 with exact scores, heap comparator, memory antidependencies, optimize-dependent in-block-use heuristic and post-scheduling SPanchored/nilcheck unlinking. Preserve free-list order and Void typing of surviving nilchecks. Reuse/port `storeOrder` as a distinct shared helper, including name-sensitive early return and position-sort ties. L parity/L proof (`compile.go:514`; `schedule.go:16-89,107-373,397-599`).

**Proof (#385):** `GoFV.Proof.SchedL.schedule_refinesSchedLF (h : schedulePass penv f = .ok out) (hf : check ce f = .ok ()) (hv : scheduleCheck penv.tables f out.func = true) : RefinesSchedLF out.tables out.func penv.tables f` (`GoFV/Proof/Pass/SchedLPass.lean`): every returning or panicking `runLF` of the input (`runL`'s `kahn` order with memory ops faulting: an access through a nil base in the nil page panics with `nilDeref`, a nil check of a wild pointer is `stuck`) is matched, up to `OutcomeRefines 0`, by a `runSched` of the output. Corollary `schedule_refinesSchedL … : RefinesSchedLFrom (NoNilFault penv.tables f) out.tables out.func penv.tables f` (a `runL` refinement on the inputs where `runL` and `runLF` agree; `GoFV.Proof.runLF_cases`, `GoFV/Proof/RunLFCases.lean`: a `runLF` run is `runL`'s, or `stuck`, or a `nilDeref` panic finished by the deferred calls; `noNilFault_of_noAct`: a function without memory ops and nil checks has no such input). Checker: the validator `scheduleCheck` (`GoFV/Opt/ScheduleCheck.lean`), decision (b) of #96: shape (the output has the input's blocks, kinds, `auxInt`s and edges; each block lists a permutation of the input's values minus the `SPanchored`s; arguments and controls are the input's bypassed one step by `rep`, a nil check's pointer of a compatible shape, an `SPanchored` only as the base of a symbolic address, `useOK`), order (`runSched`'s order of each block exists and is a dependency order, and values that may fail keep `runL`'s order up to `swapOK`: the source's first value never panics, or both are loads/nil checks on the same memory, a moved nil check being of the same base). Proof: lock-step simulation (`refinesSchedLF_of_rel`, `GoFV/Proof/Pass/SchedLSim.lean`) with the invariant `AtS` (frames agree off nil checks and `SPanchored`s, lemma (D) of the source, the nil-check equation of the `Phi` arguments at the predecessor); per block `walk_ok`/`walk_panic` (`SchedLWalk.lean`: before the source's panicking value the target runs values the source ran, values that never fail, or values `swapOK` lets it run first, which evaluate or panic with the same `nilDeref`), the class lemmas in `SchedLEval.lean`, the checker's propositions in `SchedLRel.lean`, the value step in `SchedLBlock.lean`. Witnesses `GoFV.Proof.Witness.schedule_witness` (`schedule` on lowered `clamp` lists `b1` as Go does, `scheduleCheck` accepts, the output's `runSched` returns `clamp(5, 0, 10) = 5`) and `schedule_refinesSchedL_witness` (`GoFV/Proof/Witness/ScheduleL.lean`). Coverage (`lake exe schedl-probe`): quick-v7 9,297 `schedule` sections, all inputs pass `check`, 8,956 accepted (96.3%); full-v9 96,560 sections, all inputs pass `check`, 88,680 accepted (91.8%). Every rejection is the order rule (339 quick-v7, 7,875 full-v9) except 2 / 5 `value args` (a two-step bypass), almost all a load that the source runs before a nil check of a different pointer that Go schedules first (269 / 7,008; the nil check could be `stuck` on a wild pointer where the source panics at the load); in 140 / 3,090 the load's base is itself a nil check's result, so it cannot fault (next step: a `swapOK` case for it), 17 / 132 move an `ArgIntReg` before a load.

### late nilcheck — issue #408

**Function / files:** `nilcheckelim2`, `minZeroPage`, `faultOnLoad` (`nilcheck.go:190-354`); shared sparseMap, cached line-start map, statement-boundary predicate and truncateValues (`nilcheck.go:200-203,326-349`).

**Position & ordering:** index **54**, optional, immediately after schedule and before flagalloc; explicit schedule→late nilcheck constraint (`compile.go:514-516,588-589`).

**Enabled (linux/arm64, default build):** yes; skipped under `-N`. `faultOnLoad = GOOS != "aix"`, so true on linux. `fe.Debug_checknil()` only emits removed-check warnings for positions with line>1 (`compile.go:70-74,515`; `nilcheck.go:195,215-218`).

**Size:** `nilcheckelim2` `nilcheck.go:199-338` (about 140 lines); `nilcheck.go` 338 / 214 code lines with Phase 1's `nilcheckelim`.

**What it does:**
1. Per block clear pointer-ID→faulting-value-index sparse map and pending statement lines. Scan scheduled values backwards; initialize first removal index to block length (`nilcheck.go:200-214`).
2. If a nilcheck’s pointer is recorded, transfer its position to the recorded faulting instruction when file/line differs, saving a displaced IsStmt position; for same-file/line, record an IsStmt nilcheck position instead. Reset nilcheck to Unknown, update first removal index, and continue without processing it as a faulting instruction. Backward traversal makes the earliest eliminated check in a chain win position transfer (`nilcheck.go:215-239`).
3. For memory results or tuples whose field 1 is memory, clear the fault map, **except** VarLive and VarDef of a variable whose type has no pointers, which immediately continue. Pointer-bearing VarDef is a barrier to avoid moving a fault into the live-but-uninitialized-pointer interval (`nilcheck.go:240-269`).
4. After any barrier clear, collect pointers from opcode `faultOnNilArg0/1`. Linux accepts loads and stores; AIX accepts only writes, with the special PPC64LoweredMove argument-1 exception (`nilcheck.go:272-283`).
5. Check aux addressing: Sym requires nil symbol; SymOff requires nil symbol and `0≤AuxInt<4096`; SymValAndOff uses decoded offset with the same bounds. Int32/Int64 are accepted as non-address-offset metadata; None/SizeAndAlign mean offset zero. Other aux kinds are fatal. Record the current index for each qualifying pointer (`nilcheck.go:285-323`).
6. Compact only from the first removed index, omitting Unknowns. Transfer pending IsStmt marks to matching surviving non-boundary-excluded values, then to matching block position; truncate. No cross-block search, no freeValue, and no new value allocation (`nilcheck.go:325-354`; `block.go:269-272`).

**Data structures:** sparse map keyed by exact pointer value ID, with nearest encountered qualifying fault index; shared `f.cachedLineStarts` scratch map; two-element pointer scratch storage; first-removal index (`nilcheck.go:200-213,273-274,321-349`).

**Parity traps (order dependence / nondeterminism):** exact pointer identity, not pointer-expression equivalence; backward scan controls replacement fault and winning position. Clear memory barrier **before** recording that same instruction’s fault behavior, so a faulting store can itself justify an earlier check. Removed values are reset/detached but not freed: do not push them onto the free list. Preserving statements scans only the suffix beginning at first removal. No map-iteration choice affects the pass (`nilcheck.go:215-349`).

**External state read:** GOOS-derived faultOnLoad, opcode nilCheck/faultOnNilArg/auxType, tuple/memory classification, symbols and packed offsets, VarDef’s `*ir.Name.Type().HasPointers()`, cached line ranges, XPos and frontend Debug_checknil. **No `unsafePoint` test exists here**: ARM64 atomics can simultaneously carry fault-on-nil and unsafe-point metadata. Unsafe-for-async-preemption must not be invented as an additional elimination barrier; pointer initialization safety is enforced by the memory/VarDef rule (`nilcheck.go:195-349`; `op.go:47`; `_gen/ARM64Ops.go:693-695,734-735,758-763`).

**Depends on:** scheduling’s established execution order and pointer-result unlinking, ARM64 opcode fault contracts, Linux zero-page guarantee, shared statement-preservation state (`compile.go:588-589`; `schedule.go:327-373`; `nilcheck.go:190-195,240-323`).

**Proof strategy & difficulty:** parity **M**, proof **L**: direct simulation plus a fault-preservation invariant—every removed check is covered by a guaranteed fault on the same nil pointer before an intervening observable memory effect or pointer-initialization safety boundary. Architectural fault contracts, panic position and atomic unsafe-point behavior must be modeled explicitly, rather than assuming all memory operations fault identically (`nilcheck.go:190-195,219-323`; `_gen/ARM64Ops.go:734-735`). Plan (`docs/plans/semantics2.md` §6): proven over `runSched`, whose `faultOnNilArg` ops panic on nil pointers below `minZeroPage`.

**Issue summary:** Port optional pass #54 as a backward intra-block fault analysis with exact aux-offset qualification and statement-position transfer. Preserve VarLive/pointer-free VarDef exceptions, pointer-bearing VarDef safety, Linux load-fault behavior and the absence of an unsafePoint barrier. Removed nilchecks are reset/detached, not freed. M parity/L proof (`compile.go:515`; `nilcheck.go:190-354`).

### flagalloc — issue #409

**Function / files:** `flagalloc`, `Value.clobbersFlags`, recursive `copyFlags` (`flagalloc.go:10-278`); `Value.copyInto` (`value.go:446-455`); architecture-specific `Config.splitLoad` hook (`config.go:28,185-186,206-207`).

**Position & ordering:** index **55**, required, immediately before regalloc. Explicit schedule→flagalloc and flagalloc→regalloc constraints; critical-edge absence is also an implementation precondition (`compile.go:516-517,590-593`; `flagalloc.go:119-127`).

**Enabled (linux/arm64, default build):** yes, including `-N`. ARM64 config does **not** install splitLoad; AMD64 and 386 do. Therefore the memory-dependent spilled-flag split path must be unreachable for valid ARM64 input, not silently emulated with a fallback (`compile.go:70-74,516`; `config.go:185-186,206-207,230-251`; `flagalloc.go:134-141`).

**Size:** `flagalloc.go` 270 lines / 203 code lines (`flagalloc` from :10, `clobbersFlags` :243, `copyFlags` :258).

**What it does:**
1. Run **exactly two** cached-postorder backward analyses. Initialize wanted flags from the sole flags-typed control, otherwise `end[b]`; backwards through values clear on reaching the wanted definition or a flag clobber, then overwrite wanted with each flags argument in argument order. Propagate a remaining wanted value to all predecessors by assignment, so later visits overwrite earlier requests (`flagalloc.go:14-55`).
2. Clear end state for Defer blocks and for blocks whose flags control disagrees with their requested end value (`flagalloc.go:57-71`).
3. Forward-simulate each block beginning with predecessor 0’s end value. Mark every mismatched flags operand/control/end value in `spill`; clear at clobbers, set at flags definitions (`flagalloc.go:73-108`).
4. Rebuild each schedule. Require all predecessor end states equal and reject flag phis. For a spill-marked memory-consuming flag generator, add it to removal candidates and call splitLoad. For each flags arg not currently available, recursively copy its flags/tuple dependency tree into this block and replace the arg. Append the original value; update logical current flag using the **original** flag identity (`flagalloc.go:110-168`).
5. Rematerialize mismatched flag controls with ReplaceControl, and required outgoing flags with an unlinked appended copy. The latter intentionally breaks ordinary SSA def-use representation: the physical flag is live although successor operands are not rewired to that emitted copy (`flagalloc.go:169-191`).
6. Write `FlagsLiveAtEnd`. Process removal candidates in order: zero-Uses values reset Invalid; nonzero candidates are swap-removed from the candidate list, then the swapped entry is reprocessed. Compact Invalid values out of affected blocks in original schedule order. There is no freeValue call (`flagalloc.go:194-247`).
7. `clobbersFlags` is true for opcode metadata or a tuple with flags in field 0 or 1. `copyFlags` recursively copies every flags- or tuple-typed argument in index order, copies the parent, then replaces those args through a temporary index map. `copyInto` keeps aux/type/op, clears statement marking, adds original args and rejects direct memory args (`flagalloc.go:249-278`; `value.go:446-455`).

**Data structures:** per-block end-value array; flags-ID→spill bool map (membership/update only); old-schedule/removal slices; affected-block sparse set; recursive index→copied-value maps (`flagalloc.go:14-16,74,110-111,228-232,267-277`).

**Parity traps (order dependence / nondeterminism):** two iterations are not a fixpoint; cached postorder and predecessor/argument order matter. Repeated recursive dependencies are copied repeatedly, not memoized. Allocations are child-before-parent in arg order and consume exact free-list IDs; statement bits become NotStmt. `copyFlags`’s map iteration only replaces already allocated arguments at distinct indices, so final args/Uses are order-independent. Removal-candidate swap deletion and cascading Uses changes matter; this is limited cleanup, not general deadcode. Unlinked outgoing rematerializations must be retained even with zero Uses (`flagalloc.go:17-55,143-191,204-247,267-278`; `value.go:446-455`).

**External state read:** cached postorder, opcode clobberFlags, flags/tuple/memory types, Config.splitLoad, Uses, allocator state and original positions/aux. It allocates **no stack flag-spill slots**: “spilling” means recomputation. No RegAlloc/Home/frame/ABI query occurs; `FlagsLiveAtEnd` is the persistent output for later allocation (`flagalloc.go:10-278`; `block.go:34-35`).

**Depends on:** schedule, absence of critical edges, flag generators safe to rematerialize and ARM64’s no-memory-flag-generator invariant. Regalloc follows immediately and consumes the post-SSA physical-flags representation (`compile.go:590-593`; `flagalloc.go:119-141,179-199`).

**Proof strategy & difficulty:** parity **L**, proof **L** standalone, **M** with the plan at the end of this field: direct simulation for ordering/IDs; prove or validate physical flags availability at every use and block boundary. Use a relation between logical pre-pass flag values and the machine flag register, not ordinary SSA equality, because outgoing copies intentionally have no def-use linkage. ARM64 memory-free rematerialization needs an explicit invariant (`flagalloc.go:134-141,179-191,249-278`; `value.go:451-454`). Plan (`docs/plans/semantics2.md` §6-§7): under `runSched`, flagalloc only adds pure recomputations of flag generators and redirects flag arguments to equal recomputations, so its own refinement proof is M; the one-flags-register discipline it establishes is checked by the regalloc checker, which tracks the flags register as a location.

**Issue summary:** Port required pass #55 with two-round flags liveness, exact schedule-order rematerialization, original-identity tracking, recursive copies and limited candidate cleanup. Preserve `FlagsLiveAtEnd`, NotStmt copy positions and IDs; do not allocate flag stack slots or free detached Invalids. ARM64 has no splitLoad callback, requiring a valid-input invariant. L parity/L proof (`compile.go:516`; `config.go:230-251`; `flagalloc.go:10-278`).

### regalloc — issue #410

**Function / files:** `regalloc(f *Func)` initializes `regAllocState`, runs allocation, then releases its `orig` scratch slice (`regalloc.go:148-153,914-916`). Main components: initialization and register operations (`regalloc.go:413-912`), greedy allocation (`regalloc.go:1064-2305`), spill placement (`regalloc.go:2307-2428`), merge-edge shuffling (`regalloc.go:2431-2919`), liveness/desires (`regalloc.go:2946-3383,3423-3553`), unavoidable-call analysis (`regalloc.go:3557-3623`), and the nested `stackalloc(f, spillLive)` (`stackalloc.go:93-111`; invoked at `regalloc.go:2268`). ABI-dependent register specifications come from `op.go:137-204`; homes are accessed through `stackalloc.go:408-421`.

**Position & ordering:** Index **56**, counting `number lines` as 0 and `lower` as 35; required, immediately after `flagalloc` and before `loop rotate` (`compile.go:494-519`). Explicit constraints: `critical → regalloc`, `schedule → regalloc`, `flagalloc → regalloc`, `regalloc → loop rotate`, `regalloc → trim` (`compile.go:575-578,591-596`). Critical-edge removal permits appending shuffle instructions directly to merge predecessors; scheduled values and allocated flags are prerequisites, not incidental optimizations (`regalloc.go:17-25`; `compile.go:575-578,589-596`). Output is deliberately **not strict SSA**: cross-block argument references can be non-dominating, and necessary edge copies can have zero SSA uses; ordinary dead-code elimination is unsound afterward (`regalloc.go:91-113,2639-2653`).

**Enabled (linux/arm64, default build):** Yes, including `-N`: the pass is required and has no architecture-disable predicate; the driver skips non-required passes when optimization is disabled (`compile.go:70-73,517`). ARM64 uses the generic allocator with ARM64 register tables, masks, parameter-register arrays, and instruction specifications (`config.go:228-243`; `regalloc.go:746-749,1029-1054`). Ignore RISCV64 compressed-register preference and wasm stack-value allocation for this target (`regalloc.go:263-271,492-494,607-615,870-902`). `base.Flag.ClobberDeadReg`, normally off in the requested configuration, enables inserted dead-register clobbers only for functions with at most 10,000 blocks (`regalloc.go:905-911`).

**Size:** `regalloc.go` 3,623 lines / 2,582 code lines; `stackalloc.go` 484 / 355. Main allocation `regalloc.go:1064-2305`, spill placement `2307-2428`, shuffle `2431-2919`, liveness and desired registers `2946-3383,3423-3553`, unavoidable-call analysis `3557-3623`; ABI register specs `op.go:137-204`.

**What it does:**

1. **Initialize the register universe and allocatable mask.** Reset `f.RegAlloc` to the empty cached location slice; load `Config.registers`; discover dense register numbers by the names `SP`, `SB`, `g`, `ZERO`; form the union of GP, FP, special, and SIMD masks; remove SP/SB/g/ZERO, an enabled frame-pointer register when `FPReg >= 0`, and the link register for leaf functions. Leaf detection excludes tail calls. `Flag_dynlink` makes no additional ARM64 exclusion (`regalloc.go:729-739,746-830`).

   ARM64 dense numbers are **not hardware register numbers**: 0–17 are R0–R17, 18–25 are R19–R26, 26 is g, 27 is R29, 28 is R30, 29 is ZERO, 30 is SP, 31–62 are F0–F31, and 63 is SB. The GP mask is `335544319`, admitting dense 0–25 and 28; therefore R29/g/ZERO/SP/SB are already absent, and R18/R27 are absent from the table. FP/SIMD masks admit dense 31–62. `FPReg == -1`, `LinkReg == 28`; although ARM64 has `FramePointerEnabled == true`, there is no additional dynamic FP removal because R29 is already outside the GP mask. R30 is available only in non-leaf functions (`opGen.go:116371-116444`; `internal/buildcfg/exp.go:44-51`; `regalloc.go:785-802`).

2. **Establish visit order, original-value identities, and analyses.** `layoutRegallocOrder(f)` currently returns `f.Blocks` unchanged—its name and surrounding commentary must not be mistaken for an independent layout algorithm. Build `blockOrder`, initialize `valState` and `orig` for values needing registers, compute liveness/desires, then allocate end/start-register and spill-live tables and obtain `f.Sdom()` (`layout.go:16-19`; `regalloc.go:832-868`). `needRegister` excludes memory, void, flags, and tuple types; tuple results are represented through selectors (`regalloc.go:742-744,852-859`).

3. **Compute live-out values and approximate next-use distances.**
   - A one-block function returns immediately, leaving `live`, `desired`, and `loopnest` unset. Otherwise use cached postorder and loopnest, and compute `containsUnavoidableCall` (`regalloc.go:2946-2969`).
   - Branch costs are likely **1**, ordinary **10**, unlikely **100**; only two-successor blocks use `Likely` to distinguish edges (`regalloc.go:140-143,3369-3382`).
   - In postorder, seed a sparse positional map with existing live-out records; add successor phi arguments at edge distance; add block length to distances; add controls at distance `len(b.Values)`; scan values backward, removing definitions and adding non-phi operands at their instruction indices. Calls add 100 to currently live distances and remove rematerializable live values. Propagate to predecessors with strict distance improvement; equal-distance arrivals retain the prior position (`regalloc.go:2992-3098`).
   - Loopless CFGs stop after one traversal. Irreducible CFGs use iterative propagation. Reducible loop CFGs instead capture header live-ins, sort loops by increasing depth, propagate outer-header live-ins into inner loops, add missing loop live-outs with sentinel distance `-1`, and iteratively fill unknown distances from successor live-outs using `len(successor.Values) + successor distance + branch distance + 100*numCalls[successor]`. Stop revisiting a block once it has no unknown distances; this is not a global shortest-distance solver (`regalloc.go:2975-2987,3101-3127,3133-3240`).
   - Only the reducible-loop path sorts live-out lists by `(distance, ID)` before computing desires; loopless and irreducible paths return earlier. Preserve this distinction (`regalloc.go:3122-3127,3243-3257`).

4. **Compute static desired registers.** Reverse-scan blocks in cached postorder: remove a value’s desires, remove clobbered-register desires, add singleton input constraints, and propagate result desires to tied input 0 and, for commutative instructions, input 1; `Select0` propagates to its tuple producer. Phi preferences propagate separately per predecessor, except direct backedges belonging to the header’s immediate loop. Merge into predecessor desired states until the **avoid-mask** stops changing, not until preference lists stop changing (`regalloc.go:3263-3351,3545-3553`). Each value retains at most four registers in priority order; adding a register moves it to the front, `addList` iterates backward to retain source priority, and removing an entry does not clear its stale `avoid` bits (`regalloc.go:3423-3553`).

5. **Prepare each block’s local use lists and initial state.**
   - Require `f.Entry == f.Blocks[0]`. Build per-value linked lists of uses by scanning backward: live-out pseudo-uses at `len(values)+distance`, controls at `len(values)`, and ordinary uses at instruction indices; compute `nextCall`. Calls clear the incoming-register-live set except known SP/SB. Extract prefix phis, retain a copy of the original non-phi schedule, and rebuild `b.Values` (`regalloc.go:1083-1177`).
   - Entry starts empty and must have no phis. A single-predecessor block inherits that predecessor’s end state, must have no phis, and drops values not locally register-live (`regalloc.go:1179-1200`).
   - For a merge, consider only already-visited predecessors. First candidate wins initially; fewer `spillLive` entries wins thereafter. On equal spill counts, replace the incumbent when  
     `(candidate.likelyBranch() && !incumbent.likelyBranch()) || candidate.blockOrder < incumbent.blockOrder`.  
     **This is not lexicographic likely-first ordering:** a smaller block index can displace a likely predecessor. `likelyBranch` requires every incoming predecessor edge to be single-successor or explicitly likely (`regalloc.go:1213-1246`; `block.go:415-429`).

6. **Allocate phis before ordinary instructions.**
   - In phi order, reserve the lowest available allocatable register already holding the selected predecessor’s corresponding argument, excluding registers already reserved by earlier phis.
   - Release those source registers. If a source remains live, is non-rematerializable, and has exactly one register copy, opportunistically append a preservation `Copy` to the primary predecessor in the lowest free compatible register excluding phi reservations; append this copy to that predecessor’s `endRegs`.
   - Append all phis. For unresolved phis, consider free compatible registers; scan other predecessors in `Preds` order, then their `endRegs` order, taking the first matching original argument whose register is available. Otherwise take the lowest free compatible register. If none exists, the phi becomes its own spill; otherwise its home is a register.
   - Drop non-phi values no longer live, save non-phi incoming registers in ascending dense-register order, then drop immediately dead phis (`regalloc.go:1260-1415`).

7. **Combine dynamic desires with static desires.** Successor `startRegs` and already assigned phi homes override static preference priority, in successor/phi order; an unallocated successor phi borrows the first register home found among its arguments. Reverse-scan the remaining local schedule to record up to four output preferences and preferences for the first three inputs; separately remember `Select1` preferences for a tuple’s second output (`regalloc.go:1426-1501`).

8. **Allocate scheduled instructions using exact greedy heuristics.**
   - `allocReg` intersects with allocatable registers, excludes `nospill`, and takes the **lowest dense free register**. If all candidates are occupied, scan dense registers ascending and evict the value with maximum next-use distance, updating only on strict `>`: equal distances choose the lowest register. Before eviction, if the victim is non-rematerializable, has exactly one register copy, and a free compatible register exists outside `used|tmpused`, emit an opportunistic preservation `Copy` there. An untouched inherited register may be removed from `startRegsMask`; preserve the exact `usedSinceBlockStart` updates (`regalloc.go:188-197,491-576`).
   - `allocValToReg` first reuses an allowed existing copy, preferring SP if allowed, otherwise the lowest dense register. A new representative is a `Copy` from an existing register, a rematerialization, or `LoadReg` from `makeSpill`. Fixed-register sources are preferred over ordinary sources. Compatibility mismatches can require an additional typed intermediate register and copy. Requested immediate-use registers become `nospill` (`regalloc.go:606-725`).
   - Preserve singleton-constrained inputs already in place; repeatedly fill singleton constraints whose target is free, freeing redundant/dead copies where permitted; then allocate remaining operands in **regspec input order**, which is most-constrained-first. For new assignments, use the first available desired register, then avoid registers reserved by other desires where possible; prefer SP for an existing compatible SP operand (`regalloc.go:1643-1725`; `op.go:67-72`).
   - `advanceUses` frees a value after its last use or when its next use lies beyond the next call, except fixed-register values. `dropIfUnused` treats the current instruction’s call specially by looking beyond that call for its result. `liveAfterCurrentInstruction` skips all duplicate uses at the current distance (`regalloc.go:938-988`).
   - For `resultInArg0`, consider, in order: dead arg0; dead commutative arg1; rematerializable arg0; rematerializable arg1; multiply represented arg0; multiply represented arg1. Swap actual operands when choosing arg1. Otherwise, if a compatible free register exists, try desired output, desired input0, desired input1, then an avoid-filtered preservation copy; without free space allow the old input to require restoration later. Independently preserve live `clobbersArg0/1` operands when possible (`regalloc.go:1727-1850`).
   - For `needIntTemp`, allocate an integer register after inputs but before freeing dying inputs, exclude singleton output registers, prefer avoiding future desires, protect it from output allocation, and store the result in `f.tempRegs[v.ID]` (`regalloc.go:1852-1873,1904-1909,2006-2012`).
   - Unless `resultNotInArgs`, advance/free inputs before output allocation. Apply input-specific and fixed-register clobbers, then allocate outputs in regspec order. Respect tied result0; for commutative ties prefer an available desired input register, else input0. Prefer result0 desires and saved `Select1` desires for result1, avoid other desires where a free alternative exists, and prevent output/output/temp overlap. Record a scalar register, `LocPair`, or `LocResults`; tuple/result selectors subsequently claim the recorded register. Rewrite arguments with `SetArg`, append the instruction, then drop unused results (`regalloc.go:1875-2027,1541-1556`).

9. **Handle special instructions and ABI constraints.**
   - SP/SB/ARM64ZERO receive fixed homes; GetG uses the hardware g register; `Arg` is pre-spilled and receives no register here. `KeepAlive` can retain a spill use, become `VarLive` for a rematerializable local address, or become a memory `Copy` (`regalloc.go:1514-1600`).
   - `ArgIntReg`/`ArgFloatReg` use `AuxInt8` to index `Config.intParamRegs`/`floatParamRegs`: ARM64 R0–R15 and F0–F15. `AuxCall.Reg` lazily prepends ABI singleton argument/result constraints to static machine constraints and inherits machine clobbers. `MakeResult` uses `OwnAux.ResultReg`, also lazily populated. These mutate auxiliary register-specification caches (`regalloc.go:1037-1053`; `op.go:137-204`; `opGen.go:116437-116438`).
   - A rematerializable original instruction is omitted from the rebuilt schedule and its arguments’ `Uses` are decremented; it is not immediately freed. Rematerialization requires the opcode flag and **all operands to be fixed-register ops** (`regalloc.go:1611-1621,2923-2935`).
   - Enabled dead-register clobbering inserts ascending-register `ClobberReg` values of void type, with `NoXPos`, restricted to allocatable GP registers; call inputs are excluded in the operand-bearing path (`regalloc.go:439-446,1601-1608,1891-1898`).

10. **Finish each block and place spills.**
    - Allocate control values in compatible registers; replace controls and consume their local uses. Before a single-successor edge, release g. For an unvisited loop header without an unavoidable call, promote sufficiently near live values (`dist < 100`), preserving already likely-used registers; phi arguments require a regular compatible register even for fixed/rematerializable values. Iterate live records in their existing order and apply desired-register priority (`regalloc.go:2030-2165`).
    - Save `endRegs` in ascending dense-register order. Every non-rematerializable live-out lacking a register gets a spill and a `spillLive` entry. Clear final pseudo-uses and compact dropped `startRegs` before placing spills (`regalloc.go:2169-2262`).
    - `makeSpill` lazily allocates a blockless, argumentless `StoreReg`, recording the original value and min/max sparse-dominator intervals of restore sites. It allocates **when a spill first becomes necessary**, not when the store’s final placement is chosen (`regalloc.go:580-599`).
    - `placeSpills` visits original IDs ascending. Starting at the definition block, descend through sparse-tree children that dominate all restores, subject to a shared search budget of 100 that counts child traversal as well as outer descent. Accept a candidate only if it is no deeper than the current best loop and the value is available in an incoming register; first matching end/start register provides the store’s argument. Place after its definition, or at the destination block’s start after closure-pointer/phi/register-argument prefix values. Lists attached to the same insertion point retain ascending-original-ID insertion order (`regalloc.go:2307-2428`).

11. **Allocate stack homes, repair every merge edge, and remove unused opportunistic copies.** Stack allocation precedes shuffling; shuffle may allocate **additional** spill temporaries after stack allocation. Finally repeatedly range over the opportunistic-copy map, freeing unmarked zero-use copies until fixed point, then stably compact `OpInvalid` entries from block schedules (`regalloc.go:2264-2303,2887-2906`).

**stackalloc** (embedded; `stackalloc.go`, called at `regalloc.go:2268`):

Not a separate `compile.go` pass: `stackalloc` initializes state, computes stack liveness/interference, assigns homes, and returns stack-live IDs for shuffling (`stackalloc.go:93-140`; `regalloc.go:2268-2271`).

1. **Identify stack candidates.** A candidate has no home, is not memory/void/flags, is not rematerializable, and is not on the wasm stack. Record type, defining block, argument status, and the most recently encountered `StoreReg` associated with each register value (`stackalloc.go:114-135`).
2. **Compute liveness.** Gather uses from `spillLive` and ordinary operands; phi uses belong to the corresponding predecessor and force live-out, including an associated spill. Iterate candidate IDs ascending; explore use blocks backward with a LIFO queue and sparse seen-set, stop propagation at the definition, and append the ID to each predecessor’s live-out, avoiding consecutive duplicates. Consequently each block’s returned stack-live list is ordered by candidate ID (`stackalloc.go:313-405`).
3. **Build interference.** In `f.Blocks` order, backward-scan each schedule from its stack-live set. Remove a candidate definition, add symmetric interference against remaining live candidates if their types compare equal **or either is an argument**, add operands, and re-add pre-spilled arguments so they remain live before their entry definitions. The sparse-set removal order determines adjacency-list order; duplicate edges need not be eliminated (`stackalloc.go:423-480`).
4. **Choose names deterministically.** Scan `f.Names`, then `f.NamedValues[*name]`; the first eligible name wins. Register arguments must match their `AuxNameOffset` name and offset; otherwise PPARAM names bind only to `OpArg`. Entry `Arg` homes are `LocalSlot{N: Aux.(*ir.Name), Type: v.Type, Off: AuxInt}` (`stackalloc.go:145-203`).
5. **Assign slots in `f.Blocks × b.Values` order.** Skip non-candidates and arguments already assigned. For `StoreReg`, use its input’s selected name. Reuse a named slot only when `Type.Compare` agrees and no interfering assigned value has the same `N` and `Off`. Named-slot assignment does not enter the anonymous-slot pool (`stackalloc.go:242-278`).
6. **Reuse anonymous slots by semantic type key.** `locations` is keyed by `Type.LinkString`, not type-pointer identity. Mark pool indices assigned to interfering values, choose the **first unmarked index**, otherwise append a fresh `LocalSlot` using `f.NewLocal(v.Pos,v.Type)`. `locations` at line 229 is a Go map, but **is never ranged over**; type buckets are accessed only by key, so it does not introduce randomized allocation order (`stackalloc.go:224-310`).
7. **Create autos, not final frame offsets.** `NewLocal` calls `typecheck.TempAt`, appends an auto to the frontend function’s declarations, and marks it nonmergeable. `TempAt` calculates type size, names the auto from `len(curfn.Dcl)`, and marks it EscNever/Used/AutoTemp. This helper assigns symbolic `LocalSlot` homes; it does not lay out a final byte-addressed frame (`func.go:858-861`; `cmd/compile/internal/typecheck/dcl.go:51-73`; `stackalloc.go:295-308`).

**Merge-edge shuffle** (`regalloc.go:2431-2919`):

1. **Enumerate edges deterministically.** Visit merge blocks in `visitOrder`, predecessors in `Preds` order. Reset `edgeState`; add predecessor register sources, then stack-live sources whose actual spill definition dominates the predecessor. Destinations are non-phi `startRegs` followed by successor phis with nonnil homes; each phi destination records a pointer to that edge’s phi argument for splicing (`regalloc.go:2431-2451,2496-2548`).
2. **Maintain abstract contents.** `contents : Location → {original ID, representative, final, position}` and `cache : original ID → ordered representatives` track available copies. `cachedVals` supplies deterministic traversal of map keys; it is a superset and can contain a repeated ID when an emptied cache is repopulated. `set` writes the representative’s home and updates used/unique/final/rematerializable masks (`regalloc.go:2460-2493,2781-2813`).
3. **Satisfy destinations in queue order.** Already-correct destinations update the phi argument and `Uses`, and mark tracked opportunistic copies used. Do not overwrite the last available copy of a non-rematerializable, non-fixed value. Source selection prefers fixed originals; otherwise scan representatives, retaining the first stack source unless a register is found, and replacing the choice on every register source—thus the **last register representative wins** (`regalloc.go:2633-2692`).
4. **Pre-erase the destination, then emit movement.** Register→register is `Copy`; register→slot is `StoreReg`; slot→register is `LoadReg`; slot→slot is `LoadReg` through a temporary followed by `StoreReg`. Stores use the **destination slot’s type**, not necessarily the source representative’s type. Rematerialize when permitted, adding an intermediate register/copy for incompatible destination masks or a store for stack destinations. Splice the resulting representative into phi args and adjust uses (`regalloc.go:2694-2777`).
5. **Temporary-register priority:** lowest compatible register in the first nonempty class: unused; nonunique and nonfinal; nonunique; rematerializable. If none, scan `cachedVals` then its representative slice and choose the first compatible register; emit a `StoreReg` to a **fresh `NewLocal` slot** unless its representative is rematerializable. These emergency slots are not reused by this routine (`regalloc.go:2860-2906`).
6. **Cycles and displacement.** Retain unsatisfied destinations stably and retry. If a sweep makes no progress, use the **first** remaining destination, copy/load its current occupant into the chosen temporary, and resume. Erasing a final location queues its restoration at the end; extras are appended after a successful sweep. Representative removal is swap-with-last. Preserve the concrete mask updates: the already-correct branch updates `contents.final` without calling `set`, and `erase` does not delete the `contents` entry; these details are part of algorithm parity, not opportunities to normalize state (`regalloc.go:2564-2629,2635-2657,2817-2856`).

**Data structures:** Two-word `regMask` and `uint8` dense register numbers with sentinel 255; ID-indexed `valState`, `orig`, `live`, `desired`, `startRegs`, `endRegs`, `spillLive`, and `blockOrder`; linked use records and per-block `nextCall`; ordered four-register desire lists plus an overapproximating avoid mask; sparse sets/maps; opportunistic-copy map; edge location/content and original/representative maps with explicit deterministic key traversal; stack value/interference/name arrays and type-keyed slot pools. Public output is `f.RegAlloc : []Location`, containing nil, register pointers, `LocalSlot`, `LocPair`, or `LocResults`, plus `f.tempRegs`; `setHome` extends the array with nil entries through the requested ID (`regalloc.go:155-165,280-410,1073-1081,1983-2012,2460-2493,3423-3444`; `stackalloc.go:16-35,59-66,229-239,408-421`).

**Parity traps (order dependence / nondeterminism):**

- **Actual randomized map iteration:** final `for c, used := range s.copies` can free independent dead copies in different orders. `freeValue` pushes onto the LIFO free list, so the output free-list order is genuinely nondeterministic even when surviving instructions/homes agree. Dependency chains can be removed in one or several sweeps depending on map order. No further allocation occurs inside this pass after cleanup; the immediate surviving schedule is compacted independently in visit order. Exact full-state parity therefore needs the observed deletion order or a deliberately weakened comparison contract—not a silent deterministic replacement (`regalloc.go:2274-2303`; `func.go:397-415`).
- **Other maps do not have randomized iteration in these routines:** `desiredSecondReg` is cleared/key-accessed; `placeSpills.start/after` are key-accessed; `loopLiveIn` is traversed through the ordered loop list; edge `cache/contents` use `cachedVals` and ordered destination/source slices; `tempRegs` is assigned by ID; stack `locations` is key-accessed; `NamedValues` is traversed through `Names` (`regalloc.go:1074,1094,1497-1500,1957-1967,2008-2012,2313-2317,2422-2425,2465-2470,2784-2788,2888-2890,3133-3153`; `stackalloc.go:157-160,229,282-299`).
- **All explicit sorts:** loop sorting compares only depth, so distinct loops tie and Go’s unstable deterministic sort must be reproduced for exact intermediate parity; final live sorting uses `(dist,ID)`, a total ordering for distinct live values; debug printing sorts the live slice **in place by ID**, potentially altering allocation if debug is enabled. Debug zero avoids that extra mutation; do not treat enabling allocator debug as observationally inert (`regalloc.go:3133-3136,3244-3251,3392-3396`).
- **Every heuristic tie is operational:** predecessor scan and its nonlexicographic OR; ascending mask selection and strict farthest-use comparison; phi order, first eligible other-predecessor source, first `endRegs` match; four-entry desire recency and swap-removal; output/input regspec order; desired register list order; first anonymous-slot index; last cached register source; first unresolved shuffle destination; first emergency-spill representative. These are observable in copies, spill creation, names, and homes (`regalloc.go:491-576,1213-1243,1264-1353,1643-1725,1910-1979,2587-2617,2673-2686,2887-2906,3457-3553`; `stackalloc.go:157-185,285-308`).
- **Sparse order and fixed-point boundaries:** positional-map insertion/update/swap-removal order becomes live-list order through `updateLive`; strict shorter-distance updates retain an earlier equal-distance position; reducible-loop early stopping and the unsorted early-return paths matter. Stack liveness uses ascending IDs and LIFO predecessor exploration; interference records sparse-set dense order. Desired-state convergence observes only avoid-mask growth (`regalloc.go:2992-3098,3122-3127,3200-3251,3355-3363,3545-3553`; `stackalloc.go:376-398,432-468`).
- **Cached CFG state:** use the existing cached postorder/sdom/loopnest, including inherited stale ordering; do not recompute a “cleaner” postorder. Sparse-tree sibling order affects the bounded spill search. `containsUnavoidableCall` is mutated in cached loop objects; its implementation sets true when it finds no call-free header return and does not reset existing true bits. Exits from the loop are skipped, despite broader wording in the introductory comment (`func.go:795-809`; `regalloc.go:2343-2364,2953-2969,3557-3610`).
- **IDs and scheduling:** lazy blockless spills consume IDs before placement; opportunistic copies can be appended to an already processed predecessor; edge shuffles create further values and autos after ordinary stack allocation. All constructors use the existing LIFO free values before fresh IDs. No block creation/reordering is performed by the allocator itself (`func.go:280-333`; `regalloc.go:580-599,1297-1314,2264-2303,2431-2451,2892-2897`).
- **Positions:** ordinary allocation strips statement marks at the requested use position, but `copyIntoWithXPos` can restore a same-line statement mark from the original. Edge register rematerialization commonly uses original-position `copyInto`, whereas stack rematerialization uses requested-position `copyIntoWithXPos`. Preservation copies/spills and emergency edge spills use their source positions; constructors still apply `notStmtBoundary` (`regalloc.go:551-552,588-593,619,1303,2709-2743,2892-2896`; `value.go:446-479`; `func.go:298-301,328-331`).
- **Uses and dead-looking output:** argument/control replacement and phi splicing must update `Uses`; dropped rematerializable originals manually decrement operand uses; unused edge copies may remain necessary because location semantics, not SSA def-use dominance, determines execution. Final freeing does not clear entries of `f.RegAlloc`; preserve the actual location slice rather than rebuilding it from surviving values (`regalloc.go:1611-1621,2022-2025,2042-2063,2639-2653,2772-2776`; `stackalloc.go:415-420`; `func.go:397-415`).
- **Type and identity subtleties:** type-keyed anonymous reuse uses `LinkString`, interference/named compatibility uses `Type.Compare`, named interference checks `N` identity plus offset, and edge locations are map keys whose `LocalSlot` identity must be reproduced. Do not conflate symbol equality, type-pointer equality, and physical slot overlap (`stackalloc.go:224-229,263-267,282,446-450`; `regalloc.go:2434-2435`).
- **Mutable ABI caches:** `AuxCall.Reg` detects initialization through a nonempty clobber mask; `ResultReg` detects an existing input list. Exact aux-state parity includes these lazy mutations and shared auxiliary identity (`op.go:137-164,175-190`).

**External state read:** Config’s ordered register table, GP/FP/FP32/FP64/special/SIMD masks, `hasGReg`, FP/Link registers, integer/float parameter-register arrays, architecture and `ctxt.Flag_dynlink`; `buildcfg.FramePointerEnabled`; `base.Flag.ClobberDeadReg`; opcode input/output/clobber/tied-result/temp/rematerialization metadata; ABI data and mutable `OwnAux`/`AuxCall` register specifications; type classification/size/comparison/LinkString; positions; ordered names and name-offset auxiliaries; cached CFG/loop data; frontend function declaration list and local package for new autos (`regalloc.go:746-868,905-911,1001-1054,1859-1873,2923-2935`; `op.go:137-204`; `stackalloc.go:157-203,263-299`; `func.go:858-861`; `cmd/compile/internal/typecheck/dcl.go:62-72`). `f.RegAlloc` is reset and then progressively read/written, rather than consumed as a completed incoming allocation; `tempRegs` is populated on demand. Stack homes remain symbolic, with final frame layout outside this helper (`regalloc.go:748,2006-2012`; `stackalloc.go:295-308,408-421`).

**Depends on:** Fully lowered ARM64 operation metadata, scheduled values with prefix phis and appropriately placed tuple selectors, critical-edge elimination, flag allocation, entry-first block layout with an already visited predecessor for each processed merge, shared value/Uses/position primitives, cached postorder/dominators/sparse tree/loopnest, sparse collections, ABI mapping, and frontend temporary creation (`compile.go:570-578,589-596`; `regalloc.go:1083-1085,1167-1191,1213-1246,1509-1556,2307-2428`; `op.go:137-204`; `func.go:280-333,858-861`).

**Proof strategy & difficulty:** **Parity XL; semantic proof XL overall**, with a translation validator preferable to proving every greedy heuristic. The proposed checker below is a design proposal, not a claim that Go currently supplies it. Its central invariant follows the clifv checker’s “each location contains the symbolic values asserted for it,” adapted to Go’s non-dominating representatives and phi-home agreement (`regalloc.go:91-113,2639-2653`; `/home/kev/work/fv-compiler-rust/docs/contracts/regalloc-proof.md`, “Certificate check”, “Abstract semantics”, and “Theorem”).

- **What Go currently checks.** With `checkEnabled`, the driver calls `checkFunc` after the pass, and regalloc additionally verifies that saved live register values belong to its computed live-out set (`compile.go:138-140`; `regalloc.go:2188-2205`). `checkFunc` checks graph crosslinks, value/aux/argument structure, referenced-value membership, free-list separation, use counts, and memory invariants. It explicitly **skips SSA dominance and loop-construction checking after `RegAlloc != nil`**; there is no general register/slot-content abstract interpreter or home-constraint validation in those branches (`check.go:15-37,190-289,409-516`). The allocator has local failures for empty masks, occupied-register assignments, bad phi placement, and loads targeting g, but these are not a semantic allocation certificate (`regalloc.go:469-505,1190-1191,1509-1512,717-718,2625-2627,2769-2770`). Tests add selected assertions about g reloads, spill placement, copies, and phi homes; they do not replace such a checker (`regalloc_test.go:75-84,115-118,155-158,234-237,399-405`).

- **Checker inputs and structural correspondence.** Keep immutable pre-regalloc SSA and scheduled CFG, plus post-regalloc SSA/homes/tempRegs. Supply an untrusted origin witness for inserted representatives and tuple components; verify it rather than trusting exported `orig`. Check unchanged CFG and preservation/order of semantic instructions; permit only justified rematerialization, allocator movement, selector bookkeeping, and documented KeepAlive transformations. Reject deletion/duplication of effects, altered aux/type semantics, illegal register constraints, malformed phis, invalid slots, or overlapping temp/output/input assignments where forbidden. The required exceptional transformations are explicit in the implementation (`regalloc.go:1514-1621,1852-2027,2923-2935`).

- **Abstract domain and transfers.** Use `Location → finite set of original-value/component symbols`, with unknown represented by no asserted symbols. Track SP/SB/ZERO/g and ABI incoming arguments according to their special contracts. `Copy`, `LoadReg`, and `StoreReg` read the source **location’s current contents**, check its claimed origin, and write the destination location; do not require the source representative’s definition to dominate. Ordinary instructions check all source origins at their operand homes, apply input clobbers/fixed clobbers/temp havoc in the proper order, then define result symbols at scalar/tuple/result homes. Rematerialization establishes the original symbol only after checking the opcode’s semantic recomputation lemma and fixed operands. Store/load widths must respect destination-slot typing and any narrowing relation (`regalloc.go:606-725,1514-1600,1875-2012,2633-2777`).

- **Edges and phis.** Execute appended edge moves in schedule order. For edge `p → b`, check each original phi input’s symbol is present at the phi’s allocated location, then **simultaneously rename symbols** from predecessor arguments to successor phi definitions. This is an abstract renaming, not an additional physical move. Retain compatible non-phi symbols; meet predecessor states by intersecting guaranteed facts. Check control operands before branching. This handles register and stack phis and the non-SSA inherited-register case (`regalloc.go:1355-1402,2033-2063,2431-2451,2533-2548`).

- **Loops and certificate validation.** An untrusted worklist may propose block-entry states; a small trusted verifier checks the ABI entry state, every block transfer, every edge/phi renaming, and containment of required successor facts in edge-produced facts. Prove the verifier sound independently of convergence, postorder, spill heuristics, or allocation order. On each source redefinition/phi entry, forget stale symbols appropriately so static SSA IDs in loops denote the current dynamic instance, not an earlier iteration. This is the Go adaptation of clifv’s certificate-verification architecture, necessary because Go explicitly permits non-dominating postallocation operands (`regalloc.go:91-113`; `/home/kev/work/fv-compiler-rust/docs/contracts/regalloc-proof.md`, “Certificate check” and `Inv`/`Match` discussion).

- **Soundness obligations.** Prove: entry ABI agreement; location-domain transfer soundness; simultaneous phi renaming; ordinary operation operand/result/clobber contracts; fixed-register invariants; pure rematerialization equivalence; stuttering simulation for inserted moves and omitted rematerializable originals; equal memory/call/branch/return/trap observations; and a decreasing remaining-items measure preventing infinite move-only stuttering. Separately connect symbolic slots to actual byte ranges, including width, alignment, overlap invalidation, incoming argument slots, and noninterference with program-addressable storage. **Named-slot reuse prevents assuming every spill slot is fresh private memory**; model those overlaps explicitly or prove the required alias/liveness invariant. GC/KeepAlive/debug-location correctness is an additional observable contract beyond ordinary value semantics (`stackalloc.go:157-203,263-307`; `regalloc.go:1574-1599,2738-2764`; `/home/kev/work/fv-compiler-rust/docs/contracts/regalloc-proof.md`, “Operand-view obligation” and “Frame and move lowering”).

**Plan:** `docs/plans/semantics2.md` §7 (certified location checker, `checkRegalloc f g = true → Refines (runLoc g) (runSched f)`).

**Issue summary:** Port required pass #56 as an exact operational allocator, including ARM64 dense-register numbering/masks, lazy ABI regspec mutation, cached liveness/desires, nonlexicographic predecessor choice, phi preservation, farthest-use eviction, temp registers, bounded dominator/loop-aware spill placement, named/type-keyed stack homes, and deterministic edge shuffling. Preserve every generated ID, operand/home, statement mark, schedule position, auxiliary cache mutation, and auto declaration. Resolve randomized opportunistic-copy deletion explicitly because it changes the value free list; `stackalloc.locations` itself is not ranged over. Pair the parity port with a separately proved location-content translation validator: Go’s existing postallocation checks do not validate allocation semantics and intentionally abandon SSA dominance. Scope is 3,623 + 484 physical source lines plus shared helpers; parity XL / proof XL (`compile.go:517`; `regalloc.go:1213-1243,2264-2303,2307-2428,2431-2919`; `stackalloc.go:224-310`; `check.go:451-516`).

### loop rotate — issue #411

**Function / files:** `loopRotate` (`looprotate.go:28-200`), shared cached loopnest (`func.go:795-801`), block hotness flags (`block.go:442-448`).

**Position & ordering:** index **57**, optional, after regalloc and before trim. Explicit regalloc→loop rotate constraint because rotation confuses regalloc’s ordering assumptions (`compile.go:517-519,594-595`).

**Enabled (linux/arm64, default build):** yes; skipped under `-N`. Returns unchanged for irreducible loopnest or no loops. No architecture switch; `f.IsPgoHot` adds HotPgo metadata when selecting loop tops (`compile.go:70-74,518`; `looprotate.go:29-35,120-130`).

**Size:** `looprotate.go` 192 lines / 112 code lines.

**What it does:**
1. Obtain cached loopnest; build block-ID→current-index map and empty `move`, `after` and `tops` maps. Create loop indices in cached loop discovery order and unstable-sort by depth descending, with equality for equal depths (`looprotate.go:29-101`).
2. For each loop, scan header predecessors in order, retaining the **last** Plain predecessor whose `b2l` equals that exact loop. Skip if none. Record it as top; OR HotInitial and optionally HotPgo. If top equals header stop processing that loop; otherwise also OR HotNotFlowIn (`looprotate.go:104-132`).
3. Set `after[top]=[header]`. Scan forward through the **current** block order from header until reaching top or function end, appending blocks belonging to the loop or a direct child loop whose recorded top equals that block. Intervening excluded blocks do not stop scanning (`looprotate.go:134-153`).
4. Swap header/top positions and update their index entries. Mark every block in `after[top]` for movement (`looprotate.go:154-163`).
5. Copy this intermediate order. Walk it once, skipping moved blocks; emit each remaining block followed recursively by its `after` list. Require emitted count equal original block count. CFG edges, instructions, register assignments and Entry remain unchanged (`looprotate.go:166-200`).

**Data structures:** cached loopnest; current index array; sorted loop-index slice; membership-only move map; keyed ordered after-lists and header→top map; temporary block slice; recursive emitter (`looprotate.go:37-101,166-191`).

**Parity traps (order dependence / nondeterminism):** exact unstable depth-sort ties, original loop discovery order, **last** qualifying predecessor and intermediate swaps affect output. Do not rotate from a frozen original index map. Child-before-parent processing builds nested after-lists. Maps are accessed by lookup/insertion, never ranged, so no map-order nondeterminism. Hotness uses bitwise OR; even a one-block loop gets hotness updates without movement. No IDs/Uses changes or CFG invalidation (`looprotate.go:83-200`).

**External state read:** cached loopnest, current post-regalloc block order, Plain kinds and predecessor order, existing hotness, IsPgoHot. It does not inspect or rewrite RegAlloc/Home/tempRegs/frame layout, but must preserve them while reordering blocks (`looprotate.go:28-200`; `func.go:50-57`).

**Depends on:** regalloc completion; cached loopnest and exact depth sort; hotness representation. Do not rebuild loopnest solely because layout/regalloc reordered blocks (`compile.go:594-595`; `func.go:795-801`; `looprotate.go:29-101`).

**Proof strategy & difficulty:** parity **M**, proof **S–M**: direct simulation of nested move lists and a block-permutation theorem; preserve already allocated instruction sequences and explicit CFG edges. Prove no block duplication/loss, matching the implementation’s emitted-count check (`looprotate.go:166-200`).

**Issue summary:** Port optional pass #57 as nested block-order rotation after allocation, preserving exact equal-depth sort behavior, last eligible backedge predecessor, intermediate swaps and hotness ORs. No edge rewrites or register reassignment. Cached loopnest is reused and irreducible functions are skipped. M parity/S–M proof (`compile.go:518,594-595`; `looprotate.go:28-200`).

**Proof (#385):** `GoFV.Proof.loopRotate_refinesLoc (h : loopRotatePass penv f = .ok out) : RefinesLoc out.tables out.func penv.tables f` (`GoFV/Proof/Pass/LoopRotateLoc.lean`), no hypothesis: the output differs from the input only in `f.Blocks`, `Hotness` and the loop-nest cache (`loopRotate_shape`), none of which `runLoc` reads, so both have the same `runLoc`s (`GoFV.Proof.runLoc_congr`, `GoFV/Proof/CongLoc.lean`: same `eraseFL`, `low.regAlloc`, `low.tempRegs`). Witness `GoFV.Proof.Witness.loopRotateLoc_witness` (an allocated countdown loop whose block order rotates; it returns 7 under `runLoc` before and after).

### trim — issue #412

**Function / files:** `trim`, `emptyBlock`, `trimmableBlock`, `mergePhi` (`trim.go:11-171`); statement-op classification, argument setters and CFG cache invalidation are shared (`trim.go:39-45,114`; `func.go:803-809`).

**Position & ordering:** index **58**, optional, final pass in this list; explicit regalloc→trim constraint (`compile.go:517-520,596-597`).

**Enabled (linux/arm64, default build):** yes; skipped under `-N`. No architecture/config branch and **no direct `f.RegAlloc` test** in this implementation (`compile.go:70-74,519`; `trim.go:11-171`).

**Size:** `trim.go` 169 lines / 116 code lines (`trim` :11, `emptyBlock` :119, `trimmableBlock` :135, `mergePhi` :145).

**What it does:**
1. Scan `f.Blocks` once in existing order and compact survivors. A block is trimmable iff Plain, not Entry, successor not itself, and either successor has exactly one predecessor **or all this block’s values are Phi**. Thus it also merges instruction-bearing Plain blocks into a single-predecessor successor; “empty-block removal” is not the complete behavior (`trim.go:11-18,120-142`).
2. Let successor edge target predecessor slot be `j` and original successor predecessor count `ns`. Replace that slot with trimmed block’s first predecessor; redirect that predecessor’s matching successor. Append remaining predecessors in original order, setting reciprocal edge indices (`trim.go:20-35`).
3. If trimmed block position is IsStmt, inspect only the first successor value not classified as a poor statement op. Mark it IsStmt if same file/line, then stop regardless of match. Only if no such value exists, try successor block position (`trim.go:37-53`).
4. If `ns>1`, rewrite each successor Phi at argument `j`: when its argument is a Phi defined in the removed block, replace by that Phi’s first arg and append the remaining args; otherwise append copies of the existing arg once for each additional incoming predecessor (`trim.go:55-63,146-171`).
5. Still for `ns>1`, process removed-block Phis after successor rewrites. Zero-Uses Phis resetArgs and are omitted, not freed. Surviving Phis save old args, reset, then pad with self references for the successor’s other original predecessors, place old arg0 at `j`, and append old remaining args (`trim.go:64-97`).
6. Retarget each remaining moved value’s `Block` to successor and **prepend** these values to its schedule. If any block was removed, invalidate all cached CFG analyses, clear the obsolete block-slice tail and truncate. Removed block/value objects are not free-list recycled, and RegAlloc/tempRegs are not rewritten (`trim.go:99-118`; `func.go:803-809`).

**Data structures:** in-place block/value compaction; existing edge arrays and phi arguments; temporary copied Phi arg slice; shared position helpers and CFG caches. No maps, sets or sorts (`trim.go:11-171`).

**Parity traps (order dependence / nondeterminism):** one pass, not a fixpoint; subsequent blocks observe earlier edge/value edits. Preserve predecessor replacement-at-`j` plus append order exactly—it defines the matching Phi argument permutation. Statement transfer happens **before** moved values are prepended. Uses changes from mergePhi determine which source Phis survive, and source-phi processing itself updates Uses. No freeBlock/freeValue: do not “clean up” detached objects or their existing location-table entries (`trim.go:23-118,146-171`).

**External state read:** current post-regalloc CFG and schedules, exact predecessor backindices, Phi Uses/args, Entry and positions. **RegAlloc interaction is indirect:** stable value IDs retain their already assigned locations while definitions move between blocks and Phis are rewired; the pass neither reads nor recalculates locations, stack slots, temp registers or frame layout. No new autos or IDs are allocated (`trim.go:11-171`; `func.go:53-57`).

**Depends on:** completed register allocation and its edge-copy/phi realization; well-formed reciprocal CFG edges; statement classification, precise Uses setters and complete cache invalidation. Removing critical-edge blocks is deliberately after allocation, not before (`compile.go:596-597`; `trim.go:9-10,23-35,55-118,146-171`).

**Proof strategy & difficulty:** parity **M**, proof **L**: direct simulation for graph/list/Uses parity; semantic proof by edge-contraction stuttering plus phi-index correspondence and instruction-sequence concatenation. Because this is post-regalloc, prove preservation of physical locations and previously inserted edge transfers, not merely ordinary pre-allocation SSA semantics (`trim.go:23-118,146-171`; `compile.go:596-597`).

**Issue summary:** Port optional final pass #58 with its full eligibility rule, including nonempty single-predecessor merges; preserve predecessor/Phi splice order, statement transfer, Uses-sensitive phi cleanup and prepending of moved schedules. Do not free removed objects or alter location tables. Invalidate CFG caches only when blocks were removed. M parity/L proof (`compile.go:519`; `trim.go:11-171`).

**Proof (#385):** `GoFV.Proof.trim_refinesLoc (h : trimPass penv f = .ok out) (hrel : TrimLoc.trimRelB f out.func = true) : RefinesLoc out.tables out.func penv.tables f` (`GoFV/Proof/Pass/TrimLoc.lean`), through the decided relation `GoFV.Proof.TrimLoc.trimRelB` (`GoFV/Proof/Pass/TrimLocCheck.lean`): same entry, ABI, homes, temporary registers and value-table size; every output value is an input value with the same op and type (a non-`Phi` one also the same up to position, use count and block; a `Select0`/`Select1` has its arguments in the output, since a `MOVDreg` of it reads whether it selects from `LDPSW`, `Arm64.signExtendsIn`); every output block is the input block up to position, prediction, values and edges, with as many successors, and each input successor is an *entry point* of the output successor of the same index: following removed `Plain` blocks without controls (`chaseLoc`) reaches it, and the non-`Phi` values on the way are exactly the output block's non-`Phi` values; the output's non-`Phi` values, their arguments and controls are values, and its `Phi`s keep their arguments' homes. Proof (`refinesLoc_of_trimRelB`): stuttering simulation over `runLoc` (`runLoopLoc_simIH`, `GoFV/Proof/SimLoc.lean`) with equal machine states, a `Phi` doing nothing (`enterList_np_src`/`_tgt`) and a removed block's terminator a no-op jump (`stepTermLoc_plain`); terminators do not read their successors' targets (`stepTermL_succs`). Coverage of `trimRelB` (`lake exe trim-probe`, `GoFVTest/TrimProbe.lean`): quick-v7 9,297 `trim` sections, 2,780 changed (13 merge a non-empty block, 513 drop a `Phi`), accepted 9,297, rejected 0 (unchanged by the `Select` clause); full-v9 96,560 sections, 34,653 changed (43 non-empty merges, 5,639 dropped `Phi`s), accepted 96,560, rejected 0. Witness `GoFV.Proof.Witness.trimLoc_witness` (a non-empty block spliced after `loop rotate`; the two-pass tail returns 7 under `runLoc`).
