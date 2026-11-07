# Step survey: from `trim` to object code (go1.27.3, linux/arm64)

Scope: everything the pinned compiler does to one function after the last SSA pass (`trim`,
the end of `ssa.Compile`) until the function's bytes, relocations and metadata are in the object
file: the tail of `buildssa` (frame layout), `genssa` with the arm64 value/block emitters, the
liveness and metadata it emits, `objw`, `cmd/internal/obj` with `obj/arm64` (progedit,
preprocess, `span7`), the pc tables, the DWARF the compiler and `obj` produce, and the object
writer. The linker is out of scope (trusted, §5). Paths are relative to
`third_party/go/src/cmd` unless prefixed (`runtime/…`, `internal/…` are under
`third_party/go/src`). Companions: `docs/PASSES2.md` (the SSA passes up to `trim`, whose output
is this phase's input), `docs/plans/semantics3.md` (machine semantics, the relation to `runLoc`,
ABI, frame, runtime), `docs/PLAN.md` §7 (milestones I1–I8). Tracking issue: #546; milestones
I1 #547, I2 #548, I3 #549, I4 #550, I5 #551, I6 #552 (I6b #555, blocked on #415), I7 #553,
I8 #554.

Written by the Phase3Survey agent from the source only, with one exception: the bounds-panic
wart in §3 was reproduced under `qemu-aarch64-static`. The per-step sections were compiled by
five survey agents reading the source; start lines were spot-checked, ranges at the ends of
functions can be off by a few lines, and code-line counts marked "~" are approximate
(non-blank, non-comment). Every "parity trap" is something an exact port (same Progs in the same
order with the same fields, same bytes, same relocations, same symbols) must replicate.

## 0. Pipeline

There is no pass table after `trim`: the steps below are straight-line code, called once per
function on a backend worker (`ssagen.Compile`, `compile/internal/ssagen/pgen.go:303-343`),
except the package-level steps F1–F2, which run once per package after all functions
(`compile/internal/gc/main.go:355-381`). Nothing here is disabled on linux/arm64 in the default
build; `-N` changes A1 (no merging), B2 (skipped), E1 (`BuildFuncDebugNoOptimized`), C2 (no
fallthrough `next`), and the Prog list accordingly.

**Forms.** Each step consumes and produces one of these (semantics: `docs/plans/semantics3.md` §1):

| Form | What it is | Semantics |
| --- | --- | --- |
| **L2** | allocated SSA after `trim` (homes `f.RegAlloc`, `f.tempRegs`, layout order, schedule) | `runLoc` (Phase 2) |
| **L2f** | L2 plus the frame layout: `Name.FrameOffset`, `stksize`, `stkptrsize`, merged slots, `f.RegArgs` | `runLoc` with slots placed in a concrete frame (`runFrame`, semantics3 §4) |
| **P0** | `genssa`'s Prog list (before `Flush`): instructions over obj registers, symbolic autos/params (`NAME_AUTO`/`NAME_PARAM`), branch targets as Prog identities, `TEXT` with frame and arg size, PCDATA/FUNCDATA pseudo-Progs, pseudo-instructions (`GETCALLERPC`, `RET` without epilogue, large constants) | `runProg` (semantics3 §7) |
| **P1** | after `linkpatch` with arm64 `progedit` | `runProg` |
| **P2** | after `preprocess`: prologue, stack-split check and slow path, epilogues, `Spadj` | `runProg` with an explicit frame |
| **M** | after `span7`, `MarkUnsafePoints`, `linkpcln`: `LSym.P` (machine words), `LSym.R` (relocations), `Size`, `Align`, `FuncInfo.Pcln` (pcsp, pcfile, pcline, pcinline, pcdata), funcdata symbols, jump-table data | `runMach`: an ARM64 machine on the decoded words, relocations resolved by a link map (semantics3 §3) |
| **D** | DWARF symbols of the function (info, loc, ranges, lines) and abstract functions | none (parity only) |
| **O** | the package's goobj file (`_go_.o` in the archive) | none (stock writer, trusted) |

**Content** says whether a step's output matters for the program's behaviour (**code**), only
for the runtime (**rt**: GC, stack growth, preemption, panics, tracebacks), or only for
debuggers and tools (**dbg**). Difficulty: parity / proof (S, M, L, XL). "Proof" is a
refinement theorem for code, a validator plus runtime contract for rt, and nothing beyond
parity for dbg (noted "—").

| id | step | Go function(s) | form | content | code lines | parity / proof | milestone |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A1 | merge locals | `liveness.MergeLocals` | L2 → L2f | code (frame) | ~480 + `intervals.go` ~170 | L / XL | I3 |
| A2 | frame layout | `ssafn.AllocFrame`, `cmpstackvarlt`, `needAlloc` | L2 → L2f | code (frame) | ~220 | M / L | I3 |
| A3 | open-defer info, register-arg spill records | `emitOpenDeferInfo`, `buildssa` tail | L2f | rt | ~40 | S / M | I3 |
| B1 | stack maps and unsafe points | `liveness.Compute` (`prologue`, `solve`, `epilogue`, `markUnsafePoints`, `emit`), `bvecSet`, `emitStackObjects` | L2f → maps, symbols | rt | ~390 + ~125 + ~190 + ~65 | L / XL | I3 |
| B2 | argument liveness for tracebacks | `liveness.ArgLiveness` | L2f → maps, symbol | rt (traceback) | ~200 | M / M | I3 |
| B3 | metadata prefix | `emitArgInfo`, `emitWrappedFuncInfo`, FUNCDATA Progs | → P0 | rt (traceback, wrappers) | ~150 | M / S | I3 |
| C1 | Prog builder | `objw.Progs` (`NewProgs`, `Prog`, `Append`, `SetText`, `Flush`) | → P0 | code + rt (PCDATA) | ~115 | M / M | I3 |
| C2 | block/value loop and positions | `genssa` body, `State.Prog`, `DebugFriendlySetPosFrom` | L2f → P0 | code | ~210 | L / L | I3 |
| C3 | arm64 value emission | `arm64.ssaGenValue` (families below) | L2f → P0 | code | ~1,360 lines of `ssa.go:577-1940` | L / XL | I3 |
| C4 | arm64 block emission | `arm64.ssaGenBlock`, `State.CombJump`, `oneJump` | L2f → P0 | code | ~110 + ~30 | M / M | I3 |
| C5 | inline marks, branch and jump-table resolution, debug hooks | `genssa` tail | P0 | code + dbg | ~125 | L / L | I3 |
| C6 | `defframe` | `defframe`, `arm64.zerorange`, `padframe`, `spillArgReg` | P0 | code + rt | ~100 | M / L | I3 |
| C7 | `Compile` tail | frame-size checks, `pp.Flush`, `weakenGlobalMapInitRelocs`, `fieldtrack` | P0 → (D1) | code (relocs) | ~80 | S / M | I3 |
| D1 | `Flushplist` | `obj.Flushplist`, `mkfwd`, `InitTextSym` | P0 → M | — (driver) | ~185 + ~35 | M / M | I4 |
| D2 | linkpatch and progedit | `obj.linkpatch`, `brloop`, `checkaddr`, `arm64.progedit`, `rewriteToUseGot` | P0 → P1 | code | ~120 + ~150 | M / M | I4 |
| D3 | preprocess | `arm64.preprocess`, `stacksplit`, `SpillRegisterArgs` | P1 → P2 | code + rt | ~450 + ~30 | L / XL | I4 |
| D4 | span7: classes, sizes, pools, veneers | `span7`, `oplook`, `aclass`, `con*class`, `addpool`, `flushpool`, `checkpool`, `fixUpLongBranch`, `buildop` | P2 → M | code | ~270 + tables ~2,000 | L / L | I4 |
| D5 | span7: encoding and relocations | `asmout` (111 cases), helpers, `addrRelocType`, jump-table words | P2 → M | code | ~2,000 + ~1,900 | XL / L (validated) | I4 |
| D6 | unsafe and restartable points | `obj.MarkUnsafePoints`, `isUnsafePoint`, `isRestartable` | M | rt (preemption) | ~90 | M / L | I4 |
| D7 | pc tables and funcdata | `linkpcln`, `funcpctab`, `pctospadj`, `pctofileline`, `pctoinline`, `pctopcdata`, local `InlTree` | M | rt (pcsp, pcdata) + dbg (file, line, inline) | ~230 + ~55 | M / L | I4 |
| E1 | location lists | `ssa.BuildFuncDebug`, `BuildFuncDebugNoOptimized`, `PopulateABIInRegArgOps`, `PutLocationList*` | L2f + P0 → D | dbg | ~760 + ~245 | XL / — | I5 |
| E2 | DWARF variables, scopes, inlined calls, DIEs, line program | `dwarfgen.Info`, `assembleInlines`, `obj.populateDWARF`, `dwarf.PutDefaultFunc`/`PutConcreteFunc`/`PutAbstractFunc`, `generateDebugLinesSymbol` | M → D | dbg | ~420 + ~80 + ~55 + ~210 + ~300 + ~210 + ~125 | XL / — | I5 |
| F1 | symbol numbering, FuncInfo aux symbols (package) | `NumberSyms`, `genFuncInfoSyms`, `goobj.FuncInfo` | M, D → O | — | ~230 + ~65 + ~95 | L / — (trusted) | (I5, optional) |
| F2 | object writer and content hashes (package) | `WriteObjFile`, `goobj.Writer`, `contentHash` | → O | — | ~490 | XL / — (trusted) | (I5, optional) |

Under `-N`: A1 merges nothing (`ssa/func.go:869-880`), B2 is skipped (`liveness/arg.go:21-44`),
C2 sets `next = nil` so every block ends in an explicit jump (`ssagen/ssa.go:7183-7222`), E1
uses `BuildFuncDebugNoOptimized` for ABIInternal functions (`ssagen/ssa.go:7347-7357`).

**Order inside one function** (`ssagen/ssa.go:590-619`, `6990-7533`; `ssagen/pgen.go:303-343`;
`internal/obj/plist.go:160-177`):

1. `buildssa` tail: `ssa.Compile` → `AllocFrame` (A1, A2) → open-defer symbol, `f.RegArgs` (A3).
2. `genssa`: `NewProgs` (`TEXT`, placeholder) → `liveness.Compute` (B1, appends FUNCDATA
   ArgsPointerMaps, LocalsPointerMaps, StackObjects) → ArgInfo, ArgLiveness (B2), open-defer,
   WrapInfo FUNCDATA (B3) → block loop (C2–C4) → final `BlockExit` NOP and the disconnected
   open-defer return path → inline marks (C5) → `BuildFuncDebug` (E1) → branch and jump-table
   resolution (C5) → diagnostics → `defframe` (C6), which inserts argument spills and zeroing
   **right after `TEXT`**, in front of the FUNCDATA prefix.
3. `Compile`: frame-size check → `Flush` = `Flushplist`: `mkfwd` → `linkpatch` with `progedit`
   (D2) → `preprocess` (D3) → `span7` (D4, D5, D6) → `linkpcln` (D7) → `populateDWARF` (E2) →
   weak relocations, field tracking (C7).
4. Package (after all functions, sequentially): DWARF fixups and abstract functions (E2) →
   `NumberSyms` (F1) → `WriteObjFile` (F1, F2).

### The verified pipeline's output is the input here

`GoFV.Opt.verifiedPipelineFull` stops at `trim` and its theorem
(`GoFV.Proof.PipelineFull.verifiedPipelineFull_refines`, `docs/PASSES2.md` §0) concludes with
`runLoc` of the output. Phase 3 extends that chain by one more relation, `runMach` of the
emitted code refines `runLoc` of the `trim` output (semantics3 §2), so the end-to-end statement
becomes "the machine code refines `run` of the ssagen output". The driver already imports the
`trim` output into the compiler byte-identically (H8, `docs/DRIVER.md`); Phase 3's driver hook
(I8) moves the import point to after `genssa` and then to after `Flushplist`.

## 1. Shared infrastructure new in Phase 3

### 1.1 The Prog IR
`obj.Prog` (`internal/obj/link.go`) has `As`, `From`, `Reg`, `RestArgs` (ordered extra
sources/destinations), `To`, `RegTo2`, `Scond`, `Mark`, `Spadj`, `Pc`, `Pos`, `Link`, `Pool`,
`Optab` cache, and target pointers in `To.Val`. `obj.Addr` is a tagged union over `Type`
(`TYPE_REG`, `TYPE_CONST`, `TYPE_FCONST`, `TYPE_MEM`, `TYPE_ADDR`, `TYPE_SHIFT`, `TYPE_REGREG`,
`TYPE_BRANCH`, `TYPE_SPECIAL`, `TYPE_TEXTSIZE`, …) with `Reg`, `Index`, `Scale`, `Name`
(`NAME_AUTO`, `NAME_PARAM`, `NAME_EXTERN`, `NAME_STATIC`, `NAME_GOTREF`), `Sym`, `Offset`,
`Val`, `Class`. The Lean IR (I2) mirrors these exactly, including zero/default fields, because
later steps branch on them (`checkaddr`, `aclass`). `As` numbers are generated from
`internal/obj/arm64/a.out.go` and `anames.go` (never hand-written, as `Op` in Phase 1); the
`ssa.Op → As` map is `opcodeTable[op].asm` (already in the H2 op data).

**Identity.** Prog identity is semantic for parity: block starts (`bstart`) point at the
placeholder `pp.Next` before it is filled, several empty blocks can share one, branch targets,
`Pool` and inline marks are pointers, and `Append` gives late nodes early positions
(`ssagen/ssa.go:7099,7173-7175`; `objw/prog.go:175-188`). The port uses stable node IDs
(allocation order) separate from list order, and the export must write both.

### 1.2 Registers
Three numberings meet here: Go's dense SSA numbers (`docs/PASSES2.md` §1.1; `runLoc`'s
register file), obj register numbers (`REG_R0` …, `REG_F0` …, `REG_V0` …, arrangement and
extension encodings packed into the same `int16`, `internal/obj/arm64/a.out.go:43-299`), and the
5-bit hardware fields. `v.Reg()`, `Reg0`, `Reg1`, `RegTmp` return **obj** numbers
(`compile/internal/ssa/value.go:509-543`); `Register.objNum` is in `GoFV/SSA/RegARM64.lean`.
Registers outside regalloc: **R27 = REGTMP** (assembler and emitter scratch: nil checks, atomics'
status, jump tables, large immediates and offsets, the `>= 4096` epilogue), **R18** (platform,
never used), R28 = `g`, R29 = FP, R30 = LR, R26 = closure context, ZR/SP sharing encoding 31.
Fixed clobbers that regalloc does know: R24, R25, F16, F17 in the move loops, and the call
clobber sets (`compile/internal/ssa/_gen/ARM64Ops.go:596-654`).

### 1.3 Frame
The frame is decided in three places that must agree: `AllocFrame` (A2: negative
`FrameOffset`s of autos, `stksize`, `stkptrsize`), `defframe` (C6: `TEXT` frame size = max
outgoing args rounded + locals, padded to 16 by `padframe`, `arm64/ggen.go:13-20`), and
`preprocess` (D3: `autosize = framesize + 8` for LR, plus `extrasize` 8 or 16, which keeps the
frame 16-aligned and reserves its top for the FP the caller saved just below the caller's SP;
the prologue saves this function's caller's FP at `SP-8`, `internal/obj/arm64/obj7.go:520-700`); `aclass` then turns
`NAME_AUTO` into `autosize + offset - extrasize` and `NAME_PARAM` into `autosize + offset + 8`
SP-relative offsets (`asm7.go:2011-2095`). `FixedFrameSize = 8` (the LR slot at `0(SP)`,
`internal/sys/arch.go:136`). Picture and ABI: `docs/plans/semantics3.md` §5.

### 1.4 Positions and statement marks
Prog positions are `src.XPos` with statement marks and prologue/epilogue bits. `State.Prog`
moves a statement mark to the first instruction of a same-line run within a block, comparing
line numbers, while `DebugFriendlySetPosFrom` keeps a pending mark by `SameFileAndLine`
(`ssagen/ssa.go:6755-6833`); inline marks can move a mark to an instruction anywhere later in
the function (C5); `linkpcln` and the DWARF line program read them (D7, E2). Positions are dbg
content except where they feed pcline/pcinline that tracebacks print. The Phase 1 export already
writes positions (`docs/contracts/export.md`); Phase 3 needs the whole position table (bases,
inlining tree, `XPos` index) because `pcfile`/`pcinline` number files and inline nodes from it.

### 1.5 Symbols and shared context
`*obj.LSym` identity matters: interned constant symbols (`$f64.<bits>`, `$f32.<bits>`,
`$i64.…`, appended to `ctxt.constSyms`), `gclocals·<hash>` bitmaps (interned by content hash,
`internal/obj/sym.go:241-250`), `<wrapped>.wrapinfo` shared by `LookupInit`, `.stkobj`,
`.arginfo<ABI>`, `.argliveinfo`, `.opendefer`, jump tables `<fn>.jump<bid>`, runtime symbols
(`runtime.morestack_noctxt`, `runtime.panicBounds`, `gcWriteBarrier<n>`, `memequal`). Several are
shared across functions compiled concurrently, so their creation order is not per-function; the
port returns them as definitions (as Phase 2's new autos) and the importer resolves them by name.

### 1.6 Runtime-metadata encodings
Stack-map bitmaps (two `uint32`s then bit vectors, `liveness/plive.go:1309-1380`), stack objects,
open-defer info (two uvarints), ArgInfo bytecode, ArgLiveInfo, the pc-value tables (zig-zag
value deltas, unsigned pc deltas in units of `MinLC = 4`, `internal/obj/pcln.go:25-136`),
`PCDATA_PanicBounds` (`internal/abi/bounds.go:29-70`), unsafe-point values −1/−2/−3/−4/−5
(`internal/abi/symtab.go:107-139`). Each has a runtime decoder (`runtime/symtab.go`,
`runtime/stkframe.go`, `runtime/panic.go`, `runtime/traceback.go`), which is where its meaning
is defined; a proof of an encoder is a round-trip against a Lean transcription of that decoder.

## 2. What the export must add (consolidated; for I1)

A new export format, `gofv-prog 1`, written by the patched compiler next to the `gofv-ssa`
file (same selection, same function order), one record per function, at these cut points:

1. **After `AllocFrame`** (L2f): `Dcl` before and after (stable name IDs, class, flags `Used`,
   `Needzero`, `OpenDeferSlot`, `Addrtaken`, type layout with pointer data), `FrameOffset`s,
   `stksize`, `stkptrsize`, `stkalign`, `OptDcl`, the MergeLocals partition (leaders,
   followers in order), `f.RegArgs`, the open-defer symbol.
2. **Liveness** (B1, B2): the variable vector, `Map.Vals` (stack-map index per value ID),
   `UnsafeVals`, `UnsafeBlocks`, `DeferReturn`, the partially live argument set, the arg
   liveness block/value maps, and every produced symbol (`gclocals·…`, `.stkobj`,
   `.argliveinfo`) with data, relocations, alignment and attributes.
3. **After `defframe`, before `Flush`** (P0): every Prog with a stable ID (allocation order),
   the list order, every `Addr` field (registers as obj numbers, floats as raw bits, symbols by
   definition number), `RestArgs`, `RegTo2`, `Scond`, `Mark`, positions with statement and
   xlogue bits, branch targets and `Pool` as IDs; `FuncInfo` fields set so far (spills
   `RegSpill{Reg,Reg2,Addr,Spill,Unspill}` in order, `InlMarks`, `JumpTables`, `ArgInfo`,
   `WrapInfo`, `OpenCodedDeferInfo`); the genssa side tables `bstart` (block → Prog ID) and
   `valueToProgAfter` (value → Prog ID), which E1 and the driver need. The `genssa` diagnostics
   (`-S`, HTML, `GOSSAFUNC`) run **before** `defframe`, so they are not this snapshot
   (`ssagen/ssa.go:7411-7533`).
4. **Inside `Flushplist`**: the graph after `linkpatch`, after `preprocess` (before `span7`
   strips the packed `extrasize` from `TEXT`), and after `span7`: PCs, sizes, the selected
   `Optab` index and operand classes per Prog (an `oplook` histogram gives the exact optab
   coverage, §4 D4), pool entries and flush points, inserted veneers, `LSym.P`, `LSym.R` in
   append order, `Size`, `Align`, jump-table words.
5. **After `linkpcln`**: the pcsp, pcfile, pcline, pcinline and pcdata symbols' bytes, the
   funcdata slot table, `UsedFiles`, the local inline tree, and decoded intervals as a
   secondary view.
6. **DWARF** (E1, E2): symbolic location lists (block/value endpoints) and their resolved PCs,
   the `dwarf.Var`/scope/inline-call records, and the bytes and relocations of the function's
   `SDWARFFCN`/`SDWARFLOC`/`SDWARFRANGE`/`SDWARFLINES` symbols, with the package inputs they
   read (`DwTextCount`, `UseBASEntries`, `Experiment.Dwarf5`, CU file numbering).
7. **Config**: `buildcfg.GOARM64` (default `v8.0`, `cmd/dist/build.go:139-143`), `Experiment` flags, `Flag_dynlink`,
   `Flag_shared`, `Flag_linkshared`, `Flag_locationlists`, `Flag_optimize`, `Flag_maymorestack`,
   `base.Debug.MergeLocals`, `base.Flag.N`, `ClobberDead`/`ClobberDeadReg`, `CompilingRuntime`,
   `GenDwarfInl`.

Existing listings are not substitutes: `-S`/`Debugasm` prints final Progs, bytes and relocations
but not intermediate graphs or identities; worse, **`Debugasm` disables Prog reuse and sorts
`LSym.R` in place with an unstable sort by `Off` before content hashing**
(`internal/obj/objfile.go:33-38,945-968`; `internal/obj/util.go:221-223`), so the exporter must
not turn it on, and must snapshot graphs before `objw` recycles them. `go tool objdump` and the
`cmd/internal/goobj` reader are secondary oracles for the final bytes and metadata.

Parity is checked per function at each cut point, as Phase 1/2 check per pass: parse the
record, run the Lean step on the previous cut's state, compare with the next cut. Package-level
artefacts (symbol indices, string table, hashes, the archive) are compared whole-package by the
driver's byte-identical object check (I8), not per function.

## 3. Nondeterminism and other global hazards

- **Concurrent backend.** Functions are compiled on `-c` workers; `ctxt.constSyms`, interned
  `gclocals·` symbols, `LookupInit` wrapper info, DWARF fixups (under a mutex) and stack-size
  diagnostics are shared. `NumberSyms` sorts the late constant symbols by name, which makes the
  object deterministic (`internal/obj/sym.go:255-340`). Per-function parity must therefore
  compare these symbols as definitions by name, not by creation order.
- **Unstable sorts with possible ties** (port with the shared `GoFV.Util.PdqSort`, as Phase 2):
  stack objects by frame offset only (`liveness/plive.go:1475-1476`); MergeLocals' candidates
  after eviction, rebuilt by ranging the map `rawcands` then sorted by `nameLess`
  (`liveness/mergelocals.go:617-625,655-672`; **[INFERENCE]** if two candidates tie on every
  key, Go map order reaches the partition, a reproducibility wart to check on the corpus);
  `buildop`'s optab sort, whose comparator ignores a5, size and flags (`asm7.go:2739-2793`;
  deterministic for the fixed table, but the port must use the same algorithm); debug-info piece
  sort by offset (`ssa/debug.go:592-665`); `Autot` ranged then sorted by name
  (`dwarfgen/dwarf.go:126-149`); field tracking sorted by name (off: `Experiment.FieldTrack`).
- **Relocation order.** `WriteObjFile` and `Debugasm` sort `LSym.R` by `Off` with
  `slices.SortFunc` and no tie-break (`internal/obj/objfile.go:127-137,177-184,966-968`).
  Marker relocations (`R_USEIFACE`, `R_USETYPE`, `R_USEFIELD`) share offsets, so equal keys do
  occur; the per-function comparison uses the append order (before the writer), the package
  comparison the written order.
- **Debug flags change output.** `Debugasm` (above), `-clobberdead` (inserts `OpClobber`,
  `liveness/plive.go:943-1111`), `-d=locationlists=N` (`N/1000` forces iterations,
  `ssa/debug.go:562-573`). The export runs with all of them off.
- **Known upstream candidate: wrong value in arm64 bounds-panic messages (#541).** In
  `LoweredPanicBoundsCR` (`compile/internal/arm64/ssa.go:1783-1799`), an out-of-range constant
  `x` (outside `[0, BoundsMaxConst = 31]`) is moved into R0/R1 but `xIsReg` is never set, so the
  PCDATA tells `runtime.panicBounds64` (`runtime/panic.go:211-236`) that `x` is the constant
  0 or 1. Reproduced independently for this survey: `func f(s []int, j int) []int { return
  s[100:j] }` with `j = 50` panics with `slice bounds out of range [0:50]` on linux/arm64 under
  qemu and `[100:50]` on amd64 (amd64, 386, loong64, mips, mips64 set `xIsReg`; riscv64, ppc64,
  s390x share the omission). It changes only the panic value, not control flow. The port must
  reproduce it (parity). It **is** a refinement failure: Phase 1's outcome `panicked (.bounds
  kind x y)` carries `x` (`GoFV/SSA/Sem/Val.lean:349-352`), and the machine-level `panicBounds`
  hook decodes the PCDATA as the runtime does (semantics3 §6), so the PanicBounds check (C3,
  D7) rejects such a call site and the function is unverified at Phase 3.

## 4. Per-step sections

Each section gives: **Source**, **Input → output**, **What it does**, **Parity traps**,
**Export needs** (beyond §2), **Proof** (semantics, what is trusted, difficulty).

### A1 merge locals

**Source:** `compile/internal/liveness/mergelocals.go:72-122,296-393,424-1046`;
`liveness/intervals.go:87-219,243-389`; called from `ssagen/pgen.go:168-208` inside
`AllocFrame`. Enabled by default (`base.Debug.MergeLocals = 1`, `compile/internal/base/flag.go:193`);
no candidates under `-N` (`ssa/func.go:869-880`).

**Input → output:** L2 (blocks, schedule, uses, `f.RegAlloc`, symbolic effects), `Dcl` →
partitions of `*ir.Name`s (leader, followers in order). `AllocFrame` gives followers their
leader's offset.

**What it does:** candidates are used `PAUTO`s larger than 24 bytes that are not address-taken,
not open-defer slots, not marked non-mergeable. It reruns the liveness dataflow with
`conservativeWrites = true` (a dead write must not clobber another variable's live storage),
tracks materialised addresses within blocks (`AddrSinkArg`), evicts candidates whose address
escapes a block, builds half-open live intervals in reverse layout/schedule order and greedily
merges candidates whose intervals do not overlap the leader's accumulated union, within regions
of equal or decreasing size and alignment.

**Parity traps:** the unstable post-eviction sort (§3); hash-based deselection
(`MergeLocalsHash`) is tested on prospective followers only (`mergelocals.go:424-445,736-740`);
regions do not require identical pointer layouts; `Kill(K)` starts the surviving segment at
`K+1`; `ir.Name` identity throughout.

**Export needs:** candidates in order, eviction decisions, intervals, partitions.

**Proof:** semantics-relevant: two `runLoc` slots (`LocalSlot`s of different names) become one
byte range. Statement: under the interval certificate, no two merged names are live at once
under `runFrame` (semantics3 §4), including dead writes and address uses; this is a
location-sharing argument like the regalloc checker's (`docs/plans/regalloc-check.md`), done
as a **validator**: recompute liveness on the merged layout and check disjointness. **L / XL**.

### A2 frame layout

**Source:** `ssagen/pgen.go:30-294` (`cmpstackvarlt`, `needAlloc`, `AllocFrame`),
`ssagen/ssa.go:590-619` (call site).

**Input → output:** L2 + `Dcl` → `Name.FrameOffset` (negative, from the frame top),
`Used`, reordered and truncated `Dcl`, `OptDcl` (dropped declarations, for DWARF), `stksize`,
`stkptrsize` (pointer-containing prefix), `stkalign`.

**What it does:** `needAlloc` selects `PAUTO` and register-returned `PPARAMOUT`; `Used` is
recomputed from direct `LocalSlot` homes in `f.RegAlloc` and name-valued auxes; a stable sort by
(non-allocated first, by ABI offset; merge leaders before followers; used; has pointers;
`Needzero`; alignment descending; the open-defer expression `return a.OpenDeferSlot()`; defer
index descending; name); followers move right after their leader; offsets are assigned
cumulatively with each object's alignment, a zero-size object after a pointer object takes one
byte; both sizes round to `stkalign`.

**Parity traps:** port the comparator's expression, not its comment (`pgen.go:78-84`, the
comment about open-defer slots contradicts the code); stable sort, `Dcl` order for ties;
truncation at the first unused allocatable name; new autos from `stackalloc`/`SplitSlot`
already exist (Phase 2, `docs/PASSES2.md` §1.6).

**Proof:** the frame relation of semantics3 §4: distinct live slots get disjoint, aligned
ranges inside `[SP+8, SP+8+stksize)`, the pointer prefix covers every pointer word. Decided by a
checker on the layout (no theorem about the sort). **M / L**.

### A3 open-defer info and register-argument spill records

**Source:** `ssagen/ssa.go:263-290` (`emitOpenDeferInfo`), `:595-617`.

**Input → output:** L2f → `<fn>.opendefer` (two uvarints: `-deferBits.FrameOffset`,
`-firstClosure.FrameOffset`; closure slots must be consecutive pointer words), and
`f.RegArgs []ssa.Spill{Reg, Offset, Type}` for every register-assigned input component in ABI
order (used ones or not).

**Proof:** rt: the open-defer record is read by the panic/`deferreturn` machinery
(`runtime/panic.go`), outside the refinement statement (a panic ends the run, Phase 1); the
spill records become the morestack spill code (C3 register args, D3). **S / M**.

### B1 stack maps, unsafe points, stack objects

**Source:** `liveness/plive.go:155-491` (`Map`, `getvariables`, `valueEffects`), `:493-663`
(`IsUnsafe`, `markUnsafePoints`, `hasStackMap`), `:667-894` (`prologue`, `solve`, `epilogue`),
`:911-940` (`compact`), `:1309-1389` (`emit`), `:1395-1460` (`Compute`), `:1463-1531`
(`emitStackObjects`), `:1533-1569` (fat types); `liveness/bvset.go:9-98`.

**Input → output:** L2f (`Dcl` after A2, layout blocks, schedule, `f.RegAlloc` through
`ssa.AutoVar` for `LoadReg`/`StoreReg`/`KeepAlive`/`ArgIntReg`) → `Map{Vals, UnsafeVals,
UnsafeBlocks, DeferReturn}` (stack-map index per call value; missing = don't care), the set of
partially live arguments, `Needzero` marks, the args and locals bitmap symbols, `.stkobj`, and
FUNCDATA Progs 0, 1, 2 in that order.

**What it does:** tracks pointer-containing non-heap `PAUTO`/`PPARAM`/`PPARAMOUT` (a stack-root
analysis; registers are dead across calls in ABIInternal, so call sites need only stack roots).
`VarDef` kills (only non-fat variables are killed by plain writes), `VarLive`/address-taking
read; backward dataflow over postorder to a fixpoint; `epilogue` records the live-after state at
each call, adds result and open-defer slots when the function has defers; maps are deduplicated
in first-insertion order with an FNV-1 hash table (`bvset.go`); locals bitmaps are exactly
`stkptrsize / 8` bits wide (the runtime finds the frame base from the width). Unsafe points: the
whole function if runtime or `nosplit`; otherwise ops with `unsafePoint` and, for each `WBend`,
the write-barrier diamond from the load of `runtime.writeBarrier` to `WBend` (found by memory
dependence and symbol identity). Calls to `wbZero`/`wbMove` get no stack map.

**Parity traps:** `Dcl` order, `ir.Name` identity, fat-type rules, `bvecSet`'s wrapping `uint32`
hash including unused tail bits, `emit`'s strict `>` choosing the first maximal argument,
stack-object sort (§3), `-clobberdead`.

**Proof:** rt, the GC and stack-copy contract (semantics3 §6): at every call's return address,
(i) **coverage**: every stack word that holds a pointer the rest of the run (or a defer) may use
is in the map, and every pointer into an address-taken stack object is reachable from the stack
objects; (ii) **validity**: every word the map lists holds nil or a valid pointer (hence the
`Needzero` zeroing, C6). Proven as a validator over `runFrame` states with provenance (a
pointer-typed `runLoc` slot value is a `Val.ptr` or nil), not as a proof of Go's algorithm;
unsafe points: every write-barrier diamond and every R27 live range is unsafe (with D6).
**L / XL**.

### B2 argument liveness for tracebacks

**Source:** `liveness/arg.go:21-340`; consumers `ssagen/ssa.go:7101-7105,7166-7171`.

**What it does:** for register arguments spilled by `StoreReg`, a forward "definitely
initialised" analysis (one reverse-postorder pass, intersection at joins), at most 10 pieces at
offsets ≤ 255, deduplicated maps, emitted as `.argliveinfo` with indices rewritten to byte
offsets; `PCDATA_ArgLiveIndex` changes are emitted around values. Skipped under `-N` and without
register arguments.

**Parity traps:** the 10-piece truncation before trimming always-live slots; delayed emission
until an op may fault; `-1` versus absent.

**Proof:** traceback display only (which spilled argument words are printed). Parity only, or a
round-trip lemma. **M / M** (proof optional).

### B3 metadata prefix

**Source:** `ssagen/ssa.go:6836-6958` (`emitArgInfo`), `:6961-6987` (`emitWrappedFuncInfo`),
`:6999-7016`.

**What it does:** FUNCDATA order after `TEXT`: ArgsPointerMaps, LocalsPointerMaps,
StackObjects?, ArgInfo?, ArgLiveInfo?, OpenCodedDeferInfo?, WrapInfo?. ArgInfo is a bytecode of
(offset, size) leaves and aggregate delimiters in signature order, with depth and component
limits and dictionary skipping; WrapInfo is a 4-byte reference to the wrapped function, keyed by
the wrapped symbol's name.

**Proof:** traceback/wrapper metadata: parity only. **M / S**.

### C1 the Prog builder (`objw`)

**Source:** `compile/internal/objw/prog.go:41-210`, `objw.go`.

**What it does:** `Prog(as)` first emits pending PCDATA: when both change, the order is
**unsafe-point PCDATA, stack-map PCDATA, then the instruction** (the stack-map branch recurses
into `Prog(APCDATA)`, which emits the unsafe transition first, `prog.go:127-146`); then fills the
placeholder, links a new one, sets `As` and position. `StackMapDontCare = -1000` suppresses
stack-map changes. `Append` inserts after a given node without PCDATA (used by `defframe`). Prog
numbers (`Pc`) are allocation order until assembly.

**Proof:** list building is parity; the PCDATA it inserts are checked by B1/D7's validators.
**M / M**.

### C2 the block/value loop and positions

**Source:** `ssagen/ssa.go:6708-6833,7018-7255`.

**What it does:** finds the entry statement position; for each block in layout order records
`bstart[b.ID] = pp.Next`, emits arg-live PCDATA, then each scheduled value. Generic ops handled
here: **no code** for `InitMem`, `Arg`, `SP`, `SB`, `Select0/1/N`, `MakeResult`, `GetG`,
`VarDef`, `VarLive`, `KeepAlive`, `WBend`; `Phi` checks that every argument has the phi's home
(`CheckLoweredPhi`, Go interface `!=` on locations); `Convert` checks equal registers; `InlMark`
emits a hardware NOP (`HINT $0`) and records the mark. Everything else (including `Copy`,
`LoadReg`, `StoreReg`, `ArgIntReg`) goes to `Arch.SSAGenValue` with `NextLive`/`NextUnsafe` set
from B1's maps. Empty self-loop blocks get a statement NOP; the last block if `Exit` gets a NOP so
a non-returning call's return PC stays inside the function; with open defers a disconnected
`CALL runtime.deferreturn` path that reloads register results and `RET`s.

**Parity traps:** generic no-code ops do not refresh pending liveness (`ssa.go:7118-7171`); a
block start may denote a future Prog shared by empty blocks; the open-defer suffix changes
`NextLive` but not `NextUnsafe`; arm64 has no hot-block alignment (`ssa.go:7064-7079`).

**Proof:** the core simulation (semantics3 §7): a `runLoc` block step is matched by running its
Progs; no-code ops are stutter steps whose `runLoc` effect is already in the state relation
(`Arg` reads the incoming slot; `Select` reads a pair home; `SP`/`SB`/`GetG` are fixed
registers); `CheckLoweredPhi` is exactly the `runLoc` premise that a `Phi` does nothing.
**L / L**.

### C3 arm64 value emission

**Source:** `compile/internal/arm64/ssa.go:577-1940` (`ssaGenValue`), helpers `:23-183`,
`:285-342`, `:2095-2223`; `ssagen/ssa.go:7680-7715` (`AddAux`), `:7857-7868` (`AddrAuto`),
`:7872-7942` (`Call`, `TailCall`, `PrepareCall`). `simdssa.go` only under
`GOEXPERIMENT=simd` (off). No direct `GOARM64` test: LSE `Variant` atomics are chosen upstream
(`ssagen/intrinsics.go:400-434`), so both forms can occur in one function.

**Families** (one Prog per op unless stated; "P/proof" is per family):

| Family | Ops | Prog shape | P / proof |
| --- | --- | --- | --- |
| Moves, spills | `Copy`, `MOVDreg` (nothing if same register or memory), `MOVDnop`, `ZERO` (nothing), `LoadReg`, `StoreReg` (`loadByType`/`storeByType` at `AddrAuto`), `ArgIntReg`/`ArgFloatReg` (first one consumes all `f.RegArgs` into `FuncInfo` spill records, pairing adjacent equal-class slots; no code) | `MOVD`/`FMOVS`/`FMOVD`/`VMOV .B16`; `MOV{B,BU,H,HU,W,WU,D}`, `FMOV{S,D,Q}` | S / M |
| Integer ALU | 29 two-operand (`ADD` … `RORW`, `OR→ORR`, `XOR→EOR`, `MOD→REM` …), `MADD`/`MSUB`(W), 10 immediate forms, flag-setting tuple forms (`ADDS`, `ADCS`, `SUBS`, `SBCS`, `NEGS`, `ADDSconstflags`), `ADCzerocarry`, `NGCzerocarry` | `From=R(a1), Reg=a0, To=R(d)` | S / M (div/rem L) |
| Shifts, bitfields, extensions | shifted operands via `genshift` (`TYPE_SHIFT`), `EXTR`, `BFI`/`BFXIL`/`SBFIZ`/`SBFX`/`UBFIZ`/`UBFX` (`AuxInt>>8`, `&255`), `MOV{B,BU,H,HU,W,WU}reg` (**elided or turned into `MOVD`** when the copy chain leads to a `LoadReg` of the same signedness and width, `:1353-1386`), `MVN`, `NEG`, `REV*`, `RBIT`, `CLZ` | | M / M |
| Compares, conditionals | `CMP`/`CMN`/`TST` (reg, const, shifted), `FCMP{S,D}`(0), `CSEL`/`CSEL0`/`CSINC`/`CSINV`/`CSNEG`/`CSETM` (condition from `condBits[CCop]`, a Go opcode number), 8 `CCMP`/`CCMN` forms (`ARM64ConditionalParams`), 20 flag predicates → `CSET`; `FlagConstant`/`InvertFlags` are fatal here | `TYPE_SPECIAL` condition | M / M (float L) |
| Floats | arithmetic, FMA (`Reg=a0, From=a1, RestArgs=[a2]`), `FMOV{S,D}const` (`TYPE_FCONST` from raw bits), conversions, `FRINT*`, `FMOV{S,D}{gpfp,fpgp}` (bit moves), `LoweredRound*F` (nothing), popcount `VCNT`/`VUADDLV` | | S / XL (IEEE, already in `GoFV.IEEE`) |
| Constants, addresses, memory | `MOVDconst`, `MOVDaddr` (`TYPE_ADDR`, SB symbol or SP name or plain offset), 10 loads, 6 pair loads (`TYPE_REGREG` result), 16 indexed loads (`Index` with `REG_LSL` scale), 7 stores, 11 indexed stores, 5 pair stores | `TYPE_MEM` + `AddAux` | M / L |
| Atomics | `LDAR*`, `STLR*` (1); LL/SC loops with `CBNZ R27` retry: exchange 3, add 4, CAS 6, and/or 4; LSE variants: `SWPAL` 1, `LDADDAL`+`ADD` 2, `CASAL` 4, `LDCLRAL` 2, `LDORAL` 1 | local back edge | M / XL |
| Bulk zero/move | `LoweredZero` (`STP ZR,ZR` per 16 bytes, overlapping tail), `LoweredZeroLoop` (count in `RegTmp`, 4 `STP.P`, `SUB`, `CBNZ`, tail), `LoweredMove` (nothing if same registers; `FLDPQ`/`FSTPQ` 32-byte chunks, `FMOVQ`, overlapping `MOVD` tail, scratch R25/F16/F17), `LoweredMoveLoop` (R24 count). **No `DUFFZERO`/`DUFFCOPY` at this pin** | 0 to 7+tail Progs | M / L |
| Calls | `CALLstatic`/`closure`/`inter` (`s.Call`: `To=Sym` or `To=(Ra0)`), `CALLtail*` (`RET` to symbol), `LoweredWB` (`CALL gcWriteBarrier<n>`), `LoweredMemEq` (`CALL memequal`), `LoweredPanicBounds{RR,RC,CR,CC}` (0–2 `MOVD`, `PCDATA $PanicBounds`, `CALL panicBounds`; the CR bug, §3) | | M / XL (runtime contracts) |
| Misc | `LoweredNilCheck` (**`MOVB (Ra0), R27`**), `LoweredGetClosurePtr` (nothing; R26 checked), `LoweredGetCallerSP` (`MOVD $-8(FP)` as `NAME_PARAM` address), `LoweredGetCallerPC` (`GETCALLERPC`, expanded in D3), `PRFM`, `DMB`, `OpClobber` (3), `OpClobberReg` (1) | | S / L |

**Parity traps:** obj register numbers, not dense ones; `Reg0`/`Reg1` index `LocPair`; absent
`Reg` in unary and in-place forms; raw float bits (signed zero, NaN payloads); width-specific
atomics and `RegTo2`; the extension elision depends on SSA ancestry and load types, not on the
current bits; the order of `MOVD`s in the bounds-panic sequence and the register chosen (R0, or
R1 on collision).

**Proof:** per family, a lemma "from a machine state related to a `runLoc` state before `v`,
the `runProg` run of `v`'s Progs reaches a state related to `runLoc`'s after `v`". With the
instruction semantics built from the same `BitVec` functions as `evalArm64` (semantics3 §3),
the single-instruction families are close to `rfl`; flags need the `Flags` ↔ NZCV relation; the
extension elision needs a lemma that the register already holds the extended value (`runLoc`'s
`signOf` already tracks this, `docs/plans/semantics2.md` §7); memory ops need the memory
injection; atomics use the single-threaded assumption (Phase 2's §8); calls are hooks. **L / XL**.

### C4 arm64 block emission

**Source:** `arm64/ssa.go:1968-2093` (`blockJump`, `leJumps`, `gtJumps`, `ssaGenBlock`),
`ssagen/ssa.go:7647-7677` (`oneJump`, `CombJump`).

**What it does:** `Plain`/`Defer`: `JMP` unless the successor is `next`; `Ret`: `RET`;
`Exit`/`RetJmp`: nothing; conditional kinds: one inverted branch if `Succs[0]` is next, one
branch if `Succs[1]` is next, else branch + `JMP` (order swapped when `Likely ==
BranchUnlikely`; unknown behaves as likely); `Z`/`NZ`/`ZW`/`NZW` → `CBZ`/`CBNZ`(W) on the
control register; `TBZ`/`TBNZ` with the bit in `From`; `LEnoov`/`GTnoov` two conditional
branches (plus `JMP`); `JUMPTABLE`: `MOVD (Rtable)(Rindex<<3), R27; JMP (R27)`; `First` is
fatal (removed upstream).

**Proof:** control-flow simulation with fallthrough (block order becomes semantic here, as
noted for `loop rotate` in `docs/plans/semantics2.md` §7); jump tables need the table's data
(D5) and the `R_ADDR` relocation contract. **M / M** (jump tables M / L).

### C5 inline marks, branch and jump-table resolution, debug hooks

**Source:** `ssagen/ssa.go:7257-7409`; `ssagen/pgen.go:383-403` (`StackOffset`).

**What it does:** for each inline mark, the first later instruction anywhere in the function
with the same column-1 position absorbs all marks at that position (statement mark set, mark
NOPs turned into `ANOP` with no position); remaining marks stay as NOPs. A frameless function
without calls whose first instruction is inlined gets a NOP at the entry position spliced in
front. Then `BuildFuncDebug` (E1) is called and its `GetPC` callback installed; branches are
resolved in append order with `SetTarget(bstart[target])`; jump tables become
`FuncInfo.JumpTables` entries (targets only; no data yet).

**Parity traps:** not limited to the next instruction or the same block; `hasCall` and the
frameless test use `stksize`, not the final frame; `GetPC` is evaluated after assembly.

**Proof:** NOP changes are stutter steps; branch resolution is part of C4's simulation. **L / L**.

### C6 `defframe`

**Source:** `ssagen/ssa.go:7536-7641`; `arm64/ggen.go:13-44`; `arm64/ssa.go:2095-2112`.

**What it does:** sets `TEXT`'s `To` to `TYPE_TEXTSIZE` with `Val = round(ArgWidth, 8)` and
`Offset = padframe(round(maxarg, align) + stksize)`; for optimised functions with register
arguments, spills the pointer-carrying register pieces of partially live arguments that no
`StoreReg` before the first call already spills; zeroes the `Needzero` autos, merging ranges
separated by at most 16 bytes, with `STP ZR, ZR` while `off < 512` then `MOVD ZR`. Both are
inserted right after `TEXT`, before the FUNCDATA prefix, without PCDATA.

**Proof:** code + rt: the zeroing and spills establish B1's validity (ii) at the first safe
point; they write only dead or not-yet-initialised slots. **M / L**.

### C7 the `Compile` tail

**Source:** `ssagen/pgen.go:296-343,348-378,407-423`.

**What it does:** rejects frames ≥ 1<<30 (before and after `genssa`), `Flush`es, ORs `R_WEAK`
into relocations to outlined map-init symbols (unless `WrapGlobalMapCtl == 1`), appends sorted
`R_USEFIELD` relocations when `Experiment.FieldTrack` is on (off).

**Proof:** linker-reachability metadata: trusted (linker contract). **S / M**.

### D1 `Flushplist`

**Source:** `internal/obj/plist.go:24-269`, `internal/obj/ld.go:46-83`.

**What it does:** splits the list at `TEXT`, rewrites assembly-only placeholder FUNCDATA (not
reached by compiled code), and runs `mkfwd → linkpatch (with progedit) → preprocess → assemble
→ linkpcln → populateDWARF` per function; `linkpcln` and DWARF run only if `ctxt.Errors == 0`.
`InitTextSym` (called by the compiler before `genssa`) appends the symbol to `ctxt.Text` and
sets `FuncID`, `FuncFlag`, `StartLine`, NOSPLIT/NEEDCTXT/WRAPPER attributes.

**Proof:** orchestration; composition of D2–D7. **M / M**.

### D2 linkpatch and progedit

**Source:** `internal/obj/pass.go:37-184` (`checkaddr`, `linkpatch`, `brloop`);
`internal/obj/arm64/obj7.go:45-65,306-473` (`zrReplace`, `progedit`, `rewriteToUseGot`);
`internal/obj/sym.go:159-200`; `asm7.go:3469-3499` (`chipfloat7`).

**What it does:** per Prog, `checkaddr` on every operand, then `progedit`: clear cached classes;
`$0` → `ZR` for the `zrReplace` opcodes; symbolic `B`/`BL`/`RET` targets → `TYPE_BRANCH`;
`VMOV{S,D,Q}` integer constants → loads of `$i32`/`$i64`/`$i128` symbols; `FMOV{S,D}` constants
stay immediate only if `chipfloat7 > 0`, `+0` becomes `ZR`, otherwise loads of `$f32.<bits>`/
`$f64.<bits>` read-only symbols; with `Flag_dynlink` GOT rewrites (off for ordinary builds).
Then local branch targets are resolved by PC and, with `Flag_optimize`, `JMP` chains collapsed
(`brloop` gives up after 5,000 hops).

**Parity traps:** float conversion for `FMOVS` (float32 for the zero test and symbol name,
float64 for the immediate test); `> 0` not `>= 0`; progedit sees nodes it inserted.

**Proof:** `runProg` refinement P0 → P1: constant symbols hold their bits (a linker/rodata
contract), jump-chain collapse preserves targets. **M / M**.

### D3 preprocess

**Source:** `internal/obj/arm64/obj7.go:67-304` (`stacksplit`, maymorestack),
`:475-909` (`preprocess`); `internal/obj/link.go:1251-1287` (`SpillRegisterArgs`,
`UnspillRegisterArgs`).

**What it does:** leaf detection (no `BL`); a leaf with no locals is `NOFRAME`; framed functions
get `autosize = framesize + 8 (LR) + extrasize (8 or 16)`; leaves below `StackSmall` (128) become
`NOSPLIT`. Stack check: load `g.stackguard0` (`16(R28)`), compare with SP (small frames), with
`SP - (framesize - StackSmall)` in R17 (medium) or with an underflow check (large); `BLS` to a
slow path appended at the end: entry stack-map PCDATA, unsafe PCDATA, the `FuncInfo` spills in
order, `MOVD LR, R3`, `BL runtime.morestack_noctxt` (or `morestack`/`morestackc`), end-unsafe,
unspills in the same (forward) order, `B` back to the check. Prologue: `autosize ≤ 0xf0`:
`MOVD.W R30, -autosize(RSP)` then `MOVD R29, -8(RSP)`; larger: `SUB $autosize, RSP, R20`,
`STP (R29, R30), -8(R20)`, unsafe `MOVD R20, RSP`; then `SUB $8, RSP, R29`. `RET`: restore FP and
LR, pop the frame (via R27 when ≥ 4096 bytes), `RET` or `B sym` for tail calls.
`GETCALLERPC` → `MOVD LR` (leaf) or `MOVD (RSP)`. Every SP change carries `Spadj`. No wrapper
`argp` adjustment and no Duff frame-pointer handling exist on arm64 at this pin.

**Parity traps:** `< StackSmall` for NOSPLIT vs `<= StackSmall` for the check form; artificial
`Spadj` on the slow-path entry and back edge; prologue-end position on the first SP-changing
instruction.

**Proof:** code: frame establishment and teardown relate the caller's machine state to the
body's (semantics3 §5: `BodyEntry`/`Exit`), the stack check and slow path are a hook (morestack
may move the stack, semantics3 §6), spills/unspills preserve the argument registers across it.
Also the FP chain (unwinders) and pcsp (D7). **L / XL**.

### D4 span7: classes, sizes, literal pools, branch veneers

**Source:** `internal/obj/arm64/asm7.go:49-67,1107-1443,1585-1588,7553-7581` (`span7`, pools,
`fixUpLongBranch`, `brdist`), `:318-938` (`optab`, ~550 entries), `:1590-2246` (`aclass`,
`conclass`, `con32class`, `con64class`), `:2254-2356` (`oplook`), `:2739-2815` (`buildop`);
`internal/obj/util.go:754-813` (alignment).

**What it does:** classifies operands (registers, ZR/SP, shifted/extended, immediates by
encodability: add, MOVZ/MOVN, bitmask, 2–4-instruction wide constants, pool literals;
auto/param offsets resolved against `autosize`/`extrasize`), finds the first matching optab
entry, sizes every Prog; adds pool literals (large memory offsets; large integer constants are
`MOVZ`/`MOVK` sequences, not pool loads), flushing the pool when it nears ±1 MiB or at the end
(with a branch around it unless after `B`/`RET`); then iterates PC assignment, inserting
veneers for out-of-range 14-/19-bit conditional branches until no insertion; then emits words
(D5); pads the function with zero bytes to 16.

**Parity traps:** `changed = changed || c.fixUpLongBranch(p)` stops fixing after the first
change in a pass; pools are placed once, before veneers; pool dedup compares `To` only;
`Prog.Optab` is a 1-based index into the sorted table; symbol `Align` changes load/store size.

**Proof:** not proven directly. The output is checked by the **object validator** (semantics3
§3 (c)): every word decodes to the instruction(s) the Prog's semantics prescribes at its PC,
pools are unreachable, veneers preserve the branch. **L / L** (validator).

**Coverage.** ~550 optab entries and 111 `asmout` cases exist; the compiler's subset is
estimated at 250–400 entries and 55–70 cases (**[INFERENCE]**, from the emitter's shapes; the
I1 `oplook` histogram on the corpus replaces the estimate). The generated SVE tables
(`inst_gen.go`, `encoding_gen.go`, `goops_gen.go`, case 127) are unreachable from compiled code
(no SVE ops in the arm64 back end) **[INFERENCE]**. Measured (I4, #550): the sorted table has 548 entries; the
quick corpus uses 194 of them and 58 `asmout` cases (0–9, 12, 14–18, 20–25, 27, 29–32, 39, 40,
43–47, 51–56, 58, 59, 62, 64–68, 74–77, 83, 85, 87, 88, 91, 98, 99).

### D5 span7: encoding and relocations

**Source:** `asm7.go:3616-6233` (`asmout`), helpers `:6241-8538`, constant materialisation
`:1977-2008,8086-8250`.

**What it does:** per Prog, 1–5 words from its case; relocations `R_CALLARM64` (4, `BL`/`B`
symbol), `R_CALLIND` (marker), `R_ADDRARM64` (8, `ADRP`+`ADD`), `R_ARM64_PCREL_LDST{8,16,32,64}`
(`ADRP`+load/store), `R_ADDR` (8, jump-table words), `R_ARM64_TLS_LE/IE`, `R_ARM64_GOTPCREL`
(not in ordinary builds); jump tables written as 8-byte absolute addresses of target PCs.

**Parity traps:** constant materialisation search order and ties; SP vs ZR; relocation append
order, addends and placeholder bits.

**Proof:** **XL** to port exactly (parity), but the proof does not depend on the port: the
validator decodes the words with the semantics' decoder and compares with the Prog semantics;
relocations are checked against the symbols and addends the Prog names, and their application
is the linker contract. **XL / L**.

### D6 unsafe and restartable points

**Source:** `asm7.go:1212-1216,1311-1334` (`isUnsafePoint`, `isRestartable`);
`internal/obj/plist.go:272-413` (`MarkUnsafePoints`, `Start/EndUnsafePoint`, entry helpers).

**What it does:** a Prog that names R27 in `From.Reg`, `To.Reg`, `Reg` or a `REGREG` second
register is unsafe; a multi-word Prog without `NOTUSETMP` is restartable (values −3/−4
alternating); ranges already unsafe are kept; inserted PCDATA at the neighbouring PCs.

**Proof:** rt, async preemption (semantics3 §6): `asyncPreempt` saves R0–R17, R19–R26, NZCV,
FPSR and the F registers, and returns through R27 (`runtime/preempt_arm64.s`), so a preemption
is invisible exactly when R27 is dead; obligation: every PC at which R27 is live is unsafe, and
every restartable sequence is idempotent from its first word. A validator over the M words.
**M / L**.

### D7 pc tables and funcdata

**Source:** `internal/obj/pcln.go:25-353`, `internal/obj/inl.go:58-143`,
`internal/obj/line.go:17-28`, `internal/src/xpos.go:127-195`.

**What it does:** `funcpctab` encodes (value, pc) runs: pcsp from `Spadj` (applied after the
instruction), pcfile/pcline from innermost positions, pcinline from the local inline tree,
pcdata from PCDATA Progs; empty holes become empty symbols; funcdata slots from FUNCDATA Progs.

**Proof:** pcsp is semantic for the runtime (unwinding, stack growth, GC frame size): validator
"pcsp at every PC equals the SP offset the machine semantics computes along every path".
Stack-map and unsafe-point pcdata are checked by B1/D6's validators through a round-trip with a
transcription of `runtime/symtab.go`'s `pcvalue`. pcfile/pcline/pcinline are dbg: parity.
**M / L**.

### E1 location lists

**Source:** `compile/internal/ssa/debug.go:29-60,350-399,433-1163,1196-1471` (optimised),
`:1473-1557` (encoding), `:1578-1874` (`BuildFuncDebugNoOptimized`); `ssagen/ssa.go:7347-7386`.

**What it does:** with register ABI, first creates pseudo-values for argument pieces (debug
only: genssa has already emitted the code); reassembles named split slots into variables in
`f.Names` order; a forward availability dataflow over registers and stack slots; walks the
layout to build lists with (block, value) endpoints resolved to PCs by `GetPC` after assembly;
encodes DWARF 4 or 5 (`Experiment.Dwarf5`) expressions (`DW_OP_reg*`, `DW_OP_fbreg`,
`DW_OP_piece`).

**Proof:** none (debug information). Parity, plus a non-interference lemma: E1 changes no code
(it runs after emission; its pseudo-values do not reach C2). **XL / —**.

### E2 DWARF variables, scopes, inlined calls, DIEs and the line program

**Source:** `compile/internal/dwarfgen/dwarf.go:29-696`, `scope.go:18-135`, `marker.go:15-95`,
`dwinl.go:29-441`; `internal/obj/dwarf.go:21-205` (line program), `:208-699`
(`populateDWARF`, fixups); `internal/dwarf/dwarf.go:1083-1460`.

**What it does:** per function: variables (complex SSA locations from E1, else stack offsets),
scopes from position marks, inlined-call trees and their PC ranges, concrete and abstract DIEs,
the line program (`putpclcdelta` with LINE_BASE −4, LINE_RANGE 10, OPCODE_BASE 11; PC deltas in
bytes), `R_USETYPE` relocations. Package: abstract functions and relocation fixups after all
functions (sorted by name).

**Proof:** none; parity per function given the package file numbering, whole package for
abstract functions and fixups. **XL / —**.

### F1 symbol numbering and FuncInfo symbols (package)

**Source:** `internal/obj/sym.go:255-550` (`NumberSyms`), `internal/obj/objfile.go:765-839`
(`genFuncInfoSyms`), `internal/goobj/funcinfo.go:13-145`.

**What it does:** numbers definitions (Text then Data; content-addressable short and long hashed
symbols, non-package symbols, references) and writes each function's `FuncInfo` (args, locals,
`FuncID`, `FuncFlag`, start line, files, inline tree).

**Proof:** none; the stock code runs unchanged on the imported symbols (trusted, §5). Parity is
the object comparison. **L / —**.

### F2 object writer (package)

**Source:** `internal/obj/objfile.go:33-709`, `internal/goobj/objfile.go`,
`internal/hash/hash.go:16-29`; archive `compile/internal/gc/obj.go:30-149`.

**What it does:** writes the goobj blocks (autolib, package index, files, symbol definitions in
four classes, references, hashes, relocations sorted by `Off`, aux records, data, names); content
hashes (zero-padded short, SHA-256-based long) are computed before the relocation sort.

**Proof:** none (trusted, §5). **XL / —** if ever ported; the plan does not port it.

## 5. Trusted base and what is proven (summary)

The plan (`docs/plans/semantics3.md` §6) proves the per-function path from L2 to M for
code-relevant content and validates the runtime metadata; it trusts:

| Trusted | Why |
| --- | --- |
| ARM64 instruction semantics and decoder for the emitted subset | our own transcription, co-simulated against qemu on Go-assembled words; ASL-derived agreement after #415 (semantics3 §3) |
| Linker and loader | relocation application (`R_CALLARM64`, `R_ADDRARM64`, `R_ARM64_PCREL_LDST*`, `R_ADDR`), symbol placement, read-only constant symbols, pclntab assembly, the nil page unmapped |
| Runtime | callee contracts (Phase 1's `Env.runtime`), `morestack`/`newstack`/`copystack` and `shrinkstack` given correct pcsp/maps, GC scanning given correct maps and stack objects, `asyncPreempt`, `panicBounds` decoding, `sigpanic` for nil faults, write-barrier helpers, open-coded defers |
| Stock object writer and symbol numbering (F1, F2) | run unchanged on imported symbols; their output is compared byte for byte |
| DWARF, pcfile, pcline, pcinline, ArgInfo, ArgLiveInfo, WrapInfo | no execution content; exact parity only |

Proven (I7): A1/A2 by validators, C1–C6 by the `runLoc → runProg` simulation, D2/D3 by
`runProg` refinements, D4/D5 by the object validator's soundness, B1/C6/D6/D7 metadata by
validators against the runtime contracts.
