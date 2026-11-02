# Pass survey: machine-independent SSA passes (go1.27.3, linux/arm64)

Scope: `cmd/compile/internal/ssa/compile.go` `passes` (lines 457-520) from `number lines` up to,
not including, `lower`, and the `passOrder` constraints among them (lines 530-614). Paths are
relative to `third_party/go/src/cmd/compile/internal/ssa` (also written `SSA/`) unless
prefixed. Indices are 0-based
into `passes`. Written by the PassSurvey agent from the source only (no builds); every claim
cites `file.go:line`. Use this document as the spec sheet when porting a pass: the
"parity traps" lists are what an exact port (same IDs, same `b.Values`/`f.Blocks` order, same
aux, same positions) must replicate. Semantics plan: `docs/plans/semantics.md`. Export format:
`docs/contracts/export.md`.

## 0. Pipeline

Driver (`compile.go:68-70`): a pass runs unless `(!f.Config.optimize && !p.required) ||
p.disabled`; `-N` sets `optimize = false`. Per-pass flags `-d=ssa/<name>/{off,debug=N,stats,
time,mem,dump=fn}` (`compile.go:261` `PhaseOption`; spaces in names become `_`; required passes
cannot be turned off). The export runs with defaults: all `debug = 0` (debug output never
changes the SSA, except where noted below), and `checkEnabled` off — `-d=ssa/check/on`
shuffles every `b.Values` with a CRC-seeded RNG before each pass (`compile.go:83-91`).

| idx | pass | fn | req | linux/arm64 default | under -N | issue | own LOC | difficulty |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | number lines | `numberLines` | ✓ | runs | runs | #13 | ~150 (+xposmap) | S |
| 1 | early phielim and copyelim | `copyelim` | | runs | skipped (still inside every deadcode) | #14 | ~95 | S / M |
| 2 | early deadcode | `deadcode` | | runs | skipped | #15 | ~240 | M |
| 3 | short circuit | `shortcircuit` | | runs | skipped | #16 | ~310 | L |
| 4 | decompose user | `decomposeUser` | ✓ | runs | runs | #17 | ~385 (both decomposes) | M |
| 5 | pre-opt deadcode | `deadcode` | | runs | skipped | #15 | | |
| 6 | opt | `opt` | ✓ | runs | runs | #7 | driver 192 + 39.9k generated (1,024 rules) | L port, rule lemmas |
| 7 | zero arg cse | `zcse` | ✓ | runs | runs | #18 | 57 | S |
| 8 | opt deadcode | `deadcode` | ✓ | runs | runs | #15 | | |
| 9 | generic cse | `cse` | | runs | skipped | #19 | ~400 | L |
| 10 | phiopt | `phiopt` | | runs | skipped | #20 | 352 | S |
| 11 | gcse deadcode | `deadcode` | ✓ | runs | runs | #15 | | |
| 12 | nilcheckelim | `nilcheckelim` | | runs | skipped | #23 | 173 (+storeOrder) | M |
| 13 | prove | `prove` | | runs | skipped | #24 | ~3.5k (with poset, loopbce) | XL |
| 14 | divisible | `divisible` | ✓ | runs | runs | #25 | 2.5k generated (both) + magic.go 426 | M port / L proof |
| 15 | divmod | `divmod` | ✓ | runs | runs | #25 | | |
| 16 | middle opt | `opt` | ✓ | runs | runs | #7 | | |
| 17 | known bits | `knownBits` | | runs | skipped | #26 | 359 | M |
| 18 | early fuse | `fuseEarly` | | runs | skipped | #27 | 731 (all fuse files) | L |
| 19 | expand calls | `expandCalls` | ✓ | runs | runs | #28 | ~970 (+abi accessors) | L port / XL proof |
| 20 | decompose builtin | `postExpandCallsDecompose` | ✓ | runs | runs | #17 | | |
| 21 | softfloat | `softfloat` | ✓ | **no-op** (`Config.SoftFloat` false) | no-op | #29 | 80 | S |
| 22 | branchelim | `branchelim` | | runs (`haveCondSelect`) | skipped | #30 | 336 | M |
| 23 | late opt | `opt` | ✓ | runs | runs | #7 | | |
| 24 | dead auto elim | `elimDeadAutosGeneric` | | runs | skipped | #31 | ~190 | M |
| 25 | sccp | `sccp` | | runs | skipped | #32 | 412 | M–L |
| 26 | generic deadcode | `deadcode` | ✓ | runs | runs | #15 | | |
| 27 | late fuse | `fuseLate` | | runs | skipped | #27 | | |
| 28 | check bce | `checkbce` | | **no-op** (diagnostics only) | skipped | #33 | 27 | S |
| 29 | dse | `dse` | | runs | skipped | #34 | ~226 | M |
| 30 | memcombine | `memcombine` | | runs | skipped | #35 | ~840 | L |
| 31 | writebarrier | `writebarrier` | ✓ | runs (unless `-wb=false`) | runs | #36 | ~800 (+storeOrder) | L |
| 32 | insert resched checks | `insertLoopReschedChecks` | | **disabled** (`GOEXPERIMENT=preemptibleloops` only) | skipped | #37 | 509 | M |
| 33 | cpufeatures | `cpufeatures` | SIMD | **disabled** (`GOEXPERIMENT=simd`; returns at once unless amd64) | — | — | 262 | — |
| 34 | rewrite tern | `rewriteTern` | | **disabled** (as cpufeatures) | — | — | 294 | — |

Under `-N` the pipeline is: number lines, decompose user, opt, zero arg cse, opt deadcode,
gcse deadcode, divisible, divmod, middle opt, expand calls, decompose builtin, softfloat,
late opt, generic deadcode, writebarrier.

### The verified pipeline (issue #189)

`GoFV.Opt.verifiedPipeline` (`GoFV/Opt/Verified.lean`) runs this table (`GoFV.Opt.stockPasses`,
with the same enabled test) on one function. A pass with a refinement theorem runs in the
variant the theorem is about (`optChecked`, `divisibleChecked`, `divmodChecked`, `proveChecked`,
`sccpChecked`, `memcombineChecked`, the validated `csePass`, …); the others run their stock port
(per-pass status: `docs/DRIVER.md`, "Verified mode"). The function is
checked (`GoFV.SSA.check`) once on the input and once per changed result, never inside a pass.
Each pass run gets a verdict:

| verdict | when | result kept |
| --- | --- | --- |
| `proven` | the pass has a theorem, the input passes `check` and the theorem's fragment test (`copyFrag`/`emptyFragB`, `deadFragB`, `cseFrag`, `nilFrag`, `expandCallsFrag`, `daeFrag`, `dseFrag`), and the output passes `check` | yes |
| `identity` | same function, and same tables or tables the function cannot tell apart (`tabsAgree`) | yes |
| `skipped` | an optional pass with a theorem whose input fails `check` or the fragment test, or whose output fails `check` | no (the input is kept) |
| `unverified` | a stock port that changed the function, or a required pass in one of the `skipped` situations | yes |

The pass theorems conclude `Refines`, `RefinesUnder Env.Mono`, `RefinesFrom (FrameSafe ∧
InitAvoids)`, `RefinesFrom (RwPre tabs f)`, `RefinesFrom WbPre` or `RefinesFrom DecPre`. All of
them imply `RefinesFrom (VPre k)` with `VPre k env args mem := env.Mono ∧ env.FrameSafe ∧
InitAvoids env args mem ∧ env.AllocNonNil ∧ DictArgs k args ∧ WbPre env args mem ∧
env.TempOblivious ∧ env.MemOps`
(`k` the input's dictionary parameters; `GoFV/Proof/Pass/Pipeline.lean`), which composes.
`stockPasses_sound` checks each theorem against its table entry.
`verifiedPipeline_refines`: a result without an `unverified` run refines the input under
`VPre`. `verifiedPipeline_witness` (`GoFV/Proof/Witness/Pipeline.lean`) runs the whole table on
a function that every stock-only pass leaves unchanged. To add a theorem, change the pass's
entry to `.proven run rel guard` and add its case to `stockPasses_sound`. A new kind of
precondition needs a `Rel` constructor and a conjunct of `VPre`.

### `passOrder` constraints within scope (`compile.go:530-614`)

`generic cse` < `prove`, `dse`, `nilcheckelim`; `prove` < `generic deadcode`, `divisible`,
`known bits`; `divisible` < `divmod` < `decompose builtin`; `opt` < `nilcheckelim` <
`generic deadcode`, `late fuse`; `generic deadcode` < `check bce`; `expand calls` <
`decompose builtin` < `late opt`, `softfloat`; `branchelim` < `late opt`; `known bits` <
`late opt`; `late fuse` < `memcombine`; `dse` < `insert resched checks`. Constraints into
the lowered part (`… < lower`, `… < tighten`) only bound the scope. These are what a
reordered or subset pipeline must still respect; the parity port simply follows `passes`.

## 1. Shared infrastructure and cross-pass state

Every pass reads and writes more than blocks and values. A Lean `Func` that reaches parity must
carry all of the following, and the export (`docs/contracts/export.md`) carries each of them.

### 1.1 ID allocation and free lists (`func.go:280-453`)
`newValue`/`newValueNoBlock` pop `f.freeValues` **first** (LIFO, IDs reused), otherwise take
`f.vid.get()`; `NewBlock` likewise with `f.freeBlocks`/`f.bid`. `freeValue` (`:397`) and
`freeBlock` (`:444`) push. So the IDs every pass allocates depend on the exact order in which
earlier passes freed values — `deadcode` frees in `f.Blocks × b.Values` order, then blocks;
`applyRewrite` frees all dead values at the end (block then value order); `writebarrier` frees
each store run before allocating its replacement. Model: `Func` has `nextVid`, `nextBid`,
`freeV : List ValueId`, `freeB : List BlockId`; `newValue` is a `match` on `freeV`.
`Value.Uses` counts are also state (read by rules: `x.Uses == 1`) and must be maintained
exactly by every `SetArg`/`reset`/`ReplaceControl`.

### 1.2 Constant cache (`func.go:663-700`)
`f.ConstInt64` etc. (`constVal`) reuse a cached value with the same `Op` and `Type.Compare ==
CMPeq` from `f.constants[auxint]` (scanned in slice order), else create it at the end of
`f.Entry.Values` with `src.NoXPos` and `InCache = true`. Non-numeric constants use magic keys
(`constNilMagic` …, `:684-689`). The cache persists across all passes; `freeValue` of a cached
value and `reset` of one call `unCache`, which swap-removes it from its line (`:356-395`).
Users in scope: rules (`rewrite.go` helpers), `prove`, `known bits`, `expand calls`,
`memcombine`, `sccp`, `shortcircuit`, `softfloat` (when enabled).

### 1.3 Cached CFG analyses (`func.go:766-809`)
`f.postorder()`, `f.Idom()`, `f.Sdom()`, `f.loopnest()` are computed lazily and kept until
`f.invalidateCFG()`, which only `AddEdgeTo`, `removePred`, `removeSucc`, `NewBlock`,
`fuse.go:65`, `branchelim.go:285,388`, `loopreschedchecks.go:266` call. **`Block.swapSuccessors`
and `swapSuccessorsByIdx` (`block.go:318-341`) do not invalidate**, and `opt`'s block rules
(`If (Not c)` → swap) use it. So a cached postorder can be **stale** in a later pass: `number
lines` leaves a postorder cached, `opt` may swap successors, `generic cse` then builds its
dominator-tree numbering (`newSparseTree`, `sparsetree.go:62`) from the stale postorder
(see generic cse, #19). The Lean `Func` must carry the cache (`Option (List BlockId)` etc.)
and invalidate exactly where Go does; the export writes `cache` lines with the contents.

- **Postorder** (`dom.go:23`): iterative DFS from `f.Entry` over `b.Succs` in order; order-
  sensitive, so port it verbatim.
- **Dominators** (`dom.go:58` → Lengauer–Tarjan `dominatorsLTOrig`): the immediate-dominator
  *function* is unique, so any correct algorithm gives the same `idom`; port a simple one
  (Cooper–Harvey–Kennedy, `dominatorsSimple`, `dom.go:202`, is already in the tree) and prove
  it correct once.
- **Sparse tree** (`sparsetree.go:62-155`): children are prepended while scanning the postorder,
  so each child list is in reverse postorder; `entry`/`exit` numbers come from a recursive walk
  of that order. Order-sensitive through the postorder (and its staleness). Used by `cse`,
  `phiopt`, `nilcheckelim`, `prove`, `loopbce`, `insert resched checks`.
- **Loop nest** (`likelyadjust.go:245`): not used by any pass in scope (only by later passes);
  `findIndVar` (`loopbce.go`) finds loops itself from the sparse tree.

### 1.4 Sparse sets and maps (`sparseset.go`, `sparsemap.go`, `sparsemappos.go`)
`dense` keeps insertion order; `remove` swaps the last element into the hole; `pop` takes the
last. Any pass iterating `contents()` or popping (worklists) depends on that exact order.
Users: `deadcode`, `nilcheckelim`, `branchelim`, `dse`, `sccp`, `memcombine`, `writebarrier`,
`insert resched checks`. Port them as a `List`-based structure with the same operations (the
`sparse` index is an implementation detail).

### 1.5 Sorting
`slices.SortFunc` and `sort.Sort` are Go's pattern-defeating quicksort (`slices/
zsortanyfunc.go`, `sort/zsortinterface.go`, generated from one template): insertion sort for
≤ 12 elements, otherwise pdqsort with a deterministic xorshift seeded by the length. It is
**not stable** but deterministic. Where a comparator can return 0 for distinct elements, the
port must reproduce the algorithm exactly: `generic cse` (`cse.go:115,209,380`),
`nilcheckelim`/`writebarrier` via `storeOrder` (`schedule.go:548,554`, NilCheck runs keyed by
raw position, ties possible). Where keys are unique any correct sort will do: `prove`
(`prove.go:3169`), `memcombine` (`:236,541` on success paths), `decompose` (`:422`). Build one
shared `GoFV.Util.PdqSort` port and use it everywhere for uniformity.

### 1.6 Positions
`XPos = (PosBase index, lico)` with `lico = line<<12 | col<<4 | xlogue<<2 | stmt`
(`cmd/internal/src/pos.go`); passes test `SameFileAndLine` (index + line), `IsStmt`, and move
statement marks (`number lines`, `deadcode`, `fuse`, `branchelim`, `nilcheckelim`, `prove`,
`memcombine`, `expand calls`). `number lines` builds `f.cachedLineStarts` (an `xposmap` over
the noted files and line ranges, `numberlines.go:261`), which later passes use as a scratch
set: lines outside the ranges are silently dropped and an unknown file index panics
(`biasedsparsemap.go:88-91`, `xposmap.go:65-67`). Positions are part of parity; export them
raw.

### 1.7 Names, slots, aux identity
`f.Names` (ordered) and `f.NamedValues` (map; passes iterate it only via `f.Names`) are
rewritten by `copyelim`, `deadcode`, `decompose`; they may point at freed or reused values
after `applyRewrite` (see decompose, #17). `CanonicalLocalSlots`/`CanonicalLocalSplits` decide
whether `decompose` creates new autos (`fe.SplitSlot`). Aux values are compared with Go `==`
(pointer identity for `*ir.Name`, `*obj.LSym`, `*AuxCall`, `*AuxNameOffset`; `expand calls`
makes a fresh `AuxNameOffset` per register argument, `expand_calls.go:651`), and types by
pointer (`zcse`, `v.Type == w.Type`) or by `Type.Compare` (`cse`, constant cache). `f.auxmap`
(CSE's aux ranks) is filled by `generic cse` and persists to `lowered cse`.

### 1.8 Pass name
`f.pass.name` changes behaviour: 8 `Mul` → shift rules fire only when the pass is not `opt`
(`_gen/generic.rules:1106-1121`), and `storeOrder` behaves differently in `nilcheckelim`
(`schedule.go:424`). A ported rewriter takes the pass name as a parameter.

## 2. External state the passes read (what the export must carry)

Consolidated from the per-pass sections; posted on #4. All of it is in `docs/contracts/export.md`
(draft on branch `agent/exporter`) unless marked **gap**.

- **Func state** (§1): `vid`/`bid`, free lists, `f.constants` with `InCache`, cached
  postorder/idom/sdom (possibly stale), `cachedLineStarts`, `Names`/`NamedValues`, canonical
  slots/splits, `f.Entry` (not always `f.Blocks[0]` after `fuse`/`shortcircuit`), `Uses`,
  `b.Likely`, `b.Pos`/`v.Pos` raw, `f.OwnAux`, `f.ABISelf`/`ABI0`/`ABI1`/`ABIDefault`,
  `f.NoSplit`, `f.Type`.
- **Config** (constant on the corpus): `arch`, `PtrSize`, `RegSize`, `BigEndian`,
  `unalignedOK`, `haveCondSelect`, `haveBswap*`, `SoftFloat`, `Race`, `optimize`,
  `mulRecipes`, `intParamRegs`/`floatParamRegs`, `ctxt.Flag_shared`/`Flag_dynlink`,
  `FixedFrameSize`; `buildcfg.GOOS`, `buildcfg.Experiment.{CgoCheck2, PreemptibleLoops, SIMD}`
  (SIMD also changes `CanSSA`, `value.go:633,662`); `base.Flag.WB` (`fe.UseWriteBarrier`),
  `base.Debug.Nil`; `types.LocalPkg.Path` and `base.Ctxt.Pkgpath` (`writebarrier`,
  `expand calls`).
- **Types**: kind, size, alignment, `PtrDataSize`, `HasPointers`, fields/offsets, element,
  length, `IsDirectIface`, `Compare` order, pointer identity; types created mid-pipeline
  (`PtrTo` in the dec rules) must be identifiable.
- **Aux**: `*ir.Name` (identity, `Class`, `FrameOffset`, `Addrtaken`, `Used`, `AutoTemp`,
  `OpenDeferSlot`, `Readonly`, escape); `*obj.LSym` (name, ABI, `SRODATA` + relocations + data
  bytes — rules fold loads from read-only data, itabs and type descriptors via `rewriteFixedLoad`
  and `read8..64`; `dse`/`writebarrier` test "read-only and no relocs"); `*AuxCall` with the
  complete `abiInfo` (per param/result type, name, registers, offset; spill area; ABI config);
  `stringAux` with its data-symbol name; `PanicBoundsC/CC`.
- **Frontend results**: `fe.Syslook` names (`writeBarrier`, `wbZero`, `wbMove`,
  `cgoCheckPtrWrite`, `cgoCheckMemmove`, `goschedguarded`), `ir.Syms.Zerobase`,
  `reflectdata.TypeLinksym(t)` per type (writebarrier), `GCSym`/`TypeLinksym(elem)` names
  (fixed loads), `fe.SplitSlot`'s new autos (`decompose`), `fe.StringData` symbols created by
  rules, `ABIAnalyzeTypes` for calls `writebarrier` creates (the port reimplements it from
  `abi1`).
- **Inlining index per position base** (`deadcode` keeps an `InlMark` iff some live position's
  base has that inlining index).
- **Not needed**: `f.Cache` scratch storage, posets, `f.HTMLWriter`, `ruleMatches`, debug
  output, `f.cachedLoopnest` contents (no in-scope reader).

## 3. Real nondeterminism and other global hazards

- **`sccp` is nondeterministic in the stock compiler**: `replaceConst` ranges over the Go map
  `latticeCells` (`sccp.go:576-597`) and calls `rewireSuccessor` → `removeEdge` per block
  whose control became constant. Two removed edges into the same successor that keeps ≥ 2
  predecessors swap-remove in map order, so that block's `Preds` and its phis' argument order
  differ between runs. Consequences: (1) the export must record what the compiler did
  (it does — the next section is ground truth); (2) the Lean port ranges in insertion order,
  and the parity harness replays the order the stock output shows (`docs/PARITY.md`,
  "Randomized map order"), after which the Lean pipeline continues from the *exported* state;
  (3) upstream candidate #87 (reproducible builds; repro `tests/sccp-order/`).
- No other pass in scope has order-observable map iteration (each case is argued in its
  section: `number lines` ranges, `shortcircuit` `replaceUses`, `dead auto elim`, `insert
  resched checks` `newmemphis`, `poset.aliasnodes`, `expand calls`).
- Unstable sorts with ties (§1.5) and the stale postorder cache (§1.3) are deterministic but
  must be ported exactly.
- `known bits` memoises with "seen before recursing", so in loops which values fold depends on
  the visit order (deterministic; port exactly).
- Rule conditions have side effects (`clobber`, `needRaceCleanup`): keep short-circuit order.

## 4. Per-pass sections

### number lines — issue #13
**Function / files:** `numberLines` in `numberlines.go:111-262`; helpers in the same file: `isPoorStatementOp` (:13), `nextGoodStatementIndex` (:31), `notStmtBoundary` (:63, also used by `newValue`, func.go:298), `Block.FirstPossibleStmtValue` (:73, not used by the pass), `fileAndPairs` sort (stats only). Builds `f.cachedLineStarts = newXposmap(ranges)` (numberlines.go:261; `xposmap.go`, `biasedsparsemap.go`, `sparsemap.go`).
**Position & ordering:** index 0 in `passes` (compile.go:458), `required: true`. No `passOrder` constraints.
**Enabled (linux/arm64, default build):** yes, also under -N (required). Behaviour flags: `-d=ssa/number_lines/debug>0` only adds `fmt.Printf` traces (numberlines.go:173,186,191,212,220); `stats&1` computes/LogStats line ranges (sort.Sort on unique map keys, :224-258). No Config/arch dependence.
**Size:** numberlines.go 262 lines / 216 non-blank non-comment; the pass body is ~150 lines (:111-262) plus ~55 of helpers. Shared helpers: `f.Postorder()` (func.go:773 → dom.go:23), xposmap/biasedSparseMap/sparseMap (116+107+87 lines total, also used by deadcode, applyRewrite, nilcheck).
**What it does:** Touches only `Pos` of values and blocks; never changes ops/args/CFG/IDs.
1. Walk the reachable blocks in reverse postorder (`po := f.Postorder()`, loop :129).
2. For each block, `note()` the line of `b.Pos` (if not NotStmt) and of every value examined into `ranges[fileIndex] = [min,max]` line.
3. Find the first value whose Pos is not `PosNotStmt`; `nextGoodStatementIndex` may skip forward past "poor" ops (Addr, Const*, Phi, *Make, SB/SP, ArgIntReg…, :17-20) to a later non-poor value on the same file+line (ignoring NotStmt values). The chosen value gets `WithDefaultStmt()` (:147). The skipped-over value keeps its original stmt bit.
4. Effectively empty block (no candidate): compute `line` = common `endlines` of all preds (NoXPos if they disagree; unvisited preds read the map default NoXPos). If `b.Pos` is NotStmt, set `b.Pos = line` (overwrites the whole position, :170-173). Otherwise mark `b.Pos` IsStmt if it differs from `line`; record `endlines[b.ID]`.
5. Otherwise mark the first value IsStmt if the block has no preds (entry) or if any pred's `endlines` differs in file+line (:183-198).
6. Scan forward: each later non-NotStmt value (again after `nextGoodStatementIndex` skipping) becomes IsStmt if its file+line differs from the running `firstPos`, else DefaultStmt (:200-216).
7. If `b.Pos` is not NotStmt and differs from the last line, mark it IsStmt (:217-223). `endlines[b.ID] = firstPos`.
8. Build `f.cachedLineStarts` = empty sparse map skeleton covering exactly the noted file indices and `[first,last]` line ranges.
**Data structures:** `endlines map[ID]XPos` (lookups only), `ranges map[int]lineRange` (lookups; iterated only for stats and to build the xposmap, both order-insensitive), `xposmap{maps map[int32]*biasedSparseMap}`.
**Parity traps (order dependence / nondeterminism):**
- Block order is the cached postorder (dom.go:23 DFS over `b.Succs` order from `f.Entry`). The result depends on succ order because preds visited earlier fill `endlines`, while back-edge preds read NoXPos. Unreachable blocks are not visited and keep their stmt bits.
- `b.Values` order is significant (first candidate, lookahead in `nextGoodStatementIndex`).
- Map iteration over `ranges` (newXposmap, xposmap.go:31; stats) has no effect on the result: the map is rebuilt and the stats keys are unique.
- XPos encoding: `lico` 0 is special (`IsStmt()` returns NotStmt, `withStmt` is a no-op; cmd/internal/src/pos.go:415,453). `SameFileAndLine` compares the PosBase index and line only (xpos.go:41, pos.go:413), not column.
- The `cachedLineStarts` line ranges are **persistent Func state**. Later `xposmap.set` silently drops lines outside the recorded range (biasedsparsemap.go:88-91) and panics on an unknown file index (xposmap.go:65-67). The Lean `Func` must carry the exact ranges.
- Side effect: leaves `f.cachedPostorder` populated. Later consumers such as `newSparseTree` (sparsetree.go:63) reuse it until `invalidateCFG`, so the cache contents are observable (see generic cse).
**External state read:** XPos fields: PosBase index (`FileIndex`), line, stmt bits. `f.pass.debug/stats`. No types, no Config.
**Depends on:** postorder only. Runs first, so the input is the ssagen output.
**Proof strategy & difficulty:** S. Semantics are trivially preserved because only `Pos` changes, so no simulation is needed beyond "Pos is not observable". Parity needs an exact port of the walk, the lookahead, and the range table. A Lean port can be validated by an equality check on Pos fields.
**Issue summary:** Enabled always (required, runs with -N). About 150 LOC plus xposmap (~270 LOC shared). Order traps: reverse postorder (depends on succ order), b.Values order, lico==0 corner cases. Map iteration is harmless. Output includes the persistent `f.cachedLineStarts` file/line-range table, which later passes (deadcode, applyRewrite, nilcheck) rely on; out-of-range lines silently drop stmt marks. External: XPos base index/line/stmt bits. Difficulty S; no prerequisites besides postorder.

### early phielim and copyelim — issue #14
**Function / files:** `copyelim` in `copyelim.go:10`. Helpers in the same file: `phielim` (:98), `phielimValue` (:124), `copyelimValue` (:73), `copySource` (:36). Shared: `Value.reset` (value.go:382), `SetArg`/`SetArgs1` (value.go:339,344), `Block.ReplaceControl` (block.go:210). `phielimValue` is also called from `removePhiArg` (block.go:366), `shortcircuitBlock`, and `applyRewrite` (rewrite.go:108). `copyelim` is also called by every `deadcode` (deadcode.go:213).
**Position & ordering:** index 1 (compile.go:459), not required. No `passOrder` constraints. The same function reruns as "late phielim and copyelim" (index 46, after lower). That instance is out of scope, but it is the same code.
**Enabled (linux/arm64, default build):** yes; disabled by -N (but the copyelim inside deadcode still runs wherever deadcode runs, e.g. "opt deadcode" is required). `debug>0`: `f.Warnl(v.Pos,"eliminated phi")` only (copyelim.go:150-152).
**Size:** copyelim.go 157 lines / 93 code. No exclusive helpers outside the file.
**What it does:**
1. `phielim` fixpoint (:99-117): repeat until no phi changes. For every block in `f.Blocks` and every value in `b.Values`:
   - (a) If the type is a struct or array with `Size()==0`, `v.reset(OpEmpty)` (drops args/aux/auxint, uncaches; type and Pos kept). This applies to **every** op (Loads, phis, selects, …) and is repeated on every iteration and in every deadcode.
   - (b) `copyelimValue(v)`: each arg that is a Copy is replaced by `copySource`, the ultimate non-copy source. `copySource` uses tortoise/hare cycle detection; on a copy cycle it does `w.reset(OpUnknown)` on the meeting point (:52-55), then path-compresses the whole chain (`SetArg(0,w)` on each copy, :63-67).
   - (c) `phielimValue(v)`: a phi whose args (ignoring self-references) are all one value `w` becomes `OpCopy` with `SetArgs1(w)`. Type and Pos are unchanged, the op is set directly (no `reset`), and an all-self phi is left alone.
2. Replace Copy controls of every block by `v.Args[0]` (one step; :15-21).
3. For each name in `f.Names` order, replace Copy entries in `f.NamedValues[*name]` by `Args[0]` (one step; :24-31).
4. Copies stay in the blocks; a later deadcode removes them. No values or blocks are allocated or freed.
**Data structures:** none beyond the function itself.
**Parity traps (order dependence / nondeterminism):**
- `f.Blocks` × `b.Values` order decides when phis collapse within an iteration and which copy in a cycle gets `reset(OpUnknown)`. The fixpoint result is order-dependent only in the cycle case; the port must follow the same order.
- One-step replacement for controls/names is exact only because the last fixpoint iteration ran `copyelimValue` on every value, copies included. Replicate the step, not a transitive closure (equivalent, but keep it exact).
- `Uses` counts are mutated (SetArg/ReplaceControl/reset). Later passes read `Uses`, so they are part of the state.
- `f.NamedValues` is accessed only through `f.Names` (deterministic). Stale map keys that are not in `f.Names` (see decompose user) are not updated.
- `reset(OpEmpty)` on an `InCache` value calls `f.unCache` (value.go:383), which swap-removes it from its `f.constants` line. Lookup in that line is by (op, Type.Compare) and entries are unique, so the order is harmless.
- No allocation or freeing, so no ID trap.
**External state read:** `Type.IsStruct/IsArray/Size` (types package); `f.Names`/`f.NamedValues`; `f.pass.debug`.
**Depends on:** nothing cached. Requires well-formed phis (`len(Args)==len(Preds)` is not checked here).
**Proof strategy & difficulty:** S–M direct simulation. Copy is the identity. A phi with a single distinct non-self arg equals that arg on every path; the proof needs SSA dominance or a "phi value equals arg along pred edge" invariant. The zero-size→Empty rewrite needs a semantics in which zero-size values carry no information and **zero-size Loads cannot fault**; the rewrite drops their args, including any nil-pointer operand. Copy cycles → OpUnknown needs an "unreachable / never evaluated" argument. S for parity, M for the proof because of the zero-size and cycle cases.
**Issue summary:** Enabled by default, off under -N, but it is also embedded in every deadcode (required instances), so it is effectively always run. ~95 LOC. It rewrites every zero-size struct/array value to OpEmpty, a hidden semantic rewrite that drops args (zero-size Loads lose their pointer). Order traps: f.Blocks/b.Values fixpoint order and which copy in a cycle becomes OpUnknown. No allocation, no map iteration. External: Type.Size/IsStruct/IsArray, f.Names/NamedValues. Difficulty S (parity) / M (proof).

### early deadcode, pre-opt deadcode, opt deadcode, gcse deadcode, generic deadcode — issue #15
**Function / files:** `deadcode` in `deadcode.go:174-305`; `ReachableBlocks` (:22), `liveValues` (:56), `findlive` (:13, unused by the pass), `Block.removeEdge` (:311). Shared helpers: `copyelim` (whole issue #14, deadcode.go:213), `removeSucc`/`removePred`/`removePhiArg` (block.go:305,287,357; `removePhiArg` calls `phielimValue`), `ResetControls` (block.go:191), `truncateValues` (block.go:269), `f.freeValue`/`f.freeBlock` (func.go:397,444), `f.newSparseSet`, `xposmap` via `f.cachedLineStarts`.
**Position & ordering:** "early deadcode" index 2 (not required, compile.go:460); "pre-opt deadcode" index 5 (not required, :463); "opt deadcode" index 8 (required, :466); "gcse deadcode" index 11 (required, :469); "generic deadcode" index 26 (required, :484). `passOrder`: prove→generic deadcode (:540), nilcheckelim→generic deadcode (:553), generic deadcode→tighten (:559), generic deadcode→check bce (:562). Out of scope: "lowered deadcode for cse" (39), "lowered deadcode" (43, required; lowered deadcode→checkLower), "late deadcode" (48).
**Enabled (linux/arm64, default build):** all five yes. Under -N only opt/gcse/generic run. `f.RegAlloc != nil` is fatal (:179). No arch/Config dependence. `debug` has no effect except the inner phielim `Warnl`.
**Size:** deadcode.go 360 lines / 249 code; the pass plus `ReachableBlocks`/`liveValues`/`removeEdge` is about 240 code lines. Shared: copyelim (93), xposmap+biasedSparseMap+sparseMap (~215 code), sparseSet, block edge helpers (~80).
**What it does:**
1. `ReachableBlocks` (:22-46): DFS stack from `f.Entry`; `BlockFirst` follows only `Succs[0]`. Returns a bool set.
2. Edges from dead to live blocks (:184-196): for each unreachable `b` in `f.Blocks` order and each `i` in `b.Succs` (index not advanced after a removal), `b.removeEdge(i)` if the target is reachable. `removeEdge` swap-removes the succ (`removeSucc`), swap-removes the pred in the target (`removePred`, which fixes the moved edge's back-index), then for each phi in the target, in `c.Values` order: `removePhiArg` (swap-with-last of the phi arg) and then `phielimValue`, which may turn the phi into a Copy.
3. Live `BlockFirst` blocks (:199-208): `removeEdge(1)`, Kind=Plain, `Likely=BranchUnknown`.
4. `copyelim(f)`: the full issue #14, including the zero-size→OpEmpty reset.
5. `liveValues` (:56-160). First it builds `liveInlIdx`, the set of inlining indices used by the Pos of **any** value or block in `f.Blocks`, dead or unreachable included (:71-90). Roots, for reachable blocks in `f.Blocks` order: control values first, then `b.Values` that are call/hasSideEffects/nilCheck, or `OpInlMark` whose `AuxInt` is in `liveInlIdx`. LIFO worklist closure over `Args`, skipping phi args from unreachable preds. It also returns `liveOrderStmts`: newly-live values whose Pos is not NotStmt, in discovery order.
6. Names (:221-245): for each name in `f.Names`, keep live values, deduplicated by ID with a sparse set, in original order. Delete the map entry if none remain, else compact (stable) `f.Names` and the value list (tail cleared).
7. Statement-mark preservation (:238-276). `pendingLines.clear()`. For each block (index `i` in `f.Blocks`): unreachable blocks get `ResetControls`; dead values get `resetArgs`; a dead value with Pos `PosIsStmt` in a reachable block records `pendingLines.set(v.Pos, i)`, where a later block overwrites an earlier one for the same file+line. Then over `liveOrderStmts` **from the end**: if `pendingLines.get(w.Pos)` holds block index j with `f.Blocks[j]==w.Block`, mark w IsStmt and remove the entry. Remaining entries: `foreachEntry` marks `b.Pos` IsStmt when the block's file+line matches.
8. Free dead values per block (`f.Blocks` order, `b.Values` order) with `f.freeValue` (uncaches constants), and compact `b.Values` stably. Then free unreachable blocks in `f.Blocks` order (fatal if one still holds values) and compact `f.Blocks` stably.
**Data structures:** `reachable []bool`; `live []bool`; worklist `q` (LIFO); `liveOrderStmts []*Value`; `liveInlIdx map[int]bool` (membership only); sparseSet for name dedup (membership only); `xposmap` (per-file `biasedSparseMap` over a `sparseMap` with a dense insertion-ordered array and swap-on-remove).
**Parity traps (order dependence / nondeterminism):**
- **ID reuse**: values are pushed on the LIFO free list in (f.Blocks, b.Values) order, then blocks in f.Blocks order. The next pass's first `newValue` gets the **last** dead value's ID. Every later allocation depends on this exact order.
- **Edge order**: `removeSucc`/`removePred`/`removePhiArg` are swap-with-last, so they permute `Preds` and phi args of surviving blocks. The removal order (f.Blocks order of dead blocks, the succ loop with no `i++` after a removal, and BlockFirst handling after that) must be replicated exactly.
- `removePhiArg`→`phielimValue` turns phis into Copies mid-pass; `copyelim` then cleans up.
- `liveOrderStmts` order (roots in f.Blocks order, controls before values, LIFO pop, args in index order) decides which live value receives a lost stmt mark ("first match from the end, then remove").
- `pendingLines.set` keyed by file+line keeps one entry per line, and later blocks win. `xposmap.foreachEntry` iterates a Go **map** (xposmap.go:108), but the callback only sets IsStmt on `f.Blocks[bi].Pos` (idempotent, commutative), so the order is harmless. Lines outside the number-lines ranges are silently ignored; an unknown file index panics.
- `liveInlIdx` map: membership only, harmless. It counts dead values too, so an InlMark stays live one extra round if only dead code referenced its body.
- `f.NamedValues` is accessed via `f.Names` only, so it is deterministic. Keys absent from `f.Names` are never pruned and can keep pointers to freed, later reused, Values (see decompose user).
- `freeValue` of an InCache constant removes it from `f.constants`, so later `f.ConstXX` calls create fresh values (new IDs) rather than reuse.
- Blocks are not renumbered; `f.Entry` is not changed.
- `invalidateCFG` is called only through `removeSucc`/`removePred`. If no edge is removed, a cached postorder/idom/sdom survives even when unreachable blocks are freed. That is harmless because those caches cover reachable blocks only.
**External state read:** `f.Config.ctxt.PosTable`: `pt.Pos(xpos).Base().InliningIndex()` for every value/block Pos (deadcode.go:70-90). The exporter must carry the inlining index per PosBase. Also opcodeTable flags (call, hasSideEffects, nilCheck), `f.Names`/`f.NamedValues`, `f.cachedLineStarts`, `f.RegAlloc`, and Type.Size via copyelim.
**Depends on:** copyelim (#14); number lines (cachedLineStarts must exist). Assumes SSA dominance so that no live value uses a value in an unreachable block (fatal otherwise, :295-297).
**Proof strategy & difficulty:** M. Direct simulation: unreachable blocks are never executed; dead values are pure, since everything effectful is a root and liveness is a closure over args. Phi-arg removal for an unreachable pred is safe. The phi→Copy in `removePhiArg` needs the dominance argument from the comment at deadcode.go:327-359. Positions are unobservable. Alternatively, a validator could check the output against the input restricted to reachable blocks and live values, with a pred permutation map; the edge permutation makes that fiddly, so a direct port is preferred. Ship one Lean function used by all five instances.
**Proof (done, #83):** `deadcode_refines` (`GoFV/Proof/Pass/DeadcodePass.lean`), hypotheses `check` on input and output and `DeadFrag` (conditions on the input only, decided by `deadFragB`). `deadcode = edges ; copyelim ; deadTail` (`deadcode_eq`); three refinements composed by `Refines.trans`: (1) `edgesG false f` (the edge walk with phis only losing arguments) refines `f` by the reachable-block simulation `refines_of_deadRel` (`ei_edgesG`, `wf_of_ei`, `deadRel_of_ei`, `reachable_spec`); (2) copyelim's output on deadcode's real edge removal `edgesG true f` refines it: the real walk is a state of copyelim's sweeps started at `edgesG false f` (`j_edgesG`, `inv_of_j`: a phi that `removePhiArg` turns into a copy is a phi copyelim would turn), so no new dominance argument is needed; (3) the liveness/free tail refines its input (`deadTail_rel`). `DeadFrag`: block IDs ≤ `bid.last`, listed `First` blocks with two successors, copyelim's fragment (`CopyFrag`: copy and phi arguments keep their value at the copy's shape, `RetypeInto`: shapes equal up to `retypeEqB`, which since #289 relates `Ty.str` and `Ty.slice` shapes, or an argument of shape `other`, whose values are all `poison`; phis that are `Stable` (two arguments whose copy chains end at distinct non-phis, so phielim never turns them into copies: `Inv.ends`, `inv_phielim`) are exempt from the shape condition; `EmptyFrag`: tree values of zero-size aggregate type are `EmptyOK`, an `Empty` or an `Arg` at offset 0 of shape `empty`, which evaluate to `.empty` like the `Empty` phielim makes of them) of the edge-removed functions, dominator certificates of `edgesG false f` and of copyelim's output (`check` is not usable on the intermediates: an unreachable block that lost an edge breaks its kind's successor count). Corpus (`deadcode-probe`, quick-v1): 46,059 of 46,485 checked sections in `DeadFrag` (99.1%); outside: 358 zero-size aggregates in tree blocks (`EmptyFrag`), 68 copy shapes (`CopyFrag`).
**Issue summary:** Five instances in scope (#2 early, #5 pre-opt not required; #8 opt, #11 gcse, #26 generic required), so it runs even under -N. ~240 LOC plus copyelim plus xposmap. Top traps: LIFO free-list order (values in f.Blocks×b.Values order, then blocks) sets every later ID; swap-with-last edge/phi-arg removal permutes preds; liveOrderStmts discovery order sets stmt-mark placement. The xposmap map iteration is harmless. External: PosTable inlining index per PosBase, cachedLineStarts ranges, opcodeTable flags, Names/NamedValues. Difficulty M; prerequisites copyelim and number lines.

### short circuit — issue #16
**Function / files:** `shortcircuit` in `shortcircuit.go:11`; `shortcircuitBlock` (:104), `shortcircuitPhiPlan` (:278), `Block.replaceUses` (:500), `Value.moveTo` (:516), `Block.flowsTo` (:556), all in the same file. Step 2 is `fuse(f, fuseTypePlain|fuseTypeShortCircuit)` (fuse.go:33), which also runs **`fuseBlockPlain`** (fuse.go:194-343, shared with early/late fuse). Shared: `removePred`/`removePhiArg`/`phielimValue`, `f.ConstBool` (func.go:699 → constVal), `newValue`, `reset`, `SetArgs*`, `AddArg`.
**Position & ordering:** index 3 (compile.go:461), not required. No `passOrder` constraints.
**Enabled (linux/arm64, default build):** yes; disabled by -N. No flags change behaviour (no debug output).
**Size:** shortcircuit.go 596 lines / 313 code (all exclusive). Plus `fuse` driver (36 lines) and `fuseBlockPlain` (~150 lines), shared with "early fuse"/"late fuse".
**What it does:**
1. Step 1 (:20-50): for every boolean phi `v` (f.Blocks × b.Values order) and arg `i`: if pred `p = b.Preds[i].b` is an `If` whose control **is** that arg, replace the arg with `ConstBool true` (if `e.i==0`) or `false`. The constants `ct`/`cf` are created lazily via `f.ConstBool(f.Config.Types.Bool, …)` on first need. That call reuses the `f.constants` cache, or else allocates a new value in `f.Entry` with NoXPos.
2. Step 2 is the fuse fixpoint: repeat sweeps over `f.Blocks` **in reverse index order**. Per block, run `fuseBlockPlain(b)` and then `shortcircuitBlock(b)`; `invalidateCFG` after each changed sweep.
   - `fuseBlockPlain`: merges a maximal run of Plain blocks with single-pred successors into the last block `c`. It concatenates values in run order, moves end-of-block stmt marks forward (fuse.go:226-252), transfers preds, sets `f.Entry = c` if needed, and marks the absorbed blocks `BlockInvalid` with nil Values/Preds/Succs. Those blocks stay in `f.Blocks` and are **not freed**.
   - `shortcircuitBlock(b)`: `b` must be `If`. The control chain must be `Copy`/`Not` wrappers (Uses==1, in b) over a phi `ctl` in b with Uses==1. b may contain only those wrappers plus phis; other phis are allowed only if b has exactly 2 preds and no phi is an arg of another phi (checked via a map, order-irrelevant). Take the first `ConstBool` arg index `cidx`, `p = Preds[cidx]`, taken successor `ti = 1^AuxInt^swap`; bail if `p==b` or `t==b`. With other phis, `shortcircuitPhiPlan` must find one of five CFG shapes (t/u merge at m via `flowsTo(…,5)`, u flows into t, t falls into u, t exits, u exits) or the rewrite is abandoned. Then commit:
     - `removePred(cidx)` + `removePhiArg(ctl,cidx)`;
     - redirect `p.Succs[pi]` to `t` (appending to `t.Preds`, no invalidate here), and append `Args[te.i]` to every phi in t;
     - run `fixPhi` on each other used phi. It may allocate a new 2-arg phi in t (`newValue`, Pos = phi Pos, forced NotStmt), `replaceUses` in t/u/visited blocks, `moveTo` the phi to m/t/u (swap-remove from b, append to dst), then `SetArgs1/2/3`. Fix up the destination's phis, then `phielimValue` or `reset(OpInvalid)`, and reprocess index i;
     - `reset(OpInvalid)` any remaining unused values in b;
     - if b has 0 preds, `b.Kind = BlockInvalid`, but it keeps its succ edges, controls and values;
     - finally `phielimValue(ctl)`.
**Data structures:** `flowsTo` uses `seen`/`visited` `map[*Block]struct{}` with recursive bounded DFS (cap 5); a `map[*Value]bool` holds the phi set.
**Parity traps (order dependence / nondeterminism):**
- `for bb := range visited { bb.replaceUses(v, argQ) }` (:337,:369) iterates a Go **map**. Each call rewrites args/controls of a distinct block with SetArg/ReplaceControl, so the final graph and Uses are order-independent (harmless). `for v := range m` (:150) and `for b := range seen` (:585) compute booleans only (harmless).
- Allocation: `ct`/`cf` (step 1, lazily, first-needed first; possibly reused from `f.constants`) and the plan phis (`newValue` in t) take IDs from the free list left by early deadcode. Order: f.Blocks/b.Values for step 1; reverse-f.Blocks sweeps, then b.Values index order with `i--` reprocessing, for step 2.
- Nothing is freed. `reset(OpInvalid)` values, `BlockInvalid` blocks (fused-away and dead-If), and stale succ edges of dead `b` stay until the next deadcode. **decompose user (index 4) runs before pre-opt deadcode, so it sees them**, including phis in a dead `b`.
- Pred/succ/arg orders: `removePred` swap-with-last; p's edge reuses slot `pi`; t gets a pred appended. `moveTo` swap-removes from the source block, so `b.Values` order is permuted.
- `fuseBlockPlain` choice of backing storage (`cap` comparisons, fuse.go:259-300) does not affect value order (harmless). It can change `f.Entry`, so `f.Entry` is no longer `f.Blocks[0]` (this matters for zcse).
- `b.Likely` is not adjusted. CFG caches are invalidated only at the end of a changed sweep; no analyses are used inside.
- Stmt marks: `fuseBlockPlain` moves block-end IsStmt marks (fuse.go:231-251), comparing **line only, not file**.
**External state read:** `f.Config.Types.Bool` (type pointer identity for the cached ConstBool), `Type.IsBoolean`, opcode numbers, `f.constants`, `f.scheduled` (moveTo guard).
**Depends on:** early phielim/copyelim and early deadcode (expects no copies wrapping beyond the Copy/Not chain, and all blocks reachable). The free list is from early deadcode. No dominator/postorder analyses.
**Proof strategy & difficulty:** L. A CFG-restructuring pass with five ad-hoc phi plans plus plain-block fusion. Direct simulation needs a per-shape lemma: values of moved/split phis along each path, the branch-taken argument from the const phi arg, and the flowsTo DAG/dominance claim (proved informally at :537-547). A validator is possible but no easier (it would need path-sensitive phi reasoning). Recommend a direct port with fuseBlockPlain proved once and shared with the fuse passes; prove the five fixPhi shapes as separate lemmas.
**Proof (partial, #16):** the plain fusion step is checked and proven (`fuseBlockPlainChecked_refines`, see early fuse / late fuse below); `shortcircuitBlock` and `constPhiArgs` are not yet checked (plan on #16).
**Issue summary:** Enabled by default (off under -N). ~310 LOC plus shared fuse/fuseBlockPlain (~190). Traps: reverse-f.Blocks fuse sweeps; free-list IDs for ct/cf and plan phis; swap-remove in moveTo/removePred. Two map iterations are provably harmless (commutative replaceUses / boolean checks). It leaves BlockInvalid blocks and OpInvalid values for decompose user to see, and can change f.Entry. External: Config.Types.Bool identity, f.constants. Difficulty L; shares fuseBlockPlain with early/late fuse.

### decompose user, decompose builtin — issue #17
**Function / files:** `decomposeUser` (`decompose.go:236`) with `decomposeUserPhi`/`decomposeStructPhi`/`decomposeArrayPhi` (:358,:368,:392), `decomposeUserStructInto`/`decomposeUserArrayInto` (:265,:302), `maybeAppend(2)` (:109,:117), `isStructNotSIMD` (:465). "decompose builtin" runs `postExpandCallsDecompose` (`expand_calls.go:16`) = `decomposeUser(f)` then `decomposeBuiltin(f)` (`decompose.go:16`). `decomposeBuiltin` uses `decomposeBuiltinPhi` and the `decompose{String,Slice,Int64,Complex,Interface}Phi` functions (:121-234), `deleteNamedVals` (:424), and `applyRewrite(f, rewriteBlockdec, rewriteValuedec, leaveDeadValues)` (rewrite.go:41; rules from `_gen/dec.rules` → `rewritedec.go`). `rewritedec64` runs only if `f.Config.RegSize == 4` (decompose.go:31), which is **not** the case on arm64 (config.go:230 RegSize=8). Shared: `f.SplitStruct/SplitArray/SplitString/SplitSlice/SplitInterface/SplitComplex/SplitInt64` (func.go:194-265) → `f.SplitSlot` (func.go:266, `CanonicalLocalSplits` cache) → `fe.SplitSlot` (ssagen/ssa.go:7997); `rewriteStructStore` (rewrite.go:2640).
**Position & ordering:** "decompose user" index 4 (compile.go:462, required); "decompose builtin" index 20 (compile.go:478, required). `passOrder`: divmod→decompose builtin (:546), expand calls→decompose builtin (:564), decompose builtin→late opt (:566), decompose builtin→softfloat (:568). `softfloat` also calls `decomposeBuiltin` when `Config.SoftFloat` is set (softfloat.go:76), which is not the case on arm64.
**Enabled (linux/arm64, default build):** both yes, including under -N (required). On arm64 int64 is not split (Size 8 == RegSize) and dec64 does not run. SIMD types are excluded (`IsSIMD`; SIMD GOEXPERIMENT is off). `debug>1` gives applyRewrite printf traces only.
**Size:** decompose.go 468 lines / 386 code; decomposeUser part ~185, decomposeBuiltin part ~200. rewritedec.go 929 generated lines (114 code lines of dec.rules). Shared: applyRewrite (rewrite.go:41-232, ~150, shared with opt/lower), rewriteStructStore, Split* (~70).
**What it does:**
- decompose user:
  1. For each phi in f.Blocks × b.Values (range snapshot), `decomposeUserPhi`. A struct (non-SIMD) with Size 0 becomes `reset(OpEmpty)`. Otherwise allocate n field phis in `v.Block` (`NewValue0(v.Pos, OpPhi, FieldType(i))`; MaxStruct=4). Then, for each arg `a` in order and each field i, allocate `StructSelect [i] a` **in `a.Block`** (Pos = phi Pos) and AddArg it to field phi i. `v.reset(OpStructMake)` with the field phis as args, then recurse into each field phi. Arrays: size 0 → Empty; else one elem phi, then `ArraySelect [0] a` in a.Block, then `ArrayMake1`, then recurse.
  2. Names: walk `f.Names`. Struct/array names are dropped from `f.Names` and decomposed recursively via `SplitStruct`/`SplitArray`. Each NamedValues entry with op StructMake (matching nargs) / ArrayMake1 contributes its args to the field slots, and other values are kept under the parent key. The parent map entry is deleted if nothing was kept, but **left in the map otherwise even though it is removed from `f.Names`**. Leaf (non-struct/array) field slots are appended through `maybeAppend`, which only appends slots not already map keys, and inserts a nil entry. Nested aggregate field entries are deleted after recursion. Final `f.Names` = kept names (stable) ++ newNames, where each struct emits its leaf fields first and then nested ones.
- decompose builtin = decompose user again, then `decomposeBuiltin`:
  1. Builtin phis (f.Blocks × b.Values snapshot), dispatched by type: string → (BytePtr, Int) phis plus StringPtr/StringLen per arg; slice → ptr/len/cap; interface → (Uintptr itab, BytePtr data); complex → Float32/Float64 pairs; int64 only when Size > RegSize (never on arm64). Each phi becomes `reset(*Make)` with the new phis as args. Allocation order: new phis in v.Block, then the per-arg extractor pairs/triples in `a.Block`.
  2. `applyRewrite` with dec rules and `leaveDeadValues`: fixpoint over f.Blocks/b.Values. On each value it runs `phielimValue`, copy-input elimination via `copySource` (unused copies are `reset(OpInvalid)` regardless of the dead-value choice), and the dec rules. Rules: `Load` of complex/string/slice/interface → `*Make` of component Loads/OffPtrs; extractor-of-`*Make` → copy; extractor-of-Load → `@x.Block` component Load (new values in **x.Block**, v becomes a Copy); `Store` of `*Make` → chain of component Stores; Store of size 0 → mem; `StructMake`/`ArrayMake1`/`StructSelect`/`ArraySelect` of pointer-shaped values → copy; `IMake` of `StructMake`/`ArrayMake1` → unwrapped; `rewriteStructStore`. Block rules are empty (rewritedec.go:927). At the end, OpInvalid values are freed in f.Blocks/b.Values order, with stmt-mark migration through `cachedLineStarts` keyed by **block ID**.
  3. Names: for each `f.Names[i]` of builtin type, `Split*` the slot (maybeAppend new slots) and push component args of matching `*Make` values into the component slots, recording `namedVal{i,j}` to delete. `deleteNamedVals`: `slices.SortFunc` by (locIndex desc, valIndex desc) (keys unique, so the order is algorithm-independent), then swap-with-last deletion inside each value list. Then, from the end of `f.Names`, swap-remove `OpInvalid` values and swap-remove names whose list is empty. Finally `f.Names = append(f.Names, newNames…)`.
**Data structures:** `f.NamedValues map[LocalSlot][]*Value` (lookups/inserts/deletes only, never iterated); `f.CanonicalLocalSplits map[LocalSlotSplitKey]*LocalSlot` (lookup cache); `toDelete []namedVal`; `newNames []*LocalSlot`.
**Parity traps (order dependence / nondeterminism):**
- **Allocation order**: phis, then per-arg extractors (arg order, field order), then recursion. In dec rules the allocation order is that of the generated code (e.g. rewritedec.go:150-155 allocates v0 Load before v1 OffPtr, opposite to rule nesting). Rule matching follows `rewriteValuedec` case order. All IDs come from the free list (decompose user: after shortcircuit/early deadcode; decompose builtin: after expand calls). Extractors and `@x.Block` values go into **other blocks** (a.Block / x.Block), appended at the end.
- Range snapshot semantics: `for _, v := range b.Values` while appending to b.Values does not visit the new values (Go evaluates the slice once). In applyRewrite, values created during a sweep are seen next sweep. The Lean loops must snapshot identically.
- decompose user runs while shortcircuit's `BlockInvalid` blocks and OpInvalid values are still present (pre-opt deadcode comes after), and decomposes phis in dead blocks too.
- Names ordering: `f.Names` compaction (stable), swap-with-last deletions in deleteNamedVals (reorders `f.Names` and value lists), `maybeAppend` dedup against **map key presence**, which includes stale keys left by earlier decomposeUser runs and nil entries. NamedValues is never iterated as a map, so this is deterministic.
- `deleteNamedVals` treats a value with `Op==OpInvalid` as deleted. Freed Values are zeroed (func.go:412), so they also read as OpInvalid. NamedValues can hold pointers to freed and later **reused** Values, because applyRewrite frees without pruning names. An ID-based Lean model reproduces this faithfully only if names store IDs and the free list reuses the same IDs (it does).
- `slices.SortFunc` in deleteNamedVals: keys are unique pairs, so the result is algorithm-independent.
- Positions: new phis are forced NotStmt (newValue, func.go:298); extractors copy the phi Pos. applyRewrite moves stmt marks (rewrite.go:131-144, 159-165, 203-231) using `cachedLineStarts`.
- External mutation: `fe.SplitSlot` creates **new `ir.Name` locals** (`curfn.NewLocal`, ssagen/ssa.go:8006) for PAUTO non-addrtaken parents and calls `types.CalcSize`. Order of creation equals the order of Split* calls (Dcl order matters later for stack layout/DWARF). Results are cached in `f.CanonicalLocalSplits`, keyed by (parent slot pointer, offset, type pointer).
- New types are constructed: `v.Type.Elem().PtrTo()`, `ft.PtrTo()`, `types.NewPtr` in SplitString/SplitInterface/SplitSlice. Type identity is pointer-based (interned via the type's ptr cache), and later zcse keys on type pointers.
**External state read:** types queries (IsStruct/IsArray/IsSIMD/NumFields/FieldType/FieldOff/FieldName/NumElem/Elem/Size/IsString/IsSlice/IsInterface/IsComplex/IsFloat/IsInteger/IsSigned/IsPtrShaped/PtrTo); `f.Config.Types.*` (BytePtr, Int, Uintptr, Float32/64, their Ptr types), `Config.RegSize`, `Config.PtrSize`; `LocalSlot` (N *ir.Name, Type, Off, SplitOf, SplitOffset); `ir.Name.Class`, `Addrtaken`, `Sym().Name`, `Pos` (SplitSlot); `f.Names`/`f.NamedValues`/`CanonicalLocalSplits`; `cachedLineStarts`.
**Depends on:** decompose user: shortcircuit's output (dead blocks still present), early phielim (zero-size phis already OpEmpty). decompose builtin: expand calls (passOrder), divmod; the applyRewrite framework (shared with opt); the dec rules generator order.
**Proof strategy & difficulty:** M, given the applyRewrite and rules infrastructure from opt; L standalone. Phi splitting is a local simulation: phi(Make(a_i…)) = Make(phi(a_i)…), with extractors placed in the defining block of each arg, so dominance holds. Dec rules need per-rule soundness lemmas (memory layout facts: FieldOff, PtrSize offsets), which can reuse the opt rule-proof pipeline. Names/LocalSlot bookkeeping has no semantics (debug info), so parity only. The extern `fe.SplitSlot` must be modelled as an oracle returning a fresh slot ID and recorded for parity.
**Proof (tables part done, #17):** the split slots are new non-addrtaken `PAUTO` names in the output tables, so running the input in them allocates extra `Blk.temp` frame blocks and `tabsAgree` fails (quick: decompose user 637, decompose builtin 1482 of 9297 sections). `GoFV.Opt.tabsAgreeMod tabs tabs' f` (`GoFV/Opt/TabsAgreeMod.lean`) allows them: `tabsAgree`'s conjuncts, except that the frame variables of `tabs'` that `tabs` defines are `tabs`' and every other one is not forgeable; plus an op fragment `tamOpOK` (memory/tuple arguments only last and pointer-shaped results only for `tamMemOps`/`tamPtrOps` or the roots `evalOp` sends to `atomicRoot` (`atomicRootOp`: the P5 atomics, simulated by `atomicRoot_sim`), roots `evalOp` leaves stuck). `GoFV.Proof.refinesFrom_of_tabsAgreeMod (hP : ∀ env args mem, P env args mem → env.TempOblivious ∧ InitAvoids env args mem) (h : tabsAgreeMod tabs tabs' f = true) (hf : check ce f = .ok ()) : RefinesFrom P tabs'' g tabs' f → RefinesFrom P tabs'' g tabs f`, from `run_tabsAgreeMod` (same outcome in `tabs'`: lock-step simulation with memories equal without the extra blocks, `GoFV/Proof/TabsAgreeMod*.lean`); `Sem.Env.TempOblivious` (`Sem/FrameSafe.lean`): contracts cannot tell whether `temp` blocks they get no pointer to exist. Witness `GoFV.Proof.Witness.clamp_run_pauto` (`Env.p1`). Coverage (`tabs-agree-probe`): expand calls, decompose user, decompose builtin all 9297/9297 (quick-v3) and 96533/96533 (full-v4); the extra names always come last in `frameLocals`.
**Proof (phi stage, #17):** `GoFV.Proof.DecPhi.decPhis_refines` (`GoFV/Proof/Pass/DecPhiSim.lean`): `decPhiCheck tabs f g = true → check ce f = .ok () → check ce' g = .ok () → RefinesUnder Env.Mono tabs g tabs f`, same tables on both sides. `GoFV.Opt.DecPhiCheck.decPhiCheck` (`GoFV/Opt/DecPhiCheck.lean`) gives every value of `g` a meaning "component π of source value s" (`meanOf`) and checks: same CFG, own aux, block kinds/controls and non-pure schedule sequence; source values unchanged, or a source `Phi` turned into a `Make` of its components or (zero-sized) `Empty`; new values listed in the block of their meaning's base and an extractor of the prefix's meaning, a `Make`/`Empty`, or a `Phi` whose argument j means component π of the source `Phi`'s argument j. The simulation (`DecPhiBlock.lean`) relates every value of `g` to the component of its base's source register (`MRel`, `ext`). `Decompose.phiStage env builtin f` runs the phi stage alone (user: `forEachPhi decomposeUserPhi`; builtin: `decomposeUser; forEachPhi decomposeBuiltinPhi`) and returns its tables and function. `lake exe decompose-probe`: quick-v3 9297/9297 sections accepted for both passes' phi stages (173 resp. 532 split ≥ 1 phi; `tabsAgree` of the input and the stage's tables, which have no split slots yet, holds everywhere; `decPhiCheck out.tables f out.func` on decompose user's full output 9297/9297); the dec rules change values after the phi stage in 5227 builtin sections. Witnesses `decPhis_formatBool_witness`/`decPhis_pair_witness` (`GoFV/Proof/Witness/DecPhis.lean`; stage output checked in `GoFVTest/Proof/DecPhisStage.lean`).
**Proof (both passes, #17):** `GoFV.Proof.Decompose.decomposeUser_refines` / `decomposeBuiltin_refines` (`GoFV/Proof/Pass/Decompose.lean`): `pass penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → decUserFrag penv f = true` (resp. `decBuiltinFrag`) `→ RefinesFrom DecPre out.tables out.func penv.tables f`, with `DecPre env args mem := env.Mono ∧ env.TempOblivious ∧ InitAvoids env args mem` (non-vacuity: `Witness.decPre_p1`). The fragments (`GoFV/Opt/DecomposeCheck.lean`, input only, a pass error is in the fragment) re-run the pass and check its stages, all in the output tables `T`: `tabsAgreeMod penv.tables T f` (then `refinesFrom_of_tabsAgreeMod`); decompose user: `decPhiCheck T f out.func` (`decPhis_refines`; the names stage and `renumberSlots` change no value); decompose builtin: `decPhiCheck T f g1` on the phi stage `g1 = phiStage …`, the dec rewrite re-run with the proven dec rules only (`Proven.dec`) on `g1`, both checked, validated in layers (`decRewriteOK`: `RewriteCheck.layersOK T` over `RewriteCheck.decLayers`: value-rule `Load` expansions, the extractors of a `Load` (`ldTarget`: `(StringPtr x:(Load …)) => @x.Block (Load …)`, logged before the `Load`'s own expansion), selections of a `Make` and copy-argument replacements involving a `Load`, taken in log order as the replay validates them, `Store` splits by `ssRel` — the dec `Store`-of-`Make` rules split in place, `:123` as `rewriteStructStore` — then `validate`; `Pass.Rewrite.layersOK_refines` with `dec_allSound`, under `Env.Mono`; a log with phi eliminations is checked in segments between them as `RewriteCheck.segsOK` does, `decSegsOK`, `refines_of_decSegsOK`), and with the pass output's code (`sameCode`: equal up to positions, use counts, caches and `f.Names`/`NamedValues`/splits/canon, which the semantics never reads, `run_stripNames`). Witnesses `GoFV.Proof.Witness.decomposeUser_witness` (struct phi of `pair`), `decomposeBuiltin_witness` (string phi of `strconv.FormatBool`), `decStore_witness` (in-place string `Store` splits and a `Load` expansion) and `decPhiElim_witness` (a phi elimination) by kernel evaluation of the stage checks; `GoFVTest/Proof/DecomposeFrag.lean` runs the passes and checks both inputs are in the fragments. Coverage (`decompose-probe`, "in the proof's fragment"): decompose user quick-v3 9297/9297, full-v4 96533/96533; decompose builtin quick-v3 8792/9297 (was 8381 before the `Store` splits, 8645 before the phi eliminations, 8731 before the extractors of a `Load`, 8756 before the `ld` layer in log order, 8763 before the complex `Load` splits `:16`/`:28` and extractors `:158`–`:164`; remaining: `ITab` of an `IMake` whose itab word is an integer, `dec.rules:82`, 376 — the rewrite turns `v`'s value `ptr (Ptr.ofAddr a)` into `int a`, which no validator change can accept, a semantics follow-up; an unproven dec rule fires: `:120` 119), full-v4 83048/96533 (was 77351, then 81847, 82590, 82925, 83032; `ITab` ~11500 (with `:144`, `ITab` of a `Load`, 74), unproven rule ~1011 (`:120`), `Store` split of an `IMake` with a non-`Addr` pointer itab ~610, other ~50).
**Issue summary:** Both required (run under -N); decompose builtin = decomposeUser + decomposeBuiltin (dec rules via applyRewrite, leaveDeadValues). dec64 does not run on arm64 (RegSize 8). ~385 LOC plus 929 generated dec rules plus shared applyRewrite. Traps: free-list ID order of new phis/extractors (placed in the arg's block); generated-code allocation order; range-snapshot loops; swap-with-last name deletion; maybeAppend keyed on stale map keys; NamedValues pointing at freed/reused values. External: fe.SplitSlot creates ir.Name locals, plus types queries and PtrTo construction. Difficulty M (with opt infra).

### opt / middle opt / late opt — issue #7

**Function / files:** `opt` in `opt.go:8` = `applyRewrite(f, rewriteBlockgeneric, rewriteValuegeneric, removeDeadValues)`. Driver `applyRewrite` in `rewrite.go:41-232`. Generated matcher `rewritegeneric.go` (from `_gen/generic.rules`; dispatcher `rewriteValuegeneric` at `rewritegeneric.go:11`, 241 per-op functions `rewriteValuegeneric_OpX`, `rewriteBlockgeneric` at `rewritegeneric.go:39834`). Driver helpers: `phielimValue` (`copyelim.go:123`), `copySource` (`copyelim.go:36`), `Value.reset/copyOf/removeable` (`value.go:382/429/583`), `nextGoodStatementIndex`/`isPoorStatementOp`/`notStmtBoundary` (`numberlines.go:31/13/63`), `xposmap` (`xposmap.go`, on `biasedsparsemap.go`), `Func.rewriteHash` (`print.go:35`), `Func.freeValue` (`func.go:397`), `Block.truncateValues` (`block.go:269`). Rule-condition/result helpers in `rewrite.go` (see External state).
**Position & ordering:** `opt` idx 6 (`compile.go:464`), `middle opt` idx 16 (`compile.go:474`), `late opt` idx 23 (`compile.go:481`); all three `required: true` (run under -N). passOrder: `{"opt","nilcheckelim"}` (`compile.go:557`); `{"decompose builtin","late opt"}` (:566), `{"branchelim","late opt"}` (:602), `{"known bits","late opt"}` (:610). Immediately followed by `zero arg cse` (required, "to merge OpSB values" — opt rules allocate fresh `OpSB` values, e.g. `rewritegeneric.go:7892`) and `opt deadcode` (required).
**Enabled (linux/arm64, default build):** yes, all three, also with -N. Behaviour differences: (a) the rule set depends on the pass name: 8 rules `Mul{8,16,32,64} x (Const 2^k / -2^k) → shift` have cond `v.Block.Func.pass.name != "opt"` (`_gen/generic.rules:1106-1121`), i.e. they fire only in `middle opt`/`late opt`; (b) arch-dependent conditions read `config.arch=="arm64"`, `PtrSize==8`, `RegSize==8`, `ctxt.Arch.Alignment==1` (canLoadUnaligned true, `rewrite.go:487`), little-endian `ByteOrder`; (c) `Config.Race` (`base.Flag.Race`, set at `ssagen/ssa.go:103`) gates `needRaceCleanup`; (d) `buildcfg.Experiment.SIMD` read by `CanSSA` (`value.go:633,662`; off); (e) `f.pass.debug>0` only adds `Warnl` (`copyelim.go:153`, `rewrite.go:856`); `fe.Debug_checknil()` (=`base.Debug.Nil`, `ssagen/ssa.go:8037`) is passed to `warnRule` (`rewrite.go:1107-1112`), which Warnl's when `cond && line>1` and **always returns true** — the nil-check rules fire regardless of the flag; `debug>1` adds stdout prints and turns on cycle-hash checking every iteration (`rewrite.go:178`) — no IR effect.
**Size:** driver `applyRewrite` 192 lines (150 non-comment); `rewritegeneric.go` 39,873 lines (35,700 non-comment, generated) from `_gen/generic.rules` 2,407 lines / 1,024 `=>` rules (many with `(8|16|32|64)` alternation expansion). Shared helpers: `rewrite.go` 2,901 (2,108 non-comment; shared with all arch rewriters, generic uses ~60 helpers listed below), `copyelim.go` 157, `numberlines.go` (3 funcs, ~60 lines), `xposmap.go` 116 + `biasedsparsemap.go` 107, `print.go` rewriteHash.
**What it does:** fixpoint loop (`rewrite.go:59-202`):
1. Per iteration, for each `b` in `f.Blocks` order: (i) for each control `c`, follow `OpCopy` chains replacing the control (`b.ReplaceControl`, no path compression, no dead-copy reset) (`:73-78`); (ii) `rb(b)` — `rewriteBlockgeneric`: `If (Not c) → If c` + `swapSuccessors` (negates `b.Likely`, `block.go:328`), `If (ConstBool true) → First`, `If (ConstBool false) → First` + swap (`rewritegeneric.go:39834-39872`); edges are never removed, so no CFG invalidation. (iii) `for j, v := range b.Values` (slice header snapshotted at block start): if `v.Uses==0 && v.removeable()` (`value.go:583`: not void, not nilCheck op, not memory, no side effects) then if `v.Op != OpInvalid` `v.reset(OpInvalid)` (decrements args' Uses, sets `deadChange`) and skip; else `phielimValue(v)` (phi with ≤1 distinct non-self arg → `OpCopy`); then copy-elim of every arg that is `OpCopy`: `copySource` (Floyd cycle detection; a copy cycle resets the meeting value to `OpUnknown`, `copyelim.go:52`; path-compresses every copy in the chain to point at the source), `v.SetArg(i, src)`, statement-mark transfer (below), then while the dropped copy has `Uses==0` reset it to `OpInvalid` and continue with its arg (`rewrite.go:146-150`); finally `rv(v)`; if it fired and `v.Pos` is a stmt and `nextGoodStatementIndex(v,j,b)!=j`, move the stmt mark to `b.Values[k]` (`:160-165`).
2. Stop when neither `change` nor `deadChange`. Cycle detection: after `iters > max(20, f.NumBlocks())` (`:53-56`) and `change`, hash the func (`rewriteHash`); repeat hash → set debug=2 and restart detection; second repeat → `Fatalf("rewrite cycle detected")`.
3. Final sweep (`:204-231`): for each block in `f.Blocks`, each value in `b.Values` order: `OpInvalid` values are removed from `b.Values` and `f.freeValue`d (stmt mark recorded into pendingLines first); surviving values (not NotStmt, not `notStmtBoundary` op) whose (file,line) maps to this block in pendingLines get `WithIsStmt` and the entry is removed; then `b.Pos` likewise; `truncateValues`.
- Rule matcher semantics (generated): per op, rules tried in `.rules` file order; for commutative ops, nested loops `for _i0 := 0; _i0 <= 1; _i0, v_0, v_1 = _i0+1, v_1, v_0` (e.g. `rewritegeneric.go:1785,1811,1820`) — first successful (rule, permutation) wins and determines bindings. Result construction: `v.reset(op)` (or `v.copyOf(x)` for variable results), then new values allocated in result-tree **preorder** (node, then children left-to-right) with `b.NewValue0(v.Pos, …)` in `v.Block` (or `@x.Block` for 7 rules: `_gen/generic.rules:827,842,851,862,875,978,2267`), args attached after children (e.g. `rewritedivmod.go:904-916`). Constants in results are fresh `NewValue0` values, **not** `f.constants`. Function-valued results (`rewriteStructLoad`, `rewriteStructStore`, `imakeOfStructMake`, `rewriteFixedLoad`, `devirtLECall`) allocate in their own order (`rewrite.go:2622-2658, 2811, 2150, 847`).
**Data structures:** `pendingLines` = `f.cachedLineStarts` (`xposmap`: map file-index → biasedSparseMap line→int32 block ID; created in numberLines `numberlines.go:261`, `clear()`ed at entry); `states map[string]bool` (cycle hashes, lookup only); per-rule locals; `memPreds map[*Value]bool` in `canMergeLoad` (arch only).
**Parity traps (order dependence / nondeterminism):**
- Visit order: `f.Blocks` order, then `b.Values` order with length snapshot at block entry: values appended to the *current* block during its sweep are first visited next iteration; values appended (by `@block` rules) to a *later* block are visited in the same iteration. Number of iterations and which rule fires first both depend on this.
- `Uses`-sensitive conditions (51 occurrences of `.Uses ==/>` in generic.rules, e.g. `s.Uses == 1` at `_gen/generic.rules:1177`, `div.Uses == 1` in divisible) — Uses must be exact at every step, including transient effects of dead-value resets (only reached values are reset; a value dead from later in the sweep is reset next iteration) and of the control-copy elision which does not reset dead copies.
- Commutative permutation order and rule order (above) decide bindings; a port must enumerate identically.
- Allocation: during the fixpoint no value is freed (only reset to `OpInvalid`), so new IDs come from `f.freeValues` as left by the previous pass (LIFO), then fresh `f.vid`. Final sweep frees all `OpInvalid` values in `f.Blocks`×`b.Values` order (incl. ones left `OpInvalid` by earlier passes, e.g. fuseBlockIf) → the free list handed to the next pass has the *last* freed value on top.
- `v.reset/copyOf` of an `InCache` const calls `f.unCache` (swap-remove in the per-AuxInt slice, `func.go:356-366`) — changes `f.constants` slice order; harmless because `constVal` keys on (op, Compare-equal type) and never holds duplicates.
- Positions: in-place rewrites keep `v.Pos`; every new value gets `v.Pos` verbatim including the IsStmt bit (stripped only for `notStmtBoundary` ops, `func.go:298`), so stmt marks are duplicated onto new values incl. constants. Copy-elim transfer rule (`rewrite.go:131-144`): if the dropped copy `a` is IsStmt: prefer `aa` (same block, same line, not NotStmt), else `v` (same conditions), else record `pendingLines[(file,line)] = a.Block.ID`; then `a.Pos = NotStmt`. xposmap ignores column and stores only one block per (file,line) (later `set` overwrites). Final sweep is order-dependent: an `OpInvalid` IsStmt value records its line for its block, which is then claimed only by a *later* surviving value of that block (in `b.Values` order) with the same (file,line), or by `b.Pos`; entries from the fixpoint (copy-elim) can be claimed by any surviving value of the recorded block.
- `nextGoodStatementIndex` reads `b.Values` *current* (post-append) order.
- No map iteration affects output (`xposmap.clear` iterates a map but only clears). `rewriteHash` only for failure detection.
- Aux identity: `(EqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x == y])` (`_gen/generic.rules:1646-1648`) and `isSamePtr` (`rewrite.go:884-885`) compare Aux interface/pointer identity; `isSameCall` compares `Fn.String()` (`rewrite.go:461`).
- Side effects inside conditions: `clobber(...)` (`rewrite.go:1053`) resets values (incl. a call) to `OpInvalid` while evaluating a condition; `needRaceCleanup` (`rewrite.go:2038`) scans every value of `f` and may rewrite `v.Args[0]` (a Store) into a Copy (`:2081`); conditions are `&&`-short-circuited, so evaluation order must be preserved. `devirtLECall` mutates the shared `*AuxCall` (`auxcall.Fn = sym`, `rewrite.go:850`).
- Float constant folding (Add64F, Sqrt, Floor, Cvt*, `float32ToAuxInt`, `reciprocalExact*`) must be bit-exact IEEE incl. NaN handling.
- Type construction: results use `t.Elem().PtrTo()`, `FieldType`, `typ.*` (`Config.Types`) — output may contain types absent from input.
**External state read:**
- Config: `PtrSize` (90 uses), `RegSize` (10), `arch` (`isInlinableMemclr` `rewrite.go:1491`, `isInlinableMemmove` :1510 [arm64: sz<=64 or <=1024 && disjoint], `hasSmallRotate` :1554 [false], `canRotate` :2500 [true if bits<=64], `rewriteCondSelectIntoMath` :2833), `ctxt.Arch.ByteOrder` (read16/32/64), `ctxt.Arch.Alignment` (`canLoadUnaligned`), `Race` (`needRaceCleanup`), `Types` (typ.Int/UInt/Bool/BytePtr/Uintptr/String/…), `MaxStruct`/`types.PtrSize` in `CanSSA`.
- frontend `f.fe`: `StringData(str)` (creates/looks up the `go:string` LSym via `staticdata.StringSym`, `ssagen/ssa.go:7984`), `Debug_checknil()`, `Func().Linksym()` (rewriteFixedLoad), `Warnl`.
- `f.pass.name` (Mul→shift rules), `f.pass.debug`, `f.NumBlocks()` (iteration limit).
- obj.LSym of `Addr`/call auxes: `String()`/`Name` (isSameCall names: runtime.memequal, makeslice, memmove, memclrNoHeapPointers, growslice, growsliceNoAlias, cmpstring, efaceeq, ifaceeq, mapaccess1/2_faststr, mapdelete_faststr, slicebytetostring, racefuncenter/exit + panic* names in needRaceCleanup, newobject, mallocgcSmall*SC* prefixes, `unique.Make[go.shape.string]`); `Type==objabi.SRODATA`, `len(R)`, relocs `R[i].{Type (R_ADDR/R_WEAKADDR),Off,Add,Sym.Name}`, `P` bytes (`symIsRO` :2088, `symIsROZero` :2094, `read8/16/32/64` :2239-2287, `isFixedLoad` :2109), `TypeInfo()` (→ types.Type: Size, `types.PtrDataSize`, `types.TypeHash`, `reflectdata.ABIKindOfType`, `reflectdata.GCSym`, `reflectdata.TypeLinksym(t.Elem())`, `IsPtr`), `ItabInfo()` (isDirectAndComparableIface :2708), `types.IsDirectIface/IsComparable`.
- `rttype.Type.Fields()` (offset, name, type) and `rttype.PtrType.OffsetOf("Elem")` (`rewrite.go:2127,2139`).
- Side effects outside SSA: `reflectdata.MarkTypeSymUsedInInterface` (:2164,2168,2224), `reflectdata.GCSym` may create symbols.
- ir: `ir.Syms.Zerobase` (makeslice rule `_gen/generic.rules:1643`), `isDictArgSym` reads `sym.(*ir.Name).Sym().Name == typecheck.LocalDictName` (`rewrite.go:2805`).
- types package queries: Size, Alignment (184 uses), IsInteger/IsFloat/IsPtrShaped/IsBoolean/IsStruct/IsArray/IsSIMD/IsSigned/IsUintptr/IsMemory/IsVoid/IsTuple, NumElem, NumFields, FieldType, FieldOff, Elem, PtrTo, Compare, `types.CalcSize`.
- `buildcfg.Experiment.SIMD` (CanSSA). Positions/line table via `f.cachedLineStarts` (range set built by numberLines).
**Depends on:** `f.cachedLineStarts` from numberLines (xposmap panics on out-of-range lines); `f.loopnest()` only via `canMergeLoadClobber` (arch rules, not generic). Invariants: generic ops only; `zero arg cse` must follow (fresh OpSB); `opt deadcode` removes unreachable blocks after `First` conversion. Divisible relies on opt's `Mod → Sub x (Mul (Div x c) c)` and `Eq (Sub x y) 0 → Eq x y` (`_gen/generic.rules:1155-1178`). Late opt expects post-decompose IR (SelectN/MakeResult, CondSelect from branchelim).
**Proof strategy & difficulty:** XL. Port the driver exactly (small) and the rule matcher as *data* (generated rule table interpreted in Lean, sharing the RulesExport effort) so that rule order, permutation order and preorder allocation are structural. Correctness: driver simulation proof parameterised by a per-rule soundness obligation; discharge arithmetic/boolean rules by `bv_decide`/`omega` on BitVec per width; memory rules (Load/Store/Move/Zero forwarding, struct/array decomposition) need the memory model; call-recognition rules (memequal, makeslice, memmove, racefunc, growslice, cmpstring, efaceeq/ifaceeq, mapaccess faststr, unique.Make) need runtime-spec axioms; float folding needs IEEE spec. Alternative for the long tail: untrusted port + per-step validator checking each fired rewrite against the rule's LHS/RHS instance (still needs the rule's semantic soundness). XL because ~1,000 rules (several thousand after expansion), exact Uses/alloc/position parity and heavy external symbol state.

**Proof (done for the proven rules, #113):** translation validation. `optChecked` (and `divisibleChecked`/`divmodChecked`) = `checkedRewrite` with the proven rule set (`GoFV.Rules.Proven`): the rewrite log is replayed by `RewriteCheck.validate` or the input is returned. `GoFV.Proof.Pass.Rewrite.opt_refines` / `divisible_refines` / `divmod_refines` (`RefinesFrom (RwPre penv.tables f)`: monotone contracts, malloc-family contracts that return non-nil pointers, non-nil dictionary arguments, the runtime's `memclrNoHeapPointers`/`memmove` contracts if present, #151; from `checkedRewrite_refines (hs : s.AllSound)`: validator soundness `validate_termRef` + atom simulation `AtomSim.atomSim_refines`), witness `addZero_refines` (hand-written `0 + n`, kernel-evaluated). Coverage and rejection numbers: docs/proofs/rules.md, "Proven-only rewrite passes".
**Issue summary:** Required (runs even at -N) x3 (idx 6/16/23); driver 192 LOC + 39.9k generated (1,024 rules); rule set differs by pass name (Mul→shift only in middle/late opt).
Parity traps: f.Blocks×b.Values order with snapshot length, commutative permutation order, preorder value allocation from the inherited free list, end-of-pass free order, Uses-count conditions, IsStmt propagation/pendingLines, side-effecting conditions (clobber, needRaceCleanup), aux pointer identity.
External: Config (PtrSize/RegSize/arch/ByteOrder/Alignment/Race/Types), fe.StringData/Debug_checknil, LSym name/type/relocs/bytes/TypeInfo/ItabInfo, rttype layout, reflectdata (GCSym/TypeLinksym), ir.Syms.Zerobase, .dict names.
Difficulty XL; prerequisites: rule-table export, types/aux tables, numberLines line-range map, memory model.

### zero arg cse — issue #18
**Function / files:** `zcse` in `zcse.go:14`; `vkey` (:56), `keyFor` (:65). Uses `SetArg` and `opcodeTable[op].argLen`.
**Position & ordering:** index 7 (compile.go:465), `required: true` ("required to merge OpSB values"). No `passOrder` constraints. Runs between opt and opt deadcode.
**Enabled (linux/arm64, default build):** yes, also under -N. No flags or debug output.
**Size:** zcse.go 79 lines / 57 code. No shared helpers.
**What it does:**
1. Phase 1: for each block in `f.Blocks` order and index i over `b.Values` (the length is re-read every iteration), take each value whose op has `argLen == 0`. Generic ops with argLen 0: Const{Bool,String,Nil,8,16,32,64,32F,64F,Interface,Slice}, InitMem, Arg, ArgIntReg, ArgFloatReg, SP, SB, Invalid, GetClosurePtr, GetCallerPC, FwdRef, Unknown, HasCPUFeature, Clobber, ClobberReg, Empty, ZeroSIMD (from `_gen/genericOps.go`). Build `vkey{Op, keyFor(v), Aux, Type}`, where `keyFor` sign-normalises AuxInt per const width. The first value seen for a key becomes the representative. If it is not in `f.Entry`, move it: append to `f.Entry.Values`, swap-remove from b (the last value moves to slot i), and `i--`.
2. Phase 2: for every value's args (f.Blocks × b.Values × arg index) that are zero-arg, `SetArg(i, vals[key])` (possibly the same value).
3. Block controls and `f.NamedValues` are **not** updated. Nothing is freed; duplicates die in opt deadcode.
**Data structures:** `vals map[vkey]*Value` (lookups only).
**Parity traps (order dependence / nondeterminism):**
- Representative = first in (f.Blocks, b.Values) order, where `b.Values` has already been permuted by earlier swap-removes in this pass. The entry block is not necessarily `f.Blocks[0]`, since `fuseBlockPlain` can change `f.Entry` (fuse.go:329-331). Moved values are appended to the end of `f.Entry.Values` in discovery order.
- The key uses **Go `==` on `Aux` (interface: dynamic type plus value or pointer identity)** and on `*types.Type` (**pointer identity**, not `Type.Compare`). The exporter must preserve type and aux identity exactly; structurally equal but distinct type pointers are not merged.
- Map used for lookup only, so no iteration nondeterminism.
- A moved value keeps its Pos (an IsStmt mark may now sit in the entry block). No stmt fix-up.
- A zero-arg control value of a non-entry block is not redirected, so the duplicate stays live.
**External state read:** opcodeTable argLen; Aux equality semantics; type pointer identity.
**Depends on:** opt (constants created by rules); followed by opt deadcode (required) for cleanup.
**Proof strategy & difficulty:** S. Direct simulation: zero-arg ops are pure functions of (op, auxint, aux, type) that do not depend on block, and the entry block dominates all blocks, so moving the representative to entry and redirecting uses is value-preserving. Needs: every argLen-0 op is pure and position-independent (InitMem/GetClosurePtr/Arg are entry-only anyway; HasCPUFeature reads a global flag; Clobber* do not occur in the default build). Parity: exact (f.Blocks, b.Values) iteration with swap-remove.
**Proof (done, #84):** translation validation. `zcsePass` runs `zcseChecked`: the Bool checker `ZCSE.zrel` (same CFG and controls; values equal except argument-free values moved to the entry, each argument kept or replaced by a pure entry argument-free value with the same op/aux/auxint/type; moved values always evaluate; an argument-free root of the output's entry, i.e. `InitMem`, is in the input's entry) accepts zcse's output or the input is returned. `GoFV.Proof.ZCSE.zcse_refines` (`GoFV/Proof/Pass/ZCSE*.lean`; no fragment beyond `check`: the roots keep their order, `ZCSERank.lean`, #96), witness `zcse_witness` on `decodedLen`. `lake exe zcse-probe`: the checker never rejects on the corpus.
**Issue summary:** Enabled always (required). 57 LOC. Traps: first-occurrence order with in-pass swap-remove; f.Entry may not be f.Blocks[0]; key uses pointer identity on *types.Type and Go == on Aux; controls/NamedValues not updated. No allocation or freeing, and the map is lookup-only. Difficulty S.

### generic cse — issue #19
**Function / files:** `cse` in `cse.go:18-321`; `storeOrdering` (:326), `partitionValues` (:369), `cmpVal` (:405), `lt2Cmp`, `auxmap` type, `isMemUser` (:444), `isMemDef` (:458), `getEffectiveMemoryArg` (:478), `skipDisjointMemDefs` (:503), all in cse.go. Shared: `disjoint`/`disjointTypes`/`isSamePtr`/`overlap` (rewrite.go:902-983), `f.Sdom()` (func.go:788) → `dominatorsLTOrig` (dom.go:65) + `newSparseTree` (sparsetree.go:62; `domorder` :202, `IsAncestorEq` :174), `slices.SortFunc` (pdqsort, slices/zsortanyfunc.go:61), `Type.Compare` (types/type.go:1030), `Type.IsMemory` (type.go:1549).
**Position & ordering:** index 9 (compile.go:467), not required. `passOrder`: generic cse→prove (:538), generic cse→dse (:549), generic cse→nilcheckelim (:551), generic cse→tighten (:560). The same function runs again as "lowered cse" (index 40, out of scope) and reuses `f.auxmap`.
**Enabled (linux/arm64, default build):** yes; disabled by -N. `debug>1/2` prints partitions only; `stats>0` adds a LogStat.
**Size:** cse.go 546 lines / 407 code (all exclusive except shared use by "lowered cse"). Shared: disjoint & friends (~80), Sdom/dominators/sparsetree (~250), pdqsort (Go stdlib).
**What it does:**
1. Collect all non-memory values (`!Type.IsMemory()`, which also excludes tuples/results ending in mem) in f.Blocks × b.Values order into `a`. Assign `f.auxmap[v.Aux]` IDs on first appearance; the map is **persistent in Func**.
2. `partitionValues`: `slices.SortFunc(a, cmpVal, then ID)`. `cmpVal` compares Op number, AuxInt, nargs, Block.ID for phis, Type (`Type.Compare`, skipped for Select0/1/N), and Aux (nil first, then auxmap rank). Group runs with cmpVal==EQ; drop singletons. Classes are subslices of `a`.
3. `valueEqClass[id]` = class number pNum (1…) in partition order, or `-id` for singletons/memory values.
4. Refinement fixpoint. Index loop over `partition`, which grows during the loop. For commutative ops, **swap Args[0]/Args[1] in place** when class(arg0) > class(arg1). Then `slices.SortFunc` by arg classes; a memory-user mem arg (Load/NilCheck) is compared via `getEffectiveMemoryArg`, which skips up to 255 provably disjoint Store/Zero/VarDef defs (stops at a def whose mem arg has Uses>50) and is memoised in `memTable`. Split at adjacent pairs with unequal arg classes (LocalAddr's mem arg is ignored here but not in the sort). If split: swap-remove class i from `partition`, `i--`, append the non-singleton pieces with new pNums, and reset singletons to `-id`.
5. `sdom := f.Sdom()`. For each class, `slices.SortFunc` by `domorder(block)` (dominator-tree entry number). Then for memory users by skip count; for LocalAddr by mem-arg rules using `storeOrdering` (fatal if the score is ≤0); then IsStmt values first; otherwise 0. Greedy pass: the first non-nil `v` replaces each following `w` with `IsAncestorEq(v.Block, w.Block)` (`rewrite[w.ID]=v`), stopping at the first non-dominated w.
6. Apply (f.Blocks × b.Values × args): `SetArg` to the representative. If the replaced arg `w` was IsStmt (and not NilCheck) and sits in the same block and line as the user `v`, move the mark to v. Controls are replaced unless the control is a NilCheck. NamedValues are not updated. Nothing is allocated or freed.
**Data structures:** `f.auxmap map[Aux]int32` (lookup/insert only); scratch slices from f.Cache (`a`, `o` storeOrdering cache, `valueEqClass`, `memTable` packed (memID<<8|skips), `rewrite`); `partition []eqclass` (subslices of shared storage); SparseTree.
**Parity traps (order dependence / nondeterminism):**
- **Unstable sorts with ties.** The refinement sort (:107-128) returns 0 for different values, and so does the dominator sort (same block, same stmt-ness, :215-267). `slices.SortFunc` is pdqsort: insertion sort (stable) for n≤12; for larger n, ninther pivots, partitioning, `breakPatterns` with an xorshift seeded by length, and a heapsort fallback. Which equal value in a block becomes the representative depends on this exact algorithm and on the input order produced by earlier sorts. **The Lean port must replicate Go's pdqsortCmpFunc exactly.** Deterministic, not random. The LocalAddr branch can even make the comparator non-transitive, which is more reason to port pdqsort verbatim. `partitionValues` alone has an ID tie-break, so its result is algorithm-independent provided cmpVal is a consistent preorder.
- **In-place commutative arg swaps** (:101-106) change `Args` order of every value in multi-member classes, even values that are never replaced, and repeatedly as classes refine. The decision uses current `valueEqClass` (negative IDs for singletons).
- Partition processing order: swap-remove plus append, with pNum numbering in split order. That numbering feeds the comparators.
- `f.auxmap` ranks depend on first-occurrence order across all cse runs on this Func, so it is persistent state. The key is Go `==` on the Aux interface.
- `Type.Compare` is a structural total preorder, not pointer identity: values with distinct but CMPeq type pointers can be merged. Select0/1/N ignore type.
- `domorder` numbering comes from `newSparseTree`, whose child order derives from **`f.postorder()`, the cached postorder**. A stale cache (e.g. computed by number lines and not invalidated after opt's `b.swapSuccessors()`, block.go:318, which does not call `invalidateCFG`) changes sibling numbering, which can change pdqsort tie outcomes. The Lean model must carry `cachedPostorder` with Go's exact invalidation points.
- `skipDisjointMemDefs` reads `Uses` counts (>50 cutoff). `maxId = 2^23-1` disables skipping for large IDs. `memTable` and `storeOrdering` memos are order-independent (pure functions of the graph during the pass).
- Stmt-mark transfer happens on the first rewritten use in (f.Blocks, b.Values, arg) order.
**External state read:** `Type.Compare`, `IsMemory`, `Size`, `IsPtr`/`Elem`/`IsUnsafePtr`/`NotInHeap`/`HasPointers` (disjointTypes), `types.PtrSize`; Aux equality and identity (auxmap, isSamePtr on Addr/LocalAddr aux); opcodeTable `commutative` and Op numbering (cmpVal orders by numeric Op); `f.auxmap`; cached postorder/idom/sdom; `f.pass.debug/stats`.
**Depends on:** dominators (`dominatorsLTOrig`), SparseTree, postorder (cached); disjoint/isSamePtr from rewrite.go; zcse and opt deadcode before it (it expects no copies and only reachable blocks). Followed by phiopt and the required gcse deadcode.
**Proof strategy & difficulty:** L. Recommended: an exact untrusted port (needed for parity anyway: pdqsort, auxmap, Type.Compare oracle) plus a proven **validator** for correctness. The validator checks that, for each substitution w→v, v's block dominates w's block (Sdom), and v,w are congruent: same op, auxint, Aux (==), Type CMPeq or Select exemption, same block if Phi, and args pairwise equal after applying the substitution map. Commutative ops may match swapped. Memory users' mem args must reach the same def via defs proven disjoint by `disjoint`. The arg swap of commutative ops needs a commutativity lemma per op. A direct proof of the partition-refinement fixpoint is possible but heavier.
**Proof (done, #19):** translation validation. `csePass` runs `cseChecked`: `cseRw` (cse and its substitution `rewrite`) and the Bool checker `CSE.crel` (`GoFV/Opt/CSE.lean`): same CFG, block kinds and values; every value keeps ID/op/aux/auxint/type/block, its arguments become their representatives (`rep`), the first two of a commutative op possibly swapped; controls kept or redirected; every substitution `x ↦ r` has `r` unreplaced, listed in a block that is an ancestor of `x`'s in the dominator certificate (the same block for a `Phi`), the same op/aux/auxint and type shape, not a root other than `NilCheck`, and the same arguments in the output, except `LocalAddr {n}` and `NilCheck` (first argument only) and `Load` (different memory arguments); every output block has a schedule whose roots are in the input's order. Rejection returns the input. `GoFV.Proof.CSE.cse_refines` (`GoFV/Proof/Pass/CSE*.lean`) needs the fragment `cseFrag`: the strict checker (`crel tabs true`) accepts the result too, i.e. each `Load` merge through different memory arguments is re-derived by `CSE.memEnd` (`GoFV/Opt/CSEMem.lean`: skips of `Store`/`Zero` writing a different global symbol or named local, or the same allocation at offsets apart modulo 2^64; `load_memEnd`) and the roots keep their exact order (the lenient checker also accepts permuted runs of `NilCheck`s on one memory). Go's type-based (`disjointTypes`) and `VarDef` skips are outside the fragment (#111). Lock-step simulation with equal frames at block entries (`refines_of_rel`, `CSESim`, `CSEPhi`); one block (`blockOK`, `CSEBlock`): along the target's schedule, a representative holds its value (`rep_corr`, `CSEClass`; commutative ops `evalOp_swap`, `CSEComm`), and values the source did not reach before panicking are pure with arguments (the scheduler's pure-first property), so they evaluate. Witness `cse_witness` on `decodedLen` (two `Div64 v7 v13` merged). `lake exe cse-probe <corpus>`: checker rejections and inputs outside the fragment.
**Issue summary:** Enabled by default (off under -N). ~400 LOC plus Sdom/pdqsort/disjoint. Top traps: Go pdqsort with tie-returning comparators (must be ported exactly); in-place commutative arg swaps on all multi-member classes; persistent `f.auxmap` ranks; Type.Compare structural order; domorder built from the possibly stale cached postorder (opt's swapSuccessors does not invalidate). External: Type.Compare/IsMemory/disjointTypes queries, Aux identity, Op numbering. Difficulty L; prerequisites dominators/SparseTree/postorder caching, disjoint.

### phiopt — issue #20

**Function / files:** `phiopt`, `phioptint`, `convertPhi` in `phiopt.go:28,288,344`; helpers `f.Sdom()` (SparseTree, `sparsetree.go`), `makeLCArange`/`lcaRange.find` (`lca.go:36,105`), `Value.reset/AddArg/SetArgs2`, `Block.NewValue1`.
**Position & ordering:** idx 10 (`compile.go:468`), not required; no passOrder constraints mention it. Between `generic cse` and `gcse deadcode` ("clean out after cse and phiopt").
**Enabled (linux/arm64, default build):** yes; disabled by -N. No arch/flag dependence; `f.pass.debug>0` only `Warnl` (`phiopt.go:84,100,116,129,143,336,349`).
**Size:** `phiopt.go` 352 lines (204 non-comment). Shared: `lca.go` 127, `sparsetree.go` (Parent/IsAncestorEq), dominators.
**What it does:** `sdom := f.Sdom()` once (`:29`); CFG is never modified.
- Loop 1 (`:30-150`), blocks in `f.Blocks` order with exactly 2 preds and ≥1 value: walk each pred up through single-pred/single-succ chains to `b0`/`b1`; require `b0==b1` and `b0.Kind==BlockIf`; `reverse` = which pred is reached via `b0.Succs[0]` (Fatalf if neither). For each `OpPhi` v in `b.Values`: if integer type → `phioptint` (phi of Const{8,16,32,64} 0/1 → `ZeroExtNto M (CvtBoolToUint8 [Not] ctrl)` or Copy for 1-byte); if boolean: (Const true/false pair) → `Not`/`Copy` of `b0.Controls[0]`; `x = ctrl ? true : val` with `val` dominating b → `OrB`; `ctrl ? val : false` → `AndB`; `ctrl ? val : ctrl` → AndB; `ctrl ? ctrl : val` → OrB (`:79-148`, dominance via `sdom.IsAncestorEq(tmp.Block, b)`).
- Loop 2 (`:195-285`), "strengthened": blocks with 2 preds; first phi `(ConstBool a) (ConstBool b)` with a≠b: if `pb0` is If and is idom(b) and the other succ of pb0 dominates pb1 → `convertPhi(pb0, v, ei)`; symmetric for pb1; else `b0 = LCA(pb0,pb1)` (lazily built `lcaRange`), must be If, succs must dominate preds in one orientation, both succs single-pred → `convertPhi`. Every outcome other than `continue` (non-matching phi) executes `break`, so at most one phi per block is examined past the filter.
**Data structures:** SparseTree (dominator tree with entry/exit numbering), `lcaRange` (Euler-tour RMQ), no maps.
**Parity traps (order dependence / nondeterminism):**
- Loop 2 `break` semantics: only the first constant-bool phi per block is considered (success or failure) — replicate exactly.
- `phioptint` allocates: optional `OpNot` then `OpCvtBoolToUint8`, both `NewValue1(v.Pos, …)` appended to `v.Block` (`:322-325`) — IDs from the free list in that order; appended values are not visited by the ongoing `range b.Values` (snapshot) and are not phis anyway.
- `phioptint` transiently `v.AddArg(a)` on the phi (3 args) before `v.reset` (`:325-336`); net Uses unchanged — a Lean port may skip the transient but must yield the same Uses.
- In-place rewrites keep the phi's `Pos` (phi pos is NotStmt at creation, `func.go:298`); new values inherit it.
- LCA/IsAncestorEq/Parent are semantic functions of the dominator tree → independent of sparse-tree numbering; harmless. No maps, no sorts.
- Dominance info is computed once and stays valid (no CFG edits).
**External state read:** `v.Type.IsInteger/IsBoolean/Size`, `f.Config.Types.UInt8` (`:327`), `f.pass.debug`. Nothing else.
**Depends on:** `f.Sdom()`/`f.Idom()` (dominators), `lca.go`. Benefits from CSE; assumes `b0.Controls[0]` is the boolean condition (generic If). Requires dead code removed? Not strictly; unreachable blocks are absent from sdom (IsAncestorEq false).
**Proof strategy & difficulty:** S. Direct simulation: each rewrite is a local phi replacement justified by "control reached b via pred i ⇔ cond value", requiring a lemma relating If-successor domination to path conditions, plus dominance of `tmp` (value available). Ported directly over the Lean dominator-tree API; parity is straightforward.
**Issue summary:** Enabled (off at -N), idx 10, 352 LOC (204 non-comment). Traps: loop-2 first-phi-per-block `break`, allocation order Not→CvtBoolToUint8 in phioptint, f.Blocks/b.Values order. External: only types and Config.Types.UInt8. Deps: Sdom/Idom, LCA. Difficulty S.
**Proof (done, #20):** translation validation. `phioptPass` runs `phioptChecked`: the Bool checker `PhiOpt.prel` (`GoFV/Opt/PhiOptCheck.lean`: same CFG, kinds, controls and values except rewritten `Phi`s and new `Not`/`CvtBoolToUint8`; each rewritten `Phi` justified by edge facts — the edge leaves the `If` on its control `c`, a chain of single-predecessor blocks not defining `c`, or a block dominated by a *guard* of `c`: a single-predecessor successor of the `If`, strictly dominated by `c`'s block, `domFact`) accepts phiopt's output or the input is returned. `GoFV.Proof.PhiOpt.phiopt_refines` (`GoFV/Proof/Pass/PhiOpt*.lean`; no fragment beyond `check`: `sched_transfer`), witness `phiopt_witness` on `runtime.tracefpunwindoff`. `lake exe phiopt-probe`: the checker never rejects on the quick corpus (all 306801 sections). Go's special case `pb0 == sdom.Parent(b)` does not require `sb1` to have one predecessor; the checker does, and no corpus function needs it.

### nilcheckelim — issue #23

**Function / files:** `nilcheckelim` in `nilcheck.go:15-187` (`nilcheckelim2` out of scope); helpers `storeOrder` (`schedule.go:397-558`), `valuePosCmp` (`schedule.go:591`), `isPoorStatementOp` (`numberlines.go:13`), `xposmap` (`f.cachedLineStarts`), `f.Sdom()` (child/sibling lists), `f.newSparseSet`, `f.Cache.allocValueSlice/allocInt32Slice`.
**Position & ordering:** idx 12 (`compile.go:470`), not required. passOrder: `{"generic cse","nilcheckelim"}` (:551), `{"nilcheckelim","generic deadcode"}` (:553), `{"nilcheckelim","late fuse"}` (:555), `{"opt","nilcheckelim"}` (:557).
**Enabled (linux/arm64, default build):** yes; disabled by -N. `f.fe.Debug_checknil()` (`base.Debug.Nil`) only gates `Warnl` (`nilcheck.go:131`). `storeOrder` short-circuits on `f.pass.name == "nilcheckelim"` (`schedule.go:426`).
**Size:** `nilcheckelim` 173 lines (122 non-comment). Exclusive-ish helper: `storeOrder`+`valuePosCmp` ~175 lines (127 non-comment; shared with scheduling/other passes). Shared: `xposmap`, sparse set, sparse tree.
**What it does:**
1. `nonNilValues[ID]` (value slice): seed with values whose op is Addr, LocalAddr, AddPtr, OffPtr, Add32, Add64, Sub32, Sub64, SlicePtr (`:52-62`); fixpoint over `f.Blocks`×`b.Values` marking Phis whose args are all non-nil (`:64-84`).
2. Explicit-stack DFS of the dominator tree from `f.Entry` (`:91-186`), stack items `Work(block)` / `ClearPtr(ptr)` (LIFO). For `Work b`: if b has a single pred `p` that is `If (IsNonNil ptr)` and b is its true successor and ptr not yet non-nil → mark, push ClearPtr. Then `b.Values = storeOrder(b.Values, …)` (reorders block values!). `pendingLines.clear()`. For each v: `IsNonNil ptr` with ptr known non-nil → (stmt mark moved to pendingLines) `v.reset(OpConstBool)`, AuxInt=1; `NilCheck ptr` with `nonNilValues[ptr]=nc` → stmt mark to pendingLines, `v.Op=OpCopy; v.SetArgs1(nc)` (nc = dominating NilCheck or the ptr itself); otherwise record `nonNilValues[ptr]=v`, push ClearPtr, and (fallthrough) for every other value: if not NotStmt, not poor op and its (file,line) is pending → set IsStmt, remove. Second sweep over `b.Values` for remaining pending lines, then `b.Pos`. Push `Work` for each dom child (child/sibling order). `ClearPtr` resets the entry to nil.
3. `storeOrder` (only when block has ≥1 memory value and ≥1 NilCheck in this pass): find the unique last store (Fatalf on two live stores), number the in-block store chain `3n`, DFS other values (`3*max+1` for NilCheck, `3*max+2` otherwise, phis `2`), stable counting-sort into bins, then sort each maximal run of consecutive NilChecks with `slices.SortFunc(valuePosCmp)` (`schedule.go:536-555`).
**Data structures:** `nonNilValues []*Value` (by ID), `work []bp` stack, sparseSet (membership only), `storeNumber []int32`, `count` bins, xposmap.
**Parity traps (order dependence / nondeterminism):**
- `storeOrder` permanently rewrites `b.Values` order in every reachable block containing a NilCheck and a memory value — the exact algorithm must be ported. Bins are stable w.r.t. the input order; DFS order inside does not affect store numbers for acyclic in-block deps.
- NilCheck runs sorted with `slices.SortFunc` (pdqsort, **unstable**); `valuePosCmp` uses `XPos.Before/After` = (PosBase index, raw `lico` incl. column, xlogue and is_stmt bits) (`cmd/internal/src/xpos.go:30-50`). Ties (equal XPos) are possible; runs ≤12 use insertion sort (stable), >12 need bit-exact pdqsort (deterministic, no randomness). Either port pdqsort or show ties can't occur in practice.
- Which NilCheck survives (and becomes the Copy target of later ones) is the first in post-`storeOrder` order along the dominator path.
- Dom-tree child order and LIFO stack order do not affect the result: facts are path-scoped (ClearPtr pushed before children so it pops after the subtree) and pendingLines is per block — harmless.
- No allocation/freeing: in-place `reset`/`Op=OpCopy`; `IsNonNil → ConstBool` value is not entered into `f.constants`.
- Positions: pendingLines keyed by (file, line), lost stmt from removed check moved to the first eligible later value in pass 1, any value in pass 2, else `b.Pos`; ConstBool loses its stmt.
- Unreachable blocks (not in dom tree) are not visited (none after `gcse deadcode`).
**External state read:** `f.fe.Debug_checknil()` (Warnl only), `opcodeTable` nilCheck flag via ops, `f.pass.name` (storeOrder), XPos ordering (PosBase indices — global table order), `f.Entry`.
**Depends on:** `f.Sdom()` (dominator tree with child/sibling links), `storeOrder`, `f.cachedLineStarts`. Invariants: one live store per block (storeOrder Fatalf), CSE done (efficacy), opt's user nil-check rewrites (`(NilCheck (Addr …))` etc.).
**Proof strategy & difficulty:** M. Direct simulation: invariant "on every path to the current block, `nonNilValues[p]` ≠ nil ⇒ p is non-nil at this point" (seeds justified by op semantics incl. the unsafe-arith assumption, which must be an explicit axiom); NilCheck→Copy of the dominating check preserves values. The value reordering by `storeOrder` needs a lemma that reordering within a block respecting deps and store order is semantics-preserving (or treat `b.Values` order as non-semantic before scheduling). Parity effort dominated by storeOrder + pdqsort.
**Proof (done, #23):** `GoFV.Proof.Nil.nilcheck_refines : nilcheckelimPass penv f = .ok out → check ce f = .ok () → nilFrag penv f = true → Refines out.tables out.func penv.tables f`. Checker `NilCheck.nrel` (`GoFV/Opt/NilCheckRel.lean`): same CFG/controls, block values permuted with `Phi`s in order, each removed `NilCheck p` justified by a nil check of `p` in a strict dominator or earlier in the source schedule, by `p` pointing into an allocation (`safePtr`: `Addr`/`LocalAddr`/nil check/`GetG` through `OffPtr`/`AddPtr`), or by an identical check right after it among the roots (`After`); `IsNonNil`→`ConstBool` by a dominating/earlier check; roots keep their order. Lock-step simulation with equal frames (`NilBlock`, `NilSim`); a check that passed returns a pointer into an allocation (P3 blk-nil `NilCheck`, `nilCheck_ok_safe`), so `OffPtr`/`AddPtr` of it never panic in a check. Witness `nilcheck_witness` (`(*bufio.Reader).Buffered`). Outside the fragment: `If (IsNonNil p)` edge facts (unsound in the model: a pointer `⟨nil, c≠0⟩` passes `IsNonNil` but faults only at the dereference, which the model's loads do not), phis of non-nil values, unchecked `OffPtr`/`AddPtr`/`SlicePtr` seeds (Go's assumption, semantics.md §10). Quick corpus: 2,943 changed inputs, checker accepts 1,640 (7,994/9,297 inputs in `nilFrag`).
**Issue summary:** Enabled (off at -N), idx 12, 173 LOC (+~175 storeOrder shared). Traps: storeOrder reorders b.Values (stable bins + unstable pdqsort of NilCheck runs by raw XPos incl. stmt bits), survivor choice depends on that order; dom-walk order harmless. External: base.Debug.Nil (Warnl), pass name, XPos/PosBase indices. Deps: Sdom, storeOrder, line map. Difficulty M.

### prove — issue #24

**Function / files:** `prove` in `prove.go:1573-1744`. Helpers that only prove uses: the rest of `prove.go` (factsTable, limit arithmetic, `flowLimit`, `addValueFact`, `simplifyValue`, `constantFoldArguments`, `simplifyBlock`, `removeBranch`, `topoSortValuesInBlock`), `poset.go` (the signed and unsigned partial-order sets), `loopbce.go` (`findIndVar`, `parseIndVar`, `findKNN`, `printIndVar`), and `downward_counting_loop.go` (`maybeRewriteLoopToDownwardCountingLoop`).

**Position & ordering:** It is `passes[13]` (`compile.go:471`) and is not required. `passOrder` constraints: `generic cse` < prove (`:538`), prove < `generic deadcode` (`:540`), prove < `divisible` (`:542`), prove < `known bits` (`:612`). Before it come `nilcheckelim` (12) and `gcse deadcode` (11, required). The next pass is `divisible` (required).

**Enabled (linux/arm64, default build):** Yes. `-N` turns it off because it is not required (`compile.go:69`). `-d=ssa/prove/off` also turns it off. Configuration that changes behaviour:
- `Config.haveCondSelect` is true on arm64 (`config.go:248`), so the Mul→CondSelect rewrite is live.
- `Config.arch == "amd64"/"386"` controls the Div/Mod "no fix-up" `AuxInt=1` (`prove.go:2837`). That arch check is false on arm64, so prove only emits a Warnl there.
- `canCondSelect` reads `Config.RegSize` (=8) and `arch`.
- `Config.PtrSize` sets the SliceLen/SliceCap heap bound (`prove.go:1816-1823`).
- No GOEXPERIMENT and no `buildcfg` read.

`f.pass.debug` effects:
- `>0` adds Warnl for Proved/Disproved branches, "Induction variable…", "Inverted loop iteration" and the per-rewrite messages.
- `>1` adds the `x+d` Warnl and arg-fold messages.
- `>2` adds newLimit/update traces.
- `checkEnabled` only adds `poset.CheckEmpty` in `cleanup` (`prove.go:1362`).

None of these change the SSA.

**Size:**
- `prove.go` is 3177 lines (2362 non-blank, non-comment).
- `poset.go` is 1151 lines (757 code; about 110 of those are debug-only `CheckIntegrity`/`CheckEmpty`/`DotDump`).
- `loopbce.go` is 491 lines (313 code).
- `downward_counting_loop.go` is 166 lines (93 code).
- Exclusive total ≈ 3500 code lines. This is the largest machine-independent pass.

Shared helpers:
- CFG analyses: `dominators` (`dom.go:58`), `postorder` (`dom.go:12`), `newSparseTree`/`IsAncestorEq`/`Child`/`Sibling` (`sparsetree.go`).
- Constants and value construction: `f.constVal`/`ConstInt*`/`ConstBool`/`ConstNil` (`func.go:663-733`), `Block.NewValue2`.
- Value and block mutation: `Value.reset`/`copyOf`/`SetArg`/`AddArg3` (`value.go`), `Block.ResetControls`/`swapSuccessors` (`block.go`).
- From branchelim: `canCondSelect` (`branchelim.go:72`).
- Rewrite utilities: `isPowerOfTwo` (rewrite.go), `isGenericIntConst` (`value.go:488`).
- `f.Cache` allocators: `allocLimitSlice`, `allocBoolSlice`, `allocUintSlice`, `scrPoset`.

**What it does:** It works in three phases.

1. **Induction variables (pre-walk).** `findIndVar(f)` (`loopbce.go:117`) scans `f.Blocks` in order. For each `BlockIf` whose control is `Less*`/`Leq*` (signed only), it tries both argument orders (idx 0, then 1). It accepts `ind = Phi(init, nxt)` with `nxt = Add(ind, inc)`, where `inc` is a nonzero constant ≠ MinInt. The header must have exactly 2 preds. The loop-body edge is found through `sdom.IsAncestorEq`, the body entry must have 1 pred, the entry must dominate `nxt`, and overflow checks must pass (`findKNN` for non-constant limits). When the limit is constant it may tighten it with **`f.constVal(limit.Op, limit.Type, v, true)`** (`loopbce.go:253,305`). That call can **create a new constant in `f.Entry`** even if nothing ends up using it.

   `prove` then looks at each indVar (`prove.go:1576-1597`):
   - If `ind.Uses==2 && nxt.Uses==1`, it calls `maybeRewriteLoopToDownwardCountingLoop` (see T1 below).
   - Otherwise it records the indVar in `indVars[v.entry]`, a map that is only used for lookups.

2. **Fact table init.**
   - `newFactsTable` takes two posets from `f.Cache.scrPoset` and sizes `limits` to `f.NumValues()`.
   - It sets `limits[v.ID] = initLimit(v)` for every value in `f.Blocks`/`b.Values` (`prove.go:1746`). `initLimit` gives type-based ranges plus constants, extensions, ctz/bitlen/popcount, CvtBoolToUint8, SliceLen/Cap/StringLen ≥ 0, and slice length ≤ heap/elemSize.
   - It sets `limitStack` to 4 zero entries.
   - Then `ft.checkpoint()`.
   - A pass over `f.Blocks` × `b.Values` (skipping `Uses==0`) records the first `SliceLen`/`SliceCap` per slice ID in `ft.lens`/`ft.caps`. Every later one gets `ft.update(b, v, first, signed, eq)` (`prove.go:1604-1634`).

3. **Dominator-tree DFS with an explicit stack** (`prove.go:1647-1739`).
   - `idom := f.Idom()` and `sdom := f.Sdom()` are computed once.
   - The stack starts with `{f.Entry, descend}`. On each pop it computes `parent = idom[b]` and `branch = getBranch(sdom, parent, b)` (`prove.go:2207`). `getBranch` returns positive/negative when `parent` is a `BlockIf` and `Succs[k]` dominates `b` and has exactly 1 pred; for jump tables it returns `jumpTable0+i`; otherwise unknown.
   - **descend:**
     1. `ft.checkpoint()`.
     2. For each indVar of `b`: `addIndVarRestrictions` (`prove.go:2240`).
     3. If the branch is known: `addBranchRestrictions(parent, branch)`. This uses `booleanTrue`/`booleanFalse` of the control, or for jump tables a `newLimit` on the control (through `isConstDelta`).
     4. `addSlicesOfSameLen(ft, b)` (`prove.go:1406`).
     5. If `ft.unsat`: `removeBranch(parent, branch)`, then `ft.restore()`, and the children are not visited.
     6. Otherwise:
        - `topoSortValuesInBlock(b)` **reorders `b.Values`**.
        - Then for each `v` in `b.Values` (slice captured before the loop, so values appended during the loop are not visited): `flowLimit(v)` (range propagation from args, `prove.go:1853`), `constantFoldArguments(v)`, `addValueFact(b, v)` (relational facts, `prove.go:2404`), `simplifyValue(b, v)`.
        - Then `simplifyBlock(sdom, b)`.
        - Push `{b, restore}`, then push each dom child in `sdom` child-list order (`Child`/`Sibling`).
   - **restore:** `ft.restore()`.
   - After the loop, a final `ft.restore()` undoes the initial checkpoint, then `ft.cleanup(f)` returns the posets and slices to `f.Cache`.

The fact engine has four parts:

- **`update(parent, v, w, d, r)`** (`prove.go:857-1243`):
  - It does nothing if already unsat.
  - `v==w` is a self-fact check.
  - Signed/unsigned facts go into `orderS`/`orderU` through `SetOrder`/`SetOrderOrEqual`/`SetEqual`/`SetNonEqual`. Failure means unsat.
  - It always calls `addOrdering(v,w)` and `addOrdering(w,v, reverseBits[r])` (`prove.go:840`).
  - Boolean/pointer facts are checked against the existing orderings list.
  - It derives new limits from the relation using the endpoint limits.
  - len/cap cross-facts recurse.
  - Fence-post rules, using `isConstDelta`: `x+1>w ⇒ x>=w`, `x-1>=w ∧ x>min ⇒ x>w`, and the reverse forms.
  - `x+delta > w` with constant `delta` gives signed bounds on `x`.
  - It looks through value-preserving extensions (`isCleanExt`).
  - All of this is recursive.
- **`newLimit(v, lim)`** (`prove.go:642-838`):
  - Intersects the new limit with the old one and propagates signed↔unsigned.
  - Returns if nothing changed. If the result is unsat it sets `ft.unsat`.
  - Uses the `recurseCheck` guard.
  - Pushes the old limit onto `limitStack`.
  - Propagates the new limit to every `ordering` of `v`, walking the linked list newest-first.
  - If `v` is a boolean that is now constant, it decodes `domainRelationTable` (comparisons) or `IsNonNil`/`IsInBounds`/`IsSliceInBounds` and calls `addRestrictions`/`update`.
- **Undo:** `checkpoint`/`restore` (`prove.go:1267-1307`) use three stacks: `limitStack` (marker `vid==0`), the posets' own `undo` (`poset.go:1059-1151`), and `orderingsStack` (marker `ID 0`, with `ordering` nodes recycled through `orderingCache`). `unsat` uses `unsatDepth` counting.
- **`flowLimit`:** range arithmetic per op (Zero/SignExt, Trunc, Ctz/PopCount/BitLen, Or/Xor/Com, Add/Sub/Neg/Mul, Lsh, signed/unsigned Rsh, Div, Mod, Phi union). Sub also calls `detectMod`, `detectSliceLenRelation` and `detectSubRelations`; these consult `orderS.Ordered`/`OrderedOrEqual` and walk orderings lists.
- **`addValueFact`:**
  - Add/Sub/And/Div/Rsh/Mod relational facts with overflow guards.
  - String/Slice len/cap `== SliceMake` args.
  - `IsInBounds`/`IsSliceInBounds` proven true through `checkForChunkedIndexBounds` (`prove.go:2338`).
  - Phi min/max detection through `addLocalFactsPhi` (`prove.go:2573`).

#### prove: every transformation and when it fires

| # | Where | Transformation | Fires when |
|---|---|---|---|
| T0 | `loopbce.go:253`, `:305` | `f.constVal(limit.Op, limit.Type, v, true)` may append a new cached constant (NoXPos) to `f.Entry.Values` | A constant loop limit can be tightened using the stride (`inclusive && v != limit.AuxInt` or `!inclusive && v±1 != limit.AuxInt`). This happens even when the indVar is later discarded. |
| T1 | `downward_counting_loop.go:46-166` | Loop inversion: `check.SetArg(idxEnd, start)`, `ind.SetArg(idxStart, end)`, swap `check.Args[0]`↔`[1]` (raw swap; Uses unchanged), make `nxt.Args[0]==ind` by raw swap, flip `nxt.Op` Add↔Sub (8/16/32/64) | The indVar has `ind.Uses==2 && nxt.Uses==1`, `start` is a generic int constant, `end` is not, `end.Block != ind.Block`, `safeAdd(start.AuxInt, neededRoom)` does not overflow (signed `Less`/`Leq` only; unsigned/Eq/Neq panic), both indices are found, and `sdom.IsAncestorEq(end.Block, ind.Block)`. `check = v.entry.Preds[0].b.Controls[0]`. |
| T2 | `prove.go:3150-3177` | **Reorder `b.Values`** with `slices.SortFunc` by key (dependency score, ID). Score: Phi=1; otherwise `max(2, 1+score(same-block arg))`. | Every block reached in descend that is not unsat, including `f.Entry`. The key is unique per value (ID tiebreak), so the result does not depend on the sort algorithm. Unvisited blocks keep their order. |
| T3 | `prove.go:2972-3016` | `v.SetArg(i, c)`, where `c` is a cached constant from `ConstBool`/`ConstInt8/16/32/64`/`ConstNil` with the arg's **type** (new constants are appended to `f.Entry`, NoXPos) | For every value of a visited block (Phis included), for each arg whose current path-sensitive limit is a single point (`min==max` or `umin==umax`) and whose op is not already `Const{8,16,32,64,Bool,Nil}`. Ptr-shaped args only when the value is 0 (nil). Other types are skipped. |
| T4 | `prove.go:2735-2768` | `Slicemask` → `reset(OpConst64)` (size 8) or `OpConst32`, `AuxInt=-1`, in place: same ID/Pos/Block, args dropped, not cached | `cap = x+delta` (isConstDelta) with `limits[x].umin > uint64(-delta)`, or otherwise `limits[cap].umin > 0` |
| T5 | `prove.go:2769-2780` | `Ctz{8..64}` → `Ctz{8..64}NonZero` (Op only) | Arg limit `umin>0 \|\| min>0 \|\| max<0` |
| T6 | `prove.go:2781-2790` | Signed `Rsh{8..64}x{8..64}` → unsigned `Rsh..Ux..` (Op only), then falls through to T7 | `limits[arg0].min >= 0` |
| T7 | `prove.go:2792-2809` | Shift `AuxInt = 1` ("bounded", read by `shiftIsBounded`, rewrite.go:619) | For every Lsh/Rsh/RshU: shift-amount limit `umax < 8*size(arg0)`, or `(max < bits && min >= 0)` |
| T8 | `prove.go:2811-2819` | Signed `Div{8..64}`/`Mod{8..64}` → unsigned op, `AuxInt = 0` | Both operand limits are nonnegative (`min>=0`) |
| T9 | `prove.go:2820-2838` | `AuxInt = 1` (no fix-up) | **Only on amd64/386.** On arm64 the condition (`q.max<-1 \|\| q.min>-1 \|\| p.min>mostNegativeDividend`) produces only a Warnl. |
| T10 | `prove.go:2840-2861` | `Mul{8..64}` → `And{size}` (Op only) | v's limit is not a single point; no operand is a constant power of two; both operands have `umax<=1` |
| T11 | `prove.go:2862-2878` | `Mul` → `CondSelect(y, zero, check)`. `zero = constVal(Const{size}, v.Type, 0)` (may be new in `f.Entry`). `check = b.NewValue2(v.Pos, Neq{size}, types.Types[TBOOL], zero, x)` is **appended to the end of `b.Values`** (new ID, keeps `v.Pos` including is_stmt). Then `v.reset(OpCondSelect)` and `AddArg3`. | Same guards as T10, exactly one operand (`x`, after a swap if it was `y`) has `umax<=1`, `haveCondSelect` (true on arm64), and `canCondSelect(v, arch, nil)`: size ≤ RegSize and ptr-shaped or integer |
| T12 | `prove.go:2880-2911` | `Eq{N}`↔`Neq{N}` inversion plus `SetArg(constPos, constVal(Const{N}, x.Type, 0))`: `x==1` → `x!=0`, `x!=1` → `x==0` | Exactly one side has a single-point limit equal to 1 and the other side has `umax<=1`. Uses limits, so the "constant" side may be a non-Const value. |
| T13 | `prove.go:2913-2940` | `And` → `copyOf(x)` (OpCopy, Type := x.Type) | Exactly one side is a single-point constant `c` and `wantBits & c == wantBits`, where `wantBits` = fixed leading bits of x plus all varying bits set |
| T14 | `prove.go:2942-2967` | `Or` → `copyOf(x)` | Exactly one side is a single-point constant `c` and `fixedLeadingBits(x) \| c == fixedLeadingBits(x)` |
| T15 | `prove.go:1690-1700` → `removeBranch` `:3052-3079` | Parent block `Kind = BlockFirst`, `ResetControls()` (control Uses--). If the removed branch is positive: `swapSuccessors()`, which also negates `b.Likely`. Likely is **not** reset. Edges are kept for deadcode. `b.Pos.WithIsStmt()` if the control's Pos is a stmt on the same file:line as `b.Pos`. Jump-table branches: no CFG change, only the subtree is skipped. | On descend, the facts for the child (indvar + edge + same-len slices) are unsat, **or `ft.unsat` was already true** (see the parity traps). |
| T16 | `prove.go:3018-3050` | Same `removeBranch(b, positive\|negative)` on the current block | `b.Kind==BlockIf`. For `Succs[0]` and then `Succs[1]`, when `getBranch(sdom, b, child)==unknown` (the child is not uniquely dominated through that edge): checkpoint, add the edge fact, read `unsat`, restore. Stops after the first removal. |

There is no other mutation. Prove never frees values or blocks, never calls `invalidateCFG`, and never changes `Succs`/`Preds`. Edges stay in place under `BlockFirst`.

**Data structures:**
- `factsTable` (`prove.go:509`):
  - `limits []limit` indexed by ID (from `f.Cache.allocLimitSlice`; grown by `initLimitForNewValue` `:575`).
  - `limitStack []limitFact`.
  - `recurseCheck []bool`.
  - `orderS`/`orderU *poset`.
  - `orderings map[ID]*ordering`: a singly linked list per value, newest-first, lookup only.
  - `orderingsStack []ID`.
  - `orderingCache` free list.
  - `lens`/`caps map[ID]*Value`, lookup only.
  - `reusedTopoSortScoresTable []uint`.
- `poset` (`poset.go:151`):
  - `values map[ID]uint32` (value→dense node index).
  - `nodes []posetNode`: each node has ≤2 child edges, with strict bit packed; extra nodes are used for fan-out.
  - `roots []uint32`.
  - `noneq map[uint32]bitset`, keyed by the larger index.
  - `undo []posetUndo`.
- `indVar` (`loopbce.go:20`).
- `indVars map[*Block][]indVar`.
- Work stack `[]bp`.
- `SparseTree` (`sdom`) and `idom []*Block`.

**Parity traps (order dependence / nondeterminism):**
- **`b.Values` is reordered** (T2) in every visited block. The key `(score, ID)` is a total order, so any correct sort reproduces it. Values appended after the sort are not sorted: T11 `check` at the end of `b`, and new constants at the end of `f.Entry` (`f.Entry` is always visited and sorted first). Constants from T0 exist before the walk, so they are sorted.
- **DFS visit order.** Siblings are pushed in `sdom` child-list order. `newSparseTree` builds that list in reverse postorder (`sparsetree.go:62-72`). The stack pops the last pushed first, so **siblings are visited in reverse-RPO order**. The restore entry is pushed before the children. This order decides:
  - which T15 removal happens first. After a removal, `parent.Kind==BlockFirst`, so a sibling popped later gets `branch=unknown` and does not learn the opposite fact.
  - the order of value and constant creation, and therefore IDs.
- **Allocation, no frees.** New values come from `constVal` (T0, T3, T11, T12) and `NewValue2` (T11). `newValue` pops `f.freeValues` LIFO first (`func.go:280`), so IDs depend on the free list left by `gcse deadcode`/`nilcheckelim`. `constVal` returns an existing cached value if `f.constants[c]` holds one with the same op and `Type.Compare==CMPeq`, scanning the per-key slice in order. Otherwise it appends `NewValue0I(NoXPos)` to `f.Entry` and sets `InCache`.
- **`f.constants` may return a cached constant that currently has `Uses==0`.** Such a constant is still in `f.Entry`, because constants leave the cache only when they are freed or reset (`freeValue` → `unCache`, `func.go:409`; `reset`/`copyOf`, `value.go:383,433`). The cache, including the slice order per auxint key, persists across passes and must be exported exactly.
- **Path-sensitive limits** make T3–T14 depend on the exact checkpoint/restore discipline and on recursion order inside `update`/`newLimit`:
  - orderings lists are walked newest-first;
  - the `recurseCheck` guard silently drops recursive updates (`prove.go:671-678`);
  - `update`'s fence-post, len/cap and extension recursion runs in a fixed order.

  All of this is deterministic but must be ported verbatim. Results are not a mathematical fixpoint: they depend on insertion order.
- **Poset is history-dependent (incomplete).** `noneq` bits are keyed by node index and are not migrated when nodes are aliased (`aliasnodes` `poset.go:289-340` never touches `noneq`). `SetNonEqual` on a fresh node checks nothing (`:1024`). `setOrder` turns `<=` into `<` only if `isnoneq` holds at that moment (`:858`). So answers to `Ordered`/`Equal`/`NonEqual` and the success bit of `Set*` depend on fact order. The internal structure (extra-node side choice `(i1^i2)&1` `:234`, `roots` order after `undoMergeRoot` appends at the end `:1141`, `findroot` scanning roots in order) does not change reachability answers: the DFS in `poset.go:379-441` is complete for "path with ≥1 strict edge". Port the poset verbatim, or prove that the port's answers equal Go's per call.
- **Map iteration in `aliasnodes`** (`for k, v := range po.values`, `poset.go:334`) pushes undo records in random order. This is **harmless**: each record restores one key to its own previous index, and the keys are distinct.
- All other maps (`orderings`, `lens`, `caps`, `indVars`, `domainRelationTable`, `opMin/opMax/opUMax`, `unsignedOp`, `ctzNonZeroOp`, `invertEqNeqOp`, `mostNegativeDividend`) are lookup only. No map in prove is iterated in an output-relevant way.
- **The unsat-inside-block quirk.** `addValueFact` can make `ft.unsat` true partway through a block. After that:
  - `update` becomes a no-op;
  - `simplifyBlock`'s first non-dominated edge sees `unsat` and is removed (T16);
  - every child descend sees `unsat` and calls `removeBranch(parent, branch)`. With `unknown`, or after the parent has already become `BlockFirst`, that is a no-op apart from `Controls[0]==nil` handling;
  - the whole dominated subtree is skipped: no T2–T14 there.
- **`limitStack` starts with 4 zero records** (`prove.go:567`). These act as extra checkpoint markers. Harmless, but needed if the Lean port asserts stack balance.
- **`initLimitForNewValue`** overwrites `limits[id]` without an undo record (`prove.go:575-591`). This only happens for constants, whose limits are exact and never narrowed, so it is harmless.
- **`b.Likely`:** T15/T16 positive removal negates Likely through `swapSuccessors` (`block.go:318-330`); negative removal keeps it.
- **Positions:**
  - T4 and T5–T14 keep the value's Pos.
  - T11 `check` copies `v.Pos` verbatim. `newValue` only strips is_stmt for `notStmtBoundary` ops.
  - New constants get `src.NoXPos`.
  - T15 may set is_stmt on `b.Pos`. This needs `SameFileAndLine`, so line-table information is required, not just opaque positions.
- **Pointer identity:** `ft.lens/caps` and `orderings` compare `*Value` (`o.w == w`) and `bound.Args[0] == slice`. Use IDs in Lean.
- **Cached CFG analyses:**
  - `f.Idom()`/`f.Sdom()` (`func.go:779,788`) come from the cache if it is valid. Prove does not invalidate it because it does not change edges.
  - The postorder that `newSparseTree` uses decides sibling order. The export must either carry the cached analyses or guarantee they are recomputable, i.e. not stale.
- **Randomness:** none. Poset's "non-deterministic" comment refers to the deterministic `(i1^i2)&1`.
- **`f.Cache.scrPoset` reuse across functions** (`func.go:170-182`, returned in `cleanup` `prove.go:1357`): after the final `restore()` the poset is empty except for `noneq` map keys that still hold all-zero bitsets, plus slice capacity. `setnoneq` reuses a zero bitset of the same size (`poset.go:570-582`). **Harmless.**

**External state read:**
- `Config`: `haveCondSelect`, `arch`, `RegSize`, `PtrSize`.
- `types`:
  - `Type.Size()`, `IsInteger`, `IsBoolean`, `IsPtrShaped`, `IsSigned`.
  - `Elem().Size()` of the slice type (SliceLen/Cap).
  - `Type.Compare` (constants cache) and `types.Types[TBOOL]`.
- `auxToCall(v.Aux).Fn.String()`: debug only.
- `f.pass.debug`, `f.Warnl`, `b.Logf`.
- `checkEnabled`.
- `f.constants`, `f.freeValues`, `f.vid` (allocation).
- `f.Cache` scratch (limit/bool/uint slices, scrPoset).
- `f.cachedIdom`/`cachedSdom`/`cachedPostorder`.
- Positions: `IsStmt`, `SameFileAndLine`, `WithIsStmt`.
- `opcodeTable` is not consulted.
- No `base.Flag`, no `buildcfg`, no `ir.Name`. `base.Fatalf` appears only in loopbce assertions.

**Depends on:**
- Dominators (`dom.go`), postorder, `SparseTree` with `IsAncestorEq`/`Child`/`Sibling`/entry-exit numbering.
- `findIndVar` and the downward-loop rewrite.
- The poset.
- `canCondSelect` from branchelim.
- The `f.constants` cache.

Invariants from earlier passes:
- No `OpCopy` chains are relied on, but CSE is assumed for effectiveness (`generic cse` < prove).
- Dead-but-unremoved values are tolerated (`Uses==0` skipped for lens/caps).
- The generic (not lowered) op set.
- `Phi`s with exactly 2 args for loop headers: `findIndVar` checks this and prove panics otherwise (`prove.go:1578-1581`).

Downstream consumers:
- `divisible`/`divmod` and the lowering rules read Div/Mod `AuxInt` and shift `AuxInt` (bounded).
- `generic deadcode` removes `BlockFirst` dead edges and dead consts.

**Proof strategy & difficulty:**
- **XL.**
- A direct verified port would need a soundness proof of the whole fact engine. That covers the limit arithmetic with overflow cases, about 40 `update` derivation rules, poset soundness and undo correctness, path-sensitivity through the dominator tree, and loop induction reasoning.
- Recommended: an **untrusted verbatim port** (needed anyway for exact ID/order parity) **plus a per-transformation translation validator.**
  - For each T3–T14 and each T15/T16 removed edge, the validator collects the dominating-edge assumptions: the chain of `idom` edges with `getBranch`≠unknown, plus the facts from the indVar invariant.
  - It checks the side condition with a verified decision procedure. Options: bit-vector `bv_decide` over the SSA defs in the cone of influence, with kernel-checked LRAT; or a small verified interval/difference-bound checker that emits certificates.
- T1 (loop inversion) needs its own loop-invariant proof: a simulation with an inverted counter.
- T2 is a permutation of a block's unordered value set. It is semantically trivial given schedule-independence of SSA, but it must be replicated exactly for parity.
- The indVar facts are the hardest to justify in a validator, because they need loop-invariant certificates.

**Proof (partial, #24):** `GoFV.Proof.ProveCheck.proveChecked_refines : proveChecked penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → RefinesUnder Env.Mono out.tables out.func penv.tables f` (`GoFV/Proof/Pass/Prove.lean`). `proveChecked` (proven-only, `GoFV/Opt/ProveCheck/Check.lean`; the default `prove` pass is unchanged) runs the stock port, undoes every rewrite the validator does not re-derive on the input (`revert`) and keeps the result only if `proveRel` holds. Assumptions: path facts per dominator-tree block (an `If` control below an only-predecessor successor), `Phi` range invariants (`invOK`), and per block relations `z - y ≤ c` between a `Phi` `z` of an ancestor and a value `y` of a strict ancestor of `z`'s block, for `y ≥ 0` (`relsOK`: checked on every edge into `z`'s block, kept from the predecessor elsewhere; the frame-level invariant `Q` of `AtomSim.SrcInv`, `QRel`); checker: interval analysis over BitVec terms (`Range.lean`), comparisons decided from ranges, a fact on the same two sides, equal sides, or bounds on differences `V(x) - V(y) ≤ c` along chains of facts whose sides may carry a constant offset, with a relation as the last step, and unsigned orders between nonnegative sides in the signed reading (`linDecides`, `diffLeR`, `GoFV/Proof/ProveCheck/Lin.lean`) (`Decide.lean`), where a `SliceLen`/`StringLen`/`SliceCap` of a `SliceMake`/`StringMake` stands for its component (`canon`, `canon_den`); rewrites: branch removal, bounded shifts, signed→unsigned `Rsh`/`Div`/`Mod`, `Ctz`→`CtzNonZero`, `Mul`→`And`, `Slicemask`→const, constant-folded arguments (T3: a one-point range or a decided boolean, never a pointer word, `foldOK`). Proof: `rng_sound`, `decides_sound`, `valueOK_ref`, `fold_ref`, source invariant `proveInv` (relations: `qrel_step`, `qrel_edge`), atom simulation premises `prove_atomArgs`/`prove_steps` (`GoFV/Proof/ProveCheck/*`). Witnesses `proveChecked_witness` (a dominated `IsInBounds` removed, kernel-evaluated; the port uses `Std.TreeMap`/`TreeSet` and `PdqSort.sortBy` for that) and `proveChecked_relWitness` (the bounds check of a downward loop, decided by a relation). Acceptance (`lake exe prove-probe`) per class on #24.

**Issue summary:**
- Enabled on linux/arm64 (off with -N). About 3.5k code lines: prove.go 2362 + poset 757 + loopbce 313 + downward loop 93. It is the largest machine-independent pass.
- Traps: it reorders b.Values in every visited block (unique key, safe); siblings are visited in reverse-RPO order and that order decides branch removals and alloc IDs; it allocates (freeValues LIFO, f.constants cache, findIndVar constVal) and never frees; poset answers depend on history (noneq is not migrated on alias), so port it verbatim; unsat partway through a block kills the subtree.
- No harmful map iteration. aliasnodes' range over a map is harmless.
- External state: Config.haveCondSelect/arch/RegSize/PtrSize, type sizes/kinds/Elem, the line table (SameFileAndLine), Likely, and the cached idom/sdom/postorder.
- Difficulty XL. Recommended approach: verbatim port plus a per-rewrite validator (bv_decide over dominating conditions); T1 needs a loop proof.
- Prerequisites: dominators/sparsetree/postorder port, f.constants plus free-list modelling, the canCondSelect helper.

### divisible / divmod — issue #25

**Function / files:** `divisible` / `divmod` in `opt.go:12,16` = `applyRewrite(f, rewriteBlockdivisible, rewriteValuedivisible, removeDeadValues)` / `…divmod…`. Generated `rewritedivisible.go` (1,532 lines; ops Eq{8,16,32,64}, Neq{8,16,32,64}; `rewriteBlockdivisible` returns false, `:1530`) from `_gen/divisible.rules` (167 lines, 20 `=>` rules); `rewritedivmod.go` (923 lines; ops Div{8,16,32,64}[u]; `rewriteBlockdivmod` returns false, `:921`) from `_gen/divmod.rules` (235 lines, 29 rules). Magic-number helpers `magic.go` (426 lines; `umagic`, `smagic`, `udivisible`, `sdivisible` and `*OK` predicates, `math/big`), `isPowerOfTwo`, `log8..64` in `rewrite.go`.
**Position & ordering:** `divisible` idx 14 (`compile.go:472`), `divmod` idx 15 (:473), both `required: true`. passOrder: `{"prove","divisible"}` (:542), `{"divisible","divmod"}` (:544), `{"divmod","decompose builtin"}` (:546).
**Enabled (linux/arm64, default build):** yes, also under -N (required; prove does not run then). Conditions read `config.RegSize` (=8 on arm64; selects case 1/5/6/7/8 variants, `rewritedivmod.go` 28 uses). No pass-name or flag dependence.
**Size:** generated 1,532 + 923 lines (1,433 + 833 non-comment); rules 20 + 29; `magic.go` 426 (149 non-comment). Driver shared with #7 (`applyRewrite`).
**What it does:** same `applyRewrite` fixpoint/cleanup as #7 (all driver traps apply) with tiny rule sets.
- divisible: matches the form produced by opt (`x%c==0` → `Eq x (Mul (Div x c) c)`, `_gen/divisible.rules:5-9`; opt rules `_gen/generic.rules:1155-1178`). Power-of-two c → `Eq (And x (c-1)) 0`; otherwise, when `div.Uses == 1`, unsigned → `Leq{N}U (RotateLeft (Mul x m) (N-k)) max` using `udivisible{N}(c)`, signed → adds `a` offset with `sdivisible{N}(c)`.
- divmod: signed Div by 2^k → shift/add sequence; non-power-of-two Div/Divu → 8 strength-reduction cases (`_gen/divmod.rules:51-84`) using `smagic`/`umagic`; case 4 (`Div{16,32,64}u` with `t.IsSigned()`, `:134-151`) relies on prove having converted a signed Div to `Div*u` while keeping the signed result type (prove table `prove.go:2664-2666`). Mod is not handled here (opt already rewrote Mod to Sub/Mul/Div); unsigned Div by 2^k handled by generic rules.
**Data structures:** none beyond the driver; magic computations use `math/big` (pure).
**Parity traps (order dependence / nondeterminism):** all #7 driver traps (f.Blocks×b.Values order, snapshot length, preorder allocation from inherited free list — results allocate up to ~6 new values each, fresh constants not via f.constants, final free order, IsStmt propagation to new values). Specific: `div.Uses == 1` conditions in divisible (count must be exact after opt/prove/cse); rule order within an op (e.g. Div32u case 4 before 5/6/7/8) and the `x.Op != OpConst64` test used for *all* widths in the power-of-two divisible rules (`_gen/divisible.rules:16-27`, bug-compatible); RegSize-dependent rule selection. No maps, sorts, or aux identity.
**External state read:** `Config.RegSize`, `Config.Types` (typ.UInt32/UInt64/…), value types (`t.IsSigned()`, sizes). No fe/LSym/base reads.
**Depends on:** opt's Mod/Eq normalisations; prove's signed→unsigned Div conversion preserving signed type (case 4); must precede `decompose builtin` (64-bit ops on 32-bit); `middle opt` (idx 16) cleans up (e.g. Mul by 2^k → shift now enabled since pass.name ≠ "opt").
**Proof strategy & difficulty:** M (port) / L (proof). Port reuses #7's driver + rule interpreter. Each rule needs a magic-number correctness theorem: for 8/16-bit widths `bv_decide`/exhaustive check over all c is feasible; for 32/64 need the Granlund–Montgomery / Lemire lemmas over `umagic`/`smagic`/`udivisible`/`sdivisible` (port `magic.go` as pure Nat/Int functions and prove their spec once). Case 4 additionally needs the prove-established range fact (x < 2^(N-1)) which must be justified from the signed type tag — an invariant to state explicitly.

**Proof (done for the proven rules, #113):** translation validation. `optChecked` (and `divisibleChecked`/`divmodChecked`) = `checkedRewrite` with the proven rule set (`GoFV.Rules.Proven`): the rewrite log is replayed by `RewriteCheck.validate` or the input is returned. `GoFV.Proof.Pass.Rewrite.opt_refines` / `divisible_refines` / `divmod_refines` (`RefinesFrom (RwPre penv.tables f)`: monotone contracts, malloc-family contracts that return non-nil pointers, non-nil dictionary arguments, the runtime's `memclrNoHeapPointers`/`memmove` contracts if present, #151; from `checkedRewrite_refines (hs : s.AllSound)`: validator soundness `validate_termRef` + atom simulation `AtomSim.atomSim_refines`), witness `addZero_refines` (hand-written `0 + n`, kernel-evaluated). Coverage and rejection numbers: docs/proofs/rules.md, "Proven-only rewrite passes".
**Issue summary:** Required x2 (run even at -N), idx 14/15; 49 rules, 2.5k generated LOC + magic.go 426. Same applyRewrite traps as #7 plus div.Uses==1 sensitivity and RegSize-dependent case choice. External: Config.RegSize/Types only. Deps: opt Mod→Div rewrites, prove's signed-typed Div*u (case 4). Difficulty M port / L proof (magic-number lemmas).

### known bits — issue #26

**Function / files:** `knownBits` in `known_bits.go:160-218`; `knownBitsState.fold` (:12-158), `isLiveInEdge/isLiveOutEdge` (:248-269), `computeKnownBitsForShift` (:300-334), `allPossibleValues` (:340-359). Uses `f.postorder()`, `f.ConstBool/ConstInt8/16/32/64` (`func.go:663`), `Value.copyOf`, `f.Cache.allocKnownBitsEntriesSlice/allocBitset`.
**Position & ordering:** idx 17 (`compile.go:475`), not required. passOrder: `{"known bits","lower"}` (:608), `{"known bits","late opt"}` (:610), `{"prove","known bits"}` (:612).
**Enabled (linux/arm64, default build):** yes; disabled by -N. `f.pass.debug>0` Warnl of folded values (:188); `>1` Warnl of every lattice entry (:45). No arch/flag dependence.
**Size:** 359 lines (275 non-comment), all exclusive.
**What it does:** abstract interpretation of (value, known-mask) bit lattice, memoised by value ID. `blocks := f.postorder()`; mark them reachable; for blocks in **reverse postorder**, values in `b.Values` order, skip `Uses==0`, non-integer/non-bool types and constants; `fold(v)`: if seen return cached entry; mark seen *before* recursing (cycle cut: an in-progress value reads its zero entry = "nothing known"); transfer functions for Const, And/Or/Xor/Com/Not, Phi (meet over args on live in-edges — `BlockFirst` only edge 0 live, unreachable preds skipped; early `break` when known==0), Copy/CvtBoolToUint8/SignExt/Trunc (identity, then re-normalise), Eq/Neq (contradiction or full knowledge), ZeroExt, Lsh/Rsh/RshU (enumerate all feasible shift amounts via `allPossibleValues`, meet; `v.AuxInt` = shift-bounded flag); default unknown. Deferred normalisation: bool → bit0 only, sign-extend to 64 from `Type.Size()`, `value &= known`. If all bits known (`k == -1`): `c := f.ConstX(v.Type, val)` and `v.copyOf(c)`.
**Data structures:** `entries []knownBitsEntry` (by value ID), `seenValues` bitset, `reachableBlocks` bitset.
**Parity traps (order dependence / nondeterminism):**
- Memoised results are **visit-order dependent** in the presence of cycles (loop phis): the value first entered in a cycle is read as unknown by the others and their partially-informed results are cached. Exact order needed: reverse of `f.postorder()` (cached Func postorder algorithm), `b.Values` order, recursion order Args[0] then Args[1], phi args in order with early `break` (later args not folded/cached at that time). Results are sound either way, but folded/not-folded decisions differ.
- `Uses == 0` skip sees Uses as modified by earlier `copyOf`s in the same walk.
- Allocation: `f.ConstX` reuses a cached constant from `f.constants` (match on op + `Type.Compare`), else allocates in `f.Entry` at the end with `src.NoXPos` — IDs from the free list in visit order; new constants appended to `f.Entry.Values` are not visited (Entry is first in RPO and its range is snapshotted).
- `copyOf` sets `v.Type = c.Type` (same type, but the cached const may hold a Compare-equal *different* `*types.Type` pointer → type pointer identity of v may change).
- Positions untouched (v keeps Pos; constants NoXPos). No CFG change, no maps/sorts.
- Panics on unexpected block kinds (`isLiveOutEdge` :266) and unknown sizes — generic only.
**External state read:** `v.Type.IsInteger/IsBoolean/Size`, `f.pass.debug`, `f.constants` cache contents (persistent across passes), `f.Entry`.
**Depends on:** `f.postorder()` (cached; exact DFS order), `f.constants`; prove before (removes dead branches → BlockFirst), `late opt` after to clean up copies.
**Proof strategy & difficulty:** M. Port `fold` literally (memo + seen-before-recurse) for parity. Soundness: prove each transfer function sound for the (value,known) concretisation on BitVec (bv_decide-friendly for fixed widths), the in-progress = ⊤ invariant for cycle cuts, and phi meet over live edges (needs reachability = executed-edge over-approximation lemma). The `allPossibleValues` enumerator needs a small combinatorial lemma.
**Proof (done, #26):** `GoFV.Proof.KnownBits.knownBits_refines : knownBitsPass penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → RefinesUnder Env.Mono out.tables out.func penv.tables f`. `knownBitsPass` is validated: `knownBitsWith` also returns the final entries `E` and reachable blocks `R`; checker `KnownBits.kbOK` (`GoFV/Opt/KnownBitsCheck.lean`) on `BitVec 64` entries: `R` closed under the successors a terminator can take (`First`: 0 only), `E` a post-fixpoint of the transfer functions (Phi over live in-edges only; shifts against every feasible effective amount), each changed value `Copy c` of an entry constant of its fully known value, same blocks/kinds/successors/controls/atoms. Proof: the atom simulation under the source invariant `kbInv` (registers have the bits their entries claim; `KnownBitsInv`), atoms' arguments and terminators by `kb_ref` (`KnownBitsTerm`); transfer soundness in `KnownBitsCore/Domain/Kind/Shift` by kernel bit proofs (`kb_bits`, no `bv_decide`). Witness `knownBits_witness` (`GoFV/Proof/Witness/KnownBits.lean`, `sort.isNaN[go.shape.string]`). Probe `knownbits-probe`: 0 rejections (quick); parity 100% quick and full.
**Issue summary:** Enabled (off at -N), idx 17, 359 LOC (275 non-comment). Traps: memoisation with seen-before-recurse makes results depend on RPO/b.Values/arg order; const allocation via f.constants into f.Entry in visit order (free-list IDs, NoXPos). External: types only + persistent f.constants. Deps: f.postorder(), f.constants. Difficulty M.

### early fuse / late fuse — issue #27

**Function / files:** `fuseEarly` / `fuseLate` in `fuse.go:13,18` → `fuse(f, typ)` (`fuse.go:33-66`); `fuseBlockIf` (:86-171), `isEmpty` (:175), `fuseBlockPlain` (:189-343); `fuse_comparisons.go`: `fuseIntInRange`/`fuseNanCheck`/`fuseSingleBitDifference` → `fuseComparisons` (:56-115) with predicates `canOptIntInRange` (:153), `canOptNanCheck` (:192), `canOptSingleBitDifference` (:248); `fuse_branchredirect.go`: `fuseBranchRedirect` (:29-112). Shared helpers: `canSpeculativelyExecute`/`isDivMod`/`isPtrArithmetic` (`branchelim.go:433-463`), `Block.removeEdge` (`deadcode.go:311`), `removePred`/`removeSucc`/`removePhiArg` (`block.go:287,305,357`; `removePhiArg` calls `phielimValue`), prove's `newFactsTable`/`checkpoint`/`restore`/`cleanup`/`addBranchRestrictions` (`prove.go:554,1267,1280,1357,2261`), `oneBit` (`rewrite.go:504`). `fuseTypeShortCircuit`/`shortcircuitBlock` is only used by the shortcircuit pass (`shortcircuit.go:61`), out of scope.
**Position & ordering:** `early fuse` idx 18 (`compile.go:476`), `late fuse` idx 27 (:485); both not required. passOrder: `{"nilcheckelim","late fuse"}` (:555), `{"late fuse","memcombine"}` (:598); none for early fuse.
**Enabled (linux/arm64, default build):** yes; both disabled by -N. fuseEarly = Plain|IntInRange|SingleBitDifference|NanCheck (`fuse.go:14`; doc comment at :12 omits SingleBitDifference); fuseLate = Plain|If|BranchRedirect (:18). `f.pass.debug>0` only Warnl in branch redirect (`fuse_branchredirect.go:95`).
**Size:** `fuse.go` 343 (243 non-comment), `fuse_comparisons.go` 276 (165), `fuse_branchredirect.go` 112 (73) — 731 lines total, exclusive. Shared: canSpeculativelyExecute (~30), edge helpers (~80), prove factsTable/poset (large, owned by prove issue).
**What it does:** fixpoint `for changed` (`fuse.go:34-65`): iterate `f.Blocks` **backwards** by index; per block apply, in this order and each to the same `b`: If, IntInRange, SingleBitDifference, NanCheck, Plain (subset per typ); after the sweep, BranchRedirect (late only); `f.invalidateCFG()` if changed.
- `fuseBlockIf` (late): `If` block whose successors are (possibly) empty Plain blocks converging on the same `ss` (4 shapes) and all *used* phis in `ss` agree on the two incoming args → `b.removeEdge(0)`; if s0 became pred-less: `s0.removeEdge(0)`, move s0's (dead) values to the end of b, mark s0 `BlockInvalid` (Values/Succs/Preds nil); b becomes Plain, `Likely=Unknown`, controls reset; then LIFO worklist resets dead removeable values of b (and transitively their args) to `OpInvalid` (left in place).
- `fuseComparisons` (early): b `If` with single pred p `If`, not bypassed per `p.Likely`, sharing true (→`OrB`) or false (→`AndB`) successor, predicate true and `canSpeculativelyExecute(b)` → new value `op(pc, bc)` at `bc.Pos` appended to b, `b.SetControl(v)`, `p.removeEdge(i)`, p → Plain, Likely Unknown, controls reset.
- `fuseBlockPlain`: maximal run b…c of Plain blocks with single-pred interiors (cycle-safe); move end-of-block stmt marks forward (to first same-line value in the next block or to its `Pos`); concatenate Values of b..c in run order into c (storage reuse only affects aliasing); c.Preds := b.Preds (order kept), fix preds' Succs; `f.Entry = c` if b was entry; trash b..(c exclusive): `BlockInvalid`, Values/Preds/Succs nil.
- `fuseBranchRedirect` (late): new factsTable; for `If` blocks b (backwards) that contain only their control (Uses==1) or nothing: for each pred `k` that is `If`: assume p→b branch, for each b branch (pos, neg) check `ft.unsat` under checkpoint/restore; if a branch is impossible redirect p directly to the other successor `child` (skip if child==b): `b.removePred(k)` (swap-with-last), `removePhiArg` on b's phis (swap-with-last + phielimValue), `p.Succs[pk.i] = {child, len(child.Preds)}`, append pred to child and `AddArg(v.Args[ai])` to child's phis, `k--`. Pred-less non-entry b → `Kind = BlockInvalid` (succs/controls/values left intact).
**Data structures:** `walkValues` stack; prove `factsTable` (posets orderS/orderU, limits slice, `orderings map[ID]*ordering`, checkpoint stacks).
**Parity traps (order dependence / nondeterminism):**
- Backward `f.Blocks` index order, the fixed per-block sub-transformation order, and repeated rounds; transformations invalidate other blocks mid-sweep (Invalid blocks are skipped by Kind checks).
- Edge removal uses swap-with-last on Succs/Preds and phi args (`block.go:289-296,306-314,362-365`) — successor/pred/phi-arg order after fuse is order-dependent; `removePhiArg` may turn phis into Copies.
- Blocks are never freed (no `freeBlock`, no `NewBlock`): dead blocks stay in `f.Blocks` as `BlockInvalid` until the next deadcode (after early fuse: through expand calls … sccp until `generic deadcode` idx 26; after late fuse: through check bce, dse, memcombine, writebarrier, lower… until `lowered deadcode for cse`). `f.Entry` may differ from `f.Blocks[0]`. fuseBranchRedirect's invalid blocks keep Succs/Controls/Values (asymmetric with fuseBlockPlain's trashing).
- Values: `fuseComparisons` allocates one value (free-list ID) per success; `fuseBlockIf` leaves `OpInvalid` values in `b.Values` (freed by the next applyRewrite/deadcode); merged block value order = concatenation in run order (the capacity-dependent storage choice at `fuse.go:283-301` does not change logical order).
- Positions: stmt-mark migration in fuseBlockPlain (`fuse.go:229-256`) depends on `b_next.Values` order and lines; new OrB/AndB value takes `bc.Pos` incl. IsStmt.
- `b.Likely` reset to `BranchUnknown` on p/b; fuseComparisons reads `p.Likely`.
- fuseBranchRedirect: result depends on prove's factsTable precision (posets + limits + `orderings` map; whether any map iteration there matters is a prove-issue question) — must reuse the exact prove port.
- `isEmpty`/`canSpeculativelyExecute` read `v.Uses`, op flags (IsCall, HasSideEffects, nilCheck), memory args.
**External state read:** op table flags (`opcodeTable[...].nilCheck/hasSideEffects`, `IsCall`), value types (IsMemory, IsVoid), `f.Entry`, `f.pass.debug`; branch redirect: whatever prove's factsTable reads (`initLimit` on all values: constants, types, sizes). No Config/fe/base reads.
**Depends on:** prove's factsTable (`prove.go`) for late fuse; `canSpeculativelyExecute` (branchelim.go); nilcheckelim before late fuse (creates plain chains); later deadcode to remove Invalid blocks/values; `memcombine` after late fuse.
**Proof strategy & difficulty:** L. Plain fusion, If-fusion and comparison fusion are local CFG simulations (block merging = stuttering simulation; If-fusion needs the phi-agreement lemma; comparison fusion needs "b speculatively executable ⇒ no observable effect/panic" plus OrB/AndB equivalence). Branch redirect is best done as untrusted (prove-shared factsTable) + a validator that re-checks each redirected edge's infeasibility with a proven decision procedure, or by reusing the prove soundness proof. L because of CFG surgery with swap-order edges, Invalid-block lingering, and the prove dependency.
**Proof (partial, #27):** plain fusion is done. `fuseBlockPlain` runs checked in early fuse, late fuse and short circuit (`Fuse.Plain.fuseBlockPlainChecked`, `GoFV/Opt/Fuse/PlainCheck.lean`): a pre-check and snapshot of `f` (`Plain.snapOf`: the run `b₀ … c` is linked alone, later blocks are not the entry and hold no `Phi`/parameter read, no value reads a later block's value; the run's values, `b₀`'s predecessors, `c` and the run's non-pure node sequence), the rewrite in place, and a check of the changed entries against the snapshot (`Plain.postOK`: `c` holds the run's values with `c`'s terminator and redirected successors, the non-pure nodes keep their per-block order in `c`'s schedule, the predecessors are redirected, the other run blocks emptied); a proven frame lemma (`fuseRun_frame`) covers every other entry, so the check costs about the run's size (#147). A skipped rewrite leaves `f`; a rejected one is an error and the pass returns its input (`Fuse.orInput`). `GoFV.Proof.FusePlain.fuseBlockPlainChecked_refines` (`GoFV/Proof/Pass/FusePlain*.lean`, macro-step simulation: the source runs the k blocks of the run, the target the fused block once), witness `fusePlain_witness` (3-block chain). `lake exe fuse-probe`: no rejection on quick-v1 and full-v2. **Early fuse is proven:** comparison fusion runs checked too (`Fuse.Cmp.fuseComparisonsChecked`, `GoFV/Opt/Fuse/ComparisonsCheck.lean`: a local checker with no `check` of the result: `p`, `b` and the shared successor `s` have the fused shape, `b`'s values are speculation-safe, the new `OrB`/`AndB` of the two (non-`Phi`, same-typed) controls is a free ID in `b`, `s`'s `Phi`s agree along `p`'s and `b`'s edges and lose `p`'s argument by swap-removal, the touched block entries are as expected and every other table entry is unchanged, compared pointer-first); `GoFV.Proof.FuseCmp.fuseComparisonsChecked_refines` (`GoFV/Proof/Pass/FuseCmp*.lean`; WF and use dominance of the result from the step relation, `FuseCmpPres`), the generic driver lemma `GoFV.Proof.Fuse.fuseLoop_refines` (`FuseLoop.lean`, any step of the checked-step shape, also for late fuse and short circuit) and `GoFV.Proof.FuseEarly.fuseEarly_refines` (the pass `check`s its input once), witness `fuseEarly_witness` (`0 <= a && a < 10`). If-fusion and branch redirect (late fuse) are not yet checked (plan on #27).
**Late fuse is proven (#27):** the pass checks its input once (`wfDomOK`), `fuseBlockIf` runs checked (`fuseBlockIfChecked_refines`), and every branch redirect is validated (`Fuse.fuseBranchRedirectChecked`, `GoFV/Opt/Fuse/BranchRedirectCheck.lean`): prove's validator decides `b`'s control under `p`'s branch fact (`ProveCheck.decides`, plus a signed range test for equalities and ranges of narrow values through their zero extensions), the term nodes it reads are listed in dependency order, `b` holds at most its unread control, and the result's table entries are the redirect's; no `check` of the result (WF and use dominance from the relation, `FuseRedirectPres`). `GoFV.Proof.FuseRedirect.fuseBranchRedirectChecked_ok` (`GoFV/Proof/Pass/FuseRedirect*.lean`: macro-step simulation, the source runs `p → b → child`, the target `p → child`), `GoFV.Proof.FuseLate.lateStep_ok`, `GoFV.Proof.FuseLate.fuseLate_refines` via `Fuse.fuseLoop_refinesAt`; witness `fuseLate_witness` (`a < 5` decides `a < 10`). `fuse-probe --late`: 0 rejected redirects on quick-v3 and full-v4.
**Issue summary:** Enabled (off at -N), idx 18/27; 731 LOC exclusive (fuse.go 343, comparisons 276, branchredirect 112). Traps: backward f.Blocks sweep with ordered sub-transforms, swap-with-last edge/phi-arg removal, Invalid blocks left in f.Blocks (Entry may move), stmt-mark migration, one new value per comparison fusion. External: op flags only; late fuse depends on prove's factsTable. Difficulty L; prerequisite: prove port (factsTable/poset), branchelim's canSpeculativelyExecute.

### expand calls — issue #28
**Function / files:** `expandCalls` in `SSA/expand_calls.go:21-218`. Exclusive helpers, same file: `rewriteFuncResults` (:220-268), `rewriteCallArgs` (:270-336), `decomposePair`/`decomposeOne` (:338-352), `decomposeAsNecessary` (:362-476), `rewriteSelectOrArg` (:491-700), `rewriteWideSelectToStores` (:706-801), `isBlockMultiValueExit` (:803), `registerCursor` (:807-879), `selKey`/`expandState` (:891-915), `offsetFrom` (:918-938), `prAssignForArg` (:941), `(*expandState).invalidateRecursively` (:973). `postExpandCallsDecompose` (:16-19) belongs to the *next* pass ("decompose builtin"). Shared helpers it calls: `ParamAssignmentForArgName` (:949, also used by ssagen `ssa.go:502`), `ArgOpAndRegisterFor` (:883, also used by `debug.go:483` and ssagen `ssa.go:630`), `AuxCall` accessors (`op.go:121-297`), `abi.RegisterTypes`/`appendParamTypes` (`abi/abiutils.go:118-192`), `ABIConfig.FloatIndexFor`/`NumParamRegs` (`abiutils.go:296-309`), `ABIParamAssignment.FrameOffset` (`abiutils.go:249`), `Value.invalidateRecursively` (`value.go:400`), `copyOf` (`value.go:429`), `resetArgs` (`value.go:367`), `f.ConstOffPtrSP` (`func.go:739`, constants cache), `f.spSb` (`func.go:826`), `CanSSA` (`value.go:620`), `types.NewPtr`/`NewResults`.
**Position & ordering:** index 19 in `passes` (`compile.go:477`), `required: true`. passOrder: `{"expand calls","decompose builtin"}` (`compile.go:564`). Runs after "early fuse", before "decompose builtin" (which re-runs `decomposeUser`+`decomposeBuiltin` to clean up the `*Make`/`*Select` values this pass creates).
**Enabled (linux/arm64, default build):** yes, always (required, so also under -N). Behaviour depends on: `Config.RegSize`=8 and `BigEndian`=false on arm64 (`config.go:228-248`; the Int64Hi/Lo split paths `:43-53,450-457,613-638` are dead on 64-bit); `Config.SoftFloat` (false by default; if set, `floatParamRegs=nil`, `config.go:383-385`, so ABI1 has 0 float regs); regabi is always on for arm64 (`internal/buildcfg/exp.go:65-67,141-144`) so `ABI1 = NewABIConfig(16, 16, FixedFrameSize=8, 1)` (`config.go:388`, `opGen.go:116437-116438`, `cmd/internal/sys/arch.go:136`). `x.debug = f.pass.debug` only adds `Printf` output (`:260,316,975-988`). SIMD struct paths (`at.IsSIMD()`, `:401,553,722`) unreachable with SIMD experiment off.
**Size:** `expand_calls.go` 989 lines total; pass proper ≈ :21-989 = 969 lines (~35 of which are debug printing). ABI data model needed from `abi/abiutils.go` (681 lines): accessors :29-113, `RegisterTypes`/`appendParamTypes` :118-192, `FrameOffset` :249-258, `FloatIndexFor`/`NumParamRegs` :296-309 (≈170 lines). The register *assignment* algorithm itself (`ABIAnalyze*`, `assignParam`, `tryAllocRegs`, :315-655) is NOT run by this pass — its result arrives precomputed in each `AuxCall.abiInfo` and `f.OwnAux`.
**What it does:**
1. Scan `f.Blocks`×`b.Values` once (:67-119), collecting in encounter order: `m0` (InitMem), `calls` (Static/Closure/Inter/Tail/TailInter `LECall`), `args` (`OpArg`), `selects` (non-mem `OpSelectN`), `exitBlocks` (Ret/RetJmp whose control is `OpMakeResult`, :803). In the same scan: Store whose `Args[1]` is a non-SSAable SelectN is recorded in `wideSelects` (panics if that SelectN has >1 use); a mem-typed `SelectN` gets `AuxInt := abiInfo.OutRegistersUsed()` in place and is recorded in `memForCall[call.ID]` (panic on a second one); `OpSelectNAddr` becomes `Copy(offsetFrom(Entry, SP, OffsetOfResult(which)))` (:104-110).
2. Args (:122-134): for each `OpArg v`, find its `ABIParamAssignment` in `f.OwnAux.abiInfo.InParams()` by `ir.Name` pointer (:949-957). `auxBase = offsetFrom(Entry, SP, off, NewPtr(v.Type))` is computed unconditionally (off = `FrameOffset` if stack-passed, else 0) — so a `ConstOffPtrSP` lookup/allocation happens even for register args. Then `rewriteSelectOrArg(f.Entry.Pos, f.Entry, v, v, m0, v.Type, rc)`: recursively decomposes the type (array → `ArrayMake1`, struct → `StructMake`, slice/string/interface/complex → `SliceMake`/`StringMake`/`IMake`/`ComplexMake`) building children first (fresh `NewValue0` in `f.Entry`) and overwriting the outer value `a` in place (`makeOf`, :498-509: resetArgs, Aux/AuxInt cleared, Pos/Op/Type overwritten). Leaves: register-assigned → `OpArgIntReg` (AuxInt = abi RegIndex) or `OpArgFloatReg` (AuxInt = RegIndex − #intRegs, :883-889), `Aux = &AuxNameOffset{name, offset}` (fresh heap object, :651); stack-assigned → `OpArg` with `AuxInt = container.AuxInt + offset` (new value in `container.Block`, or the original kept when it is the outermost). Zero-size → `OpEmpty`; mem → copyOf(m0).
3. Selects (:137-185): ensure a mem selector exists for the call (create `SelectN [OutRegistersUsed] call` at `call.Pos` in `call.Block` if absent, :146). If the select feeds a recorded wide Store: register results → `rewriteWideSelectToStores` emits per-leaf `SelectN [reg]` + `OffPtr`+`Store` chains into `call.Block` and the Store becomes `Copy(lastMem)`; stack results → the Store is replaced by `Copy(Move dst, OffPtr(SP, OffsetOfResult), mem)` (`Move` allocated in `store.Block` at `store.Pos`). Otherwise `rewriteSelectOrArg(call.Pos, call.Block, v, v, mem, …)` with leaves `SelectN [firstReg+nextSlice] call` (register index = sum of `len(Registers)` of earlier OutParams + cursor slice, :682-688) or `Load(OffPtr(SP, off+OffsetOfResult), mem)`.
4. Calls (:187-209): `rewriteCallArgs(v, argStart)` with `argStart` = 0 (Static/Tail), 1 (Inter/TailInter), 2 (Closure). For each actual arg (in order): `OpDereference` is retyped to `OpLoad`; tail-call self-copy of an incoming `PPARAM` at identical offset is skipped (:308-315, uses `ir.Name.FrameOffset()` + `Arch.FixedFrameSize`); `decomposeAsNecessary` (pre-order: emits `ArraySelect`/`StructSelect`/`SlicePtr|Len|Cap`/`StringPtr|Len`/`ITab`+`IData` (IMake data shortcut :428-441)/`ComplexReal|Imag` then recurses); leaves go either to the register list (`rc.addArg`) or become `Store` to `OffPtr(SP|GetCallerSP, off)` threaded on mem; non-SSAable aggregates with no regs must be `Load`s and become one `Move` (:375-387, panic otherwise). New args = preArgs ++ register leaves ++ final mem; old args left with 0 uses are `invalidateRecursively`'d (become `OpInvalid`, NOT freed). Then `v.Op` := `StaticCall`/`TailCall`/`TailCallInter`/`ClosureCall`/`InterCall`, `v.Type := NewResults(RegisterTypes(OutParams) ++ [mem])`. Tail calls first allocate `GetCallerSP` at `src.NoXPos` (:288).
5. Exits (:212-216): `rewriteFuncResults` with `f.OwnAux`: per result `i` it first allocates `LocalAddr {NameOfResult(i)} SP mem` (unconditionally, even if register-returned or self-move, :237), skips stack self-moves `Load(LocalAddr{same Name})`, decomposes the rest like call args; MakeResult args := register leaves ++ mem; re-types control to `NewResults(...)`; `b.SetControl(v)`.
**Data structures:** `expandState` with four Go maps — `wideSelects map[*Value]*Value`, `commonSelectors`/`commonArgs map[selKey]*Value` (key = {from *Value, offsetOrIndex, size, typ *types.Type}), `memForCall map[ID]*Value` — all used for lookup only, never iterated. `registerCursor` value type (`storeDest`, `storeOffset`, `regs []abi.RegIndex`, `nextSlice`, `config`, `regValues *[]*Value`); `next(t)` aligns `storeOffset` to `t.Alignment()`, advances by size and by `NumParamRegs(t)` regs (:841-850). Lists `selects`, `calls`, `args`, `exitBlocks` in f.Blocks/b.Values order.
**Parity traps (order dependence / nondeterminism):**
- Value allocation order is the whole game: fixed phase order args → selects → calls → exits, each list in f.Blocks×b.Values encounter order; within `rewriteSelectOrArg` children are allocated before the (reused) parent; within `decomposeAsNecessary` selector before recursion (pre-order). All `NewValue*` pop `f.freeValues` first (IDs freed by earlier deadcode passes are reused LIFO).
- Hidden allocations even when the result is dead: `ConstOffPtrSP` for every `OpArg` (:131) and for every `offsetFrom(…, SP, …)`; `LocalAddr` for every function result (:237); mem `SelectN` when a call has no mem selector (:146). The `ConstOffPtrSP` cache key is `(OpOffPtr, auxint=offset)` with structural `Type.Compare` (`func.go:663-685`), so a hit depends on whether a pointer type comparing CMPeq was cached earlier in this or any prior pass; new consts go into `f.Entry` with `src.NoXPos` and `InCache=true`.
- `offsetFrom` folds `OffPtr` chains and returns `from` unchanged for offset 0 when pointer-ish (:918-938); new `OffPtr`s use `from.Pos.WithNotStmt()`.
- Positions: arg rewrites use `f.Entry.Pos`; select rewrites `call.Pos`; first generated piece keeps the incoming pos, subsequent pieces `pos.WithNotStmt()` (struct fields: after each field, :563); `makeOf` overwrites `a.Pos`. `invalidateRecursively` can drop is_stmt marks (only reported under debug&1).
- Map use is lookup-only ⇒ no iteration nondeterminism. `selKey.typ` is `*types.Type` pointer identity; with `types.NewPtrCacheEnabled=false` in the backend (`ssagen/ssa.go:101`, `types/type.go:619-644`) `PtrTo()` may mint fresh type objects. [INFERENCE] Within one container no two recursion nodes share (offset, type) (zero-size types return before the lookup, :511), so `commonSelectors`/`commonArgs` effectively never hit; the port may model them as write-only but should state this as a lemma or use type identity.
- Fresh Aux objects: each `OpArgIntReg/FloatReg` gets a new `*AuxNameOffset` (:651); `rewriteCall` mints a new results `Type`. Later passes compare Aux by pointer (`cse.go:447-454`), so Aux identity created here must be modelled (e.g., an allocation counter), not structural equality.
- `b.Values` order: new values are appended to the target block (`f.Entry`, `call.Block`, `store.Block`, exit block, `container.Block`); nothing is reordered or freed.
- Panics (wide SelectN double use, two mem selectors, "Store of not a load", too many fields) are compile failures; the port may treat them as "pass fails".
**External state read:** `f.OwnAux` (`*AuxCall`, set at `ssagen/ssa.go:492` from `ABISelf.ABIAnalyze(fn.Type(), true)` :460); every call's `Aux.(*AuxCall)`; `Config.RegSize`, `Config.BigEndian`, `Config.Types` (Int, Uintptr, BytePtr, Float32/64, Int32/UInt32), `Config.ctxt.Arch.FixedFrameSize` (=8); types queries: `Size`, `Alignment`, `Kind`, `NumElem`, `Elem`, `NumFields`, `Field(i).Type`, `IsSIMD`, `IsPtr`/`IsUnsafePtr`, `Registers()` (via `NumParamRegs`), `IsDirectIface`, `CanSSA` (`MaxStruct`, `PtrSize`), `types.RoundUp`; `ir.Name` identity, `Class == PPARAM`, `FrameOffset()`; `f.pass.debug`; `base.Ctxt.Pkgpath` (debug only).
- **What the exporter must carry per `AuxCall`:** `Fn` (LSym name, nil for closure/interface), object identity, and the full `abiInfo`: `inparams`/`outparams` each with `Type`, `Name` (`*ir.Name` identity, nil for runtime calls), `Registers []RegIndex`, `offset` (int32; −1 if none); `offsetToSpillArea`, `spillAreaSize`, `inRegistersUsed`, `outRegistersUsed`; `config` (`offsetForLocals`=8, `regAmounts`={16,16}, `which`). Same for `f.OwnAux`, with outparam `Name`s identical (pointer) to the `ir.Name`s used as `LocalAddr` Aux in the function (self-move test :248). `reg *regInfo` is not needed until regalloc.
**Depends on:** invariants from ssagen (`LECall` args are actual parameters ++ mem; `MakeResult` controls; aggregate OpArgs; non-SSAable values reach calls only as `Load`/`Dereference`); `f.spSb()` finds/creates SP/SB in Entry; no prior analysis caches. Output invariant consumed by "decompose builtin"/"late opt" (dead `*Select`/`*Make` cleaned there) and by regalloc (`ArgIntReg`/`SelectN` register numbering).
**Proof strategy & difficulty:** untrusted-free direct port is feasible (no sorts, no map iteration), but the semantics change level: pre-pass calls are "aggregate value" calls, post-pass are ABI-level (register list + stack slots relative to SP). Simulation needs a calling-convention relation (registers/stack arg area ↔ aggregate values, per `abiInfo`) and a memory model for the outgoing-arg area. A validator alternative: check each rewritten call/arg/result against `abiInfo` (leaf ordering = `appendParamTypes` order, register numbering, stack offsets = `appendParamOffsets`). Difficulty **L (port) / XL (proof)**: ~1k lines of type-directed recursion with exact allocation order, plus an ABI-level semantics that no earlier pass needs.
**Issue summary:** Enabled always (required, also -N); arm64 regabi ABI1 = 16 int + 16 float regs, FixedFrameSize 8. ~970 LOC + ~170 LOC of abi data accessors. Traps: exact allocation order (args→selects→calls→exits, children-before-parent), hidden dead allocations (ConstOffPtrSP per arg, LocalAddr per result), fresh `AuxNameOffset`/results-type identity, constants-cache hits, Pos/NotStmt rules; maps are lookup-only. External: full `AuxCall.abiInfo` for every call and `f.OwnAux`, `ir.Name` identity/Class/FrameOffset, type layout queries. Difficulty L port / XL proof (needs ABI-level call semantics). Prereq: exporter carries ABI info + Aux identity.
**Proof (done on a fragment, #28):** `GoFV.Proof.EC.expandCalls_refines : expandCallsPass penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → expandCallsFrag penv f = true → RefinesUnder Env.Mono out.tables out.func penv.tables f` (`GoFV/Proof/Pass/ECMain.lean`), witness `GoFV.Proof.Witness.expandCalls_witness` on `examples/generics/main/sumOf[int]` (one `StaticLECall` with a slice argument; kernel-evaluated, which is why the pass state uses `Std.TreeMap` and parses its config on characters). The fragment `expandCallsFrag` = the output tables agree with the input's on `f` (`tabsAgree`) and the Bool checker `ECCheck.ecCheck` (`GoFV/Opt/ExpandCallsCheck.lean`) accepts the output: same CFG, kinds, controls; every source value in the same block, classified as identity, `Arg` Make-tree over parameter pieces, call with selector-chain (or `IMake` data shortcut) register pieces and stack-assigned arguments stored by a chain of new `Store`s into the outgoing-arguments area (`stackOK`: one store per leaf slot at `OffPtr [off] SP`, disjoint slots, stored values selector chains of the Go arguments; the chain may end at a new `Move [size] (OffPtr [off] SP) src mem` on the call's memory that copies a wide argument `Dereference src mem` of the first stack parameter, `moveOK`, the `Dereference` scheduled before the call, `beforeB`), call-result Make-tree over `SelectN`s (a stack-assigned call result: over `Load`s of its leaf slots `OffPtr [off + o] SP` from the call's memory, `stkLeavesOK`, the slots disjoint inside the area, `outsOK`), `MakeResult` of pieces, or invalidated (no node of the target block reads an invalidated value); the same non-pure schedule; argument reachability (a moved `Dereference` instead pure with its node arguments reaching the call, `throughB`); new values pure/frame/parameter pieces, or stack-argument stores and `Move`s with no source non-pure node between them and their call (`gapOK`), with new arguments in their block, the entry or a strict dominator (`placedSDom`, `(DomCert.make g).anc` computed once); tail calls (`TailLECall*`, stuck in the source) and values reading them accepted with any target node. Semantics: `callOp` is `stuck` in both forms unless the call's stack-argument slots are writable (`outargsOK`, semantics.md §9.3; `sem-difftest corpus 20 1` on quick-v3: 0 differ). Proof: a conversion simulation (`ECRel` `CvRel`/`Obl`, `ECLoop`/`ECOk`/`ECPanic`/`ECSim` `cvSim_refines`): target registers refine a per-value conversion `ecCv` of the source's (identity, or the ABI register pieces `leafVals` for call tuples and `MakeResult`s, `poison` for invalidated values); the obligations per class (`ECIdent`, `ECArgSel`, `ECCall`/`ECChain`/`ECStack`, `ECObl` `eco_obl`), new values that do not always evaluate anchored at a source value (`AnchoredAt`/`NewObl`: a stack store or `Move` evaluates once the source reached its call, `ecc_storeObl`, `ecc_moveObl`), the structural fields (`ECStruct` `ecs_block`), and `Ret` outcomes related by `ecRR` (pieces retyped at the register shapes; `finish_ecRR`, with the ABI round trip `GoFV/Proof/ABI*.lean`). The stack arguments: the store chain writes the slots (`ecs_chain`), they read back (`ecs_reads`) and decode to refinements of the Go arguments (`ecs_stack_params`, `ecc_decodeArgs_mixed`), and the callee sees them poisoned (`writeAll_poison`). A wide argument copied by a `Move`: the source evaluated the `Dereference` before the call (`SrcArg`, a disjunct of `Held`; `ecs_moveArgHeld`), the call's arguments have no `poison`, so its bytes were readable at `src` in the target's refining memory too, the `Move` copies them into the slot, they read back past the later stores (`ecs_move_read`) and decode to a refinement of the argument (`ecs_move_arg`); invalidated source nodes need no `Feeds` (`transfer_rank_ex`; `CvBlock.invalid`/`invArgs`). The stack results of calls: `encodeResults` writes them into the call's result memory in both forms (`ecr_callOp_src`), they read back (`ecr_encodeResults_read`), and each target leaf loads, from a memory refining the source's, its leaf's bytes of the result's encoding (`obl_selectStack`, `ECStackRes`; `convTuple`/`leafTys` skip stack results, `regLeafVals`). Wide stores (a `Store {T} p (SelectN [i] c) mem` of a register-assigned aggregate result, which the target writes as a `Copy` of a chain of new leaf `Store`s of the pieces `SelectN [first+j] c` at `p`/`OffPtr [o] p`, `wideStoreOK`/`wideLeavesOK`; the source `SelectN`, dead in the target, is `wideSel` and converts to `poison`): the leaf writes of refinements of a value's register pieces refine the write of its encoding (`ecw_split`, `ECWide`; padding stays `poison`), the chain evaluates to their `writeAll` (`ecw_chain`), the leaf stores are anchored at the source store (`ecw_storeObl`, `ecs_wideAnchored`), and the dead `SelectN`'s arguments reach its users (`throughB`, `Feeds.through`). `lake exe expand-calls-probe`: quick corpus (quick-v3) 9070/9297 accepted (97.6%; before call-argument shapes 8990, before wide stores 8886, before stack results of calls 8717, before stack arguments 8527, quick-v1 before the target-side lemma (D) and tail calls: 8246), full corpus (full-v4) 95616/96533 (99.0%; before pointer arguments of `uintptr` parameters and `Move`d blob stack arguments 95156, before wide stores 93624, before `Move`d wide stack arguments 93485, before stack results of calls 92954, before stack arguments 92610, full-v2: 86975/96531). The `IMake` target mode accepts an argument and its data operand placed in strict dominators of the call's block (`HeldT`: lemma (D) on the target, `SimAt.dinvT`, `TgtHyp.hdinvT`). Full rejections: own stack results 619, stack result shapes (blob results read through `SelectNAddr`) and `SelectNAddr` copies about 230, a `Move` not at the bottom of the store chain 34, invalidated arguments of calls without a `Move` (reach) 29, other few (see #28). Call arguments (#28): the pre-`expand calls` call retypes its arguments at the ABI parameters' shapes (semantics.md §9.3, S5), so an `unsafe.Pointer` argument of a `uintptr` parameter whose register piece is the pointer itself (`castOK`, `piecesOK … true`) decodes to the same value (`ecc_ofPieces_ptr`, `ecc_ofPieces_arg`, `ecPieceVals`); a stack parameter may have a `movTy` shape (byte blobs inside) when a `Move` copies it (`insOK`, `storeArgsOK` keeps `wf` for stored ones; `ecs_decode_hasTy_mov`).

### softfloat — issue #29
**Function / files:** `softfloat` in `SSA/softfloat.go:12-80`. Helpers: `f.unCache` (`func.go:371`), `Value.reset` (`value.go:382`), `auxTo32F`; on 32-bit only: `decomposeBuiltin`, `applyRewrite(rewriteBlockdec64, rewriteValuedec64)`.
**Position & ordering:** index 21 (`compile.go:479`), `required: true`. passOrder `{"decompose builtin","softfloat"}` (`compile.go:568`).
**Enabled (linux/arm64, default build):** runs (required) but is a no-op: returns immediately unless `f.Config.SoftFloat` (:13). `Config.SoftFloat` comes from `ssagen.Arch.SoftFloat` (`ssagen/ssa.go:102`), which arm64's galign never sets (only arm/GOARM, mips/GOMIPS, mips64, 386 GO386=softfloat: `arm/galign.go:18`, `mips/galign.go:21`, `mips64/galign.go:21`, `x86/galign.go:25`); on arm64 it is only reachable with `-d=softfloat` (`gc/main.go:186-187`). With SoftFloat on, ssagen also emits runtime soft-float calls and ABI1 loses float regs (`config.go:383-385`) — a different pipeline input altogether.
**Size:** 80 lines (pass ≈ 68 code lines); no exclusive helpers.
**What it does:** single sweep f.Blocks×b.Values: every float-typed value is `unCache`d, then Phi/Load/Arg retyped to UInt32/UInt64; `Const32F`→`Const32` (bits), `Const64F`→`Const64`; `Neg32F/64F`→`Xor32/64` with a new `Const` mask value appended to the same block (`NewValue0`, not via the constants cache); `Round32F/64F`→`Copy`. Store/Zero/Move with float `Aux` type get integer Aux. If a 64-bit int was introduced and `RegSize==4`, re-decompose (dead on arm64).
**Data structures:** none (one bool).
**Parity traps (order dependence / nondeterminism):** new mask consts allocated in block order (free-list IDs); they bypass the constants cache and `unCache` removes the old float consts from it (affects later `Const*` hits); `range b.Values` evaluates the slice once so appended masks are not revisited. No maps/sorts.
**External state read:** `Config.SoftFloat`, `Config.RegSize`, `Config.Types`; type `IsFloat`/`Size`.
**Depends on:** must run after the last pass introducing float ops ("decompose builtin").
**Proof strategy & difficulty:** direct port + simulation with a bit-level float≡int representation lemma. **S** — trivial on arm64 (identity); if ever needed, small retyping pass.
**Issue summary:** Required but a no-op on linux/arm64 (Config.SoftFloat false; only `-d=softfloat` enables it). 80 LOC. Traps (only if enabled): unCache side effects on the constants cache, mask consts allocated outside the cache. External: Config.SoftFloat/RegSize. Difficulty S; port as identity guarded by the exported SoftFloat flag.

### branchelim — issue #30

**Function / files:** `branchelim` in `branchelim.go:22-70`. Helpers that only branchelim uses: `elimIf` (`:113-287`), `elimIfElse` (`:307-390`), `isLeafPlain` (`:290`), `clobberBlock` (`:294`), `shouldElimIfElse` (`:394`), `isDivMod`, `isPtrArithmetic`. Shared: `canCondSelect` (`:72`, also used by prove), `canSpeculativelyExecute` (`:433`, also used by fuse_comparisons.go), `isPoorStatementOp` (`numberlines.go:13`), `f.postorder()`, `newSparseSet`, `Block.CopyControls`/`ResetControls`, `Value.AddArg`, `f.invalidateCFG`.

**Position & ordering:** It is `passes[22]` (`compile.go:480`) and is not required. Constraints: branchelim < `late opt` (`:602`, because late opt turns some CondSelects into arithmetic) and branchelim < `lower` (`:604`). It runs after `softfloat` (21) and before `late opt` (23).

**Enabled (linux/arm64, default build):** Yes. `-N` turns it off. It returns immediately unless `Config.haveCondSelect`, which is true on arm64 (`config.go:248`). It is also true on amd64, ppc64, loong64 and wasm.

Arch-specific branches in `canCondSelect` and `shouldElimIfElse` are inactive on arm64:
- loong64 needs a zero constant argument;
- amd64 rejects size<2 and applies a cost model.

On arm64, `shouldElimIfElse` always returns true. It does not read `f.pass.debug` and has no Warnl.

**Size:** `branchelim.go` is 475 lines (336 code), all of it exclusive to the pass apart from `canCondSelect` and `canSpeculativelyExecute`.

**What it does:**
1. **Load-address set.** `loadAddr` is a sparseSet over value IDs.
   - Seed: `Args[0]` of `Load`/`AtomicLoad8/32/64/Ptr`/`AtomicLoadAcq32/64`, and `Args[1]` of `Move`, scanning `f.Blocks` × `b.Values`.
   - Fixpoint over `f.postorder()`, with each block's values in reverse: for each value already in the set, add its args whose type is integer, pointer or unsafe pointer. Stop when the set size stops changing.
2. **Rewrite loop.** `change := true; for change { for b in f.Blocks { change = elimIf(b) || elimIfElse(b) || change } }`. `elimIfElse` is tried only if `elimIf` fails for that `b` in that round.
3. **`elimIf(dom)`**: the one-armed diamond `dom → simple → post`, `dom → post`.
   - Requirements:
     - `dom.Kind==BlockIf` and `dom.Likely==BranchUnknown`;
     - for i = 0, then 1: `Succs[i]` is a leaf plain block (Plain with 1 pred) whose successor is `Succs[i^1]`;
     - `len(post.Preds)==2` and `post != dom`;
     - post has ≥1 Phi, and every Phi passes `canCondSelect`: not in loadAddr, size ≤ RegSize, ptr-shaped or integer;
     - `len(simple.Values) ≤ 2` and `canSpeculativelyExecute(simple)`: no Phi, no Div/Mod, no OffPtr/AddPtr/SubPtr, no memory-typed value, no `hasSideEffects`, and no memory arg except `InlMark`.
   - Rewrite:
     - Every Phi in post: `Op=OpCondSelect` (in place; same ID, Pos, Type). Swap `Args[0]`/`[1]` when `(post.Preds[0]==dom) != (dom.Succs[0]==post)` (`:163`). `AddArg(dom.Controls[0])`. CondSelect means `arg2 ? arg0 : arg1` (`_gen/genericOps.go:209`).
     - `dom.Kind=post.Kind`, `CopyControls(post)`, `dom.Aux=post.Aux`, `dom.Succs = post.Succs` (reusing dom's backing array), and retarget each successor's `Preds[e.i].b = dom`.
     - Statement-mark preservation (`:196-276`, described below).
     - `v.Block = dom` for the simple and post values.
     - `dom.Values = dom.Values ++ simple.Values ++ post.Values` (`:278-279`).
     - `clobberBlock(post)`, `clobberBlock(simple)`. clobberBlock sets Values/Preds/Succs/Aux to nil, resets controls (Uses--), sets `Likely=Unknown` and `Kind=BlockInvalid`. The blocks stay in `f.Blocks` until `generic deadcode`.
     - `f.invalidateCFG()`.
4. **`elimIfElse(b)`**: the full diamond.
   - Requirements:
     - `b.Kind==BlockIf` and `Likely==Unknown`;
     - `yes=Succs[0]` and `no=Succs[1]` are both leaf plain, each has ≤1 value, and both can be speculated;
     - they share a successor `post` with `len(post.Preds)==2` and `post!=b`;
     - post has ≥1 Phi and all of them pass `canCondSelect`;
     - `shouldElimIfElse` passes (always true on arm64).
   - Rewrite: Phis become CondSelect with swap when `post.Preds[0] != b.Succs[0]` (`:348`), then `AddArg(b.Controls[0])`. Same CFG splice. `b.Values = b.Values ++ yes ++ no ++ post` (`:379-381`). clobber yes, no and post. `invalidateCFG`. **There is no statement-mark handling in this path.**

**Data structures:**
- `loadAddr` sparseSet: used only through `add`/`contains`/`size`, never iterated.
- The cached `f.postorder()` slice, taken once before any mutation.

**Parity traps (order dependence / nondeterminism):**
- Rewrites happen in `f.Blocks` order, repeated to a fixpoint. With nested or chained diamonds the result (which merges happen, the final `b.Values` concatenation order, and which block survives) depends on that order. It is deterministic. The order of the `f.Blocks` slice itself does not change: clobbered blocks remain.
- The **`b.Values` concatenation order** is fixed: dom, simple, post / b, yes, no, post. Phi→CondSelect keeps its value ID and its position in the post sequence.
- **Likely:** the surviving block keeps `dom.Likely`, which was required to be Unknown. **`post.Likely` is dropped**, even when post is a `BlockIf` with a hint. Blocks with a Likely hint are never transformed.
- **Statement marks in `elimIf` only** (`:196-276`). The logic, in order:
  1. `findBlockPos` checks whether a stmt-marked value in the block has the same file:line as `b.Pos`.
  2. `setBlockPos` marks the first non-`isPoorStatementOp` value on the block's line.
  3. Fallback: if `dom.Pos` is not a stmt, set `dom.Pos = post.Pos`.
  4. Otherwise, if dom then has a single successor with a single pred, mark the first non-poor value of that successor **if it is on the same line**, and drop the mark either way (`postStmt=false; break` happens even without a line match: quirk at `:262-268`). If still pending, set `succ.Pos = postPos` when `succ.Pos` is not a stmt.

  This needs `SameFileAndLine` (the line table) and `IsStmt` bits.
- No allocation and no freeing of values or blocks: IDs are unaffected. `AddArg`/`CopyControls`/`ResetControls` change `Uses`.
- No map iteration and no sorting. The sparseSet is never iterated.
- `f.postorder()` comes from the cache, so it depends on cache validity. It is only used for the loadAddr fixpoint, whose result is a set: the order only affects the iteration count, not the result.

**External state read:** `Config.haveCondSelect`, `Config.arch`, `Config.RegSize`; `Type.Size`, `IsPtrShaped`, `IsInteger`, `IsPtr`, `IsUnsafePtr`, `IsMemory`; `opcodeTable[op].hasSideEffects` and `MemoryArg()` (opcode arg types); `isGenericIntConst` (loong64 only); positions (`IsStmt`, `SameFileAndLine`, `WithIsStmt`).

**Depends on:**
- postorder.
- Generic ops after `decompose builtin`/`softfloat`: no tuple Phis of oversize types reach `canCondSelect` because of the size check.
- No reliance on deadcode. It tolerates existing `BlockInvalid` blocks (Kind check fails).
- It leaves `BlockInvalid` blocks behind for `generic deadcode` (26).

**Proof strategy & difficulty:**
- **M.** Direct simulation works.
- Proof obligations:
  1. Speculative execution of ≤2 side-effect-free, non-trapping values is safe. This needs an op-semantics lemma that every op admitted by `canSpeculativelyExecute` is total and pure; issue #34950 notes CPU-feature-guarded ops are a gap.
  2. `Phi` → `CondSelect(arg0, arg1, cond)` is equivalent given the swap rule.
  3. The CFG splice preserves the successor edges and the phi-arg indices of `post.Succs` (`e.i` unchanged).
- Statement marks are debug-info only and are excluded from semantics, but must still be replicated for parity.
- A validator is unnecessary.

**Issue summary:**
- Enabled on linux/arm64 (haveCondSelect=true; off with -N). 336 code lines.
- Rewrites if/else diamonds whose Phis can become CondSelect in place. Values are concatenated in a fixed order. Merged blocks are clobbered to BlockInvalid but stay in f.Blocks.
- Traps: f.Blocks-order fixpoint; post.Likely is dropped; Likely!=Unknown blocks are skipped; stmt-mark juggling needs the line table; no ID allocation.
- External state: Config.haveCondSelect/arch/RegSize, type sizes/kinds, opcodeTable.hasSideEffects/memory arg.
- Difficulty M: direct simulation plus a purity/totality lemma for the admitted ops.
- Prerequisites: postorder, a sparse-set model (membership only).

### dead auto elim — issue #31
**Function / files:** `elimDeadAutosGeneric` in `SSA/deadstore.go:244-429`; helper `isABIInternalParam` (:495-497, shared with `elimUnreadAutos`, :433-484, which is the separate "elim unread autos" pass).
**Position & ordering:** index 24 (`compile.go:482`), not required. No passOrder entries. Runs after "late opt", before "sccp" and "generic deadcode" (which removes the address computations orphaned here).
**Enabled (linux/arm64, default build):** yes; skipped under -N (not required). No config/experiment dependence beyond `f.ABISelf`.
**Size:** 186 lines (:244-429) + 3 for `isABIInternalParam`.
**What it does:** Fixpoint (max 4 rounds, :394-416; if not converged after 4 it returns *without eliminating anything*) over f.Blocks×b.Values calling `visit`, then over `b.ControlValues()`:
- `Addr`/`LocalAddr` whose Aux is an `*ir.Name` with `Class==PAUTO` or ABIInternal `PPARAM` → `addr[v]=n`.
- `VarDef` of such a name → `elim[v]=n`; `VarLive` → `usedAdd(n)`.
- `Store/Move/Zero` whose `Args[0]` is in `addr` → `elim[v]=n`; remaining args are scanned like other values.
- Panics on any other op with a SymEffect (except `OpArg`).
- Values with `Uses==0` (and not NilCheck/call/side-effecting) or no args are ignored.
- Memory/flags/Phi/memory-arg values: each arg in `addr` marks its name used, except the source of a `Move` whose target name is not (yet) used: recorded as `move[target].Add(src)` (deferred use, propagated by `usedAdd` when the target becomes used).
- Other values propagate the first unused name among their args (`addr[v]=node`); additional distinct names are marked used.
- A control value in `addr` marks its name used.
Finally every `elim` entry whose name is not `used` is turned into `Copy(MemoryArg)` (Aux/AuxInt cleared).
**Data structures:** Go maps `addr map[*Value]*ir.Name`, `elim map[*Value]*ir.Name`, `move map[*ir.Name]ir.NameSet`; `used ir.NameSet` (`ir/node.go:417`, `map[*Name]struct{}`); recursive `usedAdd`.
**Parity traps (order dependence / nondeterminism):**
- Final loop `for v, n := range elim` (:419) iterates a map: harmless — each rewrite touches only `v` (its own Args/Op/Aux), `MemoryArg()` is read from the unmodified arg list, and use-count updates commute.
- `usedAdd` iterates `for n := range s` over a NameSet (:260): harmless — it computes the reflexive-transitive closure of `move`, independent of order; `changed` is set iff `n` was newly added, also order-independent.
- Order-dependent but deterministic: the visit order (f.Blocks, b.Values, then controls) decides whether a `Move`'s target is already `used` at the time (:339) and hence how many of the 4 rounds are needed; the 4-round cap makes the iteration count observable — the port must mirror the exact round structure.
- No allocation, no freeing (values become `Copy`, keep IDs/Pos/Block). Positions untouched (is_stmt stays on the Copy).
**External state read:** `ir.Name` pointer identity of Aux, `n.Class` (`PAUTO`, `PPARAM`), `f.ABISelf.Which() == obj.ABIInternal` (`deadstore.go:496`); opcode table properties `SymEffect`, `IsCall`, `HasSideEffects`; `Type.IsMemory/IsFlags`.
**Depends on:** values reaching it are post-"late opt"; relies on later "generic deadcode" to drop now-dead address/VarDef chains. No CFG analyses.
**Proof strategy & difficulty:** direct port (maps → finite sets keyed by Name id; mirror 4-round loop). Proof: an auto whose address never escapes into a non-store use is unobservable; simulation with a memory relation that ignores the eliminated autos' slots. Alternatively a validator: recompute "address of n only reaches Store/Move-dst/Zero/VarDef/Move-src-into-unused" and check each Copy'd store targets such an n. **M** — simple data flow but the proof needs a non-escape/unobservability argument on the memory model.
**Issue summary:** Enabled (not required; off under -N). ~190 LOC. Map iterations (elim, NameSet closure) are provably harmless; the 4-round cap makes round structure observable. No allocation/freeing. External: ir.Name identity + Class (PAUTO/PPARAM), f.ABISelf ABI, opcode SymEffect/IsCall/HasSideEffects. Difficulty M (non-escape proof). Prereq: Name identity + Class in export.

### sccp — issue #32

**Function / files:** `sccp` in `sccp.go:65-121`. Helpers that only sccp uses: `worklist` and its methods `buildDefUses` (`:252`), `addUses` (`:279`), `meet` (`:300`), `visitValue` (`:376`), `propagate` (`:501`), `replaceConst` (`:576`); also `computeLattice` (`:335`), `possibleConst` (`:150`), `isConst` (`:237`), `equals` (`:126`), `rewireSuccessor` (`:543`). Shared:
- **`rewriteValuegeneric`**, i.e. the whole generic rule set, used for constant folding;
- `f.newValue`;
- `Value.reset`/`AddArgs`;
- `Block.removeEdge` (`deadcode.go:311`) → `removeSucc`/`removePred`/`removePhiArg` (`block.go:287-370`) → `phielimValue` (`copyelim.go:123`);
- `Block.swapSuccessorsByIdx`;
- `newSparseSet`, `f.Cache.allocBoolSlice`.

**Position & ordering:** It is `passes[25]` (`compile.go:483`) and is not required. No `passOrder` constraint names sccp. Before it: `late opt` (23) and `dead auto elim` (24). After it: `generic deadcode` (26, required), which cleans up sccp's garbage.

**Enabled (linux/arm64, default build):** Yes. `-N` turns it off. There are no config, arch or GOEXPERIMENT conditions in sccp itself. Folding behaviour comes from the generic rules, which read `Config`/`Config.Types`. With `f.pass.debug>0` it emits Warnl "Replace…", "Rewire…" and a summary (`:116-120`, `:581-595`), with no SSA effect.

**Size:** `sccp.go` is 601 lines (412 code), all exclusive. The generic rewrite rules it relies on are shared with opt and are not counted.

**What it does:** Wegman–Zadeck SCCP over a 3-level lattice per value (top / constant(*Value) / bottom).
1. **`buildDefUses`.** Over `f.Blocks` × `b.Values` × `Args`, it records `defUse[arg] += val` when both are `possibleConst` and `arg != val`. Then for each block it records `defBlock[ctl] += block` for each `possibleConst` control.
2. **Main loop.** It processes the edge worklist first, then the value worklist; both are FIFO through `[1:]` slicing.
   - **Edges.** The seed is `Edge{f.Entry, 0}`. For each unvisited edge (`visited map[Edge]bool`): mark it, and mark `visitedBlock[dest]`. Visit all of dest's values on the first visit, or only its Phis on later visits. On first visit, `propagate(dest)`:
     - Exit/Ret/RetJmp/Invalid: nothing.
     - Defer: all successors.
     - First/Plain: `Succs[0]`.
     - If/JumpTable: if the condition is bottom, all successors; if constant, the single taken successor (If: `1-AuxInt`; JumpTable: `AuxInt` if in range); if top, nothing.
   - **Values.** Pop from the uses worklist (deduplicated through the `inUses` sparseSet) and `visitValue`.
3. **`visitValue`:**
   - `!possibleConst` → return.
   - Already bottom → return.
   - Otherwise compute the lattice by op:
     - Const* → itself.
     - Copy → the arg's lattice.
     - Phi → `meet` over args on visited incoming edges `Edge{val.Block, i}`.
     - The listed unary/binary ops with all-constant args → `computeLattice`. Any bottom arg gives bottom; otherwise top.
   - A deferred check: if the lattice changed (and `Fatalf` if it went up), `addUses`: enqueue non-bottom uses, and re-`propagate` visited blocks that this value controls.
4. **`computeLattice`** (`:335-374`) **allocates a temporary value** `f.newValue(val.Op, val.Type, f.Entry, val.Pos)`. This **appends it to `f.Entry.Values`** (`func.go:302`). It then calls `AddArgs(constArgs...)` and `rewriteValuegeneric(temp)`.
   - If a rule matched and the result is a Const op: the lattice is `constant(temp)`, and the temp **stays in `f.Entry.Values` as a dead Const**.
   - Otherwise: `temp.reset(OpInvalid)` and the lattice is bottom. The temp **stays in `f.Entry.Values` as an OpInvalid value**.

   Neither temp is ever freed. In practice the first generic rule for all-constant args is the folding rule (for example `rewritegeneric.go:1782` for Add64, `:8811` for Div64u with `d != 0`), so no rule creates extra sub-values. If a non-folding rule ever matched first, its `b.NewValue*` calls would also append to `f.Entry`.
5. **`replaceConst`** (`:576-600`) runs `for val, lt := range t.latticeCells` (a Go map). For each constant lattice:
   - If `val` is not already a Const: `val.reset(lt.val.Op)` and `val.AuxInt = lt.val.AuxInt`. This is in place: ID, Type, Pos and Block are kept and the args are dropped (Uses--). The value is **not** inserted into `f.constants`. Phis turn into constants inside their own block.
   - Then for each block in `defBlock[val]`, `rewireSuccessor`:
     - **If:** `removeEdge(int(AuxInt))`. This drops `Succs[1]` for true, or `Succs[0]` for false (the remaining edge moves to index 0). Then `Kind=Plain`, `Likely=Unknown`, `ResetControls`.
     - **JumpTable** (index in range): `swapSuccessorsByIdx(0, idx)`, then `removeEdge(1)` repeatedly, then Plain/Unknown/ResetControls.

   This happens even for blocks that were never marked visited.

**Data structures:**
- `worklist` (`:51-61`):
  - `edges []Edge` (FIFO);
  - `uses []*Value` (FIFO) plus `inUses` sparseSet (membership only);
  - `visited map[Edge]bool`;
  - `latticeCells map[*Value]lattice`;
  - `defUse map[*Value][]*Value`;
  - `defBlock map[*Value][]*Block`;
  - `visitedBlock []bool`.
- `lattice{tag int8, val *Value}`. Equality compares Op and AuxInt (`equals` `:126`).

**Parity traps (order dependence / nondeterminism):**
- **REAL NONDETERMINISM: `replaceConst` iterates the `latticeCells` map** (`sccp.go:578`).
  - `val.reset` is order-independent, and the debug Warnl order is cosmetic.
  - **`rewireSuccessor` → `removeEdge` is not order-independent.** `removePred`/`removePhiArg` swap the last pred into the hole, so when ≥2 rewired edges from blocks with *different* control values enter the same successor, that successor's final `Preds` order and phi-argument order depend on map iteration. Example: preds `[P1,P2,X,Y]` with P1 then P2 removed gives `[Y,X]`; the opposite order gives `[X,Y]`.
  - `phielimValue` may also turn a Phi into a Copy at a different intermediate step. The final Phi/Copy outcome is the same, but the argument order of a surviving Phi can differ.
  - Blocks controlled by the *same* value are processed in `defBlock` order, which is deterministic.
  - Parity: the port ranges in insertion order; the harness recovers an admissible order from the stock `Preds` and reruns `replaceConst` with it (`GoFV/Opt/SccpReplay.lean`, `docs/PARITY.md`). Small maps (≤ 8 keys) iterate in a rotation of insertion order.
- **Temporary-value pollution and ID consumption.** Every `computeLattice` call consumes one value ID (from the `f.freeValues` LIFO first, then `f.vid`) and appends one value (dead Const or OpInvalid, Pos = the original value's Pos) to the end of `f.Entry.Values`. None of them is freed in sccp. Consequences:
  - the number of calls and their order must be replicated exactly;
  - `generic deadcode` frees them, in its own order, which seeds `f.freeValues` for later passes;
  - because the temps keep `val.Pos`, possibly with is_stmt, they could affect deadcode's statement-mark relocation.

  The temps are also never visited: `range dest.Values` captured the slice before they were appended, and temps are never in `defUse`.
- The analysis order is deterministic. Edges and uses are FIFO, built from `f.Blocks`/`b.Values`/`Args` order and `b.Succs` order. The maps `visited`, `defUse` and `defBlock` are lookup only in the analysis phase. `lt.val` may point to a temp or to a real constant; only Op and AuxInt are used.
- The `visited` key for the seed is the pseudo-edge `Edge{f.Entry,0}`. Harmless because the entry has no preds.
- **Likely** is reset to Unknown on rewired blocks (unlike prove).
- No sorting. The sparseSet is never iterated.
- Floating-point folding (Add/Sub/Mul/Div 32F/64F, Sqrt, Floor/Ceil/Trunc/RoundToEven, Cvt*) comes from the generic rules. The Lean port must match Go's IEEE semantics and the rules' NaN guards exactly.

**External state read:**
- `f.pass.debug`, `f.Name` (Warnl only).
- Everything that `rewriteValuegeneric` reads: `Config`, `Config.Types`, type sizes, `PtrSize`, and so on.
- `f.freeValues`/`f.vid` (temp allocation).
- `f.Cache` scratch.
- Positions are copied verbatim.

**Depends on:**
- The generic rewrite rules (shared with opt; a port of `rewritegeneric` is a prerequisite).
- `removeEdge`/`removePred`/`removePhiArg`/`phielimValue`.
- No dominator or postorder analysis.
- It requires `generic deadcode` after it to remove temps, dead branches and the now-unreachable blocks.
- It tolerates `BlockInvalid` blocks left by branchelim (propagate case `:503`).

**Proof strategy & difficulty:**
- **M–L.** Two options:
  1. **Validator:** the certificate is the final lattice plus the executable-edge set. Check that it is a post-fixpoint of the transfer functions (Phi meet over executable edges, folding by the verified generic-rule evaluator, executable edges consistent with constant conditions), then justify each replacement and rewire. This is the standard SCCP soundness argument.
  2. **Direct proof:** prove the worklist algorithm correct, plus monotonicity.

  The validator is simpler because the worklist order then only matters for ID parity, which the untrusted port reproduces.
- Folding soundness reduces to the correctness of the generic constant-folding rules, which is shared work with opt.
- The nondeterministic pred order is handled by replaying the stock order (`docs/PARITY.md`).
**Proof (done, #32):** `GoFV.Proof.Sccp.sccp_refines : sccpChecked penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → RefinesUnder Env.Mono out.tables out.func penv.tables f`, about the validated pass `sccpChecked` (`GoFV/Opt/SccpCheck.lean`), which the registry runs (the stock-order replay `sccpReplay` stays unvalidated, for parity only; full corpus: 0 replayed). The checker validates the final lattice and the executable edges/blocks (exported by `Sccp.analyze`; `visited` is an array by block ID, not a `Std.HashSet`, so the kernel can evaluate the analysis): closure of the executable part (a constant control picks its successor), a post-fixpoint where a constant non-`Phi` term evaluates (`evalPure`, the semantics itself, so no rewrite rule is trusted) on its arguments' constants to its own, and a constant `Phi` has its constant on every executable in-edge. Three stages through two intermediates built by `replace` with other rewirings: `h` (`rewireFirst`: a rewired `If` or `JumpTable` becomes a `First` towards the kept successor, no edge removed; `h` must pass `check` with `CheckEnv.firstAny`, which lets a `First` block keep all successors of a `JumpTable`) and `k` (`rewireKeep`: the edges removed with `removeEdgeG false`, `Phi`s only losing arguments). `f → h` by the atom simulation under the source invariant `sccpInv` (registers with a constant cell hold `poison` or the constant; `SccpInv`, `SccpTerm`), `h → k` by deadcode's `DeadRel` simulation (`deadOK_spec`, `SccpDead`), `k → g` (when they differ: `removeEdge`'s `phielimValue` turned `Phi`s into copies) by copyelim's `CopyRel` simulation (`copyOK_spec`, `SccpCopy`; `k` must pass `check`). Fold temporaries are `Const`/`Invalid` terms (`RewriteCheck.termOp` counts `Invalid`, which evaluates to `poison`). `sccp-probe`: quick 1163 changed, 0 rejected; full 11336 changed, 0 rejected. Parity of `sccpChecked`: quick 9297/9297, full 96531/96531. Witness `sccp_witness` (`GoFV/Proof/Witness/Sccp.lean`, hand-written `pick`: constant `Phi` and a removed edge; 4.7 s / 0.43 GB).

**Issue summary:**
- Enabled on linux/arm64 (off with -N). 412 code lines plus reuse of the generic rules for folding.
- REAL nondeterminism: replaceConst ranges over map latticeCells and calls removeEdge, so the Preds/phi-arg order of a shared successor can vary between runs. Parity replays the stock order (upstream candidate #87).
- Each fold attempt allocates a temp (ID from freeValues/vid) that is left in f.Entry.Values (dead Const or OpInvalid) until generic deadcode. The call count and order must be exact.
- Likely is reset on rewired blocks. Float folding semantics come from the rules.
- Difficulty M–L. Recommended: verbatim port plus a fixpoint-certificate validator.
- Prerequisites: rewritegeneric port, removeEdge/phielimValue.

### check bce — issue #33

**Function / files:** `checkbce` in `checkbce.go:13-38`. No helpers besides `f.Warnl` and `logopt.Enabled`/`logopt.LogOpt`.

**Position & ordering:** It is `passes[28]` (`compile.go:486`) and is not required. Constraint: `generic deadcode` < `check bce` (`compile.go:562`). It sits between `late fuse` (27) and `dse` (29). The flag name is `-d=ssa/check_bce/...` (spaces become `_`).

**Enabled (linux/arm64, default build):** The pass is called, but it **returns immediately**: `f.pass.debug <= 0 && !logopt.Enabled()` (`:14-16`). `logopt` is enabled only by `-json=...`. `-N` skips it entirely.

**Size:** 38 lines (27 code), all exclusive.

**What it does:** Even when enabled, it only reads the SSA. Over `f.Blocks` (skipping `BlockInvalid`) × `b.Values`, for each `OpIsInBounds`/`OpIsSliceInBounds` it emits:
- `f.Warnl(v.Pos, "Found %v", op)` if `debug>0`;
- `logopt.LogOpt(v.Pos, "isInBounds"|"isSliceInBounds", "checkbce", f.Name)` if `logopt` is enabled.

**It never mutates `f`, in any configuration: it is an SSA identity.**

**Data structures:** None.

**Parity traps (order dependence / nondeterminism):** None for the SSA. The diagnostic order follows `f.Blocks`/`b.Values` order, which is irrelevant to parity. No allocation.

**External state read:** `f.pass.debug`, `logopt.Enabled()` (`-json` flag), `f.Name`, `v.Pos` (diagnostics only).

**Depends on:** Nothing. The ordering constraint exists only so that the diagnostics reflect post-deadcode code.

**Proof strategy & difficulty:** **S.** The Lean pass is `id`, with the trivial lemma `checkbce f = f`. Parity: before and after must be byte-identical.

**Issue summary:**
- Called on linux/arm64 but returns at once (debug=0, logopt off). Even with -d=ssa/check_bce/debug=1 or -json it only emits Warnl/LogOpt diagnostics and never touches the SSA.
- 27 code lines. No nondeterminism, no allocation.
- External state: only f.pass.debug and logopt.Enabled.
- Difficulty S: the Lean port is the identity function. The proof is rfl.

### dse — issue #34
**Function / files:** `dse` in `SSA/deadstore.go:21-191`; exclusive helpers `shadowRange`/`shadowRanges` with `contains`/`add` (:193-238), const `maxShadowRanges = 64` (:15). Shared: `f.newSparseSet`/`newSparseMap` (scratch), `symIsRO` (`rewrite.go:2088`), `auxToSym`, `Value.SetArgs1`.
**Position & ordering:** index 29 (`compile.go:487`), not required. passOrder: `{"generic cse","dse"}` (`compile.go:549`), `{"dse","insert resched checks"}` (`compile.go:532`). Runs after "check bce", immediately before "memcombine" (no copyelim in between).
**Enabled (linux/arm64, default build):** yes; skipped under -N. No config/flag dependence.
**Size:** 226 lines (:13-238).
**What it does:** block-local backward dead-store elimination, per block in f.Blocks order:
1. Scan `b.Values` (skip Phi): memory-typed values go to `stores`; for each in-block memory arg `a`, add `a` to `storeUse`; also to `loadUse` unless the op is `Store`/`Zero`/`VarDef` or a `Move` whose source is `Addr` of a read-only symbol (`symIsRO`). Non-memory values: the first `LocalAddr` per Aux is remembered in `localAddrs`; `InlMark`/`Convert` are ignored; any other in-block memory arg goes to `loadUse`.
2. Find the unique store not in `storeUse` (`last`; Fatal on 0 or 2).
3. Walk the memory chain backwards from `last` via the first in-block memory arg (stops at Phi or when leaving the block). At a value in `loadUse`, clear all shadow info. For `Store/Zero/Move`: strip `OffPtr` chain to (base, off), size = type size (Store) or AuxInt; canonicalize a `LocalAddr` base to the block's first `LocalAddr` with the same Aux; if `[off, off+sz)` is contained in one recorded range for that base ID → rewrite to `Copy(mem)` (Aux/AuxInt cleared); else add the interval (merging overlapping/adjacent ranges; ignored if `off<0`, `off+sz>0xffff`, or 64 ranges already tracked).
**Data structures:** `loadUse`, `storeUse` sparseSets; `shadowed` sparseMap (value ID → 1-based index into `shadowedRanges []*shadowRanges`); `localAddrs map[any]*Value` (cleared per block); `shadowRanges.ranges []shadowRange{lo,hi uint16}`.
**Parity traps (order dependence / nondeterminism):**
- Sparse set/map are used only via `add/contains/get/set/clear` — no iteration, so internal order is irrelevant. `localAddrs` is lookup-only. `shadowRanges.ranges` order changes with merging but `contains` is order-independent ⇒ harmless.
- Semantically relevant caps must be mirrored exactly: 16-bit offset limit, `maxShadowRanges` (64), and the per-block reset; `contains` requires containment in a *single* merged range.
- "first LocalAddr per Aux in b.Values" canonicalization depends on b.Values order; base equality is value-ID identity (relies on CSE having merged addresses).
- No allocation or freeing; rewritten values keep ID/Pos (is_stmt kept on the Copy). The resulting memory `Copy`s are NOT removed before memcombine/writebarrier — later passes see them.
**External state read:** for `Move` sources: `obj.LSym` of an `Addr` Aux: `Type == objabi.SRODATA && len(R) == 0` (`rewrite.go:2088-2091`) — exporter must carry an `isRO` bit per symbol as of this point [INFERENCE: relocations of RO data syms are filled before SSA]; `Store` Aux `types.Type.Size()`; Aux identity for `LocalAddr`.
**Depends on:** CSE (address identity), no CFG analyses; produces Copies consumed as-is by memcombine/writebarrier.
**Proof strategy & difficulty:** direct port; proof by a backward "will be overwritten before any read" argument within a block on a byte-addressed memory model with base+offset aliasing (distinct bases may alias — soundness relies on only eliminating a store fully covered by a later store to the *same* base value with no intervening read, so aliasing only makes it conservative). Validator alternative is easy (recheck coverage per eliminated store). **M** — small, block-local, but needs a memory model with partial overlap.
**Proof (done, #34):** translation validation on the inputs the checker accepts. The Bool checker `DSE.drel` (`GoFV/Opt/DeadStoreCheck.lean`): same CFG, block kinds, values and controls; every value kept or an eliminated `Store`/`Zero`/`Move` turned into `Copy mem`; along each block's schedule a *pending set* per memory value (byte ranges of an `Addr`/`LocalAddr` base allocation, offset in `[0, 2^63)`): an eliminated store adds its range, a kept `Store`/`Zero`/`Move` removes the bytes it writes, a kept `VarDef` its variable, a kept `Move` must read an allocation with no pending range, any other op has none; a value with pending ranges is used only in its block, by no `Phi`/control, as the memory argument of a `Store`/`Zero`/`Move`/`VarDef` or by `LocalAddr`/`InlMark`; every block's schedule in the output lists the output's roots in the input's order. `GoFV.Proof.DSE.dse_refines` (`GoFV/Proof/Pass/DSE*.lean`; fragment `dseFrag`: dse fails or `drel` accepts): lock-step simulation, frames equal on every value without pending ranges, memories along a chain equal outside its pending bytes (`MemEq`). Witness `dse_witness` on `test/initialize` `f10` (`Zero` of the stack result overwritten by two `Store`s). `lake exe mem-probe` (quick-v1): 447 changed functions, 435 accepted (1405 eliminated stores); outside: a base that is not an `Addr`/`LocalAddr` (`NilCheck` 5, `SelectN` 5, `Phi` 1, `Load` 1: its offset may wrap). `localAddrs` is a `TreeMap` (kernel evaluation), parity 100%.
**Issue summary:** Enabled (not required; off under -N). ~226 LOC. No map/sparse iteration; caps (16-bit offsets, 64 ranges) and LocalAddr canonicalization (first per Aux in block) must be mirrored. No allocation/freeing; leaves memory Copies seen by memcombine/writebarrier. External: LSym RO-ness (SRODATA && no relocs) for Move sources. Difficulty M. Prereq: generic cse port.

### memcombine — issue #35
**Function / files:** `memcombine` in `SSA/memcombine.go:18-27`; exclusive helpers: `memcombineLoads` (:29-86), `BaseAddress`/`splitPtr` (:91-128), `combineLoads` (:130-331), `memcombineStores` (:333-380), `combineStores` (:383-755), `sizeType`/`truncate`/`zeroExtend`/`leftShift`/`rightShift`/`byteSwap` (:757-841). Shared: `mergePoint` (`rewrite.go:1001-1046`), `clobber` (`rewrite.go:1053`), `Config.haveByteSwap` (`config.go:404`), `f.ConstInt16/32/64` (constants cache), sparseSet, `slices.SortFunc`.
**Position & ordering:** index 30 (`compile.go:488`), not required. passOrder: `{"late fuse","memcombine"}` (`compile.go:598`), `{"memcombine","lower"}` (:600). Runs right after "dse".
**Enabled (linux/arm64, default build):** yes (skipped under -N). Gated by `Config.unalignedOK` (:21) = true on arm64 (`config.go:244`); `BigEndian` false; `RegSize` 8; `haveBswap64/32/16` true (`config.go:245-247`). The `arch == "S390X"` checks (:185, :477) never fire on arm64.
**Size:** 841 lines (≈ 820 excluding the header); all exclusive.
**What it does:**
- Loads: mark every arg of `Or16/32/64` (whole function, one sparse set). Per block, roots = unmarked Or values in b.Values order; BFS each root's Or tree into `order`. For each value in `order` that is still an Or, try n = max (8/4/2 by op), n/2, …, 2: `combineLoads` collects n leaves of the Or tree (left-to-right expansion, all non-root nodes `Uses==1`), requires each leaf be `[Lsh const](ZeroExtN(Load ptr mem))` with the same ext op, same `mem`, same `splitPtr` base, sorts by offset, requires contiguous offsets and little- or big-endian shifts, finds `mergePoint(root.Block, loads)` and a load in that block for `pos`; then allocates in `loadBlock`: wide `Load(r[0].load.Args[0], mem)`, optional `Bswap`, `ZeroExt`, `Lsh` (+`ConstInt64` shift, cached); root becomes `Copy(v)`; the n loads are `clobber`ed (`OpInvalid`, stay in b.Values).
- Stores: per block, mark memory args of Stores; `order` = for each unmarked (chain-last) Store in b.Values order, walk the in-block Store chain backwards appending. For each still-`Store` with size < RegSize: `combineStores` gathers up to 8 consecutive chain stores (same block, `Uses==1`, same base, cumulative size ≤ 8), builds prefix candidates of total size 8/4/2 (map `mergeableSet`), picks the largest whose sorted-by-offset entries are sequential; `mem` = memory arg of the earliest store, `pos` = its Pos. Three shapes: all-constant values → `ConstInt{16,32,64}` of the packed value; values are same-mem consecutive non-pointer Loads → widen the first load's Type in place; values are `Trunc(Rsh(base, c))` of one base in LE/BE order → allocate `Rsh`/`Trunc`/`Bswap` (at `root.Pos`, in `root.Block`). Root store is rewritten (Aux=wide type, Pos=pos, args ptr/val/mem); other stores are clobbered and retyped `TBOOL`.
**Data structures:** sparseSet `mark` (contains only), `order []*Value`, `LoadRecord`/`StoreRecord` slices, `mergeableSet map[int64][]StoreRecord` (lookup by key only).
**Parity traps (order dependence / nondeterminism):**
- `slices.SortFunc` (unstable pdqsort) by offset at :236 and :541. Harmless: every commit path afterwards checks strictly increasing offsets (contiguity with size>0), so on success keys are unique and the sorted order is determined; on failure the sorted slice is discarded (the store candidates are per-size `slices.Clone`s, :520). The port may use any sort + uniqueness lemma.
- Root/order iteration: b.Values order, BFS order of Or trees, chain-walk order of stores; a value already rewritten (Copy/Invalid) is skipped via op checks — the port must reproduce the "first success wins" visiting order exactly.
- Allocation order (IDs from free list): loads path: Load, [Bswap], [ZeroExt], [Const64 shift via cache, then Lsh]; stores path: [Const via cache], [Rsh+const], [Trunc], [Bswap]. Constants go to `f.Entry`, `src.NoXPos`, via `f.constants` (hit depends on prior cache contents).
- No `freeValue`: clobbered values remain in b.Values as `OpInvalid` (stores also retyped `TBOOL`); dead Or/shift/ext trees remain for deadcode.
- Positions: new load-side values use the Pos of the first (lowest offset) load located in `loadBlock`; store-side shift/trunc/swap use the root's *original* Pos; the root's Pos is then replaced by the earliest store's Pos.
- `mergePoint` walks single-predecessor chains (`Preds[0]`, max 100 steps) — CFG-shape dependent but deterministic.
- `splitPtr` does not look through `OpCopy`: Copies left by "dse" (no copyelim in between) block matches — must not be "cleaned up" in the port.
**External state read:** `Config.unalignedOK`, `BigEndian`, `RegSize`, `arch`, `haveBswap*`; `types.Types[TUINT16/32/64, TBOOL]`; `Type.Size()`, `HasPointers()`.
**Depends on:** late fuse (bigger blocks), CSE (base pointer identity), dse output as-is; `mergePoint` from rewrite.go.
**Proof strategy & difficulty:** direct port; proof needs a byte-level little-endian memory model (combining n loads/stores into one wide access + shifts/bswap) and unaligned-access semantics; alternatively validate each commit with a local bit-vector equivalence check (decidable, small). **L** — 800 LOC of pattern matching with endianness arithmetic; proof needs bit-vector + memory byte-layout lemmas.
**Issue summary:** Enabled (not required; off under -N); arm64 unalignedOK=true, LE, RegSize 8, bswap all sizes. ~840 LOC. Traps: two unstable SortFunc calls (harmless: unique keys on every success path), exact visiting order (b.Values, BFS of Or trees, store chains), allocations via constants cache, Pos selection rules, clobbered values left in place, Copies from dse not looked through. External: Config arch flags only. Difficulty L (byte-level memory + bit-vector reasoning). Prereq: dse, late fuse, cse ports.
**Proof (loads and stores, #35):** `GoFV.Proof.MemCombine.memcombine_refines : memcombineChecked penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → RefinesUnder Env.Mono out.tables out.func penv.tables f` (`GoFV/Proof/Pass/MemCombine.lean`; witnesses `memcombine_witness`, `encoding/binary.littleEndian.Uint16`, and `memcombine_store_witness`, `littleEndian.PutUint16`). `memcombineChecked` (`GoFV/Opt/MemCombine/Check.lean`) runs the stock pass and keeps its result iff `tabsAgree` (a combined store's aux may be a new `type` aux) and `mcOK` accept it, else returns its input. `mcOK`: atoms are `f`'s but a `Store` may change its aux and arguments, and a root of `f` that is no root of `g` is a `Store` or a `Zero` (`RewriteCheck.atomsXOK`, shared with the forwarding layer's dropped identity writes, #151); every value reached from atom arguments and controls through terms is unchanged or an `Or` that became a `Copy` with the same symbolic little-endian bytes (`symOf`, target loads covered by the source's, `coveredOK`); a changed `Store` heads a chain of `Store`s of `f` down to its memory argument whose stored values' bytes (`storedBytes`: a description narrower than 8 bytes, possibly reading narrow loads, or a `ConstBool`) tile its width from its pointer, one base and index (`splitP`), and its value's description (`symOf … true false`: 8-byte loads opaque; a dropped opaque byte only if another byte of that value is kept) has those bytes and reads only values and loads each stored value reads. Proof: the atom simulation generalised (`AtomSim.atomSimX_refines`: `AtomsX`, `AtomArgsRefX` with the changed-store obligation `ChgRefP`; dropped roots are `Store`s or `Zero`s, which never panic); loads as before (`mc_ref`: `symOf_sound`, `symOf_complete`, `covered_loadOK`, `read_cover`); stores by `store_chgRef` (`MemCombineStore.lean`: the chain's writes via `MemAtoms` (`chain_den`), each `poison` or its description's bytes (`recBytes`), one write of their bytes (`write_tiling`), refined by the target's write). The registry keeps the stock pass: store-of-loads combining (stores of single-use loads become a store of the first load, widened) is not a refinement under the current semantics (an integer load of partially poison bytes is `poison`), issue #247; the verified pipeline runs `memcombineChecked`. Coverage (`memcombine-probe`): quick-v3 9297 inputs, stock changes 181 (101 combining stores), accepted 174 (94); rejected: 3 store-of-loads, 4 store chains on an `SP`-based (uintptr-typed) base. full-v4 96533 inputs, stock changes 3489 (1417 combining stores), accepted 3078 (1007); rejected 411: 390 store-of-loads (246 combined stores of a widened load, 144 widened loads), 12 stores of 8-byte loads, 4 values outside the related set, 4 `SP`-based chains, 1 `Or64` root (`ldobj`). Parity `-p memcombine` (stock, registry unchanged) quick-v3 9297/9297.

### writebarrier — issue #36
**Function / files:** `writebarrier` in `SSA/writebarrier.go:164-597`; exclusive helpers in the same file: `ZeroRegion`, `mightBeHeapPointer` (:30), `mightContainHeapPointer` (:40-79), `needwb` (:84-118), `needWBsrc` (:121), `needWBdst` (:127-149), `computeZeroMap` (:601-696), `wbcall` (:699-729), `IsReadOnlyGlobalAddr` (:761), `isVolatile` (:854). Shared: `IsStackAddr` (:732, also ssagen `ssa.go:5666`), `IsGlobalAddr` (:744), `IsNewObject` (:774-829), `isNewObject`/`isSpecializedMalloc` (`rewrite.go:470-484`), `storeOrder` (`schedule.go:397-559`, shared with nilcheckelim `nilcheck.go:117`), `f.spSb`, `f.ConstInt32`, `StaticAuxCall` (`op.go:313`), `ABIConfig.ABIAnalyzeTypes` (`abiutils.go:315-347` + `assignParam`/`tryAllocRegs`), `f.freeValue`, `f.NewBlock`, `Block.AddEdgeTo/CopyControls/SetControl`, `reflectdata.TypeLinksym`, `f.NewLocal`.
**Position & ordering:** index 31 (`compile.go:489`), `required: true`. No passOrder entries mention it; it sits after "memcombine" and before "insert resched checks"/"lower".
**Enabled (linux/arm64, default build):** yes (required, also under -N). Gated by `f.fe.UseWriteBarrier()` = `base.Flag.WB` (`ssagen/ssa.go:8041-8042`), default true (`base/flag.go:178`), disabled by `-wb=false`. `buildcfg.Experiment.CgoCheck2` (GOEXPERIMENT=cgocheck2, off by default; not in the baseline at `exp.go:81-89`) adds cgoCheck calls (:230, :526, :544). On arm64 `f.ABIDefault == f.ABI1` (regabi always on, `ssagen/ssa.go:232-237,367`) and `len(intParamRegs)=16 ≥ 3`, so: volatile-source copying (:330-356, which calls `f.NewLocal`) is skipped; `wbcall` passes args in registers (no stack stores, :705-716); `IsNewObject` uses the register-result form (`SelectN [0]` of the call, :777-784). `f.pass.debug>0` only prints the zero map.
**Size:** 859 lines total; pass + exclusive helpers ≈ 800 (minus ~70 comment lines); `IsSanitizerSafeAddr` (:833-850) is unrelated. Plus shared `storeOrder` (163 lines) and the `ABIAnalyzeTypes` subset for `uintptr` args.
**What it does:**
1. `select1[callID] = SelectN[1]` over all values (:182-194); `computeZeroMap`: for each `IsNewObject` result `v` (`StaticCall` to `runtime.newobject` or a size-specialized `runtime.mallocgc*SC` with non-unsafe.Pointer result), `zeroes[memID] = {base: v, mask: low min(64, size/8) bits}`; then a forward fixpoint over f.Blocks×b.Values propagating masks across `Store`s to the same base (clearing written words; dropping when mask 0).
2. Per original block (range over the original `f.Blocks` slice; new blocks are not visited): mark `Store/Move/Zero` with `needwb` (pointerful type, dst not a stack addr, and dst might contain heap ptrs per zero map / RO global, and the stored value/source might be a heap pointer; Zero never needs it) by flipping Op to `StoreWB/MoveWB/ZeroWB`.
3. On first such block: lazily `spSb()`, `Syslook("writeBarrier")`, `wbaddr = Entry.NewValue1A(f.Entry.Pos, OpAddr, UInt32Ptr, wbsym, sb)`, `Syslook("wbZero")`, `Syslook("wbMove")`, `const0 = ConstInt32(UInt32, 0)`, scratch sets.
4. `b.Values = storeOrder(b.Values, …)` (reorders the whole block), then repeatedly (`goto again`) take the *last* maximal run of WB stores (allowing VarDef/VarLive, ≤2 interleaved plain Stores, but none after a MoveWB was seen): `stores`=run, `after`=tail, b truncated. Build `bThen := NewBlock(Plain)`, `bEnd := NewBlock(b.Kind)`; bEnd takes b's controls, Likely and successors (preds patched in place); b becomes `If (Neq32 (Load wbaddr mem) const0)` with `Likely=BranchUnlikely`, succs [bThen, bEnd]; bThen→bEnd. In bThen: optional duplicated NilCheck; for each StoreWB, buffer `val` (if not global and not seen) and `Load *ptr` (if not provably zero, not seen) — every 8 entries `flush` emits `WB [n]`, `Select0`, `Select1`, n×(`OffPtr`, `Store uintptr`); then for each ZeroWB/MoveWB: `Addr {TypeLinksym(T)} SB` (allocated in **b**, not bThen) and `wbcall(wbZero|wbMove)` = `StaticCall` (+`SelectN [0]`) with a fresh `AuxCall` from `ABIAnalyzeTypes([uintptr…], nil)`. In bEnd: mem `Phi(mem, memThen)`, optional NilCheck, then re-emit every store of the run as plain `Store/Zero/Move/VarDef/VarLive` (+ cgo check calls under CgoCheck2). The run's last value is moved to bEnd and reset to `WBend(mem)` (Pos NotStmt); other run values are `resetArgs` then `freeValue`d in run order; an unused original NilCheck becomes `OpInvalid`; `after` is appended to bEnd. `f.fe.Func().SetWBPos(pos)` per WB op.
**Data structures:** `select1` (Cache value slice indexed by ID), `zeroes map[ID]ZeroRegion` (lookup only, iterated only in debug print), sparseSets `sset`/`sset2` (contains/add only), `storeNumber` int32 scratch, `writes` fixed array of 8, `volatiles` slice (unused on arm64).
**Parity traps (order dependence / nondeterminism):**
- `storeOrder` rewrites `b.Values` order for every block containing a WB store: exact algorithm (store numbering 3i/3i+1/3i+2, DFS with explicit stack over in-block args in Args order, counting-sort bins) must be ported; nil-check runs inside the result are sorted with `slices.SortFunc(…, valuePosCmp)` (`schedule.go:548,554`) — **unstable pdqsort with possibly equal keys** (two NilChecks at the same position) ⇒ either port pdqsort bit-exactly or prove keys distinct.
- ID reuse: run values (except `last`) are freed in run order (LIFO list) *before* the next `again` iteration and before later blocks are processed, so subsequent `NewValue`s pop those IDs in reverse free order. Block IDs come from `NewBlock` (free block list first): bThen then bEnd, per run, last run first.
- Allocation order per run (exact): `NewBlock` bThen, bEnd; `Load`, `Neq32` in b; [NilCheck in bThen]; per StoreWB in run order: [`Load` old value] interleaved with flushes (`WB`, `Select0`, `Select1`, then per entry `OffPtr`, `Store`); final flush; per Zero/MoveWB: `Addr` in b, `StaticCall`, `SelectN` in bThen; `Phi` in bEnd; [NilCheck in bEnd]; re-emitted stores in bEnd. Lazy globals (`Addr` wbaddr in Entry, then `ConstInt32` via cache) are allocated at the first WB block, between needwb marking and storeOrder.
- `computeZeroMap` fixpoint is forward over f.Blocks×b.Values; entries once written are never deleted (a later round may overwrite with a different struct value) — deterministic but order-dependent; port the exact loop.
- Positions: bThen.Pos = b.Pos(new) = Pos of first store in run; bEnd.Pos = old b.Pos; WB-buffer stores use each store's Pos; `WBend` gets `last.Pos.WithNotStmt()`; `wbaddr` uses `f.Entry.Pos`.
- `b.Likely`: b becomes Unlikely, bEnd inherits the old Likely; succ edges of bEnd keep their `e.i` (preds of successors patched in place, :368-371).
- Aux identity: `Syslook` LSyms (one per runtime name), `TypeLinksym(T)` (one per type), fresh `AuxCall` objects per `wbcall`.
- [INFERENCE] `storeNumber` is not cleared between blocks, but only fresh/other-block IDs are queried afterwards, so stale entries are harmless.
**External state read:** `base.Flag.WB`; `buildcfg.Experiment.CgoCheck2`; `f.fe.Syslook` for `writeBarrier`, `wbZero`, `wbMove` (+`cgoCheckPtrWrite`, `cgoCheckMemmove`); `reflectdata.TypeLinksym(T)` for Zero/Move types; `f.ABIDefault`/`f.ABI1` identity, `Config.intParamRegs` length, `Config.PtrSize`, `Config.ctxt.Arch.FixedFrameSize`, `Config.Types`; `types.LocalPkg.Path == "runtime"` (:617); `Type.HasPointers/Size/Elem/IsUnsafePtr`; `obj.LSym.Type == SRODATA` for `Addr` Aux (:766); `AuxCall.Fn.String()` names (`runtime.newobject`, `runtime.mallocgcSmallNoScanSC*`, `…ScanNoHeaderSC*`, `…TinySC*`; size-specialized malloc is baseline-on, `exp.go:88`). Writes: `ir.Func.WBPos` via `SetWBPos` (not SSA state).
**Depends on:** expand calls (StaticCall/SelectN result form for `IsNewObject`), decomposition, memcombine/dse output as-is (Copies are looked through by `IsStackAddr`/`IsGlobalAddr`); before lower. Uses no cached CFG analyses; its CFG edits invalidate the caches implicitly via `f.NewBlock` (`func.go:440`) and `AddEdgeTo` (`block.go:280`) — the in-place pred patching of bEnd's successors (:368-371) is covered by those calls.
**Proof strategy & difficulty:** direct port. Proof: under a sequential semantics where the `writeBarrier` flag load, `WB` buffer ops and `wbZero/wbMove` calls are modelled as GC-only effects (no change to Go-visible memory except the buffer), the transformed block is equivalent; plus the zero-map soundness lemma for eliding barriers. Needs a CFG-splitting simulation (one block → three). **L** — CFG surgery with exact ID/free-list behaviour, storeOrder + unstable sort, ABI call construction; semantics of barriers must be axiomatized.
**Issue summary:** Enabled always (required, -N too) unless `-wb=false`; arm64 regabi ⇒ register-arg wbcalls, no volatile copies. ~800 LOC + shared storeOrder (160) + ABIAnalyzeTypes subset. Traps: storeOrder reorder incl. unstable SortFunc on NilCheck Pos (equal keys possible), freeValue of run stores ⇒ LIFO ID reuse, exact block/value allocation order, Likely/Pos rules, computeZeroMap fixpoint. External: Syslook syms, TypeLinksym per type, CgoCheck2, Flag.WB, LocalPkg.Path, AuxCall Fn names, LSym SRODATA. Difficulty L. Prereq: expand calls, storeOrder port, ABIAnalyzeTypes port.
**Proof (done, #36):** `GoFV.Proof.writebarrier_refines : writebarrierChecked penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () → RefinesFrom WB.WbPre out.tables out.func penv.tables f` (`GoFV/Proof/Pass/WBSim.lean`), with `WbPre env args mem := MemOK (addGlobals env mem) ∧ ContractsOK env` (the memory with the global image holds a defined, read-only `runtime.writeBarrier` flag and no write-barrier buffer; the environment's contracts keep that). `writebarrierChecked` (`GoFV/Opt/WriteBarrierCheck.lean`) keeps the stock result iff `tabsAgree` and `WBCheck.wbOK` accept it: every block of `f` became a chain of split segments, buffer blocks and a last segment with the block's terminator; every listed value has a role (`roleOf`) whose fields `roleOK` checks; the source schedule's non-pure nodes are the kept ones and the runs' stores in chain order (`npOK`); runs with `wbZero`/`wbMove` calls are rejected. The proof is a macro-step simulation (`runLoop_simIH`): the target walks the chain against the source's frame after the block (`WBWalk`, `WBAll`), or, when the source panics, panics alike at the same node or at a copy of the dropped nil check (`WBPanic`; the target evaluates before its panic point only values the source evaluated, `WBOrder`/`WBNpOrder`). Witness `GoFV.Proof.Witness.writebarrier_witness` (`runtime_setProfLabel`). wb-probe (`GoFVTest/WBProbe.lean`), quick-v3: 9,297 inputs, 967 changed, 68 with `wbZero`/`wbMove` calls (out of scope), 897 accepted, all equal to stock, 2 rejected (one `WB` size mismatch, one `Mul64uover` memory-typed value); full-v4: 96,533 inputs, 18,244 changed, 1,793 with `wbZero`/`wbMove` calls, 16,381 accepted (all equal to stock), 70 rejected (42 runs with more than 8 buffer entries, i.e. several `WB`s in one buffer block; 28 `Mul64uhilo`/`Mul64uover` values whose tuple type `memTyOK` rejects). To make the pass kernel-evaluable for the witness, `writebarrier` reads `ptrsize` with `decInt?`, its zero map and store sets are association lists, and `ABIAnalyze.ABIConfig.parse` goes through `ABIConfig.parse?` (pass parity quick-v3 9,297/9,297, full-v4 96,533/96,533).

### insert resched checks — issue #37
**Function / files:** `insertLoopReschedChecks` in `SSA/loopreschedchecks.go:44-272`; exclusive helpers in the same file: `edgeMem`/`rewriteTarget`/`rewrite` (:15-41), `newPhiFor` (:276), `rewriteNewPhis` (:293-358), `addDFphis` (:367-400), `findLastMems` (:403-463), `backedges` (:482-509). Shared: `f.Idom()`, `f.postorder()`, `f.Sdom()` (SparseTree child/sibling order, `isAncestor`), `f.invalidateCFG`, `StaticAuxCall` + `ABIAnalyzeTypes(nil,nil)`, `f.fe.Syslook`.
**Position & ordering:** index 32 (`compile.go:490-491`), not required, `disabled: !buildcfg.Experiment.PreemptibleLoops`. passOrder: `{"dse","insert resched checks"}`, `{"insert resched checks","lower"}`, `{"insert resched checks","tighten"}` (`compile.go:532-535`).
**Enabled (linux/arm64, default build):** **no** — PreemptibleLoops is not in the baseline (`internal/buildcfg/exp.go:81-89`); needs GOEXPERIMENT=preemptibleloops; also skipped under -N and for `f.NoSplit` functions (:64).
**Size:** 509 lines (whole file exclusive).
**What it does:** find backedges by iterative DFS from Entry in Succs order (:482-509); `findLastMems` per block (allocating `Select1`/`SelectN` for tuple/results last stores — even if unused) and an `InitMem` in Entry if none; propagate memory-at-block-end in reverse postorder; for each backedge header without a memory Phi, insert a trivial Phi (`newPhiFor`) and recursively trivial Phis on the dominance frontier (`addDFphis`, dom-tree child order); collect all uses to redirect (`rewriteNewPhis`, preorder over the dominator tree) and apply them; per backedge create blocks `test` (If: `GetG`, `SP`, `OffPtr [16]`, `Load`, `Less64U`; Likely=Unlikely) and `sched` (`StaticCall goschedguarded` + `SelectN [0]`), splice `bb→test→{sched→h, h}`, append a new arg to every header Phi, set `bb.Likely` to keep the loop edge likely; `invalidateCFG`.
**Data structures:** `tofixBackedges []edgeMem`; Cache value slices `lastMems`, `memDefsAtBlockEnds`; maps `newmemphis map[*Block]rewrite`, `dfPhiTargets map[rewriteTarget]bool`.
**Parity traps (order dependence / nondeterminism):** `for _, r := range newmemphis` applying `SetArg` (:159-163) is a map iteration — harmless iff all rewrite targets are distinct [INFERENCE: each (v,i) is assigned to the nearest dominating new-phi block and `dfPhiTargets` prevents duplicates]; debug prints iterate maps too. Allocation order depends on backedge DFS order, dom-tree child/sibling order (from `Sdom`), and per-backedge block creation (`test`, `sched`). Hidden allocations in `findLastMems`.
**External state read:** `buildcfg.Experiment.PreemptibleLoops`, `f.NoSplit`, `f.fe.Syslook("goschedguarded")`, `f.ABIDefault`, `Config.Types.Uintptr`, g struct layout assumption (stack limit at `2*PtrSize`, :227).
**Depends on:** dominators/sparse tree/postorder; dse before it.
**Proof strategy & difficulty:** not needed for the default configuration; if ever: direct port + simulation treating `goschedguarded` as a no-op call. **M** (SSA phi insertion on dominance frontiers + CFG splicing), priority none.
**Issue summary:** DISABLED on default linux/arm64 (needs GOEXPERIMENT=preemptibleloops; also off under -N and for NoSplit). 509 LOC. Traps if enabled: map iteration over newmemphis when applying rewrites (believed harmless), dom-tree/backedge-order-dependent allocation, hidden Select allocations in findLastMems. External: experiment flag, f.NoSplit, Syslook("goschedguarded"). Difficulty M; recommend: port as "pass disabled" and assert the flag in the exporter.

### cpufeatures, rewrite tern (no issue)
**Function / files:** `cpufeatures` in `SSA/cpufeatures.go:115-262` (+`ifEffect` :28-113; 262 lines); `rewriteTern` in `SSA/rewritetern.go:37-294` (294 lines) + `tern_helpers.go`.
**Position & ordering:** indices 33 and 34 (`compile.go:492-493`). "cpufeatures": `required: Experiment.SIMD`, `disabled: !Experiment.SIMD`; "rewrite tern": not required, `disabled: !Experiment.SIMD`. passOrder `{"cpufeatures","lower"}` (`compile.go:606`).
**Enabled (linux/arm64, default build):** no — SIMD is not in the baseline (`exp.go:81-89`). SIMD *can* be turned on for arm64: `ParseGOEXPERIMENT` has no per-arch restriction for it, and arm64 code consumes it (`ssagen/intrinsics.go:1674-1677` `simdARM64Intrinsics`, `internal/obj/arm64/asm7.go:2255` SVE). But even with GOEXPERIMENT=simd both passes are no-ops on arm64: `cpufeatures` returns unless `Arch.Family == goarch.AMD64` (`cpufeatures.go:116-120`), and `rewriteTern` returns if `f.maxCPUFeatures == CPUNone` (always, since cpufeatures did nothing) or arch ≠ AMD64 (`rewritetern.go:38-46`). Note SIMD=on would still change other passes on arm64 (`CanSSA` size rules `value.go:633,662`, IsSIMD paths in expand calls), so the exporter should assert SIMD=off.
**Size / proof:** not ported; model both as identity guarded by the exported SIMD flag + arch. (For reference: rewriteTern collects roots from a Go map and then sorts them by unique ID, `rewritetern.go:73-82`, so it would be deterministic on amd64.)

## 5. Recommended implementation order and shared modules

Parity is checked per pass on the **exported** input of that pass (`docs/PLAN.md` §2), so no
pass port waits for an earlier pass port; the order below is driven by shared code, by what
each pass exercises, and by the semantics phases (`docs/plans/semantics.md` §9) the proofs
need.

### 5.1 Shared modules to build first

| Module (proposed) | Content | Go source | Used by |
| --- | --- | --- | --- |
| `GoFV/SSA/Alloc.lean` | `newValue`/`NewBlock` with free lists, `freeValue`/`freeBlock`, `Uses` maintenance, `reset`, `SetArg*`, `AddArg*`, `ReplaceControl`, `truncateValues` | `func.go:280-453`, `value.go`, `block.go` | every pass |
| `GoFV/SSA/ConstCache.lean` | `constVal`, `unCache`, magic keys | `func.go:356-395,663-760` | rules, prove, known bits, expand calls, memcombine, sccp, shortcircuit |
| `GoFV/SSA/Edges.lean` | `AddEdgeTo`, `removePred`, `removeSucc`, `removeEdge`, `removePhiArg`(+`phielimValue`), `swapSuccessors*`, CFG-cache invalidation | `block.go:269-380`, `deadcode.go:311`, `copyelim.go:124` | deadcode, shortcircuit, fuse, prove, sccp, branchelim, phiopt, writebarrier, resched |
| `GoFV/SSA/Analysis/Postorder.lean`, `Dom.lean`, `SparseTree.lean`, `CfgCache.lean` | DFS postorder (verbatim), idom (unique: simple algorithm + proof), sparse tree with entry/exit numbers, `Option` caches with Go's invalidation points | `dom.go`, `sparsetree.go`, `func.go:766-809` | numberlines, cse, phiopt, nilcheckelim, prove, known bits, branchelim, resched |
| `GoFV/Util/SparseSet.lean`, `SparseMap.lean` | insertion-ordered dense list, swap-remove, pop | `sparseset.go`, `sparsemap.go`, `sparsemappos.go` | deadcode, nilcheckelim, branchelim, dse, sccp, memcombine, writebarrier |
| `GoFV/Util/PdqSort.lean` | exact port of Go's pdqsort (insertion ≤ 12, xorshift, pattern breaking) | `slices/zsortanyfunc.go` | cse, storeOrder, prove, memcombine, decompose |
| `GoFV/SSA/Pos.lean` | `XPos`/`lico`, `SameFileAndLine`, stmt marks, `xposmap` + `cachedLineStarts` | `cmd/internal/src/{pos,xpos}.go`, `xposmap.go`, `biasedsparsemap.go` | numberlines, deadcode, fuse, branchelim, nilcheckelim, prove, memcombine, expand calls, rules |
| `GoFV/SSA/TypeCmp.lean` | `Type.Compare` as rank comparison from the export's `typeorder`; pointer identity | `types/type.go` | cse, constant cache, copyelim |
| `GoFV/SSA/StoreOrder.lean` | `storeOrder` | `schedule.go:410-560` | nilcheckelim, writebarrier |
| `GoFV/Rules/Apply.lean` (#7) | `applyRewrite` driver: iteration order, copy following, `Invalid` reset, final freeing order, cycle detection | `rewrite.go:41-232` | opt ×3, divisible, divmod, decompose builtin (dec rules), sccp (folding via `rewriteValuegeneric`) |
| `GoFV/Opt/Prove/{Limit,Poset,Ctx,FactsTable,Flow,IndVar,Downward,Simplify,Pass}.lean` | verbatim ports (poset and limits difftested against Go: `scripts/prove-difftest.sh`) | `prove.go`, `poset.go`, `loopbce.go`, `downward_counting_loop.go` | prove, late fuse (`fuseBranchRedirect`) |
| later: `GoFV/SSA/ABI.lean` | ABI assignment queries over the exported `abiparam` data; `ABIAnalyzeTypes` subset for new runtime calls | `abi/abiutils.go` | expand calls, writebarrier, resched |

Every module keeps kernel-friendly definitions (`List` scans, structural recursion,
`@[csimp]` swaps to `Array` for compiled code — LEARNINGS.md), because pass correctness proofs
will unfold them.

### 5.2 Pass order

1. **Identity/guard ports** (prove the infrastructure, parity trivially): `check bce` (identity),
   `softfloat` (identity guarded by the exported `softfloat 0`), `insert resched checks` and
   `cpufeatures`/`rewrite tern` (identity guarded by the experiment flags; full port of resched
   only if the experiment is ever wanted).
2. **Small passes exercising the shared modules**: `number lines` (postorder, positions,
   `cachedLineStarts`), `copyelim`/`phielim`, `zero arg cse`, `deadcode` (free-list order,
   edge removal, stmt marks, names) — after these, every allocation/edge primitive is
   parity-tested.
3. **Rules** (#7, critical path for many passes): `applyRewrite` + rule interpreter, then
   `opt`/`middle opt`/`late opt`, `divisible`/`divmod`, `decompose user`/`decompose builtin`.
4. **Medium CFG/value passes** (parallel): `phiopt`, `nilcheckelim` (storeOrder),
   `generic cse` (PdqSort, auxmap, stale postorder), `known bits`, `early fuse`,
   `shortcircuit` (shares `fuseBlockPlain`), `branchelim`, `dead auto elim`, `dse`, `sccp`
   (needs the rule folder; parity modulo the §3 permutation).
5. **Memory/ABI passes**: `memcombine`, `writebarrier` (storeOrder, ABI subset), `expand calls`
   (ABI; land early as a parity port, prove last).
6. **`prove`** (XL, verbatim port: facts table, poset, induction variables), then
   `late fuse` (`fuseBranchRedirect` reuses prove's facts table).

Proof order follows the semantics phases: P1 passes first (copyelim, deadcode, zcse, cse,
phiopt, branchelim, fuse, shortcircuit, known bits, sccp, divisible/divmod, integer rules),
then P2 (nilcheckelim, decompose, dse, dead auto elim, memcombine), P3 (expand calls,
writebarrier), with `prove` and `cse` as translation validators (untrusted port + proven
checker) from the start.
