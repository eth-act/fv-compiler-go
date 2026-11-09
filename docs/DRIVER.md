# Driver: the Lean pipeline inside `cmd/compile`

Milestone G7 (issue #12), extended through `trim` by H8 (#386) and through object code by I8
(#554). The patched compiler can run the Lean pipeline in place of every pass of `ssa.Compile`
(`number lines` through `trim`, including `regalloc`), per function, import the allocated
function and continue with the stock `genssa`; in mode `full3` it also runs the Lean ports of
`AllocFrame`, `genssa`, `Flushplist` and the DWARF writers and installs their result (the back
end, below).

## Pieces

| Piece | Where |
| --- | --- |
| Pipeline runner `gofv-ssa-opt` | `GoFVTest/Driver/{Pipeline,Main}.lean`, `lake build gofv-ssa-opt` |
| Back end (`--back`, `--back-check`) | `GoFVTest/Driver/Back.lean` |
| Import into Go, driver hook | `patches/go/0002-gofv-driver.patch` (on top of 0001, the exporter) |
| End-to-end checks | `scripts/driver-e2e.sh` |

### `gofv-ssa-opt`

`GoFVTest.Driver.pipelinePasses` (`GoFVTest/Driver/Pipeline.lean`) is `compile.go`'s `passes`
table from `number lines` to `trim`: `GoFV.Opt.stockPasses` (`GoFV/Opt/Verified.lean`, `number
lines` … `rewrite tern`, the verified pipeline's table) followed by `loweredStockPasses` (`lower`
… `trim`), with each pass's `required` flag and Go `disabled` condition (from the export's
`config` lines); a pass runs iff `optimize || required` and `disabled` does not hold
(`StockPass.enabled`) — exactly `ssa.Compile`'s test. Ports come from
`GoFVTest/Parity/Registry.lean`: registering a port for parity also makes the driver use it.
`--verified` runs the verified pipeline instead (below). The chain carries `len(curfn.Dcl)`
(`State.dclLen`, `regalloc`'s `PassEnv.dclLen`): the input section's `dcllen` (export format
5.1) plus the `name` aux values each pass creates (`newAutos`), and the passes from `lower` on
get the file's `typelink` groups (`PassEnv.typeLink`).

```
gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>
gofv-ssa-opt --verified [--from <pass>] [--vstats FILE] [--profile] <in.ssa>
gofv-ssa-opt --list
gofv-ssa-opt --check [--mixed] [--whole-file-env] [--strict] [--jobs N] [--max-report N] [--table FILE] <dir|file>...
gofv-ssa-opt --check --verified [--whole-file-env] [--jobs N] [--max-report N] [--table FILE] <dir|file>...
gofv-ssa-opt --check --verified --e2e [--whole-file-env] [--jobs N] [--table FILE] [--accepted FILE] <dir|file>...
gofv-ssa-opt --back <in>
gofv-ssa-opt --back-check [--jobs N] [--max-report N] [--table FILE] <dir|file>...
```

- Driver mode reads a `gofv-ssa` file whose first section is the function (section `start`),
  runs the enabled passes from `--from` (default `number lines`) and prints a status line —
  `status ok`, `status unported "<pass>"` or `status error "<pass>" "<msg>"` — followed, for
  `ok` (or, with `--partial`, for the others), by a `gofv-ssa` file with one section named after
  the last pass run: the definitions the passes created or changed (types, aux values, slots
  at the numbers the Lean passes gave them; redefinitions at their own numbers) and the
  function, with its `dcllen` when the input has one. The input's type order, `typecmp`
  exceptions, `typelink` groups and `frontend` block form the pass environment
  (`PassEnv.typeOrder`, `PassEnv.typeLink`, `PassEnv.frontend`).
- `--list` prints `ported|unported "<name>"` per stock pass (all of `ssa.Compile`'s); the compiler
  reads it once.
- `--check` is whole-pipeline parity over stock export files (below).
- `--back` and `--back-check`: the back end (below).

### The import (`patches/go/0002-gofv-driver.patch`)

- `ssa/driver_gofv.go`: settings, the per-function driver, the reader of `gofv-ssa-opt`'s output
  and the importer.
- `ssa/compile.go`: `gofvDriverStart(f)` before the pass loop; `drv.skip(i)` for each enabled
  pass; `drv.finish()` writes the statistics line.
- `ssagen/ssa.go`: `ssafn.GOFVDclLen`/`GOFVDclTruncate`, so an abandoned import can drop the
  autos `fe.SplitSlot` and `f.NewLocal` made for it.
- `cmd/internal/src/xpos.go`: `src.GOFVXPos(index, lico)` builds an `XPos` from exported fields.

For a segment starting at pass `i`, the driver exports the current `f` in process with the
exporter of 0001 (`gofvNewExporter`, `section("start")`, `tail()`), pipes it into
`gofv-ssa-opt --from <passes[i]>`, and imports the result:

1. **Objects.** Numbers the export defined resolve to the compiler's own objects (the
   exporter's tables). New objects are rebuilt through the compiler's constructors: types with
   `types.NewPtr/NewSlice/NewArray/NewTuple/NewResults` or the predeclared/SSA types; symbols
   with `fe.Syslook` (the config's runtime symbols), `reflectdata.TypeLinksym` (type
   descriptors, so the linker emits them) or `base.Ctxt.LookupABI`; `*AuxCall`s with the ABI
   analysis of their parameter types (`ABIAnalyzeTypes`, with an empty `regInfo` when registers
   are used, as `StaticAuxCall` makes it: without it `Reg` drops the register arguments); new
   autos with `fe.SplitSlot` of the parent slot (the suffix is what the new name adds to the
   parent's) or, for `.autotmp_<n>` (`stackalloc`, the `regalloc` shuffle, `writebarrier`), with
   `f.NewLocal` at the definition's position and type, in number order (Lean numbers them in
   creation order, and `TempAt` names them from `len(Dcl)`); jump tables (`<fn>.jump<b>`,
   `lower`'s `JumpTable` rule) as `makeJumpTableSym` makes them; `stringAux`, `int64Aux`,
   `AuxNameOffset`, `PanicBoundsC(C)`, `auxMark` directly. Objects of the export's `frontend`
   block (and the types their symbols refer to) that a pass copied to new numbers are the
   block's compiler objects, renumbered (a type's references are resolved first, so a
   recursive type works). An `*AuxCall` redefinition (`Fn` rewritten by `devirtLECall`) is
   applied in place (undone if the import fails); a type redefinition must be what the
   compiler's object renders as. Every new or redefined object is rendered again by the
   exporter at its Lean number and must equal the Lean definition byte for byte; for a new
   symbol only its name and ABI must match (the symbol is the frontend's; its contents are
   whatever the frontend has so far).
   Several identical `*types.Type` objects can share a type number; the importer uses, for
   each number, the object with the most sizes calculated (the exporter renders the first one
   met, the stock passes call `Size()` on theirs), and a value keeps its own object when its
   type number is unchanged.
2. **Function.** Blocks and values are rebuilt from the IDs (`Values`, `Args`, `Controls`,
   `Succs`/`Preds` with edge indices, `Uses`, positions, `Likely`, aux), and `Entry`, `Type`,
   `OwnAux`, the ID allocators (`vid.last`, `bid.last`), the free lists (fresh `Value`/`Block`
   objects with the listed IDs, linked like `freeValue`/`freeBlock` do), `Names`,
   `NamedValues`, `CanonicalLocalSlots`, `CanonicalLocalSplits`, the constant cache (with
   `InCache`), and the CFG caches (`postorder`, `idom`, `sdom`, `auxmap`, `linestarts` with its
   leftover entries, the loop nest from its `cache loopnest` line with the cached postorder and
   dominator tree). Ops and block kinds are generic or ARM64 (`ARM64<name>`, the ranges of
   `opGen.go`). The state of the lowered passes: `f.RegAlloc` (`&Config.registers[i]` by name,
   inline `LocalSlot`s, `LocPair`, `LocResults`), `f.tempRegs`, `FlagsLiveAtEnd`, `Hotness`,
   `f.scheduled`, `f.laidout`. `NamedValues` can name values that are in no block and not on the
   free list (`regalloc` drops rematerializable values from the schedule without freeing them):
   they become `Value`s with just their ID (`BuildFuncDebug` reads only that). The register
   constraints `regalloc` caches in `*AuxCall`s are replayed as `regspec` does (`Reg` with the
   op's `regInfo` for each call whose `AuxCall` has a `regInfo`, `OwnAux.ResultReg` for
   `MakeResult`, in value order; undone if the import fails), and every Lean definition with a
   `callreg` line must then render as it. `DeferReturn` is remapped by block ID.
3. **Check.** `f` is exported again with the same exporter; the section must equal the Lean
   output's function text byte for byte (its `dcllen` included: the frontend's `len(Dcl)` after
   the import is the Lean pipeline's), with no new definitions, except that the entries of
   `namedx`, `splits` and `canon` (Go maps, which the exporter sorts by object numbers) are
   compared as sets.
4. **Cache.** The imported values and blocks are not in `f.Cache`'s storage, which `Cache.Reset`
   clears up to the first ID never used: their IDs are marked used there so the storage later
   passes take is cleared for the next function.

Any failure (exec, status, parse, an object that cannot be rebuilt, the check) restores `f`
(fields saved before the import, aux mutations and `Dcl` additions undone) and is recorded as
an event; the stock passes then run.

**Effects.** Some stock passes change compiler state outside the function and the definition
tables. A Lean pass returns these as `PassOut.effects`; `gofv-ssa-opt` prints the effects of the
passes it ran, in order, as `effect` lines between the status line and the file, and the importer
replays them after a successful check. Implemented: `effect useiface a<n>` —
`reflectdata.MarkTypeSymUsedInInterface(sym, curfn)` from `rewriteFixedLoad` (a type or itab
loaded from a dictionary, or a pointer type's `Elem`), i.e. the function's `R_USEIFACE`
relocations (and the DWARF `R_USETYPE` ones derived from them). `f.Type` keeps the compiler's
own object when its type number is unchanged (the debug info's `PopulateABIInRegArgOps` reads
the parameter names from it; another object of the same number made location lists differ
run to run).

**Type rounds.** The Lean passes read `types.(*Type).Compare` from the export's `typeorder`,
which only ranks the types of the export. When a run creates types (e.g. `opt` making `*byte`,
which `Compare` puts next to `*uint8`), the driver builds them in Go and runs the segment again
with them added to the export (`gofvExportWith`), up to 3 runs (`gofvTypeRounds`). Without
this, `generic cse` partitions differently in 26 corpus functions. Building the types claims
numbers in the exporter's tables, so when no further round runs because a type could not be
built, the import uses a fresh export of the same function.

**Frontend copies numbered parent first.** A pass that copies a frontend type (`importType`,
e.g. `opt` copying `testing.T` with its field types) numbers a struct before its fields. When
the importer renders such a struct, its tables are cut at the struct's number. Every object of
a claimed number therefore keeps that number in `x.types`, so the exporter never has to look up
a higher number by key in the cut tables (#119).

### Modes and settings

| Variable | Meaning |
| --- | --- |
| `GOFV_SSA_DRIVER=<path>` | enable; path of `gofv-ssa-opt` |
| `GOFV_SSA_DRIVER_MODE=full` (default) | one segment from `number lines` through `trim`; only a complete pipeline (`status ok`) is imported, anything else runs all stock passes |
| `GOFV_SSA_DRIVER_MODE=mixed` | every maximal run of ported passes is a segment (`--partial`): the state before an unported or failing pass is imported, the stock compiler runs that pass, and the next ported pass starts a new segment |
| `GOFV_SSA_DRIVER_MODE=full3` | `full`, then the back end for every function (below) |
| `GOFV_SSA_DRIVER_PKG`, `GOFV_SSA_DRIVER_FUNC` | regexps selecting packages / `<pkgpath>.<f.Name>` (default all) |
| `GOFV_SSA_DRIVER_STATS=<file>` | append one line per function: `"<pkg>" "<func>" <abi> lean=<n> stock=<n>` and one field per event (`unported "<pass>"`, `error "<pass>: <msg>"`, `import "<reason>"`, `exec`, `parse`), tab-separated; in mode `full3` one more line per function for the back end: `"<pkg>" "<func>" <abi> back=lean`, or `back=stock` and the event (`exec`, `parse`, `status`, `resolve`, `check`) with its detail |
| `GOFV_SSA_DRIVER_DUMP=<dir>` | write each run's input and output (debugging; the back end's as `<func>,<abi>.back.in`/`.out`) |

Do not combine with `GOFV_SSA_EXPORT` (its sections are written only after stock passes).

## The back end (mode `full3`, issue #554)

In mode `full3` the Lean ports of Phase 3 (`docs/PASSES3.md`) produce the function's object
code. Where the compiler splices them in: after `Flushplist` and the `Compile` tail, at the end
of `ssagen.Compile`. Stock `AllocFrame`, `genssa` and `Flushplist` (with `populateDWARF`) still
run first: they create the symbols (`gclocals·…`, `$f64.…`, type and DWARF symbols), set the
frame offsets, register the package-level DWARF records (`DwFixups`, abstract functions) and
free the Prog list, which the rest of the compile relies on. The Lean result then replaces what
they wrote into the function's own symbols.

1. **Input.** At the end of `ssa.Compile` the driver exports the function after `trim` (the
   imported Lean result, or stock's after a fallback) as a `gofv-ssa` file with one section
   `trim` (`keepForBack`); the Phase 3 exporter of 0001 links its names to that file's aux
   numbers and records the `.prog` file in memory (`frame` at `AllocFrame`, `genin`, `prog0`,
   `asm` and `dwarf` at the end of `Compile`). The driver input file (`gofv-prog 3 in`,
   `gofvProgInput`) is that file without any result: every section keeps its definitions
   (types, names, symbols, position bases, inlining nodes) and only the input lines — `frame`'s
   `in` lines, `genin`, `prog0`'s text symbol before `Flushplist` (the marker relocations),
   `symalign`, `autot` and `dbgregout`, `dwarf`'s `dwfn` and `dw*` lines.
   `GoFV.Asm.parseProgInput` reads it; `GoFVTest.Driver.Back.inputView` is the same view of a
   full `.prog` file.
2. **Lean.** `gofv-ssa-opt --back /dev/stdin` reads both files (one stream; the second starts
   at its header line) and runs `GoFVTest.Driver.Back.chain`, every step on the previous one's
   result: `allocFrame`, `genssa` on that frame (it records `valueToProgAfter`,
   `GenState.progAfter`), `buildFuncDebug` on that frame, `flush` on `genssa`'s Prog list,
   `info`, `putFunc` and `generateDebugLinesSymbol` with `GetPC` from the block starts,
   `progAfter` and the assembled PCs. Two recorded inputs are results of `AllocFrame`
   (`populateDWARF` reads them after it): `dwdcl` (the truncated `Dcl`) and the frame offsets
   and `used` flags of the `dwname` facts; the chain takes them from its own frame. `symalign`
   (`LSym.Align` of the operands' symbols) is recorded for the symbols stock's Progs reference.
   Symbols keep the input file's numbers; symbols `genssa` or the assembler create get new
   ones. The output is `status ok`, a `sym` line per referenced symbol, then the text symbol's
   `fn` header and `funcaux`, `text` with its `reloc` lines, `pcln`, `usedfiles`, `inltree`,
   a `data` line (with relocations) per symbol whose contents the ports wrote (pc-value
   tables, metadata symbols, constants, jump tables) and, when `populateDWARF` ran, `dwsyms`
   (info, loc, ranges, abstract function, lines), the child-DIE fixups (`dieref`, `dieoff`)
   and the DWARF symbols' `data` lines, in the `.prog` syntax; or
   `status error "<stage>" "<msg>"`.
3. **Install** (`ssagen/driver_back_gofv.go`). Symbols of the input file resolve by their
   number there (the exporter's table, anonymous ones included, e.g. the method-name symbols
   of `R_USENAMEDMETHOD` marker relocations; the DWARF symbols of `dwsyms` must be
   `populateDWARF`'s), new ones by role (the pc-value tables of `pcln`); any other new symbol
   is an error. Installed: the text symbol's `P`, `R` and `Size`, the funcdata list,
   and `P`, `R`, `Size` of the symbols only this function writes — pc-value tables,
   `StackObjects`, `OpenCodedDeferInfo`, `ArgInfo`, `ArgLiveInfo`, jump tables and the DWARF
   symbols (relocations that `ReferenceChildDIE` adjusted right away get the same offsets;
   the deferred ones are patched by `DwarfFixupTable.Finalize` as for stock).
4. **Check.** The compiler's state after the install, rendered with the result's symbol
   numbers in the result's order, must equal the result byte for byte. This checks the
   install and everything not installed against the compiler: the `FuncInfo` header (`Args`,
   `Locals`, `FuncFlag`, the attributes `preprocess` sets), funcaux, `UsedFiles`, the local
   inlining tree, the contents of shared symbols (`gclocals·…`, `.wrapinfo`, constants) and
   the child-DIE fixups. On any error the installed fields are restored (stock's result stays)
   and the stats line says `back=stock` with the event.

A corrupted result reaches the object file: with a wrapper that changes one hex digit of the
`text` line, the `strconv` archive differed from stock while every function said `back=lean`.

`gofv-ssa-opt --back-check <dir|file>...` runs the chain on the input view of every `.prog`
file of a corpus (with its `.ssa` file, whose last section is `trim`) and compares its result,
with symbols by name or role, with the file's stock `asm` section, metadata symbols and
`dwarf` section; the nightly gate runs it on the full corpus (`docs/GATE.md`).

## Verified mode (`--verified`, issues #189, #385)

`gofv-ssa-opt --verified <in.ssa>` runs `GoFV.Opt.verifiedPipelineFull` (`docs/PASSES.md` §0,
"The verified pipeline", for the passes before `lower`; `docs/PASSES2.md` §0, "The verified
pipeline through `trim`", for the rest) instead of the registered ports: the checked variant of
every pass with a refinement theorem, the stock port of the others, `check` between passes,
from `number lines` through `trim`. Its output has the format of driver mode and is always
`status ok` unless a pass fails; `--vstats FILE` appends one line per function:
`"<pkg>" "<func>" <abi>`, then `verified` or `unverified "<pass>: <verdict>"` (the first run
before `lower` that is not proven, identity or skipped), the number of runs per verdict before
`lower`, `lowered=<n>` (the runs from `lower` on) and `trim=verified` or
`trim=unverified "<pass>: <verdict>"` (through `trim`), tab-separated. A function whose line says
`verified` is, by `verifiedPipeline_refines`, refined by the state before `lower`; one whose line
says `trim=verified` is, by `verifiedPipelineFull_refines`, refined by the allocated function
after `trim` (`runLoc` of the output against `run` of the input, under `VPre` and no nil-page
fault of the `schedule` input). The output differs from stock wherever a checked variant undoes
a rewrite or an optional pass is skipped. The verified `regalloc` drops the call auxes' register
caches (`AuxCall.Reg`/`ResultReg`, which only Go's `regalloc` reads; `eraseCallRegs`); the
driver output fills them back (`GoFV.Opt.Regalloc.fillCallRegs`: `regspec` of every call and
`MakeResult`, in value order, as the importer replays them), because the importer checks that
every call aux it fills renders as the Lean output's (without this every function with a call
fell back to the stock passes).

How each pass of `GoFV.Opt.stockPasses` runs (`stockPasses_sound` checks every `proven`/`guarded`
entry against its theorem; the passes from `lower` on: `docs/PASSES2.md` §0):

| status | passes |
| --- | --- |
| proven (theorem, no fragment test) | number lines; short circuit; opt, middle opt, late opt (`optChecked`); zero arg cse; phiopt; prove (`proveChecked`; size guard `proveGuard`: skipped, reported as `fragment`, above `proveMaxValues` = 20,000 value IDs); divisible, divmod (`…Checked`); known bits; early fuse; softfloat; branchelim; sccp (`sccpChecked`); late fuse; check bce; memcombine (`memcombineChecked`) |
| guarded (theorem on a fragment, decided at run time: an optional pass outside it is skipped, a required one unverified) | early phielim and copyelim (`copyFrag`, `emptyFragB`); the five deadcodes (`deadFragB`); generic cse (`cseFrag`); nilcheckelim (`nilFrag`); expand calls (`expandCallsFrag`, required); decompose user, decompose builtin (`decUserFrag`, `decBuiltinFrag`, `RefinesFrom DecPre`, required); dead auto elim (`daeFrag`, `RefinesFrom (FrameSafe ∧ InitAvoids)`); dse (`dseFrag`); writebarrier (`wbGuard`: `writebarrierChecked`'s acceptance, `RefinesFrom WbPre`, required) |
| stock port (never enabled for linux/arm64 in the default build: an "off" guard) | insert resched checks; cpufeatures; rewrite tern |

The required passes run in a checked variant (opt, middle opt, late opt: `optChecked`;
divisible, divmod: `…Checked`) also run their stock port (`StockPass.full`): if the checked
result differs, the stock result is kept and the run is `unverified (checked variant
incomplete)`, because later passes and `lower` need every rewrite (an undone `PtrIndex` or
`IMake` rewrite is not lowered: without this, `driver-e2e.sh --verified` failed to build std).

`scripts/driver-e2e.sh --verified` builds std and the programs with
`GOFV_SSA_DRIVER=<wrapper running gofv-ssa-opt --verified --vstats …>` in full mode, counts the
byte-identical archives and binaries without failing on the others, and fails only when a build
fails, a program's output or exit status differs from stock under qemu, or a function falls back
to the stock passes. The report adds the per-function verdicts.

`gofv-ssa-opt --check --verified <dir|file>...` is the corpus report: per function, the
verified pipeline through `trim` from section 0 (driver export environment and type rounds, as
`--check`), the state after each pass compared with the stock section until the first difference
(from `lower` on also the chain's `dcllen`; the stock tables without their call-register caches),
and the final state compared with the last stock section (`trim`'s). It prints the functions fully
verified through `rewrite tern` and through `trim`; of those, the ones verified vacuously (the
input has an op or block kind that `run` leaves `stuck` whatever its arguments: a root that
`evalOp` hands to `atomicRoot` and `Atomic.modelled` does not cover, such as `TailLECall`, or a
block kind outside `stepTerm`'s arms other than `Exit`, such as `RetJmp`; `unmodelledIn` in
`GoFVTest/Driver/Main.lean`; the theorems say nothing about the inputs that reach one), listed by
op or block kind, and the ones whose final state equals stock. Then the functions whose final
state equals stock, the unverified functions by first
unverified run before `lower`, the functions verified through `rewrite tern` but not through
`trim` by their first unverified run, the functions by first difference (pass and its verdict), a
per-pass table of verdicts, and the skipped and unverified runs by reason. For deadcode and
copyelim runs before `lower` outside their fragment it adds which conditions of
`deadFragB`/`copyGuard` fail (`GoFVTest/Driver/FragWhy.lean`, with the first offending value's op
and type shapes): per run, for first unverified runs, and for functions whose only unverified
runs are such deadcode runs. It also counts the functions fully verified through `trim` whose
`schedule` step relies on `NilPtrsOK` (a swap that only `nilPtrSwap` allows,
`GoFVTest.SchedClass.relyNilPtrs`), and lists the rejected `regalloc` runs (`raClass`) and the
rejected `schedule` runs (`SchedClass.schedClass`: the classes of the pairs `swapOK` rejects) by
class, first unverified from `lower` on / all. It exits 1 only for parse errors or no input. The
nightly gate runs
it on the full corpus, and `driver-e2e.sh --verified`, as reports (`docs/GATE.md`).

`gofv-ssa-opt --check --verified --e2e <dir|file>...` counts the functions the end-to-end theorem
`GoFV.Proof.Obj.verified_mach` applies to (`GoFVTest/Driver/E2E.lean`): per `.ssa` file with
its companion `.prog` file, the verified pipeline as above; on a `fullyVerified` result, the back
end on the pipeline's own output (function and tables): `Env.load` with the `trim` section's
function replaced (homes and temporaries from its `f.low`), `allocFrame` on the pipeline's own
locals (`ownFrame`: `AllocFrame`'s input `Dcl` is the first `dcllen` of section 0 entries of the
stock input, the frontend's, followed by the autos the pipeline created, the `name` aux values its
tables define and section 0's do not, in creation order, with definitions made from the aux
values; the stock passes' own autos are left out; a mismatch with the pipeline's `dcllen` after
`trim` is an error), `genssa` with its Progs in the file's symbol numbers (as `chain`),
`checkG49` (the latest merged genssa slice) against `LocCtx.make` of the pipeline's tables and
function, then on `liveCtx` of it (the homes of removed values dropped, as `checkG49` runs
`checkG49L`) `entryStoresOK` at the end of the entry block's entry values (`entryLen`: the entry
stores cover the windows of the register-assigned parameters in `Blk.local` blocks, `pendWins`)
and `retRegsOK` with its class tables (every `Ret` returns its results in their ABI
registers, `MakeResult` components of no wider class), `Flushplist` on those Progs and `checkObj`
on the same Progs. From
the `.prog` file it reads only the input view (`inputView`: definitions, config, `Dcl` at
`AllocFrame`'s start, `genin`), no stock result. It prints the fully verified functions, those
the back end ran on, those `checkG49` with `entryStoresOK`, `retRegsOK`, `checkObj` and all of
them accept (the end-to-end count; a line counts the functions with a pending window and those
`entryStoresOK` rejects), the end-to-end ones whose pipeline output equals
stock, the frame sizes `ownFrame` gives on the functions whose output equals stock (against the
stock `stksize`/`stkptrsize`), the top back-end errors and rejection reasons (numbers replaced by
`#`; for `retRegsOK` the first failing condition, `retWhy`), and as a cross-check the same back
end on the stock `trim` function (whole-file tables, stock `Dcl`). `--accepted FILE` writes the
end-to-end accepted files. Exit 1 only for parse errors (including a missing `.prog`) or no
input.

`gofv-ssa-opt --verified --profile <in.ssa>` prints to stderr where the verified pipeline spends
its time on one function (ms): `verifiedPipeline` through `rewrite tern`, then per pass from
`lower` on its run, the stock port of a checked variant, `check` of the result and the theorem's
guard (for `regalloc`: `tabsAgreeL`, `Cx.make`, `certify`, `checkWith`). Each piece is timed
alone, then `runPassL` advances the chain, so it takes about twice a normal run.

## Whole-pipeline parity (`gofv-ssa-opt --check`)

Per-pass parity (`docs/PARITY.md`) replays each pass on the stock input. `--check` chains the
Lean results instead, through `trim` (the output of `regalloc` feeds `loop rotate` and `trim`): it starts from section 0 with what the driver exports (section 0's
definitions, the type order and `typecmp` exceptions restricted to those types, and the frontend
closure the exporter's `frontend` block computes for them), runs the pipeline, and compares the
state after every pass with the stock section of that pass (objects not in section 0 are paired
by `renumber`'s canonical walk, so the Lean numbering of new objects is free). The chain also
checks the pass sequence (the stock file must have a section for exactly the enabled passes) and,
after every pass, the chain's `len(curfn.Dcl)` against the section's `dcllen` (format 5.1). It
runs the type rounds as the driver does. Outcomes per function: identical to the end, identical
up to the first unported pass, first divergence at a pass, or a Lean pass error.

- `--mixed` simulates `GOFV_SSA_DRIVER_MODE=mixed`: an unported pass is taken from the stock file
  (its output section and the tables in force there) and the chain continues.
- `--whole-file-env` uses the per-pass parity environment (the whole file's type order and
  frontend), to separate divergences caused by the driver's narrower view from chain effects.

`sccp` is documented as nondeterministic (permutations across runs); divergences at `sccp` are
reported separately.

`--check` compares as the importer does. A pass that creates a symbol aux (e.g.
`writebarrier`'s `type:T` for `typedmemmove`, `opt`'s `*T` descriptors) defines it from what the
driver's export has, which may lack the contents the stock section shows later; the importer
only requires name and ABI of a new symbol (the symbol is the frontend's), so `--check` pairs new
symbols by name and ABI and does not follow their `typeinfo`/`itabinfo` references. The entries
of `namedx`, `splits` and `canon` are compared as sets. `--strict` compares every definition and
the map lines' order, as `pass-parity`.

## Results

Issue #12 has the earlier numbers and #386 the H8 ones (corpus `gofv-corpus/2aae1000ea1d`, `std`
and the corpus programs built for linux/arm64 by `scripts/driver-e2e.sh`). H8, export format 5.1:

- `gofv-ssa-opt --check` (`number lines` through `trim`): the whole pipeline is identical for
  9,297/9,297 functions of quick-v7 (42 s, `--jobs 4`) and 96,560/96,560 of full-v9 (786 s).
  There are 0 divergences and 0 Lean pass errors.
- `driver-e2e.sh --mode full -p 8`: 372/372 std archives byte-identical. 183 programs: 183
  binaries byte-identical, and 183 with the same output and exit status under qemu. 44,189
  functions go through Lean from `number lines` to `trim`, with 0 fallbacks: PASS (17 min).
- `driver-e2e.sh --verified -p 8`: 183/183 programs behave as stock. 40,887 of 42,899
  functions are fully verified, with 0 pass errors and 0 fallbacks: PASS (18 min).
- Through `trim` (#385; main 51ef75c1: every pass from `lower` to `trim` a proven step, with
  `lateB` #520, `ArgPtrsOK` #521, `tabsAgreeModL` #522): `driver-e2e.sh --verified -p 8`: 183/183
  programs behave as stock, 44,189 functions through Lean, 0 fallbacks, 0 pass errors; of 42,899
  functions, 40,897 fully verified before `lower` and 29,590 through `trim` (a717e6db plus
  addressing modes, late lower, pair and flagalloc: 23,941; #503: 12,830): PASS (66 min on a
  loaded machine). `--check --verified --jobs 4`: quick-v7 8,885 / 6,383 (through `rewrite tern` /
  through `trim`), full-v9 the table in `docs/PASSES2.md` §0.

- Back end (I8, #554; quick-v10 corpus, export `gofv-prog 3`): `gofv-ssa-opt --back-check`
  (the chain on the input view, against stock): 9,297/9,297 functions match (105 s,
  `--jobs 6`); full-v11: 96,674/96,674 (5.5 min, `--jobs 4`, load ~30). `driver-e2e.sh --mode
  full3 -p 8`: 372/372 std archives byte-identical; 183
  programs: 183 binaries byte-identical, 183 with the same output and exit status under qemu;
  44,358 functions through Lean from `number lines` to `trim` and 44,346 through the Lean back
  end (the rest stop at `Compile`'s large-frame check), 0 fallbacks in either: PASS. Wall time
  on a loaded machine (load average 100–600): stock build 40 s, driver build 82 min (two
  `gofv-ssa-opt` runs per function). `test/gcgort.go`'s driver build was killed once (SIGKILL,
  no compiler error; its largest back-end process uses 34 MB); built again alone with the same
  settings it was byte-identical with its 228 functions through the back end, and the report
  was completed with `--report-only`.

State of the known gaps:

- Type-object identity for `zero arg cse` (#101): the pipeline tracks `*types.Type` object
  classes itself. It starts from the input section's `zvar`. Each pass reports the objects of
  the values it creates or retypes (`PassOut.typeObjs`). The rule interpreter reports
  `t.PtrTo()` as a fresh object unless `ptrcache` lists `t`, `x.Type` and a type variable bound
  from a matched value as that value's object, and anything else as canonical. The classes
  become the next pass's `PassEnv.zvar` (`Pipeline.nextZvar`).
- `expand calls`' constant cache compares types with `Tables.typeEq`, which honours the
  `typecmp` exceptions (#93, fixed).
- `decompose` creates its slots at the numbers the export gives them (`renumberSlots`), so a
  chained `decompose builtin` orders slots as stock (#79, fixed).
