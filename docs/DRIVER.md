# Driver: the Lean pipeline inside `cmd/compile`

Milestone G7, issue #12. The patched compiler can run the Lean generic pipeline in place of the
stock passes before `lower`, per function, and continue with the stock `lower` onward.

## Pieces

| Piece | Where |
| --- | --- |
| Pipeline runner `gofv-ssa-opt` | `GoFVTest/Driver/{Pipeline,Main}.lean`, `lake build gofv-ssa-opt` |
| Import into Go, driver hook | `patches/go/0002-gofv-driver.patch` (on top of 0001, the exporter) |
| End-to-end checks | `scripts/driver-e2e.sh` |

### `gofv-ssa-opt`

`stockPasses` is `compile.go`'s `passes` table from `number lines` to `rewrite tern` with each
pass's `required` flag; a pass runs iff `optimize || required` and its port's `disabled`
condition (`PassEntry.disabled`, from the export's `config` lines) does not hold — exactly
`ssa.Compile`'s test. Ports come from `GoFVTest/Parity/Registry.lean`: registering a port for
parity also makes the driver use it.

```
gofv-ssa-opt [--from <pass>] [--to <pass>] [--partial] <in.ssa>
gofv-ssa-opt --list
gofv-ssa-opt --check [--mixed] [--whole-file-env] [--jobs N] [--max-report N] [--table FILE] <dir|file>...
```

- Driver mode reads a `gofv-ssa` file whose first section is the function (section `start`),
  runs the enabled passes from `--from` (default `number lines`) and prints a status line —
  `status ok`, `status unported "<pass>"` or `status error "<pass>" "<msg>"` — followed, for
  `ok` (or, with `--partial`, for the others), by a `gofv-ssa` file with one section named after
  the last pass run: the definitions the passes created or changed (types, aux values, slots
  at the numbers the Lean passes gave them; redefinitions at their own numbers) and the
  function. The input's type order, `typecmp` exceptions and `frontend` block form the pass
  environment (`PassEnv.typeOrder`, `PassEnv.frontend`).
- `--list` prints `ported|unported "<name>"` per stock pass; the compiler reads it once.
- `--check` is whole-pipeline parity over stock export files (below).

### The import (`patches/go/0002-gofv-driver.patch`)

- `ssa/driver_gofv.go`: settings, the per-function driver, the reader of `gofv-ssa-opt`'s output
  and the importer.
- `ssa/compile.go`: `gofvDriverStart(f)` before the pass loop; `drv.skip(i)` for each enabled pass
  before `lower`; `drv.finish()` writes the statistics line.
- `ssagen/ssa.go`: `ssafn.GOFVDclLen`/`GOFVDclTruncate`, so an abandoned import can drop the
  autos `fe.SplitSlot` made for it.
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
   are used, as `StaticAuxCall` makes it: without it `Reg` drops the register arguments); new autos with `fe.SplitSlot` of the
   parent slot (the suffix is what the new name adds to the parent's); `stringAux`, `int64Aux`,
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
   leftover entries; a cached loop nest is recomputed with `loopnestfor`). `DeferReturn` is
   remapped by block ID.
3. **Check.** `f` is exported again with the same exporter; the section must equal the Lean
   output's function text byte for byte, with no new definitions, except that the entries of
   `namedx`, `splits` and `canon` (Go maps, which the exporter sorts by object numbers) are
   compared as sets.
4. **Cache.** The imported values and blocks are not in `f.Cache`'s storage, which `Cache.Reset`
   clears up to the first ID never used: their IDs are marked used there so the storage later
   passes take is cleared for the next function.

Any failure (exec, status, parse, an object that cannot be rebuilt, the check) restores `f`
(fields saved before the import, aux mutations and `Dcl` additions undone) and is recorded as
an event; the stock passes then run.

**Type rounds.** The Lean passes read `types.(*Type).Compare` from the export's `typeorder`,
which only ranks the types of the export. When a run creates types (e.g. `opt` making `*byte`,
which `Compare` puts next to `*uint8`), the driver builds them in Go and runs the segment again
with them added to the export (`gofvExportWith`), up to 3 runs (`gofvTypeRounds`). Without
this, `generic cse` partitions differently in 26 corpus functions.

### Modes and settings

| Variable | Meaning |
| --- | --- |
| `GOFV_SSA_DRIVER=<path>` | enable; path of `gofv-ssa-opt` |
| `GOFV_SSA_DRIVER_MODE=full` (default) | one segment from `number lines`; only a complete pipeline (`status ok`) is imported, anything else runs all stock passes |
| `GOFV_SSA_DRIVER_MODE=mixed` | every maximal run of ported passes is a segment (`--partial`): the state before an unported or failing pass is imported, the stock compiler runs that pass, and the next ported pass starts a new segment |
| `GOFV_SSA_DRIVER_PKG`, `GOFV_SSA_DRIVER_FUNC` | regexps selecting packages / `<pkgpath>.<f.Name>` (default all) |
| `GOFV_SSA_DRIVER_STATS=<file>` | append one line per function: `"<pkg>" "<func>" <abi> lean=<n> stock=<n>` and one field per event (`unported "<pass>"`, `error "<pass>: <msg>"`, `import "<reason>"`, `exec`, `parse`), tab-separated |
| `GOFV_SSA_DRIVER_DUMP=<dir>` | write each run's input and output (debugging) |

Do not combine with `GOFV_SSA_EXPORT` (its sections are written only after stock passes).

## Whole-pipeline parity (`gofv-ssa-opt --check`)

Per-pass parity (`docs/PARITY.md`) replays each pass on the stock input. `--check` chains the
Lean results instead: it starts from section 0 with what the driver exports (section 0's
definitions, the type order and `typecmp` exceptions restricted to those types, and the frontend
closure the exporter's `frontend` block computes for them), runs the pipeline, and compares the
state after every pass with the stock section of that pass (objects not in section 0 are paired
by `renumber`'s canonical walk, so the Lean numbering of new objects is free). The chain also
checks the pass sequence (the stock file must have a section for exactly the enabled passes). It
runs the type rounds as the driver does. Outcomes per function: identical to the end, identical
up to the first unported pass, first divergence at a pass, or a Lean pass error.

- `--mixed` simulates `GOFV_SSA_DRIVER_MODE=mixed`: an unported pass is taken from the stock file
  (its output section and the tables in force there) and the chain continues.
- `--whole-file-env` uses the per-pass parity environment (the whole file's type order and
  frontend), to separate divergences caused by the driver's narrower view from chain effects.

`sccp` is documented as nondeterministic (permutations across runs); divergences at `sccp` are
reported separately.

## Results

See issue #12 for the latest numbers (corpus `gofv-corpus/2aae1000ea1d/plain`).
