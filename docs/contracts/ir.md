# Contract: the Lean SSA IR (`GoFV.SSA`)

Owner: LeanIR (issues #6, #21). Consumers: every pass port (G4), the rule interpreter (G3),
the semantics (G5) and the proofs (G6). Input format: `docs/contracts/export.md` (`gofv-ssa`).

## Modules

| Module | Content |
| --- | --- |
| `GoFV.SSA.OpInfo` | `AuxType` (Go `aux*` constants, same order), `SymEffect` |
| `GoFV.SSA.Op` | **generated** by `scripts/gen-ops.sh` (`tools/opsgen`): `Op`, `BlockKind` and their `opcodeTable`/`blockData` metadata |
| `GoFV.SSA.GoStr` | `GoStr`: Go strings as bytes, with the export's quoting |
| `GoFV.SSA.Pos` | `Pos` (`src.XPos`), `PosBase` |
| `GoFV.SSA.Type` | `TypeRef`, `TypeKind`, `TypeFlags`, `Field`, `TypeTail`, `TypeDef` |
| `GoFV.SSA.AuxData` | `AuxRef`, `SlotRef`, `AuxDef`/`AuxKind` (`*ir.Name`, `*obj.LSym`, `*AuxCall`, …), `SlotDef` |
| `GoFV.SSA.Value` | `ID`, `Value` |
| `GoFV.SSA.Block` | `BranchPrediction`, `Edge`, `Block` |
| `GoFV.SSA.Func` | `Func`, `Caches`, `SplitKey`, `SdomNode`, `LineRange` |
| `GoFV.SSA.Export` | `ExportFile`, `Section`, `Def`, `Token`, `Tables` |
| `GoFV.SSA.Parse` | `parseExport : ByteArray → Except String ExportFile` |
| `GoFV.SSA.Print` | `printExport : ExportFile → String` (inverse of `parseExport`) |
| `GoFV.SSA.Live` | `Func.reachableBlocks`, `Func.liveValues` (ports of `deadcode.go`'s `ReachableBlocks`/`liveValues`) |
| `GoFV.SSA.FmtFloat` | Go's `%g` for `float64` (exact shortest digits) |
| `GoFV.SSA.GoString` | `GoString.funcString`, `ExportFile.goString`: Go's `f.String()` |

`GoFV.SSA.Op` imports only `OpInfo`; data modules import only what they use. Nothing in
`GoFV.SSA` imports the umbrella `GoFV`.

## Ops and block kinds

- `Op` has one constructor per generic op, named as Go's without the `Op` prefix
  (`OpAdd64` ↔ `Op.Add64`), in `opcodeTable` order, `Op.Invalid` first (`OpInvalid`). The SIMD
  generic ops (`simdgenericOps.go`) are not included: they exist only under
  `GOEXPERIMENT=simd`, which the corpus does not use; parsing one fails ("unknown op").
- Metadata are `match` functions, one per `opInfo` field: `Op.name` (`Op.String()`),
  `argLen` (−1 = variadic), `auxType`, `typ` (default result type as written in `_gen`),
  `symEffect`, and each Bool field (`commutative`, `resultInArg0`, `call`, `nilCheck`,
  `hasSideEffects`, `zeroWidth`, `fixedReg`, …). `Op.all` lists every op.
- `BlockKind` likewise (`BlockIf` ↔ `BlockKind.If`), with `name`, `controls`, `auxIntType`.
- Proofs: evaluate metadata on concrete ops with `decide`/`rfl`. Avoid `simp [Op.argLen]` on
  an op variable: it generates the equation lemmas of a 446-arm `match` (quadratic, see the
  `lean-proof-performance` skill); case on the op or state per-op lemmas instead.

## Function representation

Choice: **IDs everywhere, Arrays indexed by ID** — the shape of Go's data (dense IDs from 1)
and of clifv's `Clif.Function` (IDs + lists), but with `Array` so passes run in compiled code at
Go-like cost.

- `Value`: `id`, `op`, `type : TypeRef`, `auxInt : Int64` (Go `int64`, wrapping arithmetic),
  `aux : Option AuxRef`, `pos`, `uses`, `args : Array ID`, `block : ID`.
- `Block`: `id`, `kind`, `pos`, `likely`, `auxInt : Int64`, `aux`, `controls : Array ID`
  (the non-nil `Controls`), `succs`/`preds : Array Edge` (`Edge = ⟨block ID, reverse index⟩`),
  `values : Array ID` (`b.Values` order).
- `Func`: `blocks : Array ID` (`f.Blocks` order), `blockTab : Array (Option Block)` and
  `valueTab : Array (Option Value)` indexed by ID (`none` = not in the function, e.g. freed),
  `entry`, `type`, `ownAux`, `vidLast`/`bidLast` (last IDs handed out), `freeValues`/`freeBlocks`
  (Go's free lists, head first: the IDs `newValue`/`NewBlock` reuse), `names`
  (`f.Names` with `f.NamedValues`), `namedx`, `splits`, `canon`, `consts` (`f.constants`) and
  `cache` (the `f.cached*` analyses and `auxmap`, which survive between passes).
  Accessors: `f.block? id`, `f.value? id`.
- Types, aux values, local slots and position bases are not stored in the `Func`: they are
  per-file tables (`Tables`, indexed by table number) that a section's definitions extend or
  redefine; `ExportFile.tablesAt k` gives the tables in force for section `k`. Two references
  are equal iff Go's objects are identical (`v.Aux == w.Aux`, `v.Type == w.Type`); the type
  order of `types.Compare` is the file's `typeOrder` (rank comparison).
- Go strings (symbol names, string constants, type strings) are `GoStr` (bytes): Go strings
  need not be UTF-8.
- What is redundant in Go stays redundant here and is checked, not recomputed: `uses`
  (equals the occurrences in args and controls), reverse edge indices, `value.block`.

Why this is provable: everything is a plain inductive/structure over `Nat`, `Int64`, `Array`,
`Option` with derived `DecidableEq`; IDs make sharing explicit (no pointers, no cycles), so
well-formedness is a decidable predicate (IDs in range, edges mutually inverse, each value in
exactly one block, `uses` correct) to be proven preserved per pass. Array lemmas (`getElem_set`,
`size_set`, …) are in core. For kernel evaluation (`decide +kernel` certificates), define the
scans to be evaluated over `List`s with `@[csimp]` swaps to the `Array` versions (LEARNINGS.md).

## Export parser and printer

- `parseExport` is strict: it accepts exactly the canonical text (`docs/contracts/export.md`:
  one space between tokens, canonical numbers and string escapes, flag lists in documented
  order, records in documented order and presence) and reports the first bad line otherwise.
- `printExport (parseExport x) = x` byte for byte on every accepted file; `lake exe
  ssa-roundtrip <dir>...` checks this for every `*.ssa` file below the directories.
- A pass port reads `sections[k-1].func` with `tablesAt (k-1)`, runs the pass, and compares its
  `Func` with `sections[k].func`; objects a pass creates are matched to section `k`'s new
  definitions by content (export.md, "Definitions").

## `f.String()`

`GoString.funcString name tables f` prints Go's `f.String()` (`print.go`, unscheduled order:
phis first, then dependency order; `DEAD` from the ported `findlive`), with `Value.LongString`
(`auxString`, including Go's `%g` for float aux values) and `Block.LongString`. Known
differences: (1) the export numbers types by identity, so a type Go spells through an alias
(`byte`/`uint8`, `rune`/`int32`, `any`/`interface {}`) has one spelling here; (2) `%q` of a
string aux keeps non-ASCII runes even where Go escapes non-printable ones. Export files written
with `GOFV_SSA_GOTEXT=1` carry Go's own text; `ssa-roundtrip` compares against it and counts
alias-only differences separately.
