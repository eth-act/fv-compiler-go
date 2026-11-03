# Contract: the Lean SSA IR (`GoFV.SSA`)

Owner: LeanIR (issues #6, #21). Consumers: every pass port (G4), the rule interpreter (G3),
the semantics (G5) and the proofs (G6). Input format: `docs/contracts/export.md` (`gofv-ssa`).

## Modules

| Module | Content |
| --- | --- |
| `GoFV.SSA.OpInfo` | `AuxType` (Go `aux*` constants, same order), `SymEffect`, `RegMask`, `RegIdx` (`inputInfo`/`outputInfo`), `RegInfo`, `Register` |
| `GoFV.SSA.Op` | **generated** by `scripts/gen-ops.sh` (`tools/opsgen`): `Op`, `BlockKind` and their `opcodeTable`/`blockData` metadata |
| `GoFV.SSA.OpARM64` | **generated**: per-op `Op.regInfo`, `Op.asm`, `Op.scale` (the backend fields of `opcodeTable`) |
| `GoFV.SSA.RegARM64` | **generated**: `ARM64.registers` (`registersARM64`: number, name), `paramIntReg`/`paramFloatReg`, `gpRegMask`/`fpRegMask`/`simdRegMask`/`specialRegMask`, `framepointerReg`, `linkReg`; imports only `OpInfo` |
| `GoFV.SSA.GoStr` | `GoStr`: Go strings as bytes, with the export's quoting |
| `GoFV.SSA.Pos` | `Pos` (`src.XPos`, raw `lico` fields), `PosBase`; `isStmt`/`withStmt` with Go's `lico == 0` rules, `sameFileAndLine` |
| `GoFV.SSA.Type` | `TypeRef`, `TypeKind`, `TypeFlags`, `Field`, `TypeTail`, `TypeDef` |
| `GoFV.SSA.AuxData` | `AuxRef`, `SlotRef`, `AuxDef`/`AuxKind` (`*ir.Name`, `*obj.LSym`, `*AuxCall`, …), `SlotDef` |
| `GoFV.SSA.Value` | `ID`, `Value` |
| `GoFV.SSA.Block` | `BranchPrediction`, `Edge`, `Block` |
| `GoFV.SSA.Func` | `Func`, `Caches`, `SplitKey`, `SdomNode`, `LineRange` |
| `GoFV.SSA.Export` | `ExportFile`, `Section`, `Def`, `Token`, `Tables` |
| `GoFV.SSA.Parse` | `parseExport : ByteArray → Except String ExportFile` |
| `GoFV.SSA.Print` | `printExport : ExportFile → String` (inverse of `parseExport`) |
| `GoFV.SSA.Live` | `Func.reachableBlocks`, `Func.liveValuesOrder`/`liveValues` (ports of `deadcode.go`'s `ReachableBlocks`/`liveValues`, with `liveOrderStmts`) |
| `GoFV.SSA.FmtFloat` | Go's `%g` for `float64` (exact shortest digits) |
| `GoFV.SSA.GoString` | `GoString.funcString`, `ExportFile.goString`: Go's `f.String()` |
| `GoFV.SSA.Alloc` | `newValue`/`newValueArgs`/`newBlock` (free lists first), `freeValue`/`freeBlock`, `unCache`, `setArg*`/`addArg*`/`resetArgs`/`resetValue`/`copyOf`, block controls (`setControl`, `replaceControl`, `resetBlock`, `resetWithControl*`, …), `truncateValues`, `invalidateCFG` (`func.go`, `value.go`, `block.go`) |
| `GoFV.SSA.Edges` | `addEdgeTo`, `removePred`/`removeSucc`/`removeEdge`, `removePhiArg` + `phielimValue`, `swapSuccessors*` (no cache invalidation, as in Go) |
| `GoFV.SSA.ConstCache` | `constVal` and the `Const*` constructors (`f.constants`, magic keys) |
| `GoFV.SSA.XPosMap` | `xposmap`/`biasedSparseMap` (`f.cachedLineStarts` as a pass's `pendingLines`), `ofCache`/`toCache` |
| `GoFV.SSA.TypeCmp` | `TypeOrder`: `types.(*Type).Compare` as a rank from `typeorder` |
| `GoFV.SSA.TypeNew` | `Tables.ptrTo` (`types.NewPtr`), `Tables.newResults` (`types.NewResults`): existing entry by export identity key, else a new definition at a fresh number; `Tables.typeEq` (`Compare == CMPeq` including such new types) |
| `GoFV.SSA.ABI` | `ABIConfig` (`config abi0`/`abi1`), `AuxCall`/`ABIParamAssignment` queries (`inParam`/`outParam`, `offsetOfResult`/`offsetOfArg`, `frameOffset`), `argOpAndRegisterFor`, `regCounts` (`Type.Registers`), `numParamRegs`, `registerTypes` (`abi.RegisterTypes`), `canSSA` |
| `GoFV.SSA.StoreOrder` | `storeOrder` (`schedule.go`), `Tables.isMemory` |
| `GoFV.SSA.Analysis.*` | `Postorder` (`postorderWithNumbering`), `Dom` (`dominatorsLTOrig`), `SparseTree` (`newSparseTree`, `isAncestorEq`), `CfgCache` (`Func.postorder`/`idom`/`sdom`: the cached accessors) |

`GoFV.SSA.Op` imports only `OpInfo`; data modules import only what they use. Nothing in
`GoFV.SSA` imports the umbrella `GoFV`.

## Ops and block kinds

- `Op` has one constructor per generic and ARM64 op, named as Go's constant without the `Op`
  prefix (`OpAdd64` ↔ `Op.Add64`, `OpARM64MOVDload` ↔ `Op.ARM64MOVDload`), in `opcodeTable`
  order: `Op.Invalid` first (`OpInvalid`), then the 354 ARM64 ops, then the 445 generic ops, so
  `ctorIdx` orders ops as Go's opcode numbers do (CSE sorts by op). The other archs and the
  SIMD ops (`simdgenericOps.go`, `simdARM64ops.go`) are not included: the SIMD ops exist only
  under `GOEXPERIMENT=simd`, which the corpus does not use; parsing one fails ("unknown op").
  `scripts/gen-ops.sh` checks every op, flag and register table against the pinned `opGen.go`.
- Metadata are `match` functions, one per `opInfo` field: `Op.name` (`Op.String()`: `"ADD"` for
  `OpARM64ADD`), `archName` (`"ARM64"` or `""`), `exportName` (`archName ++ name`, the export's
  spelling, unique), `generic`, `argLen` (−1 = variadic), `auxType`, `typ` (default result type
  as written in `_gen`), `symEffect`, and each Bool field (`commutative`, `resultInArg0`,
  `clobberFlags`, `call`, `nilCheck`, `faultOnNilArg0`, …). `Op.all` lists every op.
  `Op.goNum` is Go's opcode value in the pinned `opGen.go` (it differs from `ctorIdx` because
  of the left-out archs and SIMD ops; an `auxType = .CCop` AuxInt holds it), `Op.ofGoNum?` its
  inverse.
- `BlockKind` likewise (`BlockIf` ↔ `BlockKind.If`, `BlockARM64EQ` ↔ `BlockKind.ARM64EQ`), with
  `name`, `archName`, `exportName`, `controls`, `auxIntType`, `aux`, `goNum`/`ofGoNum?`.
- Proofs: evaluate metadata on concrete ops with `decide`/`rfl`. Avoid `simp [Op.argLen]` on
  an op variable: it generates the equation lemmas of an 800-arm `match` (quadratic, see the
  `lean-proof-performance` skill); case on the op or state per-op lemmas instead. A statement
  about all ops must account for the ARM64 ops (e.g. `nilCheck` holds for `NilCheck` and
  `ARM64LoweredNilCheck`).

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
  (Go's free lists as `List ID`, head first: the IDs `newValue`/`NewBlock` reuse), `names`
  (`f.Names` with `f.NamedValues`), `namedx`, `splits`, `canon`, `consts` (`f.constants`) and
  `cache` (the `f.cached*` analyses and `auxmap`, which survive between passes; `idom` and
  `sdom` are indexed by block ID like Go's slices, the printer projects them on `f.Blocks`;
  read them through `GoFV.SSA.Analysis.CfgCache`, drop them with `invalidateCFG`).
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
