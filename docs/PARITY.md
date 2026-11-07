# Per-pass stock parity

The oracle of `docs/PLAN.md` §2: every Lean pass port must produce exactly what the stock
`go1.27.3` pass produces from the same input — same value and block IDs, same order, same aux,
positions, `Uses`, free lists, constant cache and CFG caches.

## How it is checked

`lake exe pass-parity` (`GoFVTest/Parity/Main.lean`) reads `gofv-ssa` export files
(`docs/contracts/export.md`). For each file and each section `k ≥ 1` whose pass name is a
selected stock pass:

1. take section `k-1`'s function and the definition tables in force for it (definitions of
   sections `0..k-1`);
2. run the Lean port with a `PassEnv` (`GoFV/Opt/Pass.lean`: stock pass name, header, `config`
   lines, `typs`, type order, tables, and `frontend`: the whole file's definitions, from which
   a pass takes the contents of symbols it obtains from the frontend instead of computing
   them — `fe.Syslook`, `reflectdata.TypeLinksym`, relocation targets — by name
   (`PassEnv.frontendSym?`); never function state);
3. compare the result with section `k`: structural equality first, else both functions are
   printed with the export printer (`Print.func`) and must be byte-identical. Objects the pass
   created (types, aux, slots at fresh numbers) are first paired with section `k`'s new
   definitions and renamed (below); each pair, and every object redefined on either side, must
   have the same definition.

**New objects** (`GoFVTest/Parity/Renumber.lean`). A pass numbers the objects it creates
itself (any numbers past the input tables); the export numbers them while writing section `k`.
The harness walks both functions canonically — the function in print order (`f` line, block
aux, value type and aux, names, `namedx`, `splits`, `canon`, `auxmap`), then breadth first
through the references inside the new and the redefined definitions — and pairs the new
references of each kind by position. Two results that are equal up to renaming give
corresponding walks, so any real difference shows up as a definition or function mismatch.
`--check-renumber` adds a self-check instance: for every section that defines objects, the
stock output with its new objects moved to fresh numbers must compare equal (14,301 sections of
8,067 functions on the corpus, all equal). Position bases are compared at equal numbers (no
pass creates them).

A mismatch reports the file, the section and the first differing line of the printed function
(or the pass's error). A pass whose Go `disabled` condition holds (e.g. `insert resched checks`
without `GOEXPERIMENT=preemptibleloops`) is checked to have no section in that file.

**Randomized map order (`sccp`).** Stock `sccp` is nondeterministic: `replaceConst` ranges over
the Go map `latticeCells` (`docs/PASSES.md` §3). The port (`GoFV/Opt/Sccp.lean`) is
deterministic and ranges over the keys in insertion order. Only one effect of the order is
observable: when the rewiring of two or more *different* constant controls removes edges into
the same block `c`, the swap-removes leave `c.Preds` — and, by the same permutation, the
arguments of `c`'s phis and the back indices `Succs[k].i` of `c`'s predecessors — in an order
that depends on the map order (value resets, rewires of different blocks and phis turned into
copies or constants commute). Go's possible orders, by `internal/runtime/maps` (`Iter.Init`/
`Next`, `putSlotSmall`): for at most 8 keys (one group, slots filled in insertion order,
iteration from a random slot with wrap-around) exactly the rotations of the insertion order;
for more keys the order follows the keys' address hashes under a random per-map seed, which
the harness treats as any order (a superset). Measured with the host toolchain on
`map[*V]lattice` (2,000 trials per size): sizes 2–8 gave exactly the n rotations, size 9 gave
1,096 distinct orders (74 rotations), size 10 1,492. A registered pass may carry a `replay`
(`PassEntry.replay`): when the deterministic result differs, the harness runs it with the stock
output and compares its result exactly again; a match is counted in the "order replayed"
column. For `sccp` (`GoFV/Opt/SccpReplay.lean`), the replay simulates the edge removals of
each contested block on its initial predecessor list, finds an admissible order (a rotation
for small maps; for large maps a combination of per-block relative orders consistent with one
global order) that yields the stock `Preds` of every contested block, and reruns
`replaceConst` in that order. So a section counts as a match iff the port, run with an
admissible order of `latticeCells`, gives exactly the stock output; everything else (lattice,
fold temporaries, IDs, resets, rewires) is still compared exactly.

The quick corpus has no contested block (`sccp` folds in 25 functions and rewires in 20, never
two values into one block). `tests/sccp-order/run.sh [n] [go-build]` exports a program that
has one `n` times and runs the check: 16 stock exports split 8/8 between the two predecessor
orders, and all match (8 by replay).

**`regalloc`: copy deletion and new autos.** Stock `regalloc` also ranges over a Go map (`s.copies`,
"Erase any copies we never used"): the set of freed copies is the same fixed point in every
order, only the free list order differs, and from `regalloc` on the export writes `freev`
sorted (`docs/contracts/export.md`, "Format 5"); the port (`GoFV/Opt/Regalloc.lean`) sweeps the
copies by ascending ID and returns the free list sorted, so no replay is needed. `stackalloc` and
the edge shuffle create autos with `f.NewLocal`, named `.autotmp_<len(curfn.Dcl)>` by the
frontend. The pass takes `len(curfn.Dcl)` as `PassEnv.dclLen`, and the harness sets it to the
input section's `dcllen` (format 5.1, `docs/contracts/export.md`; 0 in older files). The `regalloc` line's slots are part of
the renumbering walk (`Renumber.funcRefs`).

Files are processed one at a time per worker (`--jobs N` workers, round robin), so memory stays
constant: the whole corpus (9,297 files, 1.25 GB) runs in about 25 s with 4 jobs and 130 MB.

```
lake exe pass-parity [--pass <fn|stock name|all>]... [--jobs N] [--max-report N] [--table FILE] [--check-renumber] <dir|file>...
```

- `--pass`: a Go function name selects all its instances (`deadcode` → the five deadcode
  passes), a stock name selects one (`"opt deadcode"`); default all registered passes.
- `--max-report`: mismatch reports printed per pass instance (default 10); counts are always
  complete.
- `--table`: also write the summary table (markdown) to a file.
- Exit status 1 on any mismatch, pass error, parse error, or when no file was read.

`scripts/parity.sh [--corpus quick|full] [-j jobs] [-o out.md] [-p pass]... [corpus...]` builds
the tool, runs every registered pass over the corpus (default: the newest
`../gofv-corpus/<pin12>/plain`) through `memcap`, and writes the table to `tmp/parity.md` and
the mismatch reports to `tmp/parity.md.log`. `--corpus full` selects the nightly corpus
`../gofv-corpus/<pin12>/full/plain` (all of `go list std` and `go list cmd`, issue #63;
`scripts/export-corpus.sh --corpus full`).

## Corpus versions

Corpora live outside git in `../gofv-corpus/<pin12>/` and are never modified in place: other
agents read them while new versions are made. `scripts/export-corpus.sh` writes every export to
a new version directory `quick-v<N>/` or `full-v<N>/` (`plain/`, `*.tar.zst`, `manifest.txt`,
`stats.txt`, `determinism.diff`), and then publishes it by renaming a new symlink over the
published name, so a reader sees either the old or the new version, never a mix:

| published path | points to |
| --- | --- |
| `../gofv-corpus/<pin12>/plain` | `quick-v<N>/plain` (the per-PR gate) |
| `../gofv-corpus/<pin12>/full` | `full-v<N>` (the nightly gate; read `full/plain`) |

`../gofv-corpus/<pin12>/CURRENT` holds one line per kind (`quick quick-v<N>`, `full full-v<N>`).
`scripts/parity.sh` prints it, and the version directory each corpus argument resolves to, under
the table. A version that is not deterministic (with `--check-determinism`) is never published.
The previous version is kept: a switch writes the time into the old version's `RETIRED` file,
and later switches delete versions retired more than 24 hours ago. Long runs that must not see
a switch should read a version directory (`readlink -f ../gofv-corpus/<pin12>/plain`) instead
of the published name.

Disk: `--check-determinism` compares the second export set by set and deletes each set after its
comparison, so it never holds two full copies; `--link-from <version>` (e.g. `full-v9`) replaces
every dump whose sha256 equals the same path in that version by a hard link and records the
counts in the manifest's `link` lines (full-v10: only the cmd corpus's own `cmd/compile` and
`cmd/internal/obj` functions, which change with the exporter patch, cost new space, #547).
`--switch … --keep-retired` publishes without deleting old versions.

Format changes: export with `--no-switch` (the new version is written but not published), merge
the PR whose parser reads the new format, then publish with
`scripts/export-corpus.sh --switch quick-v<N>` (and `full-v<N>`). Every switch is announced to
all agents with the format changes.

## Registering a pass

A port is a `GoFV.Opt.Pass` (`PassEnv → Func → Except String PassOut`; `Pass.ofFunc` for
passes that do not create definitions). Add one `PassEntry` to
`GoFVTest/Parity/Registry.lean`: `fn` (the Go function), `names` (the stock names of its
pipeline instances) and, for passes the driver can disable, `disabled`. A pass that creates
types, aux objects or slots returns them in `PassOut.tables` at fresh numbers (and mutated
objects as redefinitions at their own numbers). A pass whose stock result depends on Go's
randomized map iteration sets `replay` (above); no other pass may.

## Results

Corpus `gofv-corpus/2aae1000ea1d/plain` as regenerated with the #52 fix (types keyed by
`String()` too; 9,297 functions). Latest run (#386, export format 5.1, after the #426 fix):
every registered pass is at 100% on quick-v7 (9,297 functions) and on full-v9 (96,560
functions), 0 mismatches and 0 pass errors on both; `ssa-roundtrip` has 0 failures on both.

| pass | fn | functions | match | mismatch | parity | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| number lines | numberLines | 9297 | 9297 | 0 | 100% | corpus regenerated with raw stmt bits (export fix) |
| early phielim and copyelim | copyelim | 9297 | 9297 | 0 | 100% | |
| early deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| short circuit | shortcircuit | 9297 | 9297 | 0 | 100% | 4662 functions changed by the pass |
| decompose user | decomposeUser | 9297 | 9297 | 0 | 100% | 1133 functions changed by the pass, 1091 get new slots (`SplitSlot`) |
| pre-opt deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| opt deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| generic cse | cse | 9297 | 9297 | 0 | 100% | 4324 functions changed by the pass; 99.95% before the `typecmp` exceptions (#68: `Type.Compare` is not a total preorder, `*byte` CMPeq `*uint8`) |
| phiopt | phiopt | 9297 | 9297 | 0 | 100% | 214 functions changed by the pass |
| gcse deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| known bits | knownBits | 9297 | 9297 | 0 | 100% | 35 functions changed by the pass |
| generic deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| opt | opt | 9297 | 9297 | 0 | 100% | before the #62 export fix: 12 mismatches (nested generic dictionaries reached by `rewriteFixedLoad`) |
| middle opt | opt | 9297 | 9297 | 0 | 100% | |
| late opt | opt | 9297 | 9297 | 0 | 100% | |
| divisible | divisible | 9297 | 9297 | 0 | 100% | |
| divmod | divmod | 9297 | 9297 | 0 | 100% | |
| zero arg cse | zcse | 9297 | 9297 | 0 | 100% | before the #52 export fix: 84 mismatches (`byte`/`uint8` type pointers) |
| nilcheckelim | nilcheckelim | 9297 | 9297 | 0 | 100% | stock pass changes 5008 functions (incl. `storeOrder` reorders) |
| prove | prove | 9297 | 9297 | 0 | 100% | stock pass changes 7507 functions (incl. T2 value sorting); branches removed in 1255, downward-loop inversion in 64, `Mul`→`CondSelect` in 54, `Slicemask`→const in 111, signed→unsigned `Div` in 86 |
| early fuse | fuseEarly | 9297 | 9297 | 0 | 100% | 1576 functions changed by the pass |
| expand calls | expandCalls | 9297 | 9297 | 0 | 100% | files with `InterLECall` 766, `ClosureLECall` 359, `TailLECall` 164, `TailLECallInter` 4, `Dereference` 185, `ArgFloatReg` (output) 204; no `SelectNAddr` |
| decompose builtin | postExpandCallsDecompose | 9297 | 9297 | 0 | 100% | 5327 functions changed by the pass, 2897 get new slots; `namedx` present in 1001 |
| softfloat | softfloat | 9297 | 9297 | 0 | 100% | `config softfloat 0`: identity |
| branchelim | branchelim | 9297 | 9297 | 0 | 100% | 526 functions changed by the pass |
| check bce | checkbce | 9297 | 9297 | 0 | 100% | identity |
| sccp | sccp | 9297 | 9297 | 0 | 100% | stock pass changes 1163 functions (fold temporaries in all; folds in 25, rewires in 20); 0 sections need the map order replayed (no contested block); `tests/sccp-order` (16 exports, split 8/8 between the two orders): 48/48, 8 replayed |
| dead auto elim | elimDeadAutosGeneric | 9297 | 9297 | 0 | 100% | stock pass changes 355 functions |
| late fuse | fuseLate | 9297 | 9297 | 0 | 100% | 1381 functions changed by the pass (81 need `fuseBranchRedirect`, prove's facts table) |
| dse | dse | 9297 | 9297 | 0 | 100% | stock pass changes 447 functions |
| memcombine | memcombine | 9297 | 9297 | 0 | 100% | stock pass changes 181 functions |
| writebarrier | writebarrier | 9297 | 9297 | 0 | 100% | 967 functions get barriers; 20 take a `type:T` symbol first defined in this section from `PassEnv.frontend` |
| insert resched checks | insertLoopReschedChecks | — | — | 0 | disabled in 9297 | `exp.preemptibleloops 0` |
| cpufeatures | cpufeatures | — | — | 0 | disabled in 9297 | `exp.simd 0` |
| rewrite tern | rewriteTern | — | — | 0 | disabled in 9297 | `exp.simd 0` |
| lower | lower | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 9057 functions changed by the pass; full-v6: 96,553/96,553 |
| late lower | lateLower | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 3985 functions changed by the pass; full-v6: 96,553/96,553 |
| addressing modes | addressingModes | 9297 | 9297 | 0 | 100% | identity on arm64; full-v6: 96,553/96,553 |
| pair | pair | 9297 | 9297 | 0 | 100% | quick-v5; 2917 functions changed by the pass (5,269 load pairs, 7,052 store pairs); full-v6: 96,553/96,553 (44,081 changed); the load sort numbers auxes inside the comparator: `GoFV.Util.PdqSortM` (pdqsort with a stateful comparator, checked against Go by `scripts/util-difftest.sh`) |
| lowered deadcode for cse | deadcode | 9297 | 9297 | 0 | 100% | quick-v5; 3589 functions changed by the pass; full-v6: 96,553/96,553 (44,552 changed) |
| lowered cse | cse | 9297 | 9297 | 0 | 100% | quick-v5; 7618 functions changed by the pass (incl. `auxmap` only); full-v6: 96,553/96,553 (90,889 changed); `cse` unchecked (`loweredCsePass`) |
| elim unread autos | elimUnreadAutos | 9297 | 9297 | 0 | 100% | quick-v5; 136 functions changed by the pass; full-v6: 96,553/96,553 (397 changed) |
| tighten tuple selectors | tightenTupleSelectors | 9297 | 9297 | 0 | 100% | quick-v5; 7 functions changed by the pass; full-v6: 96,553/96,553 (99 changed) |
| lowered deadcode | deadcode | 9297 | 9297 | 0 | 100% | quick-v5; 1231 functions changed by the pass; full-v6: 96,553/96,553 (12,652 changed) |
| checkLower | checkLower | 9297 | 9297 | 0 | 100% | identity (no function fails); full-v6: 96,553/96,553 |
| loop invariant | licm | 9297 | 9297 | 0 | 100% | quick-v5; 271 functions changed by the pass (full-v6: 3822); full-v6: 96,553/96,553 |
| late phielim and copyelim | copyelim | 9297 | 9297 | 0 | 100% | quick-v5; identity on both corpora (`lowered deadcode` already ran copyelim); full-v6: 96,553/96,553 |
| tighten | tighten | 9297 | 9297 | 0 | 100% | quick-v5; 3600 functions get values moved (full-v6: 46,639), every function gets idom/loopnest caches; full-v6: 96,553/96,553 |
| late deadcode | deadcode | 9297 | 9297 | 0 | 100% | quick-v5; 14 functions changed (full-v6: 152); full-v6: 96,553/96,553 |
| critical | critical | 9297 | 9297 | 0 | 100% | quick-v5; 2740 functions get splitter blocks (full-v6: 34,419); full-v6: 96,553/96,553 |
| phi tighten | phiTighten | 9297 | 9297 | 0 | 100% | quick-v5; 423 functions changed (full-v6: 7535); full-v6: 96,553/96,553 |
| likelyadjust | likelyadjust | 9297 | 9297 | 0 | 100% | quick-v5; 3282 functions get predictions (full-v6: 39,329); reads the cached, possibly stale postorder and loop nest; full-v6: 96,553/96,553 |
| layout | layout | 9297 | 9297 | 0 | 100% | quick-v5; block order changed in 4228 functions (full-v6: 51,667), `laidout` set in all; full-v6: 96,553/96,553 |
| schedule | schedule | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); every function changes (`fstate scheduled`); full-v6: 96,553/96,553 |
| late nilcheck | nilcheckelim2 | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 3311 functions changed by the pass; removed checks leave the value table unfreed; full-v6: 96,553/96,553 |
| flagalloc | flagalloc | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 415 functions changed by the pass; full-v6: 96,553/96,553 |
| regalloc | regalloc | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); every function changes (`f.RegAlloc`); full-v6: 96,553/96,553; `PassEnv.dclLen` from the input section's `dcllen` (above): quick-v7 9,297/9,297, full-v9 96,560/96,560 (format 5.1) |
| loop rotate | loopRotate | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 1672 functions changed by the pass; `f.loopnest()` (`Func.loopnest`; regalloc left it cached in every input); full-v6: 96,553/96,553 |
| trim | trim | 9297 | 9297 | 0 | 100% | quick-v5 (format 5); 2780 functions changed by the pass; `flagslive`/`hotness` list blocks of `f.Blocks` only, so a trimmed block's entries go; full-v6: 96,553/96,553 |

## Phase 3: genssa (I3, #549)

`lake exe gen-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`
(`GoFVTest/GenParity.lean`) checks the Lean port of `AllocFrame` … `defframe` (`GoFV/Gen/*`,
`docs/PASSES3.md` A1–C6). For every `.prog` file (`gofv-prog 3`) with its `.ssa` file, the
input is the function after `trim` plus the `.prog` file's `frame` input (`in` lines) and
`genin` section (`GoFV.Gen.Env.load`); it compares, per function:

1. **frame** (A1 MergeLocals, A2 AllocFrame): `allocFrame` against the `frame` section's
   `out`, `opt`, `merge` and `stack` lines;
2. **f.RegArgs** (A3): `regArgsOf` against `genin`'s `regargs` (types by `String()`);
3. **prog0** (B1 liveness, B2 ArgLiveness, B3 ArgInfo/WrapInfo, C1 objw, C2 genssa loop, C3
   arm64 `ssaGenValue`, C4 `ssaGenBlock`, C5 inline marks/branches/jump tables, C6
   `defframe`): `genssa`, run on the exported frame, against the `prog0` section — every Prog
   (stable ID = allocation order, list order, every field, symbols by name and ABI), the
   `FuncInfo` records (spills, inline marks, jump tables, `funcaux`), `needzero`, the remaining
   `f.RegArgs`, and the contents (kind, size, alignment, attributes, bytes, relocations) of the
   metadata symbols (`gclocals·…`, `.stkobj`, `.opendefer`, `.arginfo<abi>`, `.argliveinfo`,
   `.wrapinfo`) against the `asm` section's `data` lines.

Mismatches are reported with a class (first differing item: `frame:dcl`, `prog:<field>:<as>`,
`funcinfo:…`, `sym:<part>:<symbol>`, `needzero`, or a port error `<stage>:error:<construct>`).

Result on quick-v9 (9,297 functions, 429,130 prog0 Progs):

| cut | functions | match | mismatch | parity |
| --- | ---: | ---: | ---: | ---: |
| frame (A1, A2) | 9297 | 9297 | 0 | 100% |
| f.RegArgs (A3) | 9297 | 9297 | 0 | 100% |
| prog0 (B1–C6) | 9297 | 9297 | 0 | 100% |
| end to end | 9297 | 9297 | 0 | 100% |

No mismatch class remains. Notes: Go's possible map-order nondeterminism in MergeLocals (two
candidates tying under `nameLess` after eviction, `docs/PASSES3.md` §3) is detected and
reported as a port error; it never occurs on quick-v9. Only 5 quick functions actually merge
stack slots, and the open-coded-defer paths occur in 135; the full corpus (needs a v2 export)
would exercise these more. The #541 `LoweredPanicBoundsCR` behaviour is reproduced.
Paths that never run for linux/arm64 or the corpus configuration fail loudly instead of being
approximated: MergeLocals hash bisection (`mergelocalshash` non-empty), `-clobberdead`.

## Phase 3: assembler (I4, #550)

`lake exe asm-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`
(`GoFVTest/AsmParity.lean`) checks the Lean port of `Flushplist` (`GoFV/Asm/*`,
`docs/PASSES3.md` D1–D7): `GoFV.Asm.flush` runs, on the `prog0` section of a `.prog` file
(P0), `linkpatch` with `progedit` and `preprocess` (`Obj7`), `span7` with `oplook`/`aclass`
(`Aclass`), literal pools and long-branch veneers (`Span7`), the `asmout` cases (`Asmout`,
`AsmoutA`, `AsmoutB`, helpers `Asm7Ops`; optab in `buildop`'s sorted order generated into
`Optab.lean` by `tools/asgen`), `MarkUnsafePoints` and `linkpcln` (`Pcln`), and the `Compile`
tail's `weakenGlobalMapInitRelocs`. It compares with the `asm` section (M), per function:

1. **Prog list**: every Prog in order with every field (`Pc`, `Spadj`, `Isize`, `Optab`, `Pool`,
   operands with cached classes, `Mark`, positions; Progs the assembler adds are numbered in
   list order from one past the largest `prog0` ID, as the exporter numbers them);
2. **FuncInfo**: `Args`, `Locals`, `FuncFlag`, attributes (`NOFRAME`, `NOSPLIT`, `LEAF` set by
   `preprocess`), spills, inline marks, jump tables, funcaux symbols;
3. **text**: `Size`, `Align`, the bytes of `P` (a mismatch names the stock Prog and its asmout
   case) and `R` in append order;
4. **pc tables**: the contents of pcsp, pcfile, pcline, pcinline and every pcdata table, the
   funcdata slots, `UsedFiles` and the local inlining tree;
5. **data**: the `$f32.`/`$f64.`/`$i64.` constants `progedit` creates and the jump-table words.

Every comparison is exact: since `gofv-prog 3` the port starts from the text symbol's `R` at the
`prog0` cut (the zero-size marker relocations `R_USEIFACE`/`R_USEIFACEMETHOD`/`R_USENAMEDMETHOD`
that `walk`, `reflectdata` and the SSA rewrite rules put on the function before `Flushplist`
appends the assembler's) and from the recorded `LSym.Align` of the operands' symbols
(`Optab.size` picks the 12-byte `ADRP`+`ADD`+load form for a `C_ADDR` operand whose symbol is
under-aligned, e.g. a `.stmp_` symbol of alignment 1). Under `gofv-prog 2` the harness had to
accept these two differences as "explained" (quick-v9: 7,540 of 9,297 functions byte-exact;
full-v10: 68,260 of 96,634); the acceptance is gone.

Result on quick-v10 (9,297 functions, 570,997 asm Progs, 1,909,776 text bytes; 7 s with 8 jobs;
the export is deterministic under `--check-determinism`):

| cut | functions | match | mismatch | parity |
| --- | ---: | ---: | ---: | ---: |
| Prog list (D2–D6) | 9297 | 9297 | 0 | 100% |
| FuncInfo | 9297 | 9297 | 0 | 100% |
| text P/R (D4, D5) | 9297 | 9297 | 0 | 100% |
| pc tables, funcdata (D7) | 9297 | 9297 | 0 | 100% |
| constants, jump tables | 9297 | 9297 | 0 | 100% |
| end to end | 9297 | 9297 | 0 | 100% |

gen-parity on quick-v10: frame, f.RegArgs, prog0 and end to end 9,297/9,297 (100%).

Paths that compiled
linux/arm64 code does not take fail loudly rather than being guessed: `-dynlink`
(`rewriteToUseGot` needs symbol kinds the export does not record), `MRS`/`MSR` (asmout cases
35–37), SVE (case 127), a `//line` position base whose own position is not line 1 (pcline needs
`PosBase.Pos()`, which `gofv-prog 3` does not record). An infinite `JMP` loop (`brloop` gives up)
leaves the typed-nil target `AddrVal.nilTarget`, numbered like the exporter's fresh ID.

## Phase 3: debug information (I5, #551)

`lake exe dwarf-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`
(`GoFVTest/DwarfParity.lean`) checks the Lean ports of the writers of `populateDWARF`
(`GoFV/Dwarf/*`, `docs/PASSES3.md` E2): the line program `generateDebugLinesSymbol` with
`putpclcdelta` (`Lines`), and the DIE writer of `cmd/internal/dwarf` (`Die`: `PutAbstractFunc`,
`PutConcreteFunc`, `PutDefaultFunc`, scopes, variables with `putvarAbbrev`, inlined subroutines,
DWARF 5 range lists, and `ssa.FuncDebug.PutLocationListDwarf5`), on the records of the
`gofv-prog 3` `dwarf` section (`dwarf.FnState` before the DIE writer: variables, scopes, inlined
calls) and `prog0`'s `BuildFuncDebug` lists with their `GetPC` endpoints. Per function it
compares, byte for byte and relocation for relocation, the debug lines, debug info, location
list, range list and abstract-function symbols at the end of `Compile` and the child-DIE
references and offsets for the package's fixups (`dieref`, `dieoff`). DWARF constants are
generated into `GoFV/Dwarf/Const.lean` by `tools/asgen` (`scripts/gen-asm.sh`). In these rows the
info symbol's leading `R_USETYPE` relocations (`dwarfgen.Info`'s) are taken from the record.

Two more rows check `dwarfgen.Info` itself (`GoFV/Dwarf/Info.lean`: `createDwarfVars` with the
complex, simple and conservative variables, `sortDeclsAndVars`, `Autot` and the `R_USETYPE`
relocations, `findScope`/`assembleScopes`, `assembleInlines` with `makePreinlineDclMap`) on the
`dwarf` section's `dw*` inputs, `prog0`'s `FuncDebug`, `Autot` and marker relocations, the
frame's `OptDcl` and the final Progs: **Info records (E2)** compares its variables, scopes,
inlined calls (`==` on the section's `var`, `scope`, `inlcall` records) and `R_USETYPE`
relocations with the record; **Info → DIE chain** runs the writers on its records and compares
every DWARF symbol and the fixups as above.

Result on quick-v10 (9,297 functions with DWARF, 2,886,136 DWARF bytes; 6 s with 6 jobs; a
function without a location list, range list or abstract function counts as a match of that
row; the corpus takes the heap-dereference lists of conservative variables, the ABI0
sort-by-offset path of `scopeVariables`, closure offsets and `IsInAbstract` variables):

| symbol | functions | match | mismatch | parity |
| --- | ---: | ---: | ---: | ---: |
| debug lines | 9297 | 9297 | 0 | 100% |
| debug info | 9297 | 9297 | 0 | 100% |
| location lists | 9297 | 9297 | 0 | 100% |
| range lists | 9297 | 9297 | 0 | 100% |
| abstract function | 9297 | 9297 | 0 | 100% |
| child-DIE fixups | 9297 | 9297 | 0 | 100% |
| Info records (E2) | 9297 | 9297 | 0 | 100% |
| Info → DIE chain | 9297 | 9297 | 0 | 100% |
| end to end | 9297 | 9297 | 0 | 100% |

Not ported yet: the package-level abstract functions and fixups (`DwarfFixupTable.Finalize`).

`lake exe debug-parity [--jobs N] [--max-report N] [--table FILE] <dir|file>...`
(`GoFVTest/DebugParity.lean`) checks the Lean port of the optimized `ssa.BuildFuncDebug`
(`GoFV/Dwarf/Debug.lean`, `docs/PASSES3.md` E1: `PopulateABIInRegArgOps` with the slot
canonicalizer, the var/slot canonicalisation, `liveness`, `buildLocationLists`, the location
expressions; `ssagen.StackOffset` as the callback) on the function after `trim` and the exported
frame after `AllocFrame` (`frame` `out`/`opt` lines). It compares with `prog0`'s `dbg*` lines:
`EntryID`, `Slots` (name by `.ssa` aux link, type by `String()` and size, offset), `Vars` with
`VarSlots`, and every nonempty location list (SSA coordinates and expression bytes), exactly.
`RegOutputParams` (set by `buildssa`) and `GetPC` are not part of it. The IDs of the dead
`ArgIntReg`/`ArgFloatReg` values `PopulateABIInRegArgOps` synthesizes come from the free list,
which the export writes sorted after `regalloc`, so they may differ from Go's; they are not
observable in the result (zero-width, must-be-first values: their entries start at
`BlockStart`).

Result on quick-v10 (9,297 functions; 57,184 slots, 38,267 vars, 35,652 nonempty location lists
with 70,867 entries; 1,570 values synthesized in 1,150 functions; 99 s with 6 jobs under load):
9,297/9,297 (100%), no mismatch class.
