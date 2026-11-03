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
