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

## Registering a pass

A port is a `GoFV.Opt.Pass` (`PassEnv → Func → Except String PassOut`; `Pass.ofFunc` for
passes that do not create definitions). Add one `PassEntry` to
`GoFVTest/Parity/Registry.lean`: `fn` (the Go function), `names` (the stock names of its
pipeline instances) and, for passes the driver can disable, `disabled`. A pass that creates
types, aux objects or slots returns them in `PassOut.tables` at fresh numbers (and mutated
objects as redefinitions at their own numbers).

## Results

Corpus `gofv-corpus/2aae1000ea1d/plain` as regenerated with the #52 fix (types keyed by
`String()` too; 9,297 functions):

| pass | fn | functions | match | mismatch | parity | notes |
| --- | --- | ---: | ---: | ---: | ---: | --- |
| number lines | numberLines | 9297 | 9297 | 0 | 100% | corpus regenerated with raw stmt bits (export fix) |
| early phielim and copyelim | copyelim | 9297 | 9297 | 0 | 100% | |
| early deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| short circuit | shortcircuit | 9297 | 9297 | 0 | 100% | 4662 functions changed by the pass |
| decompose user | decomposeUser | 9297 | 9297 | 0 | 100% | 1133 functions changed by the pass, 1091 get new slots (`SplitSlot`) |
| pre-opt deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| opt deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| generic cse | cse | 9297 | 9293 | 4 | 99.95% | 4324 functions changed by the pass; all 4: export gap #68 (`Type.Compare` not a total preorder: `*byte` CMPeq `*uint8`) |
| phiopt | phiopt | 9297 | 9297 | 0 | 100% | 214 functions changed by the pass |
| gcse deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| known bits | knownBits | 9297 | 9297 | 0 | 100% | 35 functions changed by the pass |
| generic deadcode | deadcode | 9297 | 9297 | 0 | 100% | |
| opt | opt | 9297 | 9285 | 12 | 99.87% | all 12: export gap #62 (nested generic dictionaries reached by `rewriteFixedLoad`) |
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
| dead auto elim | elimDeadAutosGeneric | 9297 | 9297 | 0 | 100% | stock pass changes 355 functions |
| late fuse | fuseLate | 9297 | 9297 | 0 | 100% | 1381 functions changed by the pass (81 need `fuseBranchRedirect`, prove's facts table) |
| dse | dse | 9297 | 9297 | 0 | 100% | stock pass changes 447 functions |
| memcombine | memcombine | 9297 | 9297 | 0 | 100% | stock pass changes 181 functions |
| writebarrier | writebarrier | 9297 | 9297 | 0 | 100% | 967 functions get barriers; 20 take a `type:T` symbol first defined in this section from `PassEnv.frontend` |
| insert resched checks | insertLoopReschedChecks | — | — | 0 | disabled in 9297 | `exp.preemptibleloops 0` |
| cpufeatures | cpufeatures | — | — | 0 | disabled in 9297 | `exp.simd 0` |
| rewrite tern | rewriteTern | — | — | 0 | disabled in 9297 | `exp.simd 0` |
