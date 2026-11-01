# Performance tracking

`perf/` keeps the build cost of every Lean module and the runtime of the compiled Lean
executables, per commit. The profiler agent (issue #1) records main and every open PR and
comments on PRs that cross the thresholds below. Anyone can run the same scripts.

| Script | Does |
| --- | --- |
| `scripts/perf-record.py [TARGET...]` | builds module by module, appends one row per (commit, module) to `perf/history.tsv` |
| `scripts/perf-compare.py BASE HEAD` | Markdown report of regressions/wins between two recorded commits; exit 1 on a regression |
| `scripts/perf-explain.py MODULE` | names the slow declarations of one module (`trace.profiler`) |
| `scripts/olean-top.lean M.olean` | largest constants of an `.olean` (Expr nodes, string-literal bytes such as `bv_decide` certificates) |
| `scripts/perf-bench.py [NAME...]` | runs the executables listed in `perf/bench.tsv`, appends to `perf/bench-history.tsv` |
| `scripts/perf-graph.py COMMIT` | critical path (CPU) through the import graph and the costliest rebuild cones |
| `scripts/perf-watch.py` | one pass of the watch loop: records origin/main and open PR heads, writes compare reports |

All builds and runs go through `scripts/memcap.sh` (8G cap per module, shared Lake cache), one
module at a time; nothing starts while `MemAvailable` is below 10G.

## Recording

```sh
python3 scripts/perf-record.py                 # every lean_lib in lakefile.toml
python3 scripts/perf-record.py GoFV.Rules.     # a prefix; or one module; or a library name
```

Targets and import order follow Lake (`globs`: `X.+` = submodules of X, `X.*` = X and its
submodules). Each module is built with `lake build +M` inside its own memcap scope; a module
killed at 8G is retried once at 16G under `flock ../gofv-heavy.lock`. Raw logs:
`perf/raw/<commit>/` (not committed). A commit already in the history is skipped (`--force`).

A module whose CPU time jumps past the regression thresholds (> 25% and > 5 s) versus its
previous measurement is measured once more and the smaller numbers are kept: under memory
pressure one run read 18.2 s CPU for `GoFVTest.SemDiff`, whose elaboration takes 3.4 s.

Modules restored from the shared Lake cache cost nothing to build. Their numbers come from the
history row with the same Lake input hash (`dep_hash`, from the module's `.trace`), status
`cached`. A cached module never measured before is elaborated once into `tmp/` with
`lake lean M.lean -- <lib args> -o …` (status `remeasured`; `lake lean` applies only the root
package's arguments, so the recorder adds the lean_lib's `leanOptions`/`moreLeanArgs`/
`weakLeanArgs`, else linter warnings land in the `.olean`), so every row of a recorded commit
has numbers. All tools set `TMPDIR` to the worktree's `tmp/` (`lake lean` writes a setup file
there; on the shared `/tmp` tmpfs it failed with errno 122). That second elaboration also checks reproducibility: its
`.olean` must equal the cached one byte for byte (`repro`). A non-reproducible `.olean` (linter
warnings with the absolute source path, see LEARNINGS.md; or nondeterministic elaboration,
which clifv fixed with `-DElab.async=false` on the module) makes every importer miss the shared
cache once the module is rebuilt anywhere; in clifv it caused a hidden 3 h rebuild in CI
(eth-act/clifv#726).

## Columns of `perf/history.tsv`

| Column | Meaning |
| --- | --- |
| `date`, `commit` | UTC time of the recording; commit (12 hex digits, `+dirty` for uncommitted changes) |
| `module` | module name; `_total` = sums over the commit's modules |
| `status` | `built`, `remeasured`, `cached` (copied), `fail`, `oom` (killed at the retry cap), `blocked` (an import failed) |
| `wall_s`, `cpu_s` | wall and CPU (user+sys) seconds of `lake build +M`; `_total`: serial sum = cold one-job build time |
| `maxrss_mb` | **peak RSS of the `lean` process** (VmHWM, polled every 0.1 s); includes the mmapped `.olean`s of its imports (~0.45 GB for `Init` alone) |
| `cgpeak_mb` | `memory.peak` of the memcap scope (what the cap is checked against); page cache charged on first touch makes it noisy, so it is reported, not compared |
| `olean_kb` | size of `M.olean*` |
| `dep_hash` | Lake input hash of the module |
| `measured_at` | commit where the numbers were measured (differs from `commit` for `cached` rows) |
| `load1` | 1-minute load average when the measurement started (the machine is shared; high load inflates wall time) |
| `olean_hash` | sha256 (16 hex) of `M.olean` |
| `repro` | `same`/`differs`: the remeasure's `.olean` vs the cached one (empty for `built` rows); `_total`: count of `differs` |
| `crit_s` | CPU critical path ending at the module (own `cpu_s` + largest `crit_s` of its imports); `_total`: the maximum = modelled cold-build time with unlimited parallelism |

Useful reads: `column -t -s$'\t' perf/history.tsv | grep _total` (cost per commit);
`awk -F'\t' '$4=="built"' perf/history.tsv | sort -t$'\t' -k7,7nr | head` (heaviest modules).

## Thresholds (`perf-compare.py`)

| Flag | Rule |
| --- | --- |
| peak RSS regression | `maxrss_mb` grew > 25% and > 512 MB |
| time regression | `wall_s` and `cpu_s` both grew > 25% and > 5 s (load 120 inflated small modules' wall time 2–10× and CPU ~1.5×) |
| new heavy module | a new module above 2 GB, 60 s CPU, or 10 MB `.olean` |
| `.olean` growth | a module's `.olean` grew > 25% and > 5 MB (exact bytes, no load noise; a proof-only module should stay well under 1 MB) |
| broken | a module that built in BASE fails or is killed in HEAD |
| benchmark regression | wall and CPU time both > 25% and > 1 s, or max RSS > 25% and > 256 MB |
| non-reproducible `.olean` | a module's `repro` is `differs` in HEAD but not in BASE |
| critical path | `_total` `crit_s` grew > 25% and > 30 s; the report names the chain |

Shrinks past the same thresholds are listed as wins. Modules whose numbers are the same
measurement in both commits (`measured_at` equal) are skipped. For a PR, BASE is its merge base
with main; for main, the previous recorded main commit.

`perf-graph.py COMMIT` shows where structural work pays (eth-act/clifv#726: removing unused
imports and moving shared lemmas into lower modules took clifv's cold build 1,370 → 425 s):
the critical chain module by module, and for each module the CPU of everything a change to it
rebuilds. At f2e7f11: 148 modules, serial CPU 318 s, critical path 44 s over 17 modules
(`GoFV.SSA.Op` 10.2 s and `GoFV.Rules.Eval` 10.5 s dominate); `GoFV.SSA.OpInfo`/`Op` sit
under 125 of the 148 modules (281 s CPU per change).

When a module regresses, `perf-explain.py M` prints its slowest declaration steps, e.g.

```
GoFV.X: 3 top-level profiler entries >= 100 ms (sum 41.0 s)
     38.20s  Elab.async             elaborating proof of foo_correct
      2.10s  Elab.command           def table
```

and LEARNINGS.md usually has the fix (kernel-friendly `List` scans, structural recursion,
leaf-wise certificates, splitting the module).

For a big `.olean`, `lake env lean --run scripts/olean-top.lean M.olean [N]` lists the largest
constants: shared `Expr` nodes of type+value and bytes of string literals (where `bv_decide`
stores its LRAT certificates as `…._cert_def_N`). Many `match_N.eq_i`/splitters point at the
stuck-`match` pathology instead (LEARNINGS.md).

## Runtime benchmarks

`perf/bench.tsv` lists `name<TAB>lake target<TAB>command`; `perf-bench.py` builds the target, runs
the command once (`--runs N`: median of N; each run in a memcap scope; ~60–75 s CPU per corpus
benchmark, so 5 benchmarks cost ~6 min CPU per changed binary set) and records wall time, CPU time and
the largest max RSS (`perf/bench-history.tsv`: `date commit bench status wall_s cpu_s maxrss_mb
runs load1 bin_hash corpus`; status `missing` when the target does not build at that commit).
Call the binary (`.lake/build/bin/x`), not `lake exe x`. A binary already measured with the same
command and corpus (`bin_hash`) is not rerun (status `cached`), so commits that don't touch an
executable cost one `lake build`; `perf-compare.py` skips such pairs. The watch loop always uses
the profiler's current registry, so a new benchmark also runs on older commits it records.

The corpus is a private snapshot: the exporter regenerates `../gofv-corpus/<pin12>` in place
(a benchmark reading it failed mid-run when it was swapped), so `perf-bench.py` copies the newest
one (as `scripts/parity.sh` picks it) to `tmp/bench-corpus/<id>` of the profiler worktree
(`id` = hash of `stats.txt` and `manifest.txt`; two newest kept) and passes it as
`$GOFV_BENCH_CORPUS`. Rows of different corpora are not compared. The runners exit 1 on
mismatches; commands accept that (`|| [ $? -eq 1 ]`), so only crashes count as `fail` —
correctness is the runners' own gates, not this one. The first registry entry
(`ssa-roundtrip-corpus`) is a gate: if more than 1% of the corpus files fail to round-trip
(`--gate-max-fail`, read from its `N files, M failed` line), it is recorded as `unparsable` and the
other benchmarks as `skipped`. A corpus the commit cannot parse makes the runners reject every
file and their numbers meaningless (af5cb6a: the regenerated corpus had `frontend` lines its
parser did not accept yet); a few new-format files are fine (845db3d: 37/9,297 with `zvar`).

| Benchmark | Runs on `$GOFV_BENCH_CORPUS/plain` (9,297 files, 1.25 GB) |
| --- | --- |
| `ssa-roundtrip-corpus` | `ssa-roundtrip`: parse, print, compare every export file |
| `pass-parity-corpus` | `pass-parity --jobs 4`: every registered pass port against the stock sections |
| `ssa-check-corpus` | `ssa-check`: the well-formedness checker on every section |
| `analysis-difftest-corpus` | `analysis-difftest`: CFG analyses vs the stock compiler's caches |
| `sem-difftest-corpus` | `sem-difftest corpus 2 1`: `GoFV.SSA.run` on every section, 2 random calls each |
