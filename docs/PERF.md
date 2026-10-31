# Performance tracking

`perf/` keeps the build cost of every Lean module and the runtime of the compiled Lean
executables, per commit. The profiler agent (issue #1) records main and every open PR and
comments on PRs that cross the thresholds below. Anyone can run the same scripts.

| Script | Does |
| --- | --- |
| `scripts/perf-record.py [TARGET...]` | builds module by module, appends one row per (commit, module) to `perf/history.tsv` |
| `scripts/perf-compare.py BASE HEAD` | Markdown report of regressions/wins between two recorded commits; exit 1 on a regression |
| `scripts/perf-explain.py MODULE` | names the slow declarations of one module (`trace.profiler`) |
| `scripts/perf-bench.py [NAME...]` | runs the executables listed in `perf/bench.tsv`, appends to `perf/bench-history.tsv` |
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

Modules restored from the shared Lake cache cost nothing to build. Their numbers come from the
history row with the same Lake input hash (`dep_hash`, from the module's `.trace`), status
`cached`. A cached module never measured before is elaborated once into `tmp/` with
`lake env lean` (status `remeasured`), so every row of a recorded commit has numbers.

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

Useful reads: `column -t -s$'\t' perf/history.tsv | grep _total` (cost per commit);
`awk -F'\t' '$4=="built"' perf/history.tsv | sort -t$'\t' -k7,7nr | head` (heaviest modules).

## Thresholds (`perf-compare.py`)

| Flag | Rule |
| --- | --- |
| peak RSS regression | `maxrss_mb` grew > 25% and > 512 MB |
| time regression | `wall_s` grew > 25% and > 5 s, and `cpu_s` grew > 25% (filters load noise) |
| new heavy module | a new module above 2 GB or 60 s |
| broken | a module that built in BASE fails or is killed in HEAD |
| benchmark regression | wall time > 25% and > 1 s and CPU time > 25%, or max RSS > 25% and > 256 MB |

Shrinks past the same thresholds are listed as wins. Modules whose numbers are the same
measurement in both commits (`measured_at` equal) are skipped. For a PR, BASE is its merge base
with main; for main, the previous recorded main commit.

When a module regresses, `perf-explain.py M` prints its slowest declaration steps, e.g.

```
GoFV.X: 3 top-level profiler entries >= 100 ms (sum 41.0 s)
     38.20s  Elab.async             elaborating proof of foo_correct
      2.10s  Elab.command           def table
```

and LEARNINGS.md usually has the fix (kernel-friendly `List` scans, structural recursion,
leaf-wise certificates, splitting the module).

## Runtime benchmarks

`perf/bench.tsv` lists `name<TAB>lake target<TAB>command`; `perf-bench.py` builds the target, runs
the command 3 times (each in a memcap scope) and records the median wall time, its CPU time and
the largest max RSS (`perf/bench-history.tsv`: `date commit bench status wall_s cpu_s maxrss_mb
runs load1 bin_hash`; status `missing` when the target does not build at that commit). Call the
binary (`.lake/build/bin/x`), not `lake exe x`. A binary already measured with the same command
(`bin_hash` = sha256 of command and binary) is not rerun (status `cached`), so commits that don't
touch an executable cost nothing; `perf-compare.py` skips such pairs. The watch loop always uses
the profiler's current registry, so a new benchmark also runs on older commits it records.

| Benchmark | Runs |
| --- | --- |
| `ssa-roundtrip-corpus` | `ssa-roundtrip` (parse + print + compare) over the whole export corpus, `$GOFV_CORPUS/plain` (default `~/work/gofv-corpus/2aae1000ea1d`, 9,297 files, 1.25 GB) |

Pass parity runners get an entry each as they land.
