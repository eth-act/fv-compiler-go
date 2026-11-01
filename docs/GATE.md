# Nightly gate

The per-PR checks (AGENTS.md) build the affected modules and run parity on the quick corpus.
The nightly gate checks the whole of the newest `origin/main` against the full corpus every
night: `scripts/nightly-gate.sh`, run by a systemd `--user` timer. Results go to the
**Nightly gate** status issue (label `nightly-gate`), one comment per night.

## Steps

The gate runs in its own detached worktree, `../fv-compiler-go-wt/nightly-gate`. Each run
checks out `origin/main` there after a fetch, and then runs the steps from that commit's copy
of the script. The full corpus is the version that `../gofv-corpus/<pin12>/full` points to
when the run starts (`readlink -f`), so a corpus switch during the run does not affect it.

| step | command | red when |
| --- | --- | --- |
| `build` | `lake build GoFV GoFVTest gofv-ssa-opt pass-parity ssa-check` | any module or executable fails |
| `no-sorry` | `scripts/no-sorry.py` | `sorry` or `admit` appears in a tracked `.lean` file, outside comments and strings |
| `axioms` | `scripts/axioms-audit.sh` | a theorem under `GoFV.Proof` depends on any axiom other than `propext`, `Classical.choice`, `Quot.sound` and the `_native` axioms listed in `scripts/axioms-allowlist.txt` |
| `ssa-check` | `ssa-check <full corpus>` | a section is not well formed (`GoFV.SSA.check`) |
| `parity` | `scripts/parity.sh <full corpus>` | a registered pass mismatches the stock pass, or reports an error |
| `check` | `gofv-ssa-opt --check --jobs 4 <full corpus>` | the whole pipeline diverges from stock, or a Lean pass fails (docs/DRIVER.md) |
| `e2e` | driver toolchain, then `scripts/driver-e2e.sh --mode full` | a std archive or a binary differs from stock, a program's output differs, or a function falls back to the stock passes |

- The axioms audit (`scripts/axioms-audit.sh`) imports every module `GoFV/Proof/**/*.lean`. It
  runs Lean's `collectAxioms`, the function behind `#print axioms`, on every theorem declared
  in those modules or named `GoFV.Proof.*`, auxiliary theorems included. `sorryAx` and declared
  axioms are always violations. A deliberate `bv_decide`/`native_decide` use adds its
  `…._native.…` axiom names to `scripts/axioms-allowlist.txt` in the same PR (docs/PLAN.md §0).
- `no-sorry` also catches files that no target builds. The axioms audit catches a `sorry` that
  is hidden from the text, for example one inside a macro.
- `e2e` rebuilds the driver toolchain (`GOFV_GO_DRIVER=1 scripts/build-go.sh` into the gate
  worktree's `tmp/go-driver`) only when `patches/go/*.patch` changed. A hash of the patches is
  stored in `tmp/go-driver/.gofv-patches`.
- If `build` fails, the steps that depend on it are skipped. Otherwise every step runs, even
  after a failure.

## Results

A run writes to `<gate worktree>/tmp/gate/<date>T<time>/`: `summary.md`, one `<step>.log` per
step, and the step outputs (`parity.md`, `check.md`, `axioms/`, `e2e-full/`). The summary is
posted as a comment on **Nightly gate**: the verdict, the commit, the corpus version, a table
of steps with result and time, and the numbers of each step.

On a red night the gate opens an issue for the first failing step. The issue is titled
`Nightly gate red: <step>`, has the label `gate-red`, and contains the commit and the tail of
the step's log. If an issue for that step is already open, the gate comments on it instead.
Close the issue when the fix is merged. The next green night confirms the fix on the status
issue.

## Schedule and memory

- `gofv-nightly-gate.timer` fires at 02:00, 03:00, 04:00, 05:00 and 06:00 local time
  (`OnCalendar=*-*-* 02..06:00:00`).
- An attempt runs the gate only if the gate has not yet run that day
  (`../gofv-gate.state`, next to the checkouts) and `MemAvailable` (the "available" column of
  `free -g`) is at least 20G (`GATE_MIN_FREE_GB`).
- Otherwise the attempt exits, and the next hourly attempt tries again. If the 06:00 attempt
  still lacks the memory, it posts "skipped" on the status issue.
- `gofv-nightly-gate.service` runs in `gofv.slice` with `MemoryMax=8G`. That cap covers the
  gate's own processes, including the qemu runs of the e2e programs. Every build and check
  step runs in its own `scripts/memcap.sh` scope, capped at 8G, also in `gofv.slice`.
- `../gofv-gate.lock` (`flock`) keeps two runs from overlapping.

## Operating it

```
scripts/nightly-gate.sh --install       # gate worktree + ~/.config/systemd/user units, timer on
systemctl --user start gofv-nightly-gate.service   # run now, as the timer would (once a day)
scripts/nightly-gate.sh --now [--no-post] [--force] # run now from a shell; --no-post: no issue
                                        # comments, --force: no memory check
systemctl --user list-timers gofv-nightly-gate.timer
journalctl --user -u gofv-nightly-gate.service
```

The unit templates are in `scripts/systemd/`. `--install` fills in the gate worktree path. It
also copies `scripts/gofv.slice` if `~/.config/systemd/user/gofv.slice` does not exist.
