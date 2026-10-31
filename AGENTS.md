# Agent rules

- Read `docs/PLAN.md` and `LEARNINGS.md` first. Pins: `docs/PINS.md`.
- Work is organised in GitHub issues on kevaundray/fv-compiler-go. Claim an issue by
  commenting before starting; reference it in commits and PRs; post progress there.
- One worktree per agent: `scripts/agent-worktree.sh <name>` → `../fv-compiler-go-wt/<name>`,
  branch `agent/<name>`. Never edit the main checkout. Use absolute paths under your worktree
  for file tools; in bash, `cd` into the worktree in the same command.
- Every lake/lean/go/test command goes through `scripts/memcap.sh` (default 8G cap). The
  machine is shared with other heavy projects: never pattern-kill processes, never run more
  than one heavy build at a time, temporary files under `$root/tmp/<agent>_*`, never `/tmp`.
- Never `git stash` (shared across worktrees). Commit on your own branch instead.
- PRs are squash-merged (`gh pr merge --squash`) by the integrator.
- No `sorry`, no new axioms on main. Generated files say which tool generated them.
- When a change makes a build measurably faster or slower, add an entry to `LEARNINGS.md`.
