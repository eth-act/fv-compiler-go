# Agent rules

- Read `docs/PLAN.md` and `LEARNINGS.md` first. Pins: `docs/PINS.md`. Lean performance
  skills (kevaundray/lean-skills, installed in `~/.agents/skills`): `lean-proof-performance`,
  `lean-build-hygiene`, `lean-asm-proofs`, `fast-lean`. `fast-lean build <Module>` (dev
  toolchain `dev-fast-v4.34.1`) is fine while iterating; checks before a PR use plain
  `lake build` and `#print axioms` (no `skippedProof`).
- Work is organised in GitHub issues on eth-act/fv-compiler-go (public). Claim an issue before
  starting (`gh issue edit N --add-assignee @me` + a comment naming your agent and branch);
  reference it in commits and PRs; post progress there. Split large issues into sub-issues.
- Never file anything upstream with Go (issues, CLs, comments, mailing lists). Possible Go
  bugs or upstream findings go into an issue here labelled `upstream-candidate` with a
  minimal repro; the user files upstream manually.
- One worktree per agent: `scripts/agent-worktree.sh <name>` → `../fv-compiler-go-wt/<name>`,
  branch `agent/<name>`. Never edit the main checkout. Use absolute paths under your worktree
  for file tools; in bash, `cd` into the worktree in the same command.
- Every lake/lean/go/test command goes through `scripts/memcap.sh` (default cap 8G, shared
  Lake cache `../gofv-lake-cache`; `lean -j4` via the lakefile's `weakLeanArgs`). One heavy process at a time per
  agent; anything above 8G only under `flock ../gofv-heavy.lock`. The machine is shared with
  other heavy projects: never pattern-kill (kill only PIDs you started), temporary files under
  `<worktree>/tmp/`, never `/tmp`. Check `free -g` before large builds.
- Never `git stash` (shared across worktrees). Commit on your own branch instead.
- Merge: the author merges. Once the per-PR checks pass (build of affected modules,
  parity on the corpus for touched passes, `#print axioms` of new theorems), rebase on
  origin/main, run `scripts/check-reverts.sh` (it fails if the branch silently undoes work
  already on main, as #191 undid #190; fix the rebase, or pass `--allow <path>` and say why in
  the PR body for an intended revert; then, right after the squash merge, add the merge commit's
  short hash with the PR number and reason to `scripts/reverts-ack.txt`, or the nightly gate's
  `reverts` step goes red), open the PR with the check results in its body and
  `gh pr merge --squash`. Read `git diff --stat origin/main...HEAD` before merging: every
  deleted or shrunk file must be one you meant to change.
- All `GoFV/Proof` modules import together (no name declared twice; docs/GATE.md `allproof`).
  A PR that adds or removes one reruns `scripts/gen-allproof.sh` and builds
  `GoFVTest.Proof.AllProof`; shared helpers go into a common module, local ones are `private`.
- No `sorry`, no new axioms on main. Every new top-level theorem gets a concrete non-vacuity
  witness. Generated files say which tool generated them; never hand-edit them.
- When a change makes a build measurably faster or slower, add an entry to `LEARNINGS.md`.
- When you stop, post on your issue: merged PRs, unmerged branches and their state, exact new
  theorem statements, check results, and precise next steps for a continuation agent. When
  your work is merged, remove your worktree's `.lake`.
