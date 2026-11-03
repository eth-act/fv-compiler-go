# Plan

gofv is a formally verified port of the Go compiler's SSA back end to Lean 4, in the style of
clifv (eth-act/clifv, a verified CLIF → AArch64 compiler). Phase 1 is the machine-independent
SSA optimisation pipeline: the passes of `cmd/compile/internal/ssa/compile.go` from
`number lines` up to, but not including, `lower` (§4, done). Phase 2 is the arm64-specific
part from `lower` through `regalloc`, `loop rotate` and `trim` (§6). Assembly emission
(`genssa`) is Phase 3.

## 0. Ground rules

- Lean core and `Std` only, no Mathlib. Pin in `docs/PINS.md`.
- No `sorry` in merged Lean files, no new `axiom` declarations. Each claimed theorem's
  `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` (plus the compiled
  evaluation axioms `bv_decide`/`native_decide` generate, where used deliberately).
- Namespaces follow directories: `GoFV.SSA`, `GoFV.Rules`, `GoFV.Opt`, `GoFV.Proof`, …
- Every executable model is checked against an oracle: the stock Go compiler (per-pass SSA
  parity) and native execution under `qemu-aarch64-static` (semantics).
- Every Lean, lake, go or test command runs through `scripts/memcap.sh` (default cap 8G, all
  scopes in `gofv.slice`, total cap 24G). The machine is shared with other heavy projects.

## 1. Correctness criterion

`GoFV.SSA.run` (to be written, `docs/plans/semantics.md`) is an executable, fuel-bounded
semantics of generic Go SSA. A pass `p : Func → Func` is correct when, for every well-formed
`f`, every terminating or panicking run of `p f` is a run of `f` (refinement; stuck or
out-of-fuel source runs carry no obligation).
Formally `GoFV.Proof.Refines tabs' (p f) tabs f` (`GoFV/Proof/Refine.lean`): every
returning or panicking run of `f` is, up to refinement, a run of `p f` with some fuel (results
refined pointwise, memory refined bytewise (`Mem.Refines`: a rewrite may make a poison value
defined, which may then be stored); a panic's memory refined once the frames of the run and its
callees are dropped, `Mem.dropFrames`, `OutcomeRefines act`);
by determinism and fuel monotonicity (`Refines.backward`) every defined run of `p f` is then a
run of `f` whenever `f` is defined. Pass theorems: `GoFV/Proof/Pass/*.lean` (issue #11).

## 2. Stock parity (the oracle)

The Lean passes are faithful ports: on the same input, `GoFV.Opt.<pass>` must produce exactly
the SSA the stock pass produces — same value and block IDs, same order, same aux data. The
oracle is a patched `go1.27.3` compiler that exports each function's SSA before and after every
pass (`docs/contracts/export.md`). Parity is checked per pass (`input_k` → Lean pass → compare
with `input_{k+1}`), so a mismatch names the pass and the first differing value.

Consequence: a function compiled by the stock compiler gets the verified pipeline's result,
and the stock compiler's later passes can consume it unchanged (a later driver can substitute
the Lean result into `cmd/compile`).

## 3. Design

- **One IR.** `GoFV.SSA.Func` mirrors `ssa.Func`/`Block`/`Value` (IDs, op, type, aux, auxint,
  args, block kind, controls, succs/preds with indices, likely). Op enum generated from
  `_gen/*Ops.go`, never hand-written.
- **Rules as data.** `generic.rules`, `dec.rules`, `divisible.rules`, `divmod.rules` are
  exported from rulegen's own parser to Lean literal data; one interpreter replicates rulegen's
  matching order (commutative expansion, conditions, result construction order, value-ID
  allocation) so `opt` reaches parity. Each rule gets its own correctness lemma, in small
  per-op proof modules.
- **Passes first, proofs afterwards** (as clifv's mid-end): each pass lands with parity on the
  corpus, then gets its simulation proof. Hard passes (`prove`, `expand calls`) may land as
  translation validators: an untrusted port plus a proven checker run on its output.
- **Write for the kernel from day one** (LEARNINGS.md): structural recursion, `List` scans in
  kernel-evaluated code with `@[csimp]` swaps to `Array` for compiled code, generated tables
  checked leaf-wise, no umbrella imports from hub modules, small modules.

## 4. Milestones

| Id | Content |
| --- | --- |
| G0 | Repo infrastructure: memcap, worktrees, shared Lake cache, perf tracking (`perf/`) |
| G1 | Exporter: patched compiler writes per-pass SSA (`docs/contracts/export.md`); corpus from std + examples |
| G2 | Lean IR: generated ops, `Func`/`Block`/`Value`, export parser, printer, round trip on the corpus |
| G3 | Rules: exporter from rulegen, Lean rule data, interpreter, `opt`/`late opt`/`middle opt` parity |
| G4 | Passes, parity each: copyelim/phielim, deadcode, shortcircuit, decompose user/builtin, zcse, cse, phiopt, nilcheckelim, prove, divisible, divmod, known bits, fuse (early/late), expand calls, softfloat, branchelim, dead auto elim, sccp, check bce, dse, memcombine, writebarrier, insert resched checks |
| G5 | Semantics `GoFV.SSA.run`, differential-tested against native arm64 execution |
| G6 | Proofs: well-formedness checker, then one simulation proof per pass, rule lemmas |
| G7 | Driver: run the Lean pipeline inside `cmd/compile` in place of the stock passes |

GitHub issues track each milestone and pass (label `milestone:Gn`, `pass`).

## 5. Build infrastructure

- `scripts/memcap.sh <cmd>`: per-command cgroup cap (`FV_MEMCAP`, default 8G) inside
  `gofv.slice` (`scripts/gofv.slice`, install into `~/.config/systemd/user/`; total 24G);
  every worktree shares one Lake artifact cache (`FV_LAKE_CACHE`, default
  `../gofv-lake-cache`, hard links); `lean -j4` via `weakLeanArgs` (untraced: no rebuilds).
- `scripts/agent-worktree.sh <name>`: one worktree per agent at `../fv-compiler-go-wt/<name>`,
  branch `agent/<name>`.
- `perf/`: per-module build time and peak RSS history, kept by the profiler agent
  (`docs/PERF.md`). A change that grows a module's peak RSS or time by more than 25% is flagged
  on its PR.

## 6. Phase 2: lowering through regalloc

Scope: the 24 passes of `compile.go` `passes` from `lower` (index 35) to `trim` (58) on
linux/arm64 (`merge conditional branches` is commented out in the pin). Survey:
`docs/PASSES2.md`; semantics of lowered SSA and the refinement relations (generic → lowered,
unscheduled → scheduled, pre- → post-regalloc): `docs/plans/semantics2.md`. Tracking issue
#387; one issue per pass (`Phase 2 pass: <name>`, labels `pass`, `phase2`).

Same method as Phase 1: the exporter writes the SSA after every pass, each Lean port reaches
exact parity on the corpus, then the passes get refinement proofs, and the driver substitutes
the Lean result. New in Phase 2:

- **Three forms, three semantics.** Unscheduled lowered SSA keeps Phase 1's `run` (extended by
  the ARM64 ops, block kinds and a flags shape), so Phase 1's proof machinery carries over;
  from `schedule` on, `runSched` follows `b.Values` order with faulting memory ops; after
  regalloc, `runLoc` runs on registers, the flags register and stack slots.
- **ARM64 op semantics** are defined directly on `BitVec` and validated against clifv's
  ASL-derived, qemu-co-simulated `FV/Arm` by per-op agreement theorems (option (c) of the
  semantics plan).
- **Regalloc is validated, not proven directly.** The port is exact but untrusted; a certified
  location checker in the style of clifv's `checkAlloc` gives `Refines (runLoc g) (runSched f)`.

| Id | Content | Issue |
| --- | --- | --- |
| H1 | Export: a section after every pass `lower` … `trim` (format `gofv-ssa 5`): ARM64 ops/aux/blocks, loop nest contents, `f.RegAlloc`, `tempRegs`, new autos, register config; new corpus versions | #379 |
| H2 | ARM64 ops (354, with all `opInfo` attributes and register specs), block kinds, register table and masks, `ARM64.rules`/`ARM64latelower.rules` as Lean data with the new helpers | #380 |
| H3 | `lower` and `late lower` parity (Phase 1 rule interpreter with the ARM64 rule sets) | #381 |
| H4 | Parity of the other passes: addressing modes, pair, the three deadcode instances, lowered cse, elim unread autos, tighten tuple selectors, checkLower, loop invariant, late phielim and copyelim, tighten, critical, phi tighten, likelyadjust, layout, schedule, late nilcheck, flagalloc, loop rotate, trim | #382 |
| H5 | `regalloc` parity, including `stackalloc` and the edge shuffle | #383 |
| H6 | Lowered semantics: flags, `evalArm64`, block kinds, `runSched`, `runLoc`; vendored `FV/Arm` subset, co-simulation on Go's encodings, agreement theorems; semantic difftest on every Phase 2 section | #384 |
| H7 | Proofs: ARM64 rule lemmas, one refinement theorem per pass, the schedule validator, the regalloc checker and its soundness, the verified pipeline through `trim` | #385 |
| H8 | Driver end-to-end through regalloc: Lean pipeline from `number lines` to `trim` inside `cmd/compile`, import of homes and new autos, byte-identical objects | #386 |

Labels `milestone:H1` … `milestone:H8`. Dependencies: H1 → H3, H4, H5 (parity needs the
sections); H2 → H3, H4, H5, H6; H3–H5 → H8; H6 → H7. H4's `loop rotate` and `trim` start from
the exported `regalloc` section and do not wait for H5.
