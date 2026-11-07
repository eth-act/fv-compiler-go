# Plan

gofv is a formally verified port of the Go compiler's SSA back end to Lean 4, in the style of
clifv (eth-act/clifv, a verified CLIF → AArch64 compiler). Phase 1 is the machine-independent
SSA optimisation pipeline: the passes of `cmd/compile/internal/ssa/compile.go` from
`number lines` up to, but not including, `lower` (§4, done). Phase 2 is the arm64-specific
part from `lower` through `regalloc`, `loop rotate` and `trim` (§6). Phase 3 is everything
after `trim` down to object code: `genssa`, the assembler and the runtime metadata (§7).

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
- **ARM64 op semantics** are defined directly on `BitVec` here, transcribed from the ASL, and
  checked by our own co-simulation under qemu on Go-assembled instructions plus the native
  semantic difftest (option (c) of the semantics plan). Nothing from clifv is vendored or
  imported until the repository has a licence (#384); agreement theorems against an ASL-derived
  model wait for that decision.
- **FMA.** The Go spec allows fused multiply-add; the Phase 2 statements hold up to a
  contraction of the source at exactly the shapes of the 12 `useFMA` rules
  (`docs/plans/semantics2.md` §2.1).
- **Regalloc is validated, not proven directly.** The port is exact but untrusted; a certified
  location checker in the style of clifv's `checkAlloc` gives `Refines (runLoc g) (runSched f)`.

| Id | Content | Issue |
| --- | --- | --- |
| H1 | Export: a section after every pass `lower` … `trim` (format `gofv-ssa 5`): ARM64 ops/aux/blocks, loop nest contents, `f.RegAlloc`, `tempRegs`, new autos, register config; new corpus versions | #379 |
| H2 | ARM64 ops (354, with all `opInfo` attributes and register specs), block kinds, register table and masks, `ARM64.rules`/`ARM64latelower.rules` as Lean data with the new helpers | #380 |
| H3 | `lower` and `late lower` parity (Phase 1 rule interpreter with the ARM64 rule sets) | #381 |
| H4 | Parity of the other passes: addressing modes, pair, the three deadcode instances, lowered cse, elim unread autos, tighten tuple selectors, checkLower, loop invariant, late phielim and copyelim, tighten, critical, phi tighten, likelyadjust, layout, schedule, late nilcheck, flagalloc, loop rotate, trim | #382 |
| H5 | `regalloc` parity, including `stackalloc` and the edge shuffle | #383 |
| H6 | Lowered semantics: flags, `evalArm64`, block kinds, `runSched`, `runLoc`; co-simulation of the ops on Go's encodings under qemu; semantic difftest on every Phase 2 section (agreement theorems against an ASL model after the licence decision) | #384 |
| H7 | Proofs: ARM64 rule lemmas, one refinement theorem per pass, the schedule validator, the regalloc checker and its soundness, the verified pipeline through `trim` | #385 |
| H8 | Driver end-to-end through regalloc: Lean pipeline from `number lines` to `trim` inside `cmd/compile`, import of homes and new autos, byte-identical objects | #386 |

Labels `milestone:H1` … `milestone:H8`. Dependencies: H1 → H3, H4, H5 (parity needs the
sections); H2 → H3, H4, H5, H6; H3–H5 → H8; H6 → H7. H4's `loop rotate` and `trim` start from
the exported `regalloc` section and do not wait for H5.

## 7. Phase 3: genssa, assembly and object code

Scope: per function on linux/arm64, from the `trim` output to the bytes, relocations and
metadata in the object file: frame layout (`AllocFrame`, MergeLocals), liveness (stack maps,
unsafe points, stack objects), `genssa` with `arm64.ssaGenValue`/`ssaGenBlock`, `defframe`,
`cmd/internal/obj` with `obj/arm64` (`progedit`, `preprocess`, `span7`: literal pools, branch
veneers, encodings, relocations), unsafe/restartable points, pc tables and funcdata, DWARF. The
package-level object writer (`NumberSyms`, `WriteObjFile`) and the linker stay stock and
trusted. Survey: `docs/PASSES3.md` (24 steps A1–F2, inputs/outputs, parity traps, export needs,
proof difficulty); machine semantics, the relation to `runLoc`, ABI, frame, runtime hooks and
what is trusted: `docs/plans/semantics3.md`. Tracking issue #546.

Same method once more: export each cut point, exact Lean ports at per-function parity, then
semantics and proofs, then the driver. New in Phase 3:

- **Forms.** L2f (framed SSA, `runFrame`), P0–P2 (Prog lists before and after `progedit` and
  `preprocess`, `runProg`: the machine with a Prog as program counter), M (machine words,
  `runMach`); debug information and the object file have no semantics (parity only).
- **Machine semantics: option (a) + (c).** Our own ARM64 instruction semantics over the forms
  the compiler emits, built on Phase 2's `BitVec` definitions and co-simulated under qemu on
  Go-assembled words; the assembler (`span7`, 8,795 lines) is ported exactly but untrusted and
  its output is checked by a proven object validator (decode the words, check each Prog's
  specification), as regalloc is in Phase 2. Agreement with an ASL-derived model (clifv's
  `FV/Arm`) only after the licence decision (#415): I6b, #555.
- **Runtime metadata is validated against runtime contracts.** pcsp, stack maps (coverage and
  validity, needed by stack moves and the GC), unsafe/restartable points (R27 dead where
  async preemption may stop), `PCDATA_PanicBounds`, morestack spill records. Calls, morestack,
  stack moves, async preemption, nil faults and panics are hooks with trusted contracts.
- **Concrete addresses.** The first end-to-end theorem guards against pointer→integer
  conversions; a parametrised address assignment comes later (semantics3 §4.3).

| Id | Content | Issue |
| --- | --- | --- |
| I1 | Export `gofv-prog 1`: after `AllocFrame`, liveness, after `defframe` (Prog list with identities, FuncInfo, `bstart`/`valueToProgAfter`), inside `Flushplist` (after `linkpatch`, `preprocess`, `span7`), pc tables, DWARF symbols; `oplook` coverage histogram; new corpus versions | #547 |
| I2 | Lean Prog IR (`Prog`, `Addr`, `LSym`, `Reloc`, `FuncInfo`), generated `As`/register constants and `optab`; parser/printer round trip | #548 |
| I3 | genssa parity: MergeLocals, `AllocFrame`, liveness and metadata symbols, `objw`, the block/value loop, arm64 value/block emission, inline marks, branches, jump tables, `defframe` | #549 |
| I4 | Assembler parity: `linkpatch`/`progedit`, `preprocess`, `span7` (classes, pools, veneers, encodings, relocations), unsafe points, pc tables and funcdata | #550 |
| I5 | Debug-info parity: location lists, DWARF variables/scopes/inlined calls/DIEs, line programs | #551 |
| I6 | Machine semantics: ARM64 subset (`Insn`, `decode`, `exec`), co-simulation, `runFrame`, `runProg`, `runMach` with runtime hooks, ABI/frame predicates, machine difftest (I6b #555: ASL agreement, blocked on #415) | #552 |
| I7 | Proofs: framing validators, genssa simulation, progedit/preprocess refinements, the object validator and its soundness, metadata validators, the end-to-end theorem through object code | #553 |
| I8 | Driver through object code: import after `genssa`, then after `Flushplist`, then with Lean DWARF; byte-identical objects; verified mode | #554 |

Labels `milestone:I1` … `milestone:I8`, `phase3`. Dependencies: I1 → I3, I4, I5 (parity needs
the records); I2 → I3, I4, I5, I6; I4 → I5 (final PCs); I6 → I7; I3 → I8 stage 1, I4 → stage 2,
I5 → stage 3; I7 → I8's verified mode. Only I6b is blocked on #415.
