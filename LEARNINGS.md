# Learnings

Tricks that make gofv's Lean proofs and builds faster, lighter or more robust, with the
measured effect. Add an entry when a change shows a measurable gain (or a regression worth
avoiding): the problem, the trick, the numbers, where it is used.

## gofv measurements

#### Big enumeration inductives cost superlinear elaboration time
- **Problem:** `GoFV.SSA.Op` with all 2,013 entries of Go's generic `opcodeTable` (445 generic
  ops + 1,567 SIMD generic ops) took about 60 s / 1.0 GB for the bare `inductive` alone
  (elaboration 34 s + type checking 24 s of the auxiliary constructions; `genSizeOf`,
  `genSizeOfSpec`, `genInjectivity` off made no difference) and hit the heartbeat limit with
  `deriving DecidableEq`. 500 constructors took about 6 s, i.e. roughly quadratic.
- **Trick:** leave the SIMD generic ops out (they exist only under `GOEXPERIMENT=simd`, off in
  go1.27.3 and in the corpus; `tools/opsgen/nosimd.go`). Metadata are `match` functions with
  the most frequent value as wildcard default.
- **Effect:** the whole generated `Op.lean` (446 constructors, 20 metadata functions,
  `DecidableEq`) builds in 7.5 s / 0.56 GB (#6).
- **Also measured:** the bare 446-constructor `inductive` already writes a 12 MB `.olean`
  (16 MB with the metadata functions; no equation lemmas or splitters stored). Forcing the
  equation lemmas of six metadata functions (`attribute [local simp] Op.argLen …`) did not
  finish within the default heartbeats (25 s CPU). So evaluate `Op` metadata on concrete ops
  with `decide`/`rfl`; never `simp [Op.argLen]` on an op variable (see the
  `lean-proof-performance` skill, "stuck match").
- **Phase 2 (ARM64 ops, #380):** one extended `Op` (800 constructors: 354 non-SIMD ARM64 + 445
  generic + `Invalid`; the 306 ARM64 SIMD ops left out like the generic ones), 25 metadata
  functions, `DecidableEq`: 13 s / 0.88 GB, 47 MB `.olean` (was 7.5 s / 0.56 GB / 16 MB). The
  size is the compiled `match`es: each metadata function's `_sparseCasesOn_1` is ~11k Expr nodes
  (`scripts/olean-top.lean`). The
  per-op register info (`Op.regInfo`, `asm`, `scale`) lives in the separate `GoFV.SSA.OpARM64`
  (1.5 MB) so Phase 1 modules do not load it. A split `generic | arm64` inductive was not
  needed; its cost would have been rewriting every Phase 1 `match` on `Op`. With the arch ops,
  statements about all ops must cover them (`Eval.nilCheck_eq` now has two cases).

#### Large `match` on a variable: keep `simp` off it, generate equations in the defining module
- **Problem:** `GoFV.SSA.Op` has 446 constructors and its 20 metadata functions are 446-arm
  `match`es. When `simp` unfolds a function that matches on a *variable* of such a type (e.g.
  a fold step `fun t op => op.effect t`), official Lean generates the splitter and all N match
  equations in the importing module and tries each: Θ(N²), stored in that module's `.olean`.
  Separately, `simp [f]` needs `f.eq_1..N`, which every importer regenerates unless some
  upstream module already did.
- **Trick:** give `simp` step lemmas (`block_nil`/`block_cons`, proved by `(rfl)`) or define
  the recursion structurally; put `attribute [local simp] f` right after a big-`match` `f` that
  importers will `simp` with; when one unfolding suffices use `unfold f` / `rw [f.eq_def]`.
- **Effect** (lean-skills `examples/run.py stuck-match eqns-upstream`, rerun here on official
  4.34.1, N = 400, load ~80): stuck `simp [block, Op.effect]` 25.0 s CPU, 64.9M heartbeats,
  39.4 MB `.olean`; step lemmas 1.8 s, 196k, 11 kB. Four importers each `simp [Op.effect]`:
  19–24 s and 39.7 MB each without upstream equations (94.5 s total), 0.6–0.8 s and 7 kB each
  with `attribute [local simp]` in the defining module (30.5 s once; 33.2 s total). Same
  numbers as lean-skills measured on 4.34.0.

#### A `dsimproc` at a constructor instead of `simp [f]` for a `match` with a catch-all arm
- **Problem:** the rule denotation's `callH` (26-arm `match` on helper and argument list,
  `| _, _ => none` last). `simp [callH]` in a rule module met it on an argument not yet in
  constructor form (`isPowerOfTwo(uint8(c))`: the conversion's `if` still undecided), unfolded
  it to its `match` and generated `callH.match_5.eq_1…26` and its splitter privately in that
  module: one rule lemma's `.olean` 4.77 MB, of which `eq_24` and the splitter ~90k objects.
  `attribute [local simp]` / `Match.getEquationsFor` in the defining module did not help (the
  equations are regenerated, private, per importing module).
- **Trick:** `dsimproc reduceCallH (callH _ _ _)`: at a helper constructor, `delta?` +
  `whnfCore`, and give up (`.continue`) if the outer matcher is still stuck; `simp` retries
  after the arguments are simplified. Same pattern as `reduceIntInfo`/`reduceEvalPure`.
- **Effect** (#69, RuleProofs6): `r_generic_1097_sound` alone 4.77 MB → 0.32 MB `.olean`,
  3.8 s → 2.0 s wall; the eight power-of-two `Div`/`Mod` rules fit in 0.86 + 0.40 MB modules;
  `divisible_unfold`'s workaround deleted. All 146 rule modules rebuilt unchanged otherwise.

#### fast-lean (`dev-fast-v4.34.1`) is safe with the shared Lake cache; profiles use official Lean
- Checked here: a module built by `fast-lean build` (proofs skipped, `#print axioms` →
  `Lean.skippedProof`) gets a different Lake input hash than the official build (the trace
  records the same toolchain string, but the hashes differ), so an official `lake build` in
  another worktree sharing `../gofv-lake-cache` rebuilt it and printed no axioms. Iterating with
  fast-lean cannot leak skipped proofs into gate builds through the cache.
- Perf numbers (`perf/`, `docs/PERF.md`) are always taken with the official toolchain, which is
  what the gates run. Faithful dev mode is a diagnostic: if `LEAN_DEV= fast-lean lean M.lean`
  is much faster than official `lake env lean M.lean`, the module hits a pathology the dev
  toolchain patches (stuck `match` in `simp`, leanprover/lean4#15755: 25.0 → 2.65 s CPU,
  64.9M → 781k heartbeats in the N = 400 case above); fix the proof, since gates use official Lean.
- `LEAN_DEV_CHECK=GoFV.Proof.Pass.EC fast-lean build …` did not check `GoFV.Proof.Pass.ECWide`
  or `…ECIdent` (EcSelects2, #28): both built without errors there, then failed in the official
  `lake build`. The prefixes look like name-component prefixes (`EC` covers `EC.*`, not `ECWide`);
  list the modules you changed by full name.

#### All `.olean`s reproducible across worktrees, thanks to `weakLeanArgs`
- **Check:** `scripts/perf-record.py --recheck` re-elaborates every module of main 47fa980 in
  the profiler's worktree with Lake's arguments and compares the `.olean` byte for byte with the
  copy other agents' worktrees put into the shared cache: 148/148 identical. Without the
  lakefile's `weakLeanArgs` (d891ea9), `GoFV.SSA.Sem.Pure` and `GoFV.SSA.Analysis.LoopNest`
  (unused-variable warnings) differ: the warning text with the absolute source path is stored
  in the `.olean` (+1 kB), so a rebuild in another worktree would invalidate every importer.
- **Rule:** keep diagnostics-only options in `weakLeanArgs`; the watch loop flags any module
  whose `.olean` becomes non-reproducible (`repro` column, `docs/PERF.md`). In clifv such a
  module caused a hidden 3 h CI rebuild (eth-act/clifv#726).
- **First catch (a26f6a1):** `GoFV.SSA.Sem.Runtime`'s `.olean` held
  `/home/…/fv-compiler-go-wt/proofinterpmono/GoFV/SSA/Sem/Runtime.lean` from an
  `ambiguousOpen` warning (`open Runtime` inside `namespace GoFV.SSA.Sem`). That linter was not
  in `weakLeanArgs`, so the module's every importer rebuilt in each worktree that rebuilt it.
  With `-Dlinter.ambiguousOpen=false` it is path-free and byte-identical from two directories.
  Every linter that warns in a build log is a candidate: the build logs of the recorded commits
  name only `unusedVariables` and `ambiguousOpen`.
- **Parallel elaboration can reorder a module's constants** (since `-j4`, 03d6b3f). Several modules
  so far wrote a different `.olean` on almost every build: the same constants, serialized in a
  different order. They were `GoFV.Proof.Pass.DSEVal` (2 builds, 2 hashes),
  `GoFV.Proof.Pass.SegCall` (5 builds, 4 hashes) and `GoFV.Proof.AtomSimLoop` (3 builds,
  3 hashes). With `set_option Elab.async false` at the top of the file, each was byte-identical
  over 3 builds, at no measurable CPU cost (DSEVal 11.2 s, SegCall 7.5 s, AtomSimLoop 8 s,
  either way). A fourth, `GoFV.Proof.Regalloc.Ops` (3 builds, 3 hashes), used less CPU
  sequentially (35.7 vs 41.9 s) but more wall time (31 vs 17 s). Most modules are unaffected, so apply it per module when the watch loop
  reports `repro` = differs (#215, #296, #1).
- **`weakLeanArgs` on a `lean_lib` do not reach `lean_exe` root modules.** Lake builds an exe's
  root module (`GoFVTest.OptProvenProbe`, root of `lean_exe opt-proven-probe`) with the exe's own
  arguments, so the lib's `-Dlinter.…=false` (and `-j4`) were missing. The `.olean` stored an
  unused-variable warning with the absolute path, and two worktrees that built it via the lib and
  via the exe got different files for the same input hash. Setting `weakLeanArgs` at package
  level covers libs and exes. Lib modules stay byte-identical and nothing rebuilds, since the
  arguments are untraced (#1).
  The flip side of untraced arguments: the shared cache kept serving the old path-bearing
  `.olean` for the unchanged input hash. Deleting that one mapping
  (`../gofv-lake-cache/outputs/gofv/<depHash>.json`; `depHash` is in the module's `.trace`) made
  the next build store the clean one. The artifact files themselves are left alone, because
  worktrees hard-link them.
  Later `constructorNameAsVariable` (a local `h` named like a constructor `LdOp.h`) leaked a
  path into `GoFV.Proof.Low.SimMem` the same way; it and `defProp` are now in `weakLeanArgs`
  as well (clifv's list). To check which linters warn anywhere:
  `grep -o "set_option linter\.[A-Za-z.]* false" perf/raw/*/*.log | sort | uniq -c`.

#### `exact lemma args` can spend seconds in a failed unification; `have h := lemma args; exact h`
- **Problem:** `ecc_storeObl` (`GoFV.Proof.Pass.ECCall`) closed a goal stated over
  `outargsOK tabs 0 m` with `exact ecc_callOp_outargs …`, whose conclusion is stated over
  `ctx.tabs ctx.act`. `exact` first unifies the expected type into the lemma
  (`Elab.app.propagateExpectedType`). That unfolded `outargsOK` and `List.all` for ~5 s, failed
  (all ❌ in `trace.profiler`), and only then elaborated the arguments, which closed the goal.
- **Trick:** `have h := lemma args; exact h` elaborates the lemma from its arguments first.
  `trace.profiler` (`set_option trace.profiler true in` on the theorem) shows the symptom: a slow
  `[Elab.app.propagateExpectedType] ❌️` under the `exact`.
- **Effect:** ECCall 12.8 → 6.0 s CPU (at 6289b62), 27.0 → 21.0 s on a later main (#297).
- **Related:** a goal that still contains `(a, b).snd` after `rw` makes `exact` unfold the
  definitions inside `a`/`b` (`ShortCircSim.R_next`: `outOf`/`factsOf`, ~3.5 s per `exact`).
  `rw [h]; dsimp only; exact hrel` reduces the projection first: ShortCircSim 8.5 → 2.3 s CPU
  (`-j1`, #1).
- **Never `simp only [evalOpL, …]`: use `evalOpL_generic`.** Unfolding `evalOpL` (800-op
  `match`, `GoFV/SSA/Sem/RunL.lean`) inside `simp` costs seconds per call even when `hg` decides
  the `if` first. `Low.SimDen.evalValueL_localAddr` 7.5 s → 0.2 s by
  `simp only [evalOpL_generic _ _ _ _ _ _ hg, …]` (module 8.5 → 2.1 s CPU, #1).
- **Find them all at once:** `lean -Dtrace.profiler=true -Dtrace.profiler.threshold=500` on
  every module, keeping each topmost failing `[Meta.isDefEq]`/`[Elab.app.propagateExpectedType]`
  ❌ node ≥ 0.5 s with its declaration and enclosing tactic step (lean-skills
  `maintaining-lean-projects`). At 4b4765c, 985 modules, 3 at a time on a 4-core orb, ~45 min:
  87 s in 38 declarations (1.7% of 5,143 CPU-s). One-line fixes (CPU, module alone):
  `ecc_moveObl`, the sibling of `ecc_storeObl` above, ECCall 23.4 → 12.7 s; witnesses whose
  term met `RefinesLoc ?_ ?_`/`RefinesSched` before its arguments (`have` each part, then
  `exact`): TrimLoc 4.8 → 1.0 s, NilLateL 4.2 → 1.6 s; `first | exact hI | exact
  hI.resetControls …` after a `split` (`with_reducible exact hI`) DeadFactsL 5.0 → 2.3 s, and its
  `‹_›` (`by with_reducible assumption`) DeadTail 8.1 → 4.9 s. Left: ~20 declarations at 1–2 s
  each where `evalAll_spec`'s `TopoRem (argsF ctx.f)` argument is elaborated before the last
  argument fixes the implicit `ctx` (fix: reorder the lemma's arguments, a statement change);
  failed structure eta inside successful `rfl`s (DeadEdge `removePred_spec`/`removeSucc_spec`,
  7.7 s); a failing `rule_close` branch unfolding `ushiftRight` in Rsh `r_generic_561_sound`
  (8.8 s).

#### `bv_decide` certificates dominate rule-proof `.olean`s; try `grind` first on ring identities
- **Problem:** PR #91's Add-family rule lemmas (87 theorems, `rule_auto` closing with
  `first | rfl | bv_decide | grind`) wrote 16 / 69 / 57 MB `.olean`s. `scripts/olean-top.lean`:
  64.6 of Add2's 69.4 MB are `bv_decide` LRAT certificates (`r_*_sound._cert_def_N`, string
  literals), 2–9 MB each, for add/sub associativity/commutativity at 64 bits.
- **Trick:** put `grind` (commutative-ring solver; no certificate, no `_native.bv_decide.ax_*`)
  before `bv_decide`. `bv_normalize` is no replacement (left `x + y + z == x + (y + z)` open).
  Rotate rules (`>>>`/`<<<` with a variable amount, one certificate per `shiftIsBounded` case)
  are not closed by `grind`; prove the identity once per width as a lemma and rewrite with it.
- **Effect** (scratch copies, same load, CPU): Add 54.0 → 42.4 s, 16.1 → 7.9 MB; Add2
  70.6 → 51.2 s, 69.4 → 22.9 MB; Add3 (mostly rotate rules) 84.8 → 67.5 s, 57.0 → 56.1 MB; the
  seven slowest rules alone 20.6 → 8.0 s, 32.6 → 1.5 MB. All 87 theorems still close.
- **Follow-up (#69, agent/ruleproofs):** no rule needs `bv_decide` any more. The rotate rules'
  goals are `x <<< y.toNat + x >>> (w#v - y).toNat = x.rotateLeft y.toNat`; one rewrite with a
  lemma proved once for all widths (`rot_add_sub`, `rot_or_sub`, `rot_xor_sub` and their
  swapped forms, `Lemmas.lean`) leaves `y.toNat ≤ w`, which `bv_omega` gets from the bounded
  shift. `rule_close` tries it before `grind` (a failing `grind cutsat` spent 15 s on one
  rotation goal). Further: splitting the `Bool`-auxint/`||` disjunctions last instead of
  first (31% smaller rotate proofs: the shared part is built once), a dsimproc for
  `GoTy.intInfo?` (its `match` equations and splitter were regenerated in every module,
  0.2 MB each), the tactics' lemma lists as simp sets instead of inside `macro` quotations
  (the quotations compile to syntax-building code: `Tactic.olean` 3.9 → 3.1 MB,
  `NonVacuous.olean` 2.1 → 0.6 MB). `Elab.async false` is no longer needed.
- **Effect** (official toolchain, one module at a time, machine load ~100; CPU = user+sys):

  | Module | before: CPU s / `.olean` MB | after: CPU s / `.olean` MB |
  | --- | --: | --: |
  | `Add` (30 lemmas) | 54.0 / 16.1 | 34 / 2.9 |
  | `Add2` (30) | 70.6 / 69.4 | 43 / 3.2 |
  | `Add3` (27) | 84.8 / 57.0 | 41 / 3.3 |

  Peak RSS 1.5–1.7 GB. The rest of each `.olean` is the proof terms themselves (`simp_all`
  congruence chains over the unfolded denotation: 1–3 k distinct subterms per plain rule,
  7–11 k per rotate rule, ~25 bytes each; `probe` prints the count per rule).

#### Bitwise 64-bit lemmas without `bv_decide`: per-bit specialisation + `grind`
- **Problem:** known bits' transfer lemmas (#26: `&&&`/`|||`/`^^^`/`~~~`, `setWidth`, constants,
  bitwise hypotheses `… = 0`) closed by `bv_decide` added 22 `_native.bv_decide.ax_*` axioms
  to `knownBits_refines`.
- **Trick:** `kb_bits` (`GoFV/Proof/Pass/KnownBitsCore.lean`): rewrite every bit-vector
  equation to `∀ i < n, getLsbD … = getLsbD …`, instantiate each such hypothesis at the goal's
  `i` and at `0` (an `elab` that tries `specialize h i (by omega)` under
  `Term.withoutErrToSorry`, restoring the state on failure), push `getLsbD` through the
  operators with `simp only`, close the Boolean formula with `grind`.
- **Effect:** all 22 lemmas kernel-checked, no extra axioms; the five KnownBits proof modules
  build in about 16 s together (`KnownBitsDomain` 11 s, as before).

#### Close repeated residual goals by one general lemma, not `omega` per goal
- **Problem:** the 64 range-check rules (`generic.rules:321–366`, #69) leave ~5 residual
  comparison goals each. Closed by `omega` on the `toNat`/`toInt` arithmetic (every signed
  reading an `if`, given to `omega` as a disjunction), each lemma stored ~37k proof terms incl.
  `_proof_N` auxiliaries (27k of them from `omega`), ~800 kB of `.olean`: 8 lemmas per module
  gave 4.2–8.7 MB `.olean`s and 20–42 s per module.
- **Trick:** prove the 16 comparison identities once for any width (`range_*` in
  `GoFV/Proof/Rules/RangeLemmas*.lean`, `omega` with `2 ^ w` an atom) and close each residual goal
  by rewriting with one of them plus `simp_all` on the case hypotheses.
- **Effect:** ~12k proof terms per lemma; the eight modules of 8 lemmas are 1.9–2.6 MB and
  11–13 s each (the identities: two modules; the signed ones with `+ 1` alone take
  ~85k proof terms, three `if`s per goal for `omega`).

#### `LEAN_NUM_THREADS` does not limit `lean`; `-jN` does
- **Measured** (official 4.34.1, `GoFV.Proof.Rules.Eq`, 30 theorems): with
  `LEAN_NUM_THREADS=2` (as `scripts/memcap.sh` exports) or `=1`, `lean` still ran 36 threads,
  up to 27 of them runnable, and used 80 s CPU in 20 s wall, the same as with the variable unset.
  With `lean -j2` it used 55 s CPU in 41 s wall. So every Lake build of a module with several
  theorems elaborates them in parallel (`Elab.async`) on up to all 32 cores, whatever the
  environment says.
- **Trade-off** (same session, load 60–80; CPU / wall / peak RSS):

  | module | default | `-j4` | `-j2` |
  | --- | --: | --: | --: |
  | `Rules.Eq` | 69.4 s / 26.3 s / 1.79 GB | 62.4 s / 30.8 s / 1.71 GB | 61.2 s / 58.9 s / 1.69 GB |
  | `Rules.Add2` | 28.4 s / 14.3 s / 1.80 GB | 26.1 s / 15.2 s / 1.73 GB | 25.4 s / 22.7 s / 1.74 GB |

- **How:** `weakLeanArgs = ["-j4", …]` in a `lean_lib` reaches every `lean` that Lake starts.
  It is not traced, so adding it rebuilds nothing (checked), and `-j2` gave byte-identical
  `.olean`s (`SSA.Op`, `Proof.Frame`, `Rules.Neq`). The clifv entry "Threads per Lean process
  don't help us" below was probably measured with the same no-op variable.
- **Adopted:** `-j4` on main 03d6b3f. Verified: a cache-free `lake build +GoFV.Proof.Rules.Eq`
  ran `lean … -j4` with at most 4 runnable threads (was 27), and its `.olean` was byte-identical
  to the copy other worktrees had put into the shared cache. Recorded per module (ff4db5d →
  54979b8, load 45–50 → 35): `Rules.Eq` 86.2 → 63.4 s CPU, `Rules.Neq` 88.4 → 61.1 s,
  `Add2` 32.4 → 26.6 s, `Lsh` 14.2 → 11.2 s; highest CPU/wall 7.2 → 3.4; wall of those
  modules +0–4 s, `Neq` 12.3 → 27.1 s.

#### Generate `match` congruence equations upstream, or sibling modules cannot be imported together
- **Problem:** `simp` in a rule-lemma module generated `binDV.match_4.congr_eq_*`,
  `fieldDV.match_1.congr_eq_*` and `Option.getD.match_1.congr_eq_*` (plus `_sparseCasesOn_*`)
  as *public* constants of that module. `Eq.lean` and `Eq2.lean` both did, and a file importing
  both failed: `environment already contains 'GoFV.Proof.Rules.fieldDV.match_1.congr_eq_1…'`.
  Each module builds fine alone, so only an importer of both notices.
- **Trick:** generate them once in the shared upstream module (`Tactic.lean`):
  `run_meta for n in [``binDV.match_4, …] do discard <| Lean.Meta.Match.genMatchCongrEqns n`.
  Check: read every `.olean`'s `constNames` and report public names defined twice
  (`scripts/axioms-audit.sh` imports all proof modules, which fails on such a clash).
- **Effect:** 35 rule modules import together; no rebuild cost.

#### Audit axioms in one process over all proof modules, not one process per module
- **Measured** (4.34.1, 271 `GoFV/Proof` modules, all built): `scripts/axioms-audit.sh` with one
  `lean` per module (`xargs -P4`) took 118 s wall, 18 min CPU. One `lean` importing all of them
  took 2.5 s wall: the per-module cost was the import, and since 4.34 `collectAxioms` reads
  imported constants' axioms from a precomputed extension instead of walking their bodies.
  Same axioms reported. It counts 11037 theorems instead of 11346: the auxiliary lemmas that
  several modules realize independently (`f.eq_1`, `f.eq_def`, `_sparseCasesOn_N.else_eq`,
  `congr_simp`) are one constant in the joint environment. These do not clash on import; plain
  declarations (and the `match_N.congr_eq_*` of the entry above) do.
- **Requires:** all proof modules import together (issue #133). The nightly gate's `allproof`
  step builds `GoFVTest/Proof/AllProof.lean` (`scripts/gen-allproof.sh`) to keep it so.

#### `first | … | …` does not catch maximum recursion or heartbeats
- **Problem:** six `Trunc` rule lemmas (`(Trunc16to8 (And16 (Const16 [y]) x)) && y&0xFF ==
  0xFF`) failed with "maximum recursion depth" although the alternative that hit it
  (`congr 1 <;> omega` in `rule_shamt`) sat inside `first`: runtime exceptions (recursion depth,
  heartbeats) pass through `first`/`try`, so later alternatives never ran. `congr 1` at default
  transparency had unfolded `BitVec.ofInt 16 c &&& x`.
- **Trick:** run the structural steps of a closer at reducible transparency
  (`with_reducible congr 1`), as already done for `apply`; isolate the culprit by running each
  alternative of the `first` alone on the dumped goal.
- **Effect:** the six lemmas close (`rule_ext`); all 957 rule lemmas rebuild unchanged.

#### Keep a fuel-recursive loop's body in small non-recursive `@[inline]` parts
- **Problem:** `GoFV.Util.PdqSort.pdqsort` (fuel recursion, a ~30-line loop body with tuple
  `let`s and four recursive calls) took 11.6 s CPU to build, almost all of it `simp`/`split`/
  `generalize` over the unfolded body in the permutation proof (`rw [pdqsort]` alone: 4.6 s).
- **Trick:** the recursion is `| fuel + 1, … => pdqStep lt (pdqsort fuel) …`; the body is
  `pdqStep` taking the recursive call as an argument, itself split into `pdqPivot` and
  `pdqPartition`, each `@[inline]` (same compiled code). Each part gets its own small lemma
  with the recursive call abstracted (`hrec`), and the induction step is one `exact`.
- **Effect:** the module went from 11.6 s / 0.51 GB to 1.9 s / 0.48 GB (#41).

#### The kernel cannot evaluate `Std.HashMap`/`HashSet`: use ID-indexed arrays in semantics code
- **Problem:** `decide +kernel` on `(({} : Std.HashMap Nat Nat).insert 3 4).size == 1` gets
  stuck: bucket indices are `USize`, whose size depends on the opaque
  `System.Platform.getNumBits`. `run`'s scheduler used a `HashMap`, so no witness could
  evaluate `run` in the kernel.
- **Trick:** the scheduler (`kahn`, `schedValid` in `GoFV/SSA/Sem/Run.lean`) indexes
  `Array (Option Nat)` by value ID instead; same results (`sem-difftest corpus`: 7,503 defined
  calls, 240,096 later-section runs agree, 0 differ, 0 gaps, as before).
- **Effect:** `run` on the corpus function `clamp` (24 values, 5 blocks, three inputs) evaluates
  by `decide +kernel` in 1.7 s CPU / 0.63 GB for the whole witness module
  (`GoFV/Proof/Witness/Clamp.lean`).
- **Also:** `check`'s `memCheck` used a `HashSet` once a function has no memory `Copy`s (clamp
  has some, so it was not hit); now an ID-indexed `Array Bool`, so `check` evaluates by
  `decide +kernel` on such functions too (`decodedLen` witness, #84). For lookup-only maps keyed
  by a structure (zcse's `vkey`), `Std.TreeMap` with a hand-written `compare` is
  kernel-evaluable and needs no proof about the map: the pass is validated by a checker.
- **Also (#24):** `String.toInt?` and `Array.qsort` get stuck in the kernel as well. prove's port
  read its config with `toInt?` and kept `Std.HashMap`s, a `HashSet` and a `qsort`; with
  `GoFV.Opt.decInt?` (over `String.toList`), `Std.TreeMap`/`TreeSet` and
  `GoFV.Util.PdqSort.sortBy` (unique keys, same order) the whole checked pass on a 5-block
  function evaluates by `decide +kernel` in about 3 s (`GoFV/Proof/Witness/Prove.lean`); prove
  parity and `prove-difftest` unchanged.
- **Also (#32):** a stuck `HashSet` need not fail fast. sccp's analysis kept its executable edges
  (`visited`) in a `Std.HashSet Edge`; `decide +kernel` on the analysis of a 4-block function
  ran out of memory instead of failing (7.5 GB at the cap after 85 s; the witness module with
  three such certificates was killed at 8 GB, also with `Elab.async false`). With an `Array
  (List Nat)` by target block ID (`GoFV/Opt/Sccp.lean`, lookups only, so parity is unaffected)
  the same certificate takes 2.6 s / 0.25 GB and the whole witness module
  (`GoFV/Proof/Witness/Sccp.lean`) 4.7 s / 0.43 GB. When a certificate blows up, first look
  for hash maps on the evaluated path.

#### Kernel `defeq` of `f a` against `f b` unfolds `f`: keep big definitions out of `rfl`
- **Problem:** in `bind_schedule_erase` (`GoFV/Proof/Cong.lean`) the case
  `none.bind (schedule f) = (none.map g).bind (schedule g)` closed by `rfl` made the kernel
  compare `schedule f` with `schedule g` (same head, different arguments), unfold `schedule`
  and the whole Kahn loop: `(kernel) deterministic timeout` at 20,000 heartbeats (hung for
  minutes at the default). `attribute [local irreducible]` does not help: the kernel ignores it.
- **Trick:** close such goals by rewriting with the library lemmas (`simp only
  [Option.map_none, Option.bind_none]`), never by `rfl`, when the two sides apply a big
  definition to different arguments; pass explicit arguments to congruence lemmas
  (`schedule_congr (f := f) (g := g) …`) so elaboration does not unify through it either.
- **Effect:** the module checks in 0.7 s CPU.

#### Literal fuel in a search makes the kernel expand it on symbolic arguments
- **Problem:** `GoFV.Opt.SchedFast.rename ids a := bsearch ids a 64 0 ids.size` (binary search,
  fuel 64). Each proof of `GoFV/Proof/SchedFast.lean` mentioning `rename` hit `(kernel)
  deterministic timeout` after 3–7 minutes wall (66–111 min CPU per `lean` run): with a literal
  fuel the kernel's defeq checks unfold `bsearch` 64 levels deep on a symbolic `ids`, a binary
  tree of `if`s.
- **Trick:** fuel `ids.size` (enough: `log₂ size + 1` steps): no literal to unfold, so the
  symbolic `bsearch` stays stuck. Same compiled behaviour.
- **Effect:** the module checks in 0.9 s wall.

#### Checker scheduling over block-local IDs (`schedFast`, #147)
- **Problem:** `Sem.schedule f b` allocates about seven arrays of size `maxNodeId` per call;
  checked CFG passes reschedule blocks per rewrite, so on big functions this dominates.
- **Trick:** `GoFV.Opt.SchedFast.schedFast` sorts the block's node IDs (`PdqSort.sortBy`,
  kernel-evaluable), renames them to their index (binary search), runs `kahn` + `schedValid`
  on the renamed block and maps back; `schedFast_spec`/`schedFast_filter` transport
  `SchedSpec` through the monotone renaming.
- **Effect:** `sched-fast-bench` on the 400 largest full-corpus files (8,832,498 blocks): output
  identical on every block; `schedule` 142.7–214.3 s, `schedFast` 24.3–24.6 s (5.8–8.8×, two
  runs on a loaded machine). Quick corpus (9,297 files, 2,961,638 blocks): identical, 13.7 s →
  7.5 s.

#### Checked CFG steps: snapshot before, check in place after, frame lemma for the rest
- **Problem:** a translation-validated rewrite step that keeps its input `f` to compare with
  the result `g` (or to fall back to) makes the rewrite copy `f`'s value and block tables (Lean
  arrays are copy-on-write: `f` is no longer unique), and any table-wide comparison (`check g`,
  even a pointer-first `tabEq`) costs O(function) per rewrite. Short circuit on full-v2 with
  `check` per fusion (#139): 667 s, vs 6.5 s unchecked (issue #147).
- **Trick:** (1) no `check` of the result: derive well-formedness and use dominance of `g` from
  the step relation (`FusePlainPres`), check the pass input once; (2) `@[noinline] snapOf f`
  runs the pre-check on `f` and copies only the entries the rewrite will change (here: the run's
  values, `b₀`'s predecessors, block `c`, the source non-pure sequence); then the rewrite runs on
  the now-unique `f` in place, and `postOK snap g` checks only those entries; a proven frame
  lemma (`fuseRun_frame`: entries outside the run's values and blocks and `b₀`'s predecessors
  are unchanged) replaces the table-wide comparison; (3) a rejected rewrite is an `Except` error
  and the pass returns its input (`Fuse.orInput`: one copy per pass, not per rewrite);
  (4) `rankOK` compiled as a linear scan via `@[csimp]` (`rankOKFast`), and `schedValid`'s
  pure-node table built once (#171).
- **Effect** (pass time, `pass-parity`, load 30–60; checked / unchecked):

  | | quick | full-v2 | 400 largest full files |
  | --- | --: | --: | --: |
  | short circuit, `check` per fusion (#139) | 7.1–8.0 s | 667 s | – |
  | + no `check`, local `tabEq` checker, rankOKFast (#171) | 2.0 s | 27.5 s | 18.7 s |
  | + snapshot / in place / frame lemma (#181) | 0.5 s | 13.3–15.2 s | 4.3 s |
  | + `schedFast` in the checker (#180) | 0.6 s | 8.4 s | 1.8 s |
  | unchecked | 0.1 s | 3.0–6.5 s | 0.4 s |

  Before `schedFast`, `Sem.schedule` took 3.2 of the 4.3 s on the 400 largest files (arrays of
  size max-value-ID per call). With both checker schedule calls removed (an unsound ablation)
  the step costs 1.1 s there, so the rest of the gap is the checker's own O(run) work
  (snapshot lists, `postOK`), which unchecked fusion does not do. Early fuse on full-v2: 13.2
  → 4.7 → 3.3 s (unchecked 1.3 s).

#### branchelim: no `check` per rewrite (#147)
- **Problem:** `BranchElim.stepOK` ran `checkOK ce g` on every accepted rewrite, and `relB`
  compared every value and block table entry (`List.range f.valueTab.size`, `f.blocks.all`).
- **Trick:** as for plain fusion (PR #171): the proofs run on path dominance (`UseDom`,
  `SDom`) instead of the certificate, `DRel.wf_pres`/`DRel.useDom_pres` derive `WF`/`UseDom` of
  the result from the relation (`GoFV/Proof/Pass/BranchElimPres.lean`), and the checker compares
  the unchanged table entries with `tabEq` (pointer first); the pass checks its input once.
- **Effect:** branchelim pass time, interleaved A/B with the same build (`pass-parity
  --pass branchelim`, load 26–30): full-v2 14.4/15.2 s → 12.3/13.7 s; quick 0.7–0.8 s →
  0.7 s (only 729 rewrites on quick). The remaining time is the rewrites themselves, the
  `loadAddr` set and the single input `check`.
- **Follow-up (`npSeqOK` on `schedFast`):** within noise (quick 0.6–0.8 s either way). On the
  400 largest full-v2 files (`--jobs 1`, 3 interleaved runs, load 24–65) branchelim took 2.4–4.0 s
  before, 2.1–4.9 s after, 1.9–2.7 s with no step checker at all (unsound ablation), and 0.6–0.9 s
  without the input `checkOK ce f` (unsound ablation). The step checker costs at most noise. An
  in-place snapshot step (#181) cannot gain 10%, so it was not built; as for early fuse (#187),
  the input `check` is the lever.

#### early fuse: the single input `check` dominates (#187)
- **Measurement:** with every rewrite checked locally (comparison fusion `tabEq`/pointer-first,
  plain fusion in place) early fuse takes 14.0 s on full-v2 (`pass-parity`); without the one
  `checkOK ce f` on the pass input (unsound ablation) 6.3 s, unchecked port 2.3 s. The
  comparison checker itself is within noise (5,847 fusions on full-v2). Next lever for the
  checked CFG passes: the input `check`, not the step checkers.
- **Proof elaboration:** composing pure checked steps inside a `do`/`let (f, c) := …` step
  (`earlyStep_ok`) by `simp [earlyStep]` or `rfl` against a projection form times out at 200k
  heartbeats (`whnf` unfolds the checkers). `generalize step f b = r at h k; obtain ⟨f1, c1⟩ :=
  r; dsimp only at h k` per step keeps it to a second; without the `dsimp` the pair `match`
  stays and the next `generalize` silently misses its target.

#### Checked CFG passes: a slim input check instead of `check` (#147)
- **Problem:** branchelim and early fuse ran the full `check` on their input only to get
  `Dom.WFDom` (`WF` + `UseDom`). Most of `check` is facts these proofs never use: types, aux
  kinds, block kinds, Go's dominator tree, loop nest, use counts, `memCheck`, argument shapes.
- **Trick:** `GoFV.SSA.wfDomCheck` = `wfCheck` (`checkGo`'s structural loops, one per-value
  shape test `WFCheck.valueOK`: arity, `Phi` arity, `Bool` auxint, block) then
  `DomCert.check`; `wfDomCheck_wf`, `Dom.WFDom.of_wfDomCheck` (UseDom through the shared core
  `Dom.use_dominated_of`/`UseDom.of_cert`). The `checkGo_wf` proof carries over almost
  verbatim (same `Loop1`/`Loop2` invariants, `valueOK_spec` instead of `checkValue_ok`).
- **Effect** (`lake exe check-bench`, all sections, accepted by both): quick-v1 306,801
  sections, `check` 14.7 s → `wfDomCheck` 3.3 s (`wfCheck` 1.1 s, `DomCert.check` 2.2 s of
  which `DomCert.make` 1.1 s); full-v2 3,185,523 sections, 369 s → 85 s. Pass time
  (`pass-parity`, old/new binaries alternated, two rounds, load 29–61): early fuse full-v2
  14.9/23.6 s → 8.4/12.1 s, quick 0.8/0.6 → 0.3/0.3 s; branchelim full-v2 11.0/15.3 s →
  6.8/8.9 s, quick 0.6/0.5 → 0.2/0.2 s. Parity 100% on both corpora.
- **Short circuit too** (`constPhiArgsChecked_refines` needs `CertOK f` for zcse's
  simulation, which `WFDom` lacks but `wfDomCheck` gives: `wfDomCheck_domCert`). Full-v2, three
  binaries alternated, two rounds, load 27–53 (`checkOK` input guard → `wfDomOK` →
  unchecked port before #121/#139): short circuit 50.4/31.4 → 20.4/13.3 s (unchecked
  4.8/2.8 s), early fuse 27.7/17.3 → 10.0/6.4 s (1.9/1.2 s), branchelim 21.9/15.4 → 8.2/5.2 s
  (3.0/1.7 s). What remains of short circuit's gap is its rewrite checkers, not the input check.
- **What was left:** `DomCert.make` was half of the slim check; done in the next entry.

#### Dominator certificate: textbook Lengauer–Tarjan, one ancestor path per block (#147)
- **Ablation** (main 6b3d35f, `pass-parity`, same session, min of 3; 400 largest full-v4
  files, `-j1`): short circuit 2.7 s as is, 1.4 s without the `wfDomOK` input guard, 1.3 s
  without step checkers, 0.4 s without both; early fuse 1.9/0.9/0.8/0.2; branchelim
  1.4/0.6/0.7/0.2; late fuse (per-If `checkOK`) 3.2 → 0.7 s without step checkers. Input guard
  and step checkers cost about the same on big files; on quick-v3 the step checkers dominate
  short circuit (0.7 → 0.4 s without them vs 0.5 s without the guard). The earlier "input check
  dominates" was measured with the full `check` guard (before `wfDomCheck`), "per-rewrite
  checkers" on quick: both were right for their setting.
- **Where `wfDomCheck` went** (big400 short-circuit inputs): `wfCheck` 0.3 s, `DomCert.make`
  0.4–0.9 s (Go's verbatim `dominatorsLTOrig`: never-emptied buckets are rescanned once per DFS
  child), `usesOK` 0.6–1.1 s (103 M tree-walk steps, one walk per use).
- **Trick:** `DomCert.make` uses its own `ltIdom` (Go's algorithm with buckets emptied; any
  correct tree passes the certificate checks, so nothing about it is proven; depths along its
  DFS preorder, no postorder) — a definition change, allowed because proofs use only `make_eq`
  (`make` depends on `cfgView f` only). `@[csimp] make_eq_ofView` drops the `cfgView` copy;
  `@[csimp] usesOK_eq_usesOKFast` keeps one ancestor path array along the block list
  (`fixPath` rewrites only the part that differs from the previous block) for functions with
  ≥ 32 blocks. Read the path with `getD`, not `p[i]? == some a`: the `Option` allocations made
  the first version 50% slower than the walks on quick. Cooper–Harvey–Kennedy measured equal to
  textbook LT (0.16 vs 0.13 s on big400), not adopted.
- **Effect** (`check-bench`): big400 short-circuit inputs `wfDomCheck` 1.33 → 0.61 s (make
  0.43 → 0.14, usesOK 0.55 → 0.17); quick-v3 all sections 3.40 → 3.03 s (`DomCert.check` 2.21 →
  1.77); full-v4 3,185,589 sections 78.9 → 67.8 s (`DomCert.check` 56.0 → 39.8, make 28.0 →
  15.7; the second run was ~13% more loaded, `checkGo` 205 → 232 s). Same trees as
  `Analysis.dominators` on every section; `check` and `wfDomCheck` reject nothing. Pass time,
  big400, 8 alternated runs each: short circuit min 2.4 → 1.9 s, early fuse 1.5 → 1.2 s,
  branchelim 1.0 → 0.8 s (−20%); quick/full within load noise. Kernel-evaluated witnesses
  that run `check`/`wfDomOK` got faster too (9 modules, median CPU 36.0 → 29.3 s).

#### Short circuit's checked `shortcircuitBlock`: WFDom of the result from local checks (#16, #147)
- **Problem:** `scOK` (#236) ran `wfDomOK g` (the whole-function `wfCheck` + dominator
  certificate) on every one of the 66,494 rewrites of full-v4, diffed both tables to find the
  changed blocks, compared both tables again (`frameOK`) and scanned all values (`scanOK`);
  `schedOK` computed two `Sem.schedule`s (tables of size max-value-ID) per checked block.
- **Trick:** (1) no `wfDomOK g`: `WF ce g` (`ShortCircPres`) from `f`'s and per-block checks of
  the touched blocks `K` (`wfKOK`: `wfCheck`'s block loops, edges to blocks outside `K` keep their
  indices); `UseDom g` (`ShortCircUseDom`) from `UseDom f`: a path of `g` maps to a path of `f`
  with `b` inserted (`p → t` ↦ `p → b → t`), uses shared with `f` keep their blocks, and the new
  uses are checked locally (`useOK`: defined in the use's block, a `Phi` argument of `b` at a
  block every path to which passes `b` (`dsOK`: a closed set, the *largest* one, since the plan's
  blocks can form loops), a moved phi outside the plan's blocks (`closeOK`: paths leave the plan's
  blocks only through the moved phi's block)); (2) `K` = the blocks `applySite` touches (`b`, `t`,
  `p`, the plan's blocks, `b`'s last predecessor's block) instead of a table diff; `frameOK`/
  `scanOK` compare raw entries pointer-first without allocating; (3) `schedOK` skips the
  schedules when the block's schedule nodes are unchanged (same schedule).
- **Effect** (`pass-parity --pass "short circuit"`, pre-#236 main f3bb926 / main 801a98c /
  this, alternated, two rounds): full-v4 `--jobs 4` (load 48–142) 13.1/14.8 → 50.6/48.1 →
  18.2/18.7 s (1.3× the unchecked step); 400 largest full-v4 files `--jobs 1` (load 26–62)
  3.1/2.7 → 18.0/24.3 → 4.5/4.0 s. Ablations on those 400 files: `wfDomOK g` was 23 of the 30 s
  overhead; with it gone, the table diff + `frameOK` 3.7 s and `scanOK` 2.2 s (`--jobs 4`), then
  `schedOK` about half of the rest; the table copy that keeping `f` costs is within noise (a
  snapshot/in-place step would not pay here). What remains is `blockOK`'s per-block work.

#### Rule lemmas: kernel "deep recursion" from `rfl` simp lemmas (#69, RuleProofs10)
- **Problem:** `divmod.rules:171/180/206/232` and `generic.rules:369/372` elaborated, but the
  kernel rejected the theorem with "(kernel) deep recursion detected" as soon as the proof used
  the condition; `set_option maxRecDepth 20000` did not help. A scan of the proof term
  (`Kernel.isDefEq` on every argument whose inferred type differs syntactically from the
  expected one; 1 min instead of 21 min for a top-down `Kernel.check` bisection) found the
  failing check: `simp` applies `@[defeq]` (`:= rfl`) lemmas such as `Option.getD_some`,
  `Option.elim_some` without a proof step, so a `congrArg` of the next rewrite expects
  `bif umagicOK 64 c then X else …` but gets `(some (bif …)).getD d` (or `if x < y then …`
  against `(some y).elim …`). The kernel's lazy delta unfolds the `bif`/`if` side and
  evaluates `umagicOK 64 c` / `Nat.decLt` on symbolic 64-bit terms.
- **Trick:** the same rewrites with a proof term (`getD_some_p`, `elim_some_p` proved
  `by simp only [Option.getD_some]`, so not `@[defeq]`); `rule_unfold_getd` keeps
  `Option.getD` out of the condition's `dsimp`, and `open GoFV.Proof.Rules.KernelSafe` makes
  `rule_norm` (also inside `rule_split1`) use them: listed explicitly they are tried before the
  `rfl` lemmas of the simp sets (`simp only [set, -lemma]` does not erase from an attribute
  set, it only warns), `GoFV/Proof/Rules/TacticCond.lean`.
- **Effect:** the five `divmod` lemmas check (`DivmodU2.lean` 8.8 s / 1.6 MB, `DivmodU3.lean`
  4.0 s / 1.1 MB); no other module changes.

#### Split a checker's long `if` chains into small definitions before proving about them (#36)
- `roleRun` (writebarrier's checker) dispatched on seven ops in an `if` chain inside a list
  recursion. `unfold roleRun at h; split at h` in `roleRun_then` hit the `whnf` heartbeat limit,
  and `roleOf_then`'s fallback case stayed unsolved. Moving the op dispatch into `thenRole` and
  the fallback into `otherRole` (same behaviour), with one lemma per helper
  (`thenOp (thenRole v j) = some (j', o) → j' = j ∧ v.op = o`, `thenOp (otherRole g x) = none`)
  and `by_cases` + `rw [if_pos h]`/`rw [if_neg h]` per branch of `roleRun`, made the whole module
  check in under 3 s.
- `rcases` patterns flatten conjunctions to the right: a lemma ending in `… ∧ P ∧ Q` where `P`
  is an `∃` needs `⟨…, ⟨p1, p2, …⟩, -⟩`; a flat pattern sends `Q` into `cases`, which fails with
  "dependent elimination failed" on an equation of a big term.

#### Rule tactics: `rule_norm` without `decide := true`, `rule_pow2`'s alternatives at reducible transparency
- **Problem:** the rule modules are half of a cold `lake build` of `GoFV` (perf/history.tsv at
  2ac1805: 1,489 of 2,987 CPU-s), spread over 170 modules of one-line `by rule_auto`/`rule_range`
  proofs. `trace.profiler` on OrB2 and Xor2: 65–75% in `rule_norm`, the `simp_all` after every
  case split (38 calls in one `rule_range` proof). `decide := true` evaluated a `Decidable`
  instance at every proposition, most of them stuck on leaf reads. (Correction: the
  `diagnostics` counts first quoted here, `PEnv.ty`/`auxInt`/`leaf` unfolded 40,851/24,176/12,355
  times in one theorem, are the same without `decide`; they are projection reductions while `simp`
  indexes terms, not `decide`'s work.) In Neq5, 23 elaborations of `rule_pow2`'s `first | exact divisible_pow2_u … | … |
  exact divisible_pow2_s_ne …` took 20 s: on a signed `!=` goal the `_u_ne` attempt failed after
  ~2.85 s of default-transparency unification through `bne` and `BitVec.sdiv`.
- **Trick:** `rule_norm` without `decide`, with `Int.reduceEq/Ne/BEq/BNe`, which decide what
  `decide` was needed for in most proofs (`if 8 == 0` of a literal divisor). The 8 proofs that
  still need `decide` (`generic.rules:2246`/`:2247` in RotateLeft6/8/10/12) call `rule_auto_dec`
  (option `gofv.ruleNorm.decide`) directly; `rule_auto` falls back to it only for proofs not yet
  marked (a fallback alone made those 8 pay a failed attempt: RotateLeft8 19.9 → 33.0 s).
  `with_reducible exact` for the four `divisible_pow2_*` alternatives: a wrong one fails on the
  head symbol. Dropping `decide` alone broke 13 proofs in 9 modules although a three-module
  sample had passed: check such a change with a full build.
- **Effect** (4-core 8G orb, cold `lake build` of `GoFV`, no Lake cache, nothing else running,
  same session): main 821.5 s wall / 3,195 CPU-s → 744.6 s / 2,922 CPU-s (−9.4% / −8.6%). Single
  modules (`lake env lean`, CPU): Neq5 40.9 → 20.6 s, Xor2 34.0 → 28.3 s, OrB2 26.0 → 21.9 s,
  RotateLeft4 10.9 → 9.7 s, RotateLeft8 19.9 → 21.9 s. Types of all 11,318 `GoFV` constants the
  rule modules see unchanged (two new syntax constants), axioms audit 0 violations.

#### Whole-tree profile: private `match` equations regenerated per module, kernel-heavy `rfl`s
- **Problem** (`lean -Dprofiler=true` on all 985 modules at f53b580, 4-core orb: 4,906 CPU-s; 28%
  `simp`, 22% kernel, 20% tactics, 12.5% import): (a) ~21,000 private `match` equations and
  splitters across the tree. A `split`/`simp` on a big `match` on a variable realizes them in the
  module doing it, and generating them upstream does not help (they are private to the
  generating module; checked with a two-module scratch build). `evalOpL` (91-arm) in 15 modules,
  ~12 s each; `argShapeOk` (64 equations) once per *theorem* in the rule modules that use it
  (asynchronous elaboration: 20 times in FloatRules, 88 s of 300 s profiled). (b) Three private
  copies of `entryFrame_makeL` proved by `split <;> rfl` on the concrete `Ctx.make tabs f`: ~41 s
  of kernel each. (c) Field equations of a concrete `removePred`/`removeSucc` by `rfl`: structure
  eta on the whole `Func` first.
- **Trick:** (a) state the `match` once as an `if` chain on a `Bool` predicate
  (`GoFV/Proof/EvalOpLDispatch.lean`, `evalOpL_eq`, by cases on the op) and rewrite with it; the
  four local copies of the 91-op set get one-line bridges (`cases op <;> rfl`, ~3 s; for a list,
  `cases op <;> first | exact absurd h Bool.false_ne_true | decide +kernel`, 4 s, where `decide`
  on membership for all 800 ops took 26 s). For `argShapeOk`, always applied to a constructor, a
  dsimproc (`reduceArgShapeOk`, like `reduceCallH`). (b) `entryFrame_tys` by `rfl` at an
  arbitrary context. (c) the same field equations at an arbitrary `Func`. Also `evalAll_spec`
  calls pass the `TopoRem` argument as `(by exact h)`, elaborated after the argument that fixes
  the implicit `ctx` (Enter, Avail 3.0 → 0.6 s).
- **Effect:** cold `lake build` of `GoFV` (989 jobs, no Lake cache, 4-core 8G orb, two modules at
  a time: `LEAN_NUM_THREADS=2`, as three or four were OOM-killed by the orb's 6 GiB workload
  cap), main f53b580 then this change, back to back: 1,797.7 s wall / 5,098 CPU-s → 1,536.4 s /
  4,406 CPU-s (−14.5% / −13.6%). CPU, module alone, before → after: CopyElimL/CSELSim/UnreadLSim ~42 → 1 s each;
  NilLateLEval 43.6 → 16.6, UnreadLOps 53.1 → 34.1, CSELOp 33.3 → 18.2, EvalL 31.9 → 20.6,
  MoveLOps 20.3 → 8.9, CopyFragL 14.5 → 4.9, FloatRules 50.8 → 38.8, RewriteTermNat 66.3 → 56.8,
  DeadEdge 7.1 → 3.2. Not fixed: `arm64Op`'s matcher (3–4 s in ~12 modules; its 25 arms differ, so
  no single dispatch lemma), and `rule_norm` itself: all 38 of its `simp_all` calls in a
  `rule_range` proof make progress, so skipping unproductive ones gains nothing.

#### prove validator: `rng` evaluated once per level and value via `@[csimp]` (#189, #24)
- **Problem:** `gofv-ssa-opt --check --verified` on quick-v3 did not finish in 90 min:
  `proveChecked` took 13 s on `test/append verifyStruct` (stock `prove`: 0.1 s). gdb sampling
  (perf is not allowed here; `gdb -batch -ex run` with `SIGINT`s, `thread apply all bt`):
  about 65% in `branchOK > decides > rng`. `rng` recurses 4 levels into the other side of every
  path fact on its value, so a value with many bounds checks costs (facts on it)^4 fact scans;
  `asmOf` ran twice (`revert`, `proveRel`) and on functions `prove` left unchanged.
- **Trick:** `rngFast` (`GoFV/Opt/ProveCheck/Range.lean`): top-down demand sets per level, then
  bottom-up `HashMap` tables per level, each entry `rngStep` (= `rng`'s body, `rng_succ` by
  `rfl`) from the table below, a missing key falling back to `rng`; `@[csimp] rng_eq_rngFast`
  (the fallback makes the proof independent of the demand computation). `asmOf` once per run,
  and none when `prove` changed no definition or terminator (`asmFor`).
- **Effect:** `verifyStruct` 13.7 → 2.3 s (`--verified --from prove`); `prove-probe` on
  quick-v3 `test` 3 min 10 s → 20 s with identical output; quick-v3 `--check --verified --jobs 6`
  in 88 s (no SLOW lines).
- **Then on full-v4** (104 min, four functions 27–92 min each): `ECCheck.depB` (expand calls'
  checker) searched every path back through a block's shared arguments — exponential;
  `depBFast` (`@[csimp] depB_eq_depBFast`, a table of fuel levels at which a value already
  failed; correct by `depB_mono`) took `walk.maplit` from 92 min to 0.6 s. `emptyFragB` built the
  dominator certificate `make f` inside `f.blocks.all fun bid => …` once per block (the compiler
  does not hoist it out of the lambda); a `let` outside fixed `rewriteValueAMD64`. full-v4
  `--check --verified --jobs 6`: 104 → 20 min (slowest function 3 min: prove's linear-fact
  search, `linFacts`, on functions with long fact lists).

#### Verified pipeline through `trim`: `copyLFragB` built `Ctx.makeL` once per copy (#385)
- **Problem:** `--check --verified` (through `trim`) spent 2,472 s on `cmd/internal/obj/arm64/init`
  (33,194 values): `gofv-ssa-opt --verified --profile` (per-piece timings) put 1,177 s in the guard
  of `lowered deadcode for cse` alone. `CopyElim.shapeOKB` read `(Ctx.makeL tabs g).tys` (and
  `g.lowered`) for every `Copy` of the function, so `copyLFragB` rebuilt the whole context per
  copy; right after `lower` the function is full of copies. Same pattern as `emptyFragB` above.
- **Trick:** `shapeOKB low tys` takes `g.lowered` and the shapes as arguments; `copyLFragB` binds
  them with a `let` outside the `f.blocks.all` lambda (`copyLFrag_of` unchanged but for the
  arguments).
- **Effect:** that guard 1,177 s → under 1 s; `obj/arm64/init` 2,472 → 103 s in the check;
  full-v9 `--check --verified --jobs 4` 1 h 28 min (5,274 s, 1.65 GB peak) with the slowest
  function at 414 s (`ssagen.simdAMD64Intrinsics`, 73k values, mostly Phase 1). The `regalloc`
  checker is not a bottleneck: `certify` + `checkWith` take 209 + 193 s on `obj/arm64/init`
  (list-based facts), but `tabsAgreeL` rejects that function first; on the other profiled giants
  (`ppc64asm.init` 69k values, `(*regAllocState).regalloc`) they take under 7 s.

#### Verified pipeline: `flagAllocB` built `Ctx.makeL` once per block (#385)
- **Problem:** with flagalloc wired into `loweredVPasses`, `--verified --profile` on
  `(*Builder).build` (4,761 values, 486 blocks) put 5.8 s in flagalloc's guard, and on
  `obj/arm64/init` (33,194 values, 2,739 blocks) the guard did not finish in 15 min.
  `blockB` read `(Ctx.makeL tabs f).tys` and `(Ctx.makeL tabs g).tys` per block, so every block
  rebuilt both contexts (with every block's schedule). Same pattern as the two entries above.
- **Trick:** `blockB tf tg` takes the shapes; `flagAllocWith` binds them with a `let` outside
  `f.blocks.all` (`blockB_spec`/`flagAllocWith_spec` state them as `(Ctx.makeL tabs _).tys`).
- **Effect:** the guard 5.8 s → 12 ms on `(*Builder).build`, > 800 s → 1.1 s on
  `obj/arm64/init`; full-v9 `--check --verified --jobs 4` with all four passes wired 81 min
  (4,859 s, 1.67 GB peak, on a loaded machine). `pairB` (MoveL's `okCert` fixpoint, about n
  rounds of n values on rejected functions) took 15–23 s on `obj/arm64/init`; P2ProofPair2's
  worklist `okCert` (agent/pairperf) brings that file to 3 s.

## Inherited from clifv (measured there, eth-act/clifv `LEARNINGS.md`)

None of these weaken what is proven: every compiler theorem still prints only `propext`,
`Classical.choice` and `Quot.sound`, and the kernel checks every proof.

### Kernel evaluation (`decide +kernel`, `rfl`)

#### Scan Lists, not Arrays, in kernel-evaluated code
- **Problem:** `Array` combinators (`find?`, `foldl`, …) are well-founded recursive. The kernel evaluates them very slowly. Every Stock module that runs `Stock.lower` under `decide +kernel` looked up `"lower"` in the 2,483-term ISLE program with `Array.find?`.
- **Trick:** define the lookup as a `List` scan and add an `@[csimp]` theorem that swaps the `Array` version back in for compiled code, so runtime is unchanged.
- **Effect:** a 700-element scan went from 4.3 GB / 17–30 s to 0.48 GB / 0.25 s; `program.termByName? "lower"` from 4.65 GB / 17 s to 0.79 GB / 2.6 s (BuildDiet, `FV/Isle/Syntax.lean`; branch `agent/build-diet`, being merged).

#### Prefer structural recursion to well-founded recursion
- **Problem:** the kernel cannot reduce well-founded definitions efficiently (or at all, in practice). `fitsCl`/`fitsTy` in `DefGenDom` used well-founded recursion, and every `decide +kernel` check over them failed.
- **Trick:** rewrite them with structural recursion (fuel or the list itself), with the same equations.
- **Effect:** the failing `DefGen` certificates now pass (T6).

#### Avoid `rfl`-based simp steps on big concrete terms
- **Problem:** `StockCmpWithFlags` elaborated in 1.9 GB, but the kernel needed 23 GB to re-check one `simp` step of `isel_eval`: monad-law lemmas proved by `rfl`, applied to a large concrete state.
- **Trick:** use copies of the monad laws proved by `rw` instead of `rfl` (a local `isel_eval_k`).
- **Effect:** 23.6 GB / 128 s → 2.1 GB / 21 s (branch `agent/build-diet`, being merged). The same change did not help three other heavy Stock modules, so measure before changing a shared tactic.

#### Never reduce the whole generated program in the kernel
- **Trick:** compute table properties with an untrusted generator that writes literal data, then check the data with small leaf-wise `decide +kernel` certificates (e.g. `TermSetData.lean` + `KillTab.lean`, `IselPrgTab.lean`). Split each conjunction and check one entry per leaf.
- **Why:** whole-table `decide`/`native_decide` hit 20+ GB or needed compiled evaluation. Leaf-wise checks stay small and need no extra axioms (T6 removed every `native_decide` from the compiler theorems this way).

#### `assumption` at reducible transparency
- **Problem:** after `ArmState` gained a field, `stlxr_congr` in `LoopRun.lean` ran out of heartbeats even at 8M: `assumption` was unfolding the state structure.
- **Trick:** run the tactic's `assumption` with reducible transparency.
- **Effect:** the file compiles in about 30 s.

#### Feed `omega` the `div_add_mod` facts for nested `%`/`/` by large powers
- **Problem:** `ofAddr_adj` (`GoFV/Proof/Pass/MoveLPairMem.lean`) needs `(r + w) % 2^24 = r % 2^24 + w` from equal `r / 2^42` and `r % 2^42 / 2^24`. `omega` elaborates it, but the kernel rejects the proof term: `(kernel) deep recursion detected` (raising `maxRecDepth` does not help, and the elaboration took 57 s).
- **Trick:** state the decompositions yourself (`Nat.div_add_mod x (2^42)`, `Nat.div_add_mod (x % 2^42) (2^24)`, `Nat.mod_mod_of_dvd`, `Nat.mod_lt`) and give `omega` the linear facts.
- **Effect:** the lemma checks in about a second, and the whole module in about 2 s.

### Module structure and imports

#### Don't import umbrella modules from hub files
- **Problem:** the generated `IselData.lean` imported the whole `FV.Backend` umbrella but used only `Isel`/`MInst`. Nearly every isel proof and every Stock module sat downstream of it.
- **Trick:** import only the modules actually used.
- **Effect:** a change to `Unwind`, `Regalloc`, `DeadCleanup`, … rebuilds about 330–445 modules instead of 1,630–1,690 (Stock: 1,116 → 78–112), about 12.3 h → 2 h of module time (#323).
- Similarly, `FV.Opt.Proof.*` no longer imports `FV.Backend` (#257), so backend changes don't rebuild the 317 rule modules. Don't add such imports back.

#### Split heavy modules
- Lean builds one module per process and a module's peak is roughly its heaviest declarations together. Splitting a heavy file into parts (keeping the old module as a file that imports the parts, so importers don't change) lowers the peak and lets the parts build in parallel.
- **Effect:** e.g. `RuleRestEmbed` 16.9 GB → ≤ 8.3 GB per part, `RuleBitops7` 16.5 → 6.4 GB, `RuleShifts3` 15.2 → 9.4 GB (branch `agent/build-diet-rules2`, being merged; single-file measurements under load).
- Don't over-split: evm.fast-dev found larger checkpoint groups built faster warm (see below).

#### Don't depend on private library internals
- A proof that reached into the private internals of `Array.qsort` would break on a toolchain update. Sorting `cfg.loops.attach` instead carries the membership fact through the sort, with the same output (#318).

### Build infrastructure

#### Threads per Lean process don't help us
- Going from 2 to 8 threads gave no measurable gain on the slow modules: they spend their time in one declaration on one thread. Across 4,198 recorded module builds the median CPU/wall ratio was 1.01 (BuildAccel).
- **Exception:** `Elab.async` matters for `bv_decide`-heavy modules (`RuleExtends`: 1,652 s off vs 174–186 s on, at about twice the memory).

#### Memory-cap every Lean process; share one Lake cache
- `scripts/memcap.sh` runs each command in a memory-capped cgroup (with a `/proc` watchdog fallback when the systemd user manager is down, #325). Without caps, one runaway `lean` triggered global OOM kills.
- `FV_LAKE_CACHE` points every worktree at one shared Lake artifact cache (hard links; same filesystem as the worktrees): a fresh worktree at a built commit needs no rebuild (#253).
- `scripts/lake-serial-build.py` builds module by module with caps from recorded peaks, runs light modules packed and heavy ones alone (#258).

#### Wrapper tools don't make cold builds faster
- [turbo-lean](https://github.com/Th0rgal/turbo-lean) is not a Lean build: `turbo-lean build` runs the project's own `lake build` and caches the outputs. Its fast paths are cache hits and per-theorem checks against `sorry`-stubbed prefixes, which a gate cannot accept.
- Measured on 7 heavy modules, run at the same time with the same caps: +4.1% wall, +1.4% CPU (a fixed ~35–50 s per call for hashing and ingest), same peak RSS, identical statements and axioms for all 22,322 constants. Not adopted (TurboLean, `docs/research/turbo-lean.md`). Our cost is kernel checking of single large declarations; only proof changes reduce it.

#### Some `.olean`s are not deterministic, so rebuilding them invalidates every dependent
- `IselTermFactsCall` and `IselCtlTry` produce different `.olean` bytes on every build (three builds, three hashes); the other 5 sampled modules are byte-identical. Statements and axioms don't change.
- Rebuilding `IselTermFactsCall` without the cache therefore rebuilt 30 downstream modules, including `KillTab` (~1,930 s). Restore such modules from the Lake cache instead of rebuilding them (TurboLean).

#### Merge first, verify on main
- When main moves faster than a full rebuild, a branch that passed its full checks on a recent main and rebases cleanly needs only a targeted build; a continuous main gate runs the full list afterwards and failures are fixed forward. A wrong merge can make main fail to build; it cannot make a false theorem pass, because the kernel checks every proof.

### From other projects (not yet measured in clifv)

From [Th0rgal/evm.fast-dev](https://github.com/Th0rgal/evm.fast-dev) (`docs/PROOF-PERFORMANCE.md`). All keep ordinary kernel checking and standard axioms. Move an entry up into the sections above once it has been measured here.

- **Kernel-opaque checked caches:** `opaque boxedValue (v : α) : {r : α // r = v} := ⟨v, rfl⟩`, used through its checked equation; full-transparency kernel reduction cannot reopen it. Reported: a 49 GiB timed-out monolith → 3–4 GiB checkpoint certificates. Candidates here: large intermediate states in Stock certificates.
- **Rewrite at the outer boundary:** prove a structural/pure evaluator equal to the executable one once, rewrite at the top, then `rfl`. Unfolding the concrete result and rewriting inside instead was 2× slower (8.8 → 19.9 s).
- **Remove repeated indexing:** proving repeated indexed extraction equal to one linear `flatMap` took a check from an unfinished 5 minutes to 39 s.
- **Compact certificates:** `of_decide_eq_true (by kernel_rfl)` (with `kernel_rfl` = `goal.refl (check := false)`) instead of `decide_cbv` shrank a 30.6 MB `.olean` to 33 KB and halved replay. clifv's `RuleAll` already uses the `check := false` idea.
- **Compact generated data:** typed DAG literals with small single-use nodes inlined shrank 9 MB ASTs to 0.3 MB (61 → 15 s).

## From kevaundray/lean-skills (measured there on Lean 4.34.0 unless noted; `~/.agents/skills`)

Skills `lean-proof-performance`, `lean-build-hygiene`, `lean-asm-proofs`, `fast-lean`; every
number comes from `examples/` there (`examples/run.py <name>`) or from the projects it credits.
Adopted: `weakLeanArgs` linters off (d891ea9) and the two entries under "gofv measurements"
above. The rest applies as rules; move an entry up once measured in gofv.

- **Deterministic `.olean`s:** linter warnings are stored in the `.olean` with the absolute
  source path, so the same module built in two worktrees differs and every importer misses the
  shared cache. Diagnostics-only options go in `weakLeanArgs` (not traced, no rebuild);
  `leanOptions`/`moreLeanArgs` only for options that change results.
- **`:= rfl` makes a lemma `@[defeq]`** (Lean 4.26–4.35): `simp` then uses it without a proof
  step and the kernel re-derives it by unfolding. On big terms prove simp step lemmas with
  `(rfl)`, `by rfl` or `rw` (ssz-fv: 38 → 964 s, one `(kernel) deep recursion`).
- **Frame lemmas once, by `cases` + induction**, then apply them, letting unification fill big
  arguments (`foo _ s`, `rw [foo]`): ten call sites 2.6 s by `simp` vs 0.3 s; restating a 60-op
  program in `exact` hit the heartbeat limit after 10 s. Relevant to the SSA semantics proofs (G5/G6).
- **Facts about literal data** (`prog[k]? = some i`, exported rule tables) by `decide`/`rfl`,
  not `simp [prog]`: 60 lemmas 0.6 s / 1.6 s vs 4.6 s.
- **`decide +kernel` by default** for closed computations: `decide` hit max recursion at
  n = 150 where `decide +kernel` handled n = 3000; `native_decide` adds an axiom.
- **Measure with `theorem`, not `example`:** constants realized inside an `example` are
  discarded, hiding a 39.4 MB `.olean` (2.8 kB shown). On this loaded machine compare
  heartbeats (`examples/lib/HB.lean`, `count_hb in`) or CPU, not wall time.
- **`lake build --no-build <targets>`** names every out-of-date module in one call (exit 3 with
  Lake 4.34): clifv's fully cached 3,138-module check 27.5 min → 1.9 s.
- **Hard-linked cache outputs are read-only:** rebuilding over them fails with
  `permission denied`; unlink a module's outputs first. Don't build the same module in two
  worktrees at once (clifv serialises with a per-module `flock`).
- **Opaque contracts for long blocks** (ssz-fv): a monolithic proof failing with kernel deep
  recursion after ~112 s checked in ~4.5 s split into result/frame/control contracts.
- **Kernel evaluation of `check` on small functions is cheap** (`decide +kernel` on
  `(check ce clamp).toBool = true`, Lengauer–Tarjan and the dominator certificate included:
  1.6 s CPU, 0.69 GB), so witnesses can discharge `check` hypotheses directly.
- **`nomatch h, …` inside `⟨…⟩` parses as one `nomatch` with several discriminants**; write
  `(nomatch h)` in anonymous-constructor lists.
- **`variable (S : Setup …)` in a namespace needs `include S`** for theorems that use `S` only
  in their proofs (Lean 4 includes section variables by the statement).
- **Whole-pipeline witnesses need `native_decide`** (#189): `decide +kernel` on
  `verifiedPipeline` gets stuck already at pass 2, on `decide (out.func.cache = st.func.cache)`
  after `copyelimPass` (the same comparison on one literal `Func` reduces). Single passes,
  `check` and `run` on the same function reduce fine; the pipeline fact is one
  `native_decide`, listed in `scripts/axioms-allowlist.txt`, built in seconds.
- **`split at h` on a deeply nested `do` blows up; `rw [if_pos c]`/`rw [if_neg c]` does not**
  (#385, regalloc checker specs): a `do` block with several `if … then throw …` checks elaborates
  to nested `have __do_jp := …` join points, each used in both branches. `dsimp only at h` (zeta)
  copies each join point into both branches, and the following `split at h` hit simp's
  `maxSteps` on `stepValue` (six levels). Case on each condition with `by_cases hc : c = true`
  and rewrite with `if_pos hc`/`if_neg hc` (no simp), `cases h` on the `throw` branch; the
  bind after a check is `exc_bind_ok` (`(x >>= k) = .ok y → ∃ a, x = .ok a ∧ k a = .ok y`). The
  five spec lemmas of `GoFV/Proof/Regalloc` elaborate in about a second.
- **`Std.HashMap` with `String` (or any `Prod`) keys does not reduce in the kernel**:
  `String.hash` and `mixHash` are opaque, so `decide +kernel` on a checker that inserts into or
  looks up such a map gets stuck. `checkRA`'s witness (`Witness/RandnRA.lean`) is a function
  without frame constants, whose `constReps`/`rematHints` maps are never touched; the whole
  check then reduces in about 2 s.
- **memcombine witnesses with stores** (#35): `memcombineChecked` now runs the store half and
  `tabsAgree`, so the kernel-evaluated witnesses got slower: `GoFV.Proof.Witness.MemCombine`
  (Uint16, loads) builds in 32 s wall (was ~19 s CPU), the new `Witness.MemCombineStore`
  (PutUint16) in 31 s. `ChgRefP` passes `Ctx.make tabs g` explicitly to
  `memRoot_of_memDef_store`: leaving the context a metavariable made unification unfold
  `Ctx.make` (whnf heartbeat timeout).
- **Whole-tree build after a semantics change** (#385, `Sem/Arm64/Reg.lean` `ptrReg` plus a
  `Pat.argsOKLs` clause change): `lake build GoFV GoFVTest` at 16G was killed (exit 143, the
  scope's 16G memory peak) about 15 s in, every retry, because ~500 dependents of the changed
  modules start at once. Building all modules in batches of 15 targets (`find GoFV GoFVTest
  -name '*.lean'`, 16G under the heavy lock, a failed batch retried module by module) took
  5 min; the whole-tree build is then a no-op (1,089 jobs).
  **Fix:** `FV_LEAN_SLOTS=N scripts/memcap.sh lake build …` caps concurrent `lean` processes at N
  (a sysroot of symlinks whose `bin/lean` waits for one of N flock slots; Lake 4.34.1 has no job
  limit of its own). It causes no rebuilds (traces use the githash). Measured: 6 × 3 s `lean` runs
  at 2 slots took 11 s.
