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
  `.olean`s (`SSA.Op`, `Proof.Frame`, `Rules.Neq`). It is not adopted yet: it trades wall time
  for less CPU on the shared machine, which is a policy choice (#1). The clifv entry "Threads
  per Lean process don't help us" below was probably measured with the same no-op variable.

#### Generate `match` congruence equations upstream, or sibling modules cannot be imported together
- **Problem:** `simp` in a rule-lemma module generated `binDV.match_4.congr_eq_*`,
  `fieldDV.match_1.congr_eq_*` and `Option.getD.match_1.congr_eq_*` (plus `_sparseCasesOn_*`)
  as *public* constants of that module. `Eq.lean` and `Eq2.lean` both did, and a file importing
  both failed: `environment already contains 'GoFV.Proof.Rules.fieldDV.match_1.congr_eq_1…'`.
  Each module builds fine alone, so only an importer of both notices.
- **Trick:** generate them once in the shared upstream module (`Tactic.lean`):
  `run_meta for n in [``binDV.match_4, …] do discard <| Lean.Meta.Match.genMatchCongrEqns n`.
  Check: read every `.olean`'s `constNames` and report public names defined twice
  (`scripts/rule-proofs.py axioms` imports all rule modules, which fails on such a clash).
- **Effect:** 35 rule modules import together; no rebuild cost.

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
