# Design review: the top-level run with a closure context (#705)

Status: design review only; nothing is implemented. Issue #705. Background: #553 (comment
6790897411, the integrator's ruling on the 148), #189. The doc names main a6c37a47 (#706, the
driver's `entryVacuous`). Semantics: `docs/plans/semantics.md` §8, `semantics2.md`; Phase 3:
`proofs3.md` §8–9; trust: `docs/proofs/STATUS.md` Assumptions.

**Decision: pending (integrator).** §9 lists the questions.

## 0. Summary

- **Problem.** No top-level run has a closure context, so `GetClosurePtr` and
  `LoweredGetClosurePtr` evaluate to `poison`. As a result 547 of quick-v10's 7,221 functions
  whose premises hold satisfy every `verified_mach` variant only vacuously: 539 under
  `verified_mach`, 8 under `verified_mach_S`. On full-v11 the figure is about 7,315.
- **Recommended change (design E).** The top-level closure context becomes an input carried by
  `Env`, the way `Env.globals` already is: a field `Env.closure : Option Val := none`, read by
  `entryFrame` alone.
  - Every run entry gets it through `entryFrame`: `run`, `runL`, `runSched`, `runLF`, `runLoc`,
    `runFrame`, `locInit`.
  - No theorem statement changes its text.
  - Two input predicates (`InitAvoids`, `ArgPtrsOK`) gain a conjunct about the closure. Both
    conjuncts are trivial when `closure = none`.
  - The machine side needs no new contract. `EntryMatch.regs` already carries the `R26`
    obligation once `entryLen` counts `LoweredGetClosurePtr`. `MorestackOK` already keeps `R26`.
    `CloOK` becomes dischargeable at the top-level activation, so the trusted base shrinks.
- **Alternative (design A, §2.4).** Thread an explicit `clo` argument through every run and the
  17 refinement relations, the signature `semantics.md` §8 planned. It costs about twice as much
  (8–10 agent-days against 4–5). It also hits a type problem: the pass preconditions
  `P : Env → List Val → Mem → Prop` cannot mention `clo`.
- **Gain.** quick-v10 goes from 6,674 to 7,221 end to end (+547, exact). full-v11 goes up by
  about 7,315, from about 67,914 to about 75,229 at G61.
- **Finding on the way (§3.3).** The trusted model of `runtime.morestack_noctxt` keeps `R26`, but
  the runtime zeroes it (`asm_arm64.s:501`). `MorestackOK` at `morestack_noctxt` is therefore
  false of the real runtime whenever `R26 ≠ 0` at entry, and every non-closure function with a
  stack check calls that symbol. It is independent of this design: one small separate fix.

## 1. The problem

| where | what |
| --- | --- |
| `GoFV/SSA/Sem/Run.lean:521` | `Frame.closure : Option Val := none` |
| `Run.lean:1026`, `RunL.lean:373` | `GetClosurePtr` / `LoweredGetClosurePtr` evaluate to `fr.closure.getD .poison` |
| `Run.lean:1228` | `entryFrame` sets no closure, so every top-level run (`runCtx`, `runCtxL`, `runCtxLoc`, `runCtxFrame`, `locInit`) has `none` |
| `Run.lean:1360` | only `runActivation env ctx clo …`, the activation of a called program function, gets one |

So for a closure, `RunPre`/`RunPreS`/`RunPreM` (`Obj/Whole.lean:188`) cannot hold, for one of two
reasons. The driver's `entryVacuous` (`GoFVTest/Driver/E2E.lean:122`, #706) detects both:

- **399, context load.** `MOVDload off(R26)` or `LDP` has a `poison` base, but `G3Pre`/`G4Pre`
  (inside `G54Pre`) require `symAddr … = some p ∧ mm.read p n = some bs`.
- **148, entry value after the start.**
  - The entry block is `LoweredGetClosurePtr, ArgIntReg…, InitMem`.
  - `entryLen` (`Gen/Entry49.lean:82`) counts only `entryOp ∨ Arg`, so k = 0.
  - RunPre's clause `entryOp24 v.op = false ∨ (InitMem ∧ lowered)` then fails at position 1,
    which is always reached.

**`entryLen` alone recovers almost nothing.**
- The test (throwaway script on the stock `trim` sections of the 547, `tmp/cloclass.py`):
  count `LoweredGetClosurePtr` in `entryLen` and keep `poison`.
- Result: **544 of the 547 remain vacuous**, because a context load lies in the entry block's
  straight-line prefix.
- The other 3: 1 never loads its context, and 2 load it only past the prefix. Those 2 become
  non-vacuous only for inputs that do not reach the load.
- So the semantic change carries the whole gain. The approved `entryLen` fix (#553) is necessary
  but not sufficient.

## 2. The semantic change

### 2.1 Which value

The context is `Option Val`, the type `Frame.closure`, `runActivation` and `Contract`
(`List Val → Option Val → Mem → COutcome`) already use.
- A `Ptr` type would need a conversion at each of those three, and gains nothing.
- The input condition (§2.2) excludes nil.
- It does not require `.ptr`: a `.int .w64` encoding of an address stays allowed, as
  `ValRel` allows it.

### 2.2 Design E (recommended): `Env.closure`

Definitions that change (exact sites):

| file:line | change |
| --- | --- |
| `GoFV/SSA/Sem/Env.lean:27` `structure Env` | new field `closure : Option Val := none`: "the closure context of the top-level activation (`R26` at entry, the funcval the caller called through); `none` outside a closure. `runActivation` ignores it." |
| `GoFV/SSA/Sem/Run.lean:1228` `entryFrame` | `closure := env.closure` |
| `Run.lean:521` `Frame.closure` | doc only |
| `GoFV/SSA/Sem/FrameSafe.lean:98` `InitAvoids` | add `∧ ∀ c, env.closure = some c → c.Avoids (· = .temp a n)` (an input, like the arguments, points into no frame temporary) |
| `GoFV/Proof/Pass/SchedLEval.lean:1176` `ArgPtrsOK` | add `∧ ∀ c, env.closure = some c → ¬ NilBase c` (and `PtrOK c` if the proof needs it; `isNN`, `Opt/ScheduleCheck.lean:160-168`, uses only "no nil base") |

Unchanged in text: `run`, `runCtx`, `runCtxL`, `runL`, `runSched`, `runLF`, `runCtxLoc`,
`runLoc`, `runCtxFrame`, `runFrame`, `locInit`, `runLoc_eq`, `runActivation`, `Env.withFuncs`,
`VPre`, all 17 `Refines*` relations, every pass theorem, `verifiedPipeline_refines`,
`verifiedPipelineFull_refines` (`Pass/PipelineFull.lean:506`), `_fixed`, `verified_mach`,
`_S`, `_M`, `_fixed`, `_S_fixed`, `_atSP`, `_S_atSP`, `obj_whole_ret`, `obj_whole_panic`,
`EntryMatch`, `MoreEntry`, `RunPre*`.
- They all quantify over `e : Env`, so they now cover every closure context.
- Every run entry builds its frame with `entryFrame`, so the change reaches all of them.

Why the conditions sit in `InitAvoids` and `ArgPtrsOK`:
- These are the preconditions the three affected pass families already take:
  - DAE and UnreadL take `FrameSafe ∧ InitAvoids` (`RefinesFrom.frameSafe_toV`).
  - `schedule` takes `ArgPtrsOK ∧ NilPtrsOK` (`Pass/SchedLPass.lean:27`), which reaches
    `verified_mach` as `ha`.
- So no pass statement and no pipeline statement changes its text.
- The alternative, a new `VPre` conjunct, would change `schedule_refinesSchedLF`'s `P` (§9 Q2).

Justification of the conditions (STATUS rows `InitAvoids`, `ArgPtrsOK`; facts about the
inputs, not trusted contracts):
- **Not nil.** A closure is entered through its funcval. The caller loads the code word from it
  before the call (`ssagen/ssa.go:5141-5149`, `rawLoad` of the closure), and that load faults
  on nil.
- **Points into no frame temporary of the callee.** The funcval exists before the callee's
  activation does.

### 2.3 Is it a pure generalisation?

Yes. For an `Env` with `closure = none`:
- `entryFrame` is today's frame: field for field, `closure := none` as before.
- Both new conjuncts are `True`.

So every existing statement is the `e.closure = none` instance of the new one: it is neither a
default argument nor a separate theorem. Acceptance artefacts in the semantics PR:
- `entryFrame_closure : (entryFrame env ctx args mem).closure = env.closure`;
- `initAvoids_iff_of_none`, `argPtrsOK_iff_of_none`: under `env.closure = none` each predicate
  is equivalent to its present body (the old definition restated in the lemma).

The hard criteria, as in `blob-regs.md` §10:

1. **No weakened statement.**
   - No theorem statement text changes.
   - The only definitions that change are `Env`, `entryFrame`, `InitAvoids` and `ArgPtrsOK`,
     each by the conjunct or field above.
   - Their `none` instances are today's (the lemmas above).
   - `verified_mach_fixed` still restates `verified_mach` verbatim. Both are untouched.
2. **sem-difftest identical** (native and the quick corpus, L0/L1/L2).
   - Every concrete environment (`Env.p1`, `Env.runtime`, the drivers', `plRunEnv`) is built
     with the default `closure := none`, so outcomes are identical by construction.
   - The PR records the run.
3. **full-v11 counts do not drop.**
   - No validator changes.
   - `entryLen` changes only for functions with `LoweredGetClosurePtr`, where it grows. There:
     - `entryStoresOK` can only improve: `storesFrom` at k = 0 starts at
       `LoweredGetClosurePtr` and is empty, so 3 of quick-v10's 35 rejections are closures at
       k = 0.
     - `argsOK` can only improve: more `Arg`s are before k.
   - Recorded: Phase 1, through `trim`, and end-to-end per mode, 0 lost per function
     (`comm` of the lists).
4. **A dedicated PR**, separate from the composition (§8).
5. **No time or memory regression.** One `Option` field and the same compiled facts. Whole-tree
   `lake build` wall time and peak RSS are recorded before and after; a LEARNINGS entry if the
   difference is measurable.

### 2.4 Design A: an explicit `clo` argument

This is the signature `semantics.md` §8 planned (`run env f args closure mem fuel`).

What changes:
- `entryFrame`, `runCtx`, `run`, `runCtxL`, `runL`, `runSched`, `runLF`, `runCtxLoc`,
  `runLoc`, `runCtxFrame`, `runFrame`, `locInit` and `runLoc_eq` take `clo`.
- The 17 refinement relations (`Refines`, `RefinesUnder`, `RefinesFrom`, `RefinesL(From)`,
  `RefinesLoc(From)`, `RefinesLS(From)`, `RefinesSched(From)`, `RefinesSchedL(F)(From)` …)
  quantify over it.
- So does their algebra (`refl`/`trans`/`mono`/`from`/`backward`).

Its costs:

- **Mechanical churn.**
  - 626 `intro`/`fun env args mem …` sites in 53 proof files gain a binder.
  - 319 `entryFrame` lines in 60 files gain an argument.
  - So do the lemmas about `run`/`runL`/`runLoc` the passes use: 229/719/553 lines.
- **The precondition type.**
  - `P : Env → List Val → Mem → Prop` cannot state the closure conditions (§2.2).
  - Either every `P` (`VPre`, `RwPre`, `ArgPtrsOK`, `NoNilFault`, `NilPtrsOK`, …) gains a
    `clo` parameter, or the relations hard-wire one fixed `CloIn clo` premise.
  - The second is less churn, but it couples every relation to two passes' needs.
- **Statements.**
  - `verifiedPipelineFull_refines` and the 8 `verified_mach*`/`obj_whole_*` statements change
    their text: a `clo` binder, and `clo` passed to `run`/`runLoc`/`locInit`.
  - They would be strictly stronger, with the old statement a one-line `clo := none`
    corollary.
- **Default argument or separate theorem?**
  - With a default `(clo : Option Val := none)`, every existing statement keeps compiling. It
    also silently stays at `none`, so a theorem meant to be general can quietly cover only
    non-closures. That is how #705 arose.
  - So under A: no default. Name `clo` explicitly everywhere, and add the `none` corollaries as
    separate theorems.

A buys nothing E does not prove: the theorems quantify over the same inputs. Its advantage is
presentational. The context sits next to `args`, and `Env` stays the world (contracts, globals)
plus one top-level input.

## 3. What the end-to-end theorems quantify over

### 3.1 Phase 1/2 side

`e` now includes `e.closure`, an input like `args`. Conditions:
- `VPre`'s `InitAvoids` gains the closure avoidance.
- The `ha` premise (`ArgPtrsOK`) gains closure ≠ nil.

**No layout condition** (the funcval `{fn, captured…}` readable) is needed in the theorem:
- `RunPre` is a fact of the run. Its `G3Pre`/`G4Pre` already require every context load
  `off(R26)` to read valid bytes of `runLoc`'s memory.
- It is satisfiable exactly when `mem` holds the closure object at the loaded offsets, so the
  premise is the layout condition, per input and per load.
- The non-vacuity witness exhibits such a memory (§6).

### 3.2 Machine side: `EntryMatch.regs` carries `R26`

Once `entryLen` counts `LoweredGetClosurePtr` (§5):
1. `hpre : enterListLoc e lc (locInit e lc args mem) (take k) = .ok sI` steps it.
2. `stepLoc_clo` (`Gen/G11.lean`) writes `(e.closure.getD .poison).retypeL (lc.ty v)` to its
   home `R26` (`cloKind`: homed in `ctxReg`, no code).
3. `EntryMatch.regs` (`Obj/Whole.lean:1037`, definition unchanged) then demands
   `ValRel E0.ι c (s0.x 26)`. That is: at the function's entry, `R26` holds the closure
   object's address under `ι` (`PtrRel`).

This is the caller's ABIInternal obligation, of the same kind as the argument registers'
relation in the same clause. Sources:
- `cmd/compile/internal/ssa/_gen/ARM64Ops.go:546`: `CALLclosure` takes the closure in `R26`.
- `ARM64Ops.go:650-653`: `LoweredGetClosurePtr` outputs `R26`, `zeroWidth`; the scheduler keeps
  it first in the entry block.
- `cmd/internal/obj/arm64/a.out.go:283`: `REGCTXT = REG_R26`.
- `cmd/compile/abi-internal.md:354-365`: "calls to closures store the address of the closure
  object in the closure context pointer register".
- `abi-internal.md:551`: the `R26` row.
- `ssagen/ssa.go:518-519`: `GetClosurePtr` exists iff `fn.Needctxt()`.

Per the integrator's ruling on #553, this needs a STATUS line on the `EntryMatch` row with these
citations, and no new contract.

`EntryMatch.regs`' exclusion `q ∈ {16, 17, 20, 29} → poison` does not touch `X26`. Nothing on
the machine side assumes `R26` is `poison` at `sI`:
- `MoreEntry` (`Whole.lean:1085`) already exempts `q = 26` from the reload requirement.
- `MorestackOK` (`Obj/Morestack.lean:73`) already keeps `R26`.
- `MoreStep.x26` (`:96`) carries that through the morestack loop.
- `EntryMatch.more` uses it (`Whole.lean:1132`).

### 3.3 morestack, and a finding about `morestack_noctxt`

A closure's prologue calls `runtime.morestack`. Only a function without `NEEDCTXT` calls
`morestack_noctxt` (`cmd/internal/obj/arm64/obj7.go:283-289`, ported at
`GoFV/Asm/Obj7.lean:448`).
- `runtime.morestack` saves `R26` in `g.sched.ctxt` (`runtime/asm_arm64.s:449`).
- `newstack` resumes through `gogo`, which restores it (`asm_arm64.s:261-269`,
  `MOVD gobuf_ctxt(R5), R26`).
- So `MorestackOK`'s `s'.x 26 = s.x 26` holds of the runtime at `morestack`, and
  `morestackHook_ok` discharges it for the model. **No new contract.**

**Finding.** `runtime.morestack_noctxt` is `MOVW $0, R26; B runtime·morestack`
(`asm_arm64.s:493-502`), so after it `R26 = 0`. Yet:
- The trusted hook `morestackHook` runs at both symbols and keeps `R26`
  (`GoFV/SSA/Sem/Hooks.lean:18`, `:199`, `:270`).
- `morestackHook_ok` proves the hook meets `MorestackOK` at both
  (`Obj/MorestackHook.lean`, `hname`).
- STATUS's hook row says "`R26` … kept" for both.

`MorestackOK` quantifies over every state at the tail call, including those with `x 26 ≠ 0`. So
at `morestack_noctxt` it is false of the real runtime. That is the tail target of every
non-closure function with a stack check.

The proofs never need it there: in a non-closure function, `R26` is `poison` at `sI`, and
`ValRel .poison _ = True`. So the fix is small, and it makes the statement stronger (the
contract demands less):
1. The hook zeroes `R26` at `morestack_noctxt`.
2. `MorestackOK` and `MoreStep` keep `R26` only when the tail calls `runtime.morestack` (a
   `ctxt` flag of the tail call).
3. `EntryMatch.more` takes `R26` from it only when `sI`'s `R26` is not `poison`.
4. A checked fact (`checkObj` or the driver) that a function with `LoweredGetClosurePtr` has
   `NEEDCTXT`, so its tail calls `runtime.morestack`.

The fix is independent of this design, and it should land whichever design is chosen: §8 PR0.

### 3.4 `CloOK` is discharged at the top-level activation

`cloFirst` (`Gen/Check11.lean:37`, required by `checkG11` and every later slice) puts every
`LoweredGetClosurePtr` in the entry block after register arguments only. Once k counts it:
- No value at a position ≥ k is a `LoweredGetClosurePtr`.
- No edge enters the entry block (Go's `check.go:421-422`, ported in `GoFV/SSA/Check.lean:415`;
  the pattern of `argsBefore`, `Gen/Entry62.lean:30`).
- Hence `LReach` from `(entry, k)` never steps a `LoweredGetClosurePtr`, and `RunPre`'s `CloOK`
  conjunct holds vacuously.

A lemma (`runPre_cloOK_of_cloBefore`, with a decidable `cloBefore lc k`) marks the trusted
`CloOK` row "discharged at the top-level activation", as `ArgOK` was for G62. `RunPre`'s text
stays the same, so no pin moves.

## 4. Refinement through the passes

Both sides of every refinement run in the same `Env`, so they get the same closure value. This
is literally equality: no `Refines` on `Val` is needed. The frame relations already require
`a.closure = b.closure`:
- `fok`: `ShortCircKBlock.lean:307`, `ZCSEBlock.lean:23`, `ECOk.lean:69`,
  `AtomSimNoPanic.lean:18-22`, `TabsAgreeModSim.lean:95,263`, `TabsAgreeModL.lean:196,598`,
  `DAESim`, `DAEBlock`, `UnreadLSim`, `UnreadLBlock`.
- `RunMono.lean:579,1022`: `fr'.closure = fr.closure`.

`lower` maps `GetClosurePtr` to `LoweredGetClosurePtr`, and both read the frame's closure
(`Low/SimAtom.lean:17`).

Uses in `GoFV/Proof` on main a6c37a47 (`grep -E`, lines / files):

| pattern | lines | files | where |
| --- | ---: | ---: | --- |
| `\.closure\b` | 32 | 19 | 6 in `Gen/G11.lean`; the rest frame equalities and the three families below |
| `LoweredGetClosurePtr` | 100 | 12 | 76 in the witnesses `GenG11`/`GenG19`/`GenG57b`; `Gen/G11`, `Spec11`, `Low/SimAtom`, `RuleL`, `Rename`, `MoveLCheck`, `SchedLEval`, `SchedLBlock`, `Obj/Whole` |
| `GetClosurePtr` (generic) | 123 | 11 | 99 in the same witnesses; `NilBlock` 8 and `CSEOp` 7 (op-class side conditions, value-independent) |
| `CloOK` | 152 | 59 | the slices' premise chains; unchanged |
| `entryFrame` | 319 | 60 | unchanged under E; each gains `clo` under A |
| `intro`/`fun env args mem …` | 626 | 53 | unchanged under E; each gains a binder under A |

Proofs that depend on `closure = none`. This is the whole non-mechanical work of design E:

| family | sites | why | new argument |
| --- | --- | --- | --- |
| `schedule` (SchedL) | `SchedLEval.lean:897-913` `evalValueL_clo`; `SchedLBlock.lean:388`; `SchedLSim.lean:117,413,461,583-586`; `SchedLWalk.lean:237` | the closure pointer has no nil base, so a load off it cannot fault (`isNN`) | invariant `clo : ∀ c, fr.closure = some c → ¬ NilBase c`, from `ArgPtrsOK` at the entry |
| dead autos (DAE) | `DAESrc.lean:39-43` `FrameOK.closure`, `:225`; `DAESim.lean:83,111`; `DAEBlock.lean:46` | `GetClosurePtr`'s value avoids the frame's temporaries | `FrameOK.closure : ∀ c, fr.closure = some c → c.Avoids U`, from `InitAvoids` |
| unread autos (UnreadL) | `UnreadLSrc.lean:83`; `UnreadLSim.lean:332,361`; `UnreadLBlock.lean:351` | as DAE (it uses DAE's `FrameOK`) | as DAE |

Any other fallout shows up as a build error. Expect a handful of `rfl`/`simp [entryFrame]` sites
that built an entry invariant with `closure = none`.

Phase 2 (regalloc, `loop rotate`, `trim`, the L-passes) is frame-generic. [INFERENCE: its
`entryFrame` uses, e.g. the 5 in `Regalloc/Sound.lean`, relate frames built by the same
`entryFrame`, so no change is expected; the build is the check.]

The Phase 3 genssa slices are per-step from any `LocState`. `g11_value` already handles any
`fr.closure`, so they need no change.

## 5. The 148: entry ordering

- **Change.** `entryLen` (`Gen/Entry49.lean:82`) also counts `ARM64LoweredGetClosurePtr`.
  - `cloFirst` places it among the entry values, and it emits no code (`cloKind = .none`).
  - k then covers `LoweredGetClosurePtr, ArgIntReg…, InitMem…`.
  - `hpre` runs it (§3.2), and RunPre's clause `entryOp24 … ∨ InitMem` holds at every position
    ≥ k.
- **No theorem change.** The theorems are stated for any k. `entryLen` is the driver's choice of
  k (`E2E.lean:260`) and the witnesses'.
- **Composition PR obligations.** At the new k, it must show (lemma or driver check) the k-side
  premises, as for today's entry values:
  - `hpc`: no Prog before k;
  - `huE`: `uL35 … k = []` (`uStepL`, `Gen/Check29.lean:36`, returns `[]` for an op without a
    `uEntry`; to be confirmed for `LoweredGetClosurePtr`);
  - `hinv`: `kSteps` gives `R26` class 64, a pointer fits.
- **Without the semantic change** this fixes only 3 of the 547 (§1).
- **Driver.** `entryVacuous`'s "closure context load" branch becomes dead (`clos` is empty past
  k), and the composition PR removes it. The "entry value after the start" check stays, as the
  integrator required on #553.

## 6. Inventory and cost (design E; agent-days)

| family | work | estimate |
| --- | --- | ---: |
| semantics and input predicates | `Env.closure`, `entryFrame`, `InitAvoids`, `ArgPtrsOK`; `entryFrame_closure`, `*_iff_of_none`; `semantics.md` §8 (the context is `env.closure`), `semantics2.md` §1 | 0.25 |
| Phase 1 pipeline | SchedL, DAE, UnreadL (§4), build fallout; `verifiedPipeline(Full)_refines` text unchanged | 1–1.5 |
| Phase 2 through `trim` | fallout only (expected none) | 0.25 |
| Phase 3 genssa slices | none (`g11_value` is closure-generic) | 0 |
| Obj composition | `entryLen`; `cloBefore` + `runPre_cloOK_of_cloBefore`; STATUS rows (`EntryMatch` R26 with §3.2's citations, `CloOK` discharged, `InitAvoids`, `ArgPtrsOK`); `verified_mach_clo_witness` | 1.5–2 |
| evidence | sem-difftest; whole-tree build, `axioms-audit.sh --replay-changed`, `check-reverts.sh`; pins re-taken (every fact whose definition closure reaches `Env`/`entryFrame`; statements unchanged); quick-v10 e2e; full-v11 e2e (about 11 h wall under the heavy lock) | 0.5–1 |
| **design E total** | | **4–5** |
| PR0: `morestack_noctxt` (§3.3) | hook, `MorestackOK`/`MoreStep` `ctxt` flag, `EntryMatch.more`, NEEDCTXT check, STATUS hook and contract rows; pins of facts that reach `morestackHook` re-taken | 1–1.5 |
| design A instead | E's work, plus §2.4's churn and the `P` type change | 8–10 |

The witness is `examples/closures/main/adder.func1`. Its entry block at `trim` is
`v7 LoweredGetClosurePtr; v6 ArgIntReg; v1 InitMem; v9 MOVDload [8] v7 v1; v11 ADD v6 v9`.
- The memory holds a closure object `{code word, captured int}`, and `e.closure` points to it.
- `R26` in `s0` holds its address.
- `RunPre` is discharged with the real context load (`G3Pre` at `v9`): non-vacuous by
  construction.
- It reuses `GenG11`'s closure setup (`Witness/GenG11.lean:1767`).

## 7. Expected gain

- **quick-v10** (G64, main a6c37a47, `entryVacuous` column): **+547 exactly**, from 6,674 to
  **7,221** end to end.
  - Per mode: `verified_mach` 6,471 → 7,010 (+539); `verified_mach_S` 203 → 211 (+8).
  - The stock column: 600.
  - This assumes no other premise changes, which the composition PR measures with 0 lost.
- **full-v11** (G61, #703): about **+7,315**, from about 67,914 to about 75,229.
  - Method: a mirror of `entryVacuous` on the stock `trim` functions of the accepted lists. The
    mirror gives 548 on quick against the driver's 547.
  - The G64 run started for #702 gives the exact base. The PR's full-v11 run gives the exact
    gain.
- **Not counted:** closures whose context loads lie past the entry prefix. They are counted
  today, but their theorem is non-vacuous only on inputs that never reach the load. With the
  context they hold on all inputs.

## 8. PR plan

0. **PR0 (independent, recommended first).** The `morestack_noctxt` fix (§3.3), on its own issue.
1. **PR1, semantics (dedicated).** §2.2 and §4.
   - Evidence: the hard criteria in §2.3, statement diff empty, sem-difftest identical, build
     time and memory.
   - No count changes: `entryLen` is untouched, so the 547 stay vacuous until PR2.
2. **PR2, composition.** §3.2, §3.4, §5 and the witness.
   - The driver vacuity branch is removed.
   - The STATUS headline: quick-v10 and full-v11 per mode, 0 lost.

## 9. Questions for the integrator

1. **Design E (`Env.closure`) or design A (explicit `clo`)?** Recommended: E. Same theorems,
   half the cost, no `P` type change.
2. **Where do the closure input conditions live?** In `InitAvoids` and `ArgPtrsOK`
   (recommended; no statement text changes), or in a new `VPre` conjunct (it would change
   `schedule`'s `P`)?
3. **PR0 (`morestack_noctxt`) first, as a separate issue?**
4. **Discharge `CloOK` at the top-level activation in PR2** (a lemma, `RunPre`'s text kept), or
   remove it from `RunPre`/`RunPreS`/`RunPreM` (a definition change, so every proof that
   destructures the per-step conjunction changes)?
