# Design review: the Phase 1 rule classes false under the semantics (#69)

Status: design review, nothing implemented. Issue #69 (ranking: comment 6865422368). The
recorded findings are in `docs/proofs/rules.md` ("Findings"); the hard criteria for a semantics
change are those of `docs/plans/blob-regs.md` §10. **Every recommendation below waits for the
integrator's decision (§9).**

## 1. Scope and method

The re-ranking on #69 (Phase1Tail11) puts the classes recorded as *false under the semantics* at the
top of the 2,388 functions that fail Phase 1 on full-v11. This review takes each class and decides
which of three kinds it is:

- **(G)**: a real Go miscompile.
- **(M)**: a model limit, where our semantics is stricter than Go.
- **(U)**: false only on inputs Go never produces, so the validator can check a side-condition on the
  input.

For each class it gives the fix, how often the fix applies on the corpus, the gain and the cost.

**Data.**
- **Base:** main cad4a601, full-v11, 96,674 functions. Files: `phase1tail10/tmp/v11-main-cad4.vstats`
  (Phase 1 94,286) and `rule-fire-probe` `fire-cad4.out`.
- **Sole-blocker functions of a class:** the Phase-1-unverified functions whose set of unproven rules
  (the `OFF` line of the fire probe) is a non-empty subset of the class's rules. These are the
  functions the class alone keeps off stock under the proven-only passes. The gain is an upper bound:
  a function can still stop at a validator check afterwards.
- **Stock e2e:** `gofv-ssa-opt --check --verified --e2e` on each class's file list, at 8G, `--jobs 2`,
  lock-free. The binary is main 949dc282 (`agent/phase1tail11-vac`, #730), which differs from
  0a04f238 only in the pipeline-side zero guard of #731. The number used is the stock column of
  "premises hold, not vacuous (end to end)": how many of the functions would be end to end if the
  pipeline reached stock on them.
- **Probes:** throwaway Python scanners over the `.ssa` sections, in the `agent/false-classes`
  worktree's `tmp/`:
  - `Convert_probe.py`
  - `MemEq-probe.py`, `MemEq-ptrful.py`
  - `CondSelect_probe.py`
  - `Zero2159-probe.py`
  - `ArithSideCond_probe.py`

| Class | Rules | Sole-blocker functions | Of them e2e at stock |
| --- | --- | ---: | ---: |
| `convert` | `generic.rules:1071`, `:1075` | 281 | 212 |
| `memeq` | `:1560`–`:1628` (`MemEq` splits, read-only `Load`s) | 989 | 607 |
| `condselect` | `:2322`–`:2386` (`CondSelect` into arithmetic) | 363 | 221 |
| `zero2159` | `:2159` (`Zero` over `VarDef (Zero …)`) | 55 | 43 |
| `divmod` | `divmod.rules:140`, `:148` (signed-typed `Div<N>u` by `smagic`) | 45 | 22 |
| `rotate` | `:2166`–`:2169` (constant rotate) | 34 | 3 |

**No class is a new Go bug.** `rotate` is the latent #90, already `upstream-candidate`; the other
five are (M) or (U). So no new upstream-candidate issue is opened.

## 2. `convert`: `generic.rules:1071`, `:1075` (281 functions): (M), never

**Rules.**
- `:1071`: `(Convert (Add(64|32) (Convert ptr mem) off) mem) => (AddPtr ptr off)`.
- `:1075`: the same with `off1 + off2`, built as `ptr+(off1+off2)` so that no intermediate pointer is
  invalid.

**Counterexample** (rules.md "Findings", semantics.md §3): every convertible pointer is held as its
word `.int a` (#290).
- **Source:** the integer `a + off`, read back by `Ptr.ofAddr`.
- **Target:** `AddPtr` is `wordRes a off`, which is `poison` once `p.off + off` leaves the block's
  window (`Sem/Ptr.lean:31-46`; 2^40 for the heap and nil, 2^24 for the frame).
- **Where they differ:** exactly when the result leaves the window, for example a negative offset
  from a block start (`runtime.subtract1`). There the source has landed in a neighbouring tile (another
  heap block, the nil page, another frame variable).
- **Where they agree:** in-bounds and one-past-the-end results.
- **Held pointers are not a problem:** for a global or a frame temporary the inner `Convert` is already
  `poison`.

**Classification: (M).** Unsafe rule (3) (`src/unsafe/unsafe.go:68-100`) makes a result outside the
original allocation, even one past its end, invalid. So every input on which the model differs is an
invalid Go program, and both sides lower to the same `ADD`. It is not (U): nothing on the SSA bounds
`p.off`.

**Instances** (558, all in `opt`):
- Kinds: 534 `:1071`, 10 `:1075`, 14 formed during the pass.
- The offset is a variable in 492 and a constant in 66.
- The base is a `Load`, `Phi`, `NilCheck` or `Arg` in 443.
- Where they come from in the Go source:
  - `internal/runtime/maps` `g.data + offset`: 135;
  - `runtime/mbitmap.go` `addb`/`subtract1`: 107;
  - `runtime.add`: 85;
  - `internal/abi`: 74;
  - `reflect`: 38.
- `unsafe.Add` emits `AddPtr` directly and is not a source (`ssagen/ssa.go:3737`).

**Options.**

| Option | Change | Verdict |
| --- | --- | --- |
| M1 | Provenance-tagged integers: `Convert` ptr→int keeps the block, `Add`/`Sub` keep the tag, int→ptr is `ptrRes` in the tagged block | Source **less defined** (fails criterion 2), although only on unsafe-rule-3 violations. `Val` changes: `.int .w64` occurs in 1,093 lines in 241 files, `Ptr.ofAddr` in 213 lines; tags would have to flow through bytes, `Phi`s and calls. 20+ agent-days |
| M2 | A window-free `wordRes` (target more defined) | Breaks `wordRes_safe` → `addPtr_safe`/`offPtr_safe`/`ptrIndex_safe` (`Proof/Pass/NilBlock.lean:733-794`), hence nilcheckelim (a proven pass lost, fails criterion 3) |
| M3 | PNVI-ae (exposure) | This is today's `Ptr.ofAddr`; the rule stays false |
| M4 | A "program obeys unsafe rule 3" premise | Not checkable; a new hypothesis on the top-level statements (fails criterion 1) |
| (U) | `off = 0`; or the base is an `Addr`, a `LocalAddr` at a constant in-window offset, or an allocation result | Holds for **1 of 558 instances, 1 of 281 functions** (a `mallocgc` result plus a constant) |

**Recommendation: never.** Record the rules as false on Go-undefined inputs. Changing this needs
either a criterion-2 exception (M1: the source is less defined only on executions that violate unsafe
rule 3) or a loss of nilcheckelim. Neither is worth it, unless the integrator wants M1 for its own
sake (decision 6).

## 3. `memeq`: `MemEq` splits and read-only loads (989 functions)

**Rules** (`generic.rules:1556-1631`):
- **Eq splits** `:1560`/`:1568`/`:1576`/`:1584`: `(MemEq p q (Const64 [n]) mem) => (EqN (Load <IntN> p
  mem) (Load <IntN> q mem))`, for n = 1, 2, 4, 8.
- **Read-only loads** `:1564`/`:1572`/`:1580`/`:1588`: `(Load <IntN> (Addr {s} SB) mem) && symIsRO(s)
  => (ConstN [readN(s, 0)])`.
- **`AndB` splits** `:1600`/`:1607`/`:1614`/`:1621`: a `MemEq` of c bytes becomes the `AndB` of a smaller
  `MemEq` and an `EqK` of two `Load`s.
- **`:1628`** (c = 25..32): two `MemEq`s, with no loads.

Of the 989 functions, 943 also need a read-only load and 594 an `AndB` split.

**Counterexample** (rules.md "Findings"):
- `memEq` (`Sem/Ptr.lean:133-146`) compares bytes, so equal pointer fragments compare equal and a
  fragment never equals a concrete byte.
- An integer `Load` of fragments is `poison`. The exception is all 8 fragments of one pointer, which
  decode to `Ptr.word`; for a global that is `.ptr`, and `Eq64` of it is `poison`.
- So at both operands holding fragment 0 of `⟨global g, 0⟩`, the source is `true` and the target is
  `poison`.

**Classification.**
- **Eq and `AndB` splits: (M).**
  - `runtime.memequal` is an intrinsic that becomes `MemEq` (`ssagen/intrinsics.go:199-203`) and
    compares raw bits, as the split does.
  - Pointers use the `AMEM` algorithm (`types/size.go:251`), so `==` on arrays and structs with
    pointers reaches `memequal`. On full-v11, 2 of 5,684 `MemEq`s are pointer-bearing:
    `(*stackAllocState).stackalloc`'s `LocalSlot ==` and `runtime.(*traceMap).put`.
  - The model gives globals and frame temporaries no address (`baseOf_global`, `Sem/Val.lean:132`),
    and narrow loads of fragments no value. Go reads their bits.
  - The `AndB` splits are false on their own (their `Load` half), not only through the Eq splits.
- **Read-only loads: not false, only unproven.**
  - `symIsRO` means `SRODATA` without relocations, so under the pipeline's `RoImage` premise the load
    reads concrete bytes.
  - `RewriteCheck.fixedOK` already validates the same fact for `:2251`/`:2255`. It lacks an arm in
    `fwdShapeOK` and `Const16` (needed for `:1572`).
- **`:1628`: true today, unproven.**

**Side-conditions probed** (1,916 instances in 988 functions: 1,327 in `opt`, 588 in `middle opt`, 1
in `late opt`):

| Condition | Instances | Functions (all instances) | Rule true under it? |
| --- | ---: | ---: | --- |
| one operand a read-only literal | 1,805 | 920 | no: a fragment on the other side gives source `false`, target `poison` |
| both operands read-only | 7 | 0 | yes, but useless |
| both pointee types pointer-free | 1,916 | 988 | no: memory is untyped; a typed-memory premise is not preserved by `Move` and is a new top-level premise (fails criterion 1) |

**Semantic options for the splits.**
- **(a) B2** (`blob-regs.md` §6: a convertible fragment refines to its address byte, and `memEq`
  compares it as that byte) does not suffice:
  - narrow loads of fragments stay `poison`;
  - globals and temporaries are never convertible, so the recorded counterexample stands.
- **(b) `memEq` `poison` on fragments** makes defined Go programs (pointer struct `==`) undefined.
  This fails criterion 2: never.
- **(c) A provenance-free byte model:** concrete addresses for globals and frame temporaries, every
  fragment decodes to its address bytes at every width, and `memEq` compares address bytes. This is
  the only change under which all eight split rules are `Rule.Sound`.
  - **Defined-ness:** loads become strictly more defined. `memEq` changes `false` → `true` where a
    fragment equals concrete bytes. That is Go's answer, and sem-difftest must list each such change.
  - **What it touches** (lines in files):

    | Pattern | Lines | Files |
    | --- | ---: | ---: |
    | `Ptr.convertible` | 146 | 31 |
    | `Ptr.held` | 165 | 31 |
    | `Ptr.word` | 757 | 218 |
    | Phase 3 `AddrAgree` | 263 | 90 |
    | `Byte.Refines`/`Mem.Refines` | 418 | 64 |
    | `memEq` (including `memEq_mono` and the Phase 3 `MemEqSpec`, `Gen/G28.lean:33-37`) | 86 | 28 |

  - Frame temporaries are non-convertible by design (`InitAvoids`), so this is a change of #290's
    scale: ≥ 15–25 agent-days `[INFERENCE]`.

**Recommendation.**
- **Read-only loads and `:1628`:** do now, 1–1.5 days. Alone they gain 1 function, but they are a
  prerequisite of the class.
- **Splits:** defer (decision 5). Worth up to 988 Phase 1 functions (607 e2e at stock), but only
  through (c).

## 4. `condselect`: `CondSelect` into arithmetic (363 functions): (U), do

**Rules** (`generic.rules:2321-2394`):
- **Shape:** `(CondSelect op:(OpN <t> x c:(ConstN)) x bool) && rewriteCondSelectIntoMath(…) => (OpN x
  (MulN <t> c (ZeroExt8toN (CvtBoolToUint8 bool))))`.
- **Variants:** the `x`-first forms on `Not bool`, the `Sub` forms on `-c`, and the shift-by-1 forms.
- **Breakdown of the 363:** `:2378` 124, `:2342` 73, `:2371` 45, `:2368` 41, `:2322` 29, the rest
  51.

**Counterexample** (rules.md "Findings"):
- At `bool = false` the source is the leaf `x` and the target computes `x op 0`.
- A 64-bit integer shape may hold an address-less (held) pointer: `Val.hasTy (.ptr p) (.int .w64) =
  p.held`, `Sem/Layout.lean:168-170`. On such a pointer `Add64`/`Sub64`/`Or64`/`Xor64` are `poison`.
- Separately, `Rule.Sound` does not constrain the types of the `OpN`/`ConstN` nodes, nor of the narrow
  forms' leaf.

**Classification: (U), with an (M) remainder at 64 bits; not (G).**
- On machine words `x op 0 = x`. No upstream-candidate issue covers these rules.
- All 598 instances are in `late opt`'s input; `branchelim` builds the `CondSelect`s
  (`branchelim.go:168,353`).
- Go types every node at the op's width, so the narrow forms are true once the shapes are checked: a
  pointer has no narrow integer shape.

**Side-condition `condMathOK`** (rule-scoped, like `sameLeaves`):
- **(a)** The `CondSelect`, `OpN`, `x` and `c` all have the op's integer shape.
- **(b)** At 64 bits, also `intD x`: `x` is defined by an op whose value is always `.int` or `poison`
  (constants, arithmetic, logic, shifts, extensions, `CvtBoolToUint8`, or a `CondSelect`/`Copy` of
  them), with fuel 16 and no `Phi`.
  - It is a structural analysis like `nonNegD` (`Opt/RewriteCheck.lean:616-639`).
  - Its soundness is an `intD_den` lemma like `nonNegD_den`.

| Condition | Instances (of 598) | Functions (all instances, of 362 with an instance) |
| --- | ---: | ---: |
| (a) | 598 | 362 |
| **(a) ∧ (width < 64 ∨ `intD x`)** | **549** | **318** (199 e2e at stock) |
| … with `intD` through `Phi` (needs a run invariant) | 561 | 330 |

- **What fails:** the 49 failing instances are all 64-bit, with `x` a `Phi` (21), `ArgIntReg` (10),
  `SelectN` (9), a `CondSelect` of a `Phi` (5) or a `Load` (4). These are plain `int`s that the model
  cannot separate from a `uintptr` holding a pointer.
- **The (M) alternative for those 44 functions:** make `int2` ops the identity on a held pointer when
  the other operand is 0. It is strictly more defined, but ad hoc:
  - `int2` appears in 145 lines in 38 files;
  - known bits, prove, `MemCombine` and the low rules would need re-checking;
  - 8–12 days. Never.

**Cost:** 3.5–5 agent-days.
- (a): 0.5 day.
- `intD` with its soundness and the premise plumbing (`Den`/`DenT`/`RewriteTermStep`): 1.5–2 days. The
  precedent is the `nonNegOK` PR b1f301a9 (20 files).
- 59 rule lemmas: 1–2 days.
- The fire-probe fix (§8), docs and a re-probe: 0.5 day.

**Recommendation: do (U).**

## 5. `zero2159`: `Zero` over `VarDef (Zero …)` (55 functions): (M), do S3

**Rule** (`:2159`): `(Zero {t} [s] dst1 vardef:(VarDef (Zero {t} [s] dst2 _))) && isSamePtr(dst1,
dst2) => vardef`.

**Counterexample** (rules.md "Findings"; semantics.md "`VarDef` and `generic.rules:2159`, a model
gap"):
- `VarDef {n}` replaces `n`'s bytes with `poison` (`Sem/Run.lean:975-977`).
- The source's outer `Zero` restores zeros; the target keeps the `poison`.

**Classification: (M); not (G), not (U).**
- **What `VarDef` is in Go.** A zero-width liveness annotation (`genericOps.go:562`,
  `liveness/plive.go`). It writes nothing.
- **Go's dse.** It treats `VarDef` as not reading memory and does not shadow by it: only
  `Store`/`Zero`/`Move` extend the shadowed ranges (`deadstore.go:54,125-171`). So semantics.md §3's
  rationale ("this is what lets `dse` drop stores shadowed by a `VarDef`") does not match Go's dse.
- **The only clobbering in Go is MergeLocals,** which shares the slots of `PAUTO`s with disjoint live
  ranges starting at `VarDef` (`ssa/func.go:869-880`, `mergelocals.go`).
- **Instances** (66):
  - 58 on a result variable (`PPARAMOUT`), from `zeroResults`' `VarDef r; Zero r` followed by a
    whole-result assignment (`ssagen/ssa.go:645-663`, `:4570-4575`);
  - 8 on an inlined callee's `PAUTO` `~r0` (`index/suffixarray`, 3 functions).
- **Why it is not (U):** both side-conditions under which the rule is already true hold for 0 of 66
  instances. They are a different base variable, and the zeroed bytes being fully overwritten before
  any read.

**Semantic change S3:** `VarDef {n}` poisons only a `PAUTO`, and is the identity on
`PPARAM`/`PPARAMOUT`, as `VarLive` is.
- **Go justification:** only `PAUTO`s are ever merged. The class is already in `Tables`
  (`Sem/Run.lean:473-485`).
- **Effect on defined-ness:** strictly more defined; natively those bytes are untouched.
- **Code it touches:**
  - About 20 `VarDef`/`poisonBlock` lemmas get a poison-or-identity split (`poisonBlock`: 74 lines in 25
    files).
  - The dse checker's clearing of pending ranges at a kept `VarDef` (`Opt/DeadStoreCheck.lean:111-114`,
    `DSERel.pend_varDef`) must be restricted to `PAUTO`s. Go never relies on it.
- **Then the rule:** `:2159` holds for non-`PAUTO` variables, and the validator extends `zeroAt` (how
  `:2158` is proven) through a non-poisoning `VarDef`.

**Criteria:**
1. No statement changes.
2. Every difference is strictly more defined.
3. The only count risk is the dse restriction `[INFERENCE: none expected]`.
4. A dedicated semantics PR, then the validator PR.

**Gain and cost.**
- **Gain:** 52 of 55 functions (all their instances are `PPARAMOUT`), of which **42 are e2e at
  stock**.
- **Cost:** 3–4 agent-days.
- **The rejected variant S4** (`VarDef` the identity everywhere) adds 3 functions but removes the
  lifetime fact that Phase 3's MergeLocals validator needs (`proofs3.md`). Defer.

**Recommendation: do S3** (decision 4).

## 6. `divmod`: signed-typed `Div<N>u` by `smagic` (45 functions): (U), do C1

**Rules** (`divmod.rules:136-148`), for example `:148`: `(Div64u <t> x (Const64 [c])) && t.IsSigned() &&
smagicOK64(c) => (Rsh64Ux64 <t> (Hmul64u x (Const64 [m])) (Const64 [s]))`.

**Counterexample** (rules.md "Findings"): `t.IsSigned()` is an oracle atom; `:148` fails at c = 7,
x = 2^64-3.

**Classification: (U).**
- **Only prove builds a signed-typed `Div<N>u`.** It does so only when it has shown the dividend and
  divisor non-negative (`prove.go:2811-2818`); ssagen maps a signed division to the signed op.
- **The rule is true for a non-negative or `poison` `x`.** Then `SignExt` is `ZeroExt` and `smagic` is
  exact; the arithmetic is in `DivmodSMagic.lean` (`smagic_ok`, `sdiv_magic_int`).
- **Not (M):** a `poison` result on a negative dividend would make the source less defined.

**Side-condition:** a rule-keyed `FrameOK` conjunct like `sameLeaves`, requiring `(e.leaf x).nonNeg`.
- The validator decides it with the existing `nonNegD` in `condFrameOK`.
- Soundness reuses `nonNegOK_of`/`nonNegD_den`.
- The four lemmas become `Rule.SoundT`, as `:1053` did.

| Check (all instances; 71 instances, 66 `:148`, 5 `:140`) | Functions | e2e at stock |
| --- | ---: | ---: |
| C1 `nonNegD` as implemented | **23** | **12** |
| C5 = C1, or a dominating branch fact (`Leq`/`Less` against a non-negative bound, `IsInBounds`; PhiOptCheck's `ifGuard`/`domFact` shape) | 37 | 17 |
| C4 = C5 plus `Copy`/`Div`/`Mod` facts and a `Phi` fixpoint | 39 | – |

- **What C1 accepts:** the 29 `ZeroExt` dividends.
- **What the branch facts add:** 15 `Phi` loop variables (`for n >= 1000 { n /= 1000 }`) and 11
  `SelectN`/`Arg`/`Load` values behind an `if x <= 0 { return }` guard.
- **What nothing accepts:** 6 functions need prove's interval facts. Examples: `crypto/x509`
  `(bits.Len64(x)+6)/7`, and `time.Date`.

**Cost:**
- C1: 1–2 agent-days.
- Branch facts: 3–5 days, because they need a block-sensitive invariant in the rewrite simulation.
  They belong to a future prove validator (`docs/PASSES.md`) rather than a second fact system.

**Recommendation: do C1; defer the branch facts** (decision 3).

## 7. `rotate`: constant rotate detection (34 functions): (G, latent #90), do as (U)

**Rules** (`:2166`–`:2169`, each for Add/Or/Xor, 12 Lean rules): `((Add32|Or32|Xor32) (Lsh32x64 x
z:(Const64 [c])) (Rsh32Ux64 x (Const64 [d]))) && c < 32 && d == 32-c && canRotate(config, 32) =>
(RotateLeft32 x z)`.

**Counterexample** (#90): the condition compares `c` signed.
- At c = -1, d = w+1 both shifts give 0.
- `RotateLeft` by 2^64-1 rotates by w-1.

**Classification:** a latent Go bug, already tracked by #90 (open, `upstream-candidate`). No trigger is
known: the out-of-range shift fold wins in every case the integrator tried. **No new issue.**

**Side-condition:** `0 ≤ c`, a rule-keyed `FrameOK` conjunct on the auxint.
- With it the rule is true: shifts by ≥ w give 0, the bits are disjoint, and `RotateLeft` reduces its
  amount mod w.
- `canRotate` is an oracle conjunct, as for the proven `:2185`.

**Corpus:** all 124 instances (123 in `opt`, 1 in `middle opt`; c ∈ {1, …, 62}) have c ≥ 0, so all 34
functions qualify. Only **3 of 34 are e2e at stock**: most are crypto kernels that stop later in the
back end.

**Cost:** 1–1.5 agent-days.
- The conjunct and its check: 0.5 day.
- 12 lemmas in the style of `rule_rotamt`: 0.5–1 day. The `Or`/`Xor` rotate proofs are large terms
  (rules.md "Kernel deep recursion").

**Recommendation: do** (decision 2).

## 8. Side findings

1. **`RuleFireProbe.withExtra` undercounts "Unblocks"** (`GoFVTest/RuleFireProbe.lean:58-67`).
   - **The bug:** it rebuilds the proven table by looking up each full-set rule's key (`file:line Op`)
     with `find?`. Width variants share a key, so every variant becomes the first proven one.
   - **Example:** at `:2378`, 153 of 156 instances need the proven `generic.rules:398` variant 4 (`Not
     (Neq8 …)`) afterwards, which the table replaces by the `Neq64` variant. Hence "sole 99, unblocks
     0".
   - **Scope:** the sole-blocker sets used here come from the `OFF` lines and are not affected. The
     fix is to keep the proven rules by identity.
2. **`MemEqSpec` can be unsatisfiable** (`Gen/G28.lean:28-37`) `[INFERENCE]`.
   - The contract asks the machine's `X0` to match `memEq`.
   - `memEq` says `false` for a fragment against concrete bytes, where `runtime.memequal` returns `true`
     if they are the pointer's address bytes.
   - On such states the end-to-end theorem is vacuous, not unsound. Option (c) of §3 removes the gap.
3. **semantics.md §3 justifies `VarDef`'s poisoning by Go's dse.** Go's dse does not shadow by
   `VarDef` (§5); the poisoning is justified by MergeLocals for `PAUTO`s only.

## 9. Recommendation table and decisions

Gain is in Phase 1 sole-blocker functions (an upper bound), with the stock e2e column beside it.
Rows are ordered by Phase 1 gain per agent-day, taking the midpoint of the cost.

| # | Class: fix | Kind | Phase 1 gain | e2e at stock | Cost (agent-days) | Gain/day (P1; e2e) | Semantics change | Recommendation |
| --- | --- | --- | ---: | ---: | --- | --- | --- | --- |
| 1 | `condselect`: shapes + `intD` | U | 318 | 199 | 3.5–5 | 75; 47 | none | **do** |
| 2 | `memeq`: provenance-free byte model (c), with read-only loads and `:1628` | M | 988 | 607 | ≥ 16–26 | ≈ 47; ≈ 29 | #290-scale, `memEq` `false`→`true` listed | **defer** (design first) |
| 3 | `rotate`: `0 ≤ c` | G-latent (#90) / U | 34 | 3 | 1–1.5 | 27; 2.4 | none | **do** |
| 4 | `divmod`: C1 (`nonNegD`) | U | 23 | 12 | 1–2 | 15; 8 | none | **do** |
| 5 | `zero2159`: S3 (`VarDef` poisons `PAUTO` only) | M | 52 | 42 | 3–4 | 15; 12 | strictly more defined | **do** (dedicated semantics PR) |
| 6 | `convert`: M1 provenance-tagged integers | M | 281 | 212 | 20+ | ≈ 13; ≈ 10 | source less defined (fails criterion 2) | never |
| 7 | `condselect` 64-bit remainder: `int2` identity at 0 | M | 44 | – | 8–12 | 4.4 | ad hoc | never |
| 8 | `divmod`: branch facts (C5) | U | +14 | +5 | 3–5 | 3.5; 1.25 | none | defer to a prove validator |
| 9 | `memeq`: read-only loads + `:1628` alone | – | 1 | – | 1–1.5 | 0.8 | none | do as the prerequisite of row 2 |
| 10 | `convert`: (U) base/offset checks | U | 1 | – | 1.5–2 | 0.6 | none | never |

Rows 1, 3, 4 and 5 together are about 8.5–12.5 agent-days for up to 427 Phase 1 functions, 256 of
them e2e at stock. Row 2 is the largest pool and needs its own design review.

**Decisions asked of the integrator:**
1. **`condselect` (U):** approve the rule-scoped shape clause and the `intD` analysis.
2. **`rotate`:** approve the `0 ≤ c` conjunct (`Rule.SoundT`). #90 stays the Go-side record.
3. **`divmod`:** C1 now; branch facts deferred to a prove validator?
4. **`zero2159`:** approve S3 as a Phase 1 semantics change (`VarDef` is the identity on
   `PPARAM`/`PPARAMOUT`), with the dse checker restricted to `PAUTO` `VarDef`s.
5. **`memeq`:** commission a design review of option (c) (addresses for globals and frame
   temporaries, provenance-free fragment decoding, `memEq` on address bytes), or defer it. Read-only
   loads and `:1628` go ahead either way.
6. **`convert`:** confirm "never" (Go-undefined inputs), or open M1 as a criterion-2 exception.
7. **Probe fix (§8.1):** fix `withExtra` so that the "Unblocks" column stops undercounting.
