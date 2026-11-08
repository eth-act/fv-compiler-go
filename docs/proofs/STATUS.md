# Phase 1 status: generic passes (issues #69, #189)

The final state of Phase 1 rule coverage (the generic passes `number lines` … `writebarrier`,
`docs/PASSES.md`). Measured on main 4c002f5 with the changes of the PR that adds this page (#69, RuleFull15) and the corpus `full-v6` (format 5, 96,553 functions;
its Phase 1 sections equal `full-v5`'s except `cmd/compile/internal/ssa`). How each number is made:
"Commands" at the end. Details of every proof are in `docs/proofs/rules.md`; this page is the
summary.

## Headline

| Measure | full-v6 |
| --- | --: |
| Functions fully verified (`gofv-ssa-opt --check --verified`: every pass run `proven`, `identity` or `skipped`; by `verifiedPipeline_refines` the output refines the input under `VPre`) | 92,918 (main before: 92,902) |
| … and identical to stock at the last section | 76,362 (76,354) |
| Functions every rewrite section of which the checked proven-only passes reproduce exactly (`opt-proven-probe`) | 93,199 / 96,553 (main before: 93,174) |
| … under the proven-only passes alone (without the validator) | 93,304 |
| … the validator the only obstacle (`BLOCKED`) | 105 (130) |

History on full-v5: 92,885 fully verified after #419 (RuleFull14); the last full-v5 number before
this summary.

## Rules

1,762 rule alternatives (`generic.rules` 1,654, `dec.rules` 47, `divisible.rules` 32,
`divmod.rules` 29; an alternative is one width or commuted form of a source rule), classified by
the semantic phase of their ops (`GoFVTest/Proof/RuleClass.lean`; "Classification" in
`rules.md`).

| Class | Proven | False | Open | Total |
| --- | --: | --: | --: | --: |
| P1 (integers, booleans) | 1,212 | 30 | 153 | 1,395 |
| P2 (pointers, composites, `Load` values, `SelectN`) | 69 | 1 | 39 | 109 |
| mem (memory ops) | 53 | 0 | 59 | 112 |
| call | 11 | 0 | 36 | 47 |
| float | 22 | 0 | 46 | 68 |
| ptr (`ConstString`, `Addr`, `NilCheck`, pointer comparisons) | 12 | 0 | 11 | 23 |
| phi | 5 | 0 | 0 | 5 |
| block | 3 | 0 | 0 | 3 |
| all | 1,387 | 31 | 344 | 1,762 |

*Proven*: a merged lemma (`Rule.Sound`, `Rule.SoundT`, `Rule.SoundW`, `Rule.MakeSel`,
`Rule.LoadSel`, `Rule.Drop`, `Rule.IMakeSM`, `Rule.AddrCmp`, `BlockRule.Sound`,
`EffectRule.NilElim`/`LoadFwd`/`StructLoad`/`StructStore`/`Seg`/`PhiSel`, `ConstString` frame
rules, dec rules); `GoFV/Rules/Proven.lean` is the proven-only rule set the theorems are about.
Per op family: the "Coverage" table of `rules.md`. The constant `Phi`s `generic.rules:782–785`
are checked by the validator layer `.pc` with sccp's checker (`GoFV.Proof.PhiConst.pc_refines`),
the `IMake` of a `StructMake` (`generic.rules:981`, `dec.rules:102`) per instance
(`RewriteCheck.imsOK`, `GoFV.Proof.Pass.Rewrite.IMFacts.step`) (#69, Phase1Tail), the
comparisons of two symbol addresses (`:1648`, `:1651`) per instance (`RewriteCheck.addrCmpOK`,
`ACFacts.step`), and the selections of an `IData` (`:982`, `:983`, `:1001`, `dec.rules:103`,
`:104`, `:127`) as `Rule.Sound` with the interface shape of the `IData` operand (`idataArgOk`),
and the `runtime.ifaceeq`/`efaceeq` folds (`:2279`, `:2287`, with `SelectN` of `MakeResult`
`:1343`) in the forwarding layer under the runtime contract `Env.IfaceEq` (§ Assumptions;
`RewriteCheck.eqCallOK`, `selMROK`) (#69, Phase1Tail2), and the `Phi` of two `Not`s
(`generic.rules:1068`, turned `Not` of a fresh `Phi`) by the validator layer `.pn`
(`RewriteCheck.pnRel`, `GoFV.Proof.PhiNot.pn_refines`) (#69, Phase1Tail4).

**False under the semantics, with the reason** (31, each marked `-- FALSE r_… #N` in its proof
module; "Findings" in `rules.md`):

- `generic.rules:2166–2169`, three alternatives each (12): constant rotate detection compares the
  shift constant signed; at `c = -1`, `d = w+1` both shifts give 0, but
  `RotateLeft x (Const [-1])` rotates by `w-1`. A Go bug candidate (#90, `upstream-candidate`).
- `CondSelect` into arithmetic, `:2325` (3), `:2342` (3), `:2355` (4), `:2368` (1), `:2371` (3)
  (14): at `bool = false` the match is the leaf `x`, the result recomputes it, and a 64-bit
  register may hold an address-less pointer on which `Sub64`/`Or64` are `poison`.
- `divmod.rules:136`, `:140`, `:144`, `:148` (`Div16u/32u/64u` of a signed type by `smagic`, 4):
  the dividend need not be non-negative; Go establishes that in `prove` before. Counterexamples
  in `rules.md`.
- `generic.rules:1039` (`config.PtrSize == 4`, 1): it builds 32-bit lengths into a 64-bit slice
  shape (`rule-sat` counterexample).

Also false, but counted as open (no marker; they fire, so the firing table lists them; sole
obstacle counts on full-v6, "Findings" in `rules.md` has the counterexamples):

- `generic.rules:1071`/`:1075` (`Convert` of an integer offset from a converted pointer: integers
  carry no provenance, so the pointer made from `addr(p) + off` need not be in `p`'s allocation,
  #156; the most frequent sole obstacle on full-v6, 255 functions).
- `:579` (#542, a Go bug, upstream golang/go#82763; `Lsh32x64` of `And32 (Rsh32x64 x c) d` by `e`, `c < e`: false for `c < 0`, `x = -1`,
  `d = 1`, `c = -1`, `e = 1` gives `2` against `0`; 9 functions).
- `MemEq` → `Eq*` of two `Load`s, `:1560`/`:1568`/`:1576`/`:1584` (with the read-only loads
  `:1564`/`:1572`/`:1580`/`:1588` they fire on; about 330 functions, in pairs): `memEq` compares
  the raw bytes, pointer fragments included, but an integer `Load` of a pointer's fragment bytes
  is `poison`, so `true` becomes `poison`.
- `:2159` (`Zero` of a `VarDef` of a `Zero` of the same pointer dropped; 48 functions): `VarDef`
  makes the variable's bytes `poison`, so the second `Zero` is not an identity write in the model.
- The `CondSelect` folds (about 240 functions on the unmarked alternatives of `:2322–:2393`) and
  `divmod.rules:136–148` (59) are false as above.

**Open** (344):

- `P1`/`P2` alternatives without a lemma (192): most never fire on the corpus; those that fire
  are in the `fire-full` table of `rules.md` (sole obstacles by rule).
- `mem` (59) and `ptr` (11): memory and pointer rules inside the model without an effect
  obligation proof: `Load` forwardings of other shapes (`:831–:907`), `Move` chains and
  `Move`/`Zero` of `Store`s (`:1740–:1942`), dropped writes `:919`/`:924`/`:930`/`:937` (open:
  the `not disjoint` class), the other `EqPtr`/`NeqPtr` of symbol addresses, locals and their
  offsets (`:1649–:1676`; `:1648`/`:1651` are proven), and `ConstString` under
  `config.PtrSize == 4` (`:1013`, `:1017`; never true
  for linux/arm64).
- `float` (46): inside the model (`Sem/Float.lean`, the AArch64 instruction of each op with
  RNE): constant folds of `Add/Sub/Mul/Div/Neg{32,64}F`, `Cvt*` of constants,
  `Ceil/Floor/Trunc/Round/RoundToEven/Sqrt` of constants, `OrB`/`Not` of float comparisons.
- `call` (36): `memequal` folds (`:1395–:1557`; `memequal` has a contract), the `Const32`
  alternatives of the proven call segments, `growslice` lengths at `Const32`
  (`:2128`/`:2131` alternatives), devirtualisation `:1733`, and **outside the model**: the
  `runtime.cmpstring` rules `:2267`, `:2271` (no contract in `Env.runtime`) and the race
  instrumentation cleanup `:2115`, `:2116` (race mode is not modelled).

## Phase 2: the verified pipeline through `trim` (#385, #189)

`GoFV.Proof.PipelineFull.verifiedPipelineFull_refines`: for a `fullyVerified` result of
`verifiedPipelineFull`, every returning or panicking `run` of the input is, up to refinement, a
`runLoc` of the allocated function after `trim`, under Phase 1's `VPre`, no nil-page fault of
the recorded `schedule` inputs, valid pointer parameters and valid checked pointers (`ArgPtrsOK`,
`NilPtrsOK`; all assumptions in one table below, § Assumptions)
(`docs/PASSES2.md` §0; witness `verifiedPipelineFull_witness`).
Measured with `gofv-ssa-opt --check --verified`: full-v9 on main 91883690 (`--jobs 6`, after
#540 constant `Phi`s and `IMake` of `StructMake`, #558 symbol-address comparisons and `IData`
selections, #559 `ifaceeq`/`efaceeq` folds; 96,560 functions, format 5.1, 463 min on a heavily
loaded machine); quick-v7 on main 51ef75c1 (6 min):

| Measure | full-v9 through `rewrite tern` (Phase 1) | full-v9 through `trim` | quick-v7 Phase 1 | quick-v7 through `trim` |
| --- | --: | --: | --: | --: |
| Functions fully verified | 93,475 (06aa0962: 92,925) | 78,876 (06aa0962: 77,952; f4da51ff #530: 75,387) | 8,885 | 6,383 |
| … verified (vacuous: unmodelled op): the input has an op or block kind `run` leaves stuck (`TailLECall*`, `RetJmp`) | 1,576 | 1,568 | 168 | 168 |
| … relying on `NilPtrsOK` (a `schedule` swap through `nilPtrSwap`) | – | 2,983 (06aa0962: 2,935) | – | – |
| … and identical to stock after `trim` | 74,595 (74,348) | 66,331 (65,752) | 7,233 | 5,699 |

Every pass from `lower` to `trim` has a theorem (addressing modes `addressingModes_refinesL`,
late lower `lateLower_refinesL`, pair `pair_refinesL`, flagalloc `flagalloc_refinesSched`).
`regalloc` now accepts all 96,560 full-v9 runs (`tabsAgreeModL` takes the new spill autos that
rejected 21,197 runs before). Of the 14,599 full-v9 functions verified through Phase 1 but not
through `trim`, the first unverified run is `lower` for 14,068 (checked variant incomplete
11,805, rejected 2,263), `schedule` (rejected) 389, `late lower` (rejected) 137, `lowered
deadcode` (rejected) 5 (06aa0962: `schedule` 378; #530: 1,019; 51ef75c1: 3,365). The 718 rejected
`schedule` runs (389 first unverified) are all in deferred classes: a nil check of a
pointer-shaped value the source computes after the faulting value (483 / 303), of a value that
is not pointer-shaped (215 / 77), of an `argPtr` piece after it (2 / 2), and `LoweredMove` before
a load on another memory (18 / 7). The Phase 1 functions not verified through `rewrite tern`
(3,085; 06aa0962: 3,635), by first unverified run: opt 1,867, late opt 597, middle opt 370,
decompose builtin 116, decompose user 59, divmod 47, expand calls 28, opt deadcode 1.
`driver-e2e.sh --verified -p 8` (66 min, a717e6db+):
183/183 programs behave as stock, 0 fallbacks, 0 pass errors; 29,590 of 42,899 functions fully
verified through `trim`.

## Phase 3: genssa, slice G1 (I7, #553)

`GoFV.Proof.Gen.g1_value`, `GoFV.Proof.Gen.g1_term` (`GoFV/Proof/Gen/G1.lean`): when the genssa
validator's slice G1 (`checkG1`) accepts a function, every non-entry value and every terminator
that goes to a successor, run by `runLoc` from a state related by `LocMatch` to a machine state,
is matched by `runProg` steps of genssa's P0 Progs to a state related before the next value or
the successor's first value. Premises (`docs/plans/proofs3.md` §3): `G1Env` (the PC table, `ret`
no Prog address, `ι` puts every block with a Phase 1 address there but frame temporaries
`Blk.temp`, no frame), `G1Inv` (no slot, registers hold values of their width class, distinct
memory block keys) and the per-step `G1Pre`/`G1TermPre` (compare arguments and `Z`/`NZ` controls
are not pointers without an integer form, a load reads 8 valid bytes, the pointer operands of a
subtraction are in one block or in no frame temporaries: `SubPre`, added with G6). Witness
`genG1_witness_50`/`_30` (`clamp`, both theorems).
Coverage on quick-v9 (`lake exe gen-check`): 268 of 9,297 functions (2.88%).

## Phase 3: genssa, slice G2 (I7, #553)

`GoFV.Proof.Gen.g2_value`, `GoFV.Proof.Gen.g2_term` (`GoFV/Proof/Gen/G2.lean`): when slice G2
(`checkG2`: G1 plus static calls and their results, addresses of globals, 64-bit spills and
reloads at their frame operands, `Exit` blocks) accepts a function, every non-entry value and
every terminator that goes to a successor is matched by `runProg` steps of genssa's P0 Progs
(P0's `CALL sym(SB)` goes to the symbol, `runProg_callMem_witness`) to a state related before the
next value or the successor's first value. Values may grow the injection (`E.Extends E'`, at a
call) and keep `G2Env`. Premises (`docs/plans/proofs3.md` §4): `G2Env` (G1's, plus a frame when the
function calls, globals at their symbols under `ι`, the callees' symbols outside the Progs, each
home slot at its frame operand, the frame layout `FrameOK`), `G2Inv` (G1's register classes and
block keys, the live blocks away from the saved `LR`/`FP` and the slots, every live slot a 64-bit
value of a home slot), `G1Pre`/`G1TermPre`, and at a static call the trusted callee contract
`CallOK` (§ Assumptions). Witnesses `genG2_value_witness` (`testInts`: a spill, a call, its
memory, a reload) and `genG2_term_witness_50`/`_30` (`clamp`: a G1 value and a branch).
Coverage on quick-v10 (`lake exe gen-check`): 1,171 of 9,297 functions (12.59%), 10,665 values.

## Phase 3: genssa, slice G3 (I7, #553)

`GoFV.Proof.Gen.g3_value`, `GoFV.Proof.Gen.g3_term` (`GoFV/Proof/Gen/G3.lean`): when slice G3
(`checkG3`: G2 with register width classes by dataflow — the class table `kt`, checked by
`checkK` — narrow loads and stores through a register or of a global, extensions,
`AND`/`LSL`/`LSR $k`, `UBFX`, `CMPW`, `SB`, and the `ZW`/`NZW`/`TBZ`/`TBNZ` tests) accepts a
function, every non-entry value and every terminator that goes to a successor is matched by
`runProg` steps of genssa's P0 Progs to a state related before the next value or the successor's
first value, with the registers at the classes the table gives there. Premises
(`docs/plans/proofs3.md` §4): `G2Env`, `G3Inv` (G2's with the class map `kAt lc kt b blk i` in
place of `regCls`), `G3Pre` (G1's compare and subtraction premises; a load reads valid bytes, a
boolean load 0 or 1) or `G1TermPre`, and at a static call `CallOK`. Witnesses
`genG3_witness_clear`/`_set`
(`pallocSum.start`, which G2 rejects: the bit test `TBNZ [63]` both ways, then `ANDconst`).
Coverage on quick-v10 (`lake exe gen-check`): 1,611 of 9,297 functions (17.32%), 17,270 values.

## Phase 3: genssa, slice G4 (I7, #553)

`GoFV.Proof.Gen.g4_value`, `GoFV.Proof.Gen.g4_term` (`GoFV/Proof/Gen/G4.lean`): when slice G4
(`checkG4`: G3 with the pair load `LDP` into a register pair, the pair store `STP` of two 64-bit
registers, both through a 64-bit register, and `Select0`/`Select1` of an `LDP` in its component's
register) accepts a function, every non-entry value and every terminator that goes to a successor
is matched by `runProg` steps of genssa's P0 Progs to a state related before the next value or the
successor's first value, with the registers at the classes the table gives there. Premises
(`docs/plans/proofs3.md` §4): G3's, with `G4Pre` (`G3Pre`, and a pair load reads valid bytes at
both of its addresses) for values. Witnesses `genG4_value_witness` (`(*errorString).Error`, which
G3 rejects: `LDP (R0), (R0, R1)` and its two selects) and `genG4_term_witness` (`pallocSum.start`:
`TBNZ [63]`). Coverage on quick-v10 (`lake exe gen-check`): 1,832 of 9,297 functions (19.70%),
21,243 values.

## Phase 3: genssa, slice G5 (I7, #553)

`GoFV.Proof.Gen.g5_value`, `GoFV.Proof.Gen.g5_term` (`GoFV/Proof/Gen/G5.lean`): when slice G5
(`checkG5`: G4 with the memory markers `VarDef`, `VarLive`, `KeepAlive` and `WBend`, which emit no
code) accepts a function, every non-entry value and every terminator that goes to a successor is
matched by `runProg` steps of genssa's P0 Progs to a state related before the next value or the
successor's first value, with the registers at the classes the table gives there. Premises
(`docs/plans/proofs3.md` §4): G4's (`G2Env`, `G3Inv`, `G4Pre` or `G1TermPre`, `CallOK`); no new
premise. Witnesses `genG5_value_witness` (`g` of `test/stackobj`, which G4 rejects: a spill, a
static call, its memory and `KeepAlive` of the spilled argument) and `genG5_term_witness`
(`pallocSum.start`: `TBNZ [63]`). Coverage on quick-v10 (`lake exe gen-check`): 1,833 of 9,297
functions (19.71%), 21,252 values.

## Phase 3: genssa, slice G6 (I7, #553)

`GoFV.Proof.Gen.g6_value`, `GoFV.Proof.Gen.g6_term` (`GoFV/Proof/Gen/G6.lean`): when slice G6
(`checkG6`: G5 with the accesses of frame variables of `NAME_AUTO` operands whose address the
function never converts to an integer — `Blk.temp`: `MOVDaddr` of one, G3's loads and stores and
G4's `LDP`/`STP` at its frame operand — their windows checked disjoint inside the locals and away
from the home slots) accepts a function, every non-entry value and every terminator that goes to
a successor is matched by `runProg` steps of genssa's P0 Progs to a state related before the next
value or the successor's first value, with the registers at the classes the table gives there.
Premises (`docs/plans/proofs3.md` §4): `G6Env` (`G2Env`, and `VarsAt`: each accessed variable's
block of the current activation at `SP + frameOff` under `ι`, which `AddrAgree` allows since it
leaves frame temporaries free), `G3Inv`, `G4Pre` (with `SubPre`) or `G1TermPre`, `CallOK`.
Witnesses `genG6_value_witness` (`SChan.Send` of `test/closedchan`, which G5 rejects: the store
`MOVD R1, -8(RSP)` and the address `MOVD $-8(RSP), R1` of a frame temporary) and
`genG6_term_witness` (`pallocSum.start`: `TBNZ [63]`). Coverage on quick-v10 (`lake exe
gen-check`): 1,946 of 9,297 functions (20.93%), 24,819 values.

## Per-pass fragment coverage (verified pipeline, full-v6)

Runs per pass of `gofv-ssa-opt --check --verified` (96,553 functions, each pass run once per function). *Proven*: the theorem's variant ran and changed the function; *identity*: same function (or tables the function cannot tell apart); *skipped*: an optional pass outside its fragment (the input is kept); *unverified*: a required pass outside its fragment, or a checked rewrite pass whose result differs from stock (`checked variant incomplete`: an unproven rule fired or the validator rejected; the stock result is kept). Every Phase 1 pass has a theorem; `insert resched checks`, `cpufeatures` and `rewrite tern` never run for linux/arm64.

| Pass | Proven | Identity | Skipped (fragment) | Unverified | Theorem's fragment / guard |
| --- | --: | --: | --: | --: | --- |
| number lines | 96,553 | 0 | 0 | 0 | none |
| early phielim and copyelim | 72,822 | 23,071 | 660 | 0 | `copyFrag`, `emptyFragB` |
| early deadcode | 95,861 | 32 | 660 | 0 | `deadFragB` |
| short circuit | 53,781 | 42,772 | 0 | 0 | none |
| decompose user | 11,312 | 85,182 | 0 | 59 | `decUserFrag` (required) |
| pre-opt deadcode | 55,939 | 39,952 | 662 | 0 | `deadFragB` |
| opt | 56,822 | 37,308 | 0 | 2,423 | checked variant (validator); stock kept if incomplete |
| zero arg cse | 30,665 | 65,888 | 0 | 0 | none |
| opt deadcode | 34,050 | 62,500 | 0 | 3 | `deadFragB` |
| generic cse | 95,429 | 0 | 1,124 | 0 | `cseFrag` |
| phiopt | 5,048 | 91,505 | 0 | 0 | none |
| gcse deadcode | 42,131 | 54,422 | 0 | 0 | `deadFragB` |
| nilcheckelim | 54,490 | 30,132 | 11,931 | 0 | `nilFrag` |
| prove | 86,192 | 10,352 | 9 | 0 | `proveGuard` (size) |
| divisible | 32,864 | 63,689 | 0 | 0 | checked variant |
| divmod | 1,976 | 94,526 | 0 | 51 | checked variant |
| middle opt | 25,486 | 70,502 | 0 | 565 | checked variant |
| known bits | 524 | 96,029 | 0 | 0 | none |
| early fuse | 20,288 | 76,265 | 0 | 0 | none |
| expand calls | 96,500 | 6 | 0 | 47 | `expandCallsFrag` (required) |
| decompose builtin | 68,017 | 28,367 | 0 | 169 | `decBuiltinFrag` (required) |
| softfloat | 0 | 96,553 | 0 | 0 | none |
| branchelim | 22,216 | 74,337 | 0 | 0 | none |
| late opt | 95,529 | 147 | 0 | 877 | checked variant |
| dead auto elim | 5,363 | 88,641 | 2,549 | 0 | `daeFrag` |
| sccp | 12,585 | 83,968 | 0 | 0 | checked variant |
| generic deadcode | 44,818 | 51,735 | 0 | 0 | `deadFragB` |
| late fuse | 18,540 | 78,013 | 0 | 0 | none |
| check bce | 0 | 96,553 | 0 | 0 | none |
| dse | 6,944 | 89,491 | 118 | 0 | `dseFrag` |
| memcombine | 3,000 | 93,553 | 0 | 0 | checked variant |
| writebarrier | 18,252 | 78,301 | 0 | 0 | `wbGuard` (required) |

Functions by first unverified run (3,635 of 96,553): opt 2,392, late opt 607, middle opt 389, decompose builtin 113, decompose user 59, divmod 47, expand calls 27, opt deadcode 1. Skipped runs keep the input, so they cost no verification, only stock identity (functions by first difference from stock: nilcheckelim 11,147, prove 5,576 (its own result differs, `proveChecked`), generic cse 1,107, early phielim and copyelim 660, dead auto elim 245, memcombine 154, dse 32, the rest 12). The deadcode/copyelim fragment failures are mostly zero-size values (`emptyFrag`: `empty Load empty` 447, `empty StructSelect empty` 178).

## Remaining validator classes (functions whose only obstacle is the rewrite validator, 105)

`BLOCKED` lines of `opt-proven-probe` (every rewrite section at stock under the proven-only
passes, not under the checked ones), by class (the generated table is `fire-full` in `rules.md`):

| Class | Functions | Why it is open |
| --- | --: | --- |
| `fwd₂: not disjoint` (`OffPtr` 36, `LocalAddr` 9, `SelectN` 7, in a snapshot segment 1, with a `drop chain Zero` in opt 1) | 54 | A forwarding past a store the validator cannot show disjoint from the `Load` (RuleFull13's and RuleFull14's analysis on #69). Three causes, none provable from `VPre`: stores into `PPARAM` slots (disjointness of a parameter slot from the other frame slots needs an `InitAvoids`-style precondition for parameter slots; the integrator decided not to add a `VPre` conjunct for it), two distinct `mallocgc` results (a relation between the results of two calls), and Go's `disjointTypes` (type-based aliasing: a store of one type cannot alias a load of an incompatible pointer type), out of scope (#111). |
| `fwd₂: move: ptr AddPtr` | 7 | A `Load` through a `Move` (`:827`) whose pointer is an `AddPtr`, which `fwdMoveOK` does not relate to the `Move`'s destination plus the offset. |
| `final: fields Copy->Copy` (late opt, snapshot segments) | 6 | Go's `copyOf` gives a forwarded `Load`'s `Copy` the stored value's type (`v.Type = a.Type`); the forwarding layer keeps the `Load`'s type, and the final comparison with the snapshot asks for equal types. Retyping the `Copy` in the layer needs the forwarding proof to carry the value across the retype. |
| `seg₁: rel` | 5 | `segOK` holds at every anchor, but `segRel`'s checks across the block fail (a dropped value used outside its segment, or a schedule that is not the source's with each segment's roots replaced). |
| `seg₁: SelectN→Move` | 5 | `memmove` call segments (`:1730`) whose size `Mul64 (SliceLen (SliceMake p (Sub64 a b) …)) (Const64 [1])` is not a constant term `termConst` evaluates: the rule matched a `Const64` size that other value rules folded first. |
| `seg₁: SelectN→Zero` | 2 | `memclrNoHeapPointers` call segments (`:1638`) whose `Zero` takes another pointer than the call's argument (a value rule rewrote it before the segment matched); `callSeg?` asks for the call's own arguments. |
| `fwd₂: store type` (late opt) | 5 | A forwarding between a pointer and a one-field struct of that pointer (`struct{p *T}`): the same bytes, but the forwarding's type check (`fwdTy`) does not relate the two shapes. |
| `fwd₂: rep Load->Const64F`, `move: args … Copy`/`LocalAddr`, `drop chain Store`/`SelectN` | 7 | Single shapes of forwardings and dropped-write chains. |
| `seg₁: Move→Store ⟨zero⟩` (2), `⟨store⟩` (1), `Store→Store` (1) | 4 | Single move and chain segments the segment checks do not match (the stores do not end in a `Zero` of the `Move`'s size; a store not at an offset of the source). |
| `nil₂: nrel` (`Convert` 2, `CondSelect` 1), `fwd₂: ptr NilCheck` 2 | 5 | Nil checks of pointers made from integers (`runtime.int32Hash`/`int64Hash`: `Convert` of an `Xor64`) or a `CondSelect` of two addresses, which no seed of `safePtr` covers. |
| `rule arity` (2), `atoms` (1), `ss: field 0 of 1` (2) | 5 | Single cases. |

Not validator classes, recorded with the remaining gaps:

- **`:1352` on `zerobase`** (quick corpus): `runtime.newobject`/`mallocgc` of size 0 return
  `runtime.zerobase` with the memory unchanged; `Env.AllocZero` claims nothing about it, so a
  dropped zero `Store`/`Zero` at such a result is not a refinement (zerobase may be a writable
  allocation with nonzero bytes). Option (a), a fresh 0-byte block, was rejected (pointer equality
  with `&zerobase` is observable); option (b), zerobase read-only in the image, was not worth the
  8 functions it would gain (#151, RuleEffects17).
- **The `recoverLoop` gap** (`docs/plans/semantics.md` §9.7, §10): after a recovery Go resumes at
  `f.DeferReturn` and reads results that escaped to the heap through SSA values; the model's
  `runDefers` reads the result's stack slot, which is `poison`, so such a run is `stuck` (sound:
  no obligation; 5 functions on full-v5).

## Assumptions

`verifiedPipeline_refines` concludes `RefinesFrom (VPre k ro)` (`GoFV/Proof/Pass/Pipeline.lean`);
every pass theorem's precondition is a conjunct. `k` are the input's dictionary parameters, `ro`
its read-only symbols. `verifiedPipelineFull_refines` adds three assumptions on the recorded
`schedule` inputs `r.nnf` (its `hn`, `ha`, `hnp`). Every assumption of the end-to-end theorems,
in one table: what it assumes, why it is justified, what would falsify it, and what
discharges it (the runtime model `Env.runtime`, the Phase 1 test environment `Env.p1`, or the
witnesses):

| Assumption | Assumes | Justification | Falsified by | Discharged for |
| --- | --- | --- | --- | --- |
| `env.Mono` (`VPre`) | every contract is monotone: a refined call (arguments, closure, memory) gives a refined outcome; calls observe their arguments (`Contract.Mono`, `GoFV/Proof/RunMono.lean`) | a callee cannot behave better on less defined arguments | a contract whose outcome on a more defined argument is less defined | `Env.p1_mono` |
| `env.FrameSafe` (`VPre`) | contracts cannot read or keep pointers into the caller's frame temporaries (results and memory avoid them, the rest equal off them) | Go's escape analysis keeps frame temporaries out of callees' reach | a callee that reads or retains a pointer into the caller's frame temporaries | — (assumed of the runtime) |
| `InitAvoids env args mem` (`VPre`) | the arguments, the memory and the global image hold no pointer into a `temp` block | no frame temporary exists before the frame | an input pointing into a `temp` block | a property of the inputs; `pfRunEnv_initAvoids` |
| `env.AllocNonNil` (`VPre`) | malloc-family contracts return a non-nil pointer first (`NilCheck.mallocName`) | the runtime's allocator throws instead of returning nil | an allocation returning nil | `Env.runtime_allocNonNil`, `Env.p1_allocNonNil` |
| `DictArgs k args` (`VPre`) | the dictionary arguments (indices `k`) are non-nil pointers | the compiler passes the instantiation's dictionary | a nil dictionary argument | a property of the inputs |
| `WB.WbPre env args mem` (`VPre`) | the memory with the global image has a defined, read-only `runtime.writeBarrier` flag and no write-barrier buffer, contracts keep that, and `runtime.wbZero`/`runtime.wbMove` are the runtime's helpers | the runtime's write-barrier protocol | a contract writing the flag, or helpers other than the runtime's | `plRunEnv_wbPre` (witness) |
| `env.noSpill` (trusted, in `WbHelpers`) | `runtime.wbZero`/`runtime.wbMove` do not spill into the caller's outgoing area | checked by hand against the go1.27.3 linux/arm64 disassembly (#36) | a runtime build whose helpers spill into the outgoing area | trusted |
| `env.TempOblivious` (`VPre`) | contracts cannot tell whether unreachable `temp` blocks exist | unreachable memory is unobservable to Go code | a contract whose outcome depends on unreachable frame temporaries | — (assumed of the runtime) |
| `env.MemOps` (`VPre`) | `runtime.memclrNoHeapPointers`/`runtime.memmove`, if present, are the runtime model's | they are the runtime's functions | other definitions of those symbols | `Env.runtime_memOps`, `Env.p1_memOps` |
| `RoImage ro env mem` (`VPre`) | contracts keep the read-only global allocations and return no memory; the symbols `ro` are read-only allocations of the memory with the global image holding their exported bytes | read-only data is mapped read-only | a write to a read-only symbol | `Env.runtime_keepsRo`, `Env.p1_keepsRo` (the image part is a property of the inputs) |
| `env.FrameKeep` (`VPre`) | contracts keep the caller's frame allocations and return no memory | callees do not free their caller's frame | a contract that drops the caller's frame | `Env.runtime_frameKeep`, `Env.p1_frameKeep` |
| `env.AllocZero` (`VPre`) | malloc-family contracts asked for a positive size return a fresh all-zero heap block (size 0 returns `runtime.zerobase`, about which nothing is claimed) | the allocator's contract | a non-zeroed or aliased allocation | `Env.runtime_allocZero`, `Env.p1_allocZero` |
| `env.GrowLen` (`VPre`) | `runtime.growslice`/`growsliceNoAlias`, if present, return a slice of their `newLen` argument | the runtime's contract | another length | `Env.runtime_growLen`, `Env.p1_growLen` |
| `env.IfaceEq eq` (`VPre`, `eq = Verified.pipelineEq env`; `RwPre`, `eq = RewriteCheck.eqPass tabs fe`) | `runtime.ifaceeq` on (a word pointing at the start of) an itab symbol of `eq.1`, and `runtime.efaceeq` on a type symbol of `eq.2`, if present, return `[PtrOps.eqPtr false [x, y]]` (the pointer equality of their data words) and the memory they were given; `eq` holds the itab and type symbols of the input's tables and the frontend's tables whose type the export marks direct-interface and comparable (`types.IsDirectIface`, `types.IsComparable`) | the runtime's code, `third_party/go/src/runtime/alg.go`: `efaceeq(t, x, y)` returns `true` for a nil `t`, panics if `t.Equal` is nil, returns `x == y` if `t.IsDirectIface()`, else `eq(x, y)`; `ifaceeq(tab, x, y)` is it with `t := tab.Type`. A comparable type has an `Equal`, a non-nil symbol is no nil descriptor, so both return `x == y` and write nothing (`generic.rules:2279`/`:2287` fold them so) | an export whose direct/comparable flags disagree with the runtime type's `TFlagDirectIface`/`Equal`, or a runtime that writes memory or panics there | `Env.runtime_ifaceEq`, `Env.p1_ifaceEq` (absent), `Env.ifaceEqDemo_ifaceEq` (present) |
| `NoNilFault tabs f env args mem` (`r.nnf`) | no run of the `schedule` input faults in the nil page or checks a wild pointer (`runL` and `runLF` agree) | `schedule`'s theorem is stated against `runLF` (memory ops fault), the passes before it against `runL`; this restricts the end-to-end statement to such inputs | — (a restriction, not a claim about Go) | `noNilFault_of_noAct` (witnesses) |
| `ArgPtrsOK tabs f env args mem` (`r.nnf`) | every pointer-shaped register piece of a parameter (`ArgIntReg` at a `.ptr` shape) reads nil or a pointer that is not wild (`Ptr.wild`: into the nil block but not nil) | Go-level: Go's type system and the garbage collector require a pointer parameter to be nil or valid; `unsafe` code that forges a wild pointer is outside the model. `swapOKB`'s `argPtr` case moves a nil check of such a piece before a fault on the same memory: it panics alike or passes, where a wild pointer would leave it `stuck` | a caller passing a forged pointer (an integer address, or nil plus an offset) as a pointer argument | `argPtrsOK_of_none` (witnesses) |
| `NilPtrsOK tabs f env args mem` (`r.nnf`, approved on #385) | in every state `runLF` of the `schedule` input reaches (a block entry, after its `Phi`s and any prefix of its order), every pointer-shaped value that a nil check checks reads nil or a pointer that is not wild, once it has a register (`NilRegsOK`) | Go-level, as `ArgPtrsOK`: a Go pointer is nil or points into an allocated object (the `unsafe.Pointer` rules); the runtime throws on a pointer in the nil page (`runtime/stack.go:676`, "invalid pointer found on stack", `0 < p < minLegalPointer`). Only checked pointers: a compiler-made `nil + k` may be computed before the check of its base panics. `nilPtrSwap` moves such a check before a fault on the same memory | a function that loads, converts or receives a forged pointer and nil-checks it (`unsafe` misuse) | `nilPtrsOK_of_none` (witnesses: `clampL_noNilPtr`, `pfF_pipeline`'s `noNilPtrB`) |
| hook `liftContract` (Phase 3, `GoFV/SSA/Sem/Hooks.lean`, `rtHookNamed`) | a call of a runtime entry point with a Phase 1 contract (`Env.runtime`) behaves as that contract lifted through ABIInternal: arguments read from their `abi.RegIndex` registers and `SP + offset` stack slots (or `fixedABI`'s registers for `LoweredMemEq` → `runtime.memequal`), memory pulled back and pushed forward through `ι`, results written to their ABI locations, `R0`–`R17`, `R19`–`R27`, `V0`–`V31` and the flags clobbered, `SP`, `R18`, `R28`–`R30` and every byte the contract does not write kept; returns to `X30` | the contracts carry the Phase 1 assumptions above; the ABI is Go's `ABIInternal` for arm64 (`cmd/compile/internal/abi`, `internal/abi`); every allocatable register is caller-saved there. Agreement with native: `mach-difftest`, 9,480/9,480 calls | a runtime routine that keeps a value in a clobbered register the caller relies on, writes memory its contract does not, or changes `R28`/`SP`; a proof that depends on the fixed `garbage` values (they stand for arbitrary values) | trusted (no theorem uses it yet) |
| hook `morestackHook` (`runtime.morestack`, `runtime.morestack_noctxt`) | the stack grows in place (`δ = 0`): `stackguard0` lowered by `growBy`, not below `stack.lo + StackGuard`; resumes after the `BL` with `X30` = the saved `R3`, `SP`, `R26`, `R28`, `R29` kept, the rest clobbered; stuck when the stack cannot grow | `runtime/asm_arm64.s` `morestack` → `newstack` → `gogo`; a moved stack (`δ ≠ 0`) is outside the model (semantics3 §6, §10) | a run that needs a stack move (`copystack`) to agree with native | trusted |
| hook `wbHook` (`runtime.gcWriteBarrier<n>`) | returns the write-barrier buffer (`8n` bytes at `RtInfo.wbuf`) in `R25`; `R27` and the flags clobbered, every other register kept | `runtime/asm_arm64.s` `gcWriteBarrier`; Phase 1's `WbPre` protocol (row above) | a buffer flush that changes other registers or memory the code reads | trusted |
| hook `panicBoundsHook` (`runtime.panicBounds`) | panics with `.bounds kind x y` decoded from the caller's `PCDATA_PanicBounds` at `X30 − 1` (`pcvalue`, `abi.BoundsDecode`), `x`/`y` from `R0`–`R15` or constants | `runtime/panic.go:211-236` `panicBounds64`, `internal/abi` `BoundsDecode` | a runtime whose decoding differs | trusted |
| `runMach` nil page (`GoFV/SSA/Sem/RunMach.lean`) | a load or store in `[0, 4096)` is `panicked nilDeref`; no other address faults | the kernel leaves the nil page unmapped; SIGSEGV there becomes `sigpanic` → `panicmem` | an access fault outside the nil page that the code relies on | trusted |
| `GoFV.Arm64` single core | exclusive stores always succeed, barriers advance the PC | one goroutine, one core, as Phase 2 §8 | a multi-threaded observation | trusted |
| `CallOK`/`CallSpec` (Phase 3 G2 and G3, `GoFV/Proof/Gen/G2.lean`, premise of `g2_value` and `g3_value` at each static call) | from the state at the callee's symbol (the caller's but for `X30`, the return address), with the call's arguments in their ABI registers and the memory injected, the hook `H.call` returns to `X30` with `SP`, `R28`, `R29` and the frame (saved `LR`/`FP`, spill slots: `StkAt`) kept, `runLoc`'s memory after the call injected by an extension of `ι` that keeps the live blocks away from the frame, and `runLoc`'s results in the ABI result registers | the callee's Phase 1 contract lifted through ABIInternal (semantics3 §6, the `liftContract` row above); Go's calling convention keeps `R28`/`R29`/`SP` and the caller's frame | a callee that writes the caller's frame or spill slots, returns elsewhere, or whose results differ from `runLoc`'s | trusted; the witness `genG2_value_witness` discharges it for a callee that returns at once |
| not modelled by the hooks | the defer machinery (`deferproc*`, `deferreturn`, `gorecover`), runtime entry points called through function values, asynchronous preemption, the collector: a run reaching them is `stuck` | sound: a stuck run carries no obligation | — (a restriction) | — |

Not assumed, by decision: disjointness of parameter slots from the other frame slots (the
`not disjoint` class above stays open), and type-based aliasing (#111).

Besides `VPre`, the theorems rest on the semantics itself (`GoFV.SSA.Sem`, its documented gaps in
`docs/plans/semantics.md` §10) and on the exporter (`docs/contracts/export.md`). Axioms: `propext`,
`Classical.choice`, `Quot.sound` and the `_native` axioms of `scripts/axioms-allowlist.txt`
(`scripts/axioms-audit.sh`); no `sorry`.

## Commands

- Fully verified: `scripts/memcap.sh lake exe gofv-ssa-opt --check --verified --jobs 6
  <corpus>/full-v6/plain`.
- Checked passes at stock, `BLOCKED` classes and the `fire-full` table of `rules.md`:
  `scripts/rule-proofs.py fire <corpus>/full-v6/plain -j 6` (runs `rule-fire-probe` and
  `opt-proven-probe`, about 25 minutes).
- Rule counts: `scripts/rule-proofs.py table` (the `classes` and `coverage` tables of `rules.md`).
