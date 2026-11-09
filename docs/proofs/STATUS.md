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
Measured with `gofv-ssa-opt --check --verified`: full-v9 on main 3b3d4ba0 (`--jobs 6`, after
#540 constant `Phi`s and `IMake` of `StructMake`, #558 symbol-address comparisons and `IData`
selections, #559 `ifaceeq`/`efaceeq` folds, #572 struct-store fields of either word shape, #573
`Phi`s of `Not`s; 96,560 functions, format 5.1, 628 min on a heavily loaded machine); quick-v7 on
main 51ef75c1 (6 min):

| Measure | full-v9 through `rewrite tern` (Phase 1) | full-v9 through `trim` | quick-v7 Phase 1 | quick-v7 through `trim` |
| --- | --: | --: | --: | --: |
| Functions fully verified | 93,571 (91883690: 93,475; 06aa0962: 92,925) | 79,216 (91883690: 78,876; 06aa0962: 77,952) | 8,885 | 6,383 |
| … verified (vacuous: unmodelled op): the input has an op or block kind `run` leaves stuck (`TailLECall*`, `RetJmp`) | 1,576 | 1,568 | 168 | 168 |
| … relying on `NilPtrsOK` (a `schedule` swap through `nilPtrSwap`) | – | 3,014 (91883690: 2,983) | – | – |
| … and identical to stock after `trim` | 74,651 (74,595) | 66,546 (66,331) | 7,233 | 5,699 |

The pointer window rule and `ARM64.rules:1183`/`1184` (#385, § Assumptions), measured against
main fa54a58a with `--jobs 4`: full-v9 through `rewrite tern` 93,475 on both, through `trim`
79,148 → 80,392 (identical to stock 66,495 → 67,041; only `lower`'s proven runs change, 80,718 →
82,086), checked lower at stock (`lower-probe`) 83,523 → 84,876 with no function lost.

Every pass from `lower` to `trim` has a theorem (addressing modes `addressingModes_refinesL`,
late lower `lateLower_refinesL`, pair `pair_refinesL`, flagalloc `flagalloc_refinesSched`).
`regalloc` now accepts all 96,560 full-v9 runs (`tabsAgreeModL` takes the new spill autos that
rejected 21,197 runs before). Of the 14,355 full-v9 functions verified through Phase 1 but not
through `trim` (91883690: 14,599), the first unverified run is `lower` for 13,805 (checked variant
incomplete 11,481, rejected 2,324), `schedule` (rejected) 393, `late lower` (rejected) 152,
`lowered deadcode` (rejected) 5 (91883690: `schedule` 389; #530: 1,019; 51ef75c1: 3,365). On
91883690 the 718 rejected `schedule` runs (389 first unverified) were all in deferred classes: a
nil check of a pointer-shaped value the source computes after the faulting value (483 / 303), of
a value that is not pointer-shaped (215 / 77), of an `argPtr` piece after it (2 / 2), and
`LoweredMove` before a load on another memory (18 / 7). The Phase 1 functions not verified
through `rewrite tern` (2,989; 91883690: 3,085), by first unverified run: opt 1,804, late opt
635, middle opt 373, divmod 47, decompose builtin 42 (116), decompose user 59, expand calls 28,
opt deadcode 1.
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

## Phase 3: genssa, slice G7 (I7, #553)

`GoFV.Proof.Gen.g7_value`, `GoFV.Proof.Gen.g7_term`, `GoFV.Proof.Gen.g7_nilPanic`
(`GoFV/Proof/Gen/G7.lean`): when slice G7 (`checkG7`: G6 with the nil checks `LoweredNilCheck p
mem`, no home, `p` in a 64-bit register `Rp`, emitted `MOVB (Rp), R27`) accepts a function,
`g7_value` and `g7_term` are `g6_value`'s and `g6_term`'s statements (a nil check that does not
panic changes only `X27`, which `LocMatch` leaves free, and the PC), and a nil check whose
`runLoc` step panics panics with `nilDeref`, and `runProg` steps reach its `MOVB`, which faults in
the nil page: `PPanics` (`GoFV/Proof/Gen/Progs7.lean`, `runProg`'s panic as `MPanics` is
`runMach`'s; `PPanics.runProg`). Premises (`docs/plans/proofs3.md` §4): G6's, with `G7Pre`
(`G4Pre`, and `NilPre`: a nil-checked pointer outside the nil block points to a byte of a live
block) for values. Witnesses `genG7_value_witness` and `genG7_panic_witness` (`(*A).g` of
`test/method`, which G6 rejects: the receiver's nil check, on a pointer to a global and on nil,
where `runProg` panics). Coverage on quick-v10 (`lake exe gen-check`): 2,109 of 9,297 functions
(22.68%), 26,795 values.

## Phase 3: genssa, slice G8 (I7, #553)

`GoFV.Proof.Gen.g8_value`, `GoFV.Proof.Gen.g8_term`, `GoFV.Proof.Gen.g8_nilPanic`
(`GoFV/Proof/Gen/G8.lean`): when slice G8 (`checkG8`: G7 with the write-barrier requests
`LoweredWB [n] mem`, `1 ≤ n ≤ 8`, homed in `(R25, -)`, emitted `CALL runtime.gcWriteBarrier<n>(SB)`,
and their `Select0` in `R25` and `Select1`, no code) accepts a function, `g8_value`, `g8_term` and
`g8_nilPanic` are `g7_value`'s, `g7_term`'s and `g7_nilPanic`'s statements under the activation
`G8Env` (`G6Env`, and a function with a write barrier has a frame: the `CALL` overwrites `X30`).
Premises (`docs/plans/proofs3.md` §4): G7's, and at a write barrier the trusted hook contract
`WbOK` (§ Assumptions): the request's `runLoc` step (`wbOp`: a fresh buffer block, the op's
clobbers) is matched by the `CALL` and the hook, the injection extended by the buffer. Witness
`genG8_value_witness` (`sync_runtime_registerPoolCleanup` of std/runtime, which G7 rejects: the
request `LoweredWB [2]`, its `Select0` and `Select1`, under a hook that is `wbHook` with the buffer
at `2^41`). Coverage on quick-v10 (`lake exe gen-check`): 2,323 of 9,297 functions (24.98%),
39,922 values.

## Phase 3: genssa, slice G9 (I7, #553)

`GoFV.Proof.Gen.g9_value`, `GoFV.Proof.Gen.g9_term`, `GoFV.Proof.Gen.g9_nilPanic`
(`GoFV/Proof/Gen/G9.lean`): when slice G9 (`checkG9`: G8 with the static calls whose distinct
result registers hold values of other classes elsewhere in the function; G2's function-wide
`resultReg` dropped, the class table follows each register) accepts a function, they are
`g8_value`'s, `g8_term`'s and `g8_nilPanic`'s statements (premises unchanged: `G8Env`, `G3Inv`,
`G7Pre`, `CallOK`, `WbOK`). Witness `genG9_value_witness` (`runtime.fint64to32`, which G8 rejects:
the call `CALL runtime.fintto32(SB)` whose result register `R0` held the 64-bit argument, under a
callee that returns 7 in `R0`, then its result and memory). Coverage on quick-v10 (`lake exe
gen-check`): 2,551 of 9,297 functions (27.43%), 44,756 values.

## Phase 3: genssa, slice G10 (I7, #553)

`GoFV.Proof.Gen.g10_value`, `GoFV.Proof.Gen.g10_term`, `GoFV.Proof.Gen.g10_nilPanic`
(`GoFV/Proof/Gen/G10.lean`): when slice G10 (`checkG10`: G9 with the interface and closure calls
`CALLinter`/`CALLclosure`, their code pointer in a register `Rn`, the closure context in `R26`,
register arguments and results as a static call's, emitted as `CALL (Rn)`; their `SelectN`s and
`results` homes) accepts a function, they are `g9_value`'s, `g9_term`'s and `g9_nilPanic`'s
statements under `G10Env` (`G8Env`, and no interface or closure call in a frameless function),
`g10_value` with the trusted indirect callee contract `ICallOK` next to `CallOK` and `WbOK`.
Witness `genG10_value_witness` (`sync.Locker.Lock`, which G9 rejects: the interface call
`CALL (R2)` through the code pointer of a global function, under a callee that returns at once,
then its memory). Coverage on quick-v10 (`lake exe gen-check`): 3,149 of 9,297 functions (33.87%),
52,418 values.

## Phase 3: genssa, slice G11 (I7, #553)

`GoFV.Proof.Gen.g11_value`, `GoFV.Proof.Gen.g11_term`, `GoFV.Proof.Gen.g11_nilPanic`
(`GoFV/Proof/Gen/G11.lean`): when slice G11 (`checkG11`: G10 with `LoweredGetClosurePtr`, no
argument, homed in `R26` at a 64-bit shape, placed in the entry block after the register arguments
only, `cloFirst`; no code) accepts a function, they are `g10_value`'s, `g10_term`'s and
`g10_nilPanic`'s statements (under `G10Env`), `g11_value` with the trusted premise `CloOK` (`X26`
holds the closure context) next to `CallOK`, `ICallOK` and `WbOK`. Witness `genG11_value_witness`
(`adder.func1` of `examples/closures`, which G10 rejects: the closure pointer `v7` from the entry
of a closure call whose context, a pointer to a global, is in `X26`). Coverage on quick-v10
(`lake exe gen-check`): 3,514 of 9,297 functions (37.79%), 59,565 values.

## Phase 3: genssa, slice G12 (I7, #553)

`GoFV.Proof.Gen.g12_value`, `GoFV.Proof.Gen.g12_term`, `GoFV.Proof.Gen.g12_nilPanic`
(`GoFV/Proof/Gen/G12.lean`): when slice G12 (`checkG12`: G11 with `Convert x mem`, the argument
and the value in one register of class 64, the memory last; no code) accepts a function, they are
`g11_value`'s, `g11_term`'s and `g11_nilPanic`'s statements (under `G10Env`, with the premises
`CallOK`, `ICallOK`, `WbOK` and `CloOK`); no new premise. Witness `genG12_value_witness`
(`runtime.subtractb`, which G11 rejects: `uintptr(unsafe.Pointer(p))` of a pointer 16 bytes into
the heap object `heap 1`, `R0` then holding its Phase 1 address `2^41 + 16`, the machine word).
Coverage on quick-v10 (`lake exe gen-check`): 3,679 of 9,297 functions (39.57%), 64,013 values.
## Phase 3: the assembler, `checkObj` (I7, #553)

`GoFV.Proof.Obj.obj_star` (`GoFV/Proof/Obj/Sim.lean`): when `checkObj` (`GoFV/Asm/CheckObj.lean`,
proofs3 §7) accepts a function's P0 Progs against the assembler's text and relocations, and the
linker model (`linkCode`) places the text at `base` (`ObjEnv`), every `runProg` run of the Progs
(`PStar` under `Link.byId` with the validated frame) is matched by a `runMach` run of the linked
words (`MStar`). The relation `ObjRel f` holds between the two: registers but `X27`/`X30` equal,
`X30` and the PC through the address map `f` (a P0 Prog's address ↦ its words), `SP`, `V`, flags
and memory equal.

The pieces:
- `obj_step`;
- `progSym_sound` (`Prog.lean`: one lemma per Prog family: shifts, ADD-type, compares, `NEG`,
  bitfield extracts, moves/loads/stores/constants/addresses, pairs, branches, `CALL`);
- `symWords_sound` (`Words.lean`, over `symInsn_sound` in `Insn.lean` and the relocated pairs in
  `Link.lean`);
- the validator's checks as propositions (`Spec.lean`).

The prologue and epilogue templates are `obj_entry` (the stack check, through the morestack path
until it passes, then the frame: `BodyEntry`) and `obj_exit` (frame popped, return through the
saved `LR`) (`Frame.lean`). The morestack path (`GoFV/Proof/Obj/Morestack.lean`): `checkTail`
(tightened: the spills `tailPlan` at `off(RSP)` of argument registers `R0`–`R15`, `1`–`8` bytes,
disjoint; before the call `SP` kept and no load; after it `SP` and `R30` kept and only slot loads)
is exposed by `checkObj_tail` and `checkTail_spec`; `symUntil_sound` runs its chunks;
`stackCheck_run` the stack check both ways; `more_loop` iterates round trips through the tail
(spills, `MOVD R30, R3`, the call, the trusted `MorestackOK`, the reloads, the branch back) by
induction on the guard until the check passes, reaching `s0` but for the reloaded registers
(`reloadVal`: the slot's low bytes extended), the other registers but `R26`, `R28`–`R30`, the slots
and the guard word (`MoreStep`).
`g7_obj_value`/`g7_obj_term` (`GoFV/Proof/Obj/G7.lean`) compose `g7_value`/`g7_term` with
`obj_star`: the first statements from `runLoc` to the machine words. They rest on the trusted
premises `HookMap` and `ICallOut` (below; `ICallOut` holds trivially for a function without
`CALL (Rn)`, `iCallOut_of_none`). `obj_panic` carries a P0 panic (a nil-page fault of a Prog, or a
hook that panics) to a machine panic (`MPanics`) under `HookPanicMap`.

Witnesses:
- `objFrame_entry_witness`, `objFrame_exit_witness` (`testInts`, framed with a stack check);
  `objFrame_morestack_witness` (`testInts` entered with `stackguard0` all ones: the check fails,
  the morestack path runs under a hook that clears the guard, `msHook_ok`, and reaches the body);
- `objG7_value_witness` (`(*A).g`'s nil check, down to the linked words);
- `objG7_term_witness` (`pallocSum.start`'s `TBNZ`);
- `objOps_csel_witness`, `objOps_blr_witness`, `objOps_fault_witness`, `objOps_ctl_witness`
  (`GoFV/Proof/Witness/ObjOps.lean`: `CSET` as `CSINC`, `BLR`, a faulting `LDAR`, `CALL (R2)`).

Coverage on quick-v10 (`lake exe obj-check`): 7,741 of 9,297 functions (83.26%; 277,986 of
429,130 P0 Progs in accepted functions), with `CSEL`/`CSINC`/`CSINV`/`CSNEG`/`CSET`/`CSETM`,
`MUL`/`MNEG`/`MADD`/`MSUB`/`UMULH`/`SMULH`, `CLZ`/`RBIT`/`REV*`, `LDAR*`/`STLR*` and `CALL (Rn)`
(was 5,533, 59.51%).

## Phase 3: genssa, slice G13 (I7, #553)

`GoFV.Proof.Gen.g13_value`, `GoFV.Proof.Gen.g13_term`, `GoFV.Proof.Gen.g13_nilPanic`
(`GoFV/Proof/Gen/G13.lean`): when slice G13 (`checkG13`: G12 with `LoweredZero [n] p mem`, `n ≥ 16`,
`p` in a register of class 64; genssa's `zeroTail` stores `STP (ZR, ZR)`/`MOVD ZR` off `p`'s
register, decided per value to lie inside the `n` bytes and cover them) accepts a function, they
are `g12_value`'s, `g12_term`'s and `g12_nilPanic`'s statements (under `G10Env`, with `CallOK`,
`ICallOK`, `WbOK` and `CloOK`); `g13_value`'s per-value premise `G13Pre` adds to `G7Pre` that a
`LoweredZero` writes valid bytes (`ZeroPre`: Phase 1's `Mem.write` of the `n` zero bytes at `p`'s
address succeeds). Witness `genG13_value_witness` (`(*pageBits).clearAll`, which G12 rejects:
`LoweredZero [64]` of the heap object `heap 1` holding 64 bytes 7 at `2^41`, after which the 64
machine bytes there are 0). Coverage on quick-v10 (`lake exe gen-check`): 3,755 of 9,297 functions
(40.38%), 69,470 values.

## Phase 3: genssa, slice G14 (I7, #553)

`GoFV.Proof.Gen.g14_value`, `GoFV.Proof.Gen.g14_term`, `GoFV.Proof.Gen.g14_nilPanic`
(`GoFV/Proof/Gen/G14.lean`): when slice G14 (`checkG14`: G13 with the integer register-index loads
`MOV{D,W,WU,H,HU,B,BU}loadidx`, `MOV{H,HU}loadidx2`, `MOV{W,WU}loadidx4`, `MOVDloadidx8`, base and
index in registers of class 64; genssa's one load from `(Rp)(Ri)` or `(Rp)(Ri<<sh)`) accepts a
function, they are `g13_value`'s, `g13_term`'s and `g13_nilPanic`'s statements (under `G10Env`,
with `CallOK`, `ICallOK`, `WbOK` and `CloOK`); `g14_value`'s per-value premise `G14Pre` adds to
`G13Pre` that a register-index load reads valid bytes (`IdxPre`: Phase 1's `Mem.read` of the `n`
bytes at the address of `ptr + idx · 2^sh` succeeds, and a boolean destination is 0 or 1).
Witness `genG14_value_witness` (`runtime.argv_index`, which G13 rejects: `MOVD (R0)(R1<<3), R0`
with `R0` the start of the heap object `heap 1` at `2^41` and `R1` 2, after which `X0` holds the
word 7 stored at offset 16). Coverage on quick-v10 (`lake exe gen-check`): 3,815 of 9,297
functions (41.03%), 71,548 values.

## Phase 3: genssa, slice G15 (I7, #553)

`GoFV.Proof.Gen.g15_value`, `GoFV.Proof.Gen.g15_term`, `GoFV.Proof.Gen.g15_nilPanic`
(`GoFV/Proof/Gen/G15.lean`): when slice G15 (`checkG15`: G14 with the static calls whose ABI
assigns zero-sized inputs to the stack, checked as G9's on the ABI without them, `callRegsZ`)
accepts a function, they are `g14_value`'s, `g14_term`'s and `g14_nilPanic`'s statements;
`g15_value` adds the trusted premise `CallOKZ` (below) next to `CallOK`. Witness
`genG15_value_witness` (`(*T3).M` of `test/recover`, which G14 rejects: the call of `main.T3.M`
with its empty-struct receiver on the stack, a callee hook returning at once). Coverage on
quick-v10 (`lake exe gen-check`): 3,824 of 9,297 functions (41.13%), 71,645 values.

## Phase 3: genssa, slice G16 (I7, #553)

`GoFV.Proof.Gen.g16_value`, `GoFV.Proof.Gen.g16_term`, `GoFV.Proof.Gen.g16_nilPanic`
(`GoFV/Proof/Gen/G16.lean`): when slice G16 (`checkG16`: G15 with the shifted add `ADDshiftLL`,
emitted `ADD Rm<<k, Rn, Rd`) accepts a function, they are `g15_value`'s, `g15_term`'s and
`g15_nilPanic`'s statements, under the same premises. Witness `genG16_value_witness`
(`spanSetSpinePointer.lookup` of std/runtime, which G15 rejects: `ADD R1<<3, R0, R0` on the start
of `heap 1` and the index 2, after which `X0` holds `2^41 + 16`). Coverage on quick-v10 (`lake exe
gen-check`): 3,874 of 9,297 functions (41.66%), 73,708 values.

## Phase 3: genssa, slice G17 (I7, #553)

`GoFV.Proof.Gen.g17_value`, `GoFV.Proof.Gen.g17_term`, `GoFV.Proof.Gen.g17_nilPanic`
(`GoFV/Proof/Gen/G17.lean`): when slice G17 (`checkG17`: G16 with `GetG`, homed in the `g`
register, no code) accepts a function, they are `g16_value`'s, `g16_term`'s and
`g16_nilPanic`'s statements; `g17_value` adds the premise `GetGOK` on the injection (below).
Witness `genG17_value_witness` (`runtime.getm`, which G16 rejects: `GetG` with `runtime.g` at the
goroutine in `X28`). Coverage on quick-v10 (`lake exe gen-check`): 3,962 of 9,297 functions
(42.61%), 75,809 values.

## Phase 3: genssa, slice G18 (I7, #553)

`GoFV.Proof.Gen.g18_value`, `GoFV.Proof.Gen.g18_term`, `GoFV.Proof.Gen.g18_nilPanic`
(`GoFV/Proof/Gen/G18.lean`): when slice G18 (`checkG18`: G17 with the integer register-index stores
`MOV{D,W,H,B}storeidx` and `MOVHstoreidx2`/`MOVWstoreidx4`/`MOVDstoreidx8`, emitted
`MOV… Rs, (Rp)(Ri<<sh)`) accepts a function, they are `g17_value`'s, `g17_term`'s and
`g17_nilPanic`'s statements, under the same premises (a successful store wrote valid bytes, as
G3's). Witness `genG18_value_witness` (`setpf` of test/ken_array, which G17 rejects:
`MOVD R1, (R0)(R1<<3)` on the start of an 8-byte `heap 1` and the index 0, after which the 8
machine bytes at its address are 0). Coverage on quick-v10 (`lake exe gen-check`): 4,052 of 9,297
functions (43.58%), 80,626 values.

## Phase 3: genssa, slice G19 (I7, #553)

`GoFV.Proof.Gen.g19_value`, `GoFV.Proof.Gen.g19_term`, `GoFV.Proof.Gen.g19_nilPanic`,
`GoFV.Proof.Gen.g19_boundsPanic` (`GoFV/Proof/Gen/G19.lean`): when slice G19 (`checkG19`: G18 with
the bounds panics `LoweredPanicBounds{RR,RC,CR,CC}`, emitted as the `MOVD`s of constants outside
`0..31`, `PCDATA $PCDATA_PanicBounds, $c` and `CALL runtime.panicBounds(SB)`, the `PCDATA` in force
at the `CALL` the `abi.BoundsEncode` of the operands) accepts a function, the first three are
`g18_value`'s, `g18_term`'s and `g18_nilPanic`'s statements under the same premises (a bounds panic
never steps to a state). `g19_boundsPanic`: a bounds panic that `runLoc` runs to the panic `e` is
matched by `runProg` steps to a state where `runProg` panics with `e'`, `BoundsAgree e e'` (equal,
or for a constant index of a signed kind `k` the unsigned kind `k + 1` of the same nonnegative
index, which Go reports with the same message), under the hook contract `BoundsOK` (below). A `CR`
whose constant index is outside `0..31` is rejected (#541: the encoding does not mark it as moved,
so the runtime reports the index 0 or 1; `runtime.markrootSpans`, `recover2.test1`). Witness
`genG19_boundsPanic_witness` (`main.func1` of test/convert4, which G18 rejects: `[9]byte(s)` with
`len(s) = 5` in `R0`, `PCDATA $PCDATA_PanicBounds, $350` and the `CALL`, after which `runProg`
panics with `.bounds 16 9 5`, as `runLoc`). Coverage on quick-v10 (`lake exe gen-check`): 4,221 of
9,297 functions (45.40%), 85,558 values.

## Phase 3: genssa, slice G20 (I7, #553)

`GoFV.Proof.Gen.g20_value`, `GoFV.Proof.Gen.g20_term`, `GoFV.Proof.Gen.g20_nilPanic`,
`GoFV.Proof.Gen.g20_boundsPanic` (`GoFV/Proof/Gen/G20.lean`): when slice G20 (`checkG20`: G19 with
`MOVDnop x`, which emits no code, when the upper-bit table `uAt` before it says `x`'s register
holds the zero or sign extension of `x`'s low bits that `signOf x` names; an entry comes only from
a narrow load (`MOV{B,H,W}{,U}load` of a register address or a global,
`MOV{B,H,W}{,U}loadidx*`) directly before) accepts a function, they are `g19_value`'s,
`g19_term`'s, `g19_nilPanic`'s and `g19_boundsPanic`'s statements under the same premises, and
`g20_value` also takes the upper-bit invariant `UOK m (uAt lc blk i)` (the machine's `X` register
of the table's entry is the extension of its low bits, `ExtOK`) and concludes `UOK m' (uAt lc blk
(i + 1))`. No new trusted premise. Witness `genG20_value_witness` (`runtime.NumCPU`, which G19
rejects: `MOVW runtime.numCPUStartup(SB), R0` with `numCPUStartup = -2`, after which the machine's
`X0` is `0xffff_ffff_ffff_fffe`, and then `MOVDnop`, after which `runLoc`'s `R0` holds the 64-bit
integer `-2`, matched by the machine). Coverage on quick-v10 (`lake exe gen-check`): 4,328 of
9,297 functions (46.55%), 89,297 values.

## Phase 3: genssa, slice G21 (I7, #553)

`GoFV.Proof.Gen.g21_value`, `GoFV.Proof.Gen.g21_term`, `GoFV.Proof.Gen.g21_nilPanic`,
`GoFV.Proof.Gen.g21_boundsPanic` (`GoFV/Proof/Gen/G21.lean`): when slice G21 (`checkG21`: G20 with
`MOVDreg x`, emitted as `Copy` (`MOVD Rx, Rv`, or nothing in one register), when G20's upper-bit
table names `x`'s register before it, `movdOK`) accepts a function, they are `g20_value`'s,
`g20_term`'s, `g20_nilPanic`'s and `g20_boundsPanic`'s statements under the same premises. No new
trusted premise. Witness `genG21_value_witness` (`(*queueOnePass).next` of std/regexp, which G20
rejects: `MOVWU 52(R0), R3` of `q.nextIndex = 0xffff_fffe`, after which the machine's `X3` is its
zero extension, then `MOVD R3, R4`, after which `runLoc`'s `R4` holds the 64-bit integer
`0xffff_fffe` and the machine's `X4` is `0x0000_0000_ffff_fffe`). Coverage on quick-v10
(`lake exe gen-check`): 4,342 of 9,297 functions (46.70%), 89,745 values.

## Phase 3: genssa, slice G22 (I7, #553)

`GoFV.Proof.Gen.g22_value`, `GoFV.Proof.Gen.g22_term`, `GoFV.Proof.Gen.g22_nilPanic`,
`GoFV.Proof.Gen.g22_boundsPanic` (`GoFV/Proof/Gen/G22.lean`): when slice G22 (`checkG22`: G21 with
`LDP sym+off(SB), (Ra, Rb)` and `STP (Rx, Ry), sym+off(SB)`, pair loads and stores of a global)
accepts a function, they are `g21_value`'s, `g21_term`'s, `g21_nilPanic`'s and
`g21_boundsPanic`'s statements under the same premises. No new trusted premise. Witness
`genG22_value_witness` (`runtime.Version`, which G21 rejects: `LDP runtime.buildVersion(SB), (R0,
R1)` with `buildVersion = (nil, 7)`, after which `runLoc`'s `R1` and the machine's `X1` hold 7).
Coverage on quick-v10 (`lake exe gen-check`): 4,472 of 9,297 functions (48.10%), 98,947 values.

## Phase 3: genssa, slice G23 (I7, #553)

`GoFV.Proof.Gen.g23_value`, `GoFV.Proof.Gen.g23_term`, `GoFV.Proof.Gen.g23_nilPanic`,
`GoFV.Proof.Gen.g23_boundsPanic` (`GoFV/Proof/Gen/G23.lean`): when slice G23 (`checkG23`: G22 with
the comparison pseudo-ops `Equal`, `NotEqual`, `LessThan`, …, as `CSET cond, Rd`) accepts a
function, they are `g22_value`'s, `g22_term`'s, `g22_nilPanic`'s and `g22_boundsPanic`'s
statements under the same premises. No new trusted premise. Witness `genG23_value_witness`
(`bytes.shouldUseASCIISet`, which G22 rejects: `CMP $8, R0` with `len(chars) = 10`, then `CSET GT,
R0`, after which `runLoc`'s `R0` holds `true` and the machine's `X0` is 1). Coverage on quick-v10
(`lake exe gen-check`): 4,624 of 9,297 functions (49.73%), 101,638 values.

## Phase 3: genssa, slice G24 (I7, #553)

`GoFV.Proof.Gen.g24_value`, `GoFV.Proof.Gen.g24_term`, `GoFV.Proof.Gen.g24_nilPanic`,
`GoFV.Proof.Gen.g24_boundsPanic` (`GoFV/Proof/Gen/G24.lean`): when slice G24 (`checkG24`: G23 with
`SP` after the entry values, run as a value without code, as `SB` in G3) accepts a function, they
are `g23_value`'s, `g23_term`'s, `g23_nilPanic`'s and `g23_boundsPanic`'s statements under the same
premises, but for `g24_value`'s activation-value premise `entryOp24 v.op = false` (G3's
activation values but `SP`), which `entryOp3 v.op = false` implies (`entryOp24_of_3`). No new
trusted premise. Witness `genG24_value_witness` (`(*SChan).Recv` of `test/closedchan`, which G23
rejects: `SP` at the head of the receiving block, after which `runLoc`'s Go register `SP` holds
`SP`'s value and the related machine state is at the same PC). Coverage on quick-v10 (`lake exe
gen-check`): 4,718 of 9,297 functions (50.74%), 106,958 values.

## Phase 3: genssa, slice G25 (I7, #553)

`GoFV.Proof.Gen.g25_value`, `GoFV.Proof.Gen.g25_term`, `GoFV.Proof.Gen.g25_nilPanic`,
`GoFV.Proof.Gen.g25_boundsPanic` (`GoFV/Proof/Gen/G25.lean`): when slice G25 (`checkG25`: G24 with
the conditional selects `CSEL`/`CSEL0` and the bit tests `TSTconst`/`TSTWconst`) accepts a
function, they are `g24_value`'s, `g24_term`'s, `g24_nilPanic`'s and `g24_boundsPanic`'s
statements under the same premises. No new trusted premise. Witness `genG25_value_witness` (the
struct wrapper of `reflect.flag.ro`, which G24 rejects: `CSEL NE, R1, ZR, R0` with `R1 = 32` after
`CMP $0` on 32, after which `runLoc`'s `R0` holds 32 and the machine's `X0` is 32). Coverage on
quick-v10 (`lake exe gen-check`): 4,925 of 9,297 functions (52.97%), 111,247 values.

## Phase 3: genssa, slice G26 (I7, #553)

`GoFV.Proof.Gen.g26_value`, `GoFV.Proof.Gen.g26_term`, `GoFV.Proof.Gen.g26_nilPanic`,
`GoFV.Proof.Gen.g26_boundsPanic` (`GoFV/Proof/Gen/G26.lean`): when slice G26 (`checkG26`: G25 on a
function with an arm64 op; on one without, which `runLoc` runs in Phase 1's mode, G1's
`MakeResult`, `InlMark` and `Copy` in `Ret` blocks) accepts a function, they are `g25_value`'s,
`g25_term`'s, `g25_nilPanic`'s and `g25_boundsPanic`'s statements under the same premises. No new
trusted premise. Witness `genG26_value_witness` (`main.func1` of examples/generics, which holds no
arm64 op and which G25 rejects: its `Copy`, `MOVD R2, R0`, with `x = 7`, after which `runLoc`'s `R0`
holds 7 and the machine's `X0` is 7). Coverage on quick-v10 (`lake exe gen-check`): 5,172 of 9,297
functions (55.63%), 111,802 values.

## Phase 3: genssa, slice G27 (I7, #553)

`GoFV.Proof.Gen.g27_value`, `GoFV.Proof.Gen.g27_term`, `GoFV.Proof.Gen.g27_nilPanic`,
`GoFV.Proof.Gen.g27_boundsPanic` (`GoFV/Proof/Gen/G27.lean`): when slice G27 (`checkG27`: G26 with
the shifted logic ops `AND`/`ORR`/`EOR`/`BIC Rm SHIFT k, Rn, Rd`, `SHIFT` one of `LSL`, `LSR`,
`ASR`) accepts a function, they are `g26_value`'s, `g26_term`'s, `g26_nilPanic`'s and
`g26_boundsPanic`'s statements under the same premises. No new trusted premise. Witness
`genG27_value_witness` (`regexp.newLazyFlag`, which G26 rejects: `ORR R2<<32, R1, R0` with
`uint32(r2) = 2` in `R1` and `r1 = 1` in `R2`, after which `runLoc`'s `R0` holds `0x100000002` and
the machine's `X0` is `0x100000002`). Coverage on quick-v10 (`lake exe gen-check`): 5,261 of 9,297
functions (56.58%), 117,659 values.

## Phase 3: genssa, slice G28 (I7, #553)

`GoFV.Proof.Gen.g28_value`, `GoFV.Proof.Gen.g28_term`, `GoFV.Proof.Gen.g28_nilPanic`,
`GoFV.Proof.Gen.g28_boundsPanic` (`GoFV/Proof/Gen/G28.lean`): when slice G28 (`checkG28`: G27 with
`LoweredMemEq p q n mem` as `CALL runtime.memequal(SB)`, `p`, `q`, `n` in `R0`, `R1`, `R2` at
class 64, the boolean result in `R0`) accepts a function, they are `g27_value`'s, `g27_term`'s,
`g27_nilPanic`'s and `g27_boundsPanic`'s statements under `G28Env` (`G10Env`, and a function with
`LoweredMemEq` has a frame) and, for values, the new trusted premise `MemEqOK` (the
`runtime.memequal` contract, § Assumptions). Witness `genG28_value_witness`
(`runtime.envKeyEqual`, which G27 rejects: `CALL runtime.memequal(SB)` on two strings of 8 equal
bytes, under a hook that implements `memequal` on the machine, after which `runLoc`'s `R0` holds
`true` and the machine's `X0` is 1). Coverage on quick-v10 (`lake exe gen-check`): 5,332 of 9,297
functions (57.35%), 120,012 values.

## Phase 3: genssa, slice G29 (I7, #553)

`GoFV.Proof.Gen.g29_value`, `GoFV.Proof.Gen.g29_term`, `GoFV.Proof.Gen.g29_nilPanic`,
`GoFV.Proof.Gen.g29_boundsPanic` (`GoFV/Proof/Gen/G29.lean`): when slice G29 (`checkG29`: G28 with
the upper-bit table `uL` of several entries carried across narrow loads, `MOVDnop` and `MOVDreg`
within a block) accepts a function, they are `g28_value`'s, `g28_term`'s, `g28_nilPanic`'s and
`g28_boundsPanic`'s statements under the same premises, except that `g29_value` takes the table's
invariant `UOKL m (uL lc blk i)` in place of `UOK m (uAt lc blk i)` and concludes
`UOKL m' (uL lc blk (i + 1))` (the table is empty at a block's entry). No new trusted premise.
Witness `genG29_value_witness` (`.eq.M1K1M2` of test/genmeth1, which G28 rejects: `MOVDnop` of a
halfword loaded two values earlier, with `0xbeef` in `R1`, after which `runLoc`'s `R1` holds the
32-bit `0xbeef` and the table gives the machine's whole `X1 = 0xbeef`). Coverage on quick-v10
(`lake exe gen-check`): 5,361 of 9,297 functions (57.66%), 121,036 values.

## Phase 3: genssa, slice G30 (I7, #553)

`GoFV.Proof.Gen.g30_value`, `GoFV.Proof.Gen.g30_term`, `GoFV.Proof.Gen.g30_nilPanic`,
`GoFV.Proof.Gen.g30_boundsPanic` (`GoFV/Proof/Gen/G30.lean`): when slice G30 (`checkG30`: G29, and
on a function with no arm64 op G26's `checkNL` that also accepts `Convert` in its argument's
register of class 64) accepts a function, they are `g29_value`'s, `g29_term`'s, `g29_nilPanic`'s
and `g29_boundsPanic`'s statements under the same premises. No new trusted premise. Witness
`genG30_value_witness` (`runtime.gclinkptr.ptr`, which G29 rejects: its `Convert`, no code, in
Phase 1's mode with `p = 0x1234` in `R0`, after which `runLoc`'s `R0` holds `0x1234` and the
machine's `X0` is `0x1234`). Coverage on quick-v10 (`lake exe gen-check`): 5,367 of 9,297
functions (57.72%), 121,060 values.

## Phase 3: genssa, slice G32 (I7, #553)

`GoFV.Proof.Gen.g32_value`, `GoFV.Proof.Gen.g32_term`, `GoFV.Proof.Gen.g32_nilPanic`,
`GoFV.Proof.Gen.g32_boundsPanic` (`GoFV/Proof/Gen/G32.lean`): when slice G32 (`checkG32`: G30 with
the register ops `MUL`, `MNEG`, `AND`, `OR`, `XOR`, `BIC`, `EON`, `ORN`, the constant ops `ORconst`,
`XORconst`, the unary ops `NEG`, `MVN`, `CSINC`, and the store-release ops `STLR`, `STLRW`, `STLRB`
with a value of exactly the access's width) accepts a function, they are `g30_value`'s,
`g30_term`'s, `g30_nilPanic`'s and `g30_boundsPanic`'s statements under the same premises. No new
trusted premise. Witnesses: `genG32_bin_witness` (`OR` in test/armimm `or64`: `ORR R1, R0, R0`,
the machine's `X0` the `OR` of `0x1234` and `0xaa00dd55000066`), `genG32_binK_witness` (`ORconst
[1 << 52]` in `runtime.funpack64`, `X1` the mantissa with bit 52 set), `genG32_un_witness` (`NEG` in
`runtime.(*atomicOffAddr).StoreMarked`, `X1 = 0x1122334455`), `genG32_stlr_witness` (its `STLR R1,
(R0)` into a heap block at `2^41`, whose 8 machine bytes then read `0x1122334455`),
`genG32_csinc_witness` (`CSINC NE, R4, R4, R4` in `internal/bytealg.countGeneric` with equal
flags, `X4` from 5 to 6). Coverage on quick-v10 (`lake exe gen-check`): 5,678 of 9,297 functions
(61.07%), 143,647 values.

## Phase 3: genssa, slice G31 (I7, #553)

`GoFV.Proof.Gen.g31_value`, `GoFV.Proof.Gen.g31_term`, `GoFV.Proof.Gen.g31_nilPanic`,
`GoFV.Proof.Gen.g31_boundsPanic` (`GoFV/Proof/Gen/G31.lean`): when slice G31 (`checkG31`: G32 with
the upper-bit table carried across G1's ops and G3's `CMPW`/`CMPWconst`, which keep the entries of
the registers they do not write, and across blocks, each starting with the entries every
predecessor ends with) accepts a function, they are `g32_value`'s, `g32_term`'s,
`g32_nilPanic`'s and `g32_boundsPanic`'s statements under the same premises, except that
`g31_value` carries `UOKL m (uL31 lc (uIn lc bid) blk i)` to value `i + 1` and `g31_term` takes it
at the block's end and concludes `UOKL m' (uIn lc e.b)` at the successor (`uIn lc entry = []`, so
the premise is trivial at the function's entry). No new trusted premise. Witnesses:
`genG31_value_witness` (`runtime.(*hexdumper).close`, which G32 rejects: `MOVD R4, R2` at the start
of `b3`, whose table comes from `b1`, the machine's whole `X2 = 0x2a`), `genG31_term_witness` (its
`CBZW R5` from `b1` to `b3`, with `UOKL` of `uIn lc 3`, which gives the whole `X5 = 0x2a`). Coverage
on quick-v10 (`lake exe gen-check`): 5,703 of 9,297 functions (61.34%), 145,016 values.

## Phase 3: genssa, slice G33 (I7, #553)

`GoFV.Proof.Gen.g33_value`, `GoFV.Proof.Gen.g33_term`, `GoFV.Proof.Gen.g33_nilPanic`,
`GoFV.Proof.Gen.g33_boundsPanic` (`GoFV/Proof/Gen/G33.lean`): when slice G33 (`checkG33`: G31 with
`CLZ`, `REV` and `SRAconst` of a 64-bit argument, `UBFIZ` of an argument holding the bits it reads,
and `CMNWconst` of an argument of at least 32 bits) accepts a function, they are `g31_value`'s,
`g31_term`'s, `g31_nilPanic`'s and `g31_boundsPanic`'s statements under the same premises. No new
trusted premise. Witnesses: `genG33_un_witness` (`REV R0, R0` in `math/bits.ReverseBytes`, the
machine's `X0 = 0x0807060504030201` from `0x0102030405060708`), `genG33_sra_witness` (`ASR $4, R0,
R1` in `internal/bytealg.Cutover`, `X1 = -16` from `-256`), `genG33_ubfiz_witness` (`UBFIZ $1, R1,
$16, R1` in `runtime.(*mspan).pinnerBitSize`, `X1 = 0x17dde` from the 16-bit `0xbeef`),
`genG33_cmnw_witness` (`CMNW $1, R1` in `runtime.(*_func).isInlined` on `0xffffffff`, the machine's
`Z` set). Coverage on quick-v10 (`lake exe gen-check`): 5,812 of 9,297 functions (62.51%),
151,700 values.

## Phase 3: genssa, slice G34 (I7, #553)

`GoFV.Proof.Gen.g34_value`, `GoFV.Proof.Gen.g34_term`, `GoFV.Proof.Gen.g34_nilPanic`,
`GoFV.Proof.Gen.g34_boundsPanic` (`GoFV/Proof/Gen/G34.lean`): when slice G34 (`checkG34`: G33 with
the upper-bit table `uL34`, which also keeps the entries of the registers a value does not write
across the single-register ops of G3, G16, G23, G25, G32 and G33, spills, reloads and `MOVDaddr`)
accepts a function, they are `g33_value`'s, `g33_term`'s, `g33_nilPanic`'s and
`g33_boundsPanic`'s statements under the same premises, with `uL34 lc (uIn34 lc bid)` and
`uIn34 lc e.b` in place of G31's tables. No new trusted premise. Witness: `genG34_witness`
(`MOVB R1, R2` in `test/atomicload`'s `f`, which G33 rejects: from the byte `0xbe` in `R1`, the
machine's `X2 = 0xffffffffffffffbe`, and G34's table keeps `R1`'s entry, which gives the whole
`X1 = 0xbe`). Coverage on quick-v10 (`lake exe gen-check`): 5,825 of 9,297 functions (62.65%),
152,495 values.

## Phase 3: genssa, slice G35 (I7, #553)

`GoFV.Proof.Gen.g35_value`, `GoFV.Proof.Gen.g35_term`, `GoFV.Proof.Gen.g35_nilPanic`,
`GoFV.Proof.Gen.g35_boundsPanic` (`GoFV/Proof/Gen/G35.lean`): when slice G35 (`checkG35`: G34 with
the upper-bit table `uL35`, which also keeps the entries of the registers other than its home's
across the pair load `LDP` and `Select0`/`Select1` of one, and gives a narrow load of a frame
variable an entry) accepts a function, they are `g34_value`'s, `g34_term`'s, `g34_nilPanic`'s and
`g34_boundsPanic`'s statements under the same premises, with `uL35 lc (uIn35 lc bid)` and
`uIn35 lc e.b` in place of G34's tables. No new trusted premise. Witness: `genG35_witness`
(`Select1` of `LDP instOpNames(SB)` in `regexp/syntax.(*InstOp).String`, which G34 rejects: G35's
table keeps `R2`'s and `R3`'s entries across it, which gives the whole `X2 = 0x2a`). Coverage on
quick-v10 (`lake exe gen-check`): 5,838 of 9,297 functions (62.79%), 152,883 values.

## Phase 3: genssa, slice G36 (I7, #553)

`GoFV.Proof.Gen.g36_value`, `GoFV.Proof.Gen.g36_term`, `GoFV.Proof.Gen.g36_nilPanic`,
`GoFV.Proof.Gen.g36_boundsPanic` (`GoFV/Proof/Gen/G36.lean`): when slice G36 (`checkG36`: G35 with
the register shifts `SLL`, `SRL`, `SRA`, the shifted adds and subtracts `ADDshiftRL`, `ADDshiftRA`,
`SUBshiftLL`, `SUBshiftRL`, `SUBshiftRA`, and `TST` of two 64-bit arguments) accepts a function,
they are `g35_value`'s, `g35_term`'s, `g35_nilPanic`'s and `g35_boundsPanic`'s statements under the
same premises. No new trusted premise. Witness: `genG36_witness` (`ADD R0>>63, R0, R1` in
`encoding/hex.DecodedLen`, which G35 rejects: from `x = -7`, the machine's `X1 = -6`). Coverage on
quick-v10 (`lake exe gen-check`): 5,967 of 9,297 functions (64.18%), 159,085 values.

## Phase 3: genssa, slice G37 (I7, #553)

`GoFV.Proof.Gen.g37_value`, `GoFV.Proof.Gen.g37_term`, `GoFV.Proof.Gen.g37_nilPanic`,
`GoFV.Proof.Gen.g37_boundsPanic` (`GoFV/Proof/Gen/G37.lean`): when slice G37 (`checkG37`: G36 with
the multiplies and divides `UMULH`, `MULH`, `UDIV`, `DIV` of 64-bit arguments and `MULW`, `UDIVW`,
`DIVW`, `UMULL` of arguments of at least 32 bits, the reversals `RBIT`, `REVW`, `REV16W`, the
multiply-adds `MADD`, `MSUB`, `MADDW`, `MSUBW`, and `SBFX`) accepts a function, they are
`g36_value`'s, `g36_term`'s, `g36_nilPanic`'s and `g36_boundsPanic`'s statements under the same
premises. No new trusted premise. Witness: `genG37_witness` (`RBIT R0, R0` in `math/bits.Reverse`,
which G36 rejects: from `x = 0x0f`, the machine's `X0 = 0xf000000000000000`). Coverage on quick-v10
(`lake exe gen-check`): 6,099 of 9,297 functions (65.60%), 165,436 values.

## Phase 3: genssa, slice G38 (I7, #553)

`GoFV.Proof.Gen.g38_value`, `GoFV.Proof.Gen.g38_term`, `GoFV.Proof.Gen.g38_nilPanic`,
`GoFV.Proof.Gen.g38_boundsPanic` (`GoFV/Proof/Gen/G38.lean`): when slice G38 (`checkG38`: G37 with
the acquire loads `LDAR`, `LDARW`, `LDARB` (`LDAR* (Rn), Rd`, homed in `(Rd;-)`) and their
`Select0` (in `Rd`) and `Select1` (the memory), both without code) accepts a function, they are
`g37_value`'s, `g37_term`'s, `g37_nilPanic`'s and `g37_boundsPanic`'s statements; `g38_value`'s
per-value premise `G38Pre` adds to `G14Pre` the run premise `LdarPre` (an acquire load reads valid
bytes: Phase 1's `Mem.read` of its `n` bytes at the address in its register succeeds; a property
of the run, as G3's for the loads, not a trusted hook). No new trusted premise. Witness:
`genG38_witness` (`LDAR (R0), R0` in `sync/atomic.LoadInt64`, which G37 rejects: `LdarPre` holds
for the pointer to the word 7 of a heap object, and the machine's `X0 = 7`). Coverage on quick-v10
(`lake exe gen-check`): 6,380 of 9,297 functions (68.62%), 177,277 values.

## Phase 3: genssa, slice G39 (I7, #553)

`GoFV.Proof.Gen.g39_value`, `GoFV.Proof.Gen.g39_term`, `GoFV.Proof.Gen.g39_nilPanic`,
`GoFV.Proof.Gen.g39_boundsPanic` (`GoFV/Proof/Gen/G39.lean`): when slice G39 (`checkG39 lc`:
`refsLive lc`, every value of the function at an ID that is a value of the function and its
arguments values of the function, then `checkG38` on `liveCtx lc`, `lc` without the homes that
`regalloc` recorded for values `trim` removed) accepts a function, they are `g38_value`'s,
`g38_term`'s, `g38_nilPanic`'s and `g38_boundsPanic`'s statements on `liveCtx lc`.
`GoFV.Proof.Gen.runLoopLoc_live`, `runCtxLoc_live`, `runLoc_live`: under `refsLive`, `runLoc`
runs alike under `lc` and `liveCtx lc`. No new premise. Witness: `genG39_witness`
(`strings.HasSuffix`, which G38 rejects for the home `R0` of the removed `v47`: `ADD R3, R1, R4`
runs alike under both contexts, and the machine's `X4 = 7`). Coverage on quick-v10
(`lake exe gen-check`): 6,447 of 9,297 functions (69.34%), 182,395 values.

## Phase 3: genssa, slice G40 (I7, #553)

`GoFV.Proof.Gen.g40_value`, `g40_term`, `g40_nilPanic`, `g40_boundsPanic`
(`GoFV/Proof/Gen/G40.lean`): when slice G40 (`checkG40`: G39 with, in a function whose values
keep the memory, `memPure`, `InitMem` anywhere and without code) accepts a function, they are
`g39_value`'s, `g39_term`'s, `g39_nilPanic`'s and `g39_boundsPanic`'s statements.
`GoFV.Proof.Gen.g40_initMem`: in such a lowered function, `InitMem` from a state holding the
activation's initial memory (`MemInit s`: `s.mem = .mem s.fr.mem0`) has `g40_value`'s conclusion
(no code, the state unchanged). `MemInit` is no trusted premise: `runLoc`'s first state holds it
and every step keeps it under `memPure` (`GoFV.Proof.Gen.memInit_stepLoc`, `memInit_stepTermLoc`).
Witness: `genG40_witness` (`unicode/utf16.IsSurrogate`, `InitMem` in the return block `b2`, which
G39 rejects; `runLoc` runs it from a state holding the initial memory to one holding it again).
Coverage on quick-v10 (`lake exe gen-check`): 6,472 of 9,297 functions (69.61%), 182,705 values.

## Phase 3: whole functions, and generic SSA to machine words (I7, #553)

`GoFV.Proof.Obj.g35_obj_value`, `g35_obj_term`, `g35_obj_nilPanic`, `g35_obj_boundsPanic`
(`GoFV/Proof/Obj/G35.lean`): `g35_value`/`g35_term`/`g35_nilPanic`/`g35_boundsPanic` composed
with `obj_star` and `obj_panic`, as `g7_obj_value`/`g7_obj_term` for G7, under `G28Env` and G35's
upper-bit table of the P0 state (`UOKL m (uL35 lc (uIn35 lc b) blk i)`; a terminator hands the
successor's start `uIn35 lc e.b` on). A panic is matched by machine steps to a state that
panics (`MPanics`) with `nilDeref`, or with a bounds panic that `BoundsAgree`s with `runLoc`'s.
`GoFV.Proof.Obj.g35_obj_callPanic` (`GoFV/Proof/Obj/CallPanic.lean`): a static call whose callee
panics, under the trusted `CallPanicOK` (§ Assumptions), is matched by machine steps to a state
that panics with the same panic; `g35_obj_icallPanic`: the same for an interface or closure call
(`CALL (Rn)`), under the trusted `ICallPanicOK`. `GoFV.Proof.Obj.g35_obj_memPanic`
(`GoFV/Proof/Obj/MemPanic.lean`): a load (`MOV{D,W,WU,H,HU,B,BU}load`, `LDP`) or store
(`MOV{D,W,H,B}store`, `STP`; `memFaultOp`) whose step panics (`nilFaults`: a nil base, the address
in the nil page) has no symbol and its base in a register holding the machine word 0, so its Prog
faults in the nil page (`nil_fault_page`, `progStep_loadN_nil`, `progStep_ldp_nil`,
`progStep_storeN_nil`, `progStep_stp_nil`): the machine panics with `nilDeref`, no premise. The
register-index loads and stores are excluded: `runLoc` faults on their nil base whatever the
index, the machine only when the index keeps the address in the nil page.

`GoFV.Proof.Obj.obj_whole_ret` (`GoFV/Proof/Obj/Whole.lean`): when `checkG35` and `checkObj` accept
a function and `retRegsOK` its returns, the machine starts at its entry (`MachEntry`, return
address `s0.x 30`; when the stack check fails, the prologue loops through the morestack tail under
`runtime.morestack`'s contract `MorestackOK`, with the spill slots apart from `g`, `TailSep`, and
the entry values surviving the tail, `MoreEntry`: each live register but `R26` reloaded from a
slot it fits, the live blocks apart from the slots and the guard word; `EntryMatch.more`), a run
of `runLoc`'s body (`runLoopLoc` from the
state `s` at the entry block) whose first `k` values (the entry values) lead to a state `sI`
related to the entry machine state (`EntryMatch`: the argument registers, no flags or slots, the
memory injected; `EntryEnv`: the frame, `g`, the caller's `LR`/`FP`; no upper-bit fact carried
into the body: G35's table after the entry values is empty, `uL35 lc [] … k = []`, the entry
block's start being empty, `checkG35_uIn_entry`) and whose every later step meets its premises
(`RunPre`, at the states `runLoc` reaches from `sI`: at a value whose step succeeds `G14Pre`,
`GetGOK` and the trusted `CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK`;
`G1TermPre`; no entry value (`entryOp24`)), and that returns
`(rs, mm)`, is matched by `runMach` of the linked words that returns to `s0.x 30` in a state `t'`
with `MachRet s0 t'` (`SP`, `g`, `R29` as at entry) and `ResultRel E (ownOutRegs lc) rs mm t'`
(`GoFV/Proof/Obj/Results.lean`): `rs` in the function's ABI result registers (`ownOutRegs`: those
of its register-assigned results), `mm` injected; a result the ABI puts on the stack (or a
zero-sized one) is no `MakeResult` argument: `expand calls` stores it to its `PPARAMOUT` variable,
which is in `mm`. `retRegsOK` (`GoFV/Gen/Results.lean`): every `Ret` block's control
is a `MakeResult` whose tuple has one component per argument, the last the memory, each result
homed in its ABI register at a class no wider than the register's (`ret_results`, in both of
`runLoc`'s modes: `valRel_retypeL_le` for lowered functions, `lmode_valRel_le` for those with no
arm64 op). The pieces: the prologue (`sim_entry`, over `obj_entry`), each value (`sim_value`, over
`g35_obj_value`), each terminator (`sim_goto`, over `g35_obj_term`), the return (`sim_ret`: the
`RET` after no-ops, `termG3_ret`, `obj_exit`, `ret_results`), the run by induction on the fuel
(`sim_from_ret`). `checkG35_cx` covers lowered functions and those with no arm64 op (G26). A
leaf (`checkObj`'s `leaf`: no `CALL`), framed or not, returns through `X30`: `SimAt` carries the
caller's return address in the P0 state's `X30` of a leaf, from the prologue (which keeps it)
through every P0 run of a value or terminator (`GoFV.Proof.Obj.obj_star_leaf`,
`leaf_step_x30`, `GoFV/Proof/Obj/Sim.lean`: from a Prog with `X30` outside the Progs and the
end, the run stays at Progs, so no hook runs, and no Prog of a leaf writes `X30`: `sameEffect`,
`progSym_ctl`); a framed leaf's epilogue recomputes `R29` as the caller's `SP - 8`
(`EntryEnv.fp0`).
`runPre_simple`: `RunPre` holds of a function whose ops from the start on are simple
(`simpleFrom`).

`GoFV.Proof.Obj.obj_whole_panic` (`Whole.lean`): `obj_whole_ret`'s premises on the entry and the
steps, the trusted `HookPanicMap` and `BoundsOK`, and the panic premise `RunPanicPre` (at every
state the run reaches, a value whose step panics is a nil check, a load or store of `memFaultOp`, a
bounds check, or a static, interface or closure call whose callee panics as `CallPanicOK` or
`ICallPanicOK` says at every `LocMatch`ed machine state): if the run of `runLoc` panics with `e`,
`runMach` panics with `e'`, `BoundsAgree e e'` (the same panic, or for a bounds check the runtime's
report of the same failure). The pieces: `sim_valuePanic` (over `g35_obj_nilPanic`,
`g35_obj_memPanic`, `g35_obj_boundsPanic`, `g35_obj_callPanic`, `g35_obj_icallPanic`; a call's
or access's `vkind33` is `vkind28`'s, `vkind33_eq28`), `sim_from_panic`; terminators never panic
(`stepTermLoc_ne_panic`).

`GoFV.Proof.Obj.verified_mach` (`GoFV/Proof/Obj/EndToEnd.lean`): `verifiedPipelineFull_refines`
composed with `obj_whole_ret` and `obj_whole_panic`. For `f` through the verified pipeline
(`fullyVerified`) and its output's genssa Progs and assembled words accepted by `checkG35`,
`retRegsOK` and `checkObj`, on every input of `VPre` with the pipeline's premises (`hn`, `ha`,
`hnp`) on which `run` of `f` returns or panics, a `runLoc` of the output refines it
(`OutcomeRefines`), `runLoc` is `finish` of its body's defined outcome (`runLoc_eq`,
`finish_defined`); when the body returns, `runMach` of the linked words returns to the caller with
the results in their registers (`obj_whole_ret`'s conclusion); when it panics and the panic
premises hold, `runMach` panics alike (`obj_whole_panic`'s conclusion). Every premise is in the
statement; the trusted ones are in the table below.

Witnesses:
- `objWhole_ret_witness` (`GoFV/Proof/Witness/ObjWhole.lean`): `pallocSum.start` on `p = 7` in
  `plRunEnv`, from `runLoc`'s first state (`locInit`) to `runMach` returning to the caller's
  `0x40` with 7 in `X0`; it runs `sim_entry`, `sim_goto` (the `TBNZ`), `sim_value` (`ANDconst`,
  `MakeResult`) and `sim_ret`.
- `objWholeNL_ret_witness` (`GoFV/Proof/Witness/ObjWholeNL.lean`): `obj_whole_ret` on
  `runtime.gclinkptr.ptr`, a function with no arm64 op (G26), `ret_results` in Phase 1's mode.
- `objWhole_panic_witness` (`GoFV/Proof/Witness/ObjPanic.lean`): `obj_whole_panic` on `(*A).g` with
  a nil receiver: the nil check's `MOVB` faults in the nil page. `g35_callPanic_witness`:
  `g35_callPanic` (P0) on `fint64to32`'s call, under a hook whose callee panics with `nilDeref`;
  `g35_icallPanic_witness`: `g35_icallPanic` on `Locker.Lock`'s interface call `v11`;
  `g35_storePanic_witness`: `g35_memPanic` on `(*queueOnePass).next`'s `MOVW R2, 52(R0)` with a
  nil `q`, which faults at address 52; `g35_loadPanic_witness`: `g35_memPanic` on its
  `MOVWU 52(R0), R3`.
- `objStarLeaf_witness` (`GoFV/Proof/Witness/ObjG7.lean`): `obj_star_leaf` on `(*A).g`, a leaf:
  the P0 run of its nil check `v6` keeps the caller's `0x40` in `X30`.
- `verified_mach_witness` (`GoFV/Proof/Witness/ObjEndToEnd.lean`): `pallocSum.start` from its
  generic SSA (the export's first section, the whole-file pass environment of
  `gofv-ssa-opt --verified`) through the verified pipeline (`fullyVerified`), with every premise
  of `verified_mach` discharged.

Not yet covered (#553): panics other than nil checks, loads, stores, bounds checks and calls
(register-index loads and stores; write barriers; `memequal`).

### End-to-end coverage (`gofv-ssa-opt --check --verified --e2e`)

The functions `verified_mach`'s function-level premises hold of (#553): the verified pipeline is
`fullyVerified` (as `--check --verified` runs it: driver export environment, type rounds), and on
the pipeline's own output (function and tables) genssa's P0 Progs are accepted by `checkG35`
against `LocCtx.make r.st.tables r.st.func`, `retRegsOK` holds of its class tables, and `checkObj`
accepts `Flushplist`'s output on those same Progs (`GoFVTest/Driver/E2E.lean`,
`docs/DRIVER.md`). Frame (`allocFrame`), Progs and object are the
ports' own; the frame is laid out on the pipeline's own locals (`ownFrame`: the frontend's
declarations, then the autos the pipeline created). From the stock `.prog` file only the driver
input view is read (definitions, config, `Dcl` at `AllocFrame`'s start, `genin`). The stock
column runs the same back end on the stock `trim` function of every function.

| quick-v10 (9,297 functions, 8 min 52 s; `agent/obj8` 2fa1c005, `--jobs 2`) | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 7,676 | 82.56% | - |
| … genssa and `Flushplist` ran | 7,676 | 82.56% | 9,297 |
| … ∧ `checkG34` | 5,435 | 58.45% | 5,825 |
| … ∧ `checkG34` ∧ `retRegsOK` | 5,435 | 58.45% | 5,825 |
| … ∧ `checkObj` | 7,036 | 75.68% | 7,741 |
| … ∧ `checkG34` ∧ `retRegsOK` ∧ `checkObj` | 5,426 | 58.36% | 5,810 |
| **… and no framed leaf (end to end, `verified_mach`)** | **5,424** | **58.34%** | 5,804 |
| … end to end, pipeline output identical to stock after `trim` | 4,673 | 50.26% | - |

The composition on G30 (#630, main e6969584) accepted 5,066 (54.49%); G31's, G33's and G34's
ops and upper-bit tables add 358. `ownFrame` gives the stock `stksize`/`stkptrsize` on all 6,459
fully verified functions whose output is identical to stock. `pallocSum.start` (the witness
`verified_mach_witness`) is among the accepted. Top reasons among the fully verified: `checkG34`:
`store shape` (274), `frame variable off another base` (229), `op LDAR` (194), `op CALLtail`
(164), `argument v# in register #` (141), `frame variable with an integer address` (134), `frame
variable operand class` (133), `op LDARW` (110), `op LoweredAtomicAdd#Variant` (81); `retRegsOK`:
none; `checkObj`: `FLDPQ` (SIMD&FP, 121), unmodelled atomics `LDADDAL`/`CASAL` (≈240 together),
`tail: spill register` (58), shifts by a register (65), `MVN` (27), divisions (36).

The full-v11 table below is the previous measurement (G18 probe, stock locals, main 8c5b1472 plus
PR #606); it is re-measured on the composition on G34.

| full-v11 (96,674 functions, in six parts, ≈5 h 06 min) | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 81,003 | 83.78% | - |
| … genssa and `Flushplist` ran | 73,422 | 75.94% | 96,674 |
| … ∧ `checkG18` | 39,575 | 40.93% | 41,865 |
| … ∧ `checkG18` ∧ `retRegsOK` | 28,813 | 29.80% | 30,586 |
| … ∧ `checkObj` | 69,055 | 71.43% | 84,567 |
| **… ∧ `checkG18` ∧ `retRegsOK` ∧ `checkObj` (end to end)** | **28,813** | **29.80%** | 30,582 |
| … end to end, pipeline output identical to stock after `trim` | 26,048 | 26.94% | - |

full-v11 ran as six invocations (`cmdmain`, `cmd/vendor`, the rest of `cmd` but `compile`,
`cmd/compile`, `stdall/std` in two halves; the single run was lost to a global OOM kill of the
machine after 5 h 41 min, at 2.9 GB RSS) whose tables are summed; `cmd/compile` alone took
4 h 00 min under a load of ≈360 (47 functions over 60 s, `ppc64asm/init` 642 s). Top reasons
among the fully verified: back-end errors `genssa: aux a# is not a Dcl name` (7,542, as above) and
`Flushplist: PosTable.Pos: no position base` (39); `retRegsOK`: a `Ret` block's results not in
their ABI registers (10,749) or a result on the stack (13); `checkObj`: `LDADDALW` (1,169), `FLDPQ`
(1,043), `CASALW` (417), `LSL`/`LSR`/`ASR` by a register (775), `tail: spill register` (275),
`RET` through another register (144), `CASALD` (127). `checkG18` (first reason; lower bounds, each
part lists its top 40): `op LDAR` (3,192), `op LoweredPanicBoundsCC` (3,072), `op MOVDnop`
(2,413), `frame variable operand class` (1,704), `op LoweredPanicBoundsCR` (≥1,524), `SP after
the entry values` (1,488), `op CALLtail` (1,388), `frame variable with an integer address`
(1,264), `pair load shape` (1,239), `op LoweredMemEq` (1,151), `store shape` (1,127).

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

The `decompose user` runs that are unverified (59 on full-v9) are not in `decompose-probe`'s count
of stock inputs outside `decUserFrag` (0 of 96,560): the probe checks the stock section before the
pass, `--verified` the verified pipeline's state. When `early phielim and copyelim` and `early
deadcode` are skipped (outside their fragments, mostly zero-size values), that state still holds
the values the stock passes removed. `decompose-probe` now also runs the pipeline's earlier passes
(`Verified.runPasses`) and checks `decUserFrag` on their result: on full-v9 (main 91883690) 96,495
of 96,560 are in the fragment; the 65 others all follow both early skips, 60 with a dead `Unknown`
value outside `tabsAgreeMod`'s covered ops (`tamOpOK`) and 5 with a `Phi` split whose argument shape
differs from the `Phi`'s (`decPhiCheck`: "new Phi: arg shape ≠ phi shape"). Both classes are in
`--verified`'s 59 (checked on samples); the probe starts from the section-0 tables, without the
driver's added type rounds.

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
| hook `panicBoundsHook` (`runtime.panicBounds`) | panics with `.bounds kind x y` decoded from the caller's `PCDATA_PanicBounds` at `X30 − 1` (`pcvalue`, `abi.BoundsDecode`), `x`/`y` from `R0`–`R15` or constants (`boundsPanic`; the kind `2·code`, `+1` when unsigned, and `BoundsConvert`, code 8, kind 16 = `ssa.BoundsConvert`, `cmd/compile/internal/ssa/op.go`) | `runtime/panic.go:211-236` `panicBounds64`, `internal/abi` `BoundsDecode` | a runtime whose decoding differs | trusted |
| `runMach` nil page (`GoFV/SSA/Sem/RunMach.lean`) | a load or store in `[0, 4096)` is `panicked nilDeref`; no other address faults | the kernel leaves the nil page unmapped; SIGSEGV there becomes `sigpanic` → `panicmem` | an access fault outside the nil page that the code relies on | trusted |
| `GoFV.Arm64` single core | exclusive stores always succeed, barriers advance the PC | one goroutine, one core, as Phase 2 §8 | a multi-threaded observation | trusted |
| `CallOK`/`CallSpec` (Phase 3 G2 and G3, `GoFV/Proof/Gen/G2.lean`, premise of `g2_value` and `g3_value` at each static call) | from the state at the callee's symbol (the caller's but for `X30`, the return address), with the call's arguments in their ABI registers and the memory injected, the hook `H.call` returns to `X30` with `SP`, `R28`, `R29` and the frame (saved `LR`/`FP`, spill slots: `StkAt`) kept, `runLoc`'s memory after the call injected by an extension of `ι` that keeps the live blocks away from the frame, and `runLoc`'s results in the ABI result registers | the callee's Phase 1 contract lifted through ABIInternal (semantics3 §6, the `liftContract` row above); Go's calling convention keeps `R28`/`R29`/`SP` and the caller's frame | a callee that writes the caller's frame or spill slots, returns elsewhere, or whose results differ from `runLoc`'s | trusted; the witness `genG2_value_witness` discharges it for a callee that returns at once |
| `CallOKZ` (Phase 3 G15, `GoFV/Proof/Gen/G15.lean`, premise of `g15_value` at each static call) | `CallOK`'s contract (`CallAt`) at a static call whose ABI, without its zero-sized stack inputs, has the register arguments and results `callRegsZ` gives | as `CallOK`: a zero-sized stack input passes no byte, so the callee's Phase 1 contract lifted through ABIInternal is the same | as `CallOK` | trusted; the witness `genG15_value_witness` discharges it for a callee that returns at once |
| `WbOK`/`WbSpec` (Phase 3 G8, `GoFV/Proof/Gen/G8.lean`, premise of `g8_value` and every later slice's `gN_value` at each write-barrier request `LoweredWB [n]`) | from the state at `runtime.gcWriteBarrier<n>`'s symbol (the caller's but for `X30`), with the memory injected, the hook `H.call` returns to `X30` with `SP`, the memory and every register but `X25` and `X27` kept, `X25` the address of the buffer under an extension of `ι` that maps the block `wbuf` there and injects `runLoc`'s memory with a fresh `8n`-byte buffer (`Mem.wbAlloc`), the live blocks away from the frame | the hook `wbHook` (row above): `runtime/asm_arm64.s` `gcWriteBarrier` returns `8n` bytes of the per-P buffer in `R25`, clobbering only `R27` and the flags; the layout puts the buffer (`RtInfo.wbuf`) apart from the live blocks and the stack | a buffer that overlaps a live block or the frame, or a flush that changes other registers or memory | trusted; the witness `genG8_value_witness` discharges it for a hook that is `wbHook` with the buffer at `2^41` |
| `ICallOK` (Phase 3 G10, `GoFV/Proof/Gen/G10.lean`, premise of `g10_value` and every later slice's `gN_value` at each interface or closure call `CALLinter`/`CALLclosure`) | from every state that is the caller's but for `X30`, with the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), the register arguments in their ABI registers and, at a closure call, `R26` holding the closure context: that address is no Prog address of the caller and not its return address, and the hook there satisfies `CallSpec` (the static callee's contract, the `CallOK` row above) | Go's internal ABI: the code pointer of a method (an itab's `fun` entry) or of a closure (its first word) is the entry of a function linked outside the caller's code, which the hook runs by its Phase 1 contract (`callTarget` names the callee by the code pointer); a closure call passes its context in `R26` (abi-internal.md: the closure context pointer register) | a code pointer into the caller's own code (a recursive call through a function value, which the hook model does not run; lifting this needs the function-level callee contract of `docs/plans/proofs3.md` §6), or a callee that breaks `CallSpec` | trusted; the witness `genG10_value_witness` discharges it for a callee that returns at once at a global function's address |
| `CloOK` (Phase 3 G11, `GoFV/Proof/Gen/G11.lean`, premise of `g11_value` and every later slice's `gN_value` at `LoweredGetClosurePtr`) | at `LoweredGetClosurePtr`, which `checkG11` places in the entry block after the register arguments only (`cloFirst`; no code but the prologue runs before it), `X26` holds the activation's closure context (`fr.closure`, `poison` outside a closure call), a 64-bit word | Go's internal ABI passes the closure context in `R26` (abi-internal.md; semantics3 §5); the prologue does not write `R26` and its `morestack` path saves and restores the context (`runtime.morestack`, `gobuf.ctxt`); the register arguments emit no code | a caller that enters a closure without its context in `R26`, or a prologue that clobbers `R26` | trusted; the witness `genG11_value_witness` discharges it for a closure context that is a pointer to a global at `2^40` |
| `GetGOK` (Phase 3 G17, `GoFV/Proof/Gen/G17.lean`, premise of `g17_value` at `GetG`) | the injection `ι` maps Phase 1's opaque global `runtime.g` (`GetG`'s result, `Sem/Pure.lean`) to the activation's goroutine `E.g`, which `LocMatch`'s frame clause puts in `X28`; `E.Extends` keeps it, so it is a property of the activation's first injection | Phase 1 models the goroutine as an opaque allocation of the environment, never nil (semantics2 §5); on arm64 the goroutine pointer lives in `R28` (`g`), which Go code does not write outside the runtime's `g` switches | a `runtime.g` symbol referenced as a global (then `G2Env.glob` puts it at its link address), or code that switches `g` | a choice of `ι`, not of external code; the witness `genG17_value_witness` takes `ι` with `runtime.g` at `X28` |
| `BoundsOK` (Phase 3 G19, `GoFV/Proof/Gen/G19.lean`, premise of `g19_boundsPanic`, …, `g35_obj_boundsPanic`, `obj_whole_panic` and the panic branch of `verified_mach`) | from every machine state at the symbol of `runtime.panicBounds` whose `X30` is the return address of a `CALL` at index `k` of the Prog list, the hook `H.call` panics with `boundsPanic c` of the state's registers, `c` the `PCDATA_PanicBounds` value in force at that `CALL` (`pbData`) | the hook's contract `panicBoundsHook` (row above): `panicBounds64` decodes the PC-value table at `X30 − 1`, which is `c` | a runtime whose `panicBounds` reads other registers or another table, or a PC-value table that the assembler does not emit as the Prog list says (D7, `checkObj`) | trusted; the witness `genG19_boundsPanic_witness` discharges it for a hook that panics with `boundsPanic 350`, the only value at its `CALL` (`boundsOK_of`) |
| `MemEqOK`/`MemEqSpec` (Phase 3 G28, `GoFV/Proof/Gen/G28.lean`, premise of `g28_value` at each `LoweredMemEq`) | from the state at `runtime.memequal`'s symbol (the caller's but for `X30`), with `X0`, `X1`, `X2` related to the arguments `p`, `q`, `n` `runLoc` reads and the memory injected (distinct keys, the live blocks away from the frame), the hook `H.call` returns to `X30` with `SP`, `R28`, `R29` and the memory kept, and `X0` related to `memEq [p, q, n, mem]`: 1 if the `n` bytes at `p` and at `q` agree, 0 if not (no claim when a read is invalid or reads `poison`) | `runtime.memequal`'s contract: `internal/bytealg/equal_arm64.s` (`NOSPLIT`, `NOFRAME`) compares the `R2` bytes at `R0` and `R1`, writes no memory, and returns with `MOVD $1, R0` or `MOVB ZR, R0` (the whole register 1 or 0); the injection relates `runLoc`'s bytes at `p`, `q` to the machine bytes at their addresses, so equal bytes are equal machine bytes and conversely | a `memequal` that writes memory or `R28`/`R29`, or returns another result | trusted; the witness `genG28_value_witness` discharges it for a hook that implements `memequal` on the machine (`GenG28.Hm`), on 8 equal bytes |
| `HookMap` (Phase 3 `checkObj`, `GoFV/Proof/Obj/Sim.lean`, premise of `obj_step`/`obj_star`, `g7_obj_value`/`g7_obj_term`, `g35_obj_value`/`g35_obj_term`, `obj_whole_ret`, `obj_whole_panic` and `verified_mach`) | a hook (callee, runtime entry) that returns from a P0 state at a symbol, after a call whose return address is a Prog or the end, also returns from every `ObjRel`-related machine state, to a related state at a Prog or the end: it treats the return address `X30` only as an address to return to (P0's ID layout and the machine's byte layout differ only there) and does not read `X27` | the callee's code is outside the function and cannot observe where the caller's words are, except through `X30`, which it only returns to (`RET`); Go code does not read `R27` (REGTMP) across a call | a callee that reads or stores its return address as data (tracebacks, `runtime.Callers`), or reads `X27` | trusted; `hookMap_retLR` discharges it for callees that return through `X30` and change nothing else (the witnesses' `GenG2.H0`) |
| `HookPanicMap` (Phase 3 `checkObj`, `Sim.lean`, premise of `obj_panic`, `g35_obj_nilPanic`/`_memPanic`/`_boundsPanic`/`_callPanic`/`_icallPanic`, `obj_whole_panic` and the panic branch of `verified_mach`) | a hook that panics from a P0 state at a symbol (after a call) panics with the same panic from every `ObjRel`-related machine state | as `HookMap` | as `HookMap` | trusted; `hookPanicMap_H0` (`objWhole_panic_witness`) |
| `CallPanicOK` (Phase 3, `GoFV/Proof/Obj/CallPanic.lean`, premise of `g35_callPanic`/`g35_obj_callPanic`; in `RunPanicPre`, premise of `obj_whole_panic` and the panic branch of `verified_mach`, at each static call whose step panics) | from every machine state at the callee's symbol that is the caller's but for `X30`, with the call's arguments in their ABI registers and the memory injected (`CallOK`'s premises, distinct keys, the live blocks away from the frame), the hook `H.call` panics with the panic `runLoc`'s call step panics with | the callee's Phase 1 contract lifted through ABIInternal (the `liftContract` row above): a callee that panics in Phase 1 on these arguments and memory panics alike on the machine, before returning | a callee whose machine code panics with another value, or returns, where its Phase 1 contract panics | trusted; the witness `g35_callPanic_witness` discharges it for a hook whose callee panics with `nilDeref` (`fint64to32`) |
| `ICallPanicOK` (Phase 3, `GoFV/Proof/Obj/CallPanic.lean`, premise of `g35_icallPanic`/`g35_obj_icallPanic`; in `RunPanicPre`, premise of `obj_whole_panic` and the panic branch of `verified_mach`, at each interface or closure call whose step panics) | from every machine state that is the caller's but for `X30`, with the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), `R26` holding the closure context of a closure call, the remaining register arguments in their ABI registers and the memory injected, the callee's code is no Prog of the caller and not its return address, and the hook there panics with the panic `runLoc`'s call step panics with | as `ICallOK` (the code pointer of a method or closure is a function entry outside the caller) and `CallPanicOK` (the callee's Phase 1 contract lifted through ABIInternal panics alike) | a callee whose machine code panics with another value or returns where its Phase 1 contract panics; a code pointer into the caller | trusted; the witness `g35_icallPanic_witness` discharges it for a hook that panics with `nilDeref` at the callee's code (`Locker.Lock`, `icallPanicOKc`) |
| `ICallOut` (Phase 3 `checkObj`, `Sim.lean`, run premise of `obj_star` (and `obj_step` at the state), `g7_obj_value`/`g7_obj_term`, `g35_obj_*`; as `∀ u, ICallOut L ps u` of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | at a `CALL (Rn)` on the P0 run, the register holds a linked symbol's address (a function value's code word, an itab's `fun` entry is a function entry) | Go's function values and itabs point to function entries (data relocations `R_ADDR`, proofs3 §6) | a function value pointing into the caller's own words or to a non-entry address | trusted per run; `iCallOut_of_none` discharges it for a list without `CALL (Rn)` (the ObjG7, ObjWhole, ObjWholeNL, ObjPanic and ObjEndToEnd witnesses) |
| `MachEntry` (Phase 3, `GoFV/SSA/Sem/RunMach.lean`, `GoFV/Proof/Obj/Frame.lean`; premises of `obj_entry`, `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | the call: PC at the entry, `SP` 16-aligned with room for the frame, `X30` outside the code, `g` above the nil page (its 32 bytes below `2^64`), `R29 = SP − 8` | the caller's side of the ABI (`obj7.go`) | a caller that enters with a misaligned `SP` or a return address in the callee's code | `objFrame_entry_witness`, `objFrame_morestack_witness`, `objWhole_ret_witness`, `objWholeNL_ret_witness`, `objWhole_panic_witness`, `verified_mach_witness` |
| `MorestackOK` (Phase 3, `GoFV/Proof/Obj/Morestack.lean`; premise of `more_loop`, `obj_entry`, `sim_entry`, `obj_whole_ret`, `obj_whole_panic`, `verified_mach`, for a function with a stack check, at the address of the morestack tail's call `tailCall`) | the address has no code and is not the return address; from every state there with the entry's `SP`, `g` and stack bound `0(g)` whose stack check fails (`¬ CheckPasses`), the hook `H.call` returns to `X30` with `X30` set to `R3` (the `MOVD R30, R3` of the tail), `SP`, `R26`, `R28`, `R29` kept, the memory kept but the guard word `gOff(g)`, and the guard lower (the loop's measure) | `runtime.morestack`/`morestack_noctxt` (`morestackHook`: `newstack` grows the stack in place, `stackguard0` lowered by `growBy` down to `stack.lo + StackGuard`, `gogo` resumes after the `BL` with `X30 = R3`); the stack can grow (the floor below the limit); `morestackHook_ok` (`GoFV/Proof/Obj/MorestackHook.lean`) proves the model meets the contract at those entry points for a check of `stackguard0` when `growBy > 0` and `stack.lo + StackGuard` is below the check's limit | a runtime that moves the stack (`δ ≠ 0`, not modelled) or cannot grow it (then the hook is stuck: no obligation); the tail's call to another symbol (the validator does not see symbol names) | `msHook_ok` (`objFrame_morestack_witness`: a hook that clears the guard), `morestackHook_ok`; vacuous (no stack check) in the ObjWhole, ObjWholeNL, ObjPanic and ObjEndToEnd witnesses |
| `TailSep`, `MoreEntry` (Phase 3, `Morestack.lean`, `Whole.lean`; premises of `obj_entry`/`sim_entry` and `obj_whole_ret`, `obj_whole_panic`, `verified_mach`, for a function with a stack check) | the spill slots of the morestack tail (`tailPlan`: `off(SP)` of the entry's `SP`) lie below `2^64` and apart from `g`'s first 32 bytes; every register `runLoc`'s first state holds a value in but `R26` is reloaded by the tail from a slot the value fits (`ValFits`: an integer of at most `8n` bits, a boolean, else `n = 8`), no vector register holds one (the hook clobbers them), and the live blocks of its memory lie apart from the slots and the guard word | ABIInternal's spill area of the register arguments is in the caller's frame, `g` is not on the stack; the spills are those of the arguments (`SpillRegisterArgs`) | a register argument the tail does not spill (the validator spills only general registers, so a function with floating-point arguments and a stack check is rejected) | `tailSep` (`objFrame_entry_witness`, `objFrame_morestack_witness`); vacuous in the whole-function witnesses |
| `EntryMatch`, `EntryEnv` (Phase 3, `GoFV/Proof/Obj/Whole.lean`; premises of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | after the entry values, `runLoc`'s registers (the arguments) are in the entry machine state's registers (none in `R16`, `R17`, `R20`, `R29`), no flags or slots, its memory injected by `ι`; the activation's `SP`, `g`, `LR`, `FP`, `framed` are the entry state's (after the prologue's frame) and the return address is no P0 address | the caller's side of ABIInternal: register arguments in `abi.RegIndex` registers; the caller's memory is the callee's | a caller that passes arguments elsewhere | `objWhole_ret_witness`, `objWholeNL_ret_witness`, `objWhole_panic_witness`, `verified_mach_witness` |
| `RunPre` (Phase 3, `GoFV/Proof/Obj/Whole.lean`; premise of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | at every state `runLoc` reaches: the slices' per-step premises `G14Pre`/`G1TermPre` (not trusted: facts of the run, e.g. a load reads valid bytes), no entry value after the entry (`entryOp24`), `GetGOK`, and the trusted `CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK` (rows above) | as the rows above | as the rows above | `runPre_simple` (functions of simple ops), `objWhole_ret_witness`, `objWhole_panic_witness` |
| not modelled by the hooks | the defer machinery (`deferproc*`, `deferreturn`, `gorecover`), runtime entry points called through function values, asynchronous preemption, the collector: a run reaching them is `stuck` | sound: a stuck run carries no obligation | — (a restriction) | — |

Not assumed, by decision: disjointness of parameter slots from the other frame slots (the
`not disjoint` class above stays open), and type-based aliasing (#111).

Besides `VPre`, the theorems rest on the semantics itself (`GoFV.SSA.Sem`, its documented gaps in
`docs/plans/semantics.md` §10) and on the exporter (`docs/contracts/export.md`). Axioms: `propext`,
`Classical.choice`, `Quot.sound` and the `_native` axioms of `scripts/axioms-allowlist.txt`
(`scripts/axioms-audit.sh`); no `sorry`.

Semantic choices that make values `poison` where Go deems the program invalid are listed with
their justification in the semantics documents. The latest (#385): a pointer outside its
block's address window is no value (`Ptr.word` is `poison`, `Val.hasTy` at the word shapes holds
only `Ptr.held` pointers), and `Ptr.convertible` is exactly the `Ptr.ofAddr` round trip. The new
`poison` cases are exactly pointers outside their allocation, which rule (3) of
[`unsafe.Pointer`](https://pkg.go.dev/unsafe#Pointer) forbids ("the result must continue to
point into the original allocated object"); in-bounds and one-past-the-end pointers stay
defined, since every allocation is smaller than its window (heap allocations at most `2^24 <
2^40` bytes, frame variables below Go's 10 MB stack-variable limit `< 2^24`;
`docs/plans/semantics2.md` §3, "Pointers outside their window"). It makes `ARM64.rules:1183`
and `1184` provable.

## Commands

- Fully verified: `scripts/memcap.sh lake exe gofv-ssa-opt --check --verified --jobs 6
  <corpus>/full-v6/plain`.
- Checked passes at stock, `BLOCKED` classes and the `fire-full` table of `rules.md`:
  `scripts/rule-proofs.py fire <corpus>/full-v6/plain -j 6` (runs `rule-fire-probe` and
  `opt-proven-probe`, about 25 minutes).
- Rule counts: `scripts/rule-proofs.py table` (the `classes` and `coverage` tables of `rules.md`).
