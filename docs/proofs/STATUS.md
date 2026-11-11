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
| mem (memory ops) | 58 | 0 | 54 | 112 |
| call | 12 | 0 | 35 | 47 |
| float | 22 | 0 | 46 | 68 |
| ptr (`ConstString`, `Addr`, `NilCheck`, pointer comparisons) | 12 | 0 | 11 | 23 |
| phi | 5 | 0 | 0 | 5 |
| block | 3 | 0 | 0 | 3 |
| all | 1,393 | 31 | 338 | 1,762 |

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
`RewriteCheck.eqCallOK`, `selMROK`) (#69, Phase1Tail2), the `Phi` of two `Not`s
(`generic.rules:1068`, turned `Not` of a fresh `Phi`) by the validator layer `.pn`
(`RewriteCheck.pnRel`, `GoFV.Proof.PhiNot.pn_refines`) (#69, Phase1Tail4), the length
register of a post-`expand calls` `growslice` call (`:2131`) in the forwarding layer under the
contract `Env.GrowLen` of `:2128` (`RewriteCheck.growPOK`, `LoadFwd.growP_src`) (#69,
Phase1Tail5), and the `Load`s of a `Zero` folded to a zero constant (`:882`–`:902`) in the
forwarding layer (`RewriteCheck.fwdZeroOK`, `LoadFwd.zeroLd_load`) (#69, Phase1Tail5).

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

**Open** (338):

- `P1`/`P2` alternatives without a lemma (192): most never fire on the corpus; those that fire
  are in the `fire-full` table of `rules.md` (sole obstacles by rule).
- `mem` (54) and `ptr` (11): memory and pointer rules inside the model without an effect
  obligation proof: `Load` forwardings of other shapes (`:831–:877`, `:907`, `:912`; the
  integer and `bool` `Load`s of a `Zero` `:882–:902` are proven), `Move` chains and
  `Move`/`Zero` of `Store`s (`:1740–:1942`), dropped writes `:919`/`:924`/`:930`/`:937` (open:
  the `not disjoint` class), the other `EqPtr`/`NeqPtr` of symbol addresses, locals and their
  offsets (`:1649–:1676`; `:1648`/`:1651` are proven), and `ConstString` under
  `config.PtrSize == 4` (`:1013`, `:1017`; never true
  for linux/arm64).
- `float` (46): inside the model (`Sem/Float.lean`, the AArch64 instruction of each op with
  RNE): constant folds of `Add/Sub/Mul/Div/Neg{32,64}F`, `Cvt*` of constants,
  `Ceil/Floor/Trunc/Round/RoundToEven/Sqrt` of constants, `OrB`/`Not` of float comparisons.
- `call` (35): `memequal` folds (`:1395–:1557`; `memequal` has a contract), the `Const32`
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
boolean load 0 or 1) or `G1TermPre`, and at a static call `CallOK`. (`G3Inv`/`CoreInv`: since
slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for
8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's
spill slots; `SlotInv` holds each slot's value at its class, 64 at every 8-byte slot.) Witnesses
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
and memory equal. With it `X27At` (proofs3 §7, "Atomics across Progs"): at a Prog where
`checkObj` relates `X27` (`Tab.ok27`: the Prog before it left `X27` as P0's `R27`, no call in
between, no branch to it), the machine's `X27` is P0's; after a call, the return address names no
such Prog.

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
and `F0`–`F15`, `4` or `8` bytes (`FMOVS`/`FMOVD`, `FSTPS`/`FSTPD`), disjoint; before the call
`SP` kept and no load; after it `SP` and `R30` kept, only slot loads, each reloaded vector
register its slot's load, the others unconstrained) is exposed by `checkObj_tail` and
`checkTail_spec`; `symUntil_sound` runs its chunks; `stackCheck_run` the stack check both ways;
`more_loop` iterates round trips through the tail (spills, `MOVD R30, R3`, the call, the trusted
`MorestackOK`, the reloads, the branch back) by induction on the guard until the check
passes, reaching `s0` but for the reloaded registers (`reloadVal`: the slot's low bytes extended;
`vreloadVal`: a vector register's `S`/`D` bytes zero-extended to 128 bits), the other registers
but `R26` (kept only when the call has a context, `runtime.morestack`; `runtime.morestack_noctxt`
zeroes it, #708), `R28`–`R30`, the vector registers not reloaded, the slots and the guard word
(`MoreStep`).
`g7_obj_value`/`g7_obj_term` (`GoFV/Proof/Obj/G7.lean`) compose `g7_value`/`g7_term` with
`obj_star`: the first statements from `runLoc` to the machine words. They rest on the trusted
premises `HookMap` (strengthened for `X27At`: a hook returns to `X30`, § Assumptions) and
`ICallOut` (below; `ICallOut` holds trivially for a function without `CALL (Rn)`,
`iCallOut_of_none`). `obj_panic` carries a P0 panic (a nil-page fault of a Prog, or a hook that
panics) to a machine panic (`MPanics`) under `HookPanicMap`.

Witnesses:
- `objFrame_entry_witness`, `objFrame_exit_witness` (`testInts`, framed with a stack check);
  `objFrame_morestack_witness` (`testInts` entered with `stackguard0` all ones: the check fails,
  the morestack path runs under a hook that clears the guard, `msHook_ok`, and reaches the body);
  `objMoreF_witness` (`GoFV/Proof/Witness/ObjMoreF.lean`: `math.Tan`, whose tail spills `F0` with
  `FMOVD`, entered with `F0 = π` and a failing check under a hook that also clobbers every vector
  register: `F0` is `π` again at the body), `fvalRel_vreloadVal_witness`;
- `objG7_value_witness` (`(*A).g`'s nil check, down to the linked words);
- `objG7_term_witness` (`pallocSum.start`'s `TBNZ`);
- `objOps_csel_witness`, `objOps_blr_witness`, `objOps_fault_witness`, `objOps_ctl_witness`
  (`GoFV/Proof/Witness/ObjOps.lean`: `CSET` as `CSINC`, `BLR`, a faulting `LDAR`, `CALL (R2)`);
  `objOps_stpq_witness`, `objOps_strq_witness` (`STP Q1, Q2, [SP, #32]` and `STR Q3, [SP, #16]`
  through `symInsn_sound`: the memory after holds all 128 bits of each register; `FSTPQ`/`FMOVQ`
  have the same effect), `objOps_eval128_witness`;
- `objBarrier_dmb_witness` (`GoFV/Proof/Witness/ObjBarrier.lean`: `checkObj` accepts
  `runtime.mallocgcSmallNoscanReuse`, whose `DMB $14` assembles to `.barrier 5 14`; `progSym_sound`
  on that Prog), `objBarrier_prfm_witness` (`PRFM PLDL1KEEP, [X0]` with `X0 = 0` through
  `symInsn_sound`: no fault, memory kept; `PRFM (R0), $0` has the same effect);
- `objAtomic_prog_witness` (`GoFV/Proof/Witness/ObjAtomic.lean`: `checkProg` accepts
  `sync/atomic.AddInt32`'s `LDADDALW`, `LDAXRW` and `STLXRW` against their words, with equal
  Prog and word effects, only `STLXRW` leaving `X27` related; `CASALW R27, (R0), R2` and its word
  have equal effects), `objAtomic_whole_witness` (`checkObj` accepts the whole function, `ok27`
  exactly at its `CBNZ R27`, where `X27At` holds iff the machine's `X27` is P0's),
  `objAtomic_ldadd_run`, `objAtomic_stlxr_run`, `objAtomic_cas_hit`, `objAtomic_cas_miss`
  (`symInsn_sound` on `LDADDAL`, `STLXR` and `CASAL` words, a `CAS` mismatch keeping the memory),
  `objAtomic_rmwEx`;
- `objSbfiz_witness` (`GoFV/Proof/Witness/ObjSbfiz.lean`: `checkObj` accepts
  `runtime.(*stkframe).argBytes`, whose `SBFIZ $3, R0, $32, R0` assembles to
  `SBFM X0, X0, #61, #31`; from `R0 = 0x80000001` the Prog gives `R0 = 0xfffffffc00000008`, the
  negative 32-bit field sign-extended and shifted, and `progSym_sound` relates the step to the
  Prog's symbolic effect).

**`SBFIZ`.** `SBFIZ $lsb, Rn, $width, Rd` (and `SBFIZW`) is the bitfield move
`SBFM Rd, Rn, #(-lsb mod w), #(width - 1)` (`Ex.mkBfm sf 0`; `sbfiz_bfm` in `Bitfield.lean`:
P0's `sbfiz`, the low `width` bits sign-extended and shifted left by `lsb`, is that move), next to
`UBFX`/`SBFX`/`UBFIZ` (`fam_ubfx`); the word is the `SBFM` that `SBFX` already decodes to.

Coverage on quick-v10 (`lake exe obj-check`, on P0'): 9,135 of 9,297 functions (98.25%; 396,700 of
429,130 P0 Progs in accepted functions; 9,124 before `SBFIZ`: the 11 functions whose first
rejection was `SBFIZ`, none lost), with `CSEL`/`CSINC`/`CSINV`/`CSNEG`/`CSET`/`CSETM`,
`MUL`/`MNEG`/`MADD`/`MSUB`/`UMULH`/`SMULH`, `CLZ`/`RBIT`/`REV*`, `LDAR*`/`STLR*`, `CALL (Rn)`, the
variable shifts, divisions, `REM`/`UREM`, `BIC`/`ORN`/`EON`/`MVN`, the SIMD&FP forms Go emits
(below), the morestack tail's `F` spills, the float constants loaded from constant symbols,
`DMB $k`/`PRFM 0(Rn), $k` as no-ops (`progSym`'s `DMB`/`PRFM` arms, `symAccess` of a `PRFM` word,
as `execLdSt`) and the atomics (was 8,729, 93.89%, before `X27` across Progs (395 functions, none
lost), 8,703, 93.61%, before `DMB`/`PRFM` (26 of the 31 functions with one; the
other 5 stop at `LDORALB`, `VCNT`, `SBFIZ`), 8,544, 91.90%, before P0' (163 rejections
`PCREL_LDST: access`, 159 now accepted, 4 stopped by a later reason), 8,464, 91.04%, before the
`F` spills (80 rejections `tail: spill register`), 8,263, 88.87%, before the `Q` stores, 7,920,
85.18%, before the integer operations after `MUL`, 7,741, 83.26%, before SIMD&FP, and 5,533,
59.51%, before the opcodes above). `LDAXR*`, `STLXR*`, `CASAL*` and the LSE read-modify-writes
`LDADDAL*`/`LDCLRAL*`/`LDEORAL*`/`LDORAL*`/`SWPAL*` are modelled per Prog (`exclOp`, `atomOp`;
co-simulation: 19 forms, 4,864 cases, 0 mismatches); the Progs that read `R27` set by the Prog
before them (`CBNZ R27` after `STLXR …, R27`, `CASAL R27`, `LDCLRAL R27`) are compared with
`X27` related (`Tab.ok27`, `X27At`): of the 407 functions that stopped at such a Prog, 395 are
accepted and 12 stop at a later Prog (`GETCALLERPC` 3, a `JMP`'s branch offset 4, `VCNT` 2,
`UMULL` 1, `SBFIZ` 1, a `TBZ`'s branch offset 1).

**SIMD&FP.** `Sym` carries the vector registers written (`Sym.v`, 128-bit values `VEx` over the
state before the Prog: `.v r`, constants, `.ofX` of a general register, loads `.ld n a`, `fp1Op`,
`fp2Op` (`Rn`, `Rm` order), `fp3Op`, `FCSEL` on the flags before the Prog, `SCVTF`/`UCVTF`), `Ex`
reads the low `S`/`D` part of a vector register (`Ex.vlo`, the value of an `FMOV` to a general
register and of an `S`/`D` store) and `FCVTZS`/`FCVTZU` (`Ex.fcvtz`), and the flags an `FCMP`
(`Fl.fcmp`). `HoldsCore.v` states the machine's vector registers as `Sym.evalV`, `sameEffect`
compares `V0`–`V31`, and the templates (prologue, epilogue, stack check) write none. Modelled on
both sides (`symInsn` for `exec`, `progSym` for `progEffect`, soundness `symInsn_sound` and
`progSym_sound` per family): `FMOVS`/`FMOVD`/`FMOVQ` loads (every address form, write-back) and
stores, moves between vector registers, from and to a general register (`FMOV ZR` is the constant
0, `VEx.mkOfX`) and of an encodable constant (`FMOV $c`, `fmovImm`); `FLDPS`/`FLDPD`/`FLDPQ`,
`FSTPS`/`FSTPD`/`FSTPQ`; `FADD`/`FSUB`/`FMUL`/`FDIV`/`FMAX`/`FMIN`/`FNMUL`, `FNEG`/`FABS`/
`FSQRT`/`FRINT*`, `FCVTSD`/`FCVTDS`, `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB`, `FCMP`/`FCMPE` (also with
`$(0.0)`), `FCSEL`, `FCVTZS`/`FCVTZU` and `SCVTF`/`UCVTF` (`S`/`D`, `W`/`X`). A store's value is
`vStoreEx` of the register: its `S`/`D` part (`Ex.vlo`) or, for a `Q` store, the whole register
(`Ex.vq`, whose 64-bit `eval` is the low half); `storesMem` and the P0 relation write the low `8 n`
bits of `Ex.eval128` (128 bits: `vq r` all of `V r`, any other value zero-extended;
`Ex.eval128_setWidth`: the same as `eval` for at most 8 bytes). Both `exec` and `progEffect` write
a `Q` register's 16 bytes little-endian at one address with one nil-page check, so a `Q` store is
one 16-byte entry, not two 8-byte ones (`NoNil` would then also require the second half's address
outside the nil page, which neither side checks). A float constant that is not an `FMOV`
immediate: `progedit` loads it from a read-only data symbol `$f64.<bits>`/`$f32.<bits>` (`ADRP` +
`LDR D`/`S` with `R_ARM64_PCREL_LDST64`/`32`, e.g. `math.Ilogb`), not from the text. `checkObj`
runs on P0' (`GoFV.Asm.p0Prime`, `GoFV/Asm/ConstLoad.lean`): P0 with that rewrite (`fconstSym?`,
the symbol numbered as the port's `flush` numbers it), so it compares the load
`FMOVD sym(SB), Fd` (`fmovP`) with the words, whose `R_ARM64_PCREL_LDST*` pair now admits a
SIMD&FP access (`ldstLo?` with `vec`, `symLdstAcc`; proof `decode_ldstLo` for either kind,
`accessBytes_vec`, `symVAccess_exec`, `symVAccess_fault` in `symUnit_sound`/`symUnit_fault`);
`ObjRel` is unchanged. The constant's bytes are the slice's business (G56, below). Not modelled:
`VCNT` (12 functions).

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

## Phase 3: genssa, slice G41 (I7, #553)

`GoFV.Proof.Gen.g41_value`, `g41_initMem`, `g41_term`, `g41_nilPanic`, `g41_boundsPanic`
(`GoFV/Proof/Gen/G41.lean`): when slice G41 (`checkG41`: G40 with the compares `CMNconst`
(`CMN $k, Rn`), `CMPshiftLL` and `CMPshiftRL` (`CMP Rm SHIFT k, Rn`) of 64-bit arguments, of the
flags shape, without home or temporary) accepts a function, they are `g40_value`'s,
`g40_initMem`'s, `g40_term`'s, `g40_nilPanic`'s and `g40_boundsPanic`'s statements; `g41_value`'s
per-value premise `G41Pre` adds to `G38Pre` the run premise `CmpPre` (the first argument of a G41
compare is no pointer without an integer form, G1's `NoBarePtr`, as G1's premise for
`CMP`/`CMPconst`: on such a pointer Phase 1 gives `Z` clear, which the machine does not compute).
`CmpPre` is a property of the run state, checkable on it, not a trusted hook. No new trusted
premise. Witness: `genG41_witness` (`CMN $1, R0` in `runtime.traceNextGen`, which G40 rejects:
`CmpPre` holds for `gen = -1`, an integer, `runLoc` runs it to flags with `Z` set, and the
machine's `Z` is set). Coverage on quick-v10 (`lake exe gen-check`): 6,570 of 9,297 functions
(70.66%), 192,225 values.

## Phase 3: genssa, slice G42 (I7, #553)

`GoFV.Proof.Gen.g42_value`, `g42_initMem`, `g42_term`, `g42_nilPanic`, `g42_boundsPanic`
(`GoFV/Proof/Gen/G42.lean`): when slice G42 (`checkG42`: G41 with `ANDconst [k] x` whose result
class exceeds the class `ca` of `x` when `0 ≤ k < 2^ca`, `AND $k, Rn, Rd`) accepts a function, they
are `g41_value`'s, `g41_initMem`'s, `g41_term`'s, `g41_nilPanic`'s and `g41_boundsPanic`'s
statements, with G41's per-value premise `G41Pre`. No new premise: the mask clears every bit of
`x`'s register above the known low `ca` bits (`GoFV.Proof.Gen.lo_andW`). Witness: `genG42_witness`
(`AND $192, R0, R1` in `unicode/utf8.RuneStart`, the byte `b` masked at type `uint32`, which G41
rejects: from `b = 0xc5` with ones above the low byte of `X0`, the low 32 bits of the machine's
`X1` are `0xc0`). Coverage on quick-v10 (`lake exe gen-check`): 6,609 of 9,297 functions
(71.08%), 194,759 values.

## Phase 3: genssa, slice G43 (I7, #553)

`GoFV.Proof.Gen.g43_value`, `g43_term`, `g43_nilPanic`, `g43_boundsPanic`
(`GoFV/Proof/Gen/G43.lean`): when slice G43 (`checkG43`: G42 with `InitMem` at clean positions
also in a function that calls or stores) accepts a function, they are `g42_value`'s, `g42_term`'s,
`g42_nilPanic`'s and `g42_boundsPanic`'s statements. `GoFV.Proof.Gen.g43_initMem`: `InitMem` from a
state holding the activation's initial memory (`MemInit`) has `g42_value`'s conclusion (no code,
the state unchanged), without G40's `memPure`. `MemInit` is no trusted premise: the check accepts
`InitMem` only at clean positions (`cleanAt`: a block of `cleanBlocks`, closed backwards by
`cleanOK`, with the values before it keeping the memory; `GoFV.Gen.Check.vkind43_initMem`,
`initMemClean_spec`), and the run carries `cleanAt → MemInit` from its first state
(`GoFV.Proof.Gen.memInit_clean_step`, `memInit_clean_term`). Witness: `genG43_witness`
(`runtime.(*debugLogWriter).varint`, `InitMem` in the return block before a call, which G42
rejects). Coverage on quick-v10 (`lake exe gen-check`): 6,622 of 9,297 functions (71.22%), 195,711
values.

## Phase 3: genssa, slice G44, float moves (I7, #553)

`GoFV.Proof.Gen.g44_value`, `g44_initMem`, `g44_term`, `g44_nilPanic`, `g44_boundsPanic`
(`GoFV/Proof/Gen/G44.lean`): when slice G44 (`checkG44`: G43 with float values in the V registers:
`Copy` between `F` registers, `FMOVS`/`FMOVDload` and `store`, `FMOVS`/`FMOVDgpfp`, `fpgp` and
`const`) accepts a function, they are G43's statements, `g44_value` under `G44Pre := G41Pre ∧
FLoadPre`. `FLoadPre` is a run premise (no trusted hook): a float load reads valid bytes, and they
are no pointer without an integer form at the float's shape. Witness: `genG44_witness`
(`math.Float64frombits`, `FMOVD R0, F0`, which G43 rejects). Coverage on quick-v10 (`lake exe
gen-check`): 6,652 of 9,297 functions (71.54%), 196,069 values.

## Phase 3: genssa, slice G45, register-index float loads and stores (I7, #553)

`GoFV.Proof.Gen.g45_value`, `g45_initMem`, `g45_term`, `g45_nilPanic`, `g45_boundsPanic`
(`GoFV/Proof/Gen/G45.lean`): when slice G45 (`checkG45`: G44 with `FMOV{S,D}loadidx{,4,8}` and
`FMOV{S,D}storeidx{,4,8}`, one `FMOVS`/`FMOVD` from or to `(Rp)(Ri<<sh)`) accepts a function,
they are G44's statements, `g45_value` under `G45Pre := G44Pre ∧ FIdxPre`. `FIdxPre` is a run
premise (no trusted hook): a float register-index load reads valid bytes, and they are no pointer
at the float's shape. Witness: `genG45_witness` (`sort.Float64Slice.Swap`, `FMOVD (R0)(R3<<3),
F0`, which G44 rejects). Coverage on quick-v10 (`lake exe gen-check`): 6,657 of 9,297 functions
(71.60%), 196,234 values.

## Phase 3: genssa, slice G46, float arithmetic, conversions and compares (I7, #553)

`GoFV.Proof.Gen.g46_value`, `g46_initMem`, `g46_term`, `g46_nilPanic`, `g46_boundsPanic`
(`GoFV/Proof/Gen/G46.lean`, value lemmas `GoFV/Proof/Gen/FArith.lean`): when slice G46
(`checkG46`: G45 with `FADD`/`FSUB`/`FMUL`/`FDIV`, `FNEG`/`FABS`/`FSQRT`, `FCVTSD`/`FCVTDS`,
`SCVTF`/`UCVTF`, `FCVTZS`/`FCVTZU`, `FCMP` and `FCMP $(0.0)`, the fused `FMADD`/`FNMSUB`; the
`FLT`/`FLE`/`FGT`/`FGE`/`LTnoov`/`GEnoov` blocks through `condBr`) accepts a function, they are
G45's statements, `g46_value` under `G46Pre := G45Pre ∧ FArithPre`. `FArithPre` is a run premise
(no trusted hook) that excludes the NaN operands on which Phase 1's result is not the machine's:
an `FADD`/`FMUL` of two NaNs of one kind that Phase 1's `FOps.ordered` swaps (`FNaNSwap`), an
`FMADD`/`FNMSUB` whose multiplicands are NaNs of one kind (`FSameNaN`). `FMSUB`/`FNMADD` are not
accepted: Phase 1 negates the other multiplicand than the machine (a NaN's sign differs). Witness:
`genG46_witness` (`sq.area`, `FMULD F0, F0, F0` of `1.5`, which G45 rejects). Coverage on
quick-v10 (`lake exe gen-check`): 6,775 of 9,297 functions (72.87%), 202,352 values.

## Phase 3: genssa, slice G47, calls with float arguments or results (I7, #553)

`GoFV.Proof.Gen.g47_value`, `g47_initMem`, `g47_term`, `g47_nilPanic`, `g47_boundsPanic`
(`GoFV/Proof/Gen/G47.lean`): when slice G47 (`checkG47`: G46 with the static, interface and
closure calls whose ABI registers are in `R0`–`R15` or `F0`–`F15`, an argument or result in an `F`
register at a float shape, and the selects of such a call's results in `F` registers) accepts a
function, they are G46's statements, `g47_value` under G46's `G46Pre`. No new premise, trusted or
not: the callee contracts `CallOKZ` and `ICallOK` already relate the V registers (`CallSpec`,
`RegRel`); `g2_callAt` and `g10_icall` take ABI registers in `F0`–`F15`, read from their V
registers. Witness: `genG47_witness` (`math.Sin`, `CALL math.sin(SB)` with `x = 1.5` in `F0`,
which G46 rejects, and a callee that returns its argument). Coverage on quick-v10 (`lake exe
gen-check`): 6,856 of 9,297 functions (73.74%), 204,468 values.

## Phase 3: genssa, slice G50, the narrow and float pair loads (I7, #553)

`GoFV.Proof.Gen.g50_value`, `g50_initMem`, `g50_term`, `g50_nilPanic`, `g50_boundsPanic`
(`GoFV/Proof/Gen/G50.lean`): when slice G50 (`checkG50`: G47 with the pair loads `LDPW` and
`LDPSW` into two X registers, `FLDPD` and `FLDPS` into two V registers, each at a 64-bit register
plus the offset, and the selects of their components; G48 and G49 are reserved) accepts a
function, they are G47's statements, `g50_value` under `G50Pre := G46Pre ∧ PairPre50`. New run
premise `PairPre50`: a pair load reads valid bytes at both of its addresses (`pairAddr`, as G4's
`G4Pre` for `LDP`) and, for `FLDPD`/`FLDPS`, what it reads at each component shape is no pointer
(as `FLoadPre`: a pointer has no V register form). Witness: `genG50_witness`
(`runtime.c128equal`, `FLDPD (R0), (F0, F1)` of `1.5 + 2.5i`, which G47 rejects). Coverage on
quick-v10 (`lake exe gen-check`): 6,911 of 9,297 functions (74.33%), 206,743 values.

## Phase 3: genssa, slice G51, cheap single-instruction ops (I7, #553)

`GoFV.Proof.Gen.g51_value`, `g51_initMem`, `g51_term`, `g51_nilPanic`, `g51_boundsPanic`
(`GoFV/Proof/Gen/G51.lean`): when slice G51 (`checkG51`: G50 with `CSNEG`, `TSTW`, `CMN`, `CMNW`,
`CMPshiftRA`; `MVNshiftLL`/`RL`/`RA`, `SBFIZ`, `RORconst`, `RORWconst`, `ROR`, `RORW`; and
`ADD`, `SUB`, `ADDconst`, `SUBconst`, `ADDshiftLL` and the shifted adds, subtracts and logic ops
with a boolean argument) accepts a function, they are G50's statements, `g51_value` under
`G51Pre := G50Pre ∧ Pre51a`. New run premise `Pre51a`: the first argument of a `CMN` or
`CMPshiftRA`, and the second of a `CMN`, is no pointer without an integer form (as G41's
`CmpPre`). Witness: `genG51_witness` (`math/bits.RotateLeft64`, `ROR R1, R0, R0`, which G50
rejects). Coverage on quick-v10 (`lake exe gen-check`): 6,982 of 9,297 functions (75.09%),
212,374 values.

## Phase 3: genssa, slice G49, frame variables in `Blk.local` blocks (I7, #553)

`GoFV.Proof.Gen.g49_value`, `g49_initMem`, `g49_term`, `g49_nilPanic`, `g49_boundsPanic`
(`GoFV/Proof/Gen/G49.lean`): when slice G49 (`checkG49`: G51 with G6's accesses, `MOVDaddr`, the
loads and stores of G3, `LDP` and `STP`, of a frame variable whose block is `Blk.local`: a
parameter or result at its `NAME_PARAM` operand, or a `PAUTO` whose address the function converts
to an integer at its `NAME_AUTO` operand; frame check `checkVars49`: windows inside the locals or
the argument area, disjoint within an operand class and from its home slots) accepts a function,
they are G51's statements, `g49_value` under `G51Pre`, all under the activation `G49Env :=
G28Env ∧ VarsAt49`. New activation premise `VarsAt49`: the injection puts the `local` block of
each accessed such variable at its operand, `E.ι (.local act x) = some (E.sp + frameOff L nc
o)`. Composed into `verified_mach` (§ whole functions below): at entry, the `local` block of a
register parameter whose address is taken is not related by `MemInj` until genssa's entry store,
so `EntryMatch` leaves its window out and the entry stores run before the full relation
(`docs/plans/proofs3.md` §8 item 8, §9). Witness: `genG49_witness` (`runtime.getm`'s ABI0 wrapper,
`MOVD R0, ~r0+0(FP)`, which G51 rejects; at `Addrs.fixed`). Coverage on quick-v10 (`lake exe
gen-check`): 7,142 of 9,297 functions (76.82%), 220,164 values.

**Vacuous at `Addrs.fixed` for two or more `Blk.local` variables** (#553). The statements hold for
every address assignment (`Addrs`), but their premise `G49Env` puts every accessed `Blk.local`
variable's block at `SP + frameOff` (`VarsAt49`), and `AddrAgree` (in `G2Env`) puts a `local`
block with an address at its base. At `Addrs.fixed` (`Blk.fixedBase?`) block `k` of activation
`a` is at `2^62 + a·2^42 + k·2^24`: two `local` blocks of one activation are a multiple of `2^24`
apart, so two variables at distinct operands of one frame cannot both be at `SP + frameOff`. A
function that accesses two or more has no `G49Env` at `Addrs.fixed` (`g49Env_fixed_apart`,
`GoFV/Proof/Gen/G49Mach.lean`): there `g49_value` … `g49_boundsPanic`, and G52's, G53's, G54's,
G55's and G57's statements (all under `G49Env`), hold of it only vacuously; in G48's mode (an
activation whose `outargs` block sits at `SP`, `SPInv`) `SP` is `outargs 0`'s fixed base `2^62`
there, so a function that accesses any `local` variable has none (`g49Env_fixed_outSP`, witness
`fixed_outSP_none`). At `Addrs.atSP base` (an `Addrs` instance, every class law proven:
activation 0's `local` blocks at `base k`, undecoded, their fixed region decoded as activation
`actM = 2^22`, which `Ptr.fixedOfAddr` never decodes; everything else as `Addrs.fixed`; the machine
instance of `docs/plans/proofs3.md` §8 item 4 for activation 0), every `G28Env` at `Addrs.fixed`
of a function of activation 0 gives a `G49Env` (`g49Env_atSP`, with `base = baseSP g L E.sp`, the
variables' frame operands, and the activation `envAtSP g L E`), so the statements hold of these
functions non-vacuously there; `verified_mach_atSP` (§ whole functions) is the end-to-end statement
at that layout. `Addrs.atSPO base osp` also puts activation 0's `outargs` block at `osp` (G48's
mode; `g49Env_atSPO` for `envAtSPO g L E`, whose `outargs` block is at `SP`, `envAtSPO_out`;
`verified_mach_S_atSP`); both are `Addrs.atSPM`. Witness
`genG49Mach_witness` (`runtime.secret_getStack`'s ABI0 wrapper, results `~r0`/`~r1` at
`NAME_PARAM` 0 and 8): no `G49Env` at `Addrs.fixed`, one at `Addrs.atSP` with the results at
`SP + 24` and `SP + 32`. On quick-v10 (stock functions, `liveCtx`, main 55116073, a
throwaway count beside `gen-check`), 21 of the functions `checkG49` accepts access two or more
(the same 21 are accepted by G52 through G57, and G57 adds none): `main.safeDiv` (`examples/defers`;
`NAME_AUTO` -40 and -42, two address-converted autos), `(*HashTrieMap[…]).CompareAndSwap` in
`encoding/binary` and in `sync`, `fmt.(*ss).Token`, `fmt.(*ss).doScan`, `regexp/syntax.dumpProg`,
`runtime.bytes`, `runtime.cgoCheckPointer`, the ABI0 wrappers `runtime.plugin_lastmoduleinit` (4
stack results), `reflect_compiledTypelinks`, `reflect_typelinks`, `runtime_pprof_readProfile`,
`secret_getStack`, `time_now`, `time_runtimeNow`, `sync/atomic.(*Value).CompareAndSwap`,
`(*Value).Swap`, `main.cmp` (`test/bigmap`; `NAME_PARAM` 0 and 1000), `main.main` (`test/ddd`),
`main.func5` and `main.func6` (`test/range4`). Of `checkG57`'s 7,378, 244 access exactly one (an
activation exists at `Addrs.fixed`: `SP` places the variable at its fixed base, as
`genG49_witness`) and 7,113 none. `fandbits` is not among the 21: after `trim` it accesses only
`x` (`FMOVSstore {x}`); `y` stays in a register.

## Phase 3: genssa, slice G52, remainders (I7, #553)

`GoFV.Proof.Gen.g52_value`, `g52_initMem`, `g52_term`, `g52_nilPanic`, `g52_boundsPanic`
(`GoFV/Proof/Gen/G52.lean`): when slice G52 (`checkG52`: G49 with `MOD`, `UMOD`, `MODW`, `UMODW`,
one `REM`/`UREM`/`REMW`/`UREMW` each) accepts a function, they are G49's statements, under
`G49Env`, `g52_value` under G51's `G51Pre` (no new premise: a register without an integer form
gives Phase 1 `poison`). Witness: `genG52_witness` (`test/ken_chan`'s `main.nrand`,
`REM R0, R1, R0` of `-17` by `5`, which G49 rejects). Coverage on quick-v10 (`lake exe
gen-check`): 7,163 of 9,297 functions (77.04%), 221,257 values.

## Phase 3: genssa, slice G53, `LoweredMove` (I7, #553)

`GoFV.Proof.Gen.g53_value`, `g53_initMem`, `g53_term`, `g53_nilPanic`, `g53_boundsPanic`
(`GoFV/Proof/Gen/G53.lean`): when slice G53 (`checkG53`: G52 with `LoweredMove [n]`, `n ≥ 16`,
as `moveTail`'s `FLDPQ`/`FSTPQ`, `FMOVQ` and `MOVD` chunks through `V16`, `V17`, `X25`, or nothing
when source and destination share their register) accepts a function, they are G52's statements,
under `G49Env`, `g53_value` under `G53Pre := G51Pre ∧ Pre53a`. New run premise `Pre53a`: the move
reads `n` valid bytes at the source and writes them at the destination, and the two ranges are
equal or disjoint (the machine copies chunk by chunk). Witness: `genG53_witness`
(`runtime.(*cpuStatsAggregate).compute`, an 88-byte move between two heap blocks, which G52
rejects). Coverage on quick-v10 (`lake exe gen-check`): 7,260 of 9,297 functions (78.08%),
227,056 values.

## Phase 3: genssa, slice G54, `LoweredZeroLoop` and `LoweredMoveLoop` (I7, #553)

`GoFV.Proof.Gen.g54_value`, `g54_initMem`, `g54_term`, `g54_nilPanic`, `g54_boundsPanic`
(`GoFV/Proof/Gen/G54.lean`): when slice G54 (`checkG54`: G53 with `LoweredZeroLoop [n]` and
`LoweredMoveLoop [n]`, `n ≥ 64`, as genssa's loop of `n / 64` iterations — `MOVD $n/64, Rc`, four
`STP.P (ZR, ZR)` or two `FLDPQ.P`/`FSTPQ.P` pairs, `SUB $1, Rc`, `CBNZ Rc` to the head — then the
straight-line tail of the `n mod 64` bytes left; `loopOK`: each `CBNZ` branches to the Prog after
its `MOVD`) accepts a function, they are G53's statements, under `G49Env`, `g54_value` under
`G54Pre := G53Pre ∧ Pre54a ∧ Pre54b`. The machine run is an induction over the iterations
(`loop_run`). New run premises `Pre54a` (the zeroing writes `n` bytes at a valid address) and
`Pre54b` (the copy reads and writes `n` valid bytes, and the two ranges are equal or disjoint, as
`Pre53a`). Witness: `genG54_witness` (`runtime.(*consistentHeapStats).unsafeClear`, a 3504-byte
`LoweredZeroLoop` with its temporary as the counter, which G53 rejects). Coverage on quick-v10
(`lake exe gen-check`): 7,308 of 9,297 functions (78.60%), 231,647 values.

## Phase 3: genssa, fall-through over no-ops, all slices (I7, #553)

`Cx.falls` (`GoFV/Gen/Check.lean`), shared by `Cx.two` and `Cx.term`: a block falls through to
the successor laid out next when only no-ops (argument-liveness `PCDATA`, inline-mark `NOP`,
`HINT $0`) lie between its last Prog and the successor's start, bounded by that start. `TwoAt`
and `TermOK.plain` take `FallAt` (`Cx.falls_spec`, `GoFV/Proof/Gen/Spec.lean`); `fall_path`
(`G1.lean`) runs the no-ops by `pstar_noops`. Every `gN_term` statement is unchanged, no new
premise. Coverage on quick-v10 (`lake exe gen-check`): G54 7,322 of 9,297 functions
(78.75%, 14 more: the functions rejected only for `expected JMP`), 232,417 values.

## Phase 3: genssa, slice G55, `VCNT`, `VUADDLV`, the `FRINT` rounds, shifted `NEG`, `CLZW`, `MULL`, `EXTR` (I7, #553)

`GoFV.Proof.Gen.g55_value`, `g55_initMem`, `g55_term`, `g55_nilPanic`, `g55_boundsPanic`
(`GoFV/Proof/Gen/G55.lean`): when slice G55 (`checkG55`: G54 with `VCNT x` as `VCNT Va.B8, Vd.B8`,
`VUADDLV x` as `VUADDLV Va.B8, Vd`, of 64-bit values in V registers, `FRINTN`/`FRINTP`/
`FRINTM`/`FRINTZ`/`FRINTA` `D`/`S` as `op Fa, Fd`, `NEGshift* [k] x` as `NEG Rm SHIFT k, Rd`,
`CLZW x` as `CLZW Rm, Rd`, `MULL x y` as `SMULL Rm, Rn, Rd` and `EXTRconst`/`EXTRWconst [k] x y`
as `EXTR`/`EXTRW $k, Rx, Ry, Rd`) accepts a function, they are G54's statements, under `G49Env`,
`g55_value` under `G54Pre` (no new premise: the rounds' mode is fixed by the opcode on both sides,
a NaN is processed by the same `IEEE.roundInt`, and `FZ = DN = 0` is the standing `FPCR = 0`).
Witnesses: `genG55_witness` (`math/bits.OnesCount`:
`VCNT` then `VUADDLV` of `0x103` give 3 in `V0`, which G54 rejects) and `genG55b_witness`
(`math/bits.LeadingZeros32`: `CLZW` of the 32-bit `0x10000` gives 15 in `X0`). Coverage on quick-v10
(`lake exe gen-check`): 7,331 of 9,297 functions (78.85%), 232,869 values.

## Phase 3: genssa, slice G57 group A, `STPW` and narrow pair loads with an aux (I7, #553)

`GoFV.Proof.Gen.vk57a_step` (`GoFV/Proof/Gen/G57a.lean`): one value `vkind57a`
(`GoFV/Gen/Check57a.lean`, tried after G55's value check) accepts, in `vk55_step`'s form under
`G49Env`: `STPW [off] p x y mem` as `STPW (Rx, Ry), off(Rn)` (sources of at least 32 bits, `ZR`
included; the machine stores their low words) and `LDPW`/`LDPSW` with an aux as `op
sym+off(SB), (Ra, Rb)` of a global or `op off'(RSP), (Ra, Rb)` of a frame variable in a
`Blk.temp` block, into two X registers. No new premise: the loads take G50's `PairPre50` (part of
`G54Pre`), which states valid bytes for every `pairOp50` op with or without an aux. Witnesses:
`genG57a_witness` (`examples/structs/main.grow`: `STPW (R2, R3), 8(R0)` of `0x11223344` and
`0x55`, which G55 rejects; the machine then holds `0x44` at the struct's address plus 8) and
`genG57a2_witness` (`runtime.bootstrapRand`: `LDPW runtime.globalRand+328(SB), (R1, R2)`, which
G55 rejects; `X1`'s low word then holds `0x04030201`).
Composition into `checkG57` and its coverage: the slice G57 entry.

## Phase 3: genssa, slice G57 group B, `DMB`, `PRFM`, float stores to frame variables (I7, #553)

`GoFV.Proof.Gen.vk57b_step` (`GoFV/Proof/Gen/G57b.lean`): one value `vkind57b` accepts (`VK57b`,
`vkind57b_spec`: `DMB $k`, `PRFM 0(Rn), $k`, and `FMOVS`/`FMOVD Fs, off(<nc>)`,
`FSTPS`/`FSTPD (Fa, Fb), off(<nc>)` to a frame variable in a `Blk.local` (G49) or `Blk.temp` (G6)
block), in `vk55_step`'s form under `G49Env`: its Prog runs, the match and `G3Inv` hold after it
under the same activation, and the upper-bit table is empty. No run premise. Composed into
`checkG57` by the slice. `checkObj` models `DMB`/`PRFM` as no-ops (the assembler entry,
`objBarrier_dmb_witness`); the composition (`verified_mach`) is on G64, G57's ops included, but
none of quick-v10's 31 functions with a `DMB` or `PRFM` is end to end (End-to-end coverage). Witnesses:
`genG57b_witness` (`test/gcgort` `main.init.func95.1`: `FSTPS` of `float32(1.5)` into the `temp`
block of `.autotmp_1`, which G55 rejects) and `genG57b2_witness`
(`runtime.mallocgcSmallNoscanReuse`: `DMB $14`, which G55 rejects).

## Phase 3: genssa, slice G57, `STPW`, narrow pair loads with an aux, `DMB`, `PRFM`, float stores to frame variables (I7, #553)

`GoFV.Proof.Gen.g57_value`, `g57_initMem`, `g57_term`, `g57_nilPanic`, `g57_boundsPanic`
(`GoFV/Proof/Gen/G57.lean`): when slice G57 (`checkG57`: G55 with group A's `vkind57a` and then
group B's `vkind57b` tried when G55 rejects a value, `GoFV/Gen/Check57.lean`) accepts a function,
they are G55's statements, under `G49Env`, `g57_value` under `G54Pre` (no new premise: the pair
loads take its `PairPre50` component; `STPW`, `DMB`, `PRFM` and the float stores need none).
Witness: `genG57_witness` (`main.grow`: `checkG55` rejects it and `checkG57` accepts it; `STPW
(R2, R3), 8(R0)` of `0x11223344` and `0x55` leaves `0x44` at the struct's address plus 8). At
`Addrs.fixed`, `g57_value` and the other four hold only vacuously of the 21 accepted functions
that access two or more `Blk.local` frame variables; at `Addrs.atSP` they hold of them
non-vacuously (`g49Env_atSP`, § slice G49). Coverage on quick-v10
(`lake exe gen-check`, with the fall-through over no-ops): 7,378 of 9,297 functions (79.35%,
33 more than G55's 7,345), 235,204 values.

## Phase 3: genssa, slice G56, float constants in read-only symbols (I7, #553)

`GoFV.Proof.Gen.g56_value`, `g56_initMem`, `g56_term`, `g56_nilPanic`, `g56_boundsPanic`
(`GoFV/Proof/Gen/G56.lean`): when slice G56 (`checkG56`, on P0' with the constant symbols in
`G2In.syms`, `GoFV.Asm.p0PrimeSyms`: G55 with `FMOVSconst`/`FMOVDconst` homed by `FMOVS`/`FMOVD
$c, Fd` or by the load `FMOVS`/`FMOVD sym(SB), Fd` of a symbol whose name is a float constant
symbol holding the bits `$c` writes, `constSymA`, `constSymAlloc?`) accepts a function, they are
G55's statements, under `G49Env`, `g56_value` under `G54Pre` (G55 adds none) and the new premise
`RoPre56 g s`: the `LocMatch`ed state's memory has the float constant symbols among the Prog
list's symbols, read-only (`RoMem (constRo (symNames g))`, what `lreach_roMem` gives at every
state of the run from `RoMem (constRo …) (addGlobals env mem)`). The load reads the constant's
bytes at the symbol's linked address (`G2Env.glob`, `ro_byte`, above the nil page by `ro_addr`,
`readMem_fconst`), the bits `FCONST` writes (`g56_fconst`). Witness: `genG56_witness`
(`runtime.float64Inf`: `FMOVDconst [+Inf]`, no `FMOV` immediate, the load of
`$f64.7ff0000000000000`, which `checkG55` rejects on P0'; `V0`'s low word is +Inf's bits after
it). Coverage on quick-v10 (`lake exe gen-check`, G56 on P0'): 7,331 of 9,297 functions (78.85%,
as G55 on P0), 232,869 values, 61 of them loading a float constant. Composed into
`verified_mach` (`RoRun` in `obj_whole_ret`/`obj_whole_panic`, below) on G56 at main e8621cd0
(`Obj/G56.lean`), now through slice G64 (G63, G62, G61, G60, G59 with these float constants,
below; `GoFV/Proof/Obj/G64.lean`).

## Phase 3: genssa, slice G48, stack arguments and stack results (I7, #553)

`GoFV.Proof.Gen.g48_value`, `g48_initMem`, `g48_term`, `g48_nilPanic`, `g48_boundsPanic`
(`GoFV/Proof/Gen/G48.lean`): when slice G48 (`checkG48`, chained on G57: G57 with the static calls
whose ABI assigns inputs or outputs to the stack, checked on the ABI without them, `callRegsS`, and
the stores and loads off `SP` without an aux at `[8, outargsSize)`, `MOV{D,W,H,B}`, `STP`, `STPW`,
`FSTPD`, `FMOV{S,D}`, their base homed in the Go register `SP` (`spBase48`), the function homing
only `SP` values and `Phi`s there (`spHomes48`)) accepts a function, they are G57's statements in
an activation whose `outargs` block sits at `SP` (`hosp : E.outSP = true`, the separation
`SepFromW`), keeping `SPInv`; `g48_value` under `G54Pre` (G57's premise), the `CallOKS` family
and the new trusted contract `CallOKStk` (Assumptions). Witness: `genG48_witness`
(`runtime.exit`'s ABI wrapper, `MOVW R0, 8(RSP)` then a call of the `ABI0` `exit`, which G57
rejects; the store of 7 lands at the machine's `SP + 8`), and `genG48_call_witness` (the `CALL`
itself, stepped by `g48_value` with `CallOKStk` discharged for a callee that returns at once). On
quick-v10 no store off `SP` reaches `outargs[0, 8)` (lowest offset 8 in 664 stores). Coverage on
quick-v10 (`lake exe gen-check`): 7,595 of 9,297 functions (81.69%), 242,306 values (+217
functions over G57).

## Phase 3: genssa, slice G58 group A, narrow and boolean operands, wider store-release sources, `LoweredRound*F` (I7, #553)

`GoFV.Proof.Gen.vk58a_step` (`GoFV/Proof/Gen/G58a.lean`): one value `vkind58a`
(`GoFV/Gen/Check58a.lean`, tried after G57's value check) accepts (`VK58a`, `vkind58a_spec`),
in `vk57a_step`'s form under `G49Env` with no run premise and with `hL : UOKL m L` (as
`vk51c_step`: G32's ops keep the upper-bit table's other entries): `REV16W` of a 16-bit argument
for a result of at most 16 bits; `MADDW`/`MSUBW` for a result of class `c ≤ 32` of arguments of
at least `c` bits; G32's register and constant ops, G36's register shifts (as the amount), G33's
`UBFIZ` and G32's `CSINC` with a boolean argument (0 or 1 in the whole register); `STLRW`/`STLRB`
of a source wider than the access (Phase 1's `fitPiece` truncates; `encode_fit58`); and
`LoweredRound32F`/`64F` with no code, the result in the argument's `F` register (`FOps.round` is
the identity). Composition into `checkG58` is the slice's. A probe of G57's check with `vkind58a`
accepts 19 of the 20 functions with one of these sole reasons
(`runtime.checkFinalizersAndCleanups.func1` then fails at a `Phi`'s class). Witnesses:
`genG58a_witness` (`math/bits.ReverseBytes16`: `REV16W` of `0x1234`), `genG58a2_witness`
(`test/copy` `main.u16`: `MSUBW` of a 16-bit divisor), `genG58a3_witness`
(`runtime.(*pinState).set`: `LSL` by the boolean `multipin`), `genG58a4_witness`
(`runtime.(*timers).unlock`: `STLRW` of a 64-bit `int`, `0x88` stored at the address),
`genG58a5_witness` (`test/gcgort` `main.init.func95.1`: `LoweredRound32F` of `float32(1.5)`).

## Phase 3: genssa, slice G58 group B, G35's upper-bit table across more writes (I7, #553)

`GoFV.Gen.Check.uStep35` (`GoFV/Gen/Check35.lean`) follows `LDPW`/`LDPSW` (entries of the
extended words), `LDAR*`, the selects of pair and acquire loads, and the G36 register shifts, G37
ops and `SBFIZ` register by register (`pairOp35`); `GoFV/Proof/Gen/Keep35.lean` (`uStep35_ldp`,
`uStep35_sel`, `uStep35_pairW`, `uStep35_keepOp`, `keepOps35`, `uStep35_keepOps`, `uokl_xw`,
`uokl_one`, `WPairW`, `uokl_wpair`). Every `g*_value` statement from G35 to G57 and G48's is
unchanged; `vk51b_step` and `vk57a_step` take `UOKL m L`. Exercised by `genG57_witness`
(`main.grow`: the table before `STPW` now holds the `LDPSW` words' entries for `R8`, `R9`). 12
functions G57 rejected only for `upper bits unknown` are accepted (proofs3.md §4, slice G58 group
B); they raise G57 to 7,390 and G48 to 7,607.

## Phase 3: genssa, slice G58, narrow and boolean operands, wider store-release sources, `LoweredRound*F`, G35's upper-bit table across more writes (I7, #553)

`GoFV.Proof.Gen.g58_value`, `g58_initMem`, `g58_term`, `g58_nilPanic`, `g58_boundsPanic`
(`GoFV/Proof/Gen/G58.lean`): when slice G58 (`checkG58`: G48, itself on G57, with group A's
`vkind58a` tried when G48 rejects a value, over group B's upper-bit table, and G48's `spHomes48`,
`GoFV/Gen/Check58.lean`) accepts a function, they are G48's statements: in an activation whose
`outargs` block sits at `SP` (`hosp : E.outSP = true`, `SPInv`, kept by `g58_value`,
`g58_initMem`, `g58_term`), under `G49Env`, `g58_value` under `G54Pre`, the contracts of the mode
`E.outSP` and `CallOKStk` (no new premise; group A's values need none). Since the lift to G60
they take either mode `osp`, the mode `true` only for a function that needs G48's mode
(`needs48`, § slice G60). Witness: `genG58_witness`
(`math/bits.ReverseBytes16`: `checkG48` rejects it and `checkG58` accepts it; in the mode `outSP`,
`REV16W R0, R0` of `0x1234` leaves `0x3412` in `X0`'s low halfword, `SPInv` kept). Coverage on
quick-v10 (`lake exe gen-check --jobs 1`, now G58 the last slice): 7,626 of 9,297 functions
(82.02%, 19 more than G48's 7,607, by group A), 245,347 values; no earlier slice's count drops.

## Phase 3: genssa, slice G59 group P, float pair loads of a global or a frame variable (I7, #553)

`GoFV.Proof.Gen.vk59p_step` (`GoFV/Proof/Gen/G59p.lean`): one value `vkind59p`
(`GoFV/Gen/Check59p.lean`, tried after G58's value check) accepts (`VK59p`, `vkind59p_spec`), in
`vk57a_step`'s form under `G49Env` with `hL` and G50's `PairPre50` (no new premise): `FLDPD`/`FLDPS`
with an aux, of a global (`FLDPD sym+off(SB), (Fa, Fb)`, `g59_fldpGlob`) or of a `Blk.temp` frame
variable (`g59_fldpVar`), into two distinct V registers; their selects are G50's. Composition into
`checkG59` is the slice's. A probe of G58's check with `vkind59p` accepts the 6 functions whose sole
reason was `pair load shape` (`test/zerodivide` `main.init.func33`–`func38`). Witness:
`genG59p_witness` (`main.init.func33`: `FLDPD main.d(SB), (F2, F3)` of `complex(1.5, 2.5)` leaves
the bits of `1.5` and `2.5` in `V2`, `V3`; `checkG58` rejects the function).

## Phase 3: genssa, slice G59 group D, `Defer` blocks (I7, #553)

`GoFV.Gen.Check.Cx.term` (`GoFV/Gen/Check.lean`), the terminator check every slice reaches through
`Cx.termG3`/`Cx.termG2`, accepts a `Defer` block (two successors, one control) as `Plain`'s
fall-through or `JMP` to `Succs[0]`: Go's `ssaGenBlock` emits nothing else for it (`case
ssa.BlockPlain, ssa.BlockDefer`), and Phase 1's `stepTerm` goes to successor 0 (the `deferproc`
call returned; a recovery returns through `finish`). `TermOK` (`GoFV/Proof/Gen/Spec.lean`) has a
`defer` field and `branch` takes `b.kind ≠ .Defer`; `Cx.term_spec`, `stepTermL_defer` and
`term_core`'s `Defer` case (`GoFV/Proof/Gen/G1.lean`). Every `g*_term` statement from G1 to G58 is
unchanged. Witness: `genG59d_witness` (`GoFV/Proof/Witness/GenG59d.lean`, `test/defer`
`main.test1helper`: `checkG58` accepts it, and `g58_term` relates `b3`'s `Defer` step to its
`JMP` to `b4`). The 13 functions G58 rejected only for `block kind Defer` are accepted by
`checkG58` (proofs3.md §4, slice G59 group D).

## Phase 3: genssa, slice G59 group K, narrower register classes (I7, #553)

G3's class table (`GoFV/Gen/Check.lean` `kNarrow`, `GoFV/Gen/Check3.lean` `kLe`, `kJoin`, `kMeet`,
`kPhis`, `kPass`) now holds a class a register's content can be read at: the same class, an
integer class of at least 8 bits no wider than an integer or pointer content, or any integer class
over a boolean. `CoreInv`/`G1Inv` give `GoFV.Proof.Gen.FitsW` (`Rel.lean`), read by
`valRel_retypeLW`, `valRel_retypeW`, `fvalRel_retypeLW`; edges by `kLe_spec`, `checkK_spec` and
`CoreInv.monoW` (`KLeW`) in `termK_stepX`. Every `gN_*`/`gNL_*` statement is unchanged, no new
premise. Witness `genG59k_witness` (`GenG59k.lean`, `math.lz`: `checkG58` accepts it with `R0` at 64
bits at `b5`'s end and 32 at `b3`'s start; `g58_term` runs `b5`'s jump from `0xffffffff00000045` in
`R0`, and `arg_rel` relates `v27`'s 32-bit read `0x45` to `X0`). The 8 functions G58 rejected only
for `a register read at another class` (7) or `control read at another class` (1) are accepted
(proofs3.md §4, slice G59 group K).

## Phase 3: genssa, slice G59 group U, G35's upper-bit table across narrow stores, shifted logic ops, `Convert`, boolean loads and `Copy` (I7, #553)

`GoFV.Gen.Check.pairOp35` (`GoFV/Gen/Check35.lean`) also follows narrow stores through a register,
G27's shifted logic ops, `Convert` and narrow loads with no entry, and `uStep35` gives a register
`Copy` its source's entry (`copyStep35`); `GoFV/Proof/Gen/Keep35.lean` (`uStep35_copy`,
`uokl_keepOps`, `uokl_xw35`, `st_uokl`, `extOK_zero`, `uokl_copyKeep`, `uokl_copyMov`,
`g2_copySame`, `g2_copyMov`, `vk33_keep35`'s new cases); `g3_store`, `g6_store`, `g49_store`,
`g12_conv`, `g27_logSh`, `g51c_logSh` conclude `XW`. Every `g*_value` statement from G35 to G58 is
unchanged, with no new premise. Witness: `GoFV.Proof.Witness.GenG59u.genG59u_witness`
(`runtime.(*scavChunkData).pack`: `checkG58` accepts it; across `ORshiftLL` the table keeps `R2`'s
word entry, which G34's step dropped, and after `g58_value`'s run of the `ORR` `X2` is still a
zero-extended word). The 13 functions G58 rejected only for `upper bits unknown` are accepted
(proofs3.md §4, slice G59 group U).

## Phase 3: genssa, slice G59, float pair loads of a global or a frame variable, `Defer` blocks, narrower register classes, G35's upper-bit table across stores, shifted logic ops, `Convert` and `Copy` (I7, #553)

`GoFV.Proof.Gen.g59_value`, `g59_initMem`, `g59_term`, `g59_nilPanic`, `g59_boundsPanic`
(`GoFV/Proof/Gen/G59.lean`): when slice G59 (`checkG59`: G58, on G48, on G57, with group P's
`vkind59p` tried when G58 rejects a value, over the shared checks groups D, K and U change, and
G48's `spHomes48`, `GoFV/Gen/Check59.lean`) accepts a function, they are G58's statements: in an
activation whose `outargs` block sits at `SP` (`hosp : E.outSP = true`, `SPInv`, kept), under
`G49Env`, `g59_value` under `G54Pre`, the contracts of the mode `E.outSP` and `CallOKStk` (no new
premise: group P's loads take its `PairPre50` component); since the lift to G60 at either mode, as
G58's. Witness: `genG59_witness`
(`test/zerodivide` `main.init.func33`: `checkG58` rejects it and `checkG59` accepts it; in the
mode `outSP`, `FLDPD main.d(SB), (F2, F3)` of `complex(1.5, 2.5)` leaves the bits of `1.5` and
`2.5` in `V2`, `V3`). Coverage on quick-v10 (`lake exe gen-check --jobs 1`, G59 the last slice):
7,667 of 9,297 functions (82.46%, 41 more than G58's 7,626: 6 by group P, 35 by D, K and U),
249,111 values; no earlier slice's count drops (G58 itself now 7,661, G48 7,641).

## Phase 3: genssa, slice G60, G59 with G56's float constants (I7, #553)

`GoFV.Proof.Gen.g60_value`, `g60_initMem`, `g60_term`, `g60_nilPanic`, `g60_boundsPanic`
(`GoFV/Proof/Gen/G60.lean`): G57–G59 are stacked on G55, not on G56; `checkG60` (on P0', with the
constant symbols in `G2In.syms`, `GoFV/Gen/Check60.lean`) is G59 with G56's float constants
(`vkind56a`, tried before G59's kinds as `vkind56` tries it before G55's), with G48's `spHomes48`.
When it accepts a function, they are G59's statements, under `G49Env`, `g60_value` under
`G54Pre` and G56's `RoPre56` (`vk60_step`: G59's values by `vk59_step`, the float constants by
`g56_fconst`), at either mode `osp` (`G3Inv … osp`, the contracts of the mode), per function: the
mode `true` (the activation's `outargs` block at `SP`, `hosp`, `SPInv` kept, `CallOKStk`) is needed
only by a function with one of G48's own kinds (`needs48`, checked: `take48`, a static call with
stack arguments or results, an access off `SP`; `hn48 : needs48 lc = true → osp = true`), every
other function runs at the mode `false`, `SepFrom` and the contracts `CallOK` …, as G57 and before
(`vk48_stepM`: at the mode `false` G48's call is one on `callRegsZ`, `CallOKZ`'s contract, and
`g2_callAt` runs it in either mode). G58's and G59's theorems (`g58_value` … `g59_term`) take the
mode the same way. `vkind60_eq48`: on an op of none of G56's (`op56`), G58's
(`op58a`) and G59's (`op59p`) groups `vkind60` is `vkind48`, so off G52–G59's groups what it
accepts `vkind49` or G48's `kind48` accepts (`vkind60_ok49`: what the composition's accesses, calls
and entry stores read). Witness: `genG60_witness` (`math.sqrt`:
`FMOVDconst [MaxFloat64]` in `F1`, the load of `$f64.7fefffffffffffff` on P0'; `checkG59` rejects
the function (the load), `checkG56` rejects it (`v96`'s `SLL` of a narrow argument, G58's), and
`checkG60` accepts it; at G48's mode, `V1`'s low word is `math.MaxFloat64`'s bits after it).
Coverage on quick-v10 (`lake exe gen-check --jobs 2`, G60 on P0', `agent/lift60b` on main 70f8f2ec): 7,667
of 9,297 functions (82.46%, as G59 on P0), 249,111 values, 69 of them loading a float constant
from a constant symbol (61 by G56). Composed into `verified_mach` through slice G64
(`GoFV/Proof/Obj/G64.lean`, `g64_obj_*`, below).

## Phase 3: genssa, slice G61, the atomic read-modify-writes (I7, #553)

`GoFV.Proof.Gen.g61_value`, `g61_initMem`, `g61_term`, `g61_nilPanic`, `g61_boundsPanic`
(`GoFV/Proof/Gen/G61.lean`): `checkG61` (on P0', `GoFV/Gen/Check61.lean`) is G60 with group A
(`vkind61a`, `GoFV/Gen/Check61a.lean`, tried before G60's kinds): the lowered atomic
exchanges, adds, compare-and-swaps, ands and ors (`LoweredAtomic*`), both genssa's
load-exclusive/store-exclusive loops and the LSE `*Variant` forms, and their `Select0`/`Select1`;
and `atomOK`, on the whole function: each loop's `CBNZ R27` branches to its `LDAXR`, each
compare-and-swap's `BNE` to its `CSET`. Off group A's ops (`op61a`) `vkind61` is `vkind60`
(`vkind61_eq60`); of an atomic it accepts what `vkind61a` accepts (`vkind61_atom`, which the
atomics' panic reads). When it accepts a function, they are G60's statements at
either mode `osp`, with G60's premises and no new one (`vk61_step`: G60's values by `vk60_step`,
group A by `vk61a_step`, `GoFV/Proof/Gen/G61e.lean`, from the case lemmas `g61_xchg`, `g61_add`,
`g61_logic`, `g61_cas`, `g61_lse`, `g61_casV` and G38's components, each closed by `atom_finish`).
The loops run once: on one core a store-exclusive succeeds and leaves `R27 = 0` (`GoFV.Arm64`'s
single-core row, Assumptions; nothing else is assumed). **Run premises: none added** (unlike G38's
`LdarPre`): `g61_value` takes exactly `g60_value`'s premises, because a successful `stepLoc` of an
atomic already gives an aligned location whose bytes it read and wrote (`Atomic.rmw`/`Atomic.cas`
are `stuck` otherwise; `stepLoc_rmw61`, `stepLoc_cas61`), and `addr_rel` then gives its machine
address, outside the nil page. An atomic's own nil fault (`nilFaults`, a `.panic` outcome) is
covered by the composition (`g61_obj_atomPanic`, below). Witness: `genG61_witness`
(`sync/atomic.SwapInt64` on P0', mode `false`: `checkG60`
rejects it, `checkG61` accepts it; `LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27` from `addr`
the pointer to the word 7 of `GenG14`'s `heap 1` and `new = 9` leaves `X2 = 7`). Coverage on
quick-v10 (`lake exe gen-check --jobs 2`, G61 on P0', on main 2320a5d3): 7,983 of 9,297 functions
(85.86%, +316 over G60's 7,667: 218 of std/runtime, 84 of std/sync, 10 of std/encoding, 4 tests;
all 91 of std/sync/atomic), 269,353 values; G60 and every earlier slice unchanged. Composed into
`verified_mach` (`GoFV/Proof/Obj/G64.lean`, below), with `checkObj`'s atomics (#687, #692).

## Phase 3: genssa, slice G62, incoming stack arguments (I7, #553)

`GoFV.Proof.Gen.g62_value`, `g62_initMem`, `g62_term`, `g62_nilPanic`, `g62_boundsPanic`
(`GoFV/Proof/Gen/G62.lean`): `checkG62` (on P0', `GoFV/Gen/Check62.lean`) is G61 with the `Arg`
of a parameter the function's ABI assigns to the stack (`vkind62a`, tried when G61 rejects a
value): no temporary, no argument, a 64-bit class, homed in the slot of its own piece
(`argKey x type off`, `stackalloc`'s home) at a `NAME_PARAM` operand, the caller's stack argument
`x+off(FP)`; genssa emits no code for it. `homeOK10` (G10 on) accepts the slot home of an `Arg`;
every slice before G62 still rejects the `Arg` by its value check, and `slot_spill10` now says a
slot home is a spill's or an `Arg`'s (calls and interface calls are still never slot-homed). When
`checkG62` accepts a function, they are G61's statements at either mode `osp` (`vk62_step`: G61's
values by `vk61_step`, an `Arg` by `g62_arg`, `GoFV/Proof/Gen/G62a.lean`: `runLoc` writes
`argVal`'s piece to the slot, the machine does not step, the class table is unchanged and the
upper-bit table empty after it). **Run premise added: `ArgOK`** (Assumptions): at an `Arg`, the
machine's bytes at its slot's frame address hold the piece (`SlotRel`), the caller's stack
argument (ABI0: at `8 + offset` above the entry `SP`). It is a caller-side fact about the entry
state; in the composition on G62 it is discharged: the `Arg`s run before the start `k` with the
entry values (`entryLen`), their slots are related at the entry by the caller's side
(`EntryMatch.stack`, an ABI0 caller obligation of the entry condition), and no `Arg` runs after `k`
(`argsOK`, checked), so `ArgOK` holds vacuously along the run (`NoArgRun`). Witness:
`genG62_witness` (`runtime.syscall_Exit`'s ABI0 wrapper on P0', mode `false`:
`checkG61` rejects it, `checkG62` accepts it; `v5 = Arg {code}` from the first state of an
activation on `code = 7`, with the caller's word 7 at `SP + 24`, leaves the slot of `code`
holding 7 and the machine's word there 7). Coverage on quick-v10 (`lake exe gen-check --jobs 2`,
G62 on P0', on main 0f930080): 8,175 of 9,297 functions (87.93%, +192 over G61's 7,983: 187 of
std/runtime, 3 of std/internal, 1 of std/sync, 1 of std/bytes), 271,361 values; rows G1 to G61
identical to main's run, the rejected set a subset of G61's. Composed into `verified_mach` (the
composition on G62, below).

## Phase 3: genssa, slice G63, float spills and reloads (I7, #553)

`GoFV.Proof.Gen.g63_value`, `g63_initMem`, `g63_term`, `g63_nilPanic`, `g63_boundsPanic`
(`GoFV/Proof/Gen/G63.lean`): `checkG63` (on P0', `GoFV/Gen/Check63.lean`) is G62 with the spill
and the reload of a `float64` homed in an `F` register (`vkind63a`, tried when G62 rejects a
`StoreReg` or `LoadReg`; G2's spill and reload take X registers only): a `StoreReg` of a float
shape of class 64 whose argument is in an `F` register, homed in a spill slot with a frame
operand, is `FMOVD Fs, off(RSP)` (`fspill63`); a `LoadReg` of a 64-bit value from such a slot into
an `F` register at a float shape of class 64 is `FMOVD off(RSP), Fd` (`freload63`), as genssa's
`storeByType`/`loadByType` emit them (`cmd/compile/internal/arm64/ssa.go`, `ssa.OpStoreReg`,
`ssa.OpLoadReg`). The slots are `checkFrame`'s 8-byte slots (a `float32` slot fails `slotOK`).
When `checkG63` accepts a function, they are G62's statements at either mode `osp` (`vk63_step`:
G62's values by `vk62_step`; `g63_fspill`, `GoFV/Proof/Gen/G63a.lean`: the V register's low 64
bits stored at the slot relate as a register (`SlotRel`, `valRel_of_fvalRel`); `g63_freload`: the
slot's 8 bytes loaded into the V register relate to the value by `fvalRel_of_valRel`; neither
writes an X register, `uokl_f63`). **Run premise added: `FReloadPre`** (not trusted, a fact of
the run, as G44's `FLoadPre`): a float reload reads, at its float shape, no pointer without an
integer form (a V register relates only integers and `poison`, `FValRel`; a slot relates a pointer
by its injected address). It is in `RunPre`'s per-step premises since the lift to G64. Witness:
`genG63_witness` (`doprint` of `test/ken_cplx0` on P0', mode `false`: `checkG62` rejects it,
`checkG63` accepts it; `v2 = StoreReg v15` from `1.5` in `F0` runs `FMOVD F0, c+0(FP)` and
leaves the slot of `c`'s first piece holding the bits `0x3FF8000000000000` and the machine's
word at `SP + 24` the same). Coverage on quick-v10 (`lake exe gen-check --jobs 2`, G63 on P0', on
agent/g62 c6b60516): 8,206 of 9,297 functions (88.26%, +31 over G62's 8,175: 31 of the 32 whose
whole reason set was `argument v# in register #` with `writes register #`; the 32nd,
`test/ken_convert` `main`, then fails G35's `MOVDnop/MOVDreg: upper bits unknown`), 274,435
values; rows G1 to G62 identical to G62's run, the rejected set a subset of G62's. The 11 `float
spill shape` and 12 `float reload shape` functions are `float32` spills (4-byte slots). Composed
into `verified_mach` (the composition on G64, below), `FReloadPre` among `RunPre`'s per-step
premises.

## Phase 3: genssa, slice G64, 128-bit moves of blobs (I7, #553)

`GoFV.Proof.Gen.g64_value`, `g64_initMem`, `g64_term`, `g64_nilPanic`, `g64_boundsPanic`
(`GoFV/Proof/Gen/G64.lean`): `checkG64` (on P0', `GoFV/Gen/Check64.lean`) is G63 with the 128-bit
moves `lower` makes of a `Move` of 16 to 64 bytes (`ARM64.rules` 420–428): `FMOVQload` into an
`F` register at the shape `blob 16` (`FMOVQ src, Fd`), `FMOVQstore` of such a blob (`FMOVQ Fs,
dst`), `FLDPQ` into two distinct `F` registers (`FLDPQ src, (Fa, Fb)`), `FSTPQ` (`FSTPQ (Fx, Fy),
dst`) and the selects of `FLDPQ`'s components homed in their registers (no code) (`vkind64a`,
tried when G63 rejects one of these ops). The operand (`qaccessA`) is G3's (`off(Rn)` through a
64-bit register, `sym+off(SB)` of a global) or a frame variable's (G57b's `fvar57?`: G6's `Blk.temp`
or G49's `Blk.local` variables); accesses off `SP` without a symbol (G48's outgoing area) stay
rejected. A blob's V register home is accepted by `homeOK10` (`blobHome`; every slice before G64
rejects the blob values themselves by their value check). `runLoc` loads a blob as its 16 raw bytes
(`Arm64.load16`) and stores them back (`Arm64.storeBytes 16`); the machine moves the 128 bits.
**Relation change:** `LocMatch` relates a V register by `VRel` (`GoFV/SSA/Sem/LocMatch.lean`): a
blob bytewise (`BlobRel`: each byte `ByteRel` to the register's byte at its position, pointer
fragments as bytes of the injected address, as memory bytes are), every other value by `FValRel`
as before (by definition, so the earlier slices' `poison` and float cases are unchanged; the callee
contracts' `RegRel` keeps `FValRel`, `RegRel.loc`). `Facts.clsReg` admits a blob in a V register.
When `checkG64` accepts a function, they are G63's statements at either mode `osp` (`vk64_step`:
G63's values by `vk63_step`; `GoFV/Proof/Gen/G64a.lean`: `g64_qload`/`g64_qldp` relate the loaded
bytes of a live block to the 128 bits the machine loads (`blobRel_load`, `memInj_byteRel`);
`g64_qstore`/`g64_qstp` write the bytes of the register's content read at the blob shape (`poison`
or a 16-byte blob, `store16_rel`) and keep `MemInj` (`memInj_write16`); `g64_qsel` reads the
component's register; the operand's machine address by `qbase64`). **Run premise added:
`QLoadPre`** (not trusted, a fact of the run, as G3's loads and G44's `FLoadPre`): an `FMOVQload`
reads 16 valid bytes at its address (`symAddr`), an `FLDPQ` 16 at each of its two (`pairAddr`); Go
copies memory it owns. It is in `RunPre`'s per-step premises since the lift to G64. Coverage on quick-v10
(`lake exe gen-check --jobs 2`, G64 on P0', on agent/g63 b19f5edd): 8,261 of 9,297 functions
(88.85%, +55 over G63's 8,206; the ceiling of the 61 functions whose whole reason set was the blob
moves is 58, the 3 others store to the outgoing area off `SP`), 281,544 values; rows G1 to G63
identical to G63's run, the rejected set a subset of G63's. Witness: `genG64_witness`
(`GenG64.lean`, `makearray` of `test/range` on P0', mode `false`: `checkG63` rejects it, `checkG64`
accepts it; `v10 = FLDPQ` from a memory holding `main..stmp_16` runs `FLDPQ main..stmp_16(SB),
(F0, F1)` and leaves the blobs of the literal's first two 16-byte halves in `F0`/`F1` and their
128 bits in `V0`/`V1`; `QLoadPre` holds by the two valid reads). Composed into `verified_mach`
(the composition on G64, below), `QLoadPre` among `RunPre`'s per-step premises.

## Phase 3: genssa, slice G65, float frame-variable loads and float pair stores (I7, #553)

`GoFV.Proof.Gen.g65_value`, `g65_initMem`, `g65_term`, `g65_nilPanic`, `g65_boundsPanic`
(`GoFV/Proof/Gen/G65.lean`): `checkG65` (on P0', `GoFV/Gen/Check65.lean`) is G64 with, tried when
G64 rejects a value (`vkind65a`): `FMOVSload`/`FMOVDload` of a frame variable (G57b's `fvar57?`:
G6's `Blk.temp` or G49's `Blk.local` variables) into an `F` register at the op's width (`FMOVS`/
`FMOVD off(<nc>), Fd`), and `FSTPS`/`FSTPD` through a 64-bit register without a symbol or to a
global (G3's `accessA`: `FSTPS`/`FSTPD (Fa, Fb), off(Rn)` or `sym+off(SB)`), floats of the op's
element width in `F` registers. Before G65, G44 loaded floats through a register or of a global only
and G57 stored float pairs to frame variables only. When `checkG65` accepts a function, they are
G64's statements at either mode `osp` (`vk65_step`: G64's values by `vk64_step`;
`GoFV/Proof/Gen/G65a.lean`: `g65_fvload` is G44's float load at the variable's block (`VarAt57`),
`g65_fstpReg`/`g65_fstpGlob` are G57's `STPW`/G22's `STP` with V registers and the machine's pair
store at the operand's address, `progStep_fstpAt`). **No premise added:** the loads use G44's
`FLoadPre`, already in `G54Pre`, so the lift replaces only `checkG64` by `checkG65`. Coverage on
quick-v10 (`lake exe gen-check --jobs 2`, G65 on P0', on main 1187b1e7): 8,274 of 9,297 functions
(88.99%, +13 over G64's 8,261: every function whose whole reason set was these accesses), 284,888
values; rows G1 to G64 identical to G64's run, the rejected set a subset of G64's. Witness:
`genG65_witness` (`GenG65.lean`, `init.func82` of `test/gcgort` on P0', mode `false`: `checkG64`
rejects it, `checkG65` accepts it; `v21 = FMOVDload {u}` runs `FMOVD u-8(SP), F1` from a memory
holding `u = 1.01` in its `temp` block at `SP + 16` and leaves `1.01`'s bits in `F1` and in `V1`'s
low word; `FLoadPre` holds by the valid read of `u`). Not yet composed into `verified_mach`.

## Phase 3: genssa, slice G66, spill slots of 1, 2 and 4 bytes (I7, #553)

`GoFV.Proof.Gen.g66_value`, `g66_initMem`, `g66_term`, `g66_nilPanic`, `g66_boundsPanic`
(`GoFV/Proof/Gen/G66.lean`): `checkG66` (on P0', `GoFV/Gen/Check66.lean`) is G65 with, tried when
G65 rejects a value (`vkind66a`): the spill of an integer or boolean of 1, 2 or 4 bytes from an `X`
register (`MOVB`/`MOVH`/`MOVW Rs, off(RSP)`), its reload (`loadByType`: `MOV{B,H,W}` for a signed
type, `MOV{B,H,W}U` otherwise), the spill and reload of a `float32` through an `F` register
(`FMOVS`), and an incoming stack argument of any class. `checkFrame` (G2's, shared) takes slots of
1, 2, 4 or 8 bytes with disjoint windows, every homed value of its slot's class and size
(`slotsApart`, `homeFits`); every earlier slice still has 8-byte slots only (its spills, reloads
and `Arg`s are of class 64), and their accepted sets are unchanged. Design review:
`docs/plans/slot-size.md` (#711, integrator's decision on #553: option P3). When `checkG66` accepts
a function, they are G65's statements at either mode `osp` (`vk66_step`: G65's values by
`vk65_step`; `GoFV/Proof/Gen/G66a.lean`: `g66_nspill`, `g66_nreload`, `g66_fspill`,
`g66_freload`, the slot written through `slot_write_match`; an `Arg` by G62's `g62_arg`, now at any
class). **No premise added.** **`StkAt` per slot size:** each spill slot's window in `StkAt` is the
slot's own size (`(E.lc.slotTy k).size`; before, 8 bytes, `StkAt8`); `StkAt_eq_of_slots8`
(`GoFV/Proof/Gen/Stack.lean`) proves `StkAt E = StkAt8 E` when every slot has 8 bytes, which is
every function a slice before G66 accepts, so the contracts and invariants stated with `StkAt`
(the callee contracts' rows below, `G3Inv`/`CoreInv`) are literally the same there. `SlotInv` holds
each slot's value at its class (`slotCls`, 64 at every 8-byte slot). Coverage on quick-v10 (`lake
exe gen-check --jobs 2`, G66 on P0', on main 0faee08f): 8,789 of 9,297 functions (94.54%, +515 over
G65's 8,274); rows G1 to G65 identical to G65's run, the rejected set a subset of G65's. Witnesses:
`genG66_witness` (`GenG66.lean`, `runtime.procyield`'s ABI0 wrapper, mode `false`: `checkG65`
rejects it, `checkG66` accepts it; the narrow stack argument `v5 = Arg {cycles}` and the narrow
reload `v2 = LoadReg v5`, `MOVWU cycles+0(FP), R0`, after which the slot's 4 bytes and `X0`'s low
32 bits hold 7) and `genG66s_witness` (`GenG66s.lean`, `runtime.randn`: the narrow spill
`v17 = StoreReg v6`, `MOVW R0, n+0(FP)`, after which the slot's 4 bytes hold 7). Not yet composed
into `verified_mach` (the lift follows G66b).

## Phase 3: whole functions, and generic SSA to machine words (I7, #553)

`GoFV.Proof.Obj.g64_obj_value`, `g64_obj_term`, `g64_obj_nilPanic`, `g64_obj_boundsPanic`
(`GoFV/Proof/Obj/G64.lean`): G64's statements on `checkG64L` (`g64L_value`/`g64L_initMem`/
`g64L_term`/`g64L_nilPanic`/`g64L_boundsPanic`; slice G64 is G63, G62, G61, G60 with the atomics,
with the incoming stack arguments, the float spills and reloads and the 128-bit blob moves;
`g64_obj_value` takes `ArgOK`, which the whole-function run discharges, `NoArgRun`, and
`FReloadPre` and `QLoadPre`, run facts in `RunPre`)
composed
with `obj_star` and `obj_panic`, as `g7_obj_value`/`g7_obj_term` for G7, under `G49Env` (`G28Env`
and `VarsAt49`) and G35's
upper-bit table of the P0 state (`UOKL m (uL35 lc (uIn35 lc b) blk i)`; a terminator hands the
successor's start `uIn35 lc e.b` on). `g64_obj_value` also covers an `InitMem` in a lowered
function, from a state holding the initial memory (`MemInit`) at a clean position (`MemAt`;
`checkG64L` accepts it only there, `g64L_clean`): no code, the state unchanged. A panic is matched
by machine steps to a state that
panics (`MPanics`) with `nilDeref`, or with a bounds panic that `BoundsAgree`s with `runLoc`'s.
`GoFV.Proof.Obj.g64_obj_callPanic` (`GoFV/Proof/Obj/CallPanic.lean`): a static call whose callee
panics, under the trusted `CallPanicOK` (§ Assumptions), is matched by machine steps to a state
that panics with the same panic; `g64_obj_icallPanic`: the same for an interface or closure call
(`CALL (Rn)`), under the trusted `ICallPanicOK`; at G48's mode (the mode `true`, which a function
that needs it takes, `hn48`) under `CallPanicOKS`/`ICallPanicOKS` (`CallPanicOKAt`,
`ICallPanicOKAt`: `SepFromW`; a call with stack arguments or results, G48's `callKind48`, at the
registers of `callRegsS`; at the mode `false` such a call has the registers of `callRegsZ`,
`take48_call`).
Both cover every call `checkG64L` accepts (a call
is no op of G64's (`qop64`), no spill or reload, no `Arg`, no op of G61's group A, G52–G59's
groups, G49 frame-variable access, G51 op, G50 pair load or select: `vkind64_eq63`,
`vkind63_eq62`, `vkind62_eq61`, `vkind61_eq60`, `vkind60_eq48`, `vkind48_ok`, `vkind56_eq49`,
`vkind49_ok51`, `vkind51_eq50`, `vkind50_eq47`): one
of G46's kinds (ABI registers in `R0`–`R15`) or G47's `callKind47`/`icallKind47` (`F0`–`F15`
admitted; an argument there is read at its float shape from its V register, `argsV`,
`vkind47_call`, `vkind47_icall`). `GoFV.Proof.Obj.g64_obj_memPanic`
(`GoFV/Proof/Obj/MemPanic.lean`): a load (`MOV{D,W,WU,H,HU,B,BU}load`, `LDP`) or store
(`MOV{D,W,H,B}store`, `STP`; `memFaultOp`) whose step panics (`nilFaults`: a nil base, the address
in the nil page) has no symbol, so it is no G49 frame-variable access (`frameVar49?_none`,
`vkind49_eq51`; nor an op of G64's, a spill or a reload, `vkind64_eq63`, `vkind63_eq62`, nor of
G61's group A or G52–G59's groups, `vkind61_eq60`, `vkind60_ok49`; an
access off `SP`, G48's
`kind48`, takes G48's mode, `take48`, and does not fault: under `SPInv` its base relates to
`SP`, above the nil page), and its
base in a register holding the
machine word 0, so its Prog
faults in the nil page (`nil_fault_page`, `progStep_loadN_nil`, `progStep_ldp_nil`,
`progStep_storeN_nil`, `progStep_stp_nil`): the machine panics with `nilDeref`, no premise.
`GoFV.Proof.Obj.g64_obj_ldarPanic`: the same for an acquire load (`LDAR`, `LDARW`, `LDARB`,
`ldar?`) whose step panics: its address (argument 0, offset 0, no symbol) is nil
(`stepLoc_ldar_panic`), so `LDAR* (Rn)` faults at address 0 (`progStep_ldar_nil`).
`GoFV.Proof.Obj.g64_obj_atomPanic` (`GoFV/Proof/Obj/AtomPanic.lean`): the same for an atomic of
G61's group A (`atom61?`) whose step panics: the generic atomic never panics, so the panic is
`nilFaults`' on its pointer (argument 0, no symbol; `nilFaults_atom61`, `stepLoc_atom61_panic`),
which is nil, its register the machine word 0; what `vkind61` accepts of it is `vkind61a`'s
(`vkind61_atom`), whose Progs (`atomPats61`) reach their first access, `LDAXR*` (the loops), the
LSE instruction, or after `MVN Rv, R27` (`LDCLRAL*`) or `MOV Rold, R27` (`CASAL*`) the LSE
instruction, which faults at address 0 (`progStep_ldaxr_nil`, `progStep_lse_nil`,
`progStep_casal_nil`; `atom_nil_run`): no premise. The
register-index loads and stores are excluded: `runLoc` faults on their nil base whatever the
index, the machine only when the index keeps the address in the nil page. A G50 pair load
(`LDPW`, `LDPSW`, `FLDPD`, `FLDPS`), a G53 `LoweredMove`, a G54 loop or a G64 128-bit load or
store (`FMOVQload`, `FLDPQ`, `FMOVQstore`, `FSTPQ`) whose step panics is outside `RunPanicPre`.

`GoFV.Proof.Obj.obj_whole_ret` (`GoFV/Proof/Obj/Whole.lean`): when `checkG64L` and `checkObj` accept
a function and `retRegsOK` its returns, the machine starts at its entry (`MachEntry`, return
address `s0.x 30`; when the stack check fails, the prologue loops through the morestack tail under
`runtime.morestack`'s contract `MorestackOK`, with the spill slots apart from `g`, `TailSep`, and
the entry values surviving the tail, `MoreEntry`: each live register but `R26` reloaded from a
slot it fits (a vector register from its `F` register's slot), the live blocks apart from the
slots and the guard word; `EntryMatch.more`), a run
of `runLoc`'s body (`runLoopLoc` from the
state `s` at the entry block) whose first `k` values (the entry values and the `Arg`s of the
incoming stack arguments) lead to a state `sI`
related to the entry machine state (`EntryMatch E0 g W`: the argument registers, no flags, every
slot the home of an `Arg` whose caller bytes at `8 + off` above the entry `SP` hold its value,
`SlotRel`, apart from `g`'s first 32 bytes: the stack clause, ABI0's caller obligation, which for a
function with no `Arg` is G61's `slots = []`, `EntryMatch_stack_nil`;
the memory injected into a memory that is the machine's but for the bytes `W`, here the windows of
the register-assigned parameters in `Blk.local` blocks the function accesses, `InWins L E0.sp
(pendWins lc g)`; `EntryEnv`: the frame, `g`, the caller's `LR`/`FP`; no upper-bit fact carried
into the body: G49's table (G35's) after the entry values is empty, `uL35 lc [] … k = []`, the entry
block's start being empty, `checkG64L_uIn_entry`), whose entry stores from value `k` cover those
windows (`entryStoresOK lc g k`, `GoFV/Gen/Entry49.lean`, checked: `entryStoresOK_cover`), whose
`Arg`s all run before `k` (`argsOK lc g spills k`, `GoFV/Gen/Entry62.lean`, checked: every `Arg`
in the entry block before `k`, no edge to the entry block, so no `Arg` runs after `k`, `NoArgRun`,
and `ArgOK` holds vacuously along the run; a function with an `Arg` has no pending window and no
morestack spill, so the morestack path keeps its slots, `EntryMatch.more`, and `sim_entry` relates
them at their frame operands, above the saved words and outside `W`) and
whose every later step meets its premises
(`RunPreM osp`: `RunPre` at the mode `false`, `RunPreS` at the mode `true`, at the states `runLoc`
reaches from `sI`: at a value whose step succeeds `G54Pre`
(`G14Pre`, `LdarPre`, `CmpPre`, `FLoadPre`, `FIdxPre`, `FArithPre`, G50's `PairPre50`, G51's
`Pre51a`, G53's `Pre53a` and G54's `Pre54a`, `Pre54b`: a `LoweredMove`, `LoweredZeroLoop` or
`LoweredMoveLoop` accesses valid bytes, a copy's two ranges the same or disjoint), G63's
`FReloadPre` (a float reload reads no pointer without an integer form) and G64's `QLoadPre` (a
128-bit load reads valid bytes), `GetGOK` and
the trusted
`CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`,
`MemEqOK`, at G48's mode `CallOKS`, `CallOKZS`, `ICallOKS`, `WbOKS`, `MemEqOKS` (the contracts of
the mode `osp`: `CallOKAt`, …) and `CallOKStk`; `G1TermPre`; no entry value (`entryOp24`) but an
`InitMem` in a lowered function), at a mode `osp` that is `true` if the function needs G48's mode
(`hn48`; then `hosp`: the activation's `outargs` block at `SP`; `SPInv E0 sI`, `hspI`, which
`SimAt` carries: `g60_value` keeps it, the entry stores keep it by `spInv_step`), `G3Inv` of `sI`
at the mode (`SepFromW` at `true`),
whose first state `s` holds the initial memory (`MemInit`; `SimAt` carries it to every clean
position, `MemAt`: `memAt_enter` through the entry values, `memInit_clean_step` along a value,
`memInit_clean_term` along an edge), and that returns
`(rs, mm)`, is matched by `runMach` of the linked words that returns to `s0.x 30` in a state `t'`
with `MachRet s0 t'` (`SP`, `g`, `R29` as at entry) and `ResultRel E (ownOutRegs lc) rs mm t'`
(`GoFV/Proof/Obj/Results.lean`): `rs` in the function's ABI result registers (`ownOutRegs`: those
of its register-assigned results), each related to its X register (`R0`–`R15`, `ValRel`) or, a
result in `F0`–`F15` (Go registers 31–46), to its V register (`FValRel`), `mm` injected; a result
the ABI puts on the stack (or a zero-sized one) is no `MakeResult` argument: `expand calls` stores
it to its `PPARAMOUT` variable, which is in `mm`. `retRegsOK` (`GoFV/Gen/Results.lean`): every
`Ret` block's control is a `MakeResult` whose tuple has one component per argument, the last the
memory, each result homed in its ABI register at a class no wider than the register's, a result
in an `F` register at a float shape (`fTy`) read at a float shape of its class (`ret_results`, in
both of `runLoc`'s modes: `valRel_retypeL_le` for lowered functions, `lmode_valRel_le` for those
with no arm64 op; `fvalRel_retypeL`, `lmode_fvalRel` for the V registers). The pieces: the
prologue (`sim_entry`, over `obj_entry`, to `SimAtW`: the P0 state related with its memory
replaced by one that agrees with it outside `W`, but for the saved `LR`/`FP` words), the entry
stores (`sim_entryStores`: each entry store, `entryStore?`, is a store or `STP` of G49's
frame-variable path, `entryStore?_spec`, whose Prog writes its window alike in both memories,
`g64L_entryStore`, `GoFV/Proof/Obj/Entry49.lean`, over `op_mem2W`, `g49_storeW`, `g49_stpW`,
`writeMem_agree`; no entry store panics, it has a symbol; the spills and values without code
between the entry values and the entry stores, which `storesFrom` steps over (`entrySkip`: a
`StoreReg` or `SB` without an aux, `SP`, `InitMem`), run against the same relaxed memory,
`sim_entrySkip`, `g64L_entrySkip`, `GoFV/Proof/Obj/EntrySkip.lean`, over the W-forms
`g2_spillW`, `g63_fspillW`, `g24_spW`, `g3_sbW`: a spill writes its slot alike in both memories,
the others run no code, none panics, `stepLoc_entrySkip_ne_panic`; after them no byte is left
out and `SimAtW` is `SimAt`), each value (`sim_value`, over
`g64_obj_value`, at a value that is no `Arg`, `NoArgRun`), each terminator (`sim_goto`, over
`g64_obj_term`), the return (`sim_ret`: the
`RET` after no-ops, `termG3_ret`, `obj_exit`, `ret_results`), the run by induction on the fuel
(`sim_from_ret`). `checkG64L_cx` covers lowered functions and those with no arm64 op (G26). A
leaf (`checkObj`'s `leaf`: no `CALL`), framed or not, returns through `X30`: `SimAt` carries the
caller's return address in the P0 state's `X30` of a leaf, from the prologue (which keeps it)
through every P0 run of a value or terminator (`GoFV.Proof.Obj.obj_star_leaf`,
`leaf_step_x30`, `GoFV/Proof/Obj/Sim.lean`: from a Prog with `X30` outside the Progs and the
end, the run stays at Progs, so no hook runs, and no Prog of a leaf writes `X30`: `sameEffect`,
`progSym_ctl`); a framed leaf's epilogue recomputes `R29` as the caller's `SP - 8`
(`EntryEnv.fp0`).
`runPre_simple`: `RunPre` holds of a function whose ops from the start on are simple
(`simpleFrom`, no G50 pair load, `CMN`, `CMPshiftRA`, `LoweredMove`, G54 loop, reload
(`LoadReg`) or G64 128-bit load among them; `g51Pre_simple`, `g54Pre_simple`, `pre64_simple`).

`GoFV.Proof.Obj.obj_whole_panic` (`Whole.lean`): `obj_whole_ret`'s premises on the entry and the
steps, the trusted `HookPanicMap` and `BoundsOK`, and the panic premise `RunPanicPre` (at every
state the run reaches, a value whose step panics is a nil check, a load or store of `memFaultOp`,
an acquire load (`ldar?`), an atomic of G61's group A (`atom61?`), a bounds check, or a static,
interface or closure call whose callee
panics as `CallPanicOK` or `ICallPanicOK` says at every `LocMatch`ed machine state): if the run of
`runLoc` panics with `e`, `runMach` panics with `e'`, `BoundsAgree e e'` (the same panic, or for a
bounds check the runtime's report of the same failure). The pieces: `sim_valuePanic` (over
`g64_obj_nilPanic`, `g64_obj_memPanic`, `g64_obj_ldarPanic`, `g64_obj_atomPanic`,
`g64_obj_boundsPanic`, `g64_obj_callPanic`, `g64_obj_icallPanic`; an access's `vkind64` is
`vkind62`'s, `vkind64_eq63`, `vkind63_eq62`, its `vkind62` `vkind61`'s, `vkind62_eq61`, its
`vkind61` `vkind60`'s, `vkind61_eq60`, and its `vkind56` is `vkind49`'s, `vkind56_eq49`
(`vkind56_eq55`, `vkind55_eq54`, `vkind54_eq53`, `vkind53_eq52`, `vkind52_eq49`), which is
`vkind28`'s, `vkind49_eq51`,
`vkind51_eq50`, `vkind50_eq47`,
`vkind47_eq46`, `vkind46_eq45`, `vkind45_eq44`, `vkind44_eq43`, `vkind43_eq42`, `vkind42_eq41`,
`vkind41_eq40`, `vkind40_eq38`, `vkind38_eq28`; a call's is that chain's or G47's, `vkind47_call`,
`vkind47_icall`), `sim_from_panic`;
terminators
never panic (`stepTermLoc_ne_panic`).

`GoFV.Proof.Obj.verified_mach` (`GoFV/Proof/Obj/EndToEnd.lean`): `verifiedPipelineFull_refines`
composed with `obj_whole_ret` and `obj_whole_panic`. For `f` through the verified pipeline
(`fullyVerified`) and its output's genssa Progs with the float constant loads (P0') and assembled
words accepted by `checkG64` (slice G64 on `LocCtx.make` of the output: `refsLive`, and
`checkG64L` on `lc = liveCtx` of it,
its loops' branch targets included, `loopOK`),
`entryStoresOK` (on `lc`, at the entry stores' position `k`), `argsOK` (on `lc`, at `k`, with the
object's morestack spills), `retRegsOK` (on `lc`) and
`checkObj` (on P0'), with `memTyL lc` when the Progs load a float constant (`hmt`) and the input
memory holding the float constant symbols (`hro : RoMem (constRo (symNames g)) (addGlobals e
mem)`; `RoRun` by `lreach_roMem`, or `roRun_nil` without a constant), on every input of `VPre`
with the pipeline's premises (`hn`,
`ha`, `hnp`) on which `run` of `f` returns or panics, a `runLoc` of the output refines it
(`OutcomeRefines`), `runLoc` is `finish` of its body's defined outcome on `lc` (`runLoc_eq`,
`runLoopLoc_live`, `finish_defined`; `locInit` holds the initial memory, `MemInit`, by `rfl`);
when the body returns, `runMach` of the linked words returns
to the caller with the results in their registers (`obj_whole_ret`'s conclusion); when it panics
and the panic
premises hold, `runMach` panics alike (`obj_whole_panic`'s conclusion). `verified_mach` is for a
function that does not need G48's mode (`hn48 : needs48 lc = false`, checked); it is main's
statement over `checkG64`, with G63's `FReloadPre` and G64's `QLoadPre` among `RunPre`'s per-step
premises (over `checkG62` before the lift to G64; with `argsOK` and the stack clause of `EntryMatch`
since the lift to G62, over `checkG61`, with `EntryMatch`'s `slots = []`, before it; over
`checkG60` before the lift to G61, where `RunPanicPre` came to admit an
atomic's nil fault), with `SepFrom` and the contracts `CallOK` …, `CallPanicOK`,
`ICallPanicOK`. `GoFV.Proof.Obj.verified_mach_S` covers every function `checkG64` accepts, in G48's
mode: `hinv : G3Inv … sI true` (`SepFromW`), `hosp : E0.outSP = true`, `hspI` (`SPInv E0 sI` of a
lowered function: the `outargs` block at `SP`, the Go register `SP` holding `SP`), `RunPreS` (the
`CallOKS` family, `CallOKStk`) and `RunPanicPreS` (`CallPanicOKS`, `ICallPanicOKS`). Both are
`verified_mach_M` at a mode (`obj_whole_ret`/`obj_whole_panic` over `{osp}`, `RunPreM`,
`RunPanicPreM`, `SimAt` at the mode). Every premise is in the statement; the trusted ones are in the
table below.

**The address assignment** (`docs/plans/proofs3.md` §8, item 6; #553, #385). `verified_mach`,
`verifiedPipelineFull_refines` and every Phase 1/2/3 theorem hold under every admissible address
assignment (`[Addrs]`, option 2). The checkers do not read it: they evaluate their constants at
`Addrs.fixed` (`Rules.opValC`, `Val.retypeC`, `Val.hasTyC`, `Mem.loadC`, `evalPureC` in
`GoFV/SSA/Sem/Agree.lean`; `termConst`, `constTop`, `nonNegD`, `fixedOK`, Sccp's `constVal`/
`fixOK`/`repOK`, the static instances of `ruleOK`, `ruleOK1`, `ruleDefsL`, `blockOK1`), with a
guard: an integer an op reads as a pointer is a constant only below `2^62` (`opGuard`), where every
admissible assignment decodes alike (`*_agree`). So `verifiedPipeline`, `verifiedPipelineFull` and
the slice checkers `checkG*` take no `Addrs` instance (checked by `GoFVTest/AddrsFree.lean`), and
the verdict `gofv-ssa-opt` computes is `verified_mach`'s premise under every instance, the
machine's among them. Counts unchanged: `gofv-ssa-opt --check --verified` on quick-v10 (8,919
through `rewrite tern`, 7,845 through `trim`, main 6f6f8ea0) and full-v11 (93,683 and 84,123,
main 06837b1e; 93,683 and 83,919 on 7641ba1d) is identical to main, function by function.

**The machine layout** (`GoFV.Proof.Obj.verified_mach_atSP`, `verified_mach_S_atSP`,
`GoFV/Proof/Obj/EndToEndAtSP.lean`; `docs/plans/proofs3.md` §8 items 4 and 6; #553).
`verified_mach` at the instance `Addrs.atSP (baseSP g L E0.sp)` (§ slice G49: activation 0's
`local` blocks undecoded at their frame operands from `SP`), for the activation `envAtSP g L E0`;
`verified_mach_S` at `Addrs.atSPO (baseSP g L E0.sp) E0.sp.toNat` (its `outargs` block undecoded at
`SP` too, G48's mode), for `envAtSPO g L E0`; both with the premise `G49Env` replaced by
`G28Env` of `E0` at `Addrs.fixed`, which asks no place of a frame variable (`g49Env_atSP`, `g49Env_atSPO`; the
pipeline's context is activation 0, `liveCtx_make_act`). Their other premises are the theorems
(the table below) at that instance; the checked ones (`verifiedPipelineFull`, `checkG64`, `argsOK`,
`needs48`, `liveCtx`, `retRegsOK`, `entryStoresOK`, `pendWins`, `memTyL`, `checkObj`) take no instance
(`GoFVTest/AddrsFree.lean`), so they are what `gofv-ssa-opt --e2e` computes. Unlike
`verified_mach_fixed`, `verified_mach_atSP` holds non-vacuously of the functions that access two
or more `Blk.local` variables; unlike `verified_mach_S_fixed`, `verified_mach_S_atSP` holds
non-vacuously of the functions that access any (in G48's mode, at `Addrs.fixed`, `SPInv` pins
`SP` to `outargs 0`'s fixed base `2^62`, and no frame operand reaches a `local` block's fixed base:
`g49Env_fixed_outSP`, witness `fixed_outSP_none`; End-to-end coverage below). Under it a `Convert` of such a block's address
is `poison` (the block is undecoded, a held pointer; §8 item 5), so of a function whose
frame-variable address becomes an integer it covers the runs that do not branch on that integer.

Witnesses:
- `objWhole_ret_witness` (`GoFV/Proof/Witness/ObjWhole.lean`): `pallocSum.start` on `p = 7` in
  `plRunEnv`, from `runLoc`'s first state (`locInit`) to `runMach` returning to the caller's
  `0x40` with 7 in `X0`; it runs `sim_entry`, `sim_goto` (the `TBNZ`), `sim_value` (`ANDconst`,
  `MakeResult`) and `sim_ret`. `ObjWholeS.objWhole_ret_witness`: the same at G48's mode (`SP` at
  `outargs 0`'s fixed base `0x4000000000000000`, `SepFromW`, `SPInv`, `RunPreS`).
- `objWholeNL_ret_witness` (`GoFV/Proof/Witness/ObjWholeNL.lean`): `obj_whole_ret` on
  `runtime.gclinkptr.ptr`, a function with no arm64 op (G26), `ret_results` in Phase 1's mode.
- `objWhole_panic_witness` (`GoFV/Proof/Witness/ObjPanic.lean`): `obj_whole_panic` on `(*A).g` with
  a nil receiver: the nil check's `MOVB` faults in the nil page.
  `g64_callPanic_witness`: `g64_callPanic` (P0) on `fint64to32`'s call (`CallPanicOK`, the mode
  `false`: `needs48` is false of it), under a hook whose callee panics with `nilDeref`;
  `g64_icallPanic_witness`: `g64_icallPanic` on `Locker.Lock`'s interface call `v11`;
  `g64_storePanic_witness`: `g64_memPanic` on `(*queueOnePass).next`'s `MOVW R2, 52(R0)` with a
  nil `q`, which faults at address 52; `g64_loadPanic_witness`: `g64_memPanic` on its
  `MOVWU 52(R0), R3`; `g64_ldarPanic_witness`: `g64_ldarPanic` on `sync/atomic.LoadInt64`'s
  `LDAR (R0), R0` with a nil `addr`, which faults at address 0; `g64_atomPanic_witness`:
  `g64_atomPanic` on `sync/atomic.SwapInt64`'s `LDAXR (R0), R2; STLXR R1, (R0), R27; CBNZ R27`
  with a nil `addr`, whose `LDAXR` faults at address 0.
- `objStarLeaf_witness` (`GoFV/Proof/Witness/ObjG7.lean`): `obj_star_leaf` on `(*A).g`, a leaf:
  the P0 run of its nil check `v6` keeps the caller's `0x40` in `X30`.
- `entryStore_witness` (`GoFV/Proof/Witness/ObjEntry49.lean`): `g64L_entryStore` on
  `runtime.getm`'s ABI0 wrapper's `MOVD R0, ~r0+0(FP)` (`entryStore?`: operand offset 0, 8 bytes)
  from a machine whose `~r0` window holds garbage (`0xAB`), related to `runLoc`'s state with its
  memory replaced in that window (as `EntryMatch` leaves a pending window out): after the `MOVD`
  the relation is `LocMatch` in full.
- `verified_mach_witness` (`GoFV/Proof/Witness/ObjEndToEnd.lean`): `pallocSum.start` from its
  generic SSA (the export's first section, the whole-file pass environment of
  `gofv-ssa-opt --verified`) through the verified pipeline (`fullyVerified`), with every premise
  of `verified_mach` discharged (`checkG64` on its output: `refsLive`, `checkG64L` on `liveCtx`;
  `entryStoresOK`: no pending window, `EntryMatch` with nothing left out; `argsOK`: no `Arg`, so
  the stack clause holds of no slot; `needs48` false).
  `verified_mach_S_witness` (`GoFV/Proof/Witness/ObjEndToEndS.lean`): the same for
  `verified_mach_S`, at G48's mode (`ObjWholeS`).
- `verified_mach_atSP_witness` (`GoFV/Proof/Witness/ObjEndToEndAtSP.lean`):
  `runtime.secret_getStack`'s ABI0 wrapper (two stack results, `Blk.local` blocks at `NAME_PARAM`
  0 and 8, so no `G49Env` at `Addrs.fixed`) from its generic SSA through `verifiedPipelineFull`
  (`fullyVerified`), with every premise of `verified_mach_atSP` discharged: `plRunEnv` with
  `runtime/secret.getStack` returning `0x11` and `0x22` (`VPre` at the machine layout), a hook
  that returns them in `R0`/`R1` (`CallSpec` at every activation extending `envAtSP`), the stock
  Progs accepted by `checkG64`, `retRegsOK`, `entryStoresOK`, `argsOK` and `checkObj` (`needs48`
  false),
  `EntryMatch` with the results' blocks at `SP + 24` and `SP + 32`, `RunPre` with the call's
  contract. `runMach` returns to the caller's `0x40` (`MachRet`, `ResultRel`) with `0x11` and
  `0x22` at the caller's `SP + 8` and `SP + 16`.
- `verified_mach_S_atSP_witness` (`GoFV/Proof/Witness/ObjEndToEndAtSPS.lean`): the same wrapper
  for `verified_mach_S_atSP`, at G48's mode (`Addrs.atSPO`, `envAtSPO`: `EntryMatch` with the
  `outargs` block at `SP`, its first word the saved `LR`'s, `poison`, `SepFromW`; `SPInv`: the Go
  register `SP` holds the held pointer to `outargs 0`; `RunPreS` with the call's contracts
  `CallOKS`, `CallOKZS`, `CallOKStk`).

Not yet covered (#553): panics other than nil checks, loads, stores, acquire loads, atomics, bounds
checks and calls (register-index loads and stores; G50's pair loads; G53's `LoweredMove`; G54's
loops; G64's 128-bit loads and stores; write barriers; `memequal`).

**Read-only data** (`docs/plans/proofs3.md` §10; the base for the float constants `$f64.<bits>` and
`JUMPTABLE`'s table):
- `GoFV.Proof.Obj.lreach_roMem` (`GoFV/Proof/Obj/RoReach.lean`). Assume:
  - the input memory with the global image has the read-only allocations `ro` (`RoMem`);
  - the contracts keep them (`Env.KeepsRo`, already in Phase 1's `RoImage`);
  - every value of the function whose shape may hold a memory has a memory op (`memTyL`,
    `GoFV/Gen/MemTyL.lean`, a checked condition).

  Then every memory of every state `runLoc` reaches has them: stores need a writable allocation,
  and calls are contracts (`stepLoc_locMems`, `arm64Op_mems`, `stepTermLoc_locMems`,
  `GoFV/Proof/Obj/RoLoc.lean`).
- `GoFV.Proof.Gen.ro_byte` (`GoFV/Proof/Gen/RoByte.lean`, moved from `RoReach.lean` for slice
  G56): in a `LocMatch`ed state, each concrete byte of such an allocation is in the machine's
  memory at the global's address (`MemInj`, `AddrAgree`). `ro_addr`: the allocation lies above the
  nil page.
- `constSymAlloc?` (`GoFV/SSA/Sem/ConstSym.lean`): the allocation of a float constant symbol,
  built from its name.

No trusted clause is added. Witness: `objRo_witness` (`GoFV/Proof/Witness/ObjRo.lean`, on
`pallocSum.start` in `plRunEnv`, which has the read-only `runtime.writeBarrier` flag). Used by
slice G56 (float constants loaded from `$f64.<bits>`/`$f32.<bits>`, `checkObj` on P0') and in
`verified_mach`, which takes two premises for it: `memTyL lc = true` (checked by the driver,
sound by `memTyL_val`) and `RoMem (constRo (symNames g)) (addGlobals e mem)` (Assumptions, row
`RoMem` of the constant symbols); `obj_whole_ret`/`obj_whole_panic` take `RoRun` (`RoPre56` at
every state the run reaches), which `verified_mach` gives by `lreach_roMem` with `Env.KeepsRo`
from `RoImage`. `JUMPTABLE` needs its slice.

### End-to-end coverage (`gofv-ssa-opt --check --verified --e2e`)

The functions `verified_mach`'s function-level premises hold of (#553): the verified pipeline is
`fullyVerified` (as `--check --verified` runs it: driver export environment, type rounds), and on
the pipeline's own output (function and tables) genssa's Progs with `progedit`'s float constant
loads (P0', the constant symbols numbered as `Flushplist` numbers them) are accepted by `checkG64`
against `LocCtx.make r.st.tables r.st.func`, `entryStoresOK`, `argsOK` and `retRegsOK` hold of
`liveCtx` of
it and its class
tables (and `memTyL` when the Progs load a float constant), and `checkObj`
accepts `Flushplist`'s output on P0' (`GoFVTest/Driver/E2E.lean`,
`docs/DRIVER.md`). Frame (`allocFrame`), Progs and object are the
ports' own; the frame is laid out on the pipeline's own locals (`ownFrame`: the frontend's
declarations, then the autos the pipeline created). From the stock `.prog` file only the driver
input view is read (definitions, config, `Dcl` at `AllocFrame`'s start, `genin`). The stock
column runs the same back end on the stock `trim` function of every function.

**Entry stores after spills (`entrySkip`).** `storesFrom` steps over the spills (`StoreReg`) and
the values without code (`SP`, `SB`, `InitMem`) genssa places between the entry values and the
entry stores (`GoFV/Gen/Entry49.lean`; proof `sim_entrySkip`, `g64L_entrySkip`). quick-v10, main
3f22d5c4's driver against `agent/entryspill` on it (`--jobs 2`): end to end 6,675 → 6,698
(`verified_mach` 6,472 → 6,493, `verified_mach_S` 203 → 205), 0 lost (`comm` of the accepted
lists); `entryStoresOK` rejects 35 → 12 of the 77 with a pending window (stock 51 → 21), end to
end with a pending window 42 → 65; vacuous at `Addrs.fixed` under `verified_mach_S` 7 → 9.

| quick-v10 (9,297 functions, 8.5 min; the composition on G64 with `SBFIZ` in `checkObj`, per function at either mode (`agent/sbfiz` on main a6c37a47, the vacuity audit `entryVacuous`), P0' in `checkG64` and `checkObj`, `--jobs 2`) | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 7,895 | 84.91% | - |
| … genssa and `Flushplist` ran | 7,895 | 84.91% | 9,297 |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` | 7,225 | 77.71% | 8,204 |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` | 7,225 | 77.71% | 8,203 |
| … ∧ `checkObj` | 7,861 | 84.55% | 9,135 |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` (the premises hold) | 7,222 | 77.68% | 8,163 |
| … of them vacuous (closure context, `entryVacuous`: every variant) | 547 | 5.88% | 600 |
| **… premises hold, not vacuous (end to end, `verified_mach` or `verified_mach_S`)** | **6,675** | **71.79%** | 7,563 |
| … of which `needs48 = false`: `verified_mach` (`SepFrom`, `CallOK` …) | 6,472 | 69.61% | 7,330 |
| … of which `needs48 = true`: `verified_mach_S` (G48's mode) | 203 | 2.18% | 233 |
| … end to end, pipeline output identical to stock after `trim` | 5,637 | 60.63% | - |

`SBFIZ` in `checkObj` adds 1 end-to-end function, `runtime.(*stkframe).argBytes`, under
`verified_mach`. It loses none: the sorted accepted lists, `comm`'d against main a6c37a47
(6,674: 6,471 + 203), show +1 / +0 per mode. Stock column: 7,557 → 7,563. Of the functions whose
other premises hold, `checkObj` now rejects 3 (the stack check of a huge frame twice,
`runtime.poll_runtime_pollUnblock`'s `JMP`); on full-v11 (G61), `SBFIZ` was the first `checkObj`
reason for 58 of them.

**Vacuous at the entry (closure context; correction).** The end-to-end counts before this
table, here, on #189 and on #553, counted closures whose premises hold but of which every
`verified_mach` variant holds only vacuously: quick-v10 7,221 (G64) included 547 such
closures, and full-v11 75,229 (G61) included 7,314. The top-level run (`GoFV.SSA.run`,
`runLoc`, `locInit`) has no closure context (`fr.closure = none`), so a closure's
`LoweredGetClosurePtr` is `poison`, and `RunPre` (`RunPreS`, `RunPreM`) cannot hold of its run:

- 399 (quick-v10) load off the closure pointer at a position every run reaches, where `G3Pre`
  (`G4Pre` for `LDP`) asks for valid bytes at `symAddr` of `poison`;
- 148 have register arguments: their entry block is `LoweredGetClosurePtr, ArgIntReg…`, the
  start `entryLen` stops at the closure pointer (k = 0), and `RunPre`'s
  `entryOp24 v.op = false ∨ (InitMem ∧ lowered)` fails at the first `ArgIntReg`.

The driver now finds them (`entryVacuous`: the entry block's values from `entryLen` that cannot
panic, up to an entry value or a load off the closure pointer) and counts them in a column of
their own, outside the end-to-end headline. Functions vacuous at `Addrs.fixed` stay counted,
because the `_atSP` variants cover them. No other op stops `RunPre` this way:
`entryVacuous`'s first reason covers any entry value after the start. On full-v11 the driver
finds 7,338 of the 76,036 functions whose premises hold on the composition on G64 vacuous (the
full-v11 table below), 7,314 of them among the G61 run's 75,229, so the G61 count corrected is
67,915 (a mirror of the check on the stock `trim` functions had estimated about 67,914). None of the 562
end-to-end closures leaves its closure pointer unused, so counting `LoweredGetClosurePtr` in
`entryLen` alone would make none of them non-vacuous. The fix is a closure context in the
top-level run (#705, design review first). All the earlier quick-v10 and full-v11 end-to-end
counts below include such closures as well.

The composition on G64 (G62 with G63's float spills and reloads and G64's 128-bit blob moves;
`FReloadPre` and `QLoadPre` in `RunPre`'s per-step conjunction) counts 7,221 end to end (7,010
under `verified_mach`, 211 under `verified_mach_S`), 26 more than the composition on G62 (7,195)
and none fewer (`comm` of the accepted lists), in either mode (`needs48` is unchanged: +26 under
`verified_mach`, +0 under `verified_mach_S`): 5 of std/runtime, 4 of std/fmt, 2 each of
std/strconv and std/hash, 1 each of std/strings and std/regexp, 11 tests; 17 of the 26 hold a
128-bit move (`FMOVQ`, `FLDPQ`, `FSTPQ`), the others a float spill or reload. **`checkObj` and
the new Progs:** `checkObj` already models `FMOVQ` loads and stores, `FLDPQ`/`FSTPQ` and `FMOVD`
to and from a frame slot (`fmovP`, `fpairP`; the SIMD&FP paragraph of the assembler entry; the
machine semantics of their words, `LDR`/`STR`/`LDP`/`STP` of `Q` and `D` registers, are among the
forms I6's qemu co-simulation covers, #566: every corpus form, 0 mismatches), and
it rejects none of the functions G63 and G64 add: of the 7,225 that `checkG64`, `entryStoresOK`,
`argsOK` and `retRegsOK` accept it rejects 4, the same 4 as on G62 (the stack check of a huge
frame twice, `SBFIZ`, `runtime.poll_runtime_pollUnblock`'s `JMP`); 125 of the 7,221 end-to-end
functions contain a `FMOVQ`, `FLDPQ` or `FSTPQ` Prog and 10 an `FMOVD` to or from a frame slot.
`argsOK` rejects none (stock column: none). `checkG64` accepts 7,260; 77 have a pending window,
`entryStoresOK` rejects 35, 42 are end to end with a pending window (stock column: 8,255, 95, 51,
44). Vacuous at `Addrs.fixed`: 30 of the 7,010 under `verified_mach` (stock 33 of 7,914), 7 of
the 211 under `verified_mach_S` (stock 7 of 243). The first rejection reasons of `checkG64` among
the fully verified: `store shape` (382), `op CALLtail` (164), `Arg width` (37), `branch shape`
and `load shape` (9 each); `op FMOVQload` no longer occurs.

| quick-v10 (9,297 functions, 5.5 min; the composition on G62, per function at either mode (`agent/lift62` on main e3ac04bb, G62 #698), P0' in `checkG62` and `checkObj`, `--jobs 2`) | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 7,895 | 84.91% | - |
| … genssa and `Flushplist` ran | 7,895 | 84.91% | 9,297 |
| … ∧ `checkG62` ∧ `entryStoresOK` ∧ `argsOK` | 7,199 | 77.43% | 8,136 |
| … ∧ `checkG62` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` | 7,199 | 77.43% | 8,135 |
| … ∧ `checkObj` | 7,858 | 84.52% | 9,124 |
| **… ∧ `checkG62` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` (end to end, `verified_mach` or `verified_mach_S`)** | **7,195** | **77.39%** | 8,089 |
| … of which `needs48 = false`: `verified_mach` (`SepFrom`, `CallOK` …) | 6,984 | 75.12% | 7,854 |
| … of which `needs48 = true`: `verified_mach_S` (G48's mode) | 211 | 2.27% | 235 |
| … end to end, pipeline output identical to stock after `trim` | 6,130 | 65.93% | - |

The composition on G62 (G61 with the incoming stack arguments; `EntryMatch`'s stack clause, the
checked `argsOK`) counts 7,195 end to end (6,984 under `verified_mach`, 211 under
`verified_mach_S`), 192 more than the composition on G61 (7,003 on main e80f022b rebased on #693:
6,792 + 211) and none fewer, in either mode (`needs48` is unchanged, so each function keeps its
mode: +192 under `verified_mach`, +0 under `verified_mach_S`): 187 of std/runtime, 3 of
std/internal, 1 of std/sync, 1 of std/bytes, exactly G62's gain in `gen-check`. `argsOK` rejects
none of the 7,199 functions `checkG62` and `entryStoresOK` accept (stock column: none of 8,136):
every `Arg` sits before `entryLen`, no edge enters the entry block, and no function with an `Arg`
has a pending window or a morestack spill. `checkG62` accepts 7,227; 69 have a pending window,
`entryStoresOK` rejects 28, 41 are end to end with a pending window (stock column: 8,170, 76, 34,
42). Vacuous at `Addrs.fixed` (below): 30 of the 6,984 under `verified_mach` (stock 33 of
7,854), 7 of the 211 under `verified_mach_S` (stock 7 of 235). The first rejection reasons of
`checkG62` among the fully verified: `store shape` (381), `op CALLtail` (164), `Arg width` (37,
the narrow stack parameters), then `branch shape`, `argument v# in register #`, `load shape`,
`op FMOVQload` (9 each); `frame variable off another base` (229 on G61, the stack parameters'
windows) no longer occurs.

| quick-v10 (9,297 functions, 5.5 min; the composition on G61, per function at either mode (`agent/lift61` on main 0f930080: objatom part B #692, G61 #691, the composition on G60 #690), P0' in `checkG61` and `checkObj`, `--jobs 2`) | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 7,878 | 84.73% | - |
| … genssa and `Flushplist` ran | 7,878 | 84.73% | 9,297 |
| … ∧ `checkG61` ∧ `entryStoresOK` | 7,007 | 75.36% | 7,944 |
| … ∧ `checkG61` ∧ `entryStoresOK` ∧ `retRegsOK` | 7,007 | 75.36% | 7,943 |
| … ∧ `checkObj` | 7,841 | 84.33% | 9,124 |
| **… ∧ `checkG61` ∧ `entryStoresOK` ∧ `retRegsOK` ∧ `checkObj` (end to end, `verified_mach` or `verified_mach_S`)** | **7,003** | **75.32%** | 7,897 |
| … of which `needs48 = false`: `verified_mach` (`SepFrom`, `CallOK` …) | 6,792 | 73.06% | 7,662 |
| … of which `needs48 = true`: `verified_mach_S` (G48's mode) | 211 | 2.27% | 235 |
| … end to end, pipeline output identical to stock after `trim` | 5,938 | 63.87% | - |

The composition on G61 (G60 with the atomic read-modify-writes; `checkObj` with the atomics,
#687, and `X27` across Progs, #692; the atomics' nil fault in `RunPanicPre`, `g61_obj_atomPanic`)
counts 7,003 end to end (6,792 under `verified_mach`, 211 under `verified_mach_S`), 258 more than
the composition on G60 (6,745 on main 0f930080) and none fewer: 170 of std/runtime, 78 of
std/sync (52 of std/sync/atomic), 6 of std/encoding, 4 tests (`test/ken_chan` 3, `test/deferfin`
1). `checkG61` ∧ `entryStoresOK` accepts 259 more fully verified functions than `checkG60` (7,007);
`checkObj` rejects 4 of them (3 before: the stack check of a huge frame twice, `SBFIZ` not
modelled, and now `runtime.poll_runtime_pollUnblock`, a `JMP` whose target is not the Prog
`checkObj` expects). G61's 316 over G60 in `gen-check` are all functions, of any pipeline; among
the fully verified, a function whose first `checkG60` rejection was an atomic op is now rejected
by its next reason (`store shape` 358 → 381) or by `entryStoresOK` (19 → 28). `checkG61` accepts
7,035; 69 have a pending window, `entryStoresOK` rejects 28, 41 are end to end with a pending
window (stock column: 7,978, 76, 34, 42). Vacuous at `Addrs.fixed` (below): 20 of the 6,792
under `verified_mach` (stock 23 of 7,662), 7 of the 211 under `verified_mach_S` (stock 7 of 235).
The first rejection reasons of `checkG61` among the fully verified: `store shape` (381), `frame
variable off another base` (229), `op CALLtail` (164), then `branch shape`, `argument v# in
register #`, `load shape`, `op FMOVQload` (9 each); no atomic op is left among them. `checkObj`'s:
`JMP` to a register (12), the stack check of a huge frame (11).

| quick-v10, the composition on G60 (`agent/lift60b` on main 70f8f2ec: objatom #687, ZeroIdx #686, G59 #685, Zero2 #684, objbar #683, G58 #682), P0' in `checkG60` and `checkObj`, `--jobs 2` | pipeline output | share | stock `trim` |
| --- | ---: | ---: | ---: |
| … ∧ `checkG60` ∧ `entryStoresOK` | 6,748 | 72.58% | 7,638 |
| **end to end, `verified_mach` or `verified_mach_S`** | **6,745** | **72.55%** | 7,597 |
| … of which `needs48 = false`: `verified_mach` | 6,550 | 70.45% | 7,384 |
| … of which `needs48 = true`: `verified_mach_S` | 195 | 2.10% | 213 |
| … end to end, pipeline output identical to stock after `trim` | 5,729 | 61.62% | - |

The composition on G60 (G59 with G56's float constants, through G48's stack arguments and
results, G58 and G59; per function: `verified_mach` at the mode `false` for a function that does
not need G48's mode, `needs48 = false`, `verified_mach_S` in G48's mode, `outargs` at `SP`,
`hosp`, `SPInv`, the `CallOKS` family, `CallOKStk`, `CallPanicOKS`, `ICallPanicOKS`, for the 195
that do) counts 6,745 end to end (6,550 under `verified_mach`, 195 under `verified_mach_S`), 261 more
than the composition on G56 (6,484, main cdf73c37) and none fewer: a superset of the first lift to
G60 without G48's mode (6,524, `agent/lift60` on main ae9b2124), which was one of G56's. On the
tree before main's #683/#684 (`agent/lift60b` 3c64c72c: G59 on G58 and G48, main f1204bce with
a757b5c4) it counted 6,734 (7,867 fully verified, stock column 7,595); by the first slice
`gen-check` lists for each of the 210 over the first lift, 194 need G48 (stack arguments and
results: `hash/crc32`'s `Checksum`, `math.Asin`/`Atan`/…, `runtime.Callers`, `forEachP`'s
closures, …), 16 pass an earlier slice after main's changes since ae9b2124 (#681's `Zero` stores)
or the checks G58 and G59 share. With #684's two-store `Zero` (7,867 → 7,878 fully verified) 11
more are end to end (`fmt.(*fmt).clearflags`, `(*fmt).init`, `runtime.dumpint`, 8 closures of
`test/gcgort`); #683's `DMB`/`PRFM` adds none: of the 31 quick-v10 functions with one, none is end
to end. `checkG60` ∧ `entryStoresOK` accepts 6,748 fully verified functions and `checkObj` rejects
3 of them (`SBFIZ` not modelled, the stack check of a huge frame twice); stock column 7,597 (7,382
on the first lift). `checkG60` accepts 6,767; 59 have a pending window, `entryStoresOK` rejects 19,
40 are end to end with a pending window (stock column: 7,663, 66, 25, 41). The first rejection reasons of `checkG60` among
the fully verified are led by `store shape` (358), `frame variable off another base` (229),
`op CALLtail` (164), the atomic read-modify-write ops (`LoweredAtomicCas#Variant` 129, `…Add…`
107, `…Or…` 21, `…Exchange…` 19, `…And…` 16), `branch shape`, `load shape` and `op FMOVQload` (9
each), `argument v# in register #` (8, 183 before G48) and `SP access MOVDaddr` (7); `checkObj`'s
by the atomics' opcodes (`LDADDALW` 72, `CASALW` 71, `CASALD` 64, `LDADDALD` 48, `SWPALW` 10, …),
`JMP` to a register (12) and the stack check of a huge frame (11). `memTyL` and the P0' numbering
check are not among them. `gen-check` on the same tree: G60 7,667 (82.46%, as G59 on P0), 69 of
them loading a float constant on P0' (61 by G56). The tree on main 3672e208 (before #686) gave the
same end-to-end set, and so does main 544c0e3b (before #687): #687's atomics in `checkObj` move its
rejection reasons (now led by `CBNZ: CBZ` 162, `CASALW`/`CASALD` reading `R#` 71/64, `JMP` to a
register 12, the stack check of a huge frame 11) but no function end to end, since `checkG60`
rejects the atomic ops (`LoweredAtomic*`). `X27` across Progs in `checkObj` (objatom part B: the
atomics' `R27` readers, `Tab.ok27`, `X27At`) adds none either: `checkObj` alone 7,532 → 7,841
(stock column 8,729 → 9,124), end to end 6,745 (the same set), its rejections among the fully
verified now led by `JMP` to a register (12) and the stack check of a huge frame (11), no atomic
left (`checkG60` still rejects every function with an atomic op; slice G61).

**Vacuous at `Addrs.fixed`, per theorem** (#553). `gofv-ssa-opt --e2e` counts, for each end-to-end
function, the distinct frame operands of its accessed `Blk.local` variables (forgeable, with a
`NAME_AUTO`/`NAME_PARAM` operand; `Res.locals`). Under `verified_mach` (mode `false`) a function
with two or more has no `G49Env` at `Addrs.fixed` (`g49Env_fixed_apart`): 20 of the 6,792 on G61
(stock column 23 of 7,662; 20 of 6,550 on G60), for which `verified_mach_fixed` holds only
vacuously. Under
`verified_mach_S` (G48's mode) `SPInv` puts `outargs 0` at `SP`, so at `Addrs.fixed` `SP` is
`outargs 0`'s fixed base `2^62`, and `VarsAt49` would put a `Blk.local` variable `x` at
`2^62 + frameOff`, where `AddrAgree` asks `2^62 + x·2^24`: no frame operand within the
stack-variable limit is that (`g49Env_fixed_outSP`, witness `fixed_outSP_none` on
`secret_getStack`'s wrapper), so a function with one has none: 7 of the 211 on G61 (stock column 7
of 235; 7 of 195 on G60), for which `verified_mach_S_fixed` holds only vacuously.
`verified_mach_atSP` (at
`Addrs.atSP`) and `verified_mach_S_atSP` (at `Addrs.atSPO`, `outargs 0` at `SP`) hold of all of
them with a satisfiable activation premise.

**Functions with two or more `Blk.local` variables: vacuous at `Addrs.fixed`, not at the machine
layout** (#553; before G48's mode, see above). Of the functions counted end to end, those that access two or more `Blk.local`
frame variables at distinct operands have no `G49Env` at `Addrs.fixed` (§ slice G49), so
`verified_mach_fixed` holds of them only vacuously; `verified_mach_atSP` (§ whole functions) asks
no place of a frame variable at `Addrs.fixed` (`G28Env`) and holds of them non-vacuously at
`Addrs.atSP` (witness: `verified_mach_atSP_witness`, `secret_getStack`'s wrapper, every premise
discharged). Measured on main ae9b2124 with this change (#672; the composition on G56, `gofv-ssa-opt
--check --verified --e2e --jobs 2`, 337 s, with a throwaway count in `back` of the accessed
forgeable `NAME_AUTO`/`NAME_PARAM` variables of `liveCtx` of the pipeline output): 6,494 end to
end, of which 18 access two or more (the same 18 as on main 55116073): `main.safeDiv`
(`examples/defers`), `fmt.(*ss).Token`, `fmt.(*ss).doScan`, `regexp/syntax.dumpProg`,
`runtime.bytes`, `runtime.cgoCheckPointer`, the ABI0 wrappers `runtime.plugin_lastmoduleinit` (4),
`reflect_compiledTypelinks`, `reflect_typelinks`, `runtime_pprof_readProfile` (3),
`secret_getStack`, `time_now` (3), `time_runtimeNow` (3), `sync/atomic.(*Value).CompareAndSwap`,
`(*Value).Swap`, `main.cmp` (`test/bigmap`), `main.func5` and `main.func6` (`test/range4`); 194
access exactly one, 6,282 none. So all 6,494 are end to end under `verified_mach_atSP` with a
satisfiable activation premise, and the 6,476 with at most one also under `verified_mach_fixed`.

The composition on G56 (`agent/fconst` on main cdf73c37, G55 #669; G55's `VCNT`/`VUADDLV`/
`FRINT*`/shifted `NEG`/`CLZW`/`MULL`/`EXTR` and the float constants loaded from their read-only
symbols, P0'; `RoRun` from `memTyL` and `RoMem (constRo …)`) counted 6,484 end to end on the
pipeline output (7,845 fully verified; `checkG56` ∧ `entryStoresOK` 6,486, `checkObj` 7,499; stock
column 7,281; 5,503 identical to stock), as the composition on G54
(main e53604fc): no fully verified function needs G55's ops or a float constant load to pass, and
`checkObj` on P0' accepts 3 more fully verified functions (7,499), none of which `checkG56` with
`entryStoresOK` accepts. The stock column, where the float constants and G55's ops occur, goes
from 7,206 to 7,281 (`checkObj` 8,544 → 8,703, `checkG56` ∧ `entryStoresOK` 7,290 → 7,311).
`checkG56` accepts 6,502 fully verified functions; 49 of them have a pending window,
`entryStoresOK` rejects 16, 33 are end to end with a pending window (stock column: 7,329, 51, 18,
33). `memTyL` (required only of a function that loads a float constant) and the P0' numbering
check do not appear among the listed rejection reasons (the top 40). This table predates the
count above (main cdf73c37, before #670's two-store forms, which bring the end-to-end count to
6,494): its 6,484 include the functions with two or more `Blk.local` variables, for which
`verified_mach_fixed` is vacuous and `verified_mach_atSP` is not.

The composition on G54 (main e53604fc: through G52's remainders, G53's `LoweredMove` and G54's
loops; `G54Pre` in `RunPre`) counted 6,484 end to end, 201 over the composition on G49's 6,283
(main 74bf59ed, #662's `checkObj`): `checkG54` ∧ `entryStoresOK` accepted 6,486 fully verified
functions (+142 over `checkG49`'s 6,344), and `checkObj` with the morestack tail's F0–F15 spills
(#667) rejected 2 of them (the 2: `SBFIZ` not modelled, the stack check of a huge frame); stock
column 7,206.

On main 74bf59ed, with #662's `checkObj`, the composition on G49 counted 6,283 end to end (67.58%;
`checkG49` ∧ `entryStoresOK` 6,344, `checkObj` 7,427; 65.87%, 6,124, with main's
older `checkObj` on 1169f32c). The composition on G49 (frame variables in `Blk.local` blocks; the
entry stores) added 113 over G51's 6,011. `checkG49` accepts 6,359 fully verified functions; 48 of them have a pending window
(a register-assigned parameter in a `Blk.local` block that the function accesses), of which
`entryStoresOK` rejects 15 (`entry stores (#) do not cover the pending window`, e.g.
`runtime.(*Pinner).Pin`: no entry store at the head of the entry block) and 33 are end to end
(stock column: 7,142, 50, 17, 33).

The composition on G34 (#632) accepted 5,424 (58.34%), framed leaves excluded; on G37 with framed
leaves 5,538 (59.56%); on G38 (the acquire loads) the probe counted 5,802 (62.40%); on G39 (the
homes of removed values, #642) 5,853 (62.95%); on G40 (`InitMem` after the entry values, main
be69adb9) 5,874 (63.18%). On G41 (`CMNconst`, `CMPshift{LL,RL}`, main e24a029b, whose float loads,
#643, add 71 fully verified functions) it counted 5,931 (63.79%), G42 (`ANDconst` widening a
narrow argument) adds 19 (5,950), and G43 (`InitMem` at clean positions, main 71de6125) 7 (5,957).
On G44 (float moves, loads and stores) the count on main 833350fe stays 5,957: `checkObj` does not
model the `FMOVD`/`FMOVS` forms G44 accepts yet (SIMD&FP, 43 functions among the fully verified),
and on the stock column `retRegsOK` rejects 22 of the functions `checkG44` accepts. Main
c3414814 (#649, narrow left shifts in `lower`) adds 64 fully verified functions and 13 end to end
(5,970). The compositions on G45 (register-index float loads and stores) and G46 (float
arithmetic, conversions, compares, `FMADD`/`FNMSUB`; `FArithPre` in `RunPre`) stay at 5,970:
`checkG46` accepts 28 more fully verified functions than `checkG44` (6,086), every one of them
rejected by `checkObj`, which did not model the SIMD&FP forms (the binding constraint for floats
end to end). With `checkObj`'s SIMD&FP forms, register shifts, `UDIV`/`SDIV`/`REM`, `BIC`/`ORN`/
`EON`/`MVN` and the Q stores (#662; main 873c6ecf adds 11 fully verified functions) the
composition on G46 counted 6,084 end to end (5,970 before): `checkObj` rejected only 2 of the
6,086 functions `checkG46` accepts. The composition on G47 (calls with float arguments or
results; no new premise) had stayed at 5,970 with main's `checkObj`: `retRegsOK` rejected 27 of
the 6,146 functions `checkG47` accepted (`floating-point result`). With results in `F0`–`F15`
(`retArgOK`'s F branch, `ResultRel`'s V clause) and the composition on G50 (the narrow and float
pair loads; `PairPre50` in `RunPre`), `retRegsOK` rejected none of the 6,185 functions `checkG50`
accepted and 5,986 were end to end with main's `checkObj` (+16); the composition on G51 (cheap
ops; `Pre51a` in `RunPre`) added 25 (6,011). `ownFrame` gives the stock
`stksize`/`stkptrsize` on all fully verified functions whose output is identical to stock.
`pallocSum.start` (the witness `verified_mach_witness`) is among the accepted.

The full-v11 table below is the composition on G64 (main b26adfeb, #702; binary `gofv-ssa-opt`
built on `agent/lift64`, whose code is main's): per function `verified_mach` (`needs48 = false`)
or `verified_mach_S` (G48's mode), P0' in `checkG64` and `checkObj`. That binary predates the
driver's `entryVacuous` (#706), so the vacuity rows come from a second run, main aeb502b8's
driver over the 76,036 functions whose premises hold (the six parts' accepted lists in 29 chunks
of at most 3,000 files, `--jobs 2`, 7 h 32 min summed). Its verdicts agree with the first run's
on all 76,036 (fully verified, every premise holding on the pipeline output), and it finds 7,338
of them vacuous at the entry. The table predates `SBFIZ` in `checkObj` (#714).

| full-v11 (96,674 functions, in six parts, 14 h 1 min summed; composition on G64, main b26adfeb; vacuity: main aeb502b8's driver on the accepted lists; `--jobs 2`) | pipeline output | share | stock `trim` | share |
| --- | ---: | ---: | ---: | ---: |
| fully verified (Phase 2, through `trim`) | 84,855 | 87.77% | - | - |
| … genssa and `Flushplist` ran | 84,768 | 87.68% | 96,674 | 100.00% |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` | 76,136 | 78.75% | 83,720 | 86.60% |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` | 76,133 | 78.75% | 83,701 | 86.58% |
| … ∧ `checkObj` | 84,242 | 87.14% | 95,154 | 98.42% |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `checkObj` | 76,039 | 78.65% | 83,421 | 86.29% |
| … ∧ `checkG64` ∧ `entryStoresOK` ∧ `argsOK` ∧ `retRegsOK` ∧ `checkObj` (the premises hold) | 76,036 | 78.65% | 83,402 | 86.27% |
| … of them vacuous (closure context, `entryVacuous`: every variant) | 7,338 | 7.59% | - | - |
| **… premises hold, not vacuous (end to end, `verified_mach` or `verified_mach_S`)** | **68,698** | **71.06%** | - | - |
| … of which `needs48 = false`: `verified_mach` | 68,130 | 70.47% | - | - |
| … of which `needs48 = true`: `verified_mach_S` (G48's mode) | 568 | 0.58% | - | - |
| … end to end, pipeline output identical to stock after `trim` | 58,790 | 60.81% | - | - |
| fully verified, pipeline output identical to stock | 69,843 | 72.24% | - | - |

The stock column has no vacuity rows: the second run covers only the functions whose premises
hold on the pipeline output (on those, 7,336 of the 76,002 whose premises hold on stock are
vacuous). Before the vacuity audit, the premises hold of 83,402 stock functions (82,721 under
`verified_mach`, 681 under `verified_mach_S`).

The composition on G64 counts **68,698** end to end (71.06%; 68,130 under `verified_mach`, 568
under `verified_mach_S`). The premises hold of 76,036 (78.65%; 75,458 + 578), 807 more than on
the composition on G61, and none fewer: all of the G61 run's 75,229 are among them (`comm` of the
sorted accepted lists). 7,338 of the 76,036 are closures vacuous at the entry (7,328 under
`verified_mach`, 10 under `verified_mach_S`): in 4,286 an entry value comes after the start, and
3,052 load off the closure pointer. **Correction of the G61 count.** 7,314 of the 7,338 are
among the G61 run's 75,229, so the composition on G61 counts 67,915 end to end (70.25%), not
about 67,914 as the mirror estimated.

`checkG64` accepts 77,575 fully verified functions. 2,034 of them have a pending window,
`entryStoresOK` rejects 1,433, `argsOK` 6, and 600 have a pending window and hold before the
vacuity audit (stock column: 85,437, 2,253, 1,705, 12, 547). Vacuous at `Addrs.fixed`: 305 of
the 68,130 under `verified_mach` and 13 of the 568 under `verified_mach_S`; the `_atSP` variants
hold of all of them non-vacuously. `ownFrame` gives the stock `stksize`/`stkptrsize` on all
69,843 fully verified functions whose output is identical to stock.

Earlier: the composition on G61 (main e80f022b, #694, 10 h 48 min summed) 75,229 premises hold
(77.81%; 74,656 + 573), 67,915 end to end. On G60 (main 2320a5d3, #690) 73,268 premises hold
(75.78%). On G44 (main c3414814 plus #650) 67,896 (70.23%). On G34 (main 0d51e03e, framed
leaves excluded) 60,599 (62.68%). The G18 probe (stock locals, main 8c5b1472 plus #606) 28,813
(29.80%). The counts before G64 include the vacuous closures.

full-v11 runs as six invocations (`cmdmain`, `cmd/vendor`, the rest of `cmd` but `compile`,
`cmd/compile`, `stdall/std` in two halves), each at `--jobs 2` under `nice -n 10`, whose tables
are summed (`merge-parts.py`; the per-mode, pending-window and vacuity lines summed
separately). `cmd/vendor` took 5 h 52 min: `golang.org/x/arch`'s `ppc64asm.init` and
`s390xasm.init` alone took 5 h 25 min and 5 h 44 min. `cmd/compile` took 6 h 11 min, of which
`ssagen.simdAMD64Intrinsics` took 4 h 25 min. The machine was at load ~210, peak RSS 1.6 GB, with
no OOM kill. Top reasons among the fully verified (first reason; no part hit a table's cap):

- back-end errors: 87, all `Flushplist: PosTable.Pos: no position base`;
- `entryStoresOK`: 1,433, all `entry stores do not cover the pending window`;
- `retRegsOK`: 3 (`result of class # read at class #`);
- `checkG64`: `store shape` (4,308), `op CALLtail` (1,425), `MOVDnop/MOVDreg: upper bits unknown`
  (267), `SP access MOVDaddr` (186), `pair store shape` (175), `op CALLtailinter` (144),
  `branch shape` (140), `load shape` (119), `two frame variables overlap` (84), `bounds panic:
  constant index outside` (65), `argument v# in register #` (59), `Arg width` (53),
  `op LoweredGetCallerSP` (48). G61's `FLDPQ`/`FMOVQload` reasons are gone (G64);
- `checkObj`: `JMP` to a register (169), `SBFIZ` not modelled (162; #714 since), `RET` through
  another register (144), a branch whose target is not the Prog `checkObj` expects (24), the
  stack check of a huge frame (20), a Prog writing `R#` (6). Among the functions `checkG64`,
  `entryStoresOK`, `argsOK` and `retRegsOK` accept, `checkObj` rejects 97: `SBFIZ` (72), the
  stack check of a huge frame (13), and a branch whose target is not the Prog `checkObj` expects
  (12).

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
witnesses). `verified_mach_fixed` and `verified_mach_atSP` take `verified_mach`'s assumptions, at
`Addrs.fixed` and at `Addrs.atSP` (where `G28Env` at `Addrs.fixed` replaces `G49Env`); the latter
adds none. `verified_mach_S` (G48's mode, for a function that needs it, `needs48`) takes the `S`
rows of the callee contracts (`CallOKS` …, `CallOKStk`, `CallPanicOKS`, `ICallPanicOKS`) in place
of those without `S`; `verified_mach_S_fixed` and `verified_mach_S_atSP` (at `Addrs.atSPO`) take
its assumptions:

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
| `RoMem (constRo (symNames g)) (addGlobals e mem)` (Phase 3 §10, premise `hro` of `verified_mach` and `verified_mach_fixed`; with `memTyL lc = true`, `hmt`, and `Env.KeepsRo` from `RoImage` it gives `RoRun` by `lreach_roMem`, `RoPre56` of `g56_value` at every reached state) | the input memory has, for each float constant symbol `$f64.<bits>`/`$f32.<bits>` among the Prog list's symbols (`G2In.syms` of P0'), a read-only allocation at `Blk.global` of that name holding the bits little-endian (`constSymAlloc?`); with `EntryMatch`'s `MemInj` and `G2Env.glob`, the machine's memory holds those bytes at the symbol's linked address on entry | `ctxt.Float64Sym`/`Float32Sym` (`cmd/internal/obj/sym.go:163-191`) make an `SRODATA`, local, content-addressable symbol whose contents are the bits its name spells (`asm-parity` checks the port's against Go's, `Cmp.data`); the linker lays it out in read-only data and the loader maps it read-only, so the loaded image holds those bytes at the symbol's address and no store reaches them. Phase 1's export image has no assembler symbols (`addGlobals` adds none), so the premise is on the input memory: an assumption about the linker and loader, not the compiled code; it has `RoImage`'s image-part form (equivalently `RoImage (ro ++ constRo …)`) | a linker or loader that places other bytes at the symbol's address, or maps it writable and writes it before or during the call | a property of the inputs (the loaded image); `verified_mach_witness` (no constant symbol, `constRo` empty), `genG56_witness` (`RoPre56` from a memory holding `$f64.7ff0000000000000`) |
| `env.FrameKeep` (`VPre`) | contracts keep the caller's frame allocations and return no memory | callees do not free their caller's frame | a contract that drops the caller's frame | `Env.runtime_frameKeep`, `Env.p1_frameKeep` |
| `env.AllocZero` (`VPre`) | malloc-family contracts asked for a positive size return a fresh all-zero heap block (size 0 returns `runtime.zerobase`, about which nothing is claimed) | the allocator's contract | a non-zeroed or aliased allocation | `Env.runtime_allocZero`, `Env.p1_allocZero` |
| `env.GrowLen` (`VPre`) | `runtime.growslice`/`growsliceNoAlias`, if present, return a slice of their `newLen` argument | the runtime's contract | another length | `Env.runtime_growLen`, `Env.p1_growLen` |
| `env.IfaceEq eq` (`VPre`, `eq = Verified.pipelineEq env`; `RwPre`, `eq = RewriteCheck.eqPass tabs fe`) | `runtime.ifaceeq` on (a word pointing at the start of) an itab symbol of `eq.1`, and `runtime.efaceeq` on a type symbol of `eq.2`, if present, return `[PtrOps.eqPtr false [x, y]]` (the pointer equality of their data words) and the memory they were given; `eq` holds the itab and type symbols of the input's tables and the frontend's tables whose type the export marks direct-interface and comparable (`types.IsDirectIface`, `types.IsComparable`) | the runtime's code, `third_party/go/src/runtime/alg.go`: `efaceeq(t, x, y)` returns `true` for a nil `t`, panics if `t.Equal` is nil, returns `x == y` if `t.IsDirectIface()`, else `eq(x, y)`; `ifaceeq(tab, x, y)` is it with `t := tab.Type`. A comparable type has an `Equal`, a non-nil symbol is no nil descriptor, so both return `x == y` and write nothing (`generic.rules:2279`/`:2287` fold them so) | an export whose direct/comparable flags disagree with the runtime type's `TFlagDirectIface`/`Equal`, or a runtime that writes memory or panics there | `Env.runtime_ifaceEq`, `Env.p1_ifaceEq` (absent), `Env.ifaceEqDemo_ifaceEq` (present) |
| `NoNilFault tabs f env args mem` (`r.nnf`) | no run of the `schedule` input faults in the nil page or checks a wild pointer (`runL` and `runLF` agree) | `schedule`'s theorem is stated against `runLF` (memory ops fault), the passes before it against `runL`; this restricts the end-to-end statement to such inputs | — (a restriction, not a claim about Go) | `noNilFault_of_noAct` (witnesses) |
| `ArgPtrsOK tabs f env args mem` (`r.nnf`) | every pointer-shaped register piece of a parameter (`ArgIntReg` at a `.ptr` shape) reads nil or a pointer that is not wild (`Ptr.wild`: into the nil block but not nil) | Go-level: Go's type system and the garbage collector require a pointer parameter to be nil or valid; `unsafe` code that forges a wild pointer is outside the model. `swapOKB`'s `argPtr` case moves a nil check of such a piece before a fault on the same memory: it panics alike or passes, where a wild pointer would leave it `stuck` | a caller passing a forged pointer (an integer address, or nil plus an offset) as a pointer argument | `argPtrsOK_of_none` (witnesses) |
| `NilPtrsOK tabs f env args mem` (`r.nnf`, approved on #385) | in every state `runLF` of the `schedule` input reaches (a block entry, after its `Phi`s and any prefix of its order), every pointer-shaped value that a nil check checks reads nil or a pointer that is not wild, once it has a register (`NilRegsOK`) | Go-level, as `ArgPtrsOK`: a Go pointer is nil or points into an allocated object (the `unsafe.Pointer` rules); the runtime throws on a pointer in the nil page (`runtime/stack.go:676`, "invalid pointer found on stack", `0 < p < minLegalPointer`). Only checked pointers: a compiler-made `nil + k` may be computed before the check of its base panics. `nilPtrSwap` moves such a check before a fault on the same memory | a function that loads, converts or receives a forged pointer and nil-checks it (`unsafe` misuse) | `nilPtrsOK_of_none` (witnesses: `clampL_noNilPtr`, `pfF_pipeline`'s `noNilPtrB`) |
| hook `liftContract` (Phase 3, `GoFV/SSA/Sem/Hooks.lean`, `rtHookNamed`) | a call of a runtime entry point with a Phase 1 contract (`Env.runtime`) behaves as that contract lifted through ABIInternal: arguments read from their `abi.RegIndex` registers and `SP + offset` stack slots (or `fixedABI`'s registers for `LoweredMemEq` → `runtime.memequal`), memory pulled back and pushed forward through `ι`, results written to their ABI locations, `R0`–`R17`, `R19`–`R27`, `V0`–`V31` and the flags clobbered, `SP`, `R18`, `R28`–`R30` and every byte the contract does not write kept; returns to `X30` | the contracts carry the Phase 1 assumptions above; the ABI is Go's `ABIInternal` for arm64 (`cmd/compile/internal/abi`, `internal/abi`); every allocatable register is caller-saved there. Agreement with native: `mach-difftest`, 9,480/9,480 calls | a runtime routine that keeps a value in a clobbered register the caller relies on, writes memory its contract does not, or changes `R28`/`SP`; a proof that depends on the fixed `garbage` values (they stand for arbitrary values) | trusted (no theorem uses it yet) |
| hook `morestackHook` (`runtime.morestack`, `runtime.morestack_noctxt`) | the stack grows in place (`δ = 0`): `stackguard0` lowered by `growBy`, not below `stack.lo + StackGuard`; resumes after the `BL` with `X30` = the saved `R3`, `SP`, `R28`, `R29` kept, `R26` kept at `runtime.morestack` and `0` at `runtime.morestack_noctxt`, the rest clobbered; stuck when the stack cannot grow | `runtime/asm_arm64.s` `morestack` → `newstack` → `gogo`: `morestack` saves `R26` in `g.sched.ctxt` (`:449`) and `gogo` restores it (`:269`); `morestack_noctxt` is `MOVW $0, R26; B runtime·morestack` (`:493-502`; until #708 the model kept `R26` there too); a moved stack (`δ ≠ 0`) is outside the model (semantics3 §6, §10) | a run that needs a stack move (`copystack`) to agree with native | trusted |
| hook `wbHook` (`runtime.gcWriteBarrier<n>`) | returns the write-barrier buffer (`8n` bytes at `RtInfo.wbuf`) in `R25`; `R27` and the flags clobbered, every other register kept | `runtime/asm_arm64.s` `gcWriteBarrier`; Phase 1's `WbPre` protocol (row above) | a buffer flush that changes other registers or memory the code reads | trusted |
| hook `panicBoundsHook` (`runtime.panicBounds`) | panics with `.bounds kind x y` decoded from the caller's `PCDATA_PanicBounds` at `X30 − 1` (`pcvalue`, `abi.BoundsDecode`), `x`/`y` from `R0`–`R15` or constants (`boundsPanic`; the kind `2·code`, `+1` when unsigned, and `BoundsConvert`, code 8, kind 16 = `ssa.BoundsConvert`, `cmd/compile/internal/ssa/op.go`) | `runtime/panic.go:211-236` `panicBounds64`, `internal/abi` `BoundsDecode` | a runtime whose decoding differs | trusted |
| `runMach` nil page (`GoFV/SSA/Sem/RunMach.lean`) | a load or store in `[0, 4096)` is `panicked nilDeref`; no other address faults | the kernel leaves the nil page unmapped; SIGSEGV there becomes `sigpanic` → `panicmem` | an access fault outside the nil page that the code relies on | trusted |
| `GoFV.Arm64` single core | exclusive stores always succeed, barriers advance the PC; `DMB`/`DSB`/`ISB` are no-ops because of it (they only order memory accesses between observers, and one core has none), and so is `checkObj`'s `DMB` (`progSymCore`); `PRFM` is a no-op independently of it (a hint with no architectural effect on registers or memory, Arm ARM C6.2 `PRFM`). `checkObj` relies on it for the exclusive accesses: `LDAXR*` is a plain load, `STLXR*` a store with status 0 on both sides (`symExcl`, `atomP`, as `execExcl` and `progEffect`); the LSE single instructions (`CASAL*`, `LDADDAL*`, `LDCLRAL*`, `LDEORAL*`, `LDORAL*`, `SWPAL*`) are one load and one store, with no other observer in between. Genssa slice G61 relies on the same row and nothing more: `progStep_stlxr` (`Progs61.lean`, from `progEffect`) leaves `R27 = 0`, so each load-exclusive/store-exclusive loop's `CBNZ R27` falls through and the loop runs once (`xchg_run`, `add_run`, `logic_run`, `cas_run`); `progStep_lse`/`progStep_casal` are one load and one store; on the SSA side `runLoc`'s generic `Atomic.rmw`/`Atomic.cas` are one read-modify-write of the memory | one goroutine, one core, as Phase 2 §8 | a multi-threaded observation (another core's store between an `LDAXR` and its `STLXR`, which would fail it) | trusted |
| `CallOK`/`CallSpec` (Phase 3 G2 and G3, `GoFV/Proof/Gen/G2.lean`, premise of `g2_value` and `g3_value` at each static call) | from the state at the callee's symbol (the caller's but for `X30`, the return address), with the call's arguments in their ABI registers and the memory injected, the hook `H.call` returns to `X30` with `SP`, `R28`, `R29` and the frame (saved `LR`/`FP`, spill slots: `StkAt`) kept, `runLoc`'s memory after the call injected by an extension of `ι` that keeps the live blocks away from the frame, and `runLoc`'s results in the ABI result registers | the callee's Phase 1 contract lifted through ABIInternal (semantics3 §6, the `liftContract` row above); Go's calling convention keeps `R28`/`R29`/`SP` and the caller's frame. Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a callee that writes the caller's frame or spill slots, returns elsewhere, or whose results differ from `runLoc`'s | trusted; the witness `genG2_value_witness` discharges it for a callee that returns at once |
| `CallOKZ` (Phase 3 G15, `GoFV/Proof/Gen/G15.lean`, premise of `g15_value` at each static call) | `CallOK`'s contract (`CallAt`) at a static call whose ABI, without its zero-sized stack inputs, has the register arguments and results `callRegsZ` gives | as `CallOK`: a zero-sized stack input passes no byte, so the callee's Phase 1 contract lifted through ABIInternal is the same. Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | as `CallOK` | trusted; the witness `genG15_value_witness` discharges it for a callee that returns at once |
| `WbOK`/`WbSpec` (Phase 3 G8, `GoFV/Proof/Gen/G8.lean`, premise of `g8_value` and every later slice's `gN_value` at each write-barrier request `LoweredWB [n]`) | from the state at `runtime.gcWriteBarrier<n>`'s symbol (the caller's but for `X30`), with the memory injected, the hook `H.call` returns to `X30` with `SP`, the memory and every register but `X25` and `X27` kept, `X25` the address of the buffer under an extension of `ι` that maps the block `wbuf` there and injects `runLoc`'s memory with a fresh `8n`-byte buffer (`Mem.wbAlloc`), the live blocks away from the frame | the hook `wbHook` (row above): `runtime/asm_arm64.s` `gcWriteBarrier` returns `8n` bytes of the per-P buffer in `R25`, clobbering only `R27` and the flags; the layout puts the buffer (`RtInfo.wbuf`) apart from the live blocks and the stack. Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a buffer that overlaps a live block or the frame, or a flush that changes other registers or memory | trusted; the witness `genG8_value_witness` discharges it for a hook that is `wbHook` with the buffer at `2^41` |
| `ICallOK` (Phase 3 G10, `GoFV/Proof/Gen/G10.lean`, premise of `g10_value` and every later slice's `gN_value` at each interface or closure call `CALLinter`/`CALLclosure`) | from every state that is the caller's but for `X30`, with the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), the register arguments in their ABI registers and, at a closure call, `R26` holding the closure context: that address is no Prog address of the caller and not its return address, and the hook there satisfies `CallSpec` (the static callee's contract, the `CallOK` row above) | Go's internal ABI: the code pointer of a method (an itab's `fun` entry) or of a closure (its first word) is the entry of a function linked outside the caller's code, which the hook runs by its Phase 1 contract (`callTarget` names the callee by the code pointer); a closure call passes its context in `R26` (abi-internal.md: the closure context pointer register). Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a code pointer into the caller's own code (a recursive call through a function value, which the hook model does not run; lifting this needs the function-level callee contract of `docs/plans/proofs3.md` §6), or a callee that breaks `CallSpec` | trusted; the witness `genG10_value_witness` discharges it for a callee that returns at once at a global function's address |
| `CallOKS`/`CallSpecS`, `CallOKZS`, `ICallOKS`, `WbOKS`/`WbSpecS`, `MemEqOKS`/`MemEqSpecS` (Phase 3 G48b; `GoFV/Proof/Gen/G2.lean`, `G15.lean`, `G10.lean`, `G8.lean`, `G28.lean`; selected by the mode `w` of `CallOKAt w`, `CallOKZAt w`, `ICallOKAt w`, `WbOKAt w`, `MemEqOKAt w`, which at `w = false` are the rows above verbatim; premises of `g53_valueS` (`GoFV/Proof/Gen/G53S.lean`), and of `g53_value`/`g54_value`/`g55_value`/`g57_value` at the mode `true`, in a function whose `outargs` block sits at `SP`, `MatchEnv.outSP`; from the lift to G60, in `RunPreS` (`RunPreM true`), premises of `obj_whole_ret`/`obj_whole_panic` at the mode `true` and of `verified_mach_S`, for a function that needs G48's mode (`needs48`); `verified_mach` takes the rows without `S`) | each the contract of the row of its name without `S`, with `SepFromW` in place of `SepFrom` in its premise and, where it has one, its conclusion: a live block's byte in the frame `StkAt E` lies below `Blk.writableFrom` and is `poison` (the caller's `outargs` word at `0(SP)`, which holds its saved `LR`); the frame `StkAt E`, that word included, is kept | as the rows without `S`; and no callee writes its caller's `0(SP)` word. The callee's prologue (`cmd/internal/obj/arm64/obj7.go:589-684`) saves its own `LR` and `FP` strictly below the caller's `SP`: a small frame by `MOVD.W R30, -aoffset(RSP)` then `MOVD R29, -8(RSP)` (`obj7.go:662-683`), a large one by `SUB $autosize, RSP, R20`, `STP (R29, R30), -8(R20)`, `MOVD R20, RSP` (`obj7.go:598-633`); its split check passes `LR` in `R3` to `runtime.morestack` (`MOV LR, R3`; `BL runtime.morestack`, `obj7.go:261-290`), which saves the caller's state in `g.sched`/`m.morebuf` (`runtime/asm_arm64.s:444-449`, `465-468`) and switches to the `g0` stack before it writes a frame (`asm_arm64.s:481-487`); `runtime.systemstack` (`asm_arm64.s:333-390`) likewise switches stacks (`MOVD R3, RSP`, line 375). Go's stack arguments and results start at `FixedFrameSize = 8` (`cmd/internal/sys/arch.go:136`; `offsetForLocals`, `cmd/compile/internal/ssa/config.go:387-388`; `cmd/compile/internal/abi/abiutils.go:318`), so a Phase 1 callee writes none of the word either (`Mem.write` needs `off ≥ Blk.writableFrom`). Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a callee or runtime routine that writes its caller's `0(SP)` word, or the falsifiers of the rows without `S` | trusted; `OutSP.callOKS_noCall` discharges `CallOKAt true` at a value that is no call; no witness runs a call with `outSP` yet (the G48 slice) |
| `CallOKStk` (Phase 3 G48, `GoFV/Proof/Gen/G48.lean`, premise of `g48_value` at each static call whose ABI assigns inputs or outputs to the stack, in a function whose `outargs` block sits at `SP`; in `RunPreS`, premise of `obj_whole_ret`/`obj_whole_panic` at the mode `true` and of `verified_mach_S`, from the lift to G60; not of `verified_mach`) | `CallOKS`'s contract (`CallAtM true`: `CallSpecS`) at the register arguments and results of the ABI without its stack-assigned parameters (`callRegsS`): from the state at the callee's symbol, with the stack arguments the caller stored at `8(RSP)` and up in the injected memory, the hook returns to `X30` with `SP`, `R28`, `R29` and the frame `StkAt E` (the caller's saved-`LR` word at `0(SP)` included) kept, `runLoc`'s memory after the call (stack results written into `outargs` by `encodeResults`) injected by an extension of `ι` under `SepFromW`, and the register results in their ABI registers | the `CallOKS` row; Go's arm64 ABI places stack parameters from `FixedFrameSize = 8` above the caller's `SP` (`cmd/internal/sys/arch.go:136`; `cmd/compile/internal/abi/abiutils.go:318`, `stackOffset` from `offsetForLocals`), where the callee reads its arguments and writes its results (`runtime/asm_arm64.s:590-597`: `CALLFN` copies stack arguments to `8(RSP)`); the callee's prologue saves `LR`/`FP` below the caller's `SP` (`cmd/internal/obj/arm64/obj7.go:589-684`); Phase 1's `decodeArgs`/`encodeResults` read and write the same offsets of `outargs`. Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a callee that writes the caller's `0(SP)` word or bytes of `outargs` outside its results, or an ABI whose stack offsets differ from `ABIParam.offset` | trusted; `GenG48.callOKStkC` discharges it for a callee that returns at once (`GenG2.H0`) at `runtime.exit`'s stack-argument call, which `genG48_call_witness` steps |
| `ArgOK` (Phase 3 G62, `GoFV/Proof/Gen/G62a.lean`, premise of `g62_value` and `g64_obj_value` at each value, at either mode; **discharged in the composition on G62**: no premise of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`, `verified_mach_S`) | at an `Arg {x} [off]` homed in its slot `k` (`argKey x type off`, with a `NAME_PARAM` operand at frame offset `o`; `x` an input parameter the function's ABI assigns to the stack, `stackParam`), the machine's bytes at `SP + o` hold `argVal`'s piece `off` of `x`'s image at the value's shape as a spill slot holds a value (`SlotRel`); vacuous at every other value | its caller-side content is now the stack clause of the entry condition (`EntryMatch.stack`: the `EntryMatch`, `EntryEnv` row below, with the ABI0 citations) | as the stack clause | **discharged** in the composition: the `Arg`s run before the start `k` with the entry values (`entryLen`; neither emits code, so nothing writes the caller's bytes before `k` but the prologue, below the entry `SP`), their slots are related at the entry by `EntryMatch.stack`, and no `Arg` runs after `k` (`argsOK`'s `argsBefore`, checked), so `ArgOK` holds vacuously at every state the run reaches (`NoArgRun`, `noArgRun_of_argsBefore`, `GoFV/Proof/Obj/Whole.lean`); for the slice alone, `GenG62.argOK0` discharges it for `genG62_witness`'s machine state `m0` by compiled evaluation (`argFacts`, in `g62_facts`) |
| `CloOK` (Phase 3 G11, `GoFV/Proof/Gen/G11.lean`, premise of `g11_value` and every later slice's `gN_value` at `LoweredGetClosurePtr`) | at `LoweredGetClosurePtr`, which `checkG11` places in the entry block after the register arguments only (`cloFirst`; no code but the prologue runs before it), `X26` holds the activation's closure context (`fr.closure`, `poison` outside a closure call), a 64-bit word | Go's internal ABI passes the closure context in `R26` (abi-internal.md; semantics3 §5); the prologue does not write `R26` and its `morestack` path saves and restores the context (`runtime.morestack`, `gobuf.ctxt`); the register arguments emit no code | a caller that enters a closure without its context in `R26`, or a prologue that clobbers `R26` | trusted; the witness `genG11_value_witness` discharges it for a closure context that is a pointer to a global at `2^40` |
| `GetGOK` (Phase 3 G17, `GoFV/Proof/Gen/G17.lean`, premise of `g17_value` at `GetG`) | the injection `ι` maps Phase 1's opaque global `runtime.g` (`GetG`'s result, `Sem/Pure.lean`) to the activation's goroutine `E.g`, which `LocMatch`'s frame clause puts in `X28`; `E.Extends` keeps it, so it is a property of the activation's first injection | Phase 1 models the goroutine as an opaque allocation of the environment, never nil (semantics2 §5); on arm64 the goroutine pointer lives in `R28` (`g`), which Go code does not write outside the runtime's `g` switches | a `runtime.g` symbol referenced as a global (then `G2Env.glob` puts it at its link address), or code that switches `g` | a choice of `ι`, not of external code; the witness `genG17_value_witness` takes `ι` with `runtime.g` at `X28` |
| `BoundsOK` (Phase 3 G19, `GoFV/Proof/Gen/G19.lean`, premise of `g19_boundsPanic`, …, `g42_obj_boundsPanic`, `obj_whole_panic` and the panic branch of `verified_mach`) | from every machine state at the symbol of `runtime.panicBounds` whose `X30` is the return address of a `CALL` at index `k` of the Prog list, the hook `H.call` panics with `boundsPanic c` of the state's registers, `c` the `PCDATA_PanicBounds` value in force at that `CALL` (`pbData`) | the hook's contract `panicBoundsHook` (row above): `panicBounds64` decodes the PC-value table at `X30 − 1`, which is `c` | a runtime whose `panicBounds` reads other registers or another table, or a PC-value table that the assembler does not emit as the Prog list says (D7, `checkObj`) | trusted; the witness `genG19_boundsPanic_witness` discharges it for a hook that panics with `boundsPanic 350`, the only value at its `CALL` (`boundsOK_of`) |
| `MemEqOK`/`MemEqSpec` (Phase 3 G28, `GoFV/Proof/Gen/G28.lean`, premise of `g28_value` at each `LoweredMemEq`) | from the state at `runtime.memequal`'s symbol (the caller's but for `X30`), with `X0`, `X1`, `X2` related to the arguments `p`, `q`, `n` `runLoc` reads and the memory injected (distinct keys, the live blocks away from the frame), the hook `H.call` returns to `X30` with `SP`, `R28`, `R29` and the memory kept, and `X0` related to `memEq [p, q, n, mem]`: 1 if the `n` bytes at `p` and at `q` agree, 0 if not (no claim when a read is invalid or reads `poison`) | `runtime.memequal`'s contract: `internal/bytealg/equal_arm64.s` (`NOSPLIT`, `NOFRAME`) compares the `R2` bytes at `R0` and `R1`, writes no memory, and returns with `MOVD $1, R0` or `MOVB ZR, R0` (the whole register 1 or 0); the injection relates `runLoc`'s bytes at `p`, `q` to the machine bytes at their addresses, so equal bytes are equal machine bytes and conversely. Since slice G66 the protected spill-slot window (`StkAt`) is the slot's size; identical to before for 8-byte-slot functions (`StkAt_eq_of_slots8`); faithful because callees never write the caller's spill slots | a `memequal` that writes memory or `R28`/`R29`, or returns another result | trusted; the witness `genG28_value_witness` discharges it for a hook that implements `memequal` on the machine (`GenG28.Hm`), on 8 equal bytes |
| `HookMap` (Phase 3 `checkObj`, `GoFV/Proof/Obj/Sim.lean`, premise of `obj_step`/`obj_star`, `g7_obj_value`/`g7_obj_term`, `g64_obj_value`/`g64_obj_term`, `obj_whole_ret`, `obj_whole_panic` and `verified_mach`) | a hook (callee, runtime entry) that returns from a P0 state at a symbol, after a call whose return address is a Prog or the end, also returns from every `ObjRel`-related machine state, to a related state at the P0 state's `X30` (next row): it treats the return address `X30` only as an address to return to (P0's ID layout and the machine's byte layout differ only there) and does not read `X27` | the callee's code is outside the function and cannot observe where the caller's words are, except through `X30`, which it only returns to (`RET`); Go code does not read `R27` (REGTMP) across a call | a callee that reads or stores its return address as data (tracebacks, `runtime.Callers`), or reads `X27` | trusted; `hookMap_retLR` discharges it for callees that return through `X30` and change nothing else (the witnesses' `GenG2.H0`), `hookMap_H` for the `ObjEndToEndAtSP`/`ObjEndToEndAtSPS` callee |
| `HookMap` returns to `LR` (Phase 3 `checkObj`, `Sim.lean`: `HookMap`'s conclusion `s'.pc = s.x 30`, used by `obj_step` for `X27At`'s `ret27`: after a call `checkObj` relies on `X27` at no Prog the return address names, `Tab.ok27`, so a hook may return with any `X27` but must land on that Prog) | a hook that returns from a P0 state at a symbol returns to that state's `X30`, the return address of its `BL`/`BLR` | the arm64 `BL`/`RET` ABI: a callee returns with `RET` to `LR`. The modelled hooks (`GoFV/SSA/Sem/Hooks.lean`): the three that return set `pc := s.x 30` (`liftContract`, `morestackHook`, `wbHook`), `panicBoundsHook` only panics; `runtime.morestack` is moreover under `MorestackOK` (returns to `X30`; the tail is no P0 Prog, and `checkObj` relies on `X27` at neither the `TEXT` nor the first body Prog, `ok27_spec`), panicking callees under the `CallPanicOK` family (no return); recovery is outside the model: no hook for `deferproc*`, `deferreturn`, `gorecover`, so a run reaching them is `stuck` (row "not modelled by the hooks") | recovery resuming at `deferreturn` (after a `recover`, Go resumes the frame at its `deferreturn` call, not at the panicking call's return address), or any routine that does not `RET` to `LR` (a `gogo` to another PC) | `hookMap_retLR` (`GenG2.H0`: the `ObjG7`, `ObjWhole`, `ObjWholeS`, `ObjWholeNL`, `ObjPanic` witnesses), `hookMap_H` (`ObjEndToEndAtSP`, `ObjEndToEndAtSPS`); trusted for `RtInfo.hooks` (every `.ret` hook sets `pc := s.x 30`) |
| `HookPanicMap` (Phase 3 `checkObj`, `Sim.lean`, premise of `obj_panic`, `g42_obj_nilPanic`/`_memPanic`/`_ldarPanic`/`_boundsPanic`/`_callPanic`/`_icallPanic`, `obj_whole_panic` and the panic branch of `verified_mach`) | a hook that panics from a P0 state at a symbol (after a call) panics with the same panic from every `ObjRel`-related machine state | as `HookMap` | as `HookMap` | trusted; `hookPanicMap_H0` (`objWhole_panic_witness`) |
| `CallPanicOK` (Phase 3, `GoFV/Proof/Obj/CallPanic.lean`, premise of `g42_callPanic`/`g42_obj_callPanic`; in `RunPanicPre`, premise of `obj_whole_panic` and the panic branch of `verified_mach`, at each static call whose step panics) | from every machine state at the callee's symbol that is the caller's but for `X30`, with the call's arguments in their ABI registers and the memory injected (`CallOK`'s premises, distinct keys, the live blocks away from the frame), the hook `H.call` panics with the panic `runLoc`'s call step panics with | the callee's Phase 1 contract lifted through ABIInternal (the `liftContract` row above): a callee that panics in Phase 1 on these arguments and memory panics alike on the machine, before returning | a callee whose machine code panics with another value, or returns, where its Phase 1 contract panics | trusted; the witness `g42_callPanic_witness` discharges it for a hook whose callee panics with `nilDeref` (`fint64to32`) |
| `ICallPanicOK` (Phase 3, `GoFV/Proof/Obj/CallPanic.lean`, premise of `g42_icallPanic`/`g42_obj_icallPanic`; in `RunPanicPre`, premise of `obj_whole_panic` and the panic branch of `verified_mach`, at each interface or closure call whose step panics) | from every machine state that is the caller's but for `X30`, with the PC the content of the code register `Rn` (related to `runLoc`'s code pointer), `R26` holding the closure context of a closure call, the remaining register arguments in their ABI registers and the memory injected, the callee's code is no Prog of the caller and not its return address, and the hook there panics with the panic `runLoc`'s call step panics with | as `ICallOK` (the code pointer of a method or closure is a function entry outside the caller) and `CallPanicOK` (the callee's Phase 1 contract lifted through ABIInternal panics alike) | a callee whose machine code panics with another value or returns where its Phase 1 contract panics; a code pointer into the caller | trusted; the witness `g42_icallPanic_witness` discharges it for a hook that panics with `nilDeref` at the callee's code (`Locker.Lock`, `icallPanicOKc`) |
| `CallPanicOKS`, `ICallPanicOKS` (Phase 3, the lift to G60, `GoFV/Proof/Obj/CallPanic.lean`; selected by the mode `w` of `CallPanicOKAt w`, `ICallPanicOKAt w`, which at `w = false` are the two rows above verbatim; premises of `g61_callPanic`/`g61_icallPanic` at the mode `true` and, in `RunPanicPreS`, of `obj_whole_panic` at the mode `true` and the panic branch of `verified_mach_S`, at each call whose step panics, for a function that needs G48's mode (`needs48`: its `outargs` block sits at `SP`); not of `verified_mach`) | each the contract of the row of its name without `S`, with `SepFromW` in place of `SepFrom` in its premise (a live block's byte in the frame `StkAt E` lies below `Blk.writableFrom` and is `poison`: the caller's saved-`LR` word at `0(SP)` is the first of its `outargs` block); `CallPanicOKS` at the ABI registers of `callRegsZ` or of `callRegsS` (a static call with stack arguments or results, G48's `callKind48`; the stack arguments in the injected memory) | as `CallPanicOK`/`ICallPanicOK`: the callee's Phase 1 contract lifted through ABIInternal; the `outargs` block's first word is the callee's to overwrite, which `SepFromW` leaves `poison` | a callee whose machine panic differs from its Phase 1 panic, or that writes the caller's frame (`StkAt`, the saved `LR`) before panicking | trusted; `g60_callPanicS_witness` (`CallPanicOKS` of `Hp` at every state) |
| `ICallOut` (Phase 3 `checkObj`, `Sim.lean`, run premise of `obj_star` (and `obj_step` at the state), `g7_obj_value`/`g7_obj_term`, `g42_obj_*`; as `∀ u, ICallOut L ps u` of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | at a `CALL (Rn)` on the P0 run, the register holds a linked symbol's address (a function value's code word, an itab's `fun` entry is a function entry) | Go's function values and itabs point to function entries (data relocations `R_ADDR`, proofs3 §6) | a function value pointing into the caller's own words or to a non-entry address | trusted per run; `iCallOut_of_none` discharges it for a list without `CALL (Rn)` (the ObjG7, ObjWhole, ObjWholeNL, ObjPanic and ObjEndToEnd witnesses) |
| `MachEntry` (Phase 3, `GoFV/SSA/Sem/RunMach.lean`, `GoFV/Proof/Obj/Frame.lean`; premises of `obj_entry`, `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | the call: PC at the entry, `SP` 16-aligned with room for the frame, `X30` outside the code, `g` above the nil page (its 32 bytes below `2^64`), `R29 = SP − 8` | the caller's side of the ABI (`obj7.go`) | a caller that enters with a misaligned `SP` or a return address in the callee's code | `objFrame_entry_witness`, `objFrame_morestack_witness`, `objWhole_ret_witness`, `objWholeNL_ret_witness`, `objWhole_panic_witness`, `verified_mach_witness` |
| `MorestackOK` (Phase 3, `GoFV/Proof/Obj/Morestack.lean`; premise of `more_loop`, `obj_entry`, `sim_entry`, `obj_whole_ret`, `obj_whole_panic`, `verified_mach`, for a function with a stack check, at the address of the morestack tail's call `tailCall`, with a context `ctxt`: `live26 sI` in `sim_entry`/`obj_whole_*`, `ctxtBefore lc k` in the `verified_mach` family) | the address has no code and is not the return address; from every state there with the entry's `SP`, `g` and stack bound `0(g)` whose stack check fails (`¬ CheckPasses`), the hook `H.call` returns to `X30` with `X30` set to `R3` (the `MOVD R30, R3` of the tail), `SP`, `R28`, `R29` kept, `R26` kept when `ctxt`, the memory kept but the guard word `gOff(g)`, and the guard lower (the loop's measure). `ctxtBefore lc k`: an entry value before `k` has `R26` in its home (`ctxtBefore_of_live26`: otherwise `R26` holds no value at `sI`, so `EntryMatch.more` needs nothing of it) | `runtime.morestack` with or without a context, `runtime.morestack_noctxt` without (`morestackHook`: `newstack` grows the stack in place, `stackguard0` lowered by `growBy` down to `stack.lo + StackGuard`, `gogo` resumes after the `BL` with `X30 = R3`; `R26` saved and restored by `morestack`, `runtime/asm_arm64.s:449`, `:269`, zeroed by `morestack_noctxt`, `:493-502`); the assembler calls `morestack_noctxt` from a function without `NEEDCTXT` (`cmd/internal/obj/arm64/obj7.go:283-289`, `GoFV/Asm/Obj7.lean:448`), and the e2e driver checks that a function with `ctxtBefore` at `entryLen` calls `runtime.morestack` (`morestackCtxtWhy`, by the relocation's symbol name); the stack can grow (the floor below the limit); `morestackHook_ok` (`GoFV/Proof/Obj/MorestackHook.lean`) proves the model meets the contract at `runtime.morestack` with any context and at `runtime.morestack_noctxt` without, for a check of `stackguard0` when `growBy > 0` and `stack.lo + StackGuard` is below the check's limit. Until #708 the contract kept `R26` unconditionally, which `morestack_noctxt` does not | a runtime that moves the stack (`δ ≠ 0`, not modelled) or cannot grow it (then the hook is stuck: no obligation); the tail's call to another symbol (`checkObj` does not see symbol names; the driver checks the name only with a context) | `msHook_ok` (`objFrame_morestack_witness`: a hook that clears the guard), `msHookV_ok` (`objMoreF_witness`: one that also clobbers every vector register), both at `runtime.morestack_noctxt` without a context, `morestackHook_ok`; vacuous (no stack check) in the ObjWhole, ObjWholeNL, ObjPanic and ObjEndToEnd witnesses |
| `TailSep`, `MoreEntry` (Phase 3, `Morestack.lean`, `Whole.lean`; premises of `obj_entry`/`sim_entry` and `obj_whole_ret`, `obj_whole_panic`, `verified_mach`, for a function with a stack check) | the spill slots of the morestack tail (`tailPlan`: `off(SP)` of the entry's `SP`) lie below `2^64` and apart from `g`'s first 32 bytes; every register `runLoc`'s first state holds a value in but `R26` is reloaded by the tail from a slot the value fits (`ValFits`: an integer of at most `8n` bits, a boolean, else `n = 8`; a vector register from a slot of its `F` register, `reloadOf sl true`, whose `4`/`8` bytes hold the float's bits, which `FValRel` reads alone: the hook clobbers the vector registers), and the live blocks of its memory lie apart from the slots and the guard word | ABIInternal's spill area of the register arguments is in the caller's frame, `g` is not on the stack; the spills are those of the arguments (`SpillRegisterArgs`) | a register argument the tail does not spill (the validator spills `R0`–`R15` and `F0`–`F15`, `FMOVS`/`FMOVD`/`FSTPS`/`FSTPD` for the floats) | `tailSep` (`objFrame_entry_witness`, `objFrame_morestack_witness`, `objMoreF_witness` with an `F0` spill); vacuous in the whole-function witnesses |
| `EntryMatch`, `EntryEnv` (Phase 3, `GoFV/Proof/Obj/Whole.lean`; premises of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | after the entry values and the `Arg`s of the incoming stack arguments (`entryLen`), `runLoc`'s registers (the arguments) are in the entry machine state's registers (none in `R16`, `R17`, `R20`, `R29`), no flags; **the stack clause** (`EntryMatch.stack`, an ABI0 caller obligation): every slot is the home of an `Arg` (G62) with a `NAME_PARAM` operand `x+off(FP)`, `off ≥ 0`, and the entry state's bytes at `SP + 8 + off` hold its value as a spill slot holds one (`SlotRel`), below `2^64` and apart from `g`'s first 32 bytes; for a function with no `Arg` the clause is `slots = []`, the condition before G62 (`EntryMatch_stack_nil`); its memory injected by `ι` into a memory that is the entry state's but for the windows of the register-assigned parameters in `Blk.local` blocks the function accesses (`pendWins`: the caller's spill area, written by the entry stores, whose cover is the checked boolean `entryStoresOK`, no assumption); the activation's `SP`, `g`, `LR`, `FP`, `framed` are the entry state's (after the prologue's frame) and the return address is no P0 address | the caller's side of ABIInternal: register arguments in `abi.RegIndex` registers; the caller's memory is the callee's. The stack clause is the caller's side of ABI0's stack layout (`cmd/compile/internal/abi/abiutils.go:270-318`: `ABIConfig.offsetForLocals` = `FixedFrameSize` = 8 on arm64, the stack-assigned parameters from there at `ABIParamAssignment.Offset()`, `:108`; every parameter of an `ABI0` function, and those past the registers of an `ABIInternal` one): before the `CALL` the caller stores each stack-assigned argument at `8 + offset(RSP)` (as `runtime/asm_arm64.s:590-597`'s `CALLFN` copies `reflectcall`'s stack arguments to `8(RSP)`), which is `8 + offset` above the callee's entry `SP`, and after the prologue the callee's `x+off(FP)` = `SP + autosize + 8 + off` (`frameOff .PARAM`, `sim_entry`). The callee writes nothing there before its `Arg`s: genssa emits no code for an `Arg` (`cmd/compile/internal/ssagen/ssa.go:7121-7122`, "input args need no code"), the prologue writes only the saved `LR`/`FP` words below the entry `SP`, Go's scheduler puts the `Arg`s at the top of the entry block (`cmd/compile/internal/ssa/schedule.go:18,164-166`, `ScoreArg`), and `argsOK` (checked) puts every `Arg` before `k` and, in a function with one, no pending window and no morestack spill (the morestack tail keeps the bytes, `EntryMatch.more`; the guard word is among `g`'s first 32 bytes, `checkObj_gOff`) | a caller that passes arguments elsewhere; a caller that passes a stack argument elsewhere than `8 + offset(RSP)` (an assembly caller off ABI0) | `objWhole_ret_witness`, `objWholeNL_ret_witness`, `objWhole_panic_witness`, `verified_mach_witness`; the left-out window: `entryStore_witness`; the stack clause's bytes: `genG62_witness`'s `m0` (the word 7 at `SP + 24`, `GenG62.argOK0`) |
| `RunPre` (Phase 3, `GoFV/Proof/Obj/Whole.lean`; premise of `obj_whole_ret`, `obj_whole_panic`, `verified_mach`) | at every state `runLoc` reaches: the slices' per-step premises `G54Pre`, G63's `FReloadPre`, G64's `QLoadPre` and `G1TermPre` (not trusted: facts of the run, e.g. a load, an acquire load or a 128-bit load reads valid bytes, a `LoweredMove` or G54 loop accesses valid bytes, a float reload reads no bare pointer), no entry value after the entry (`entryOp24`), `GetGOK`, and the trusted `CallOK`, `CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK` (rows above) | as the rows above | as the rows above | `runPre_simple` (functions of simple ops), `objWhole_ret_witness`, `objWhole_panic_witness` |
| not modelled by the hooks | the defer machinery (`deferproc*`, `deferreturn`, `gorecover`), runtime entry points called through function values, asynchronous preemption, the collector: a run reaching them is `stuck` | sound: a stuck run carries no obligation | — (a restriction) | — |

Not assumed, by decision: disjointness of parameter slots from the other frame slots (the
`not disjoint` class above stays open), and type-based aliasing (#111).

**Limitation: run premise `FArithPre` excludes NaN-NaN operand cases** (Phase 3 G46 on,
`GoFV/Proof/Gen/G46.lean`; #176). On these operands Phase 1's float semantics and the machine give
different results, and the slices' value theorems (`g46_value` and later, so the end-to-end
theorem) say nothing about a run that reaches one; Phase 1's semantics is unchanged for now
(`GoFV/Proof/Gen/FArith.lean`, each pattern checked by `#eval`):

- `FADD`/`FMUL` of two NaNs of one kind (`FNaNSwap`): Phase 1 orders the operands by encoding
  (`FOps.ordered`), the machine takes `Rn, Rm`. `FADDS 0x7FC00001, 0x7FC00000`: Phase 1
  `0x7FC00000`, machine `0x7FC00001`; `FMULD 0xFFF8000000000000, 0x7FF8000000000000`: Phase 1
  `0x7FF8000000000000`, machine `0xFFF8000000000000`; `FADDD 0x7FF0000000000002,
  0x7FF0000000000001`: Phase 1 `0x7FF8000000000001`, machine `0x7FF8000000000002`.
- `FMADD`/`FNMSUB` whose multiplicands are NaNs of one kind (`FSameNaN`): Phase 1 computes
  `FPMulAdd(±arg0, ±arg1, arg2)`, the machine on genssa's operands `FPMulAdd(±arg0, ±arg2, arg1)`.
  `FMADDD 1.0, 0x7FF8000000000001, 0x7FF8000000000002`: Phase 1 `0x7FF8000000000001`, machine
  `0x7FF8000000000002`.
- `FMSUB`/`FNMADD` are not accepted at all (no slice proves them): Phase 1 negates the other
  multiplicand, so a NaN result can carry the other sign. `FMSUBD 1.0, 0x7FF8000000000000, 2.0`:
  Phase 1 `0xFFF8000000000000`, machine `0x7FF8000000000000`; `FNMADDS 1.0, 2.0, 0x7FC00000`:
  Phase 1 `0x7FC00000`, machine `0xFFC00000`.

Lifting it means making Phase 1's `FOps.ordered` and `Arm64.fmadd` operand order the hardware's,
which Phase 2's `Contract` proofs (`fmadd`) depend on.

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
