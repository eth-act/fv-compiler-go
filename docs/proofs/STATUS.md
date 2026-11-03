# Phase 1 status: generic passes (issues #69, #189)

The final state of Phase 1 rule coverage (the generic passes `number lines` … `writebarrier`,
`docs/PASSES.md`). Measured on main @MAIN@ with the corpus `full-v6` (format 5, 96,553 functions;
its Phase 1 sections equal `full-v5`'s except `cmd/compile/internal/ssa`). How each number is made:
"Commands" at the end. Details of every proof are in `docs/proofs/rules.md`; this page is the
summary.

## Headline

| Measure | full-v6 |
| --- | --: |
| Functions fully verified (`gofv-ssa-opt --check --verified`: every pass run `proven`, `identity` or `skipped`; by `verifiedPipeline_refines` the output refines the input under `VPre`) | @FV@ |
| … and identical to stock at the last section | @FVS@ |
| Functions every rewrite section of which the checked proven-only passes reproduce exactly (`opt-proven-probe`) | 93,199 / 96,553 |
| … under the proven-only passes alone (without the validator) | 93,304 |
| … the validator the only obstacle (`BLOCKED`) | 105 |

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
| P2 (pointers, composites, `Load` values, `SelectN`) | 63 | 1 | 45 | 109 |
| mem (memory ops) | 52 | 0 | 60 | 112 |
| call | 9 | 0 | 38 | 47 |
| float | 22 | 0 | 46 | 68 |
| ptr (`ConstString`, `Addr`, `NilCheck`, pointer comparisons) | 8 | 0 | 15 | 23 |
| phi | 0 | 0 | 5 | 5 |
| block | 3 | 0 | 0 | 3 |
| all | 1,369 | 31 | 362 | 1,762 |

*Proven*: a merged lemma (`Rule.Sound`, `Rule.SoundT`, `Rule.SoundW`, `Rule.MakeSel`,
`Rule.LoadSel`, `Rule.Drop`, `BlockRule.Sound`, `EffectRule.NilElim`/`LoadFwd`/`StructLoad`/
`StructStore`/`Seg`, `ConstString` frame rules, dec rules); `GoFV/Rules/Proven.lean` is the
proven-only rule set the theorems are about. Per op family: the "Coverage" table of `rules.md`.

**False under the semantics, with the reason** (31; "Findings" in `rules.md`; each marked
`-- FALSE … #N` in its proof module):

- `generic.rules:2166–2169` and their `Or`/`Xor` expansions (12): constant rotate detection
  compares the shift constant signed; at `c = -1`, `d = w+1` both shifts give 0, but
  `RotateLeft x (Const [-1])` rotates by `w-1`. A Go bug candidate (#90, `upstream-candidate`).
- `divmod.rules:136–148` (`Div16u/32u/64u` of a signed type by `smagic`, 4): the dividend need
  not be non-negative; Go establishes that in `prove` before. Counterexamples in `rules.md`.
- `generic.rules:1071`, `:1075` (`Convert` of an integer offset from a converted pointer): integers
  carry no provenance, so the pointer made from `addr(p) + off` need not be in `p`'s allocation
  (#156).
- `generic.rules:1053` (the `SliceMake` of `AddPtr … Slicemask` with a different argument) and
  `:1039` (32-bit lengths in a 64-bit slice): the pattern does not check what `ssagen`
  guarantees (`:1053` is proven with the validator's instance premises `sameLeaves`/`makeTop`;
  the 32-bit form stays false).
- `CondSelect` into arithmetic (`:2325`, `:2342`, `:2355`, `:2368`, `:2371` rows): at
  `bool = false` the match is the leaf `x`, the result recomputes it, and a 64-bit register may
  hold an address-less pointer on which `Sub64`/`Or64` are `poison`.
- `generic.rules:579` (`Lsh32x64` of `And32 (Rsh32x64 x c) d` by `e`, `c < e`): false for
  `c < 0` (`x = -1`, `d = 1`, `c = -1`, `e = 1`: `2` against `0`).

**Open** (362): the `P1`/`P2` alternatives without a lemma (198, most never fire on the corpus;
the ones that fire are in the `fire-full` table of `rules.md`), and 164 effect, call, float,
pointer and phi alternatives:

- *out of the model*: the float rules on ops without an `evalPure` arm or with IEEE rounding the
  model does not pin (`Ceil`, `Floor`, `Trunc`, `Round`, `RoundToEven`, `Sqrt`, the `Cvt`
  conversions, constant-folded `Add/Sub/Mul/Div/Neg` of `32F`/`64F`, `OrB`/`Not` of float
  comparisons; 46), the runtime calls the model has no contract for (`StaticLECall` folds of
  `memequal`, `cmpstring`, `makeslice`/`growslice` sizes, `InterLECall` devirtualisation, the
  `SelectN` of `runtime.memequal` results; 38), and the five `Phi` rules (`:782–:785`, `:1068`,
  which need a phi obligation the rule lemmas do not state; `applyRewrite`'s own phi
  elimination is proven, "Phi eliminations" in `rules.md`);
- *in the model, not proven*: the remaining memory rules (`Load` forwardings through `Move`/
  `Zero` of other shapes, `Move` chains `:1740–:1942`, `Store` drops `:919`/`:924`/`:930`/`:937`,
  the `EqPtr`/`NeqPtr` of two allocations `:1648–:1676`; 75 `mem`/`ptr` alternatives).

## Per-pass fragment coverage (verified pipeline, full-v6)

@PASSES@

## Remaining validator classes (functions whose only obstacle is the rewrite validator, 105)

`BLOCKED` lines of `opt-proven-probe` (every rewrite section at stock under the proven-only
passes, not under the checked ones), by class (the generated table is `fire-full` in `rules.md`):

| Class | Functions | Why it is open |
| --- | --: | --- |
| `fwd₂: not disjoint` (`OffPtr` 37, `LocalAddr` 9, `SelectN` 7, `snap` 1, with a `drop chain Zero` 1) | 55 | A forwarding past a store the validator cannot show disjoint from the `Load`. About 30 are stores into `PPARAM` slots: disjointness of a parameter slot from the other frame slots needs an `InitAvoids`-style precondition for parameter slots, and the integrator decided not to add a `VPre` conjunct for it. Two are distinct `mallocgc` results (needs a relation between the results of two calls). The rest are Go's `disjointTypes` (type-based aliasing: a store of one type cannot alias a load of an incompatible pointer type), which is out of scope (#111). |
| `fwd₂: move: ptr AddPtr` | 7 | A `Load` through a `Move` (`:827`) at an `AddPtr` of the destination: `fwdMoveOK` knows constant `OffPtr` offsets only, not a variable index. |
| `final: fields Copy->Copy` (late opt, snapshot segments) | 6 | Go's `copyOf` gives a forwarded `Load`'s `Copy` the stored value's type (`ptr` vs `int`, interface vs pointer, both of compatible shape); the forwarding layer keeps the `Load`'s type and the final comparison asks for equal types. Retyping the `Copy` in the layer needs the forwarding proof to move the value across a compatible retype. |
| `seg₁: rel` | 5 | A segment whose dropped values are used outside it, or whose schedule is not the source's with the segment's roots replaced (`segRel`'s block checks). |
| `seg₁: SelectN→Move` | 5 | `memmove` call segments (`:1730`) whose destination argument value rules rewrote before the segment matched (`PtrIndex p (Sub64 c (SliceLen …))` with a constant-zero index became `p`): `callSeg?` asks for the call's own arguments. |
| `fwd₂: store type` (late opt) | 5 | A forwarding between a pointer and a one-field struct of that pointer (`struct{p *T}`): the same bytes, but `fwdTy` relates only equal or nested-field shapes. |
| `fwd₂: rep Load->Const64F`, `move: args … Copy`/`LocalAddr`, `drop chain Store`/`SelectN` | 7 | Single shapes of forwardings and dropped-write chains. |
| `seg₁: Move→Store ⟨zero⟩`/`⟨store⟩`, `SelectN→Zero`, `Store→Store` | 6 | Single shapes of move/call/chain segments (a `Zero` of another size, sizes the constant-term evaluator does not fold). |
| `nil₂: nrel` (`Convert` 2, `CondSelect` 1), `fwd₂: ptr NilCheck` 2 | 5 | Nil checks of pointers made from integers (`runtime.int32Hash`/`int64Hash`: `Convert` of an `Xor64`) or a `CondSelect` of two addresses, which no seed of `safePtr` covers. |
| `rule arity`, `atoms`, `ss: field 0 of 1` (2) | 4 | Single cases. |

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

## Trusted assumptions: `VPre`

`verifiedPipeline_refines` concludes `RefinesFrom (VPre k ro)` (`GoFV/Proof/Pass/Pipeline.lean`);
every pass theorem's precondition is a conjunct. `k` are the input's dictionary parameters, `ro`
its read-only symbols. Each conjunct, what it assumes, and whether the runtime model
(`Env.runtime`) and the Phase 1 test environment (`Env.p1`) satisfy it:

| Conjunct | Assumes | Discharged for |
| --- | --- | --- |
| `env.Mono` | every contract is monotone: a refined call (arguments, closure, memory) gives a refined outcome; calls observe their arguments (`Contract.Mono`, `GoFV/Proof/RunMono.lean`) | `Env.p1_mono` |
| `env.FrameSafe` | contracts cannot read or keep pointers into the caller's frame temporaries (results and memory avoid them, the rest equal off them) | — (assumed of the runtime) |
| `InitAvoids env args mem` | the arguments, the memory and the global image hold no pointer into a `temp` block (no frame temporary exists before the frame) | a property of the inputs |
| `env.AllocNonNil` | malloc-family contracts return a non-nil pointer first (`NilCheck.mallocName`) | `Env.runtime_allocNonNil`, `Env.p1_allocNonNil` |
| `DictArgs k args` | the dictionary arguments (indices `k`) are non-nil pointers | a property of the inputs |
| `WB.WbPre env args mem` | the memory with the global image has a defined, read-only `runtime.writeBarrier` flag and no write-barrier buffer, contracts keep that, and `runtime.wbZero`/`runtime.wbMove` are the runtime's helpers that do not spill into the caller's outgoing area (`WbHelpers`, `env.noSpill`: checked against the go1.27.3 linux/arm64 disassembly, #36) | trusted (`env.noSpill`) |
| `env.TempOblivious` | contracts cannot tell whether unreachable `temp` blocks exist | — (assumed of the runtime) |
| `env.MemOps` | `runtime.memclrNoHeapPointers`/`runtime.memmove`, if present, are the runtime model's | `Env.runtime_memOps`, `Env.p1_memOps` |
| `RoImage ro env mem` | contracts keep the read-only global allocations and return no memory; the symbols `ro` are read-only allocations of the memory with the global image holding their exported bytes | `Env.runtime_keepsRo`, `Env.p1_keepsRo` (the image part is a property of the inputs) |
| `env.FrameKeep` | contracts keep the caller's frame allocations and return no memory | `Env.runtime_frameKeep`, `Env.p1_frameKeep` |
| `env.AllocZero` | malloc-family contracts asked for a positive size return a fresh all-zero heap block (size 0 returns `runtime.zerobase`, about which nothing is claimed) | `Env.runtime_allocZero`, `Env.p1_allocZero` |
| `env.GrowLen` | `runtime.growslice`/`growsliceNoAlias`, if present, return a slice of their `newLen` argument | `Env.runtime_growLen`, `Env.p1_growLen` |

Not in `VPre` by decision: disjointness of parameter slots from the other frame slots (the
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
