# Plan: semantics of lowered arm64 SSA (Phase 2, milestone H6)

Status: plan (milestone H6, #384; tracking #387). Phase 1 semantics: `docs/plans/semantics.md`
(`GoFV.SSA.run`, `GoFV/SSA/Sem/*`). Pass survey: `docs/PASSES2.md`. Source of truth for the
ops: `third_party/go/src/cmd/compile/internal/ssa/_gen/ARM64Ops.go` (354 ops, plus 306 SIMD
ops that only `GOEXPERIMENT=simd` produces; 25 block kinds; "AO line" below), the rules
`_gen/ARM64.rules` (1,233 source rules) and `_gen/ARM64latelower.rules` (69), and, for what an
op means on the machine, the instructions `ssaGenValue`/`ssaGenBlock` emit for it
(`cmd/compile/internal/arm64/ssa.go`, 2,223 lines). Decisions taken on #384 (integrator, 2026-11-03, reversible) are
recorded in §4 (licence), §6 (panic order) and §11 (FMA); clifv's `FV/Arm` (eth-act/clifv,
`docs/contracts/arm.md` there) is discussed as an option only.

## 1. The three forms of lowered SSA

Phase 2 code passes through three forms with different evaluation rules. Each gets a semantics;
each pass is proven against the form it consumes and produces.

| Form | Produced by | What changes | Semantics |
| --- | --- | --- | --- |
| **L0, unscheduled lowered SSA** | `lower` … `layout` | ARM64 ops and block kinds replace generic ones; flags values; tuple results (`ADDSflags`, `LoweredMuluhilo`, …). Still SSA with explicit memory values; `b.Values` order is not an execution order. | `runL` (`Sem/RunL.lean`): Phase 1's runner with the ARM64 ops, block kinds and register reads of narrow values (§3–§5); `runL = run` on generic SSA (`runL_generic`) |
| **L1, scheduled SSA** | `schedule`, `late nilcheck`, `flagalloc` | `b.Values` is the execution order; memory is linear (at most one memory value live, loads before the store that kills their memory); `late nilcheck` relies on faulting loads/stores replacing explicit nil checks; `flagalloc` keeps at most one flags value live. | `runSched` (§6): `b.Values` order, one current memory, faulting memory ops |
| **L2, allocated SSA** | `regalloc`, `loop rotate`, `trim` | Every value has a home (`f.RegAlloc`): a register, a stack slot (`LocalSlot`), a pair or a result list. New `Copy`, `LoadReg`, `StoreReg` and rematerialised values; phis whose args share the phi's home. **Args no longer dominate uses** (`check.go:451-454` skips the dominance check once `f.RegAlloc != nil`): the function is not SSA any more, and evaluating it as SSA is wrong. | `runLoc` (§7): a machine state of registers, flags, stack slots and memory |

The forms nest: L0 ⊇ generic SSA (Phase 1 ops stay legal), and a function in L1 or L2 is still
a `GoFV.SSA.Func`. The point of three semantics instead of one machine semantics is reuse: every
pass from `lower` to `layout` is proven against `runL`, which is Phase 1's `run` on generic SSA,
so the Phase 1 machinery (`Refines`, `RefinesFrom`, `VPre`, `verifiedPipeline`, `check`, the rule
interpreter's soundness #113) extends to it by adding op cases, not by restarting.

**Decision (#384, integrator): `runL` is a separate runner, Phase 1 byte-identical.** H6 first
extended `run` itself (an arm64 arm in `evalOp`, an `Arm64.evalPure` fallback in `evalPure`, the
arm64 kinds in `stepTerm`, and zero extension of narrow values in `Val.retype`/`encode`). The
narrow values cannot be confined to arm64 ops: lowering hands narrow and boolean values to
generic `Phi`s, `MakeResult`s and `Copy`s of wider types (§3), whose shaping is Phase 1's. So
extending `run` changed Phase 1's definitions and broke Phase 1 lemmas that state the old shaping.
Instead `runL` (`Sem/RunL.lean`) is Phase 1's block loop (`runCtxL`, `runLoopL`, `enterBlockL`,
`evalValueL`) with `evalOpL` (Phase 1's `evalOp` for a generic op, the arm64 definitions
otherwise), `stepTermL` (Phase 1's `stepTerm` for a generic kind) and, in a lowered function
(`Func.lowered`: an arm64 op or block kind), `Val.retypeL` in place of `Val.retype`. Every Phase 1
definition and proof is unchanged. The "same `run`" intent is a theorem:

```
theorem runL_generic (h : f.lowered = false) : runL env tabs f args mem fuel = run env tabs f args mem fuel
```

(`GoFV/SSA/Sem/RunL.lean`; witness `runL_generic_witness`, `clamp`). The `lower` theorem relates
`run` of its input to `runL` of its output; the L0 → L0 passes are stated over `runL`.

## 2. Correctness criterion

As Phase 1 (`docs/PLAN.md` §1): a pass `p` is correct when every returning or panicking run of
`p f` is, up to refinement, a run of `f` (`GoFV.Proof.Refines`, backward from target outcomes via
determinism and fuel monotonicity). Across forms the two runs use different semantics:

```
Refines₀₀ (p f) f  :=  Refines over runL     / runL         -- lower … layout (L0 → L0; lower: runL / run)
Refines₀₁ (schedule f) f   over runSched / runL             -- the schedule pass (L0 → L1)
Refines₁₁ (p f) f   over runSched / runSched                -- late nilcheck, flagalloc
Refines₁₂ (regalloc f) f   over runLoc / runSched           -- regalloc (L1 → L2)
Refines₂₂ (p f) f   over runLoc / runLoc                    -- loop rotate, trim
```

All five share `Outcome`, `Val.Refines`, `Mem.Refines` and `OutcomeRefines`, so they compose
into the Phase 2 end-to-end statement (H7/H8):

> for `f` the input of `lower` and `g` the Lean pipeline's output after `trim`, there is an
> `f'` with `Contract f f'` (§2.1) and `RefinesFrom VPre₂ (runLoc g) (run f')`; with Phase 1's
> `verifiedPipeline_refines`, `runLoc g` refines a contraction of the ssagen output `f₀`.

`VPre₂` is Phase 1's `VPre` plus the lowered-code preconditions (§8): the runtime contracts hold
for register-passed arguments, `g` (x28) is preserved by callees, and memory below
`minZeroPage` (4,096, `nilcheck.go:192`) is unmapped.

Proven form (#385, `GoFV.Proof.PipelineFull.verifiedPipelineFull_refines`, `docs/PASSES2.md` §0):
for a `fullyVerified` result of the verified pipeline from `number lines` through `trim`, every
returning or panicking `run` of the ssagen output `f₀` is, up to refinement, a `runLoc` of the
result, under Phase 1's `VPre` and `NoNilFault` of the `schedule` input (where `schedule`'s
`runLF` theorem meets `runL`). The verified `lower` accepts only inputs without fused
multiply-add shapes (`contractAll f = f`), so no `Contract` appears; composing a contraction
with the refinements before `lower` is open.

### 2.1 Floating-point contraction (decision on #384)

The Go spec allows an implementation to fuse `x*y + z` into one rounding ("An implementation may
combine multiple floating-point operations into a single fused operation, possibly across
statements, and produce a result that differs from the value obtained by executing and rounding
the instructions individually", `doc/go_spec.html:5092-5094`). `lower` does so with the 12 `useFMA` rules
(`_gen/ARM64.rules:1798-1809`: `FADD`/`FSUB` of an `FMUL`/`FNMUL`, single and double precision,
to `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB`; `useFMA` is always true with the default `base.FmaHash ==
nil`, `func.go:850-855`). No Phase 1 rule fuses.

The relaxation is syntactic and limited to those shapes; Phase 1's semantics, `Val.Refines` and
`OutcomeRefines` stay unchanged. `Contract f f'` holds when `f'` is `f` with some values whose
op and argument shape match the left-hand side of one of the 12 rules (on the lowered ops, or the
generic `Add/Sub{32,64}F` of a `Mul{32,64}F`/`Neg(Mul)` they come from) replaced by the fused op
of the right-hand side, with the same arguments; the multiply itself stays (it may have other
uses). An explicit conversion, which the spec says prevents fusion, leaves a `Round32F`/`Round64F`
(lowered to `LoweredRound*F`) between the multiply and the add, so no rule shape matches it. The
`lower` theorem is then

```
∃ f', Contract f f' ∧ RefinesFrom VPre₂ (lower f) f'      -- runL of lower f, run of f'
```

and the Phase 2 end-to-end statement carries the same `∃ f', Contract f f' ∧ …`. Every other
float op must refine exactly. The rule lemmas for the 12 fused rules are proven against the
fused op of `f'` (an equality), so the relaxation appears in exactly one place.

## 3. Values: flags and the lowered domain

Phase 1's `Val` (`GoFV/SSA/Sem/Val.lean:93`) already has the right shapes for lowered code:
integers and floats are `Val.int w bits` (floats as IEEE bit patterns since P4, exactly what
the registers hold), booleans `Val.bool`, pointers `Val.ptr` with provenance, tuples, memory
snapshots, `poison`.

**Flags.** Lowered compares produce values of type `flags` (`CMP`, `CMPconst`, `TST`, `FCMPD`,
`CCMP`, …, and the second result of `ADDS`/`SUBS`/`ADCS`/`SBCS`/`NEGS` tuples). A flags value
is the four bits N, Z, C, V, as `PSTATE.NZCV` in clifv's model (`Arm.PFlag`). Two encodings:

1. a new constructor `Val.flags (nzcv : BitVec 4)`; clean, but every Phase 1 proof that does
   `cases v` gets a new case (`Val` is matched exhaustively in `Val.Refines`, `retype`,
   `hasTy`, `encode`, the ABI pieces);
2. a shape `Ty.flags` over existing constructors, `Val.agg [.bool n, .bool z, .bool c, .bool v]`
   (`Flags.toVal`/`Flags.ofVal`), with `retype`/`hasTy` cases for the shape only.

**Choose 2.** It leaves every Phase 1 lemma untouched (flags never reach memory, the ABI or
`decode`), and `Flags` is a plain Lean structure with `ConditionHolds` on it. Revisit only if
a proof is measurably easier with 1.

**Pointer arithmetic.** `lower` turns `AddPtr`, `SubPtr`, `OffPtr` and pointer compares into
integer ops (`_gen/ARM64.rules:5,8,243,251,305-306,450`): `(Add(Ptr|64|…) ...) => (ADD ...)`,
`(OffPtr [off] ptr:(SP)) => (MOVDaddr [int32(off)] ptr)` else `(ADDconst [off] ptr)`,
`(EqPtr x y) => (Equal (CMP x y))`, `(IsNonNil p) => (NotEqual (CMPconst [0] p))`; `Convert`
stays generic (`checkLower`'s whitelist, `lower.go:31-34`). So the integer ops of L0 must keep
provenance where the generic op did. Rule: every 64-bit ARM64 integer op is defined on words,
through one lifting `liftW`, with these provenance cases taken first:

- `ADD p i`, `ADD i p`, `ADDconst [c] p`, `SUB p i`, `SUBconst [c] p`, `MOVDaddr [c] p` (and
  `ADDshiftLL p i [s]`, which the addressing rules produce) with `p` a pointer and `i` an
  integer give the pointer `p + i` (Phase 1 `AddPtr`/`OffPtr`);
- `SUB p q` of two pointers is Phase 1's `SubPtr`; `CMP p q`/`CMPconst [0] p` compare as
  Phase 1's `EqPtr`/`IsNonNil` where those are defined (same block, or nil), and otherwise by
  concrete addresses (`Ptr.addr?`);
- any other op reads pointers as concrete words (`Ptr.addr?`; no address ⇒ `poison`), and its
  64-bit integer result keeps its word at a pointer shape (Phase 1 §3.2: an integer is read back
  as a pointer through `Ptr.ofAddr`).

This inherits Phase 1's open points on concrete addresses (#156: out-of-window arithmetic, nil
comparison by block, `Convert` round-trips). Lowered code adds one: an `ADD p i` whose `i` is
itself a pointer (rare; `unsafe` code) is computed on words, the sum of the two addresses
(`poison` if one has none), symmetrically, as `ADD` is `commutative` and cse swaps its operands.

**Totality.** ARM64 ops are total, as the instructions are: `UDIV`/`SDIV` by zero give 0, shifts
take the amount modulo the width, `CLZ`/`RBIT` of 0 are defined. Passes rely on it: `loop
invariant` hoists every `earlyOk` op (division included, `_gen/ARM64Ops.go:198-219`) out of
loops without a guard, so a lowered op must not be `poison` where the machine instruction is
defined. `poison` arises only from `poison` inputs whose bits the op uses and from the pointer
cases above.

**Booleans.** Lowered boolean producers (`Equal`, `LessThan`, …, `CSET`-like, `MOVBUreg` of a
bool) keep type `bool`; the semantics returns `Val.bool` at `bool` type and `Val.int .w8 0/1`
at `uint8`. An arm64 op whose type is `bool` yields the boolean of bit 0 of its register (the
bit Go branches on, `(If c) => (TBNZ [0] c)`).

**Narrow values in registers (as implemented, H6).** A value of a type narrower than 64 bits is
held at its type's width (Phase 1's `retype`), but the register it lives in has upper bits that
Go's rules rely on in exactly two ways, and `runL` follows both:

1. *Dropped zero extensions.* `(MOVWUreg x) && ZeroUpper32Bits(x, 3) => x`,
   `(MOVBUreg x:(Equal …)) => x` and `(CvtBoolToUint8 x) => (Copy x)` hand a narrower (or
   boolean) value to a use of a wider type; Go's rewrite removes the copies inline
   (`rewrite.go`, `applyRewrite`), so the use may be a generic `Phi`, `MakeResult` or `Copy`. An
   arm64 op reads any narrower integer or boolean zero-extended (`Arm64.reg`). In a lowered
   function `runL` shapes every value with `Val.retypeL`: a narrower integer or a boolean at a
   wider integer or a pointer shape is zero-extended (`Val.widen`), then shaped by Phase 1's
   `Val.retype`. Calls pass their register pieces at their leaves' shapes (`fitPieces`, since
   Phase 1's `encode` makes a piece of another width `poison`), atomics their operands at the
   location's width (`atomicArgs`). Phase 1's `Val.retype` and `encode` are unchanged (§1).
2. *Register copies of extended loads.* `(MOVBreg x:(MOVBload …)) => (MOVDreg x)` and the other
   "don't extend after proper load" / "fold double extensions" rules (`ARM64latelower.rules`)
   pass a sign-extended narrow register on through `MOVDreg`/`MOVDnop`. These read their
   argument (`Arm64.signExtendsIn`: a sign-extending load or extension, or a `Select0`/`Select1`
   of `LDPSW`, since `pair` merges the `MOVWload`s of such a `MOVDreg` after `late lower`; found
   by the regalloc checker in `runtime.checkdead`) and sign-extend it, else zero-extend
   (`Sem.arm64Op`).

Results are 64-bit (`.int .w64`), narrowed by `retypeL` to the value's type; a `W` op
zero-extends its 32-bit result, as writing `Wd` does.

## 4. Op semantics: options

### (a) Define each ARM64 op directly

`evalArm64 : Op → AuxInt → Aux → Ty → List Val → Val`, one definition per op family on
`BitVec`, written from the AO comments (`ARM64Ops.go`) and the ASL of the instruction the op
emits, in the style of Phase 1's `evalPure` (one `match`, one module per family so a rule
lemma unfolds only its family).

- For: the same style, value domain and proof tooling as Phase 1; the 1,302 lowering rules get
  lemmas of the form `evalPure (generic op) … = evalArm64 (arm64 ops) …` by `bv_decide`/`rfl`,
  cheap per rule; pointer and poison cases are explicit.
- Against: ~330 new trusted definitions. The AO comments are informal (e.g. the semantics of
  `ARM64ConditionalParams`, of the `noov` conditions, of the `Variant` atomics); a definition
  error is invisible to proofs and only an oracle catches it.

### (b) Define lowered ops by clifv's `FV/Arm` instruction semantics

The meaning of an op is the run of the instruction(s) `ssaGenValue` emits for it, executed by
`Arm.exec` on a canonical `ArmState` holding the arguments in fixed registers (exactly clifv's
`csem` approach for its register allocator, `docs/contracts/regalloc-proof.md`: "no
per-instruction formula is hand-written").

- For: no new trusted per-op definitions; the model is ASL-transcribed and co-simulated
  against `qemu-aarch64-static` (760 forms, 152,000 vectors, 0 failures in clifv); Phase 3
  (`genssa`) then needs only the encoding and the frame, not the op semantics.
- Against:
  1. **Domain mismatch.** `ArmState` is concrete: 64-bit registers, flat byte memory. Phase 1
     values have provenance pointers, memory snapshots, aggregates and `poison`, and Phase 1's
     proofs rely on them (provenance makes frame slots unobservable; `poison` makes `dse`,
     `dead auto elim`, rule side conditions sound). Every op needs a wrapper that concretises
     its arguments and abstracts its results; `poison` cannot be represented (an op with a
     poison input must be declared poison, which is wrong for `CSEL` whose unselected input is
     poison).
  2. **Memory ops cannot use the Arm memory** before Phase 3: loads, stores, `DUFFZERO`,
     `LoweredZero`/`LoweredMove`, atomics, calls, nil checks would still need a definition on
     the Phase 1 memory model. That is about a third of the ops that matter.
  3. **Proof cost.** A rule lemma would unfold LNSym-style decode/execute (`decode_raw_inst`,
     nested matches over encoding fields) under `sym_n`: every rule lemma would pay for a
     fetch/decode/execute unfolding per instruction instead of one `BitVec` goal, and there are
     1,302 rules.
  4. **Coverage.** clifv's model lacks the LSE atomics Go emits for the `Variant` atomics
     (`LDADDAL`, `LDCLRAL`, `LDORAL`, `SWPAL`, `CASAL`; no file under `FV/Arm` implements them)
     and treats `PRFM` as `Unimplemented`. The forms it has (`LDAXR`/`STLXR`, `CNT`/`UADDLV`
     for popcount, `LDP`/`STP` of q registers, `DMB`, the scalar ALU and FP classes) were
     co-simulated on Cranelift's encodings; Go's assembler (`cmd/internal/obj/arm64`) produces
     the words here, so co-simulation must be redone on Go's encodings anyway.

### (c) Mixed

Direct definitions as in (a) — the proof-facing semantics, in Phase 1's domain — **validated
by an oracle**, today our own co-simulation, later (licence permitting) also proofs against an
ASL-derived model:

1. Every ARM64 op is defined directly (a) in this repository, transcribed from the Arm ARM ASL
   of the instruction `ssaGenValue` emits (`AddWithCarry`, `DecodeBitMasks`, the bitfield move,
   `ConditionHolds` on `Flags`), each definition citing its ASL source; floats on the existing
   `GoFV.IEEE` (`GoFV/SSA/Sem/Float/*`).
2. **Co-simulation under `qemu-aarch64-static`, built here** (no code from clifv): for each op
   whose `ssaGenValue` case emits one instruction on registers (integer ALU, shifts, bitfields,
   extends, multiplies/divides, compares, conditional selects/compares, float arithmetic,
   compare and conversion: about 250 ops), a harness assembles the instruction with Go's own
   assembler (`cmd/asm`, the encodings `genssa` produces), runs it on random register and flag
   states with edge-value bias, and compares with `evalArm64` (`GoFVTest/Arm64Cosim`, a
   `scripts/arm64-cosim.sh`). The forms Go emits that a scalar model rarely covers are
   included: LSE atomics (`LDADDAL`, `LDCLRAL`, `LDORAL`, `SWPAL`, `CASAL` for the `Variant`
   atomics), `LDAXR`/`STLXR`, `CNT`/`UADDLV` (popcount), q-register pairs, `DMB`, `PRFM`.
3. The native semantic difftest (`scripts/sem-difftest.sh`) is extended to the lowered sections
   (after every pass from `lower` to `trim`, under `runL`, `runSched`, `runLoc` as appropriate):
   the same inputs must give the same outcome on every section and natively.
4. Pseudo and multi-instruction ops — memory ops, calls (`CALLstatic`, `CALLclosure`,
   `CALLinter`, `CALLtail*`), `LoweredNilCheck`, `DUFFZERO`/`DUFFCOPY`,
   `LoweredZero`/`LoweredMove`, atomics, `LoweredGetClosurePtr`/`GetCallerSP`/`GetCallerPC`,
   `GetG` (left generic on arm64, `lower.go:39-43`), `MOVDaddr` of a symbol,
   `LoweredPanicBounds*`, `LoweredMemEq`, `LoweredRound*F`, write barrier calls — are defined on
   the Phase 1 memory model as the generic op they come from (often literally
   `evalPure`/`evalValue` of that op), their instruction sequences proven in Phase 3.
5. **Deferred until the licence decision:** per-op agreement theorems
   `evalArm64 op args = result of Arm.exec (the instruction)` against an ASL-derived Lean
   model (clifv's `FV/Arm` is the candidate), which would move the ~250 definitions out of the
   trusted base and are the per-op lemmas Phase 3 (`genssa`) needs.

### Recommendation and decision: (c)

It keeps one runner for generic and unscheduled lowered SSA (`runL`, equal to `run` on generic
SSA, §1: all of Phase 1 carries over), keeps
the rule lemmas at `BitVec` cost, and checks the op definitions against the machine through
co-simulation now, with machine-checked agreement later. (b)'s advantages arrive through (c.5)
without its domain and cost problems.

**Licence decision (#384, integrator, reversible).** Nothing from clifv is vendored into or
imported by this repository until the user picks a licence for it (fv-compiler-go has no
`LICENSE` file). clifv's `FV/Arm` is LNSym-derived and Apache-2.0 (copyright Amazon.com;
clifv's additions are released under Apache-2.0 too, `third_party/NOTICE-lnsym.md` in clifv),
70 modules, 14.8k lines, Lean core + `Std`, same `v4.34.1`; once a licence exists, the options
are vendoring the needed subset into `GoFV/Arm` with every copyright header, a "Modified by
fv-compiler-go" line and the NOTICE files, or a pinned `require` (which would bring a second
IEEE core, `FV.Float`, next to `GoFV.IEEE`). Until then (c.1–c.4) are the plan. Note for the
licence decision: `GoFV.IEEE` itself was ported from clifv's `FV/Float` in Phase 1 (its module
headers say so).

## 5. Block kinds

The 25 ARM64 block kinds (AO 795-839) branch on a control value:

| Kinds | Control | Taken (`Succs[0]`) when |
| --- | --- | --- |
| `EQ NE LT LE GT GE ULT ULE UGT UGE` | flags | `ConditionHolds` of the condition |
| `LTnoov LEnoov GTnoov GEnoov` | flags | the condition ignoring V (`N`, `N∨Z`, …; AO comments) |
| `FLT FLE FGT FGE` | flags (float compare) | the ordered float condition (`MI`, `LS`, `GT`, `GE`) |
| `Z NZ` / `ZW NZW` | 64-/32-bit integer | control = 0 / ≠ 0 |
| `TBZ TBNZ` [bit] | integer | bit `AuxInt` clear / set |
| `JUMPTABLE` {sym} | index, table address | as generic `JumpTable` (index < n) |

A flags control that is `poison` is `stuck`, as Phase 1's `If`. Generic `Plain`, `Ret`,
`RetJmp`, `Exit`, `First`, `Defer` keep their Phase 1 meaning.

## 6. `runSched`: scheduled SSA (L1)

Phase 1's `run` computes its own evaluation order of a block (`GoFV/SSA/Sem/Run.lean:13-16`,
`kahn`: ready pure values first, then a ready `NilCheck`, then other roots by ID), so it ignores
`b.Values` order. That is what makes `schedule` (which only permutes `b.Values`) invisible, and
it is right for L0. From `schedule` on two things change:

- **Faulting memory ops.** `late nilcheck` (`nilcheckelim2`) deletes a `LoweredNilCheck` of `p`
  when a later value in the same block faults on a nil `p` (`faultOnNilArg0/1`, offset within
  `minZeroPage`) before any value with side effects. Under `run`, a load from `nil + off` is
  `poison` (Phase 1 §3.4), so the deletion would turn a panic into a continuation: not a
  refinement. `runSched` gives every op with `faultOnNilArg0/1` the machine behaviour: an access
  whose base is nil (`Ptr.isNil`) and whose address (base plus the op's offset) lies in
  `[0, minZeroPage)` is `panicked nilDeref` (`nilFaults`). **Wild pointers (decision, #385):** a
  pointer into `Blk.nil` other than nil itself (`Ptr.wild`: an integer address below the heap,
  or nil moved by an offset) is undefined behaviour at a nil check: under `runSched` a
  `LoweredNilCheck` of a wild pointer is `stuck` (`wildNil`), and an access through a wild base
  does not fault. Why: the machine faults with a nil dereference only in the nil page, so a
  check of `nil + X` may fault where the access at `nil + X + k` (`X + k ≥ minZeroPage`) that
  `late nilcheck` puts in its place does not; Go's nil-check removal (and `schedule`'s moving a
  check before an access at `p + k`) presumes no wild pointer (an invalid `unsafe.Pointer`).
  With it a check panics exactly when an access at `p + k` (`k < minZeroPage`) faults: when `p`
  is nil. `runL` (L0) keeps Phase 1's `NilCheck` (every `Blk.nil` pointer panics); `runLF`
  (`GoFV.Proof.RefineSched`) differs from `runL` by these faults and stuck wild checks.
- **Order is the schedule.** `runSched` evaluates the non-phi values in `b.Values` order (no
  `kahn`), with one current memory (a memory-typed value updates it; a memory argument must be
  the current memory or a load's memory still current at that point, else `stuck`).

Theorem for the `schedule` pass: if `b.Values` of `f'` is a topological order of `f`'s block
values, memory-linear, and `f'` is otherwise `f` (validated by a checker, as Phase 1 does for
`dominators`), then `Refines (runSched f') (run f)`. The pass also rewires every use of a
`LoweredNilCheck`'s result (and of `SPanchored`) to the checked pointer and turns the check
`Void` (`schedule.go:327-373`); under `run` a check that does not panic returns its pointer, so
this is the identity on non-panicking runs. A subtlety to settle first: two ready roots
not ordered by their arguments (e.g. a `LoweredNilCheck` and a `LoweredPanicBounds*` on the
same memory) are run nil check first by `run`'s rank but may be ordered the other way by Go's
`schedule` score; the outcomes differ (`nilDeref` vs `bounds`). Phase 1 hit the same question
(#96, canonical rank tie-break for NilCheck/roots). **Decision (#384): deferred to the schedule
proof.** Whoever proves `schedule` proposes on #96 either (a) a refinement that is
nondeterministic in which ready panic is reported, or (b) a schedule validator that rejects any
function in which two panicking roots are reordered relative to `run`'s rank. (b) is the default
if (a) would need changes to `OutcomeRefines`. `runSched` itself does not depend on the choice.

## 7. `runLoc`: allocated SSA (L2)

State: a register file `Reg → Val` indexed by Go's register numbers (`Config.registers`; their
`objNum` maps to Arm `GPR i`/`SFP i` in Phase 3), the flags register (`Flags`), stack slots
`LocalSlot → Val` (a write kills overlapping slots of the same `N`: `Off`/size ranges, splits
via `SplitOf`/`SplitOffset`), the current memory (`Mem`, as `runSched`), and the
activation's frame. `runLoc` never consults SSA value IDs for data — only homes:

- a value reads each argument from `Home(arg)` and writes its result to `Home(v)` (`LocPair`/
  `LocResults` for tuples; `f.tempRegs[v]` is clobbered);
- `Copy` moves between homes; `StoreReg` writes a slot, `LoadReg` reads one; a rematerialised
  value is recomputed;
- a `Phi` does nothing (Go's regalloc gives a phi and all its arguments one home, edge copies
  placed at the end of predecessors, `CheckLoweredPhi` in `ssagen`);
- flags producers write the flags register, flags consumers (`CSEL`, conditional branches,
  `ADC`/`SBC`) read it, ops with `clobberFlags` destroy it (`poison`);
- `ArgIntReg`/`ArgFloatReg` read the ABI's entry registers; `Arg` reads its parameter's incoming
  stack slot (`stackalloc.go:196`, `LocalSlot{N: param, Off: AuxInt}`), which is the parameter's
  Phase 1 frame allocation;
- a call reads its register arguments per `AuxCall.Reg` (fixed registers), stores nothing new,
  and afterwards every allocatable register except the result registers holds `poison` (Go's
  ABIInternal has no callee-saved registers besides `g`, `SP`, `ZR`); results arrive in their
  fixed registers; `MakeResult` reads the ABI result registers.

**As implemented (H6, `GoFV/SSA/Sem/RunLoc.lean`, `GoFV.SSA.runLoc`).**
- `runLoc` runs `b.Values` in order on a `LocState`. The state holds the register file by Go's
  register number, the flags register, the stack slots written so far (a write kills the
  overlapping slots of the same variable) and the current memory. Each value reads its
  arguments from their homes at the arguments' shapes and writes its result to its home. Its op
  is `runL`'s (`evalOpL`, faulting as under `runSched`) and values take their shapes as under
  `runSched` (`LMode.loc f = LMode.sched f`), so every op means what it means in L0/L1,
  `Arg`/`ArgIntReg` read their parameter as there, and a register read at a narrower type gives
  its low bits.
- A tuple's components go to the home's registers (`LocPair`, `LocResults`) in order (a result
  that is not a tuple writes `poison` to every component); a memory component is the current
  memory and a flags component the flags register. A value of type `mem` or `flags` has no home:
  it is the current memory or the flags register. So a flags value computed in one block and
  read as the control of another reads the register, including `flagalloc`'s unlinked
  recomputations.
- `LoadReg`/`StoreReg`/`Copy` move their argument. `MOVDreg`/`MOVDnop` copy the upper bits of
  their argument's register (`movdLoc`, `LocCtx.signOf`): a `LoadReg` sign-extends exactly the
  signed narrow types, a `Copy` keeps its argument's bits, any other producer as under `runL`
  (`Arm64.signExtendsIn`).
- `ZERO` reads as the 0 of the reader's shape and ignores writes. Regalloc homes zero constants of
  every type there; the first corpus run found 24 functions in which a `bool` `false` read an
  `int64` `0` from it.
- Before a value's result is written, these hold `poison`: the registers in its op's
  `regInfo.clobbers` (the caller-saved set for calls), its argument registers it clobbers
  (`clobbersArg0`/`clobbersArg1`), its `f.tempRegs` register, and the flags register for an op
  with `clobberFlags`.
- A `Phi` does nothing; one whose argument has another home is `stuck`.
- Controls are read from their homes for `stepTermL`. A `Ret`'s `MakeResult` (home
  `LocResults []`) is its arguments read from their homes.

**Refinement L1 → L2 (regalloc), recommended design: a certified checker**, in the style of
clifv's `checkAlloc` (`FV/Backend/RegallocCheck.lean`, `checkAlloc_sound`,
`docs/contracts/regalloc{,-proof}.md`), adapted to Go's in-place form:

1. *Origins.* Every value of the allocated `g` gets an origin in the pre-regalloc `f`: a value
   kept by regalloc is its own origin (same ID, op, aux, auxint; its args' origins are the
   original args); `Copy`/`LoadReg`/`StoreReg` take the origin of their argument; a
   rematerialised clone of a rematerializeable value (`v.rematerializeable()`: the op flag and
   every argument `fixedReg`, `regalloc.go:2923-2935`; constants, `MOVDaddr` of `SP`/`SB`) takes
   the origin of the original (same op/aux/auxint/args); so does a flag generator `flagalloc`
   recomputed (`copyFlags`, `flagalloc.go:258`), recursively through its tuple/flags arguments.
   `Arg` values are pre-spilled: their home is the parameter's incoming slot.
2. *Abstract state.* For each location (register, flags, slot) the set of origins it surely
   holds. Transfer per value: kill the destination, `tempRegs` and clobbers, then add `origin(v)`
   at `Home(v)`; at a call, kill everything except the results. Meet: intersection. The fixpoint
   is computed untrusted; the checker only verifies the in-state certificate per block (clifv's
   `CheckCtx.verify`), so the proof needs no fixpoint theory.
3. *Checks.* Each argument's origin is in its home's set at the use (phi arguments at the end of
   the predecessor); fixed-register constraints (ABI call args/results, `resultInArg0`,
   op `regInfo` input/output masks) hold; every memory argument is the current memory; slots
   are frame slots no `LocalAddr`/`Addr` of `g` refers to (spills are unobservable through
   memory); `f.RegAlloc` covers every value that needs a home.
4. *Theorem.* `checkRegalloc f g = true → Refines (runLoc g) (runSched f)`, by a simulation
   whose relation is "every location's set member equals that origin's value in the source
   run" (clifv's `Match`), with `runSched f` driving. Done: `GoFV.Proof.RA.checkRA_sound`
   (`docs/plans/regalloc-check.md` §4).

Go's own validation is weaker and is not a substitute: `checkFunc` skips dominance after
regalloc, and `ssagen` only checks phi homes. A *direct* simulation proof of Go's 3,623-line
allocator is not attempted: it is heuristic-heavy (eviction by next use, spill placement, edge
shuffles), and the checker makes its heuristics irrelevant to correctness — parity (H5) still
requires porting them exactly, but the port is untrusted.

**flagalloc under this plan.** `flagalloc` (L1 → L1) only appends pure recomputations of flag
generators and redirects flag arguments and controls to them; under `runSched`, where flags are
ordinary SSA values, that is a refinement by a short argument (equal pure recomputation). Its
real content — at most one flags value live, so one physical flags register suffices, including
the unlinked recomputations at block ends that have no SSA uses (`flagalloc.go:179-191`) — is
checked by the regalloc checker, which tracks the flags register as a location.

`loop rotate` (block order only) and `trim` (removal of Plain blocks into their successor,
including non-empty blocks whose successor has one predecessor, with phi-argument splicing) are
proven over `runLoc` directly; block order is not semantic until Phase 3 (fallthrough).

## 8. Environment changes for lowered code

- **Calls.** `CALLstatic {AuxCall}` etc. keep Phase 1's post-`expand calls` meaning (Go-typed
  arguments decoded from register pieces and the outgoing area via `abiparam`), so the Phase 1
  `Contract`s are reused unchanged. In `runLoc` the register pieces come from the ABI registers.
- **`g` and `GetG`.** `GetG` stays generic on arm64 (`hasGReg`, `lower.go:39-43`) and reads x28;
  callees and contracts preserve it
  (`VPre₂`).
- **Nil page.** `VPre₂` assumes no allocation lies in `[0, minZeroPage)`, so faulting accesses
  there are exactly the nil dereferences.
- **Atomics.** Lowered atomics (`LoweredAtomic*`, `*Variant`) keep Phase 1 §9.5's
  single-threaded meaning (as clifv's trusted single-core assumption, `docs/decisions/arm-model.md`).

## 9. Modules (proposed)

| Module | Content |
| --- | --- |
| `GoFV/SSA/Sem/Flags.lean` | `Flags`, `ConditionHolds`, `AddWithCarry`, `Ty.flags` encoding |
| `GoFV/SSA/Sem/Arm64/{Int,Shift,Bitfield,Mul,Cond,Float,Conv}.lean` | `evalArm64` per family, on `liftW` |
| `GoFV/SSA/Sem/Arm64/Mem.lean` | lowered loads/stores/pairs/zero/move on the Phase 1 memory, faulting variants |
| `GoFV/SSA/Sem/Arm64/Pseudo.lean` | calls, nil check, `GetG`, atomics, `MOVDaddr` of symbols, panics |
| `GoFV/SSA/Sem/RunL.lean` | `runL` (L0, §1): `evalOpL`, `stepTermL`, `Val.retypeL`, `arm64Op`, `runL_generic` |
| `GoFV/SSA/Sem/RunSched.lean`, `RunLoc.lean` | §6, §7 |
| `GoFVTest/Arm64Cosim/*.lean`, `scripts/arm64-cosim.sh` | §4 (c.2) co-simulation of `evalArm64` against qemu on Go-assembled instructions |
| `GoFV/SSA/Sem/FMA.lean` | `Contract f f'` (§2.1) |
| (deferred) `GoFV/Arm/**`, `GoFV/Proof/Arm64Agree/*.lean` | §4 (c.5), only after the licence decision |
| `GoFV/Proof/Regalloc/*.lean` | the checker, `Match`, `checkRegalloc_sound` |

## 10. Phasing (H6)

1. `Flags`, block kinds, `evalArm64` for the integer families; difftest on `lower` sections.
2. Memory and pseudo ops; difftest on all L0 sections.
3. `runSched`, faulting ops, the schedule tie-break decision (§6); difftest on L1 sections.
4. `runLoc`; difftest on L2 sections (requires the H1 export of homes). Done: `runLoc`, and the
   difftest runs `regalloc`, `loop rotate` and `trim` with it.
5. Co-simulation harness on Go's encodings (c.2), run per op family as the families land.
6. After the licence decision only: an ASL-derived Lean model and agreement theorems (c.5).

## 11. Open questions and risks

- Ready-root order (§6, #96) at `schedule`: deferred to the schedule proof, validator by default.
- Concrete addresses for lowered pointer compares and arithmetic (#156).
- Float ops whose lowering is not one instruction (`LoweredRound32F/64F`, `FMOVDgpfp` moves).
  FMA fusion is decided (§2.1).
- Popcount and other SIMD-register sequences (`VCNT`, `VUADDLV`): defined directly on the
  Phase 1 domain (they only move integer bits through a vector register), co-simulated (c.2).
- The licence question (§4): until it is answered the op definitions stay in the trusted base,
  checked by co-simulation and the native difftest only.
