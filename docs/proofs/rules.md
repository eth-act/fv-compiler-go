# Rule lemmas (`GoFV/Proof/Rules`, issue #69)

One correctness lemma per exported rewrite rule (`GoFV/Rules/Generated`,
`docs/contracts/rules.md`), in small per-op-family modules. The obligation every lemma proves
is `GoFV.Proof.Rules.Rule.Sound r`; the rule interpreter's soundness proof (`GoFV.Rules.Interp`,
later) consumes it, as clifv's interpreter proof consumes its `Opt.SimplifyFn` obligation.

## The obligation (`GoFV/Proof/Rules/Den.lean`)

`Rule.Sound r` says: for every **instance** of `r`'s match pattern whose checks and condition
hold, the value the result gives `v` refines (`Sem.Refines`) the value `v` had. Values are
those of the semantics, `GoFV.SSA.Sem.evalValue`: a pure value is
`(evalPure op (shape of its type) auxInt aux args).retype (shape of its type)`.

- **Instance** (`PEnv`): for every position of the pattern (reversed path of argument indices,
  `[]` = `v`) the value at a leaf (`_`, `x`) and the type shape, auxint and aux of an op node.
  Op-node values are computed from their arguments (`Pat.den`), so the only freedom is at the
  leaves and in the node fields.
- **Bindings** (`sigma`): each rule variable at its binding occurrence (values, `<t>` as a type
  shape, `[c]` as `auxIntTo<T>`). `same x`, `<e>` and `[e]` occurrences become hypotheses
  (`Pat.cons`); pointer identity is weakened to equality of values and type shapes, which only
  strengthens the obligation.
- **Checker facts** (`Pat.wf`): `Bool` auxints are 0 or 1 (`docs/contracts/check.md`, "Aux").
  The shift and division flags of the semantics (`auxInt == 1`) and `shiftIsBounded`
  (`auxInt != 0`) agree only under this fact.
- **Top type**: the top value before `retype` has the shape of `v`'s type (`Val.hasTy`), i.e.
  `v`'s type is not narrower than its op. See "Narrow result types".
- **Leaf types** (`Pat.typed`): a leaf `x` is bound with its position, so `x.Type` is the
  instance's type at the leaf, and every leaf value has its type's shape. Without it a rule
  whose result uses a leaf's type (`(Neg64 <y.Type> y)`, `(Add64 <c.Type> c d)` under
  `c.Type.Size() == 8`) is unprovable: the leaf could be an 8-bit integer typed `int64`.
- **Argument shapes** (`Pat.argsOK e.ty [] r.pat = true`, #69 RuleProofs7): at every op node
  the arguments' types have the shapes `argShapeOk` asks for: the pointer argument of `OffPtr`,
  `AddPtr`, `PtrIndex`, `IsNonNil` and both of `EqPtr`/`NeqPtr` pointer-typed, the offset of
  `AddPtr`/`PtrIndex` a 64-bit integer, `Convert` between a pointer and a 64-bit integer (by
  its result shape). With `Pat.typed` the leaves then have these shapes. Without it
  `generic.rules:964` (`(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])`) is false: a
  `uintptr` leaf `p = 2^40-8` under a pointer-typed inner `OffPtr` becomes the pointer
  `Ptr.ofAddr p` plus `y` (its allocation kept), while the result adds `x+y` as an integer;
  likewise `:970` with an `int32` index (`Mul64` of a narrower integer is `poison`).
- **Expressions** (conditions, `[auxint]`, `<type>`) are evaluated by `evalE`, a total pure
  evaluator mirroring `GoFV.Rules.Eval.eval` on integers, booleans, op constants, type shapes
  (`typ.<T>`, `types.Types[k]`, `t.Size()` of an integer/boolean shape, `t.Elem().Size()` of a
  pointer shape with a known element size: `t.Elem()` is the record `{Size}`) and the pure
  `rewrite.go` helpers (`isPowerOfTwo`, `log*`, `ntz*`, `nlz*`, `bits.*`, `uaddOvf`,
  `shiftIsBounded`, the `magic`/`divisible` helpers, …). Everything else — `x.Uses`,
  `clobber`, `config` fields, `canRotate`, symbol helpers, floats, `x.Op` — comes from an
  `Oracle`, over which the obligation is universally quantified. So a rule whose correctness
  needs such an atom cannot be proved from this denotation (none of the P1 rules needs one);
  side conditions such as `x.Uses == 1 && clobber(x)` are simply ignored. The same holds on the
  result side: an aux, type or auxint the evaluator does not model is the oracle's, i.e. the
  rule must be correct for every choice.
- **Typed oracle** (`Oracle.BoolTyped`): the oracle answers every expression of Go type `bool`
  with a boolean. Without it the oracle could answer `div.Uses` with a non-integer, so
  `div.Uses == 1` is not a boolean, `&&` does not evaluate, and the whole condition of
  `div.Uses == 1 && x.Op != OpConst16 && sdivisibleOK16(c)` becomes the oracle's: then
  `r_divisible_116` would have to hold for `c = -3`, where `sdivisibleOK16` is false and the
  result is wrong (found by agent Divisible). `rule_unfold` replaces each such atom in the
  condition by a fresh `Bool` (`rule_oracle_bool`).
- **Commutative patterns**: only the written argument order is considered. The interpreter's
  swapped matches are covered by `GoFV/Proof/Rules/Comm.lean` (`commOpsP1_sound`: every
  phase-P1 op that a pattern marks `commute` is symmetric in its first two arguments).

What the interpreter's proof must supply when it applies `Rule.Sound`: the instance read off
the matched values (leaf values from the registers, node fields from the values), the
condition's evaluation (`GoFV.Rules.Eval.eval` agrees with `evalE` where `evalE` does not
defer to the oracle; `eval` is total, with fuel for the nesting depth, as are the matcher and
result construction),
the checker facts, that `typ.<T>`/`types.Types[k]` of the export's `Config.Types` have the
shapes of `typShape`/`typesShape`, and `CommSound` for swapped matches. `Rule.Sound` ignores
`@b` placement and positions; a copy result's new type is the interpreter's concern
(`Val.retype` is idempotent, so a copied value is unchanged).

### Assumptions to discharge (#108)

`Rule.Sound` assumes four typing facts the interpreter's proof must establish from a semantic
invariant of `GoFV.SSA.Sem`, of the checker or of the rule evaluator, not from the rule:

- **Register typing** (for `Pat.typed`): in every reachable state, every register `v` the
  match reads as a leaf holds a value of its type's shape,
  `(regVal v).hasTy (tabs.ty v.Type) = true` (`Val.hasTy`; `poison` has every shape). The
  instance then sets `e.leaf p := regVal v` and `e.ty p := tabs.ty v.Type`. This is the same
  register-typing invariant the phi passes need: `GoFV.Proof.Typed.hasTy` /
  `evalValue_hasTy` (from `Val.retype_hasTy`, total-shaping `retype`, #108). A 64-bit integer
  leaf may also be a pointer without a concrete address (`Val.hasTy`), so
  `val_poison_of_asInt_none` gives `poison` or (at 64 bits) a pointer.
- **Top type** (`hty`): the matched value's op computes a value of its type's shape before
  `retype`, i.e. no narrow result types (see "Narrow result types").
- **Argument shapes** (`Pat.argsOK`): the checked rewrite passes' validator checks them on the
  matched values' types (`RewriteCheck.ruleOK`), so `checkedRewrite_refines` discharges them
  from the validator; Semantics' argument checks in `GoFV.SSA.check` make the validator never
  reject for this reason.
- **Typed oracle** (`Oracle.BoolTyped or := ∀ x, exprTy [] x = .bool → ∃ b, or.dv x = .bool b`):
  the oracle built from `GoFV.Rules.Eval.eval` answers a `bool`-typed expression with a
  boolean, i.e. `eval` of a well-typed `bool` expression that does not fail is a boolean.
  `GoFV.Opt.RewriteCheck.oracle` (`true` for every `bool` expression) and the oracles of
  `rule-sat` and `NonVacuous.lean` (`Oracle.const_boolTyped`) satisfy it.

## Classification

`GoFVTest/Proof/RuleClass.lean` classifies each rule by the semantic phase of its ops
(`docs/plans/semantics.md` §9): `P1` (every op of pattern and result has a phase-P1 arm in
`evalPure`: integers, booleans, tuples; fixed arity; build or variable-copy result), `P2` (the
same, but some ops have only a later `evalPure` arm: pointers, composites, `Load` from a memory
value, `SelectN`; `p2Names`, snapshot of #98/#141), else the first op without an `evalPure` arm by
priority `call` > `mem` > `float` > `ptr` (`ConstString`, `Addr`, `NilCheck`, …) > `phi`;
`block` for block rules. `Rule.Sound`'s denotation (`Pat.den` through `evalPure`) covers the
`P1` and `P2` rules ("pure"); the others need an obligation about memory, effects or blocks.

<!-- BEGIN classes -->
<!-- Generated by scripts/rule-proofs.py table. -->

| File | P1 | P2 | mem | call | float | ptr | phi | block | Total |
| --- | --: | --: | --: | --: | --: | --: | --: | --: | --: |
| `generic` | 1336 | 72 | 104 | 47 | 68 | 19 | 5 | 3 | 1654 |
| `dec` | 0 | 37 | 8 | 0 | 0 | 2 | 0 | 0 | 47 |
| `divisible` | 32 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 32 |
| `divmod` | 27 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | 29 |
| all | 1395 | 109 | 112 | 47 | 68 | 23 | 5 | 3 | 1762 |

<!-- END classes -->

## Coverage

Per rule file and op family of the top op. *Proven*: a `Rule.Sound` lemma is merged.
*False*: the rule is wrong under the stated semantics (see "Findings"). *Not P1*: the rule
needs a later phase of the semantics.

<!-- BEGIN coverage -->
<!-- Generated by scripts/rule-proofs.py table. -->

| File | Family | Proven | Pending (P1/P2) | False | Not pure | Total |
| --- | --- | --: | --: | --: | --: | --: |
| `dec` | ArrayMake | 0 | 1 | 0 | 0 | 1 |
| `dec` | ArraySelect | 0 | 4 | 0 | 0 | 4 |
| `dec` | ComplexImag | 0 | 3 | 0 | 0 | 3 |
| `dec` | ComplexReal | 0 | 3 | 0 | 0 | 3 |
| `dec` | IData | 0 | 2 | 0 | 0 | 2 |
| `dec` | IMake | 0 | 1 | 0 | 1 | 2 |
| `dec` | ITab | 0 | 2 | 0 | 0 | 2 |
| `dec` | Load | 0 | 5 | 0 | 0 | 5 |
| `dec` | SliceCap | 0 | 2 | 0 | 0 | 2 |
| `dec` | SliceLen | 0 | 2 | 0 | 0 | 2 |
| `dec` | SlicePtr | 0 | 2 | 0 | 0 | 2 |
| `dec` | SlicePtrUnchecked | 0 | 1 | 0 | 0 | 1 |
| `dec` | Store | 0 | 0 | 0 | 8 | 8 |
| `dec` | StringLen | 0 | 2 | 0 | 0 | 2 |
| `dec` | StringPtr | 0 | 2 | 0 | 0 | 2 |
| `dec` | StructMake | 0 | 1 | 0 | 0 | 1 |
| `dec` | StructSelect | 0 | 4 | 0 | 1 | 5 |
| `divisible` | Eq | 12 | 4 | 0 | 0 | 16 |
| `divisible` | Neq | 12 | 4 | 0 | 0 | 16 |
| `divmod` | Div | 11 | 12 | 4 | 2 | 29 |
| `generic` | Add | 88 | 1 | 4 | 2 | 95 |
| `generic` | AddPtr | 1 | 1 | 0 | 0 | 2 |
| `generic` | And | 40 | 8 | 0 | 0 | 48 |
| `generic` | AndB | 0 | 36 | 0 | 0 | 36 |
| `generic` | ArraySelect | 0 | 2 | 0 | 0 | 2 |
| `generic` | BitLen | 0 | 8 | 0 | 0 | 8 |
| `generic` | Block | 0 | 0 | 0 | 3 | 3 |
| `generic` | Ceil | 0 | 0 | 0 | 1 | 1 |
| `generic` | Com | 12 | 0 | 0 | 0 | 12 |
| `generic` | CondSelect | 0 | 59 | 0 | 0 | 59 |
| `generic` | ConstInterface | 0 | 1 | 0 | 0 | 1 |
| `generic` | ConstSlice | 0 | 2 | 0 | 0 | 2 |
| `generic` | ConstString | 0 | 0 | 0 | 4 | 4 |
| `generic` | Convert | 0 | 5 | 0 | 0 | 5 |
| `generic` | Ctz | 0 | 8 | 0 | 0 | 8 |
| `generic` | Cvt | 0 | 0 | 0 | 11 | 11 |
| `generic` | CvtBoolToUint | 0 | 2 | 0 | 0 | 2 |
| `generic` | Div | 20 | 2 | 0 | 4 | 26 |
| `generic` | Eq | 52 | 4 | 0 | 2 | 58 |
| `generic` | EqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | EqInter | 0 | 1 | 0 | 0 | 1 |
| `generic` | EqPtr | 0 | 9 | 0 | 11 | 20 |
| `generic` | EqSlice | 0 | 1 | 0 | 0 | 1 |
| `generic` | Floor | 0 | 0 | 0 | 1 | 1 |
| `generic` | IMake | 0 | 1 | 0 | 1 | 2 |
| `generic` | InterLECall | 0 | 0 | 0 | 1 | 1 |
| `generic` | IsInBounds | 0 | 29 | 0 | 0 | 29 |
| `generic` | IsNonNil | 0 | 3 | 0 | 3 | 6 |
| `generic` | IsSliceInBounds | 0 | 8 | 0 | 0 | 8 |
| `generic` | Leq | 60 | 0 | 0 | 2 | 62 |
| `generic` | Less | 52 | 8 | 0 | 2 | 62 |
| `generic` | Load | 0 | 2 | 0 | 33 | 35 |
| `generic` | Lsh | 65 | 23 | 0 | 0 | 88 |
| `generic` | MemEq | 0 | 11 | 0 | 0 | 11 |
| `generic` | Mod | 24 | 5 | 0 | 0 | 29 |
| `generic` | Move | 0 | 0 | 0 | 25 | 25 |
| `generic` | Mul | 44 | 8 | 0 | 8 | 60 |
| `generic` | Neg | 24 | 0 | 0 | 2 | 26 |
| `generic` | Neq | 44 | 8 | 0 | 2 | 54 |
| `generic` | NeqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | NeqInter | 0 | 1 | 0 | 0 | 1 |
| `generic` | NeqPtr | 0 | 9 | 0 | 11 | 20 |
| `generic` | NeqSlice | 0 | 1 | 0 | 0 | 1 |
| `generic` | NilCheck | 0 | 0 | 0 | 8 | 8 |
| `generic` | Not | 27 | 2 | 0 | 4 | 33 |
| `generic` | OffPtr | 2 | 0 | 0 | 0 | 2 |
| `generic` | Or | 72 | 4 | 4 | 0 | 80 |
| `generic` | OrB | 0 | 36 | 0 | 20 | 56 |
| `generic` | Phi | 0 | 0 | 0 | 5 | 5 |
| `generic` | PopCount | 0 | 8 | 0 | 0 | 8 |
| `generic` | PtrIndex | 1 | 1 | 0 | 0 | 2 |
| `generic` | RotateLeft | 88 | 0 | 0 | 0 | 88 |
| `generic` | Round | 0 | 0 | 0 | 2 | 2 |
| `generic` | RoundToEven | 0 | 0 | 0 | 1 | 1 |
| `generic` | Rsh | 116 | 24 | 0 | 0 | 140 |
| `generic` | Select | 0 | 3 | 0 | 0 | 3 |
| `generic` | SelectN | 0 | 0 | 0 | 15 | 15 |
| `generic` | SignExt | 15 | 0 | 0 | 0 | 15 |
| `generic` | SliceCap | 0 | 4 | 0 | 1 | 5 |
| `generic` | SliceLen | 0 | 3 | 0 | 3 | 6 |
| `generic` | SliceMake | 0 | 2 | 0 | 0 | 2 |
| `generic` | SlicePtr | 0 | 1 | 0 | 0 | 1 |
| `generic` | Slicemask | 0 | 4 | 0 | 0 | 4 |
| `generic` | Sqrt | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticCall | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticLECall | 0 | 0 | 0 | 24 | 24 |
| `generic` | Store | 0 | 0 | 0 | 21 | 21 |
| `generic` | StringLen | 0 | 1 | 0 | 0 | 1 |
| `generic` | StringPtr | 0 | 0 | 0 | 1 | 1 |
| `generic` | StructSelect | 0 | 3 | 0 | 1 | 4 |
| `generic` | Sub | 68 | 0 | 0 | 2 | 70 |
| `generic` | Trunc | 32 | 0 | 0 | 1 | 33 |
| `generic` | Xor | 56 | 8 | 4 | 0 | 68 |
| `generic` | Zero | 0 | 0 | 0 | 6 | 6 |
| `generic` | ZeroExt | 12 | 0 | 0 | 0 | 12 |
| all | | 1060 | 428 | 16 | 258 | 1762 |

<!-- END coverage -->

Regenerate both tables with `scripts/rule-proofs.py table` (it reruns the classifier if
`tmp/rules/class.tsv` is missing).

## Proven-only rewrite passes (issue #113)

`scripts/rule-proofs.py proven` writes `GoFV/Rules/Proven.lean` (the `generic`, `divisible`
and `divmod` rule sets restricted to the rules with a merged `Rule.Sound` lemma, in matching
order, no block rules) and `GoFV/Proof/Rules/Proven.lean` (`generic_allSound`, … :
`RuleSet.AllSound`, every value rule of the set is sound; `GoFV/Proof/Rules/AllSound.lean`).
Rerun it whenever lemmas are added. `GoFV.Opt.optProven`/`divisibleProven`/`divmodProven` run
`applyRewrite` with these sets (clifv's `--opt-proven-only`); the rewrite passes' theorems take
`RuleSet.AllSound` of their rule set as hypothesis.

**Checked passes.** `GoFV.Opt.optChecked`/`divisibleChecked`/`divmodChecked` run the proven-only
pass with its log on (`RwState.log`: every fired value rule with the definitions it built, copy
and control replacements, phi eliminations, block rules) and keep the result only if
`GoFV.Opt.RewriteCheck.validate` accepts it (else the input): replaying the log on the input's
definitions, each rule firing must be an instance of its rule as `Rule.Sound` states it (pattern
match on the definitions through term ops only, swapped only at `commOps`, `Pat.cons` with
`same` only of leaf variables, `Pat.wf`, condition by `evalE` with an oracle read off the built
nodes that answers every boolean-typed expression with a boolean (`Oracle.BoolTyped`), top op
producing its type's shape (`natShape`, or `ptrTop`: `OffPtr`/`AddPtr`/`PtrIndex`/`Convert`
at a pointer or `Convert` at the 64-bit integer shape, `evalPure_ptrTop`), argument shapes
(`Pat.argsOK` on the matched types), integer-, boolean- or pointer-shaped leaves, built nodes = `resDen`, no cyclic
match), a copy-argument replacement is replayed when its source is reached from the old argument
through copies of compatible shape, no phi elimination or block rule, the arguments of listed
values and the controls are listed (`closedOK`, input and output), and every definition and
control of the result must be the replayed one up to copies of compatible shape; the atoms
(phis, roots, frame values incl. `GetClosurePtr`/`GetCallerSP`) must be unchanged, in the same
order, or droppable (`dropAtom`: no panic, no memory effect). These are the passes the theorems
are about (issue #113).

`lake exe opt-proven-probe <corpus>` runs the full, proven-only and checked variants on every
stock instance's input. Quick corpus (`quick-v1`, 9,297 functions; 1,024 proven rules; "rules
fired": value and block rules, `RwState.fired`, each instance run on the stock input):

| Pass | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept | Validator rejects | Checked parity |
| --- | --: | --: | --: | --: | --: | --: | --: | --: |
| opt | 100.00% | 43.34% | 69.28% | 99,454 | 17,343 | 17.44% | 1 | 43.34% |
| middle opt | 100.00% | 77.47% | 94.26% | 11,934 | 1,662 | 13.93% | 6 | 77.43% |
| late opt | 100.00% | 84.60% | 1.37% | 8,314 | 47 | 0.57% | 0 | 84.60% |
| divisible | 100.00% | 99.96% | 62.33% | 9 | 4 | 44.44% | 0 | 99.96% |
| divmod | 100.00% | 99.02% | 96.91% | 441 | 273 | 61.90% | 0 | 99.02% |

Functions all of whose rewrite sections the checked passes reproduce exactly: 3,547 of 9,297
(38.15%; 3,536 with 957 and with 993 proven rules: the first divisible/divmod lemmas, #137, add
the 11). Later counts are in "Firing frequency" (`scripts/rule-proofs.py fire`): 3,562 with
1,048 proven rules, 3,597 (38.69%) with 1,056 (Mul by ±2^k), 4,701 (50.56%) with 1,060
(`Pat.argsOK`, pointer leaves and tops in the validator, OffPtr/PtrIndex/AddPtr).

"No-op": the proven-only output equals the input (late opt's inputs carry dead values that
every variant removes). The proven-only passes keep copy elimination, phi elimination and
dead-value removal. Validator rejections (all REJECT lines of the probe): 6 top ops whose value
is narrower than the op (`natShape`, `generic.rules:1189/1192` on divmod-built values in middle
opt; "Narrow result types", correct rejections) and 1 phi elimination (opt). Before the
copy-argument replay 25 more firings were rejected (the rule matched after copy elimination had
rewritten an argument the replay had not seen), and dead `GetClosurePtr`/`GetCallerSP` removal
168 late opt results.

**Proof structure.** Pure values are terms over the *atoms* (phis, roots, frame values):
`GoFV.Proof.Term.den`, `TermRef`. Two theorems combine into the passes' refinement
(`GoFV/Proof/Pass/Rewrite.lean`): the validator's soundness `validate_termRef` (an accepted log
makes every atom argument and control of the output refine the input's as a term:
`Term.AtomArgsRef`, `Term.ControlsRef`) and the atom simulation
`GoFV.Proof.AtomSim.atomSim_refines` (two checked functions with the same atoms, schedule roots
and terminators whose atom arguments and controls refine as terms: `RefinesUnder Env.Mono`;
lock-step `runLoop_simE` with refined memories, `evalOp_mono` at atoms). The atom simulation's
witness `GoFV.Proof.Witness.addZero_atomSim` runs `checkedRewrite` on the hand-written
`addZero(n) = 0 + n` with the rule `(Add64 (Const64 [0]) x) => x` (kernel evaluation), discharges
all premises (the rewritten argument `v4 → v2` and the `MakeResult` control by hand) and reads
`addZero(7) = 7` off the output.

**Theorems** (`GoFV/Proof/Pass/Rewrite.lean`): `checkedRewrite_refines (hs : s.AllSound)
(h : checkedRewrite (Interp.Table.ofRuleSet s) penv f = .ok out) (hf : check ce f = .ok ())
(hg : check ce' out.func = .ok ()) : RefinesUnder Env.Mono out.tables out.func penv.tables f`,
and its instances `opt_refines` (`optChecked`: `opt`, `middle opt`, `late opt`),
`divisible_refines`, `divmod_refines`, whose proofs are `generic_allSound`, `divisible_allSound`,
`divmod_allSound`: the theorems are about the passes restricted to the proven rules
(`GoFV.Rules.Proven`, regenerated by `scripts/rule-proofs.py proven`), so every merged rule lemma
widens what the theorem covers without changing its statement. Register typing at the leaves
(`Rule.Sound`'s `Pat.typed`) is `Term.retypeShapes` (#108). Witness:
`GoFV.Proof.Witness.addZero_refines` (the theorem on the `addZero` run above). Validator
soundness: `validate_termRef` (`GoFV/Proof/Pass/RewriteTerm*.lean`).

## Firing frequency: what keeps the proven-only passes from stock (#69, #113)

`scripts/rule-proofs.py fire` runs `lake exe rule-fire-probe` (`GoFVTest/RuleFireProbe.lean`)
on the quick corpus: for every rewrite section, the full pass with its log, the proven-only pass
and the checked pass. Per unproven rule (`file.rules:line Op`, block rules as `block <Kind>`):
*Firings* in the full passes; *Sole obstacle*: functions off stock under the proven-only passes
whose sections off stock fire exactly this one unproven rule in the full pass; *Unblocks*:
functions that reach stock in every rewrite section when this rule alone is added to the proven
rules (tried for every function with at most two unproven rules). Rules are proved in descending
order of *Unblocks*. Rows: every rule with a non-zero count, then the 15 most frequent others.

<!-- BEGIN fire -->
<!-- Generated by scripts/rule-proofs.py fire. -->

Corpus `quick-v1/plain`: 9297 functions with a rewrite section; every section at stock under the proven-only passes 4701, under the checked passes 4701 (validator the only obstacle: 0). Functions off stock by the number of unproven rules the full passes fire on their sections off stock: 0: 2, 1: 1240, 2: 1061, 3 or more: 2293.

| Rule | Lemma | Class | Firings | Sole obstacle | Unblocks |
| --- | --- | --- | --: | --: | --: |
| `generic.rules:1022 ConstString` | `r_generic_1022` | ptr | 6924 | 380 | 380 |
| `generic.rules:1367 NilCheck` | `r_generic_1367` | call | 1909 | 127 | 127 |
| `generic.rules:1381 NilCheck` | `r_generic_1381` | mem | 5901 | 83 | 83 |
| `generic.rules:1062 NilCheck` | `r_generic_1062` | mem | 686 | 70 | 70 |
| `generic.rules:974 Load` | `r_generic_974` | mem | 580 | 65 | 65 |
| `block If` | `block` | block | 8570 | 63 | 63 |
| `generic.rules:1684 NeqPtr` | `r_generic_1684` | P2 | 1246 | 63 | 63 |
| `generic.rules:1071 Convert` | `r_generic_1071/r_generic_1071_2` | P2 | 218 | 41 | 41 |
| `generic.rules:1057 ConstInterface` | `r_generic_1057` | P2 | 524 | 40 | 40 |
| `generic.rules:973 StructSelect` | `r_generic_973` | ptr | 5789 | 39 | 39 |
| `generic.rules:800 Load` | `r_generic_800` | mem | 1446 | 33 | 33 |
| `generic.rules:1384 NilCheck` | `r_generic_1384` | mem | 488 | 29 | 29 |
| `generic.rules:1072 Convert` | `r_generic_1072` | P2 | 291 | 20 | 20 |
| `generic.rules:1375 NilCheck` | `r_generic_1375` | mem | 679 | 17 | 17 |
| `generic.rules:1044 ConstSlice` | `r_generic_1044` | P2 | 381 | 16 | 16 |
| `generic.rules:322 AndB` | `r_generic_322/r_generic_322_2` | P1 | 116 | 16 | 16 |
| `divmod.rules:180 Div64u` | `r_divmod_180` | P1 | 76 | 14 | 14 |
| `generic.rules:1053 SliceMake` | `r_generic_1053` | P2 | 88 | 12 | 12 |
| `generic.rules:610 Less64` | `r_generic_610_3` | P1 | 160 | 11 | 11 |
| `generic.rules:1015 ConstString` | `r_generic_1015` | ptr | 194 | 9 | 9 |
| `generic.rules:806 Load` | `r_generic_806` | mem | 488 | 6 | 6 |
| `generic.rules:1683 EqPtr` | `r_generic_1683` | P2 | 1734 | 5 | 5 |
| `generic.rules:827 Load` | `r_generic_827` | mem | 1151 | 5 | 5 |
| `generic.rules:336 AndB` | `r_generic_336/r_generic_336_2` | P1 | 37 | 5 | 5 |
| `generic.rules:372 OrB` | `r_generic_372/r_generic_372_2/r_generic_372_3/r_generic_372_4` | P1 | 35 | 5 | 5 |
| `generic.rules:1075 Convert` | `r_generic_1075/r_generic_1075_2` | P2 | 21 | 5 | 5 |
| `generic.rules:2159 Zero` | `r_generic_2159` | mem | 6 | 5 | 5 |
| `generic.rules:975 Store` | `r_generic_975` | mem | 810 | 3 | 3 |
| `generic.rules:992 ArraySelect` | `r_generic_992` | P2 | 361 | 3 | 3 |
| `generic.rules:2155 Move` | `r_generic_2155` | mem | 145 | 3 | 3 |
| `divmod.rules:171 Div32u` | `r_divmod_171` | P1 | 30 | 3 | 3 |
| `generic.rules:2371 CondSelect` | `r_generic_2371/r_generic_2371_2/r_generic_2371_3` | P1 | 9 | 3 | 3 |
| `generic.rules:1743 Move` | `r_generic_1743` | mem | 8 | 3 | 3 |
| `divmod.rules:206 Div64u` | `r_divmod_206` | P1 | 6 | 3 | 3 |
| `generic.rules:1352 Zero` | `r_generic_1352` | call | 85 | 2 | 2 |
| `generic.rules:1357 Store` | `r_generic_1357` | call | 28 | 2 | 2 |
| `generic.rules:2342 CondSelect` | `r_generic_2342/r_generic_2342_2/r_generic_2342_3` | P1 | 24 | 2 | 2 |
| `generic.rules:1328 Mul64F` | `r_generic_1328` | float | 7 | 2 | 2 |
| `generic.rules:346 OrB` | `r_generic_346/r_generic_346_2` | P1 | 6 | 2 | 2 |
| `generic.rules:340 AndB` | `r_generic_340/r_generic_340_2` | P1 | 4 | 2 | 2 |
| `generic.rules:1031 SliceLen` | `r_generic_1031` | P2 | 1524 | 1 | 1 |
| `generic.rules:1730 SelectN` | `r_generic_1730/r_generic_1730_2` | call | 139 | 1 | 1 |
| `generic.rules:1592 MemEq` | `r_generic_1592` | P2 | 51 | 1 | 1 |
| `divmod.rules:148 Div64u` | `r_divmod_148` | P1 | 29 | 1 | 1 |
| `generic.rules:1005 Store` | `r_generic_1005` | mem | 23 | 1 | 1 |
| `divmod.rules:159 Div16u` | `r_divmod_159` | P1 | 20 | 1 | 1 |
| `generic.rules:321 AndB` | `r_generic_321/r_generic_321_2` | P1 | 16 | 1 | 1 |
| `generic.rules:919 Store` | `r_generic_919` | mem | 15 | 1 | 1 |
| `generic.rules:2158 Zero` | `r_generic_2158` | mem | 13 | 1 | 1 |
| `generic.rules:369 AndB` | `r_generic_369/r_generic_369_2/r_generic_369_3/r_generic_369_4` | P1 | 12 | 1 | 1 |
| `generic.rules:2146 Move` | `r_generic_2146` | mem | 12 | 1 | 1 |
| `generic.rules:345 OrB` | `r_generic_345/r_generic_345_2` | P1 | 9 | 1 | 1 |
| `generic.rules:360 OrB` | `r_generic_360/r_generic_360_2` | P1 | 7 | 1 | 1 |
| `generic.rules:1183 Eq32` | `r_generic_1183_2` | P1 | 6 | 1 | 1 |
| `divmod.rules:232 Div64u` | `r_divmod_232` | P1 | 5 | 1 | 1 |
| `generic.rules:334 AndB` | `r_generic_334/r_generic_334_2` | P1 | 5 | 1 | 1 |
| `generic.rules:531 Rsh32Ux64` | `r_generic_531` | P1 | 3 | 1 | 1 |
| `generic.rules:2355 CondSelect` | `r_generic_2355/r_generic_2355_2/r_generic_2355_3/r_generic_2355_4` | P1 | 3 | 1 | 1 |
| `divisible.rules:152 Eq64` | `r_divisible_152` | P1 | 2 | 1 | 1 |
| `generic.rules:2166 Or64` | `r_generic_2166_2` | P1 | 2 | 1 | 1 |
| `generic.rules:2168 Or16` | `r_generic_2168_2` | P1 | 1 | 1 | 1 |
| `generic.rules:2167 Or32` | `r_generic_2167_2` | P1 | 1 | 1 | 1 |
| `generic.rules:357 OrB` | `r_generic_357/r_generic_357_2` | P1 | 1 | 1 | 1 |
| `generic.rules:275 IsSliceInBounds` | `r_generic_275` | P1 | 1656 | 0 | 0 |
| `generic.rules:1012 StringLen` | `r_generic_1012` | P2 | 1091 | 0 | 0 |
| `generic.rules:255 IsInBounds` | `r_generic_255` | P1 | 889 | 0 | 0 |
| `generic.rules:1011 StringPtr` | `r_generic_1011` | ptr | 610 | 0 | 0 |
| `generic.rules:1032 SliceCap` | `r_generic_1032` | P2 | 580 | 0 | 0 |
| `generic.rules:278 IsSliceInBounds` | `r_generic_278` | P2 | 289 | 0 | 0 |
| `generic.rules:1646 EqPtr` | `r_generic_1646` | P2 | 269 | 0 | 0 |
| `generic.rules:271 IsSliceInBounds` | `r_generic_271` | P1 | 247 | 0 | 0 |
| `generic.rules:997 Store` | `r_generic_997` | mem | 241 | 0 | 0 |
| `generic.rules:813 Load` | `r_generic_813` | mem | 224 | 0 | 0 |
| `generic.rules:585 Neq64` | `r_generic_585_3` | P1 | 204 | 0 | 0 |
| `generic.rules:2255 Load` | `r_generic_2255` | mem | 181 | 0 | 0 |
| `generic.rules:1035 SlicePtr` | `r_generic_1035` | P2 | 179 | 0 | 0 |
| `generic.rules:791 NeqInter` | `r_generic_791` | P2 | 174 | 0 | 0 |
| `generic.rules:792 EqSlice` | `r_generic_792` | P2 | 138 | 0 | 0 |

<!-- END fire -->

## Proof method (`GoFV/Proof/Rules/Tactic.lean`)

`rule_auto` = `rule_unfold` (reduce `Rule.Sound r` for the concrete rule data: denotation
definitions by `simp only`; `evalPure`, `Op.auxType` and the helper dispatch by dsimprocs
that unfold once at a constructor or string literal, so `simp` never sees the 446-arm
`match`es) → `rule_norm` (`simp_all` with the op families unfolded to `BitVec`/`Bool` terms)
→ case splits (`rule_split1`: whether a leaf is an integer of the width its consumer reads
— the leaf is then replaced by that integer —, whether a node's type is an integer of another
width, `if` conditions, and only when none is left the disjunctions: the checker's `Bool`
auxints, `||` in conditions) → `rule_close` (auxint reads generalized to bounded `Int`s,
constants pushed into `BitVec.ofInt`, then `rfl`; a rotation written as two shifts by one
rewrite with `rot_add_sub`/`rot_or_sub`/… and the amount bound by `bv_omega` (`rule_rot`); a
ring identity by `grind` after complements and constant shifts become ring terms; a bitwise
identity per bit (`ext`, `simp`) after all-ones constants become `BitVec.allOnes`
(`rule_bits`); `bv_decide` only as the last resort). The rules' `c&d`, `c|d`, `c^d` constant
folds (`GoFV.Rules.bitwise` on 64-bit patterns) are pushed into `BitVec` by `rule_arith`
(`ofNat_pat64`, `BitVec.ofNat_and`, …).

Amounts and comparisons without `bv_decide` (#69, RuleProofs4): `rule_rotamt` (a rotation by
two amounts, nested rotations, `x.rotateLeft a = x`: `rotateLeft_congr`,
`rotateLeft_rotateLeft`, `rotateLeft_eq_self`; a rotation reads its amount at any width modulo
the width, `rotate_retype_amt`), `rule_shamt` (constant shifts: `ofInt_goShl`/`ofInt_goShr_*`
folds, `shl_shl`/`ushr_ushr`/`sshr_sshr`, `shl_ushr_shl`/`ushr_shl_ushr`, masks
`ushr_shl`/`sshr_shl`/`shl_ushr`, shifts by at least the width) and `rule_cmpc` (comparisons
against constants as `toNat`/`toInt` arithmetic, `toInt_omega`) turn amounts and conditions
into `Nat`/`Int` arithmetic (`rule_amt`, `rule_cmp`: `wrapInt` as `%`, `pat64`, `toNat_*`) and
close with `omega`; `rule_omega_facts` adds what `omega` cannot see (`a &&& b` bounds and
remainders by the goal's power-of-two modulus, `Int.tmod` sign cases, `(x >>> n).toNat`
bounds). The structural lemmas are applied `with_reducible`: at default transparency a failed
`apply rotateLeft_eq_self` unfolds `sshiftRight` of a 64-bit vector (heartbeat timeouts).
`rule_subst` replaces `subst_vars`, whose `whnf` of both sides evaluated conditions such as
`bitwise int16 (· &&& ·) c 15 = 15` down to `2 ^ 64` (maximum recursion depth).

Extensions and truncations (#69, RuleProofs5): constant folds of `ZeroExt`/`SignExt`/`Trunc`
by `rule_arith` (`setWidth_ofInt_of_le`/`_of_ge`, `signExtend_ofInt`); a retype to a type that
of the same width is the identity (`retype_int_of_not_other`, `rule_sem`; any other shape is
`poison`, `tyOtherInt`); a boolean retyped is a boolean at `bool` and `poison` elsewhere
(`retype_bool`, split on `tyIsBool`); negated
comparisons and boolean equations (`not_slt_eq`, …, `not_beq_eq`, `rule_close_s`); `rule_ext`
closes a value truncated and extended again after a shift cleared or sign-filled its high bits
(`ushr_setWidth_setWidth`, `sshr_setWidth_signExtend`), else both sides as `toNat` arithmetic
(low-bit masks `a &&& 255` as `a % 256`, `rule_amt`). `rule_shamt` runs `congr 1` at reducible
transparency: at default transparency it unfolded `BitVec.ofInt 16 c &&& x` into a
maximum-recursion error, which `first` does not catch (runtime exceptions pass through it).

Division and remainder (#69, RuleProofs5): `rule_div` folds constants (`sdiv_ofInt`,
`srem_ofInt`: Go's truncated `/`, `%` on auxints in range, ranges by `omega`; `udiv_ofInt`,
`umod_ofInt` on the low bits), rewrites a negated divisor (`sdiv_neg_ofInt`, `srem_neg_right`)
and the minimal one (`sdiv_intMin_and_neg`: `x / MIN = (x & -x) >>> (w-1)`), and a remainder as
`x - (x / y) * y` (`sub_udiv_mul`, `sub_sdiv_mul`, unconditional). `rule_pow2` turns the
`isPowerOfTwo(uintN(c))` condition into `c = 2 ^ (bitsLen c - 1)` (`isPow2_toNat`) and the
division into a shift (`udiv_pow2`) or the remainder into a mask (`umod_pow2_and`), a product
with `c` (`uintN(c)`) or `-c` (`uintN(-c)`, `ofInt_wrap_neg`) into a (negated) left shift
(`mul_pow2`, `mul_negpow2`; `generic.rules:1106–1120`, RuleProofs7).
The eight rules closed this way (`generic.rules:1097–1100`, `1127–1130`) used to generate
`callH.match_5`'s equations and splitter in every module (2.9 MB of `.olean`): `callH` is now
evaluated by the dsimproc `reduceCallH` (one `delta` + `whnfCore` at a helper constructor; it
waits until the arguments select an arm), never unfolded by `simp` (LEARNINGS.md).
Divisibility by a power of two (`divisible.rules:17–26`, `isPowerOfTwo(c)` of a signed `c`):
`isPow2_signed` gives `c = 2 ^ k`, `k + 1 < w`, and `divisible_pow2_u`/`_s` (`_ne`) close
`(x == x / c * c) = (x & (c-1) == 0)` (signed: `x.srem c = 0` iff `2 ^ k` divides `x.toNat`).

**Conditions** (#69, RuleProofs6). `rule_unfold` evaluates the condition after the intros
(`hcond`), in its own `dsimp`. `rule_cond_bool` replaces a comparison that cannot evaluate
because an operand is the oracle's (`x.Op != OpConst64`, `div.Uses == 1`,
`config.RegSize == 8`) by a fresh `Bool` (`binDV_cmp_bool`: a comparison evaluates to a boolean
or falls back to the `bool`-typed oracle answer), so that `&&`/`||` around it evaluate and the
modelled conjuncts (`isPowerOfTwo(c)`, `smagicOK(c)`) become hypotheses. Comparisons that read
instance fields (`c.Type.Size() == 8`) are left alone: they evaluate after the case splits.

**Pointer rules** (#69, RuleProofs7; `OffPtr.lean`, `PtrIndex.lean`, `AddPtr.lean`). `rule_unfold` introduces
the argument shapes as `hat` and, if the rule mentions an op `argShapeOk` constrains, reduces
them to type equations (`isPtrTy_iff`, `isInt64Ty_iff`; otherwise `hat` is cleared, so the P1
proofs are unchanged). The proofs are by hand: a pointer-shaped leaf is `poison` or a pointer
(`val_of_hasTy_ptr`), a 64-bit one `poison`, an integer or an address-less pointer
(`val_of_hasTy_int64`), offsets add (`ptr_add_add`), and the top value equals its retyping by
`hty` (`refines_retype_of_hasTy`). `rule_auto` does not close them (it falls back to
`bv_decide`).

Match congruence equations (`binDV.match_4.congr_eq_*`, …) are generated once in
`Tactic.lean`: generated by `simp` in two rule modules they are two public declarations of the
same name and the modules cannot be imported together (`scripts/rule-proofs.py axioms` imports
every module, so it catches this).

`bv_decide` stores an LRAT certificate per goal in the `.olean` (`<thm>._cert_def_N`, up to
9 MB for one 64-bit ring identity) and adds `Lean.ofReduceBool` axioms; no proven rule needs it
now (`probe` reports `BV` for a rule closed by it). Its order after `grind`/`rule_rot` and
the dropped `bv_decide` cases removed the need for `set_option Elab.async false` in the rule
modules (LEARNINGS.md, "`bv_decide` certificates in rule-lemma `.olean`s").

`scripts/rule-proofs.py probe <Family>` tries `rule_auto` on the pending rules of a family
(`tmp/rules/probe-<Family>.tsv`: rule, `OK`/`BV`/`FAIL`, ms, distinct subterms of the proof
— about 25 bytes of `.olean` each —, error); `emit <Family>` writes the module for the rules
that passed.

## Non-vacuity

`Rule.Sound` is one definition for all rules, so its non-vacuity is shown once and per family
rather than per lemma (agreed with Main), in `GoFV/Proof/Rules/NonVacuous.lean`:

- `Rule.Inst r e or`: every hypothesis of `Rule.Sound r` holds at the instance `e`, `or` and
  the matched value is not `poison`. There `Rule.Sound r` gives `Refines (Pat.raw e r.pat)
  (Rule.res r e or)` with a non-poison left side, i.e. the result equals the matched value
  (`Rule.Sound.refines`); an instance where it does not refutes `Rule.Sound r`
  (`Rule.not_sound`).
- `mut646_not_sound : ¬ Rule.Sound mut646`, `mut646` being `generic.rules:646` with the
  constant changed (`(Add16 (Const16 [1]) x) => x`).
- Per op family, instances of representative proven rules (`inst_r_generic_675`: no
  condition; `inst_r_generic_2185`: a rotate rule whose condition needs a bounded shift and an
  oracle atom, `canRotate`; `inst_r_generic_479` RotateLeft, `inst_r_generic_453` Lsh,
  `inst_r_generic_232` Rsh, `inst_r_generic_716` Less, `inst_r_generic_714` Leq,
  `inst_r_generic_103` ZeroExt, `inst_r_generic_108` SignExt, `inst_r_generic_752` Trunc,
  `inst_r_generic_400` Not, `inst_r_generic_284` EqB, `inst_r_generic_290` NeqB,
  `inst_r_generic_173` Div, `inst_r_generic_1142` Mod, `inst_r_generic_1097` Div by a power
  of two, `inst_r_divisible_17` divisibility by a power of two, `inst_r_generic_1112`/`_1120`
  Mul by ±2^k, `inst_r_generic_964` OffPtr and `inst_r_generic_970` PtrIndex at heap
  pointers, `inst_r_generic_126` AddPtr). `Rule.Inst` includes `Oracle.BoolTyped` and `Pat.argsOK`; `Oracle.const b` satisfies it
  (`Oracle.const_boolTyped`), as does `Oracle.litFalse` (unmodelled literals `false`, other
  atoms `true`, for `v.Block.Func.pass.name != "opt"`).
- `lake exe rule-sat` (`GoFVTest/Proof/RuleSat.lean`; `scripts/rule-proofs.py sat`) searches
  an instance of every exported rule at run time (random leaves, auxints from boundary values,
  `[c]`/`<t>`/`same x` solved, oracle atoms all `true` or all `false`, helper-call atoms and
  unmodelled literals independently) and checks `Bool`
  mirrors of the hypotheses. `sat` fails if a proven rule has no instance or a
  counterexample. It also reports counterexamples among the pending rules (`CEX`), which are
  how the findings below were found. Last run (with `Pat.typed`: leaves typed by their
  values' shapes): P1 rules SAT 1332, CEX 9 (all `generic.rules:504–516`, "Narrow result
  types"), NONE 54; all 1056 proven rules SAT (its oracles answer every atom with a
  boolean, so they are `BoolTyped`).

`Comm.lean` has `sub16_not_comm` (the commutativity obligation is not trivial).

## Findings

- **#90 (`upstream-candidate`)**: constant rotate detection, `generic.rules:2166–2169` and
  their Or/Xor expansions (12 rules). The condition `c < w && d == w-c` compares the shift
  constant signed; for `c = -1`, `d = w+1` both shifts give 0 but `RotateLeft x (Const64 [-1])`
  rotates by `w-1`. Missing precondition `c >= 0`. Marked `-- FALSE … #90` in
  `GoFV/Proof/Rules/Add.lean`; `Rule.Sound` is false for them.

- **`divmod.rules:136–148`** (`Div16u/32u/64u` of a signed type by `smagic`): false under the
  semantics, not a Go bug. `t.IsSigned()` is an oracle atom and nothing makes the dividend
  non-negative, which Go establishes before (prove pass). Counterexamples (agent DivmodU):
  136 at `c = 3`, `x = 0xFFFF` (21845 vs 32767); 140 at `c = 3`, `x = 2^32-1`; 144 at `c = 7`,
  `x = 4294967291`; 148 at `c = 7`, `x = 2^64-3`. Marked `-- FALSE … #69` in `Div.lean`.

- **`generic.rules:1071–1073` (`Convert` round trips)**: false under the semantics even with
  `Pat.argsOK`, not a Go bug (RuleProofs7). `Convert` goes through concrete addresses
  (`Ptr.addr?`, `Ptr.ofAddr`), which are not inverse for a pointer whose offset leaves its
  allocation's address range: `(Convert (Convert p mem) mem) => p` at `p = ⟨heap 0, 2^40⟩`
  gives `Ptr.ofAddr (2^41) = ⟨heap 1, 0⟩ ≠ p`; `:1071` likewise at `off = 0`. Needs a
  semantic invariant bounding pointer offsets (or block-preserving `Convert`), Semantics'
  decision; `:1684`/`:1683` (`NeqPtr`/`EqPtr` of `ConstNil`) are of the same kind.

## Narrow result types

`Rule.Sound` assumes the matched value's type is not narrower than its op. The checker does
not guarantee this, and `divmod.rules` builds such values (`(Rsh64x64 <typ.UInt32> …)` read
as their low bits by `Val.retype`). A rule whose result is a copy (`=> x`) or has its own
`<type>` changes the shape of such a value: under the semantics the rewrite is then not a
refinement (e.g. `(Rsh64x64 x (Const64 [0])) => x` on a value typed `uint32` turns a 32-bit
value into a 64-bit one). The interpreter proof needs either a typing invariant excluding
such matches or a semantics in which a narrow-typed value is read at its op's width.

The same applies to results that build a constant with the matched value's type:
`generic.rules:504–516` fold nested constant shifts into `(Lsh16x64 x (Const64 <t> [c+d]))`
with `t` the type of the 16-bit shift, so the new shift amount is a `Const64` typed `int16`.
Under `Val.retype` that amount is truncated to 16 bits and then read at 64 bits, i.e. `poison`
(`rule-sat` instance: `x = 31`, `c = 1`, `d = 65`). Go materializes the constant at 64 bits,
so this is a limit of the model, not a Go bug; these rules stay pending until the semantics
reads a narrow-typed value at its op's width.

## Build cost

Official toolchain, each module alone under memcap, machine load ~100; CPU = user+sys:

| Module | CPU s | Max RSS MB | `.olean` MB |
| --- | --: | --: | --: |
| `Den` | — | — | 9.0 |
| `Lemmas` / `Names` / `Tactic` | 7 / — / 43 | — | 1.6 / 0.8 / 3.1 |
| `Comm` | — | — | 0.4 |
| `NonVacuous` | 4 | 1300 | 0.6 |
| `Add` (30 lemmas) | 34 | 1709 | 2.9 |
| `Add2` (30) | 43 | 1634 | 3.2 |
| `Add3` (27) | 41 | 1577 | 3.3 |
| other family modules without rotate rules (8–30 lemmas) | — | ≤ 1760 | 0.3–2.6 |
| `Or`, `Or2`, `Xor`, `Xor2` (30, 18; with rotate rules) | — | ≤ 1760 | 2.6–3.5 |

All 35 modules of `GoFV/Proof/Rules` rebuilt after a `Tactic.lean` change: 137 s wall, 728 s CPU, peak 1.8 GB per process.

Before (PR #91 as first pushed): `Add`/`Add2`/`Add3` 16 / 69 / 57 MB, 54–85 s CPU, under
`Elab.async false`; 90% of it `bv_decide` LRAT certificates (LEARNINGS.md). What remains is
the proof terms themselves, ~25 bytes per distinct subterm: 1–3 k subterms for a plain rule,
7–11 k for a rotate rule (`probe` prints the count per rule). Smaller proofs need a different
proof shape (e.g. a verified symbolic evaluator of patterns, so a rule lemma is a `decide` on
rule data plus one `BitVec` identity); nothing outside `GoFV/Proof/Rules` imports these
modules.

**Axioms:** `propext`, `Classical.choice`, `Quot.sound` for every proven rule and the
non-vacuity theorems; `probe` marks a rule closed by `bv_decide` (which would add
`…._native.bv_decide.ax_*`, allowed by `docs/PLAN.md` §0) as `BV`; none is.
