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
  `AddPtr`, `PtrIndex`, `IsNonNil` pointer-typed, both of `EqPtr`/`NeqPtr` pointer words (a
  pointer or a 64-bit integer: `uintptr` itabs), the offset of
  `AddPtr`/`PtrIndex` a 64-bit integer, `Convert` between a pointer and a 64-bit integer (by
  its result shape; a `Convert` of any other shape is excluded), both arguments of
  `Eq<N>`/`Neq<N>` `N`-bit integers (#69 RuleProofs11; `generic.rules:369`/`:372` reuse a
  `Const64` node of the pattern in the result, which could otherwise be typed `int32`), both
  arguments of `IsInBounds`/`IsSliceInBounds` 64-bit integers (#69 RuleProofs14: `int` on the
  64-bit target; the semantics compares at the first argument's width, so a `Const64` typed
  `int32` would compare its low 32 bits while `:255`'s result compares the auxints), the first
  word of an `EqInter`/`NeqInter` operand a 64-bit integer (`ifaceArgOk`, the interface shape's
  itab word; `:790`/`:791` retype it to `uintptr`, which turns a pointer with an address into
  that address). With
  `Pat.typed` the leaves then have these shapes. Without it
  `generic.rules:964` (`(OffPtr (OffPtr p [y]) [x]) => (OffPtr p [x+y])`) is false: a
  `uintptr` leaf `p = 2^40-8` under a pointer-typed inner `OffPtr` becomes the pointer
  `Ptr.ofAddr p` plus `y` (its allocation kept), while the result adds `x+y` as an integer;
  likewise `:970` with an `int32` index (`Mul64` of a narrower integer is `poison`).
- **Non-negative arguments** (`Pat.nonNegOK e r.pat r.cond = true`, #69 RuleProofs11/12): every
  leaf the condition passes to `isNonNegative` holds `poison` or an integer with a clear sign
  bit (`Val.nonNeg`). The checked rewrite discharges it with `nonNegD` (`RewriteCheck`, a
  structural port of `rewrite.go`'s `isNonNegative` on the post-event definitions, proven by
  `nonNegD_den` in `GoFV/Proof/Pass/RewriteTermNonNeg.lean`); `StringLen`/`SliceLen`/`SliceCap`
  are not taken as non-negative there, since the semantics' composites carry arbitrary
  integers. Without it `generic.rules:610`, `:611`, `:1090`, `:1134–1138` are false (see
  "Findings"). On `quick-v3` all 164 firings of these rules test a `SliceLen`/`StringLen`
  leaf, so the validator discharges none of them (the 12 functions they would bring to stock
  are validator-only). Making `*Len` poison on a negative component breaks the passes that put
  `SliceLen`/`StringLen` into the target (phi split of decompose builtin, expand calls); the
  planned fix (Semantics4) poisons negative lengths at construction (`decode`, `Comp.make` at
  slice/string shapes), which needs `Ty` to tell slices and strings from structs. Then
  `nnTable` can take `SliceLen`/`StringLen`/`SliceCap` as non-negative.
- **Expressions** (conditions, `[auxint]`, `<type>`) are evaluated by `evalE`, a total pure
  evaluator mirroring `GoFV.Rules.Eval.eval` on integers, booleans, op constants, type shapes
  (`typ.<T>` incl. `typ.BytePtr` = `.ptr (some 1)`, `types.Types[k]`, `t.Size()` of an
  integer/boolean shape, `t.Elem().Size()` of a pointer shape with a known element size:
  `t.Elem()` is the record `{Size}`; `t.Elem().PtrTo()` of a slice shape, an aggregate of at
  least two fields whose first is the data pointer `.ptr el`: `t.Elem()` is the record
  `{PtrTo = .ptr el}`) and the pure
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
  phase-P1 op that a pattern marks `commute`, `EqPtr`/`NeqPtr` and the float
  `Add`/`Mul`/`Eq`/`Neq{32,64}F`, whose operands the semantics orders by encoding, is symmetric
  in its first two arguments).

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
  reject for the pointer ops. The `Eq<N>`/`Neq<N>` widths are checked by the validator only:
  0 rejections for this reason on `quick-v1` and `full-v2` (#69 RuleProofs11).
- **Typed oracle** (`Oracle.BoolTyped or := ∀ x, exprTy [] x = .bool → ∃ b, or.dv x = .bool b`):
  the oracle built from `GoFV.Rules.Eval.eval` answers a `bool`-typed expression with a
  boolean, i.e. `eval` of a well-typed `bool` expression that does not fail is a boolean.
  `GoFV.Opt.RewriteCheck.oracle` (`true` for every `bool` expression) and the oracles of
  `rule-sat` and `NonVacuous.lean` (`Oracle.const_boolTyped`) satisfy it.

## Rules beyond `Rule.Sound`: blocks, effects, frame values (#151)

`Rule.Sound` covers value rules whose pattern and result are `evalPure` terms. Three more kinds
of rules matter for the proven-only passes (see "Firing frequency"): block rules, rules whose
pattern contains an effectful value (memory ops, nil checks, calls), and rules on values the
semantics evaluates from the tables rather than by `evalPure` (`ConstString`, `Addr`). Each gets
its own obligation; the proven-only rule sets carry one list per obligation (`RuleSet.values`,
`RuleSet.blocks`, and effect rules once the first is proven), and `RuleSet.AllSound` asks the
matching obligation of every rule.

### Block rules: `BlockRule.Sound` (`GoFV/Proof/Rules/Block.lean`, proven for all three)

`Sem.stepTerm` reads an `If` block's control only as a boolean: `true` → `Succs[0]`, `false` →
`Succs[1]`, anything else stuck. So swapping the successors is negating the control, and
`First` is an `If` on the constant `true`. A block rule `(If ctrl yes no) && cond =>
(If x no yes)` / `(If x yes no)` / `(First …)` is therefore sound when the *control rule*
`BlockRule.ctrlRule br` — the value rule `ctrl && cond => (Not x)` (swapped), `=> x`, or
`=> (ConstBool [!swapped])` (`First`) — satisfies `Rule.Sound`:

```lean
def BlockRule.Sound (br : BlockRule) : Prop := ∃ cr, BlockRule.ctrlRule br = some cr ∧ Rule.Sound cr
```

`generic.rules:1064–1066` (`If (Not c)` swapped, `If (ConstBool [c])` → `First`) are proven in
`GoFV/Proof/Rules/BlockIf.lean` (`r_generic_1064_sound`, …; their control rules by `rule_auto`).
Other block-rule shapes (more controls, other kinds, aux fields) have no control rule and cannot
be proven under this obligation; there are none in the four rule files.

**Validator.** A block-rule event now logs the rule index and the new controls
(`RwEvent.blockRule b i ctrls`). `RewriteCheck.replay` keeps the replayed terminator of every
block the log touched (`BState`: kind, controls, successors swapped or not; `bstate`): a
`control b i c` event (copy elimination of a control) replaces control `i` when `c` is reached
through compatible copies; a block-rule event is accepted when the block has two successors and
is an `If` on one boolean-shaped control `c`, and the control rule fires at `c` as a value rule
(`ruleOK`) with the definitions the new controls determine (`ctrlDefs`: `c` redefined in place as
`Not nc`, `Copy nc` or the constant). `finalOK` checks every block of the output against its
replayed terminator (kind, successors in the replayed order, controls up to copies);
`atomsOK` no longer compares kinds, successors and controls.

**Theorem.** The atom simulation's premise on terminators is no longer "same kind and
successors, controls refining as terms" (`ControlsRef`) but `Term.TermStepRef`: every block of
the output keeps the input's successors (as a set) and its terminator, as a function of its
controls' terms (`stepVals`, `Sem.stepTerm` on control values), refines the input's
(`GoFV/Proof/TermStep.lean`; under a source invariant `StepRefsP`, `GoFV/Proof/AtomSimSet.lean`).
`validate_termRef` establishes it from the replay (`BInv`: the replayed terminators refine the
input's, kept by every event, `GoFV/Proof/Pass/RewriteTermBlock.lean`; `eff_not`, `eff_copy`,
`eff_const` turn the control rule's refinement into the terminators'). `checkedRewrite_refines`
and `opt_refines`/`divisible_refines`/`divmod_refines` keep their statements; their rule-set
hypothesis `RuleSet.AllSound` now also asks `BlockRule.Sound` of the block rules.

### Nil-check eliminations: `EffectRule.NilElim` (`GoFV/Proof/Rules/NilElim.lean`)

`(NilCheck x:(Op …) _) => x` replaces a root by its pointer. Each instance is validated by
nilcheckelim's checker rather than by a value refinement: `RuleSet.nilChecks` (tried on a
`NilCheck` after its value row, `Interp.Table.nilChecks`) holds the rules with
`EffectRule.NilElim r := RewriteCheck.nilElimOK r = true` (the result is the checked pointer, whose
op can be a `NilCheck.safePtr true` seed: `Addr`, `LocalAddr`, `NilCheck`, `GetG`, `OffPtr`,
`SelectN`, `Arg`). `RewriteCheck.accepts` takes the log's nil-check events out in its nil-check
layers (`nilPre`: `NilCheck p mem` → `Copy p` on the layer's input; see "Layers" below),
requires `NilCheck.nrel true` between the layer's input and that function, `check` of it, and
the layer input's dictionary parameters in the result's tables to be the pass input's in the
pass's tables (`nilOK`), and validates the output against the last layer's function with the
remaining events. `safePtr` follows `OffPtr`, `AddPtr`, `PtrIndex` and `Copy` to its seeds (each
keeps a non-nil pointer's allocation, `offPtr_safe`, `addPtr_safe`, `ptrIndex_safe`; a `Copy`
is its argument), so a nil check whose pointer the log forwarded from a `Store` (a `Copy` after
the forwarding layer) is justified by the stored pointer. Two more cases cover pointers that the
log's value rules turn into seeds after the nil-check layers ran: the `StringPtr` of a non-empty
string constant (`NilCheck.nonEmptyStr`; the data pointer `Sem.frameVal` gives the constant is the
start of a global, at every shape of the constant, `safe_str_select`; `:1022` + `:1011` make it an
`Addr`, whose nil check `:1375` drops) and a `StructSelect [i]` of a `StructMake` whose field `i`
has pointer shape (`NilCheck.ptrField`) and whose argument `i` is a `safePtr` pointer
(`safe_struct_select`; `:973` makes it that argument). Witnesses:
`GoFV.Proof.Witness.ns_checkedRewrite` and `sm_checkedRewrite` (`GoFV/Proof/Witness/NilSel.lean`,
kernel evaluation).

`safePtr true` (the rewrite passes' seeds) also takes as non-nil the first result of a
malloc-family call (`NilCheck.mallocCall`: a `StaticLECall` of `runtime.newobject` or a
`runtime.mallocgc*SC*` allocator, `NilCheck.mallocName`, whose type and ABI give the result a
pointer shape) and a dictionary parameter (`NilCheck.dictArg`: an `Arg` of the input parameter
named `.dict`, of pointer shape). Neither is non-nil by the semantics alone: the contracts are
the environment's, the arguments the caller's. So the checked rewrite passes are proven under the
precondition `RwPre tabs f env args mem := env.Mono ∧ NilPre tabs f env args mem`
(`GoFV/Proof/Pass/Rewrite.lean`), `NilPre` = `Env.AllocNonNil` (every malloc-family contract
that returns gives a non-nil pointer first; the runtime's do, `Env.runtime_allocNonNil`) and
`DictArgs (NilCheck.dictParams tabs f) args` (the dictionary arguments are non-nil pointers;
`GoFV/Proof/NilPre.lean`). `NilCheck.dictParams` depends only on the ABI assignments of
`f.OwnAux` and their names, which no pass changes. Proof (`GoFV/Proof/Pass/NilSeeds.lean`): under
`AllocNonNil` the call's register holds a tuple whose first component is a non-nil pointer or
`poison` (`callOp_static_ok`, `safe_selectN_malloc`); under `DictFrame` (the frame's images of
the dictionary parameters encode non-nil pointers; `dictFrame_entry` from `DictArgs`, kept by
every block step) the `Arg` reads a non-nil pointer or `poison` (`safe_argVal_dict`); both are
new cases of `safe_chain` (`NilBlock.lean`). `Nil.refinesFrom_of_rel : NRel true tabs f g →
RefinesFrom (NilPre tabs f) tabs g tabs f`; nilcheckelim itself keeps `nrel false` and
`refines_of_rel : NRel false tabs f g → Refines tabs g tabs f`.

**Theorems**: `checkedRewrite_refines` (and `opt_refines`, `divisible_refines`,
`divmod_refines`) now conclude `RefinesFrom (RwPre penv.tables f) out.tables out.func
penv.tables f`. The verified pipeline (`GoFV/Proof/Pass/Pipeline.lean`) names this relation
`Rel.rw`; `VPre k` adds `Env.AllocNonNil` and `DictArgs k`, with `k` the pipeline input's
dictionary parameters (`VState.dict`; a proven pass whose input has other dictionary parameters
is skipped), and `verifiedPipeline_refines` concludes `VRefines (NilCheck.dictParams env.tables
f)`. Witness: `GoFV.Proof.Witness.nm_checkedRewrite` (`newInt(.dict)`: both nil checks removed,
kernel evaluation) and `nm_rwPre` (the precondition with a dictionary). Proven:
`generic.rules:1062`, `:1367`, `:1372`, `:1375`, `:1381`, `:1384`, `:1388`. Not provable this way
(the pointer is no seed): `:1376` (`Convert` of `Addr`).

### Load-of-Store forwarding: `EffectRule.LoadFwd` (`GoFV/Proof/Rules/LoadFwd.lean`)

`(Load <t1> p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && … => x` (`:800`) and its forms
through one to three more `Store`s at addresses `disjoint` from the read (`:806`, `:813`, `:821`)
replace a `Load` (a term: `Sem.loadOp`, `poison` on an invalid access) by `Copy x`. The `Store`
is a root, an atom of `Term.den`, so `Rule.SoundT` cannot see what it wrote; the rule is
validated per instance, like the nil-check eliminations: `RuleSet.loads` (tried on a `Load`
after its value row, `Interp.Table.loads`) holds the rules with `EffectRule.LoadFwd r :=
RewriteCheck.fwdShapeOK r = true` (the result is the value one of the up to four `Store`s of the
`Load`'s memory chain stores). `RewriteCheck.accepts` takes the log's forwarding events out in
its forwarding layers (`fwdPre`: `Load p m` → `Copy x` on the layer's input; copy-argument
replacements of the forwarded `Load` logged before it are dropped; see "Layers" below), requires
`fwdRel` between the layer's input and that function and `check` of it. `fwdRel`: the same
blocks and atoms, every value unchanged but for the forwarded `Load`s (`fwdRepOK`), each with
`fwdOK` = `fwdChain` (through at most eight memory `Copy`s and `Store`s at pointers disjoint from
the read, a `Store`/`StoreWB` at a pointer equal to the `Load`'s of a value that stands for `x`,
`storedOK`: `x` reached from it through compatible `Copy`s, `copyReach`, since copy elimination
ran before the rule matched, the stored value of a `fwdTyEq` shape; the `Load` and `x` have
one shape, `fwdTyEq`: an integer, boolean or pointer shape (`scalarTy`, `fwdScalarEq`) or a
non-empty aggregate of such fields at increasing, non-overlapping offsets (`fwdAgg`, `fwdFields`,
`fwdAggEq`: strings, interfaces, flat structs); the `Store`'s type that shape or a pointer
stored as `int64`, `fwdStoreTy`), and ranks ordering every listed non-`Phi` value after its
arguments (`fwdRank`, `fwdRankOK`). Pointers: `ptrBase` (a base and a constant offset through
`OffPtr`s, pointer `Copy`s and `PtrIndex`es by a `Const64` index, `constIdx?`, the index times
the element size of the `PtrIndex`'s pointer shape), `baseSameB` (the same value, the start of one allocation:
`LocalAddr`s of one variable or `Addr`s of one symbol, `baseBlk?`, or `AddPtr`/`PtrIndex` of
equal bases by structurally equal indices, `termEqB`), `samePtrB` (equal bases, equal offsets),
`disjointB` (equal bases at offsets whose byte ranges do not overlap modulo 2^64, `offSep`, or
bases in different allocations).

**Constants** (`:830`, `:832`): `(Load <float64> p1 (Store {t2} p2 (Const64 [x]) _)) && … =>
(Const64F [math.Float64frombits(uint64(x))])` and its converse rebuild the `Load` as a constant
instead of a `Copy` (`fwdShapeOK`'s second case: a one-`Store` chain of a `const64Op`, a
one-node argument-less `const64Op` result). Floats are integers of their width in the semantics
(`tyOf`, `FOps.const64`), so `Const64 [c]` and `Const64F [c]` denote the same `.int .w64` value:
`fwdNewOK` accepts, besides `Copy x` with `fwdOK`, a new definition `w` with `fwdConstOK` (the
first `Store` at the Load's pointer, `fwdStored`, writes a `const64Op` value of `w`'s auxint at a
shape `fwdTyEq` to the Load's, and `fwdOK` reads it back). `fwdEvent?` returns the new definition,
which `fwdCopy` installs.

**Theorem.** `LoadFwd.fwd_refines : check ce f = .ok () → check ce' g = .ok () → fwdRel tabs f
g = true → RefinesUnder Env.Mono tabs g tabs f`, by the atom simulation. It needs a fact about
the source's memory roots that no valuation of the atoms has: `MemDefs` (on the source's `DenOK`
set of a block entry, each `Store`/`Move`/`Zero` register is `memDef`, the write of its arguments'
registers, which are in the set, and each `LocalAddr` register its frame variable in activation
0, where the atom simulation runs; established by `src_eval_mem` from `evalValue`, kept by
`memDefs_phis` along edges) gives `termRef_apply` the premise `MemAtoms` of `TermRefP`/`StepRefP`
(on the valuation it builds, every non-`poison` memory root is the write of its arguments'
terms, every `LocalAddr` its variable). With it, `fwd_den` (by induction on the rank) reads a
forwarded `Load` through its chain (`chain_load`, `GoFV/Proof/Pass/LoadFwdPtr.lean`:
`ptrBase_den` with `ptrIndex_den`, `baseBlk_den`, `samePtr_den`, `disjoint_sep` +
`load_write_sep` past the disjoint writes, `load_write` at the `Store` of the stored value:
`decodeLoad_encode`, at an aggregate field by field, `fields_encode`, and a stored `poison`
aggregate is all `poison` bytes, which a `Load` reads as `poison`, semantics.md §3.4
`decodeLoad`; then `copyReach_den` to `x`, whose rank `copyReach_rank` bounds). The fuel of
`TermRefP`'s right side may depend on the valuations. A constant result reads the stored
constant through its chain the same way (`chain_load`), which denotes the result's bits
(`opVal_const64`, `fwdConstOK_spec`). `checkedRewrite_refines` composes the
layers (`chain_refines`) and the atom simulation (statement unchanged). Proven:
`generic.rules:800`, `:806`, `:813`, `:821`, `:830`, `:832`; witnesses
`GoFV.Proof.Witness.sl_checkedRewrite` (`*p = x; return *p`), `sl2_checkedRewrite`
(`p[0] = x; p[1] = y; return p[0]`, `:806`), `sls_checkedRewrite` (`*p = s; return *p` at a
string; `sls_decodeLoad`), `fc_checkedRewrite` (the stored value a `Copy` of `x`),
`pi_checkedRewrite` (`PtrIndex p [0]` read through a `Store` at `PtrIndex p [1]`) and
`cf_checkedRewrite` (`*p = bits(1.5); return *(*float64)(p)` with `:830`: the `Load` becomes
`Const64F` of the stored bits; `GoFV/Proof/Witness/FwdCopy.lean`), kernel evaluation.

**Fallback.** `checkedRewrite t` tries the tables `checkedTiers t` in order: `t`, then without
the table's forwardings (`{t with loads := #[]}`), then also without its struct-store splits,
then also without its nil-check eliminations, each only if it removes rules (`checkedFirst`), so
a forwarding, split or nil-check elimination the validator cannot relate costs only that
function's events of that kind (`checkedRewrite_cases`: the validator reads only the table's
value and block rules, `validate_congr`, `checkedTiers_rules`). Forwardings the validator does
not relate: chains with a `Store` the validator cannot prove disjoint (`Addr`s or `LocalAddr`s
of one symbol at unknown offsets, an `Arg` pointer against a `LocalAddr`), a
`Store` of a `Load` of the same address left in the chain by an earlier rewrite, and (late opt) a
one-pointer struct stored at the pointer type.

### Struct-load expansions: `EffectRule.StructLoad` (`GoFV/Proof/Rules/StructLoad.lean`)

`(Load <t> _ _) && t.IsStruct() && t.Size() > 0 && CanSSA(t) && !t.IsSIMD() =>
rewriteStructLoad(v)` (`:974`) redefines the `Load` as `StructMake` of fresh `Load <tᵢ> (OffPtr
[oᵢ] ptr) mem`, one per field. The result is a helper's, not a pattern, so the rule is validated
per instance: `RuleSet.structLoads` (tried on a `Load` after `loads`, `Interp.Table.structLoads`)
holds the rules with `EffectRule.StructLoad r := RewriteCheck.structLoadShapeOK r = true`; their
events log `v`'s new definition and then, per field, the `OffPtr` and the `Load`
(`Interp.structLoadDefs`). `replay` checks a rule event whose index misses the op row by
`structLoadOK`: the `Load`'s shape is `agg fs n` with every field inside it, recursively
(`layoutOK`), and at an offset below `n`; the new definition is a `StructMake` of the same type
whose arguments are the fresh `Load`s, each of the field's shape on an `OffPtr [oᵢ]` (pointer
shape) of the `Load`'s pointer, from the `Load`'s memory (`slFieldsOK`). No rule-level fact
enters the proof.

**Theorem.** The expansion refines the `Load` as a term, for every valuation of the atoms
(memory included): `GoFV.Proof.Pass.StructLoad.structLoad_ref` (`StructLoadMem.lean`: a valid
read of the struct's `n` bytes covers each field's bytes, read at the pointer moved by the
offset, `read_sub`; that pointer stays inside the window because the read does, §3.4 of
`docs/plans/semantics.md`, merged in #203; decoding a well-laid-out shape reads only its own
bytes, `decode_congr`; an invalid read is `poison`, refined by anything). `SLFacts.step` lifts
it to the denotations of a closed set, with three times the fuel, and `ReplayInv.structLoad`
keeps the replay invariant (`GoFV/Proof/Pass/StructLoad.lean`), so `replay_inv`,
`checkedRewrite_refines` and the pass theorems keep their statements. Proven: `:974`; witness
`GoFV.Proof.Witness.lf_checkedRewrite` (`s := *p; return s.a` on `struct{ a, b int }`, kernel
evaluation).

### Layers (issue #151)

The nil-check eliminations, forwardings and struct-store splits (`generic.rules:975`,
`ssPre`/`ssRel`, `StructStore.ss_refines`) change roots, so `RewriteCheck.accepts` takes their
events out of the log and applies them to the input in layers (`RewriteCheck.layersOK` over
`RewriteCheck.layers` = nil-check eliminations of `safePtr` pointers, forwardings `fwdOK` holds
of, struct-load expansions, struct-store splits of the input's `Store`s, those of the first
layer's fresh field stores, the remaining forwardings, the remaining nil-check eliminations),
each related to its input by its own relation (`layerOK`: `nilOK`, `fwdRel` + `check`,
`validate` with the layer's events alone + `check`, `ssRel` + `check`; a layer without events
is skipped), and `validate` relates the last function and the output with the remaining events.
A selective layer (`nilPre`/`fwdPre` with `sel`) applies only the events its relation holds of in
its input, the later layer of its kind the rest: a split's pointer may be an eliminated nil check
(a `Copy` after the first nil-check layer) and its `StructMake`'s arguments forwarded `Load`s, a
forwarded field `Load` may read a split's field `Store` (only after the split layer), and an
eliminated nil check's pointer may be a forwarded `Load` (`generic.rules:1367` after `:800`:
only after the forwarding layers).

A `Store` of a `Load` that `:974` expanded (a struct copy `*p = *q`) stores the expansion's
`StructMake` of fresh field `Load`s when `:975` splits it, which the split relation needs in its
input: the struct-load layer (`slPre`) applies the log's expansions that `structLoadOK` validates
on its input (the `Load` becomes the `StructMake`, the fresh `OffPtr`s and `Load`s are put in,
`slApply`) and is related to its input by `validate` with these events (`slTaken`). The split
layer applies only splits of its input's `Store`s (`ssStep` looks the event up in the layer's
input), so a split of a fresh field store of another split (a nested struct) is left to the
second split layer, where that store is a `Store` of the input. A split's chain starts at the
split `Store`'s memory up to copies, or, when that memory is another split `Store` of the block
(with fields), at the last store of that split's chain (`ssStart`: copy elimination gives the
second of two consecutive splits the first chain's last store); `StructStoreBlock.prevInv` then
takes the chain's start from the other split's last field store (`startSplit`,
`prevInv_succ`, `bufK_full`). Witness: `GoFV.Proof.Witness.ss2_checkedRewrite` (`*p = P{x, y};
*p = P{y, x}`; `ss2_start`: the old condition fails, `ssStart` holds).

**Theorems.** `layersOK_cases`: an accepted run gives a `LayerChain` (`nil`/`fwd`/`rw`/`ss` steps
`layerOK` accepts; `LayerChain.congr` moves the `rw` steps to a table with the same value and
block rules, `validate_congr`) from the input to a function the output is validated against;
`chain_refines (hs : s.AllSound)`: a chain from a checked function ends in a checked function
that refines it under `RwPre` of the pass input (`Nil.refinesFrom_of_rel`, `LoadFwd.fwd_refines`,
`validate_termRef` + `AtomSim.atomSim_refines`, `StructStore.ss_refines` per step);
`checkedRewrite_refines` composes it with the atom simulation (statement unchanged). Witnesses:
`GoFV.Proof.Witness.nf_checkedRewrite` (`*pp = new(int); q := *pp; _ = *q`: the nil check of the
forwarded `newobject` result removed) and `sc_checkedRewrite` (`*p = *q` on `struct{ a, b int }`:
the `Store` of the expanded `Load` split into field `Store`s of field `Load`s), kernel
evaluation.

### Frame-value rules (`ConstString`, `GoFV/Proof/Rules/DenT.lean`, `ConstString.lean`)

`ConstString {str}` and `Addr {sym} SB` are term nodes evaluated from the tables
(`Rules.opVal`: `strVal`/`addrVal`, as `Sem.frameVal`). The obligation `Rule.SoundT` is
`Rule.Sound` with this denotation for all tables, under `FrameOK`: an aux `fe.StringData(x)` names
the data symbol of the non-empty string aux bound to `x`, an auxint `int64(len(x))` is its
length, an aux `{x}` of a built node is the aux bound to `x`, an auxint shift `a << b` or
`a >> b` of a built node shifts by a nonnegative amount (Go panics on a negative one, so the
rewriter built no node; `evalE` leaves the panicking case to the oracle) (`frameNodeOK`, on
every built node), a condition conjunct `x == ""` holds of the string aux bound to `x`
(`condFrameOK`; the aux is no rule value, so `evalE` leaves the comparison to the oracle), a
condition conjunct `isSamePtr(x, y)` of leaves `x`, `y` holds as equality of their values
(`condFrameOK` checks that both leaves matched the same value; `samePtrVars`), and a condition
conjunct `x.NumElem() == 1` makes the type `x` the shape `.agg [(0, f)] f.size` of a
one-element array (`Sem.tyOf` of `[1]T`; `condFrameOK` checks the evaluated type;
`numElem1Vars`), whose `t.Elem()` `evalE` evaluates to `f`.
`Rule.soundT_of_sound` lifts the `Rule.Sound` lemmas of rules without such nodes.
`fe.StringData` appends a symbol to the tables: `checkedRewrite` keeps the result's tables when
the input cannot tell them from its own (`tabsAgree`). Proven: `generic.rules:1022`
(`r_generic_1022_sound`), `:1015` (the empty string: `StringMake (ConstNil) (Const64 [0])`),
`:1011` (`(StringPtr (StringMake (Addr <t> {s} base) _)) => (Addr <t> {s} base)`, rebuilt with
the matched aux), `:1592` (`(MemEq p q _ _) && isSamePtr(p, q) => (ConstBool [true])`: `memEq`
of one pointer twice is `poison` or `true`, `MemEqSame.lean`), `:574` (both rules,
`((x >> c) & d) << e => (x >> (c-e)) & (d<<e)` with `c >= e`: the built `d<<e` gives `e ≥ 0`,
without which the rule is false in the model; then a bit identity, `ShiftMask.lean`), `:994`
(`Load` of a one-element array `=> ArrayMake1 (Load <t.Elem()> ptr mem)`: both loads read the
same `f.size` bytes, `load_one`, `ArrayLoad.lean`); witnesses
`GoFV.Proof.Witness.hi_checkedRewrite` (`func hi() string { return "hi" }`, kernel evaluation)
and, since `rule-sat` draws no tables, `Rule.InstT` instances `inst_r_generic_1015` (aux `""`),
`inst_r_generic_1011` (an `Addr` of a symbol under a string of length 2),
`inst_r_generic_1592` (`MemEq p p 0 mem`), `inst_r_generic_574`, `inst_r_generic_574_2`
(`((0x1234 >> 4) & 0xff) << 2`) and `inst_r_generic_994` (a `Load <[1]int64>` of eight zero
bytes).

### Dec rules: decompose builtin (`GoFV/Proof/Rules/Dec.lean`, issue #17)

The 47 `dec.rules` rules run in the rewrite step of decompose builtin
(`Rules.rewritePass decTable false`, `GoFV/Opt/Decompose.lean`). `GoFV.Rules.Proven.dec` (the
dec rule set restricted to merged lemmas) and `dec_allSound` are generated by
`scripts/rule-proofs.py proven`. For a log of the step `GoFV.Proof.Pass.Rewrite.validate_refines`
gives the refinement from `RewriteCheck.validate` and `tabsAgree` directly (the dec table has no
nil-check eliminations or Load forwardings, so `accepts` is `tabsAgree` and `validate`; witness
`GoFV.Proof.Witness.addZero_validate_refines`).

**Validator and obligation changes.** Selections (`StringPtr`, `SliceLen`, `ITab`,
`StructSelect [i]`, …) are accepted as tops when the selected component of their argument's shape
is the top's shape, or the argument is a scalar (the selection is then `poison`): `selTop`, proved
by `raw_selTop`. A `Load` at a scalar shape or an aggregate of scalars is a top (`loadTop`,
`loadOp_hasTy`), and leaves may have any shape (`leavesOK`: defined). `argShapeOk` asks of the
arguments of a `Make` (`StringMake`, `SliceMake`, `IMake`, `ComplexMake`, `StructMake`,
`ArrayMake1`) the shapes of their type's components (`makeArgOk`, `shapeSub`): without it
`(StringPtr (StringMake ptr _)) => ptr` is false (a pointer leaf typed `int64` under a field of
shape `int8`). `evalE` models `IsPtrShaped`, `IsString`, `IsSlice`, `IsInterface` by shape
(`kindE`: false at every other shape, the oracle's at the kind's shape, which a struct can
share), `config.PtrSize` (8, `configField`) and the pointer `typ.*Ptr` types.

**Proven** (26): the selections of a `Make` `:13`, `:14`, `:42`, `:43`, `:58`–`:61`, `:82`, `:83`,
`:126` (`select_retype_make`), and `:115`, `:116` (a selection of a pointer is `poison`; the
matched value is then always `poison`, so `rule-sat` finds no instance: the rewrite never changes a
defined value); `:106` (and `generic.rules:973`), the variadic `(StructSelect [i]
x:(StructMake ___)) => x.Args[i]`, as `Rule.MakeSel` (below); the Load splits `:45`, `:63`,
`:87` (`DecLoad.lean`: the condition fixes the string, slice or interface shape, `.other` gives
`poison`; there the split is a struct-load expansion whose first component is read at the
pointer itself, `loadSplit_ref` from `StructLoad.structLoad_ref`, the read bounded by the
block's address window; `rule-sat` has no memory instances, so the non-vacuity witness is the
pass execution `GoFV.Proof.Witness.ls_checkedRewrite`: `strLen`, `{dec.rules:45}`); the
extractors of a `Load` `:135`, `:136`, `:144`, `:146`, `:150`, `:151`, `:154` (`DecLoad.lean`:
component `k` of a `Load` of the kind's shape is refined by the `Load` of field `k` at its offset,
`selLoad_ref`/`selLoad0_ref`, `SelLoad.lean`; witness `GoFV.Proof.Witness.xs_checkedRewrite`,
`{dec.rules:136}`) and `:132`, `:141` as `Rule.LoadSel` (below).
**False under the semantics**: `:119`, `:120` (a one-field pointer-shaped aggregate is `.agg [p]`,
Go's is the pointer; `docs/plans/semantics.md` §10). **Not provable as `Rule.Sound`**: `:103`,
`:104`, `:125`, `:127` (correct only at the interface shape, which the obligation does not fix),
`:102` (`imakeOfStructMake`). **Pending**: `:16`/`:28` and the complex extractors `:158`–`:164`
(`t.IsComplex()` and `t.Size()` of an aggregate shape are not modelled); the `Store` splits
(`:10`–`:93`, `:123`, `:129`: an effect obligation, as `rewriteStructStore`, issue #151).

**`@b` results** (`… => @x.Block (…)`). The block a result is built in is not read by the term
denotations, so `resultOK` accepts a `build` whose node 0 is a fresh `t` (not `v`) with `v`
redefined as `Copy t` at its own type, compatible with `t`'s (`RewriteCheck.blockTopOK`);
`BuildRes` carries the top (`v`, or the fresh `t` with `BlockTop`), and `RuleFacts.top` reads `v`
through the copy (`den_copy`; `stepK` grows by one for it). `Rule.Sound` is unchanged.

**Unconditional selections of a `Load`: `Rule.LoadSel`** (`AllSound.lean`, `DecLoadSel.lean`,
`GoFV/Proof/Pass/RewriteLoadSel.lean`). `(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block
(Load <v.Type> (OffPtr <v.Type.PtrTo()> [t.FieldOff(int(i))] ptr) mem)` (`:141`) and the
`ArraySelect` form `:132` have no condition: nothing ties `v`'s type to the field's (a `Load` of
the same bytes at another shape need not refine the field, e.g. a global pointer read as
`int64`), so they are false as `Rule.Sound`. `Rule.Checked` gains `Rule.LoadSel` (`loadSelShape`:
a selection op over a `Load`, `@b` build result, no condition); the replay validates such an
event per instance, and only so (`RewriteCheck.loadSelOK`: the `Load`'s shape is `agg fs n` with
`layoutsOK` and every offset below `n`, field `k` is `(o, t)`, `v` becomes `Copy top` at its type,
`top` a fresh `Load` of shape `t` (`copyCompat` with `v`'s) on a fresh pointer-shaped `OffPtr [o]`
of the `Load`'s pointer, from its memory). `LSFacts.step` proves it refines the denotations of a
closed set with three times the fuel (`selLoad_ref` at `v`); `ReplayInv.loadSel` keeps the replay
invariant. Pass execution witness: `GoFV.Proof.Witness.lsel_checkedRewrite` (`loadField`,
`{dec.rules:141}`).

**Selections of a `Make`: `makeSelOK`, `Rule.MakeSel`** (`GoFV/Proof/Rules/AllSound.lean`,
`DecMakeSel.lean`, `GoFV/Proof/Pass/RewriteMakeSel.lean`). An event of a rule with
`makeSelShape` (a selection op over a `Make` op pattern, copy result, no `@b`) is first validated
per instance (`RewriteCheck.makeSelOK`): `v` selects component `k` (`selIndex?`) of `s = Make …`
whose argument `k` is a value `a`, `v` becomes `Copy a` at `a`'s type, and where the `Make`'s
shape has a component `k`, `a`'s shape is that component's and `v`'s (`shapeSub`), or `a` is an
`Addr` and both are word shapes (`.int .w64` or a pointer: a global has no concrete address,
so `retype` at both keeps it). Else the event is checked as a rule instance (`ruleOK`).
`MSFacts.step` proves the per-instance case refines the selection as a term at the same fuel:
component `k` of the retyped `Make` is argument `k` retyped at the field's shape
(`select_retype_make_get`), so only the selected argument matters (`addr_den`, `retype_word`
for an `Addr`). This accepts `(IData (IMake itab data))` whose itab is typed `*uint8` (the
interface's itab word is `.int .w64`; `Pat.argsOK` asks it of every `Make` argument) and
`(ITab (IMake itab _))` with an `Addr {go:itab.…}` itab (agreed with Semantics5: no semantic
change; an itab with a concrete address is not kept by `retype` at `.int .w64`). A `___` pattern
has no `Rule.Sound` form (`Pat.arityOk`): `RuleSet.AllSound` asks of each value rule
`Rule.Checked` = `Rule.SoundT` or `Rule.MakeSel` (`makeSelShape` and no `Pat.arityOk`), whose
events only `makeSelOK` accepts. Pass execution witness: `GoFV.Proof.Witness.mks_checkedRewrite`
(`pick`, `{generic.rules:973}`). `generic.rules:973` is in `Proven.generic` too.

`lake exe dec-rewrite-probe <corpus>` (`GoFVTest/DecRewriteProbe.lean`) runs the step alone (input:
the function after `decomposeUser` and the builtin phi splits) with all dec rules, the ptr-class
rules, the proven rules and none, and counts sections where rules fire, the step's result is
accepted (`RewriteCheck.accepts`), the full step's output is reproduced by the table and accepted,
and the whole pass (with the checked step) is at stock; per rule the first failing `ruleOK`
condition.

| Corpus (sections) | Table | Rules fired | Step accepted | Full step reproduced and accepted | Checked pass at stock |
| --- | --- | --: | --: | --: | --: |
| quick-v3 (9,297) | all 47 | 5,147 | 8,385 | 8,385 | 8,385 |
| quick-v3 | ptr class (21) | 4,824 | 8,732 | 7,415 | 7,415 |
| quick-v3 | proven (26) | 5,115 | 8,825 | 8,381 | 8,381 |
| quick-v3 | none | 0 | 9,297 | 4,150 | 4,150 |
| full-v2 (96,531), 13 proven, before `Rule.MakeSel` | all 47 | 67,840 | 58,923 | — | 58,923 |
| full-v2 | ptr class | 62,023 | 63,176 | — | 48,877 |
| full-v2 | proven (13) | 56,221 | 72,146 | — | 48,877 |
| full-v2 | none | 0 | 96,531 | — | 28,691 |

Before the validator changes every firing section was rejected (quick: 4,150 accepted = the
no-op sections; full 28,691). The full step extends the tables in 406 quick sections (types
such as `t.Elem().PtrTo()`), so the step's refinement is in the output's tables under `tabsAgree`.
Main obstacles (quick, proven row, sections not reproduced, `CLASS` lines of the probe): `Store`
splits ~280 sections (`:93` alone 100, `:72` 67, `:51` 34, both 38, `:123` 38); `ITab` of an
`IMake` whose itab is not an `Addr` ~390 (`ArgIntReg`, `Convert`, `Load`, `Phi`, `SelectN`,
`ConstNil`, `NilCheck`); `:120` (false in the model) 119; a phi elimination in the step's log 90
(the validator rejects `phielim`); complex `Load` splits ~25. History (proven row, full step
reproduced and accepted): 13 rules 6,131; `Rule.MakeSel` 6,852; `makeSelOK` for every selection of
a `Make` and the Load splits 8,264; the extractors (`@b` results) 8,293; `Rule.LoadSel` 8,381.

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
| `dec` | ArrayMake | 0 | 0 | 1 | 0 | 1 |
| `dec` | ArraySelect | 3 | 1 | 0 | 0 | 4 |
| `dec` | ComplexImag | 1 | 2 | 0 | 0 | 3 |
| `dec` | ComplexReal | 1 | 2 | 0 | 0 | 3 |
| `dec` | IData | 2 | 0 | 0 | 0 | 2 |
| `dec` | IMake | 0 | 1 | 0 | 1 | 2 |
| `dec` | ITab | 2 | 0 | 0 | 0 | 2 |
| `dec` | Load | 3 | 2 | 0 | 0 | 5 |
| `dec` | SliceCap | 2 | 0 | 0 | 0 | 2 |
| `dec` | SliceLen | 2 | 0 | 0 | 0 | 2 |
| `dec` | SlicePtr | 2 | 0 | 0 | 0 | 2 |
| `dec` | SlicePtrUnchecked | 1 | 0 | 0 | 0 | 1 |
| `dec` | Store | 0 | 0 | 0 | 8 | 8 |
| `dec` | StringLen | 2 | 0 | 0 | 0 | 2 |
| `dec` | StringPtr | 2 | 0 | 0 | 0 | 2 |
| `dec` | StructMake | 0 | 0 | 1 | 0 | 1 |
| `dec` | StructSelect | 3 | 2 | 0 | 1 | 5 |
| `divisible` | Eq | 12 | 4 | 0 | 0 | 16 |
| `divisible` | Neq | 12 | 4 | 0 | 0 | 16 |
| `divmod` | Div | 16 | 7 | 4 | 2 | 29 |
| `generic` | Add | 88 | 1 | 4 | 2 | 95 |
| `generic` | AddPtr | 1 | 1 | 0 | 0 | 2 |
| `generic` | And | 40 | 8 | 0 | 0 | 48 |
| `generic` | AndB | 36 | 0 | 0 | 0 | 36 |
| `generic` | ArraySelect | 1 | 1 | 0 | 0 | 2 |
| `generic` | BitLen | 0 | 8 | 0 | 0 | 8 |
| `generic` | Block | 3 | 0 | 0 | 3 | 3 |
| `generic` | Ceil | 0 | 0 | 0 | 1 | 1 |
| `generic` | Com | 12 | 0 | 0 | 0 | 12 |
| `generic` | CondSelect | 0 | 53 | 6 | 0 | 59 |
| `generic` | ConstInterface | 1 | 0 | 0 | 0 | 1 |
| `generic` | ConstSlice | 1 | 0 | 1 | 0 | 2 |
| `generic` | ConstString | 2 | 0 | 0 | 4 | 4 |
| `generic` | Convert | 1 | 4 | 0 | 0 | 5 |
| `generic` | Ctz | 0 | 8 | 0 | 0 | 8 |
| `generic` | Cvt | 0 | 0 | 0 | 11 | 11 |
| `generic` | CvtBoolToUint | 0 | 2 | 0 | 0 | 2 |
| `generic` | Div | 21 | 1 | 0 | 4 | 26 |
| `generic` | Eq | 54 | 4 | 0 | 2 | 58 |
| `generic` | EqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | EqInter | 1 | 0 | 0 | 0 | 1 |
| `generic` | EqPtr | 2 | 7 | 0 | 11 | 20 |
| `generic` | EqSlice | 1 | 0 | 0 | 0 | 1 |
| `generic` | Floor | 0 | 0 | 0 | 1 | 1 |
| `generic` | IMake | 0 | 1 | 0 | 1 | 2 |
| `generic` | InterLECall | 0 | 0 | 0 | 1 | 1 |
| `generic` | IsInBounds | 8 | 21 | 0 | 0 | 29 |
| `generic` | IsNonNil | 0 | 3 | 0 | 3 | 6 |
| `generic` | IsSliceInBounds | 4 | 4 | 0 | 0 | 8 |
| `generic` | Leq | 62 | 0 | 0 | 2 | 62 |
| `generic` | Less | 62 | 0 | 0 | 2 | 62 |
| `generic` | Load | 5 | 2 | 0 | 33 | 35 |
| `generic` | Lsh | 67 | 21 | 0 | 0 | 88 |
| `generic` | MemEq | 1 | 10 | 0 | 0 | 11 |
| `generic` | Mod | 29 | 0 | 0 | 0 | 29 |
| `generic` | Move | 0 | 0 | 0 | 25 | 25 |
| `generic` | Mul | 45 | 8 | 0 | 8 | 60 |
| `generic` | Neg | 24 | 0 | 0 | 2 | 26 |
| `generic` | Neq | 50 | 4 | 0 | 2 | 54 |
| `generic` | NeqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | NeqInter | 1 | 0 | 0 | 0 | 1 |
| `generic` | NeqPtr | 1 | 8 | 0 | 11 | 20 |
| `generic` | NeqSlice | 1 | 0 | 0 | 0 | 1 |
| `generic` | NilCheck | 7 | 0 | 0 | 8 | 8 |
| `generic` | Not | 27 | 2 | 0 | 4 | 33 |
| `generic` | OffPtr | 2 | 0 | 0 | 0 | 2 |
| `generic` | Or | 72 | 4 | 4 | 0 | 80 |
| `generic` | OrB | 48 | 0 | 0 | 20 | 56 |
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
| `generic` | SliceCap | 1 | 3 | 0 | 1 | 5 |
| `generic` | SliceLen | 1 | 2 | 0 | 3 | 6 |
| `generic` | SliceMake | 0 | 1 | 1 | 0 | 2 |
| `generic` | SlicePtr | 0 | 1 | 0 | 0 | 1 |
| `generic` | Slicemask | 0 | 4 | 0 | 0 | 4 |
| `generic` | Sqrt | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticCall | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticLECall | 0 | 0 | 0 | 24 | 24 |
| `generic` | Store | 1 | 0 | 0 | 21 | 21 |
| `generic` | StringLen | 1 | 0 | 0 | 0 | 1 |
| `generic` | StringPtr | 1 | 0 | 0 | 1 | 1 |
| `generic` | StructSelect | 1 | 3 | 0 | 1 | 4 |
| `generic` | Sub | 68 | 0 | 0 | 2 | 70 |
| `generic` | Trunc | 32 | 0 | 0 | 1 | 33 |
| `generic` | Xor | 56 | 8 | 4 | 0 | 68 |
| `generic` | Zero | 0 | 0 | 0 | 6 | 6 |
| `generic` | ZeroExt | 12 | 0 | 0 | 0 | 12 |
| all | | 1251 | 269 | 26 | 258 | 1762 |

<!-- END coverage -->

Regenerate both tables with `scripts/rule-proofs.py table` (it reruns the classifier if
`tmp/rules/class.tsv` is missing).

## Proven-only rewrite passes (issue #113)

`scripts/rule-proofs.py proven` writes `GoFV/Rules/Proven.lean` (the `generic`, `divisible`
and `divmod` rule sets restricted to the rules with a merged `Rule.Sound` lemma, and the block
rules with a merged `BlockRule.Sound` lemma, in matching order) and `GoFV/Proof/Rules/Proven.lean`
(`generic_allSound`, … : `RuleSet.AllSound`, every value rule of the set satisfies `Rule.Sound`
and every block rule `BlockRule.Sound`; `GoFV/Proof/Rules/AllSound.lean`).
Rerun it whenever lemmas are added. `GoFV.Opt.optProven`/`divisibleProven`/`divmodProven` run
`applyRewrite` with these sets (clifv's `--opt-proven-only`); the rewrite passes' theorems take
`RuleSet.AllSound` of their rule set as hypothesis.

**Checked passes.** `GoFV.Opt.optChecked`/`divisibleChecked`/`divmodChecked` run the proven-only
pass with its log on (`RwState.log`: every fired value rule with the definitions it built, copy
and control replacements, phi eliminations, block rules) and keep the result, with the
tables the pass extended, only if `GoFV.Opt.RewriteCheck.accepts` it (else the input with the
input's tables): `GoFV.Opt.tabsAgree` (the input cannot tell the result's tables from its own:
#169, `GoFV.Proof.refinesUnder_of_tabsAgree`) and `GoFV.Opt.RewriteCheck.validate` in the
result's tables: replaying the log on the input's
definitions, each rule firing must be an instance of its rule as `Rule.Sound` states it (pattern
match on the definitions through term ops only, swapped only at `commOps`, `Pat.cons` with
`same` only of leaf variables, `Pat.wf`, condition by `evalE` with an oracle read off the built
nodes that answers every boolean-typed expression with a boolean (`Oracle.BoolTyped`), top op
producing its type's shape (`topOK`: `natShape`, integer, float and boolean ops: a float is the
integer of its width; `ptrTop`: `OffPtr`/`AddPtr`/`PtrIndex`/`Convert`
at a pointer or `Convert` at the 64-bit integer shape, `evalPure_ptrTop`; `constTop`: `ConstNil`/
`ConstSlice`/`ConstInterface` whose constant has the type's shape, `evalPure_constTop`; all in
`raw_topOK`), argument shapes
(`Pat.argsOK` on the matched types), integer-, boolean- or pointer-shaped leaves, built nodes = `resDen`, no cyclic
match), a copy-argument replacement is replayed when its source is reached from the old argument
through copies of compatible shape, a block rule as its control rule at the block's control (see
"Rules beyond `Rule.Sound`"), no phi elimination, the arguments of listed
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
(`Pat.argsOK`, pointer leaves and tops in the validator, OffPtr/PtrIndex/AddPtr), 4,762
(51.22%) with 1,060 value and 3 block rules (#151), 5,247 (56.44%) with 1,067 (#69
RuleProofs8: constant composites `:1057`/`:1044` via `constTop`; nil comparisons
`:1683`/`:1684` after the pointer model of #156, with `EqPtr`/`NeqPtr` in `commOps` and
`boolOp` and their arguments pointer words, i.e. pointers or 64-bit integers), 5,289 (56.89%)
with 1,131 (#69 RuleProofs9: range checks `generic.rules:321–366`, `AndB`/`OrB`), 5,301 (57.02%)
with the extended tables (`tabsAgree`; the 59 `:1044` rejections gone) and the interface
constant at the interface shape of #169 (`ConstInterface` = `(int64 0, nil)`; #169 had made the
constant ill-shaped, 470 `:1057` rejections and 5,245 at stock).
Probe after RuleProofs9 (1,131 rules, extended tables): opt 58.46%, middle opt 94.76%, late opt
95.26%, divisible 99.98%, divmod 99.02% checked parity.
Probe after Load-of-Store forwarding (#151; 1,145 rules: `:800`, `:806`, `:813`, `:821` as
forwardings, with the no-forwarding fallback): 6,180 of 9,297 functions (66.47%) at stock under
the checked passes; opt 67.44%, middle opt 97.76%, late opt 96.74%, divisible 99.98%, divmod
99.96% checked parity; validator rejects 1 / 6 / 0 / 0 / 0 (the phi elimination and the six
narrow tops below), forwarding fallbacks 46 / 3 / 9 / 0 / 0.
After #69 RuleProofs11 (1,154 rules: single-bit tests `:369`/`:372` under the `Eq<N>`/`Neq<N>`
argument widths of `argShapeOk`, `Convert` round trip `:1072` under `convArgOk`, memory-shaped
leaves accepted by `leavesOK`, since `:1072` binds the `mem` argument): 6,241 of 9,297 (67.13%) at
stock under the checked passes (`fire`).
After struct-load expansions (#151; 1,155 rules: `:974` as `RuleSet.structLoads`), on quick-v3
(the corpus of #202): 6,381 of 9,297 (68.64%) at stock under the checked passes, 6,241 (67.13%)
without `:974`; opt 69.43%, middle opt 97.76%, late opt 97.09%, divisible 99.98%, divmod 99.96%
checked parity; validator rejects 4 / 6 / 0 / 0 / 0 (unchanged by `:974`: the phi elimination,
three nil-check eliminations `nrel` rejects in `runtime.*Hash`, the six narrow tops), forwarding
fallbacks 50 / 3 / 9 / 0 / 0 (47 / 3 / 9 without `:974`).
After aggregate Load-of-Store forwarding (#151: `Mem.load` decodes with `decodeLoad`, so a stored
`poison` aggregate loads as `poison`; `fwdTy` accepts `fwdAgg` shapes), on quick-v3 at 683d0c6
(with `:975` struct-store splits): 7,004 of 9,297 (75.34%) at stock under the checked passes,
6,993 (75.22%) before; opt 76.38% (76.26%) checked parity, the others unchanged; forwarding and
split fallbacks 78 / 3 / 9 / 0 / 0 (116 / 3 / 9 before: the 38 aggregate store shapes of opt are
gone; the rest are struct-store splits, "stored Load"/"walk"/"chain start", and the forwarding
chains below); validator rejects 158 / 6 / 1 / 0 / 0 on both. At ccc1a85 (before `:975`): 6,381
→ 6,388, forwarding fallbacks 50 / 3 / 9 → 12 / 3 / 9.
After #69 RuleProofs14 (float ops in `natShape`, the float `Add`/`Mul`/`Eq`/`Neq` in `commOps`:
the 11 float firings `:622`/`:623`/`:625`/`:1328` the validator rejected at the top or, matched
swapped, as `nomatch`): 7,010 (75.40%) at e22af29 (7,004 before).
With the bounds checks, `:585`, `:790–793`, `:992`, `:1012`, `:1031`, `:1032` (1,234 rules, at
b5a909f): 7,317 (78.70%) at stock under the checked passes, 7,559 under the proven-only ones;
7,624 (82.01%) / 7,876 at 8693405 (with the nil-check eliminations of #233).
With aggregate leaves in the validator (#69 RuleProofs15: `leavesOK` asks only that a leaf be
defined, since `Val.retype` gives a value of the shape at every shape, so the interface/slice
operands of `:790–793` are accepted): 7,759 (83.46%) / 7,876 at 97ccd7b.
With the frame facts of aux-bound variables (`:1011`, `:1015`; 1,239 rules): 7,950 (85.51%) /
8,066 at a853397 (7,772 before, with #237's validator layers).
With the `StringPtr`/`StructSelect` cases of `safePtr` (nil checks of a string constant's data
pointer and of a `StructMake`'s pointer field): 7,983 (85.87%) at 216e265 (7,979 before).
With forwarding through copies of the stored value (`storedOK`) and constant `PtrIndex` offsets
in `ptrBase`: 7,999 (86.04%) at 39885ba (7,995 before).

"No-op": the proven-only output equals the input (late opt's inputs carry dead values that
every variant removes). The proven-only passes keep copy elimination, phi elimination and
dead-value removal. Validator rejections (all REJECT lines of the probe): 6 top ops whose value
is narrower than the op (`natShape`, `generic.rules:1189/1192` on divmod-built values in middle
opt; "Narrow result types", correct rejections) and 1 phi elimination (opt). The 59 firings of
`:1044` (opt) whose `ConstNil <v.Type.Elem().PtrTo()>` has a pointer type the interpreter
created were rejected while `checkedRewrite` kept the input's tables (the type is `.other`
there); they are accepted since the validator runs in the result's tables. Before the
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

**Theorems** (`GoFV/Proof/Pass/Rewrite.lean`; the accepted case runs the input in the result's
tables, `refinesFrom_of_tabsAgree`): `checkedRewrite_refines (hs : s.AllSound)
(h : checkedRewrite (Interp.Table.ofRuleSet s) penv f = .ok out) (hf : check ce f = .ok ())
(hg : check ce' out.func = .ok ()) : RefinesFrom (RwPre penv.tables f) out.tables out.func
penv.tables f` (`RwPre`: `Env.Mono` and, for the nil-check eliminations, `NilPre`; "Nil-check
eliminations" above),
and its instances `opt_refines` (`optChecked`: `opt`, `middle opt`, `late opt`),
`divisible_refines`, `divmod_refines`, whose proofs are `generic_allSound`, `divisible_allSound`,
`divmod_allSound`: the theorems are about the passes restricted to the proven rules
(`GoFV.Rules.Proven`, regenerated by `scripts/rule-proofs.py proven`), so every merged rule lemma
widens what the theorem covers without changing its statement. Register typing at the leaves
(`Rule.Sound`'s `Pat.typed`) is `Val.retype_hasTy` (#108): the validator's leaves are defined
values (`leavesOK`), whose denotations have their type's shape at every shape. Witness:
`GoFV.Proof.Witness.addZero_refines` (the theorem on the `addZero` run above); for a block rule
`GoFV.Proof.Witness.notIf_refines` (`if !b {return 1}; return 2` with `{generic.rules:1064}`:
the entry becomes `If b` with swapped successors, kernel evaluation; the output returns
`notIf(false) = 1`). Validator
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

Corpus `quick-v3/plain`: 9297 functions with a rewrite section; every section at stock under the proven-only passes 8152, under the checked passes 8055 (validator the only obstacle: 97). Functions off stock by the number of unproven rules the full passes fire on their sections off stock: 0: 6, 1: 413, 2: 317, 3 or more: 409.

| Rule | Lemma | Class | Firings | Sole obstacle | Unblocks |
| --- | --- | --- | --: | --: | --: |
| `generic.rules:1071 Convert` | `r_generic_1071/r_generic_1071_2` | P2 | 218 | 89 | 89 |
| `generic.rules:278 IsSliceInBounds` | `r_generic_278` | P2 | 289 | 78 | 78 |
| `generic.rules:1638 SelectN` | `r_generic_1638/r_generic_1638_2` | call | 38 | 31 | 31 |
| `generic.rules:1053 SliceMake` | `r_generic_1053` | P2 | 88 | 21 | 21 |
| `generic.rules:1049 SliceLen` | `r_generic_1049` | ptr | 79 | 19 | 19 |
| `generic.rules:827 Load` | `r_generic_827` | mem | 1151 | 17 | 17 |
| `generic.rules:1730 SelectN` | `r_generic_1730/r_generic_1730_2` | call | 139 | 17 | 17 |
| `generic.rules:830 Load` | `r_generic_830` | mem | 46 | 16 | 16 |
| `generic.rules:1833 Store` | `r_generic_1833` | mem | 43 | 12 | 12 |
| `generic.rules:2342 CondSelect` | `r_generic_2342/r_generic_2342_2/r_generic_2342_3` | P1 | 24 | 10 | 10 |
| `generic.rules:1075 Convert` | `r_generic_1075/r_generic_1075_2` | P2 | 21 | 8 | 8 |
| `generic.rules:2371 CondSelect` | `r_generic_2371/r_generic_2371_2/r_generic_2371_3` | P1 | 9 | 8 | 8 |
| `generic.rules:1857 Store` | `r_generic_1857` | mem | 40 | 7 | 7 |
| `generic.rules:1844 Store` | `r_generic_1844` | mem | 38 | 7 | 7 |
| `generic.rules:2159 Zero` | `r_generic_2159` | mem | 6 | 6 | 6 |
| `generic.rules:1352 Zero` | `r_generic_1352` | call | 85 | 5 | 5 |
| `generic.rules:1005 Store` | `r_generic_1005` | mem | 23 | 4 | 4 |
| `generic.rules:1743 Move` | `r_generic_1743` | mem | 8 | 4 | 4 |
| `generic.rules:1035 SlicePtr` | `r_generic_1035` | P2 | 179 | 3 | 3 |
| `generic.rules:2155 Move` | `r_generic_2155` | mem | 145 | 3 | 3 |
| `generic.rules:943 Store` | `r_generic_943` | mem | 35 | 3 | 3 |
| `generic.rules:1357 Store` | `r_generic_1357` | call | 28 | 3 | 3 |
| `generic.rules:1381 NilCheck` | `r_generic_1381` | mem | 5901 | 2 | 2 |
| `generic.rules:1691 IsNonNil` | `r_generic_1691` | mem | 56 | 2 | 2 |
| `generic.rules:1036 SliceLen` | `r_generic_1036` | P2 | 33 | 2 | 2 |
| `generic.rules:770 Slicemask` | `r_generic_770` | P1 | 31 | 2 | 2 |
| `divmod.rules:148 Div64u` | `r_divmod_148` | P1 | 29 | 2 | 2 |
| `generic.rules:1183 Eq64` | `r_generic_1183_3` | P1 | 16 | 2 | 2 |
| `generic.rules:1680 NeqPtr` | `r_generic_1680` | P2 | 7 | 2 | 2 |
| `generic.rules:531 Rsh32Ux64` | `r_generic_531` | P1 | 3 | 2 | 2 |
| `generic.rules:744 Or32` | `r_generic_744` | P1 | 3 | 2 | 2 |
| `divmod.rules:221 Div32u` | `r_divmod_221` | P1 | 2 | 2 | 2 |
| `generic.rules:2325 CondSelect` | `r_generic_2325/r_generic_2325_2/r_generic_2325_3` | P1 | 2 | 2 | 2 |
| `generic.rules:2128 SliceLen` | `r_generic_2128/r_generic_2128_2` | call | 100 | 1 | 1 |
| `generic.rules:1689 IsNonNil` | `r_generic_1689` | ptr | 58 | 1 | 1 |
| `generic.rules:1648 EqPtr` | `r_generic_1648` | ptr | 22 | 1 | 1 |
| `generic.rules:981 IMake` | `r_generic_981` | ptr | 15 | 1 | 1 |
| `generic.rules:919 Store` | `r_generic_919` | mem | 15 | 1 | 1 |
| `generic.rules:2158 Zero` | `r_generic_2158` | mem | 13 | 1 | 1 |
| `generic.rules:1687 IsNonNil` | `r_generic_1687` | P2 | 12 | 1 | 1 |
| `generic.rules:2146 Move` | `r_generic_2146` | mem | 12 | 1 | 1 |
| `generic.rules:1651 NeqPtr` | `r_generic_1651` | ptr | 11 | 1 | 1 |
| `generic.rules:1183 Eq32` | `r_generic_1183_2` | P1 | 6 | 1 | 1 |
| `generic.rules:2355 CondSelect` | `r_generic_2355/r_generic_2355_2/r_generic_2355_3/r_generic_2355_4` | P1 | 3 | 1 | 1 |
| `generic.rules:1564 Load` | `r_generic_1564` | mem | 2 | 1 | 1 |
| `divisible.rules:152 Eq64` | `r_divisible_152` | P1 | 2 | 1 | 1 |
| `generic.rules:2166 Or64` | `r_generic_2166_2` | P1 | 2 | 1 | 1 |
| `generic.rules:1324 Mul64F` | `r_generic_1324_2` | float | 2 | 1 | 1 |
| `generic.rules:2168 Or16` | `r_generic_2168_2` | P1 | 1 | 1 | 1 |
| `generic.rules:1331 Div64F` | `r_generic_1331` | float | 1 | 1 | 1 |
| `generic.rules:1742 Move` | `r_generic_1742` | mem | 1 | 1 | 1 |
| `generic.rules:2167 Or32` | `r_generic_2167_2` | P1 | 1 | 1 | 1 |
| `generic.rules:2368 CondSelect` | `r_generic_2368` | P1 | 1 | 1 | 1 |
| `generic.rules:1367 NilCheck` | `r_generic_1367` | call | 1909 | 0 | 0 |
| `generic.rules:800 Load` | `r_generic_800` | mem | 1446 | 0 | 0 |
| `generic.rules:975 Store` | `r_generic_975` | mem | 810 | 0 | 0 |
| `generic.rules:1062 NilCheck` | `r_generic_1062` | mem | 686 | 0 | 0 |
| `generic.rules:1375 NilCheck` | `r_generic_1375` | mem | 679 | 0 | 0 |
| `generic.rules:974 Load` | `r_generic_974` | mem | 580 | 0 | 0 |
| `generic.rules:806 Load` | `r_generic_806` | mem | 488 | 0 | 0 |
| `generic.rules:1384 NilCheck` | `r_generic_1384` | mem | 488 | 0 | 0 |
| `generic.rules:997 Store` | `r_generic_997` | mem | 241 | 0 | 0 |
| `generic.rules:813 Load` | `r_generic_813` | mem | 224 | 0 | 0 |
| `generic.rules:2255 Load` | `r_generic_2255` | mem | 181 | 0 | 0 |
| `generic.rules:1037 SliceCap` | `r_generic_1037` | P2 | 114 | 0 | 0 |
| `generic.rules:1362 Store` | `r_generic_1362` | call | 107 | 0 | 0 |
| `generic.rules:785 Phi` | `r_generic_785` | phi | 89 | 0 | 0 |
| `generic.rules:1584 MemEq` | `r_generic_1584` | P2 | 73 | 0 | 0 |

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
(`rule_bits`); never `bv_decide`, see below). The rules' `c&d`, `c|d`, `c^d` constant
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
`hty` (`refines_retype_of_hasTy`). `rule_auto` does not close them. Nil comparisons
(RuleProofs8, `EqPtr.lean`): `Ptr.null.eq p = p.isNil`
(`null_eq`). Constant composites (RuleProofs8, `ConstComp.lean`): `hty` fixes the top type's
fields (`ty_of_hasTy_agg`, `ty_of_hasTy_null`, `ty_of_hasTy_int64`), then `Refines.refl`.

**Range checks** (#69, RuleProofs9; `AndB*.lean`, `OrB*.lean`: `generic.rules:321–366`, 64
lemmas, tactic `rule_range` in `TacticRange.lean`). `AndB`/`OrB` of two comparisons of `x` with
constants become one unsigned comparison of `x - c` (or `c - d` with `x - d`). With one
operand a mistyped constant its comparison is `none` and the result a `match none, some b`:
`bool_split1` cases on `b` (`rcases hb : b`), next to `rule_split1`, under `repeat'` (`repeat`
stops at the first case it cannot split, leaving the others unsplit). Each residual goal equates
the result with the comparisons the splits decided; one of the 16 `range_*` lemmas
(`RangeLemmas*.lean`, any width; e.g. `range_and_s : c.toInt ≤ d.toInt → (x - c).ult (d - c) = (c.sle x && x.slt d)`, side
condition at the constants by `Int.bmod_eq_of_le`/`BitVec.toNat_ofInt` and `omega`) rewrites it
to the `&&`/`||` of the case hypotheses, closed by `simp_all`. Closing each residual goal by
`omega` instead (comparisons as `toNat`/`toInt` arithmetic, both cases of every signed reading
`if 2 * x.toNat < 2 ^ w then …` as a hypothesis: `ite_facts`) worked but stored ~800 kB of
`.olean` per lemma (LEARNINGS.md). The single-bit rules `:369`/`:372` (`x|(c^d) == c`) are not
covered: see "Findings" (the reused `cv` constant node may be mistyped).

**Kernel "deep recursion"** (#69, RuleProofs10; `TacticCond.lean`, `DivmodU2.lean`, `DivmodU3.lean`). For
`divmod.rules:159/171/180/206/232` (64-bit `umagic`, `umagic(c).m` in the condition, `Avg64u`)
the kernel rejected the elaborated proof. Cause: `simp` applies `@[defeq]` lemmas
(`Option.getD_some`, `Option.elim_some`) without a proof step, so the next rewrite's
`congrArg` makes the kernel compare `bif umagicOK 64 c then …` with `(some (bif …)).getD d`
(`if x < y then …` with `(some y).elim …`); its lazy delta unfolds the `bif`/`if` side and
evaluates `umagicOK 64 c` / `Nat.decLt` on symbolic terms (LEARNINGS.md). `rule_unfold_getd`
evaluates the condition without `Option.getD` in the `dsimp` set (`rule_cond_ds`) and
rewrites it by `simp` with `getD_some_p` (a proof term); under `open
GoFV.Proof.Rules.KernelSafe`, `rule_norm` (also inside `rule_split1`) lists `getD_some_p` and
`elim_some_p` first, so they apply before the `rfl` lemmas of the simp sets. Then `divu_auto` as for `:154`, the condition's
`m&1 == 0` / `c&1 == 0` as `m % 2 = 0` (`m_even_of_and_one`) / `lowBits 64 c % 2 = 0`
(`lowBits_even_of_and_one`), and the closers `close_hmul_half` (180), `close_mul_half` (171),
`close_mul_full` (159), `close_hmul_even` (206; `umagic(c).m + 1` does not wrap for an even
divisor, `m_succ_lt`), `close_avg_hmul` (232; `Avg64u` sees `x ≥ Hmul x m`, `hmul_le`).

**Float rules** (#69, RuleProofs12/13; `FloatCmp.lean`, `FloatRules.lean`, `FloatArith.lean`).
Den: float auxints and literals are `DV.f64`/`DV.f32` (their IEEE encodings; a literal check
`[c]` compares encodings, which for `±0` is stricter than Go's `==`), the condition language
compares them by `IEEE.compare` (`floatCmp`), `auxIntOk` says a float auxint is not NaN (check.go),
and `argShapeOk` gives the float ops' arguments the integer shape of their width.
- `OrB (Neq64F x x) (cmp x c)` and its swapped, `Abs x` and `Neg64F x` forms (375/376/381/382/
  385/386, 12 lemmas, `float_auto`): a NaN `x` makes every comparison `un` (`compare_nan_*`;
  `Abs`/`Neg` keep NaN-ness, `isNaN_abs`, `isNaN_neg`), so `Neq x x` is true and the rule's
  `Not (cmp' c x)` too; otherwise `compare x x = eq` (`compare_self`), `compare c x` is the
  swapped `compare x c` (`compare_swap`), and the three ordered results are split
  (`compare_cases`, the constant not NaN by `auxIntOk`). A mistyped operand of `OrB` (`none`)
  leaves the other operand's Boolean to `bool_split1`. The 32-bit forms (377/378/387/388) need
  `isNaN` of `Const32F`'s `IEEE.convert` and are not proved (no firings).
- Constant folds `generic.rules:622–629` (8 lemmas, `float_const`): both sides compute the same
  `IEEE.compare` of the same encodings; a split on its result closes them.
- `generic.rules:1328` `(Mul64F x (Const64F [2])) => (Add64F x x)`: `IEEE.round` only sees
  the value `mant * 2^exp`, so `round f rm s (m * 2^k) (e - k) = round f rm s m e`
  (`round_scale`: same leading bit, same ulp position, `truncShift` of `m * 2^k` by `t + k` is
  `truncShift m t`). `x * 2` rounds `m * 2^52` at `e - 51` (`2` unpacks as `2^52 * 2^-51`) and
  `x + x` rounds `2m` at `e` (`mul_two_eq_add`, any format and either operand order; NaN,
  infinity and zero cases agree as well), so `Mul64F v 2 = Add64F v v` for every value
  (`fops_mul_two64`).
- 1324–1326 (`x * 1 → x`, `x * -1 → -x`) are not proved: they change a NaN's encoding (#176).

**Bounds checks, comparisons, selections** (#69, RuleProofs14).
- `IsInBounds.lean`, `IsSliceInBounds.lean`: `rule_auto` closes `:240`, `:242`, `:247`, `:250`,
  `:252`, `:253`, `:273`, `:275`. The constant folds `:255`/`:277` close by `bounds_auto`
  (`rule_auto` with `ult_ofInt64`/`ule_ofInt64`: for `d ≥ 0`, `c <ᵤ d` iff `0 ≤ c < d`); `x x`
  (`:243`, `:271`) by `inBounds_self`. The 32-bit forms and `:257` (a `Mod32u` at a 64-bit
  argument is always `poison`) have no instance with the 64-bit arguments `argShapeOk` asks
  for; `:278` waits on nonnegative slice lengths (#10).
- `NeqConst.lean` (`:585`, four widths): `neqc_auto` closes `ofInt c ≠ ofInt d` for distinct
  auxints in range (`ofInt_ne_of_range`).
- `IfaceCmp.lean` (`:790–793`): `eqFirst_refines`. The first words of the operands are
  compared before and after `ITab`'s `uintptr` / `SlicePtr`'s `*byte` retype; a retype to a
  pointer shape keeps a word's pointer, a retype to `uintptr` keeps a word of the 64-bit integer
  shape (`ifaceArgOk`).
- `SelMake.lean` (`:992`, `:1012`, `:1031`, `:1032`): as `Dec.lean`'s selections (`dec_unfold`,
  `sel_make2`/`sel_make3`). Not proved: `:1035–1038` (a selection of a selection, retyped at the
  inner and the outer type).
- `:1071`/`:1075` (`(Convert (Add64 (Convert ptr mem) off) mem) => (AddPtr ptr off)`) are false
  under the semantics: `Convert` of an integer is `Ptr.ofAddr` of any address, while `AddPtr`
  is `poison` outside the allocation's window (§3.3). Go's unsafe rules make the
  out-of-window case undefined; the model would need `Convert` to poison it.

Match congruence equations (`binDV.match_4.congr_eq_*`, …) are generated once in
`Tactic.lean`: generated by `simp` in two rule modules they are two public declarations of the
same name and the modules cannot be imported together (`scripts/axioms-audit.sh`, which
`scripts/rule-proofs.py axioms` runs, imports every module, so it catches this).

`bv_decide` stores an LRAT certificate per goal in the `.olean` (`<thm>._cert_def_N`, up to
9 MB for one 64-bit ring identity) and adds `_native.bv_decide.ax_*` axioms, which
`scripts/axioms-audit.sh` rejects. `rule_close` therefore has no `bv_decide` fallback (#69,
RuleProofs13: #214 merged 30 proofs that fell through to it, #218 replaced them). Its last
closer is `bv_decide`'s rewriting front end alone, `bv_normalize` (no SAT call, no axioms;
`enums := false`, else it declares `PUnit.enumToBitVec` in every module and two rule modules no
longer import together), which closes 12 goals of EqB/NeqB/Or*/Rsh that `bv_decide` used to
close before reaching the SAT solver; a goal it leaves open fails. The dropped `bv_decide`
cases also removed the need for
`set_option Elab.async false` in the rule modules (LEARNINGS.md, "`bv_decide` certificates in
rule-lemma `.olean`s").

`scripts/rule-proofs.py probe <Family>` tries `rule_auto` on the pending rules of a family
(`tmp/rules/probe-<Family>.tsv`: rule, `OK`/`FAIL` — `FAIL` also when the proof uses an axiom
other than `propext`, `Classical.choice`, `Quot.sound` —, ms, distinct subterms of the proof
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
  pointers, `inst_r_generic_126` AddPtr, `inst_r_generic_1057` ConstInterface,
  `inst_r_generic_1044` ConstSlice, `inst_r_generic_1684`/`_1683` NeqPtr/EqPtr of nil,
  `inst_r_generic_322` AndB and `inst_r_generic_346` OrB range checks, `inst_r_generic_369`/`_372`
  single-bit tests, `inst_r_generic_1072` `Convert` round trip).
  `Rule.Inst` includes `Oracle.BoolTyped` and `Pat.argsOK`; `Oracle.const b` satisfies it
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

- **`generic.rules:1071`, `:1075` (`Convert` of an integer offset from a converted pointer)**:
  false under the semantics, not a Go bug: integers carry no provenance, so the pointer the
  outer `Convert` makes from `addr(p) + off` need not be `p`'s allocation (Semantics, #156).
  `:1072` (`(Convert (Convert p mem) mem) => p`) and `:1683`/`:1684` became provable with
  #156's pointer model (address windows, convertible pointers, nil comparison by block);
  `:1072` is proven (`Convert.lean`, RuleProofs11) once `convArgOk` rules out a `Convert` of a
  type other than a pointer or a 64-bit integer (an `int32` one would truncate the leaf).
  Integer → pointer → integer uses `Ptr.addr?_ofAddr` (the pointer at an address has that
  address).

- **`generic.rules:1053`** (`(SliceMake (AddPtr <t> x (And64 y (Slicemask _))) w:(Const64
  [c]) z) && c > 0 => (SliceMake (AddPtr <t> x y) w z)`): false under the semantics, not a Go
  bug. Go's comment: "len > 0 implies cap > 0 implies Slicemask is all 1"; the pattern does
  not check that the `Slicemask` argument is the capacity, which `ssagen` guarantees. At
  `Slicemask (Const64 [0])`, `x = ⟨heap 0, 0⟩`, `y = 8`, `c = 1` the slice pointer is `x`, the
  result's `x + 8`. Needs a provenance fact about the `Slicemask` argument. `:1039`
  (`config.PtrSize == 4`) builds 32-bit lengths into a 64-bit slice shape (`rule-sat`
  counterexample). Marked `-- FALSE … #69` in `ConstComp.lean`.

- **`isNonNegative(x)` rules** (`generic.rules:610`, `:611`, `:1090`, `:1134–1138`; RuleProofs10,
  proven by RuleProofs12): false under the bare semantics, not Go bugs. `isNonNegative` is an
  oracle atom (it reads the value graph), so without a premise nothing makes `x` non-negative;
  e.g. `:610` (`(Less64 (Const64 [0]) x) => (Neq64 (Const64 [0]) x)`) at `x = -1`: `false` vs
  `true`. The obligation now carries `Pat.nonNegOK` (see "The obligation"); with it all
  are proven (`Less.lean`, `Div.lean` with `sdiv_intMin64_of_msb`, `Mod.lean` with
  `mods_pow2`/`srem_pow2_of_msb` in `DivmodSPow2.lean`).

- **`CondSelect` into arithmetic** (`generic.rules:2342`, `:2371`; RuleProofs10): false under
  the semantics, not Go bugs. At `bool = false` the matched value is the leaf `x` itself, the
  result recomputes it (`x - 0`, `x | 0`); a 64-bit integer register may hold an address-less
  pointer (`Val.hasTy`), on which `Sub64`/`Or64` are `poison`. Also the `Add64`/`Or64` node
  and its `Const64` argument are op nodes whose type `Rule.Sound` does not constrain (a
  mistyped node is `poison`, the leaf is not). The other `CondSelect` rules of
  `generic.rules:2325–2393` have the same shape. Marked `-- FALSE … #69` in `Add.lean`,
  `Or.lean` for the two rows of the firing table.

- **`generic.rules:369`, `:372`** (`(OrB (Eq64 x cv:(Const64 [c])) (Eq64 x (Const64 [d])))
  && c|d == c && oneBit(c^d) => (Eq64 (Or64 x (Const64 [c^d])) cv)`, and the `AndB`/`Neq`
  form): proven (#69 RuleProofs11, `OneBit.lean`, `OneBit2.lean`, all widths). Under the old
  obligation they were false: `cv` (the first `Const64`, reused in the result) could be an op
  node typed `int32` (its value `poison`), and `OrB` is parallel, so `OrB poison (x == d)` is
  `true` while the result `Eq64 … cv` is `poison`. `argShapeOk` now asks both arguments of
  `Eq<N>`/`Neq<N>` to be `N`-bit integers. The bit identity is `onebit_bv`
  (`x | (c^d) == c` iff `x == c || x == d` when `d ⊆ c` and `c^d` is one bit); `onebit_int`
  and `onebit_int_ne` read it off the condition's `Int` facts.

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
non-vacuity theorems: `scripts/rule-proofs.py axioms` runs the gate's `scripts/axioms-audit.sh`
(empty allowlist), and `probe` fails a rule whose proof uses any other axiom.
