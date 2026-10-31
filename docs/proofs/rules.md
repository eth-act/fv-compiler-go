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
- **Expressions** (conditions, `[auxint]`, `<type>`) are evaluated by `evalE`, a total pure
  evaluator mirroring `GoFV.Rules.Eval.eval` on integers, booleans, op constants, type shapes
  (`typ.<T>`, `types.Types[k]`, `t.Size()` of an integer/boolean shape) and the pure
  `rewrite.go` helpers (`isPowerOfTwo`, `log*`, `ntz*`, `nlz*`, `bits.*`, `uaddOvf`,
  `shiftIsBounded`, the `magic`/`divisible` helpers, …). Everything else — `x.Uses`,
  `clobber`, `config` fields, `canRotate`, symbol helpers, floats, `x.Op` — comes from an
  `Oracle`, over which the obligation is universally quantified. So a rule whose correctness
  needs such an atom cannot be proved from this denotation (none of the P1 rules needs one);
  side conditions such as `x.Uses == 1 && clobber(x)` are simply ignored. The same holds on the
  result side: an aux, type or auxint the evaluator does not model is the oracle's, i.e. the
  rule must be correct for every choice.
- **Commutative patterns**: only the written argument order is considered. The interpreter's
  swapped matches are covered by `GoFV/Proof/Rules/Comm.lean` (`commOpsP1_sound`: every
  phase-P1 op that a pattern marks `commute` is symmetric in its first two arguments).

What the interpreter's proof must supply when it applies `Rule.Sound`: the instance read off
the matched values (leaf values from the registers, node fields from the values), the
condition's evaluation (`GoFV.Rules.Eval.eval` agrees with `evalE` where `evalE` does not
defer to the oracle; `eval` is `partial` today and needs a structural rewrite for that proof),
the checker facts, that `typ.<T>`/`types.Types[k]` of the export's `Config.Types` have the
shapes of `typShape`/`typesShape`, and `CommSound` for swapped matches. `Rule.Sound` ignores
`@b` placement and positions; a copy result's new type is the interpreter's concern
(`Val.retype` is idempotent, so a copied value is unchanged).

## Classification

`GoFVTest/Proof/RuleClass.lean` classifies each rule by the semantic phase of its ops
(`docs/plans/semantics.md` §9): `P1` (every op of pattern and result has a phase-P1 arm in
`evalPure`: integers, booleans, tuples; fixed arity; build or variable-copy result), else the
first later-phase op by priority `call` > `mem` > `float` > `ptr` (pointers, composites,
strings, interfaces, other) > `phi`; `block` for block rules.

<!-- BEGIN classes -->
<!-- END classes -->

## Coverage

Per rule file and op family of the top op. *Proven*: a `Rule.Sound` lemma is merged.
*False*: the rule is wrong under the stated semantics (see "Findings"). *Not P1*: the rule
needs a later phase of the semantics.

<!-- BEGIN coverage -->
<!-- END coverage -->

Regenerate both tables with `scripts/rule-proofs.py table` (it reruns the classifier if
`tmp/rules/class.tsv` is missing).

## Proof method (`GoFV/Proof/Rules/Tactic.lean`)

`rule_auto` = `rule_unfold` (reduce `Rule.Sound r` for the concrete rule data: denotation
definitions by `simp only`; `evalPure`, `Op.auxType` and the helper dispatch by dsimprocs
that unfold once at a constructor or string literal, so `simp` never sees the 446-arm
`match`es) → `rule_norm` (`simp_all` with the op families unfolded to `BitVec`/`Bool` terms)
→ case splits (`rule_split1`: whether a leaf is an integer of the width its consumer reads
— the leaf is then replaced by that integer —, whether a node's type is an integer of another
width, `if` conditions, disjunctions) → `rule_close` (auxint reads generalized to bounded
`Int`s, constants pushed into `BitVec.ofInt`, shifts and rotations by `BitVec` amounts, then
`rfl`, `bv_decide` or `grind`). `bv_decide` adds its `Lean.ofReduceBool` certificate axiom
(allowed, `docs/PLAN.md` §0); the axioms of each module are listed below.

`scripts/rule-proofs.py probe <Family>` tries `rule_auto` on the pending rules of a family
(`tmp/rules/probe-<Family>.tsv`); `emit <Family>` writes the module for the rules that passed.

## Non-vacuity

`Rule.Sound` is one definition for all rules, so its non-vacuity is shown once and per family
rather than per lemma (agreed with Main): `GoFV/Proof/Rules/NonVacuous.lean` proves that a
mutated rule is not sound and that the false rules below are not, and gives, per op-family
module, concrete instances of representative rules whose hypotheses hold with a non-poison
source value.

## Findings

<!-- findings are added here with their issues -->

## Narrow result types

`Rule.Sound` assumes the matched value's type is not narrower than its op. The checker does
not guarantee this, and `divmod.rules` builds such values (`(Rsh64x64 <typ.UInt32> …)` read
as their low bits by `Val.retype`). A rule whose result is a copy (`=> x`) or has its own
`<type>` changes the shape of such a value: under the semantics the rewrite is then not a
refinement (e.g. `(Rsh64x64 x (Const64 [0])) => x` on a value typed `uint32` turns a 32-bit
value into a 64-bit one). The interpreter proof needs either a typing invariant excluding
such matches or a semantics in which a narrow-typed value is read at its op's width.

## Build cost

<!-- per-module build cost is added when the modules land -->
