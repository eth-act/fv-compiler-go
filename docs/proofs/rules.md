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

### Assumptions to discharge (#108)

`Rule.Sound` assumes two typing facts the interpreter's proof must establish from a semantic
invariant of `GoFV.SSA.Sem`, not from the rule:

- **Register typing** (for `Pat.typed`): in every reachable state, every register `v` the
  match reads as a leaf holds a value of its type's shape,
  `(regVal v).hasTy (tabs.ty v.Type) = true` (`Val.hasTy`; `poison` has every shape). The
  instance then sets `e.leaf p := regVal v` and `e.ty p := tabs.ty v.Type`. This is the same
  register-typing invariant the phi passes need (ProofPhiopt, owned by agent Semantics); it does
  not hold today for some bool-typed `Phi`/`Load`/`SelectN`/`StructSelect` registers, which
  Semantics is closing.
- **Top type** (`hty`): the matched value's op computes a value of its type's shape before
  `retype`, i.e. no narrow result types (see "Narrow result types").

## Classification

`GoFVTest/Proof/RuleClass.lean` classifies each rule by the semantic phase of its ops
(`docs/plans/semantics.md` §9): `P1` (every op of pattern and result has a phase-P1 arm in
`evalPure`: integers, booleans, tuples; fixed arity; build or variable-copy result), else the
first later-phase op by priority `call` > `mem` > `float` > `ptr` (pointers, composites,
strings, interfaces, other) > `phi`; `block` for block rules.

<!-- BEGIN classes -->
<!-- Generated by scripts/rule-proofs.py table. -->

| File | P1 | mem | call | float | ptr | phi | block | Total |
| --- | --: | --: | --: | --: | --: | --: | --: | --: |
| `generic` | 1336 | 118 | 47 | 68 | 77 | 5 | 3 | 1654 |
| `dec` | 0 | 26 | 0 | 0 | 21 | 0 | 0 | 47 |
| `divisible` | 32 | 0 | 0 | 0 | 0 | 0 | 0 | 32 |
| `divmod` | 27 | 0 | 0 | 0 | 2 | 0 | 0 | 29 |
| all | 1395 | 144 | 47 | 68 | 100 | 5 | 3 | 1762 |

<!-- END classes -->

## Coverage

Per rule file and op family of the top op. *Proven*: a `Rule.Sound` lemma is merged.
*False*: the rule is wrong under the stated semantics (see "Findings"). *Not P1*: the rule
needs a later phase of the semantics.

<!-- BEGIN coverage -->
<!-- Generated by scripts/rule-proofs.py table. -->

| File | Family | Proven | Pending (P1) | False | Not P1 | Total |
| --- | --- | --: | --: | --: | --: | --: |
| `dec` | ArrayMake | 0 | 0 | 0 | 1 | 1 |
| `dec` | ArraySelect | 0 | 0 | 0 | 4 | 4 |
| `dec` | ComplexImag | 0 | 0 | 0 | 3 | 3 |
| `dec` | ComplexReal | 0 | 0 | 0 | 3 | 3 |
| `dec` | IData | 0 | 0 | 0 | 2 | 2 |
| `dec` | IMake | 0 | 0 | 0 | 2 | 2 |
| `dec` | ITab | 0 | 0 | 0 | 2 | 2 |
| `dec` | Load | 0 | 0 | 0 | 5 | 5 |
| `dec` | SliceCap | 0 | 0 | 0 | 2 | 2 |
| `dec` | SliceLen | 0 | 0 | 0 | 2 | 2 |
| `dec` | SlicePtr | 0 | 0 | 0 | 2 | 2 |
| `dec` | SlicePtrUnchecked | 0 | 0 | 0 | 1 | 1 |
| `dec` | Store | 0 | 0 | 0 | 8 | 8 |
| `dec` | StringLen | 0 | 0 | 0 | 2 | 2 |
| `dec` | StringPtr | 0 | 0 | 0 | 2 | 2 |
| `dec` | StructMake | 0 | 0 | 0 | 1 | 1 |
| `dec` | StructSelect | 0 | 0 | 0 | 5 | 5 |
| `divisible` | Eq | 0 | 16 | 0 | 0 | 16 |
| `divisible` | Neq | 0 | 16 | 0 | 0 | 16 |
| `divmod` | Div | 0 | 27 | 0 | 2 | 29 |
| `generic` | Add | 88 | 1 | 4 | 2 | 95 |
| `generic` | AddPtr | 0 | 0 | 0 | 2 | 2 |
| `generic` | And | 40 | 8 | 0 | 0 | 48 |
| `generic` | AndB | 0 | 36 | 0 | 0 | 36 |
| `generic` | ArraySelect | 0 | 0 | 0 | 2 | 2 |
| `generic` | BitLen | 0 | 8 | 0 | 0 | 8 |
| `generic` | Block | 0 | 0 | 0 | 3 | 3 |
| `generic` | Ceil | 0 | 0 | 0 | 1 | 1 |
| `generic` | Com | 12 | 0 | 0 | 0 | 12 |
| `generic` | CondSelect | 0 | 59 | 0 | 0 | 59 |
| `generic` | ConstInterface | 0 | 0 | 0 | 1 | 1 |
| `generic` | ConstSlice | 0 | 0 | 0 | 2 | 2 |
| `generic` | ConstString | 0 | 0 | 0 | 4 | 4 |
| `generic` | Convert | 0 | 0 | 0 | 5 | 5 |
| `generic` | Ctz | 0 | 8 | 0 | 0 | 8 |
| `generic` | Cvt | 0 | 0 | 0 | 11 | 11 |
| `generic` | CvtBoolToUint | 0 | 2 | 0 | 0 | 2 |
| `generic` | Div | 0 | 22 | 0 | 4 | 26 |
| `generic` | Eq | 44 | 12 | 0 | 2 | 58 |
| `generic` | EqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | EqInter | 0 | 0 | 0 | 1 | 1 |
| `generic` | EqPtr | 0 | 0 | 0 | 20 | 20 |
| `generic` | EqSlice | 0 | 0 | 0 | 1 | 1 |
| `generic` | Floor | 0 | 0 | 0 | 1 | 1 |
| `generic` | IMake | 0 | 0 | 0 | 2 | 2 |
| `generic` | InterLECall | 0 | 0 | 0 | 1 | 1 |
| `generic` | IsInBounds | 0 | 29 | 0 | 0 | 29 |
| `generic` | IsNonNil | 0 | 0 | 0 | 6 | 6 |
| `generic` | IsSliceInBounds | 0 | 7 | 0 | 1 | 8 |
| `generic` | Leq | 60 | 0 | 0 | 2 | 62 |
| `generic` | Less | 52 | 8 | 0 | 2 | 62 |
| `generic` | Load | 0 | 0 | 0 | 35 | 35 |
| `generic` | Lsh | 65 | 23 | 0 | 0 | 88 |
| `generic` | MemEq | 0 | 0 | 0 | 11 | 11 |
| `generic` | Mod | 0 | 29 | 0 | 0 | 29 |
| `generic` | Move | 0 | 0 | 0 | 25 | 25 |
| `generic` | Mul | 36 | 16 | 0 | 8 | 60 |
| `generic` | Neg | 24 | 0 | 0 | 2 | 26 |
| `generic` | Neq | 40 | 12 | 0 | 2 | 54 |
| `generic` | NeqB | 5 | 0 | 0 | 0 | 5 |
| `generic` | NeqInter | 0 | 0 | 0 | 1 | 1 |
| `generic` | NeqPtr | 0 | 0 | 0 | 20 | 20 |
| `generic` | NeqSlice | 0 | 0 | 0 | 1 | 1 |
| `generic` | NilCheck | 0 | 0 | 0 | 8 | 8 |
| `generic` | Not | 27 | 0 | 0 | 6 | 33 |
| `generic` | OffPtr | 0 | 0 | 0 | 2 | 2 |
| `generic` | Or | 72 | 4 | 4 | 0 | 80 |
| `generic` | OrB | 0 | 36 | 0 | 20 | 56 |
| `generic` | Phi | 0 | 0 | 0 | 5 | 5 |
| `generic` | PopCount | 0 | 8 | 0 | 0 | 8 |
| `generic` | PtrIndex | 0 | 0 | 0 | 2 | 2 |
| `generic` | RotateLeft | 88 | 0 | 0 | 0 | 88 |
| `generic` | Round | 0 | 0 | 0 | 2 | 2 |
| `generic` | RoundToEven | 0 | 0 | 0 | 1 | 1 |
| `generic` | Rsh | 116 | 24 | 0 | 0 | 140 |
| `generic` | Select | 0 | 3 | 0 | 0 | 3 |
| `generic` | SelectN | 0 | 0 | 0 | 15 | 15 |
| `generic` | SignExt | 15 | 0 | 0 | 0 | 15 |
| `generic` | SliceCap | 0 | 0 | 0 | 5 | 5 |
| `generic` | SliceLen | 0 | 0 | 0 | 6 | 6 |
| `generic` | SliceMake | 0 | 0 | 0 | 2 | 2 |
| `generic` | SlicePtr | 0 | 0 | 0 | 1 | 1 |
| `generic` | Slicemask | 0 | 4 | 0 | 0 | 4 |
| `generic` | Sqrt | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticCall | 0 | 0 | 0 | 1 | 1 |
| `generic` | StaticLECall | 0 | 0 | 0 | 24 | 24 |
| `generic` | Store | 0 | 0 | 0 | 21 | 21 |
| `generic` | StringLen | 0 | 0 | 0 | 1 | 1 |
| `generic` | StringPtr | 0 | 0 | 0 | 1 | 1 |
| `generic` | StructSelect | 0 | 0 | 0 | 4 | 4 |
| `generic` | Sub | 68 | 0 | 0 | 2 | 70 |
| `generic` | Trunc | 32 | 0 | 0 | 1 | 33 |
| `generic` | Xor | 56 | 8 | 4 | 0 | 68 |
| `generic` | Zero | 0 | 0 | 0 | 6 | 6 |
| `generic` | ZeroExt | 12 | 0 | 0 | 0 | 12 |
| all | | 957 | 426 | 12 | 367 | 1762 |

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

`lake exe opt-proven-probe <corpus>` runs both variants on every stock instance's input. Quick
corpus (`quick-v1`, 9,297 functions; 566 proven rules; "rules fired": value and block rules,
`RwState.fired`, each instance run on the stock input):

| Pass | Full parity | Proven-only parity | Proven-only no-op | Rules fired (full) | Rules fired (proven-only) | Firings kept |
| --- | --: | --: | --: | --: | --: | --: |
| opt | 100.00% | 41.82% | 75.51% | 99,454 | 11,589 | 11.65% |
| middle opt | 100.00% | 76.37% | 96.44% | 11,934 | 669 | 5.61% |
| late opt | 100.00% | 84.60% | 1.37% | 8,314 | 47 | 0.57% |
| divisible | 100.00% | 99.92% | 62.34% | 9 | 0 | 0.00% |
| divmod | 100.00% | 97.88% | 98.11% | 441 | 0 | 0.00% |

"No-op": the proven-only output equals the input (late opt's inputs carry dead values that
every variant removes). The proven-only passes keep copy elimination, phi elimination and
dead-value removal.

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
is not another integer width is the identity (`retype_int_of_not_other`, `rule_sem`); negated
comparisons and boolean equations (`not_slt_eq`, …, `not_beq_eq`, `rule_close_s`); `rule_ext`
closes a value truncated and extended again after a shift cleared or sign-filled its high bits
(`ushr_setWidth_setWidth`, `sshr_setWidth_signExtend`), else both sides as `toNat` arithmetic
(low-bit masks `a &&& 255` as `a % 256`, `rule_amt`). `rule_shamt` runs `congr 1` at reducible
transparency: at default transparency it unfolded `BitVec.ofInt 16 c &&& x` into a
maximum-recursion error, which `first` does not catch (runtime exceptions pass through it).

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
  `inst_r_generic_400` Not, `inst_r_generic_284` EqB, `inst_r_generic_290` NeqB).
- `lake exe rule-sat` (`GoFVTest/Proof/RuleSat.lean`; `scripts/rule-proofs.py sat`) searches
  an instance of every exported rule at run time (random leaves, auxints from boundary values,
  `[c]`/`<t>`/`same x` solved, oracle atoms all `true` or all `false`) and checks `Bool`
  mirrors of the hypotheses. `sat` fails if a proven rule has no instance or a
  counterexample. It also reports counterexamples among the pending rules (`CEX`), which are
  how the findings below were found. Last run (with `Pat.typed`: leaves typed by their
  values' shapes): P1 rules SAT 1332, CEX 9 (all `generic.rules:504–516`, "Narrow result
  types"), NONE 54; all 957 proven rules SAT.

`Comm.lean` has `sub16_not_comm` (the commutativity obligation is not trivial).

## Findings

- **#90 (`upstream-candidate`)**: constant rotate detection, `generic.rules:2166–2169` and
  their Or/Xor expansions (12 rules). The condition `c < w && d == w-c` compares the shift
  constant signed; for `c = -1`, `d = w+1` both shifts give 0 but `RotateLeft x (Const64 [-1])`
  rotates by `w-1`. Missing precondition `c >= 0`. Marked `-- FALSE … #90` in
  `GoFV/Proof/Rules/Add.lean`; `Rule.Sound` is false for them.

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
