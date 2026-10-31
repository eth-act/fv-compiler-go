# Rewrite rules as Lean data (`tools/rules2lean`, `GoFV/Rules`)

The machine-independent rewrite passes (`opt`, `middle opt`, `late opt`, `divisible`,
`divmod`, `decompose builtin`'s value rewrites) run rulegen-generated code over four rule files
of the pinned compiler (`docs/PINS.md`). gofv exports those rules as Lean data; an interpreter
(issue #7) replays them. This contract fixes the data format, the matching and construction
semantics the interpreter must reproduce exactly (parity, `docs/PLAN.md` §2), and the Go
helpers and expression forms the rules use.

| Rule file | Rewrite function | Used by (compile.go) | Dead values |
| --- | --- | --- | --- |
| `generic.rules` | `rewriteValuegeneric`, `rewriteBlockgeneric` | `opt`, `middle opt`, `late opt` (`opt.go: opt`) | `removeDeadValues` |
| `divisible.rules` | `rewriteValuedivisible` | `divisible` | `removeDeadValues` |
| `divmod.rules` | `rewriteValuedivmod` | `divmod` | `removeDeadValues` |
| `dec.rules` | `rewriteValuedec` | `decompose builtin` (`decomposeBuiltin`, after the phi decomposition) | `leaveDeadValues` |

`dec64.rules` is not exported: `decompose builtin` and `softfloat` only run it when
`Config.RegSize == 4` or soft-float, never for linux/arm64.

## Regeneration

```sh
scripts/memcap.sh go run -C tools/rules2lean .     # GO=<go binary> to choose the toolchain
scripts/memcap.sh lake build GoFV.Rules.Generated GoFVTest.Rules.Data
```

`tools/rules2lean/main.go` runs `go run -overlay` in the pinned
`third_party/go/src/cmd/compile/internal/ssa/_gen` with `tools/rules2lean/export.go` added to
that package (as `zz_rules2lean.go`, build tag `rules2lean`). The exporter therefore runs
rulegen's own code unchanged: the rule-file reader (copied loop of `genRulesSuffix`),
`expandOr`, `Rule.parse`, `parseValue`/`extract`/`split`/`splitNameExpr`, `varCount`,
`typeName`, `parseEllipsisRules`, and the op and block tables (`genericOps`, `genericBlocks`).
`third_party/go` is not modified (rulegen's own `main` is never reached; should the overlay
not apply it would write to `tmp/rules2lean/rulegen-out`). It needs no network and takes about
10 s and 0.35 GB.

Three checks run on every export and abort it on a mismatch:

1. **Against the stock generated code.** For every rewrite function in the pinned
   `rewrite{generic,dec,divisible,divmod}.go` and every `case Block…` of the block function,
   the sequence of `// match:`, `// cond:`, `// result:` comments equals the exported rules in
   order (1654 + 47 + 32 + 29 rules).
2. **Against rulegen's code generator.** Each rule is also passed through rulegen's real
   `genMatch`/`genResult` (`genBlockRewrite` for block rules). The sequence of declared Go
   variables (which decides bind vs. compare, and so each variable's type) and the sequence of
   `b.NewValue0` ops must equal the exporter's.
3. **Type checking.** Every Go expression of every rule is type-checked by `go/types` inside a
   synthetic file added to the pinned `cmd/compile/internal/ssa` package (function bodies of
   the package are dropped; imports come from the pinned source tree, with
   `internal/buildcfg/zbootstrap.go` supplied in memory if the tree is unbuilt). Each statement
   reproduces the context the generated code uses (`auxIntToInt32(v.AuxInt) != (e)`,
   `int64ToAuxInt((e))`, `b.NewValue0(pos, op, (e))`, ...), so untyped constants get the type
   the generated code gives them. Any type error aborts.

The export is deterministic (two runs give identical files). It also rewrites the inventory
section at the end of this document.

## Generated modules

`GoFV/Rules/Syntax.lean` (datatypes, hand-written) and `GoFV/Rules/Generated/` (tool output,
never edit):

| Module | Contents |
| --- | --- |
| `GoFV.Rules.Generated.<File>.ValuesNN` | one `def r_<file>_<line> : Rule` per rule, and `def ops_<Op> : List Rule` per op in matching order; ops in Go-name order, about 120 rules per module, an op never split |
| `GoFV.Rules.Generated.Generic.Blocks` | `def r_generic_<line> : BlockRule` and `def blocks_<Kind> : List BlockRule` |
| `GoFV.Rules.Generated.<File>` | `ruleSet : RuleSet` (`values : List (Op × List Rule)` in Go-name order, `blocks`), `counts : Nat × Nat` |
| `GoFV.Rules.Generated` | imports the four `<File>` modules |

`<File>` is `Generic`, `Dec`, `Divisible`, `Divmod`; all in namespace
`GoFV.Rules.Generated.<File>`. Rule names: `r_<file>_<line>` with the line of rulegen's `Loc`
(the line where the rule's `=>` is found); rules expanded from one source rule by `|` get
`_2`, `_3`, ... in expansion order. Each def's doc comment is the normalised rule text.

Counts: generic 241 ops / 1651 value rules + 1 block kind (`If`) / 3 block rules; dec 17 / 47;
divisible 8 / 32; divmod 8 / 29 (after `|` expansion). The generated modules import only
`GoFV.Rules.Syntax`, which imports only `GoFV.SSA.Op`.

Build cost (`scripts/perf-record.py GoFV.Rules. GoFVTest.Rules.`, each module alone under
memcap, machine load ~65; RSS includes the ~0.45 GB of importing `GoFV.SSA.Op`):

| Module | Wall s | Max RSS MB | `.olean` KB |
| --- | --: | --: | --: |
| `GoFV.Rules.Syntax` | 2.5 | 530 | 2837 |
| `Generic.Values00` | 3.0 | 542 | 2408 |
| `Generic.Values01` | 2.6 | 533 | 1953 |
| `Generic.Values02` | 3.2 | 557 | 2661 |
| `Generic.Values03` | 2.7 | 553 | 2514 |
| `Generic.Values04` | 2.1 | 525 | 1725 |
| `Generic.Values05` | 4.9 | 556 | 3035 |
| `Generic.Values06` | 6.7 | 586 | 4533 |
| `Generic.Values07` | 4.3 | 541 | 2444 |
| `Generic.Values08` | 6.7 | 497 | 2122 |
| `Generic.Values09` | 7.7 | 542 | 2595 |
| `Generic.Values10` | 3.0 | 530 | 1716 |
| `Generic.Values11` | 3.4 | 536 | 1834 |
| `Generic.Values12` | 5.0 | 581 | 4360 |
| `Generic.Values13` | 3.1 | 539 | 2322 |
| `Generic.Values14` | 2.0 | 505 | 1413 |
| `Generic.Blocks` | 1.2 | 458 | 74 |
| `Generic` | 1.8 | 518 | 855 |
| `Dec.Values00` / `Dec` | 1.4 / 0.8 | 495 / 458 | 1086 / 74 |
| `Divisible.Values00` / `Divisible` | 2.2 / 0.8 | 513 / 442 | 1123 / 43 |
| `Divmod.Values00` / `Divmod` | 2.0 / 0.8 | 507 / 454 | 1373 / 43 |
| `GoFV.Rules.Generated` | 1.1 | 468 | 2 |
| `GoFVTest.Rules.Data` | 1.8 | 493 | 213 |

`GoFVTest/Rules/Data.lean` checks the counts (`rfl`) and, by `#guard`, that every rule is
well formed against the op table: variable and node indices in range, `commute` only on
commutative ops, pattern and result argument counts equal to `Op.argLen` (or the variadic
checks), and `pat`/`op`/table key agree.

## Data format (`GoFV/Rules/Syntax.lean`)

**Expressions.** Every Go expression is an `Expr` whose nodes carry their Go type
(`GoTy`: basic types as constructors, everything else `named "<go/types spelling relative to
package ssa>"`, e.g. `"*Value"`, `"*types.Type"`, `"Sym"`, `"[37]*types.Type"`).

- Constants are folded by `go/types`: `lit ty c` with `c : Lit` exact (`int` already converted
  to `ty`; floats as the IEEE bits of the value rounded to `ty`). A reference to a named
  constant of a named type is `cnst name ty c` (`types.TUINT64`, `types.CMPeq`), an `Op`
  constant is `op o`. Untyped constants remain only as constant shift counts (`.untypedInt`).
- `var i`: rule variable `i`; `rsv r`: `v`, `b`, `config`, `fe`, `typ` (see `Reserved`).
- `glob` package variable; `field` (auto-dereferencing); `call fn args` (package-level
  function, name qualified unless in package `ssa`: `isPowerOfTwo`, `math.IsNaN`,
  `bits.Len64`); `method x m args`; `builtin`; `conv ty x` (`T(x)`); `assert ty x` (`x.(T)`);
  `unop`; `binop` (`land`/`lor` short-circuit); `index`; `deref`.
- Generic helpers (`isPowerOfTwo[T]`, `oneBit[T]`) are called as `call`; the instantiation is
  the argument's type.

**Variables.** `Rule.vars : List Var`, `Var = ⟨name, kind, ty⟩`, numbered in rulegen's
declaration order. `kind`: `value` (`*Value`), `type` (a value's `Type`), `auxInt`
(`auxIntTo<T>(x.AuxInt)`), `aux` (`auxTo<T>(x.Aux)`); `ty` is the Go type of the binding.

**Patterns.** `Pat`: `wild` (`_`), `bind x`, `same x` (pointer identity with `x`), and
`op o name ty auxInt aux arity args commute`. `Field`: `any`, `bind x`, `eq e`. `Arity`:
`fixed` (op with fixed `argLength`: no check), `exact n` (variadic op: `len(Args) = n`),
`atLeast n` (trailing `___`: `len(Args) ≥ n`, `n` pattern arguments), `ellipsis`.

**Results.** `Result.copy e` (`v.copyOf(e)`: a variable, a `{code}` result or a bare Go
expression such as `x.Args[i]`, `rewriteStructStore(v)`); `Result.build nodes`; `Result.setOp o`
(ellipsis rule `(Op ...) => (Op2 ...)`; none exist in the four files). `RNode = ⟨op, ty, auxInt,
aux, args⟩`, `args : List RArg` (`var x` / `node j`). `Rule.block = some e` is `@e`.
`Rule.pos` is the pattern path of the value whose `Pos` new values get (`[]` = `v`; always
`[]` here because no generic op has `faultOnNilArg0/1`).

**Block rules.** `BlockRule = ⟨loc, kind, vars, controls : List Pat, auxInt, aux, cond,
newKind, newControls : List (NewControl × CtrlPos), newAuxInt, newAux, swapSuccs⟩`. A control
pattern is either an `op` pattern or `bind x` (a plain name binds the control value).

## Semantics the interpreter must replicate

The following is what the generated Go code does; `rewrite*.go` and `rulegen.go` are the
reference. "Value" means a `*Value`; equality of values and of `*types.Type` is pointer
identity.

### Dispatch

`rewriteValue<file>(v)`: if `v.Op` has rules, run that op's rules in list order and stop at the
first that fires (returns true); otherwise return false. An ellipsis rule only sets `v.Op`.
`rewriteBlock<file>(b)`: same over `b.Kind`'s block rules. A rule that cannot fail is always
last (rulegen enforces it).

### Matching a value rule

The match of `pat` against `v` succeeds for the first *assignment* of the commutative choices,
in the order below, under which every check holds; then `cond` is evaluated with those
bindings. If `cond` is false the next assignment is tried; when none is left, the rule fails
and the next rule is tried.

- **Commutative expansion.** Each `op` pattern node with `commute = true` has a choice bit:
  0 = pattern args 0,1 match value args 0,1; 1 = swapped. Choice bits are ordered by a preorder
  walk of the pattern (node before its arguments, arguments left to right), and assignments
  are enumerated lexicographically with 0 before 1, the first node most significant (nested
  `for` loops in the generated code; a failed check `continue`s the innermost loop). The
  pattern is static, so the number of bits is fixed per rule; a node's bit applies to whichever
  value that node is matched against under the earlier bits. `commute` is rulegen's decision,
  exported as is: true iff the op is commutative and neither (a) the two pattern arguments are
  textually equal nor (b) both are identifiers occurring exactly once in the match and the
  condition (`varCount`; block rules never apply (b)).
- **Checks of an `op` node `o` against value `w`.** `w.Op = o`; arity (`exact n`:
  `len(w.Args) = n`; `atLeast n` on a variadic op with `n ≥ 1`: `len(w.Args) ≥ n`); `ty`:
  `bind x` binds `w.Type`, `eq e` requires `w.Type == e` (pointer identity); `auxInt`:
  `bind`/`eq` on `auxIntTo<T>(w.AuxInt)` with `T` from the op's aux type (table below);
  `aux`: on `auxTo<T>(w.Aux)`; `name = some x` binds `w`; then each argument pattern against
  `w.Args[i]` (after the commutative swap): `wild` nothing, `bind x` binds, `same x` requires
  identity with `x`'s value. Arguments are the raw `Args`: copies are *not* looked through
  (applyRewrite has already removed copies from `v`'s own arguments, not deeper ones).
- **Order.** Bind vs. compare is decided by rulegen's declaration order, which the export
  already encodes (`bind` = first occurrence). All checks are pure, so the order in which an
  implementation performs them does not matter, except that an implementation must not
  evaluate an `eq` expression or `cond` before the variables it reads are bound.
- **`cond`** is evaluated once per complete assignment, after all pattern checks, in Go
  semantics (`&&`/`||` short-circuit). It may have side effects: `clobber(x, ...)` resets the
  given values to `OpInvalid` (always returns true; always the last conjuncts),
  `resetCopy(v, x)`, and `warnRule` (diagnostic only). Since side-effecting calls are last in
  a `&&` chain and return true, they only run when the rule fires.
- **Reserved names** in expressions: `v`; `b = v.Block`; `config = b.Func.Config`;
  `fe = b.Func.fe`; `typ = &config.Types`. `v.Block.Func.pass.name` is read by some
  conditions (`!= "opt"`), so the pass name is part of the interpreter's input.

### Building a value rule's result

Value creation is `b.NewValue0(pos, op, ty)` (`func.go: Func.newValue`): reuse the head of
`f.freeValues` (LIFO, ID kept) if non-empty, else a fresh ID `f.vid.get()`; `Op`, `Type`,
`Block = b`, `Pos = pos` (with the statement mark cleared if `notStmtBoundary(op)`), `AuxInt =
0`, no args; appended to the end of `b.Values`. `pos` is `v.Pos` for every generic value rule.

`Result.copy e`: evaluate `e` (this may itself build values: `rewriteStructStore`,
`rewriteFixedLoad`, `devirtLECall`, ...), then `v.copyOf(e)`: if `e` is `v` nothing happens;
else uncache `v`, `v.Op = OpCopy`, drop `v`'s args (decrementing their `Uses`), add `e` as
the only arg (incrementing its `Uses`), `AuxInt = 0`, `Aux = nil`, `v.Type = e.Type`.

`Result.build nodes` with `block = none` (in place). Statements in this exact order:

1. Node 0 (the top): `v.reset(op)` (uncache; `Op = op`; drop args, decrementing their `Uses`;
   `AuxInt = 0`; `Aux = nil`; the type is kept), then `v.Type = ty` if `ty = some _`.
2. Then, recursively for a node `n` (starting with node 0): set `n.AuxInt =
   <T>ToAuxInt(auxInt)`, then `n.Aux = <T>ToAux(aux)`, then for each argument in order: a
   variable is used as is; `node j` is either a node not built yet (it is then always the next
   node of the list) — create it with `b.NewValue0(pos, op_j, ty_j)` and process it
   recursively before continuing — or an already built node (shared: rulegen gives textually
   identical result subtrees one value). Then add all arguments (`AddArg…`, incrementing
   `Uses`).

So `nodes` is in allocation order: node 1, 2, ... receive their IDs in list order, after the
top was reset. Every `ty`/`auxInt`/`aux` expression is evaluated at that point, i.e. after
`v.reset`: an expression reading `v.AuxInt`/`v.Aux`/`v.Args` there sees the reset value (none
in the four files do; `v.Type` is unchanged unless the top has `<type>`).

`block = some e` (`@e` placement): evaluate `e` first; all nodes, including node 0, are
created by `NewValue0` in block `e`; right after creating node 0, `v.copyOf(node0)`; then node
0's aux fields and arguments as above.

### Block rules

Match: for each control `i`, its pattern against `b.Controls[i]` (an `op` pattern checks
`Controls[i].Op`; `bind x` binds the control), then the block's `auxInt`/`aux` fields
(`auxIntTo<T>(b.AuxInt)`), then `cond`. Commutative expansion as for values. Reserved names:
`b` (the block), `config`, `typ` only. Result, in order: build each new control in order
(`NewControl.build`: nodes created by `b.NewValue0(pos, ...)` in block `b`, node 0 is the
control, no sharing); `pos` is `CtrlPos.control i path` = the `Pos` of the value matched at
that path under control `i`, or `.block` = `b.Pos`. Then `b.Reset(newKind)` (no controls),
`b.resetWithControl(newKind, c0)` or `resetWithControl2(newKind, c0, c1)` (each sets `Kind`,
clears controls (decrementing `Uses`), `Aux = nil`, `AuxInt = 0`, adds the controls); then
`b.AuxInt`/`b.Aux` if given; then, if `swapSuccs`, `b.swapSuccessors()` (swap `Succs[0]` and
`Succs[1]`, fix the predecessors' back-indices, `b.Likely *= -1`).

### The fixpoint loop (`rewrite.go: applyRewrite`)

```
itersLimit = max(f.NumBlocks(), 20); iters = 0
repeat:
  change = deadChange = false
  for b in f.Blocks:
    for each control i of b: while c.Op == OpCopy: c = c.Args[0]; b.ReplaceControl(i, c)
    if rewriteBlock(b): change = true
    for (j, v) in b.Values   -- the slice as it was when this block's loop started
      if v.Uses == 0 && v.removeable():          -- not Void, not nilCheck, not Mem, no side effects
        if v.Op != OpInvalid && deadcode == removeDeadValues: v.reset(OpInvalid); deadChange = true
        continue
      vchange = phielimValue(v)
      for each arg i of v with a.Op == OpCopy:
        v.SetArg(i, copySource(a)); vchange = true; (statement-mark moves, below)
        while a.Uses == 0: next = a.Args[0]; a.reset(OpInvalid); a = next
      if rewriteValue(v): vchange = true; (statement-mark move via nextGoodStatementIndex)
      change = change || vchange
  if !change && !deadChange: break
  iters++; if iters > itersLimit && change: cycle detection (f.rewriteHash), fatal on a repeat
for b in f.Blocks: remove every OpInvalid value from b.Values in order, f.freeValue(v) each
  (pushes onto f.freeValues: the last value freed is the first reused), and settle pending
  statement marks
```

Values created during a sweep over a block are appended to `b.Values` but not visited in that
sweep. Statement marks (`Pos.IsStmt`) are moved by the copy elimination, after a successful
rewrite, and in the final cleanup (`pendingLines`); parity on positions requires replicating
that code too. `decompose builtin` passes `leaveDeadValues` (no dead-value resets in the loop;
`OpInvalid` values made by `copySource`/`clobber` are still freed at the end).

### Go expression semantics

- Integer arithmetic wraps at the node type's width; `/` and `%` truncate toward zero
  (division by zero would panic; the rules guard it); shifts by ≥ width give 0 (or all sign
  bits for signed `>>`); `int`/`uint` are 64-bit.
- Conversions between integer types truncate/extend; float↔int and float32↔float64 follow
  Go (`float32(x)` rounds to nearest even). Float arithmetic is IEEE in the node's type
  (`float32` results rounded to float32).
- `auxIntTo<T>`/`<T>ToAuxInt` (rewrite.go): `Bool`: `≠ 0` / `1|0`; `Int8/16/32`: truncate /
  sign-extend; `Int64`: identity; `UInt8`: `uint8(i)` / `int64(int8(i))`; `Float32`:
  `float32(math.Float64frombits(uint64(i)))` / `int64(math.Float64bits(float64(f)))`;
  `Float64`: bits. Aux: `auxToSym`, `auxToType`, `auxToCall`, `auxToString` (type assertions
  on the `Aux` interface) and `symToAux`, `typeToAux`, `callToAux`. The conversion for a field
  is the op's aux type's (`Op.auxType`): `Bool→bool`, `Int8..Int64`, `UInt8`, `Float32`,
  `Float64`, `SymOff/CallOff→int32`, `TypSize→int64`; aux side `String→string`,
  `Sym/SymOff/SymValAndOff→Sym`, `Call/CallOff→*AuxCall`, `Typ/TypSize→*types.Type`.

## Helper inventory (scopes issue #7)

Counts are over the exported rules (after `|` expansion): *Uses* = expression occurrences,
*Rules* = rules containing it, then uses per file. Every helper here must be ported to Lean
(or modelled) for the interpreter to cover all rules; *expression roles* counts where
expressions occur (`cond`, `matchAuxInt`/`matchAux`/`matchType` = `eq` fields,
`resType`/`resAuxInt`/`resAux` = result node fields, `copy` = `Result.copy`, `block` = `@`).

<!-- BEGIN rules2lean inventory -->
<!-- END rules2lean inventory -->
