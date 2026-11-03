# Rewrite rules as Lean data (`tools/rules2lean`, `GoFV/Rules`)

The machine-independent rewrite passes (`opt`, `middle opt`, `late opt`, `divisible`,
`divmod`, `decompose builtin`'s value rewrites) and the arm64 lowering passes (`lower`,
`late lower`, Phase 2) run rulegen-generated code over six rule files of the pinned compiler
(`docs/PINS.md`). gofv exports those rules as Lean data; an interpreter (issue #7) replays them.
This contract fixes the data format, the matching and construction semantics the interpreter
must reproduce exactly (parity, `docs/PLAN.md` §2), and the Go helpers and expression forms the
rules use.

| Rule file | Rewrite function | Used by (compile.go) | Dead values |
| --- | --- | --- | --- |
| `generic.rules` | `rewriteValuegeneric`, `rewriteBlockgeneric` | `opt`, `middle opt`, `late opt` (`opt.go: opt`) | `removeDeadValues` |
| `divisible.rules` | `rewriteValuedivisible` | `divisible` | `removeDeadValues` |
| `divmod.rules` | `rewriteValuedivmod` | `divmod` | `removeDeadValues` |
| `dec.rules` | `rewriteValuedec` | `decompose builtin` (`decomposeBuiltin`, after the phi decomposition) | `leaveDeadValues` |
| `ARM64.rules` | `rewriteValueARM64`, `rewriteBlockARM64` (`Config.lowerValue`/`lowerBlock`) | `lower` (`lower.go: lower`) | `removeDeadValues` |
| `ARM64latelower.rules` | `rewriteValueARM64latelower`, `rewriteBlockARM64latelower` (no block rules) | `late lower` (`lower.go: lateLower`) | `removeDeadValues` |

`dec64.rules` is not exported: `decompose builtin` and `softfloat` only run it when
`Config.RegSize == 4` or soft-float, never for linux/arm64. `simdARM64.rules`, which rulegen
appends to `ARM64.rules` (419 rewrite functions and dispatch cases of `rewriteARM64.go`), is
not exported either: every one of its rules starts at a SIMD op (a generic SIMD op of
`simdgenericOps.go` or an ARM64 op of `simdARM64ops.go`), which exist only under
`GOEXPERIMENT=simd` and are not in `GoFV.SSA.Op` (`tools/opsgen/nosimd.go`). The exporter
checks that every rule of the SIMD file starts at a SIMD op, that no other rule does, and that
no exported rule mentions a SIMD op anywhere.

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
`typeName`, `parseEllipsisRules`, `getBlockInfo`, and the op and block tables (`genericOps`,
`genericBlocks`, the `ARM64` arch). `third_party/go` is not modified (rulegen's own `main` is
never reached; should the overlay not apply it would write to `tmp/rules2lean/rulegen-out`). It
needs no network and takes about 5 s and 0.4 GB.

Three checks run on every export and abort it on a mismatch:

1. **Against the stock generated code.** For every rewrite function in the pinned
   `rewrite{generic,dec,divisible,divmod,ARM64,ARM64latelower}.go` and every `case Block…` of
   the block function, the sequence of `// match:`, `// cond:`, `// result:` comments equals
   the exported rules in order (1654 + 47 + 32 + 29 + 1319 + 82 rules). The dispatch switch of
   `rewriteValue<file>` has a case for exactly the exported ops: a call of the op's function,
   or `v.Op = Op…` for an ellipsis rule (171 in `ARM64.rules`), with the exported target op.
2. **Against rulegen's code generator.** Each rule is also passed through rulegen's real
   `genMatch`/`genResult` (`genBlockRewrite` for block rules). The sequence of declared Go
   variables (which decides bind vs. compare, and so each variable's type), the sequence of
   `b.NewValue0` ops and their position arguments (`v.Pos`, the faulting matched value's
   `x.Pos`, `b.Pos`, a control's `Pos`), and the position `genMatch` chose must equal the
   exporter's.
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
| `GoFV.Rules.Generated.<File>.Blocks` | `def r_<file>_<line> : BlockRule` and `def blocks_<Kind> : List BlockRule` (`Generic`, `ARM64`) |
| `GoFV.Rules.Generated.<File>` | `ruleSet : RuleSet` (`values : List (Op × List Rule)` in Go-name order, `blocks`), `counts : Nat × Nat` |
| `GoFV.Rules.Generated` | imports the six `<File>` modules |

`<File>` is `Generic`, `Dec`, `Divisible`, `Divmod`, `ARM64`, `ARM64latelower`; all in
namespace `GoFV.Rules.Generated.<File>`. Rule names: `r_<file>_<line>` with the line of
rulegen's `Loc` (the line where the rule's `=>` is found); rules expanded from one source rule
by `|` get `_2`, `_3`, ... in expansion order. Each def's doc comment is the normalised rule
text. Ops and block kinds are `GoFV.SSA.Op`/`BlockKind` constructors, i.e. the Go constant
without `Op`/`Block` (`.Add64`, `.ARM64MOVDload`, `.ARM64EQ`); `ops_<Op>`/`blocks_<Kind>` use the
same name.

Counts: generic 241 ops / 1651 value rules + 1 block kind (`If`) / 3 block rules; dec 17 / 47;
divisible 8 / 32; divmod 8 / 29; ARM64 506 ops / 1268 value rules (171 of them ellipsis rules)
and 26 block kinds / 222 block rules; ARM64latelower 22 / 82 (after `|` expansion). The
generated modules import only `GoFV.Rules.Syntax`, which imports only `GoFV.SSA.Op`.

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
checks), `pat`/`op`/table key agree, ellipsis targets have the source op's `argLen`, and block
rules match and build `BlockKind.controls` controls.

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
- A keyed struct literal `T{f1: e1, f2: e2}` (only `PanicBoundsC{C: c}` and
  `PanicBoundsCC{Cx: …, Cy: …}` in `ARM64.rules`) is the pseudo-call
  `call "T{f1,f2}" [e1, e2] T`: the struct with those fields, the others zero.

**Variables.** `Rule.vars : List Var`, `Var = ⟨name, kind, ty⟩`, numbered in rulegen's
declaration order. `kind`: `value` (`*Value`), `type` (a value's `Type`), `auxInt`
(`auxIntTo<T>(x.AuxInt)`), `aux` (`auxTo<T>(x.Aux)`); `ty` is the Go type of the binding.

**Patterns.** `Pat`: `wild` (`_`), `bind x`, `same x` (pointer identity with `x`), and
`op o name ty auxInt aux arity args commute`. `Field`: `any`, `bind x`, `eq e`. `Arity`:
`fixed` (op with fixed `argLength`: no check), `exact n` (variadic op: `len(Args) = n`),
`atLeast n` (trailing `___`: `len(Args) ≥ n`, `n` pattern arguments), `ellipsis`.

**Results.** `Result.copy e` (`v.copyOf(e)`: a variable, a `{code}` result or a bare Go
expression such as `x.Args[i]`, `rewriteStructStore(v)`); `Result.build nodes`; `Result.setOp o`
(ellipsis rule `(Op ...) => (Op2 ...)`; 171 in `ARM64.rules`, none in the four Phase 1 files).
`RNode = ⟨op, ty, auxInt, aux, args⟩`, `args : List RArg`: `var x`, `node j`, or `expr e`, a Go
expression of type `*Value` that rulegen passes through to `AddArg` (`flagArg(boolval)`, five
`CSEL`/`CSEL0` rules of `ARM64.rules`). `Rule.block = some e` is `@e`. `Rule.pos` is the pattern
path of the value whose `Pos` new values get (`[]` = `v`): rulegen uses the position of the
last matched op with `faultOnNilArg0/1` (preorder), so it is `[]` for every generic rule and
for the ARM64 rules whose top op faults; 20 ARM64 rules have a deeper one (`[1]` for
`(FMOVDload [off] {sym} ptr (MOVDstore [off] {sym} ptr val _))`, `[0, 0, 2, 2]` for the
`runtime.memmove` → `Move` rule).

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
0`, no args; appended to the end of `b.Values`. `pos` is the `Pos` of the value at `Rule.pos`
(`v.Pos` for every generic value rule).

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
- ARM64 aux types (rewrite.go): `ARM64BitField→arm64BitField` (`auxIntToArm64BitField` /
  `arm64BitFieldToAuxInt`: identity on the int64; `lsb()`/`width()` unpack it, built by
  `armBFAuxInt(lsb, width)`), `FlagConstant→flagConstant` (identity; its `eq`/`lt`/`ugt`/…
  methods read the N/Z/C/V bits), `CCop→Op` (`auxIntToOp(i) = Op(i)`, `opToAuxInt(o) =
  int64(o)`: the AuxInt holds **Go's opcode number** of the pinned opGen.go, which differs from
  `Op.ctorIdx`; convert with `Op.goNum` / `Op.ofGoNum?`), and on the aux side
  `PanicBoundsC`/`PanicBoundsCC` (`auxToPanicBoundsC(C)`, `panicBoundsC(C)ToAux`: the struct
  values `{C}` / `{Cx, Cy}` stored in `Aux`).

## The interpreter (`GoFV/Rules`, `GoFV/Opt/Opt.lean`)

| Module | Contents |
| --- | --- |
| `GoFV.Rules.GoVal` | `GVal` (runtime values of rule expressions) and Go integer/float semantics (wrapping, shifts, conversions, `math.RoundToEven`, bit counts) |
| `GoFV.Rules.Env` | `RwEnv` (pass name, `Config` values, `typs`, type order, frontend tables), `RwState` (function, tables, `pendingLines`), the monad `RwM` |
| `GoFV.Rules.Helpers.{Types,Sym,Ptr,Magic}` | pure ports of the `rewrite.go`/`magic.go` helpers (type queries, symbols and calls, pointer analyses, magic numbers) |
| `GoFV.Rules.Helpers.Build` | helpers that build values or objects: `rewriteStructStore`/`Load`, `imakeOfStructMake`, `devirtLECall`, `needRaceCleanup`, `clobber`, `resetCopy`, `t.PtrTo()`, `typeToAux`, symbols by name (`fe.StringData`, relocation targets: input tables, then `PassEnv.frontend`) |
| `GoFV.Rules.Eval` | `Eval.eval`: every `Expr` form, fields, methods, the helper calls by name |
| `GoFV.Rules.Interp` | matcher (depth-first over the pattern in preorder, commutative choice 0 before 1, checks of not-yet-bound variables postponed to the end), result construction, block rules; `Interp.Table` (rules indexed by `Op.ctorIdx`) |
| `GoFV.Rules.Apply` | `applyRewrite` (fixpoint loop, copy elimination, statement marks, final freeing) |
| `GoFV.Rules.Run` | `rewritePass t removeDead : GoFV.Opt.Pass` |
| `GoFV.Opt.Opt` | `opt` (= `middle opt`, `late opt`), `divisible`, `divmod` |

Deviation: Go detects rewrite cycles by hashing and aborts compilation on a repeat; the port
aborts after 100,000 iterations (no accepted function cycles). Parity: `docs/PARITY.md`.

## Helper inventory (scopes issue #7)

Counts are over the exported rules (after `|` expansion): *Uses* = expression occurrences,
*Rules* = rules containing it, then uses per file. Every helper here must be ported to Lean
(or modelled) for the interpreter to cover all rules; *expression roles* counts where
expressions occur (`cond`, `matchAuxInt`/`matchAux`/`matchType` = `eq` fields,
`resType`/`resAuxInt`/`resAux` = result node fields, `copy` = `Result.copy`, `block` = `@`).

<!-- BEGIN rules2lean inventory -->
<!-- Generated by tools/rules2lean; do not edit by hand. -->

#### Functions

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `shiftIsBounded` | `func(v *Value) bool` | 216 | 120 | 192 / 0 / 0 / 0 / 24 / 0 |
| `isPowerOfTwo` | `func[T int8 \| int16 \| int32 \| int64 \| uint8 \| uint16 \| uint32 \| uint64](n T) bool` | 118 | 118 | 24 / 0 / 16 / 4 / 74 / 0 |
| `isSamePtr` | `func(p1 *Value, p2 *Value) bool` | 116 | 72 | 116 / 0 / 0 / 0 / 0 / 0 |
| `is32Bit` | `func(n int64) bool` | 109 | 109 | 1 / 0 / 0 / 0 / 108 / 0 |
| `canRotate` | `func(c *Config, bits int64) bool` | 108 | 108 | 108 / 0 / 0 / 0 / 0 / 0 |
| `log64` | `func(n int64) int64` | 76 | 74 | 0 / 0 / 0 / 2 / 74 / 0 |
| `armBFAuxInt` | `func(lsb int64, width int64) arm64BitField` | 57 | 57 | 0 / 0 / 0 / 0 / 57 / 0 |
| `clobberIfDead` | `func(v *Value) bool` | 50 | 50 | 0 / 0 / 0 / 0 / 50 / 0 |
| `isSameCall` | `func(aux Aux, name string) bool` | 50 | 41 | 48 / 0 / 0 / 0 / 2 / 0 |
| `clobber` | `func(vv ...*Value) bool` | 41 | 39 | 31 / 0 / 0 / 0 / 10 / 0 |
| `rewriteCondSelectIntoMath` | `func(config *Config, op Op, constant int64) bool` | 40 | 32 | 40 / 0 / 0 / 0 / 0 / 0 |
| `registerizable` | `func(b *Block, typ *types.Type) bool` | 38 | 14 | 38 / 0 / 0 / 0 / 0 / 0 |
| `disjoint` | `func(p1 *Value, n1 int64, p2 *Value, n2 int64) bool` | 37 | 20 | 37 / 0 / 0 / 0 / 0 / 0 |
| `symIsRO` | `func(sym Sym) bool` | 27 | 27 | 20 / 0 / 0 / 0 / 7 / 0 |
| `oneBit` | `func[T int8 \| int16 \| int32 \| int64](x T) bool` | 24 | 24 | 16 / 0 / 0 / 0 / 8 / 0 |
| `canLoadUnaligned` | `func(c *Config) bool` | 22 | 22 | 22 / 0 / 0 / 0 / 0 / 0 |
| `canMergeSym` | `func(x Sym, y Sym) bool` | 21 | 21 | 0 / 0 / 0 / 0 / 21 / 0 |
| `mergeSym` | `func(x Sym, y Sym) Sym` | 21 | 21 | 0 / 0 / 0 / 0 / 21 / 0 |
| `uaddOvf` | `func(a int64, b int64) bool` | 20 | 20 | 20 / 0 / 0 / 0 / 0 / 0 |
| `isNonNegative` | `func(v *Value) bool` | 14 | 14 | 14 / 0 / 0 / 0 / 0 / 0 |
| `umagic32` | `func(c int32) umagicData` | 14 | 6 | 0 / 0 / 0 / 14 / 0 / 0 |
| `b2i` | `func(b bool) int64` | 13 | 13 | 0 / 0 / 0 / 0 / 13 / 0 |
| `read32` | `func(sym Sym, off int64, byteorder binary.ByteOrder) uint32` | 13 | 11 | 11 / 0 / 0 / 0 / 2 / 0 |
| `types.NewTuple` | `func(t1 *types.Type, t2 *types.Type) *types.Type` | 13 | 8 | 0 / 0 / 0 / 0 / 13 / 0 |
| `ccARM64Eval` | `func(op Op, flags *Value) int` | 12 | 12 | 0 / 0 / 0 / 0 / 12 / 0 |
| `smagic32` | `func(c int32) smagicData` | 12 | 5 | 0 / 0 / 0 / 12 / 0 / 0 |
| `flagArg` | `func(v *Value) *Value` | 11 | 6 | 0 / 0 / 0 / 0 / 11 / 0 |
| `ntz64` | `func(x int64) int` | 11 | 11 | 3 / 0 / 0 / 0 / 8 / 0 |
| `isInlinableMemmove` | `func(dst *Value, src *Value, sz int64, c *Config) bool` | 10 | 10 | 8 / 0 / 0 / 0 / 2 / 0 |
| `CanSSA` | `func(t *types.Type) bool` | 9 | 9 | 9 / 0 / 0 / 0 / 0 / 0 |
| `read16` | `func(sym Sym, off int64, byteorder binary.ByteOrder) uint16` | 9 | 9 | 7 / 0 / 0 / 0 / 2 / 0 |
| `read8` | `func(sym Sym, off int64) uint8` | 9 | 9 | 7 / 0 / 0 / 0 / 2 / 0 |
| `umagic16` | `func(c int16) umagicData` | 9 | 4 | 0 / 0 / 0 / 9 / 0 / 0 |
| `addToSub` | `func(op Op) Op` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `isFixedLoad` | `func(v *Value, sym Sym, off int64) bool` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `modularMultiplicativeInverse` | `func(x uint64) (y uint64)` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `rewriteFixedLoad` | `func(v *Value, sym Sym, sb *Value, off int64) *Value` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `rotateRight64` | `func(v int64, rotate int64) int64` | 8 | 8 | 0 / 0 / 0 / 0 / 8 / 0 |
| `sdivisible16` | `func(c int16) sdivisibleData` | 8 | 2 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisible32` | `func(c int32) sdivisibleData` | 8 | 2 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisible64` | `func(c int64) sdivisibleData` | 8 | 2 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisible8` | `func(c int8) sdivisibleData` | 8 | 2 | 0 / 0 / 8 / 0 / 0 / 0 |
| `smagic64` | `func(c int64) smagicData` | 8 | 3 | 0 / 0 / 0 / 8 / 0 / 0 |
| `subFlags64` | `func(x int64, y int64) flagConstant` | 8 | 8 | 0 / 0 / 0 / 0 / 8 / 0 |
| `arm64Negate` | `func(op Op) Op` | 7 | 7 | 0 / 0 / 0 / 0 / 7 / 0 |
| `isARM64addcon` | `func(v int64) bool` | 7 | 7 | 0 / 0 / 0 / 0 / 0 / 7 |
| `umagic64` | `func(c int64) umagicData` | 7 | 3 | 0 / 0 / 0 / 7 / 0 / 0 |
| `arm64BFWidth` | `func(mask int64, rshift int64) int64` | 6 | 6 | 0 / 0 / 0 / 0 / 6 / 0 |
| `arm64Invert` | `func(op Op) Op` | 6 | 6 | 0 / 0 / 0 / 0 / 6 / 0 |
| `isARM64BFMask` | `func(lsb int64, mask int64, rshift int64) bool` | 6 | 6 | 0 / 0 / 0 / 0 / 6 / 0 |
| `isConstZero` | `func(v *Value) bool` | 6 | 6 | 6 / 0 / 0 / 0 / 0 / 0 |
| `udivisible16` | `func(c int16) udivisibleData` | 6 | 2 | 0 / 0 / 6 / 0 / 0 / 0 |
| `udivisible32` | `func(c int32) udivisibleData` | 6 | 2 | 0 / 0 / 6 / 0 / 0 / 0 |
| `udivisible64` | `func(c int64) udivisibleData` | 6 | 2 | 0 / 0 / 6 / 0 / 0 / 0 |
| `udivisible8` | `func(c int8) udivisibleData` | 6 | 2 | 0 / 0 / 6 / 0 / 0 / 0 |
| `umagicOK32` | `func(c int32) bool` | 6 | 6 | 0 / 0 / 0 / 6 / 0 / 0 |
| `isARM64bitcon` | `func(x uint64) bool` | 5 | 5 | 0 / 0 / 0 / 0 / 0 / 5 |
| `isMalloc` | `func(aux Aux) bool` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `smagicOK32` | `func(c int32) bool` | 5 | 5 | 0 / 0 / 0 / 5 / 0 / 0 |
| `bitsMulU32` | `func(x int32, y int32) (r struct{hi int32; lo int32})` | 4 | 2 | 4 / 0 / 0 / 0 / 0 / 0 |
| `bitsMulU64` | `func(x int64, y int64) (r struct{hi int64; lo int64})` | 4 | 2 | 4 / 0 / 0 / 0 / 0 / 0 |
| `copyCompatibleType` | `func(t1 *types.Type, t2 *types.Type) bool` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `hasSmallRotate` | `func(c *Config) bool` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `is32BitInt` | `func(t *types.Type) bool` | 4 | 4 | 2 / 0 / 0 / 0 / 2 / 0 |
| `read64` | `func(sym Sym, off int64, byteorder binary.ByteOrder) uint64` | 4 | 4 | 3 / 0 / 0 / 0 / 1 / 0 |
| `smagic16` | `func(c int16) smagicData` | 4 | 2 | 0 / 0 / 0 / 4 / 0 / 0 |
| `umagicOK16` | `func(c int16) bool` | 4 | 4 | 0 / 0 / 0 / 4 / 0 / 0 |
| `is16BitInt` | `func(t *types.Type) bool` | 3 | 3 | 1 / 0 / 0 / 0 / 2 / 0 |
| `is32BitFloat` | `func(t *types.Type) bool` | 3 | 3 | 2 / 0 / 0 / 0 / 1 / 0 |
| `is64BitFloat` | `func(t *types.Type) bool` | 3 | 3 | 2 / 0 / 0 / 0 / 1 / 0 |
| `is64BitInt` | `func(t *types.Type) bool` | 3 | 3 | 2 / 0 / 0 / 0 / 1 / 0 |
| `is8BitInt` | `func(t *types.Type) bool` | 3 | 3 | 1 / 0 / 0 / 0 / 2 / 0 |
| `isVolatile` | `func(v *Value) bool` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `log16u` | `func(n uint16) int64` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `log32u` | `func(n uint32) int64` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `log64u` | `func(n uint64) int64` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `log8u` | `func(n uint8) int64` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `math.IsNaN` | `func(f float64) (is bool)` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `ntz16` | `func(x int16) int` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `ntz32` | `func(x int32) int` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `ntz8` | `func(x int8) int` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `sdivisibleOK16` | `func(c int16) bool` | 3 | 3 | 1 / 0 / 2 / 0 / 0 / 0 |
| `sdivisibleOK8` | `func(c int8) bool` | 3 | 3 | 1 / 0 / 2 / 0 / 0 / 0 |
| `smagicOK64` | `func(c int64) bool` | 3 | 3 | 0 / 0 / 0 / 3 / 0 / 0 |
| `udivisibleOK16` | `func(c int16) bool` | 3 | 3 | 1 / 0 / 2 / 0 / 0 / 0 |
| `udivisibleOK8` | `func(c int8) bool` | 3 | 3 | 1 / 0 / 2 / 0 / 0 / 0 |
| `umagicOK64` | `func(c int64) bool` | 3 | 3 | 0 / 0 / 0 / 3 / 0 / 0 |
| `warnRule` | `func(cond bool, v *Value, s string) bool` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `bits.Len16` | `func(x uint16) (n int)` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.Len32` | `func(x uint32) (n int)` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.Len64` | `func(x uint64) (n int)` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.Len8` | `func(x uint8) int` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.OnesCount16` | `func(x uint16) int` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.OnesCount32` | `func(x uint32) int` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.OnesCount64` | `func(x uint64) int` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bits.OnesCount8` | `func(x uint8) int` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `bitsAdd64` | `func(x int64, y int64, carry int64) (r struct{sum int64; carry int64})` | 2 | 1 | 2 / 0 / 0 / 0 / 0 / 0 |
| `canonLessThan` | `func(x *Value, y *Value) bool` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `imakeOfStructMake` | `func(v *Value) *Value` | 2 | 2 | 1 / 1 / 0 / 0 / 0 / 0 |
| `isInlinableMemclr` | `func(c *Config, sz int64) bool` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `isStackPtr` | `func(v *Value) bool` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `log16` | `func(n int16) int64` | 2 | 1 | 0 / 0 / 0 / 2 / 0 / 0 |
| `log32` | `func(n int32) int64` | 2 | 1 | 0 / 0 / 0 / 2 / 0 / 0 |
| `log8` | `func(n int8) int64` | 2 | 1 | 0 / 0 / 0 / 2 / 0 / 0 |
| `logLargeCopy` | `func(v *Value, s int64) bool` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `makeJumpTableSym` | `func(b *Block) *obj.LSym` | 2 | 1 | 0 / 0 / 0 / 0 / 2 / 0 |
| `math.Float32frombits` | `func(b uint32) float32` | 2 | 1 | 2 / 0 / 0 / 0 / 0 / 0 |
| `math.Float64frombits` | `func(b uint64) float64` | 2 | 1 | 2 / 0 / 0 / 0 / 0 / 0 |
| `math.Sqrt` | `func(x float64) float64` | 2 | 1 | 2 / 0 / 0 / 0 / 0 / 0 |
| `needRaceCleanup` | `func(sym *AuxCall, v *Value) bool` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `resetCopy` | `func(v *Value, arg *Value) bool` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `rewriteStructStore` | `func(v *Value) *Value` | 2 | 2 | 1 / 1 / 0 / 0 / 0 / 0 |
| `sdivisibleOK32` | `func(c int32) bool` | 2 | 2 | 0 / 0 / 2 / 0 / 0 / 0 |
| `sdivisibleOK64` | `func(c int64) bool` | 2 | 2 | 0 / 0 / 2 / 0 / 0 / 0 |
| `smagic8` | `func(c int8) smagicData` | 2 | 1 | 0 / 0 / 0 / 2 / 0 / 0 |
| `smagicOK16` | `func(c int16) bool` | 2 | 2 | 0 / 0 / 0 / 2 / 0 / 0 |
| `udivisibleOK32` | `func(c int32) bool` | 2 | 2 | 0 / 0 / 2 / 0 / 0 / 0 |
| `udivisibleOK64` | `func(c int64) bool` | 2 | 2 | 0 / 0 / 2 / 0 / 0 / 0 |
| `umagic8` | `func(c int8) umagicData` | 2 | 1 | 0 / 0 / 0 / 2 / 0 / 0 |
| `ZeroUpper32Bits` | `func(x *Value, depth int) bool` | 1 | 1 | 0 / 0 / 0 / 0 / 0 / 1 |
| `addFlags32` | `func(x int32, y int32) flagConstant` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `addFlags64` | `func(x int64, y int64) flagConstant` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `bool2int` | `func(x bool) int` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `canMulStrengthReduce` | `func(config *Config, x int64) bool` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `canMulStrengthReduce32` | `func(config *Config, x int32) bool` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `devirtLECall` | `func(v *Value, sym *obj.LSym) *Value` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `isDictArgSym` | `func(sym Sym) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `isDirectAndComparableIface` | `func(v *Value) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `isDirectAndComparableType` | `func(v *Value) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `isPtr` | `func(t *types.Type) bool` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `logicFlags32` | `func(x int32) flagConstant` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `logicFlags64` | `func(x int64) flagConstant` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `math.Ceil` | `func(x float64) float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `math.Float32bits` | `func(f float32) uint32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `math.Float64bits` | `func(f float64) uint64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `math.Floor` | `func(x float64) float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `math.RoundToEven` | `func(x float64) float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `math.Trunc` | `func(x float64) float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `mulStrengthReduce` | `func(m *Value, v *Value, x int64) *Value` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `mulStrengthReduce32` | `func(m *Value, v *Value, x int32) *Value` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `nlz16` | `func(x int16) int` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `nlz32` | `func(x int32) int` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `nlz64` | `func(x int64) int` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `nlz8` | `func(x int8) int` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `reciprocalExact32` | `func(c float32) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `reciprocalExact64` | `func(c float64) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `rewriteStructLoad` | `func(v *Value) *Value` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `smagicOK8` | `func(c int8) bool` | 1 | 1 | 0 / 0 / 0 / 1 / 0 / 0 |
| `subFlags32` | `func(x int32, y int32) flagConstant` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `symIsROZero` | `func(sym Sym) bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `umagicOK8` | `func(c int8) bool` | 1 | 1 | 0 / 0 / 0 / 1 / 0 / 0 |

#### Methods

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `*types.Type.Size` | `func() int64` | 245 | 103 | 209 / 12 / 0 / 0 / 24 / 0 |
| `*types.Type.Alignment` | `func() int64` | 92 | 14 | 92 / 0 / 0 / 0 / 0 / 0 |
| `arm64BitField.lsb` | `func() int64` | 44 | 20 | 0 / 0 / 0 / 0 / 44 / 0 |
| `arm64BitField.width` | `func() int64` | 36 | 28 | 0 / 0 / 0 / 0 / 36 / 0 |
| `*types.Type.IsPtrShaped` | `func() bool` | 20 | 20 | 0 / 4 / 0 / 0 / 16 / 0 |
| `*Func.useFMA` | `func(v *Value) bool` | 12 | 12 | 0 / 0 / 0 / 0 / 12 / 0 |
| `*types.Type.Elem` | `func() *types.Type` | 12 | 11 | 6 / 4 / 0 / 0 / 2 / 0 |
| `*types.Type.FieldType` | `func(i int) *types.Type` | 10 | 7 | 10 / 0 / 0 / 0 / 0 / 0 |
| `*types.Type.IsSigned` | `func() bool` | 10 | 10 | 0 / 0 / 0 / 4 / 6 / 0 |
| `*types.Type.PtrTo` | `func() *types.Type` | 8 | 8 | 3 / 5 / 0 / 0 / 0 / 0 |
| `*types.Type.IsComplex` | `func() bool` | 6 | 6 | 0 / 6 / 0 / 0 / 0 / 0 |
| `*types.Type.IsFloat` | `func() bool` | 4 | 4 | 0 / 0 / 0 / 0 / 4 / 0 |
| `*types.Type.IsSlice` | `func() bool` | 4 | 4 | 0 / 4 / 0 / 0 / 0 / 0 |
| `*types.Type.Compare` | `func(x *types.Type) types.Cmp` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `*types.Type.IsInterface` | `func() bool` | 3 | 3 | 0 / 3 / 0 / 0 / 0 / 0 |
| `*types.Type.IsString` | `func() bool` | 3 | 3 | 0 / 3 / 0 / 0 / 0 / 0 |
| `Frontend.Debug_checknil` | `func() bool` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `flagConstant.eq` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ge` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.geNoov` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.gt` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.le` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.lt` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ltNoov` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ne` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.uge` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ugt` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ule` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `flagConstant.ult` | `func() bool` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `*types.Type.FieldOff` | `func(i int) int64` | 2 | 2 | 1 / 1 / 0 / 0 / 0 / 0 |
| `*types.Type.HasPointers` | `func() bool` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `*types.Type.IsBoolean` | `func() bool` | 2 | 2 | 1 / 0 / 0 / 0 / 1 / 0 |
| `*types.Type.IsInteger` | `func() bool` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `Frontend.StringData` | `func(string) *obj.LSym` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `flagConstant.gtNoov` | `func() bool` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `flagConstant.leNoov` | `func() bool` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `*types.Type.IsArray` | `func() bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `*types.Type.IsPtr` | `func() bool` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `*types.Type.IsSIMD` | `func() bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `*types.Type.IsStruct` | `func() bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `*types.Type.NumElem` | `func() int64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |

#### Fields

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `*Value.Type` | `*types.Type` | 601 | 382 | 362 / 11 / 0 / 0 / 228 / 0 |
| `*Value.Uses` | `int32` | 359 | 315 | 126 / 0 / 16 / 0 / 216 / 1 |
| `*Value.Op` | `Op` | 217 | 168 | 136 / 2 / 32 / 0 / 47 / 0 |
| `*Types.UInt64` | `*types.Type` | 211 | 136 | 27 / 0 / 0 / 85 / 87 / 12 |
| `*Types.UInt32` | `*types.Type` | 98 | 49 | 16 / 0 / 0 / 37 / 45 / 0 |
| `*Types.Int64` | `*types.Type` | 71 | 32 | 52 / 0 / 0 / 2 / 17 / 0 |
| `*Config.ctxt` | `*obj.Link` | 68 | 64 | 21 / 0 / 0 / 0 / 47 / 0 |
| `*Types.Bool` | `*types.Type` | 62 | 57 | 59 / 0 / 0 / 0 / 3 / 0 |
| `*Types.Int32` | `*types.Type` | 58 | 27 | 39 / 0 / 0 / 3 / 16 / 0 |
| `*Config.PtrSize` | `int64` | 57 | 55 | 45 / 12 / 0 / 0 / 0 / 0 |
| `*obj.Link.Flag_dynlink` | `bool` | 42 | 42 | 0 / 0 / 0 / 0 / 42 / 0 |
| `*Value.AuxInt` | `int64` | 40 | 32 | 40 / 0 / 0 / 0 / 0 / 0 |
| `*Value.Block` | `*Block` | 40 | 40 | 15 / 13 / 0 / 0 / 12 / 0 |
| `*obj.Link.Arch` | `*obj.LinkArch` | 26 | 22 | 21 / 0 / 0 / 0 / 5 / 0 |
| `*obj.LinkArch.ByteOrder` | `binary.ByteOrder` | 26 | 22 | 21 / 0 / 0 / 0 / 5 / 0 |
| `*Types.Vec128` | `*types.Type` | 25 | 7 | 0 / 0 / 0 / 0 / 25 / 0 |
| `*Types.BytePtr` | `*types.Type` | 23 | 21 | 17 / 6 / 0 / 0 / 0 / 0 |
| `*Block.Func` | `*Func` | 22 | 22 | 8 / 0 / 0 / 0 / 14 / 0 |
| `*Types.Int` | `*types.Type` | 22 | 18 | 11 / 9 / 0 / 0 / 2 / 0 |
| `*Config.RegSize` | `int64` | 19 | 19 | 5 / 0 / 0 / 14 / 0 / 0 |
| `umagicData.m` | `uint64` | 18 | 14 | 0 / 0 / 0 / 18 / 0 / 0 |
| `*Types.Int8` | `*types.Type` | 17 | 12 | 17 / 0 / 0 / 0 / 0 / 0 |
| `*Types.Int16` | `*types.Type` | 16 | 11 | 16 / 0 / 0 / 0 / 0 / 0 |
| `*Types.Float64` | `*types.Type` | 15 | 7 | 0 / 6 / 0 / 0 / 9 / 0 |
| `*Types.Uintptr` | `*types.Type` | 15 | 12 | 9 / 3 / 0 / 0 / 3 / 0 |
| `smagicData.m` | `uint64` | 15 | 11 | 0 / 0 / 0 / 15 / 0 / 0 |
| `umagicData.s` | `int64` | 14 | 14 | 0 / 0 / 0 / 14 / 0 / 0 |
| `*Types.UInt16` | `*types.Type` | 12 | 9 | 2 / 0 / 0 / 0 / 10 / 0 |
| `smagicData.s` | `int64` | 11 | 11 | 0 / 0 / 0 / 11 / 0 / 0 |
| `*Types.IntPtr` | `*types.Type` | 9 | 7 | 0 / 9 / 0 / 0 / 0 / 0 |
| `*Func.pass` | `*pass` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `*pass.name` | `string` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `sdivisibleData.a` | `uint64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisibleData.k` | `int64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisibleData.m` | `uint64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `sdivisibleData.max` | `uint64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `udivisibleData.k` | `int64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `udivisibleData.m` | `uint64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `udivisibleData.max` | `uint64` | 8 | 8 | 0 / 0 / 8 / 0 / 0 / 0 |
| `*Types.UInt8` | `*types.Type` | 7 | 7 | 3 / 0 / 0 / 0 / 4 / 0 |
| `*Types.Float32` | `*types.Type` | 6 | 4 | 0 / 6 / 0 / 0 / 0 / 0 |
| `*Value.Aux` | `Aux` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `*Types.BytePtrPtr` | `*types.Type` | 3 | 3 | 0 / 3 / 0 / 0 / 0 / 0 |
| `*Types.Float32Ptr` | `*types.Type` | 3 | 3 | 0 / 3 / 0 / 0 / 0 / 0 |
| `*Types.Float64Ptr` | `*types.Type` | 3 | 3 | 0 / 3 / 0 / 0 / 0 / 0 |
| `*Value.Args` | `[]*Value` | 3 | 3 | 2 / 1 / 0 / 0 / 0 / 0 |
| `*Func.Entry` | `*Block` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `*Types.String` | `*types.Type` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `PanicBoundsC.C` | `int64` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `ir.symsStruct.Zerobase` | `*obj.LSym` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `struct{hi int32; lo int32}.hi` | `int32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `struct{hi int32; lo int32}.lo` | `int32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `struct{hi int64; lo int64}.hi` | `int64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `struct{hi int64; lo int64}.lo` | `int64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `struct{sum int64; carry int64}.carry` | `int64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `struct{sum int64; carry int64}.sum` | `int64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |

#### Package variables

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `types.TypeFlags` | `*types.Type` | 223 | 213 | 0 / 0 / 0 / 0 / 223 / 0 |
| `types.Types` | `[37]*types.Type` | 96 | 96 | 96 / 0 / 0 / 0 / 0 / 0 |
| `types.TypeMem` | `*types.Type` | 81 | 56 | 48 / 6 / 0 / 0 / 27 / 0 |
| `ir.Syms` | `ir.symsStruct` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |

#### Builtins

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `min` | 11 | 11 | 1 / 0 / 0 / 0 / 10 / 0 |
| `len` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |

#### Conversions

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `int64 -> uint64` | 201 | 112 | 104 / 0 / 0 / 0 / 93 / 4 |
| `int64 -> int32` | 154 | 146 | 6 / 0 / 4 / 0 / 144 / 0 |
| `int32 -> int64` | 90 | 62 | 11 / 0 / 0 / 0 / 74 / 5 |
| `uint64 -> int64` | 70 | 64 | 16 / 0 / 10 / 12 / 32 / 0 |
| `int32 -> uint32` | 69 | 41 | 63 / 0 / 0 / 0 / 6 / 0 |
| `int8 -> uint8` | 64 | 39 | 64 / 0 / 0 / 0 / 0 / 0 |
| `int16 -> uint16` | 63 | 38 | 63 / 0 / 0 / 0 / 0 / 0 |
| `int -> int64` | 30 | 30 | 22 / 0 / 0 / 0 / 8 / 0 |
| `uint32 -> int64` | 29 | 25 | 13 / 0 / 0 / 0 / 16 / 0 |
| `uint64 -> int32` | 23 | 17 | 0 / 0 / 10 / 13 / 0 / 0 |
| `int64 -> int64` | 21 | 13 | 8 / 0 / 4 / 8 / 1 / 0 |
| `int64 -> uint` | 19 | 18 | 10 / 0 / 0 / 0 / 9 / 0 |
| `int64 -> uint32` | 19 | 12 | 0 / 0 / 0 / 0 / 19 / 0 |
| `uint16 -> int64` | 15 | 15 | 13 / 0 / 0 / 0 / 2 / 0 |
| `uint8 -> int64` | 15 | 15 | 13 / 0 / 0 / 0 / 2 / 0 |
| `int -> int32` | 13 | 13 | 13 / 0 / 0 / 0 / 0 / 0 |
| `uint32 -> int32` | 13 | 13 | 12 / 0 / 0 / 0 / 1 / 0 |
| `uint16 -> int16` | 10 | 10 | 9 / 0 / 0 / 0 / 1 / 0 |
| `uint64 -> int16` | 10 | 4 | 0 / 0 / 10 / 0 / 0 / 0 |
| `uint64 -> int8` | 10 | 4 | 0 / 0 / 10 / 0 / 0 / 0 |
| `uint8 -> int8` | 10 | 10 | 9 / 0 / 0 / 0 / 1 / 0 |
| `uint32 -> uint64` | 8 | 6 | 8 / 0 / 0 / 0 / 0 / 0 |
| `int64 -> int16` | 6 | 6 | 1 / 0 / 4 / 0 / 1 / 0 |
| `int64 -> int8` | 6 | 6 | 1 / 0 / 4 / 0 / 1 / 0 |
| `int16 -> int64` | 5 | 5 | 2 / 0 / 0 / 0 / 3 / 0 |
| `int8 -> int64` | 5 | 5 | 2 / 0 / 0 / 0 / 3 / 0 |
| `int32 -> uint64` | 4 | 3 | 2 / 0 / 0 / 0 / 0 / 2 |
| `float32 -> float64` | 3 | 3 | 2 / 0 / 0 / 0 / 1 / 0 |
| `int16 -> int32` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `int8 -> int32` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `int16 -> uint64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `int64 -> int` | 2 | 2 | 1 / 1 / 0 / 0 / 0 / 0 |
| `int8 -> int16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `int8 -> uint64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint16 -> int32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint16 -> uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint16 -> uint64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint64 -> uint16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint64 -> uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint64 -> uint8` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint8 -> int32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint8 -> uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `uint8 -> uint64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `float32 -> int32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `float32 -> int64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `float64 -> float32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `float64 -> float64` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `float64 -> int32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `float64 -> int64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int16 -> int8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int32 -> float32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int32 -> float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int32 -> int16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int32 -> int8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int64 -> float32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int64 -> float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `int64 -> uint16` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `int64 -> uint8` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `uint8 -> int16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |

#### Type assertions

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `Sym.(*obj.LSym)` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |

#### Operators

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `&& bool` | 1249 | 751 | 862 / 7 / 48 / 30 / 302 / 0 |
| `== int32` | 432 | 388 | 151 / 0 / 16 / 2 / 262 / 1 |
| `== int64` | 275 | 223 | 188 / 10 / 0 / 15 / 62 / 0 |
| `- int64` | 271 | 196 | 119 / 0 / 20 / 18 / 114 / 0 |
| `+ int64` | 226 | 162 | 113 / 0 / 0 / 13 / 100 / 0 |
| `!= Op` | 172 | 131 | 96 / 2 / 32 / 0 / 42 / 0 |
| `\|\| bool` | 164 | 158 | 121 / 0 / 0 / 0 / 43 / 0 |
| `unary ! bool` | 151 | 151 | 48 / 0 / 0 / 0 / 91 / 12 |
| `< int64` | 147 | 115 | 92 / 0 / 0 / 0 / 55 / 0 |
| `>= int64` | 121 | 108 | 94 / 0 / 0 / 0 / 27 / 0 |
| `<= int64` | 97 | 61 | 68 / 0 / 0 / 0 / 29 / 0 |
| `index [37]*types.Type` | 96 | 96 | 96 / 0 / 0 / 0 / 0 / 0 |
| `/ int64` | 82 | 42 | 1 / 0 / 0 / 0 / 81 / 0 |
| `+ int32` | 72 | 56 | 29 / 0 / 0 / 0 / 43 / 0 |
| `% int64` | 43 | 43 | 2 / 0 / 0 / 0 / 41 / 0 |
| `& int64` | 41 | 39 | 21 / 0 / 0 / 1 / 19 / 0 |
| `<< int64` | 39 | 37 | 15 / 0 / 0 / 0 / 24 / 0 |
| `- int16` | 38 | 30 | 34 / 0 / 4 / 0 / 0 / 0 |
| `- int32` | 38 | 30 | 34 / 0 / 4 / 0 / 0 / 0 |
| `- int8` | 37 | 29 | 33 / 0 / 4 / 0 / 0 / 0 |
| `< int32` | 36 | 24 | 32 / 0 / 0 / 0 / 4 / 0 |
| `== Sym` | 34 | 34 | 7 / 0 / 0 / 0 / 27 / 0 |
| `unary - int64` | 33 | 30 | 20 / 0 / 0 / 0 / 13 / 0 |
| `>= uint64` | 32 | 24 | 32 / 0 / 0 / 0 / 0 / 0 |
| `< int16` | 30 | 18 | 30 / 0 / 0 / 0 / 0 / 0 |
| `unary ^ int64` | 30 | 30 | 4 / 0 / 0 / 0 / 26 / 0 |
| `!= int64` | 29 | 29 | 17 / 0 / 0 / 0 / 12 / 0 |
| `+ int16` | 29 | 13 | 29 / 0 / 0 / 0 / 0 / 0 |
| `+ int8` | 29 | 13 | 29 / 0 / 0 / 0 / 0 / 0 |
| `> int64` | 29 | 29 | 14 / 1 / 0 / 0 / 14 / 0 |
| `< int8` | 28 | 16 | 28 / 0 / 0 / 0 / 0 / 0 |
| `== int16` | 24 | 24 | 23 / 0 / 0 / 1 / 0 / 0 |
| `& int32` | 23 | 23 | 20 / 0 / 0 / 2 / 1 / 0 |
| `== uint64` | 23 | 17 | 2 / 0 / 0 / 6 / 15 / 0 |
| `== int8` | 22 | 22 | 22 / 0 / 0 / 0 / 0 / 0 |
| `>= int32` | 22 | 22 | 12 / 0 / 0 / 0 / 10 / 0 |
| `<< uint64` | 21 | 21 | 6 / 0 / 0 / 0 / 14 / 1 |
| `& int16` | 20 | 20 | 19 / 0 / 0 / 1 / 0 / 0 |
| `<< int32` | 20 | 20 | 8 / 0 / 0 / 0 / 12 / 0 |
| `& int8` | 18 | 18 | 18 / 0 / 0 / 0 / 0 / 0 |
| `* int64` | 16 | 16 | 4 / 4 / 0 / 0 / 8 / 0 |
| `>> uint64` | 16 | 16 | 2 / 0 / 0 / 0 / 14 / 0 |
| `!= int32` | 15 | 15 | 11 / 0 / 0 / 0 / 4 / 0 |
| `>> int64` | 15 | 15 | 1 / 0 / 0 / 0 / 14 / 0 |
| `+ uint64` | 14 | 10 | 0 / 0 / 0 / 14 / 0 / 0 |
| `unary - int32` | 14 | 13 | 12 / 0 / 0 / 0 / 2 / 0 |
| `/ uint64` | 12 | 12 | 1 / 0 / 0 / 10 / 1 / 0 |
| `unary - int16` | 12 | 11 | 12 / 0 / 0 / 0 / 0 / 0 |
| `unary - int8` | 12 | 11 | 12 / 0 / 0 / 0 / 0 / 0 |
| `& uint64` | 11 | 11 | 0 / 0 / 0 / 8 / 3 / 0 |
| `!= string` | 10 | 10 | 10 / 0 / 0 / 0 / 0 / 0 |
| `<= int32` | 10 | 8 | 10 / 0 / 0 / 0 / 0 / 0 |
| `== uint32` | 10 | 7 | 2 / 0 / 0 / 0 / 8 / 0 |
| `^ int64` | 10 | 8 | 8 / 0 / 0 / 0 / 2 / 0 |
| `>= int16` | 9 | 9 | 9 / 0 / 0 / 0 / 0 / 0 |
| `>= int8` | 9 | 9 | 9 / 0 / 0 / 0 / 0 / 0 |
| `!= int16` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `!= int8` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `- int` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `<< int16` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `>= uint16` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `>= uint32` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `>= uint8` | 8 | 8 | 8 / 0 / 0 / 0 / 0 / 0 |
| `^ int16` | 8 | 6 | 8 / 0 / 0 / 0 / 0 / 0 |
| `^ int32` | 8 | 6 | 8 / 0 / 0 / 0 / 0 / 0 |
| `^ int8` | 8 | 6 | 8 / 0 / 0 / 0 / 0 / 0 |
| `\| int64` | 8 | 8 | 5 / 0 / 0 / 0 / 3 / 0 |
| `!= Sym` | 7 | 7 | 7 / 0 / 0 / 0 / 0 / 0 |
| `<< int8` | 7 | 7 | 7 / 0 / 0 / 0 / 0 / 0 |
| `> int32` | 7 | 7 | 7 / 0 / 0 / 0 / 0 / 0 |
| `\| uint64` | 7 | 7 | 6 / 0 / 0 / 0 / 0 / 1 |
| `% uint64` | 6 | 6 | 3 / 0 / 0 / 0 / 3 / 0 |
| `< int` | 6 | 6 | 0 / 0 / 0 / 0 / 6 / 0 |
| `> int` | 6 | 6 | 0 / 0 / 0 / 0 / 6 / 0 |
| `!= *Value` | 5 | 5 | 0 / 0 / 0 / 0 / 5 / 0 |
| `<= int8` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `== float32` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `== float64` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `> int16` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `> int8` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `\| int16` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `\| int32` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `\| int8` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |
| `% uint32` | 4 | 4 | 3 / 0 / 0 / 0 / 1 / 0 |
| `/ float32` | 4 | 2 | 4 / 0 / 0 / 0 / 0 / 0 |
| `/ float64` | 4 | 2 | 4 / 0 / 0 / 0 / 0 / 0 |
| `<= int16` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `== Op` | 4 | 4 | 0 / 0 / 0 / 0 / 4 / 0 |
| `> uint16` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `> uint32` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `> uint64` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `> uint8` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `unary ^ int16` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `unary ^ int32` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `unary ^ int8` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `% int32` | 3 | 3 | 2 / 0 / 0 / 0 / 1 / 0 |
| `% uint16` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `% uint8` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `* float32` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `* float64` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `* int16` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `* int32` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `* int8` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `+ float32` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `+ float64` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `- float32` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `- float64` | 3 | 1 | 3 / 0 / 0 / 0 / 0 / 0 |
| `< float32` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `< float64` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `== arm64BitField` | 3 | 3 | 0 / 0 / 0 / 0 / 3 / 0 |
| `== types.Cmp` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |
| `index []*Value` | 3 | 3 | 2 / 1 / 0 / 0 / 0 / 0 |
| `!= float32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `!= float64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `!= uint64` | 2 | 2 | 0 / 0 / 0 / 2 / 0 / 0 |
| `% int16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `% int8` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `* uint16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `* uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `* uint64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `* uint8` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `/ int32` | 2 | 2 | 1 / 0 / 0 / 0 / 1 / 0 |
| `/ uint32` | 2 | 2 | 1 / 0 / 0 / 0 / 1 / 0 |
| `<< uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `<= uint64` | 2 | 2 | 1 / 0 / 0 / 0 / 1 / 0 |
| `== string` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `== uint16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `== uint8` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `>= float32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `>= float64` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `>> uint16` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `>> uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `>> uint8` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `\| uint32` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `!= bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `/ int16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `/ int8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `/ uint16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `/ uint8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `< uint16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `< uint32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `< uint64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `< uint8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `<= float32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `<= float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `<= uint16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `<= uint32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `<= uint8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `== *Value` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |
| `== bool` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `>> int16` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `>> int32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `>> int8` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `unary - float32` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |
| `unary - float64` | 1 | 1 | 1 / 0 / 0 / 0 / 0 / 0 |

#### Named constants

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `types.TUINT8` | `types.Kind` | 56 | 56 | 56 / 0 / 0 / 0 / 0 / 0 |
| `types.TUINT64` | `types.Kind` | 40 | 40 | 40 / 0 / 0 / 0 / 0 / 0 |
| `types.CMPeq` | `types.Cmp` | 3 | 3 | 3 / 0 / 0 / 0 / 0 / 0 |

#### Reserved names

| Name | Go type | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --- | --: | --: | --- |
| `typ` | `*Types` | 678 | 318 | 270 / 48 / 0 / 127 / 221 / 12 |
| `config` | `*Config` | 332 | 290 | 255 / 12 / 0 / 14 / 51 / 0 |
| `v` | `*Value` | 134 | 122 | 56 / 8 / 0 / 0 / 70 / 0 |
| `b` | `*Block` | 42 | 17 | 38 / 0 / 0 / 0 / 4 / 0 |
| `fe` | `Frontend` | 5 | 5 | 5 / 0 / 0 / 0 / 0 / 0 |

#### Aux conversions

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `auxIntToInt64` | 1858 | 1343 | 804 / 5 / 16 / 7 / 1014 / 12 |
| `int64ToAuxInt` | 1069 | 867 | 389 / 20 / 22 / 62 / 563 / 13 |
| `auxIntToInt32` | 563 | 463 | 324 / 0 / 16 / 12 / 208 / 3 |
| `int32ToAuxInt` | 410 | 354 | 191 / 0 / 22 / 13 / 184 / 0 |
| `auxIntToInt16` | 312 | 243 | 288 / 0 / 16 / 7 / 1 / 0 |
| `auxIntToInt8` | 307 | 238 | 287 / 0 / 16 / 3 / 1 / 0 |
| `boolToAuxInt` | 274 | 274 | 244 / 0 / 0 / 0 / 30 / 0 |
| `auxToSym` | 192 | 153 | 64 / 0 / 0 / 0 / 128 / 0 |
| `int8ToAuxInt` | 168 | 135 | 146 / 0 / 22 / 0 / 0 / 0 |
| `int16ToAuxInt` | 167 | 134 | 145 / 0 / 22 / 0 / 0 / 0 |
| `auxToType` | 166 | 70 | 155 / 4 / 0 / 0 / 7 / 0 |
| `typeToAux` | 100 | 50 | 88 / 12 / 0 / 0 / 0 / 0 |
| `auxIntToBool` | 97 | 95 | 63 / 0 / 0 / 0 / 34 / 0 |
| `symToAux` | 75 | 74 | 9 / 0 / 0 / 0 / 66 / 0 |
| `arm64BitFieldToAuxInt` | 58 | 58 | 0 / 0 / 0 / 0 / 58 / 0 |
| `auxIntToFloat64` | 47 | 39 | 42 / 0 / 0 / 0 / 5 / 0 |
| `auxToCall` | 47 | 44 | 45 / 0 / 0 / 0 / 2 / 0 |
| `auxIntToFlagConstant` | 40 | 40 | 0 / 0 / 0 / 0 / 40 / 0 |
| `auxIntToArm64BitField` | 37 | 37 | 0 / 0 / 0 / 0 / 37 / 0 |
| `auxIntToFloat32` | 34 | 26 | 33 / 0 / 0 / 0 / 1 / 0 |
| `auxIntToOp` | 32 | 32 | 0 / 0 / 0 / 0 / 32 / 0 |
| `opToAuxInt` | 30 | 30 | 0 / 0 / 0 / 0 / 30 / 0 |
| `float64ToAuxInt` | 18 | 18 | 16 / 0 / 0 / 0 / 2 / 0 |
| `flagConstantToAuxInt` | 13 | 13 | 0 / 0 / 0 / 0 / 13 / 0 |
| `float32ToAuxInt` | 11 | 11 | 11 / 0 / 0 / 0 / 0 / 0 |
| `auxToString` | 4 | 4 | 4 / 0 / 0 / 0 / 0 / 0 |
| `auxToPanicBoundsC` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `callToAux` | 2 | 2 | 2 / 0 / 0 / 0 / 0 / 0 |
| `panicBoundsCCToAux` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `panicBoundsCToAux` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `uint8ToAuxInt` | 1 | 1 | 0 / 0 / 0 / 0 / 1 / 0 |

#### Expression roles

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `resType` | 2359 | 1251 | 1236 / 50 / 144 / 184 / 733 / 12 |
| `resAuxInt` | 2219 | 1841 | 1142 / 20 / 88 / 75 / 881 / 13 |
| `cond` | 1654 | 1654 | 861 / 26 / 32 / 29 / 692 / 14 |
| `matchAuxInt` | 989 | 952 | 583 / 2 / 32 / 0 / 370 / 2 |
| `copy` | 248 | 248 | 173 / 19 / 0 / 0 / 41 / 15 |
| `resAux` | 181 | 126 | 99 / 12 / 0 / 0 / 70 / 0 |
| `matchType` | 75 | 57 | 60 / 0 / 0 / 0 / 15 / 0 |
| `block` | 22 | 22 | 7 / 13 / 0 / 0 / 2 / 0 |
| `matchAux` | 14 | 14 | 10 / 0 / 0 / 0 / 4 / 0 |
| `resArg` | 5 | 5 | 0 / 0 / 0 / 0 / 5 / 0 |

#### Composite literals

| Form | Uses | Rules | generic / dec / divisible / divmod / ARM64 / ARM64latelower |
| --- | --: | --: | --- |
| `PanicBoundsCC{Cx,Cy}` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |
| `PanicBoundsC{C}` | 2 | 2 | 0 / 0 / 0 / 0 / 2 / 0 |

#### Op constants in expressions

`OpARM64Equal`, `OpARM64LessThanU`, `OpARM64NotEqual`, `OpArrayMake1`, `OpConst16`, `OpConst32`, `OpConst64`, `OpConst8`, `OpSB`, `OpStructMake`

#### Used only by the arm64 rule files

Forms of the tables above with no use in `generic` / `dec` / `divisible` / `divmod`, i.e. what the
interpreter needs beyond Phase 1 for `ARM64` and `ARM64latelower`:

- Functions (30): `ZeroUpper32Bits`, `addFlags32`, `addFlags64`, `arm64BFWidth`, `arm64Invert`, `arm64Negate`, `armBFAuxInt`, `b2i`, `canMergeSym`, `canMulStrengthReduce`, `canMulStrengthReduce32`, `canonLessThan`, `ccARM64Eval`, `clobberIfDead`, `flagArg`, `isARM64BFMask`, `isARM64addcon`, `isARM64bitcon`, `isPtr`, `logLargeCopy`, `logicFlags32`, `logicFlags64`, `makeJumpTableSym`, `mergeSym`, `mulStrengthReduce`, `mulStrengthReduce32`, `rotateRight64`, `subFlags32`, `subFlags64`, `types.NewTuple`
- Methods (20): `*Func.useFMA`, `*types.Type.HasPointers`, `*types.Type.IsFloat`, `*types.Type.IsPtr`, `arm64BitField.lsb`, `arm64BitField.width`, `flagConstant.eq`, `flagConstant.ge`, `flagConstant.geNoov`, `flagConstant.gt`, `flagConstant.gtNoov`, `flagConstant.le`, `flagConstant.leNoov`, `flagConstant.lt`, `flagConstant.ltNoov`, `flagConstant.ne`, `flagConstant.uge`, `flagConstant.ugt`, `flagConstant.ule`, `flagConstant.ult`
- Fields (4): `*Func.Entry`, `*Types.Vec128`, `*obj.Link.Flag_dynlink`, `PanicBoundsC.C`
- Package variables (1): `types.TypeFlags`
- Conversions (4): `float64 -> float64`, `int64 -> uint16`, `int64 -> uint32`, `int64 -> uint8`
- Operators (6): `!= *Value`, `< int`, `== *Value`, `== Op`, `== arm64BitField`, `> int`
- Aux conversions (10): `arm64BitFieldToAuxInt`, `auxIntToArm64BitField`, `auxIntToFlagConstant`, `auxIntToOp`, `auxToPanicBoundsC`, `flagConstantToAuxInt`, `opToAuxInt`, `panicBoundsCCToAux`, `panicBoundsCToAux`, `uint8ToAuxInt`
- Composite literals (2): `PanicBoundsCC{Cx,Cy}`, `PanicBoundsC{C}`

<!-- END rules2lean inventory -->
