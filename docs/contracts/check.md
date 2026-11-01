# Contract: the well-formedness checker (`GoFV.SSA.check`)

Owner: Semantics (issue #8). Consumers: every pass proof (G6) takes `check env f = .ok ()` as
its precondition (PLAN.md §1: "for every well-formed `f`"); the semantics (`GoFV.SSA.run`, #10)
is stuck exactly where these facts fail.

## Interface

| Module | Content |
| --- | --- |
| `GoFV.SSA.Check` | `CheckEnv` (tables + `typs`), `check : CheckEnv → Func → Except String Unit` |
| `GoFV.SSA.Analysis.LoopNest` | port of `loopnestfor` (`likelyadjust.go`): `loopnest f po sdom`, `LoopNest.isWithinOrEq` |
| `GoFVTest.SSACheck` | `lake exe ssa-check [--mutate] <dir>...` over every section of the corpus |

`check { tabs, typs } f` is Go's `checkFunc(f)` including `memCheck`, in Go's order, returning
Go's first failure message (IDs as `v<n>`/`b<n>`). `tabs` are the tables in force for the
section (`ExportFile.tablesAt`), `typs` the `typs` line of section 0 (`SP`/`SB` must have the
`Uintptr` type, `StringLen` `Int`; `IsMemory` compares with `Mem`).

State assumed, as for every pass in scope (`lower` excluded): `f.RegAlloc == nil`,
`f.scheduled == false`, `f.pass != nil`, `Config.SoftFloat == false`. So the scheduled-only
checks (single live memory at every point, phis first, `NilCheck` void type) and the
regalloc/soft-float checks are skipped exactly as Go skips them.

Postorder, dominators and the sparse tree are recomputed from the CFG
(`GoFV.SSA.Analysis.{Postorder,Dom,SparseTree}`, ports of Go's), never read from `f.cache`,
which may be stale between passes; the loop nest likewise (`Analysis.LoopNest`).

Port notes:

- Go dereferences values and blocks through pointers; the Lean IR names them by ID, so the
  port also checks what Go's types guarantee: every ID in `f.Blocks`/`b.Values` has a table
  entry with that ID. An argument or control that is not in the function is reported by Go's
  "is missing" check (the earlier per-value checks skip its type).
- `isExactFloat32` is computed on the bits (trailing-zero test, then exponent range with
  float32 subnormals), equivalent to Go's `x == float64(float32(x))`.
- `IsMergeCandidate` uses `base.Debug.MergeLocals = 1`, `-N` off, `PtrSize = 8`.
- Aux kinds of the other architectures (`CCop`, `S390X*`) never occur on generic ops and are
  rejected as "unknown aux type".

## Corpus result

Regenerated corpus `gofv-corpus/2aae1000ea1d/plain` (9,297 files): every section of every file
passes — 306,801 sections, 2,961,638 blocks, 16,825,576 values, about 95 s. The self-test
(`--mutate`) corrupts every passing section in up to four ways (use count +1, an argument
outside the function, a broken reverse edge index, an entry-block use of a later block's
value) and requires each corruption to be rejected with the expected message: 806,559 mutants,
all rejected as expected. With the dominator certificate (`DomCert.check`) every section still
passes (306,801/306,801, 70 s CPU).

## Facts the pass proofs need

What a passing `check` gives, grouped by the proofs that use it. The proofs will state these as
lemmas `check env f = .ok () → P f` (a `WF f` structure), proved once against this module.

**IR integrity** (every pass; `Alloc`/`Edges` lemmas):
- `f.Blocks` lists distinct block IDs, each with a table entry carrying that ID; each value is
  listed in exactly one block, its table entry has that ID and `v.block` is that block.
- Edges are crosslinked: `b.succs[j] = ⟨c, i⟩ ↔ c.preds[i] = ⟨b, j⟩`; all ends are in the
  function; the entry is in the function and has no predecessors.
- Arguments and controls are values of the function; `freeValues`/`freeBlocks` contain no live
  ID (allocation from the free lists yields a fresh ID: needed by every pass that creates
  values or blocks).
- `v.uses` is the number of occurrences in arguments and controls (deadcode, copyelim,
  `resetArgs` bookkeeping).

**Shapes the semantics relies on** (so `run` is not stuck on well-formed input):
- Block kinds: `Plain` 1 successor, no control; `If` 2 successors, one `bool` control;
  `First` 2 successors, no control; `JumpTable` one control; `Ret`/`Exit`/`RetJmp` no
  successors, one memory control; `Defer` 2 successors, one memory control; a prediction only
  with 2 successors.
- Arity: every non-variadic op has exactly `Op.argLen` arguments; a `Phi` has one argument
  per predecessor (`enterBlock` reads argument `i` for incoming edge `i`); non-`Phi` memory
  arguments come last (`callExtern`, `PanicBounds`, `MakeResult` read the memory as the last
  argument).
- Aux: `Bool` auxints are 0/1 (the "bounded" / "not −1" flags of shifts and division),
  `Int8/16/32` auxints fit their width (constants of `Const8/16/32`), float auxints are not NaN
  and `Float32` ones are exact; `String`/`Call`/`NameOffsetInt8`/`SizeAndAlign` ops carry an
  aux of the right kind (`ArgIntReg`'s name resolution, call targets).
- Argument sizes: for `Add/Sub/Mul/Div/Mod/And/Or/Xor/Eq/Neq/Less/Leq/Neg/Com` of each width
  and the extensions/truncations, every argument's type has the op's size — so the integer
  families of `evalPure` see arguments of their width (no `poison` from a shape mismatch).
  Not checked by Go (and so not a fact): the unsigned comparisons, shifts, `Ctz`/`BitLen`/…,
  and the *result* type; rules do type results narrower than the op (`(Rsh64x64 <int32> …)`
  in `divmod.rules`), which the semantics reads as the low bits (`Val.retype`).
- `Addr` has an `SB` argument; `LocalAddr` has `SP` and a memory; `Load`/`Store`/`NilCheck`
  memory arguments are memories; `CondSelect`'s condition is `bool`; `AddPtr` is pointer +
  integer (P2).

**Dominance** (every value-moving pass: cse, phiopt, branchelim, tighten-like rewrites, fuse;
and the semantics' "a use reads its definition's latest activation", §3.6 of
`docs/plans/semantics.md`):
- Every argument's block dominates the using block, for a `Phi` argument `i` the block of
  predecessor `i`; every control's block dominates its block. Unreachable using blocks are
  exempt (Go's `domCheck`).
- Go's check trusts its Lengauer–Tarjan dominators; the proofs cannot. So `check` is Go's
  `checkFunc` (`checkGo`) followed by a **dominator certificate** (`GoFV.SSA.DomCert.check`,
  on the control-flow graph alone, `cfgView`): depths (entry 0, every other tree block one
  below its immediate dominator), every successor of a tree block is a non-entry tree block
  whose immediate dominator is an ancestor of the edge's source, every non-entry tree block has
  a tree predecessor it does not dominate, every use in a tree block is defined in an ancestor
  (`Phi` argument `i`: of predecessor `i`, if that is a tree block). It never rejects what Go
  accepts (corpus result above). It certifies soundness (ancestors lie on every path:
  `GoFV.Proof.Dom.use_dominated`), not that the tree is the complete dominator tree. The
  certificate's tree comes from its own textbook Lengauer–Tarjan (`DomCert.ltIdom`, buckets
  emptied; Go's verbatim `Analysis.dominators` rescans them and was 3× slower on big
  functions, #147); nothing about it is proven, the checks validate it.
- **Slim input check** (#147): a proof that needs only the IR-integrity facts above (without
  free lists and use counts), arity, `Phi` arity, `Bool` auxints and dominance (`WF`, the
  certificate `CertOK`, `UseDom`) can guard on `GoFV.SSA.wfDomCheck f` instead: `checkGo`'s
  structural loops (`wfCheck`, per value `WFCheck.valueOK`) and `DomCert.check`, no types/aux
  kinds/block kinds, Go dominator tree, loop nest, use counts, `memCheck` or argument shapes.
  `GoFV.Proof.wfDomCheck_wf`, `wfDomCheck_domCert`, `GoFV.Proof.Dom.WFDom.of_wfDomCheck`. Used
  by branchelim, early fuse and short circuit (`wfDomOK`); accepts every section `check`
  accepts (quick-v1 306,801, full-v2 3,185,523), 3.3 s vs 14.7 s (quick) and 85 s vs 369 s
  (full) for `check` (`lake exe check-bench`).

**Memory** (P2 proofs: dse, memcombine, writebarrier, nilcheckelim; the semantics' single
memory chain):
- No tuple has memory as its first component.
- Unless a memory value is copied or unused, or a non-entry block has no predecessors: each
  block has at most one live (not overwritten) memory value, and memory `Phi` arguments are the
  last memory of the corresponding predecessor (propagated through store-free blocks).

**Pointer-op argument shapes** (beyond Go's `checkFunc`, #69; rule proofs' `Pat.argTyped`):
`check` ends with `checkArgShapes`: by the shapes of the arguments' types (`Tables.ty`),
`PtrIndex` takes a pointer and a 64-bit integer; `OffPtr`, `IsNonNil`, `EqPtr`, `NeqPtr` take
pointer-sized words (a pointer or a 64-bit integer: `SP` after `expand calls` and itab words
after `decompose builtin` are `uintptr`); `AddPtr` a word and a 64-bit integer; `Convert`
converts a word to a pointer or 64-bit integer shape. `GoFV.Proof.check_argShapes`: every
listed value passes `argShapeOK`. Corpus: quick-v1 306,801/306,801 sections and full-v2
3,185,523/3,185,523 still pass (0 new rejections).

**Loops** (only `loopnestfor`'s own consistency; no pass in scope needs it as a fact): without
irreducible loops, an edge into a loop enters at its header. This is implied by dominance for
natural loops; Go checks it to validate `loopnestfor`, and so does the port.

**Not checked** (facts a proof must get elsewhere): acyclicity of non-`Phi` arguments within a
block (Go's "TODO: check for cycles in values"; `run` is stuck on a cycle via `schedule`),
argument types of ops outside the size table and the pointer ops above, reachability of
blocks.
