# Plan: semantics of generic Go SSA (`GoFV.SSA.run`, issue #9)

Status: plan (G5); phases P1–P4 implemented (§9.1–§9.4). Implementation and native difftest: #10. Pass survey: `docs/PASSES.md`.
Source of truth for the ops: `third_party/go/src/cmd/compile/internal/ssa/_gen/genericOps.go`
(go1.27.3; "gO line" below) and the rules `_gen/{generic,dec,divisible,divmod}.rules`.
`decOps.go`, `divisibleOps.go` and `divmodOps.go` define **no** ops (they only name rule sets),
so the generic op set is the 446 entries of `genericOps` (412 without the SIMD tail, which only
`GOEXPERIMENT=simd` on amd64 produces; `simdgenericOps.go` adds 1567 more, out of scope).

## 1. Goal and correctness criterion

`GoFV.SSA.run` is an executable, fuel-bounded semantics of one `GoFV.SSA.Func` in **every
form the in-scope passes produce**: from `ssagen`'s output (section 0 of the export) to the
input of `lower` (after `expand calls`, `decompose builtin`, `writebarrier`). Because the
export gives the SSA after every pass, `run` can be checked on every section, not only the
first and last.

Criterion (PLAN.md §1, clifv's mid-end criterion): a pass `p` is correct when for every
well-formed `f` (port of `check.go`, #8), every environment `env`, arguments `args`, initial
memory `m`: if `run env (p f) args m fuel` is `returned r m'` or `panicked e m'`, then
`run env f args m fuel'` is the same outcome for some `fuel'` — up to the refinement order of
§3.5 (a source `poison` is refined by anything). Source runs that are `stuck` or `outOfFuel`
carry no obligation. This is the shape clifv proves (`Opt.runLoop_refines`,
`docs/contracts/midend.md`): backward from target outcomes; we prove it by forward simulation
plus determinism of `run` (§3.6 makes `run` deterministic).

## 2. Module shape (mirrors clifv's `FV/Clif`)

| Module | Content | clifv analogue |
| --- | --- | --- |
| `GoFV/SSA/Sem/Val.lean` | `Width`, `Val`, `Ptr`, refinement `Val.Refines` | `Clif.Val` (`Syntax.lean`) |
| `GoFV/SSA/Sem/Mem.lean` | allocations, bytes with pointer fragments, concrete addresses, encode/decode by shape, load/read/write | `Clif/Mem.lean` |
| `GoFV/SSA/Sem/Ptr.lean` | pointer arithmetic and comparison, composites, `Load`/`Dereference`, `MemEq`, atomic loads | `Clif/Sem.lean` |
| `GoFV/SSA/Sem/Image.lean` | the global image of an export file (read-only data with relocations, string data, zeroed variables) | `Clif.Program.initMem` |
| `GoFV/SSA/Sem/Int.lean`, `Shift.lean`, `Cmp.lean`, `Conv.lean` | per-op integer semantics on `BitVec w`, separately unfoldable | `Clif/Sem.lean` |
| `GoFV/SSA/Sem/Float.lean` | IEEE ops on bit patterns (port of clifv `FV/Float` + `Clif/FSem.lean`) | `Clif/FSem.lean` |
| `GoFV/SSA/Sem/Layout.lean` | Go type layout from the exported `type` table: size, field offsets, pointer words, ABI pieces | — |
| `GoFV/SSA/Sem/Pure.lean` | `evalPure : Op → Type → AuxInt → Aux → List Val → Val` (total) | `Clif.evalInst` |
| `GoFV/SSA/Sem/Env.lean` | callee contracts, runtime contracts, global image | `Clif.Env`, `Clif/Rust.lean` |
| `GoFV/SSA/Sem/Run.lean` | frames, block step, calls, `Outcome`, `runLoop`, `run` | `Clif/Run.lean` |

Rules (#7) get their lemmas against `evalPure` (one module per op family, as clifv's
`FV/Opt/Proof/Rule*`). Keep `evalPure` a `match` on the op with one definition per family so
a rule lemma unfolds only its own family (LEARNINGS: small modules, no umbrella imports).

## 3. Values, pointers, memory

### 3.1 Types

`run` needs the Go types of the export (`docs/contracts/export.md`, `type` lines): kind, size,
alignment, fields with offsets, element type/length, `PtrDataSize`, and the SSA pseudo-types
(`mem`, `flags`, `void`, tuples, `RESULTS`). `Layout.lean` derives from them: the scalar
pieces of a type (for `Load`/`Store` of composites and for ABI assignment), and which words
are pointers. Sizes are exported, never recomputed (the exporter writes `?` for sizes Go never
calculated; `run` is `stuck` on those).

### 3.2 Value domain

```lean
inductive Width | w8 | w16 | w32 | w64            -- Width.bits : Nat
inductive Val
  | int   (w : Width) (x : BitVec w.bits)         -- all integer kinds; uintptr = int w64
  | bool  (b : Bool)
  | f32   (x : BitVec 32) | f64 (x : BitVec 64)   -- IEEE bit patterns (NaN payloads exact)
  | ptr   (p : Ptr)                               -- *T, unsafe.Pointer, map/chan/func words
  | mem   (m : Mem)                               -- a memory *snapshot* (3.4)
  | tuple (vs : List Val)                         -- TUPLE and RESULTS types
  | agg   (vs : List Val)                         -- struct, [1]T, string (ptr,len),
                                                  -- slice (ptr,len,cap), iface (tab,data),
                                                  -- complex (re,im); shape from the SSA type
  | blob  (bs : List Byte)                        -- Dereference: a non-SSA-able value
  | empty                                         -- zero-sized types (OpEmpty)
  | poison                                        -- 3.5
```

A value's meaning is fixed by its exported **type**, not only by its op: well-formed SSA does
type integer results narrower than their op — `divmod.rules` builds `(Rsh64x64 <t> …)` and
`(Rsh32x64 <t> …)` with `t` = `int32`/`int16` (found by the P1 difftest: `divconst` at section
`divmod`; 990 such values in the corpus, all `Rsh64x64`/`Rsh32x64`, none wider than the op).
So every produced integer is retyped to its value's width (`Val.retype`, `Sem/Layout.lean`):
a narrower type keeps the low bits; a wider one would expose undefined high bits and is
`poison`. `retype` is **total-shaping** (#108): every value that does not fit the shape is
`poison` (a non-boolean at `bool`, a boolean or memory at an integer shape, a 32-bit integer at a
pointer shape, …), composites are retyped componentwise, so `(v.retype t).hasTy t` always holds
(`Val.retype_hasTy`, `GoFV/Proof/Retype.lean`) and every register has its value's shape
(`GoFV.Proof.evalValue_hasTy`, `Typed.hasTy`). Well-typed producers yield values of their shape
anyway: total shaping left every difftest outcome unchanged (native 11,900 calls; corpus 39,131
defined calls, same counts). Other shape mismatches give `poison` inside `evalPure` (pure ops
never fail). Two mixes Go relies on are kept. A pointer without a concrete address (a global: a
closure's code pointer loaded as `uintptr`, `unsafe.Pointer` ↔ `uintptr` of a global) stays a
pointer at the 64-bit integer shape, which `Val.hasTy` accepts. And a 64-bit integer **keeps
its word at a pointer shape** (`Val.retype (.ptr _) (.int .w64 a) = .int .w64 a`,
`Val.hasTy (.int .w64 _) (.ptr _)`; #10): the word is the pointer at its address (§3.3), so a
`uintptr` itab word that `decompose builtin` passes on as `*itab` (`dec.rules:82`) is the same
value on both sides.
**Strings and slices** have their own shapes, `Ty.str` (pointer, length) and `Ty.slice e`
(pointer, length, capacity), with the layout of the aggregate they used to be (`Ty.asAgg`:
offsets 0/8/16, sizes 16/24; `Sem/Layout.lean` maps `STRING`/`SLICE` to them). Their values
have valid lengths: `0 ≤ len` for a string, `0 ≤ len ≤ cap` for a slice, as signed `int`s
(`Val.strOK`, `Val.sliceOK`). The invariant holds wherever a value takes the shape, not only at
`StringMake`/`SliceMake`: `decode` (loads, arguments, results), `Val.retype` (every op result,
phi, contract result) and `Val.hasTy` give `poison` (resp. `false`) for a length that is
negative, above the capacity or not a concrete integer, and `ConstString` is checked too. So
`StringLen`, `SliceLen` and `SliceCap` of a register are nonnegative or `poison`
(`Val.hasTy_str`, `Val.hasTy_slice`, `GoFV/Proof/Retype.lean`), which `isNonNegative` relies on.
Encoding, decoding and retyping at `t` are those at `t.asAgg` followed by the length check
`Val.checkLen t` (`decode_asAgg`, `retype_asAgg`, `load_asAgg`, `encode_asAgg`,
`GoFV/Proof/ValRefine.lean`), which only adds `poison`, so proofs and checkers treat strings and
slices as aggregates. The contracts already produce valid strings and slices (`makeslice`,
`growslice` check their lengths).
Integer ops have no sign: signedness is in the op
(`Less64` vs `Less64U`, `Rsh64x64` vs `Rsh64Ux64`, `SignExt` vs `ZeroExt`), as in Go.
`ConstN` auxints are sign-extended to 64 bits even for unsigned types (gO 339); `run` takes
the low `N` bits. `bool` is separate from `int w8` because Go SSA keeps `Bool` distinct
(`CvtBoolToUint8` converts).

### 3.3 Pointers and provenance

`structure Ptr where alloc : Nat; off : BitVec 64` with `alloc = 0` the nil pointer
(offset 0) — a CompCert-style block/offset pointer. Every allocation also has a concrete base
address (`Alloc.base`, bump-allocated as in clifv's `Mem.alloc`, never reused), used only
where Go exposes addresses:

- `Convert` ptr→uintptr gives `base + off` (`Ptr.addr?`); uintptr→ptr is the identity: the
  integer keeps its word at the pointer shape (§3.2);
- every op that reads a pointer reads a **pointer word** through `Val.asPtrWord`: a pointer
  is itself, a 64-bit integer `a` is `Ptr.ofAddr a` (the heap or frame block whose encoding
  contains the address, else `Blk.nil`). That covers `Load`/`Store`/`Move`/`Zero` (and their
  `WB` forms), `NilCheck`, atomics, `MemEq`, `SubPtr`, `EqPtr`/`NeqPtr`, the runtime contracts
  that take pointers (`Runtime.asPtr`) and the SemDiff renderer. `decodePtr` of 8 concrete bytes
  gives the integer they hold, so a word loads back as it was stored;
- `EqPtr`/`NeqPtr` compare concrete addresses, so `&a[len(a)] == &b[0]` behaves as on the
  machine;
- `SubPtr` (unused by the frontend today) is the difference of concrete addresses.

`AddPtr`, `OffPtr`, `PtrIndex` keep the allocation and add to `off` mod 2^64; a result whose
offset leaves its block's **address window** (`Blk.window?`: `nil` and heap blocks `2^40`, frame
blocks `2^24`; globals unbounded) is `poison` (#156). Every allocation is smaller than its
window, so in-bounds and one-past-the-end pointers are unaffected; Go's unsafe rules make
anything else invalid. On an integer word `x` they add as integers under the window rule of the
pointer at that address (`PtrOps.wordRes`: `x + k` if `(Ptr.ofAddr x).add k` is in its window,
else `poison`), so the word behaves exactly like that pointer (`Ptr.ofAddr_add_of_inWindow`,
`PtrOps.offPtr_asPtrWord`/`addPtr_asPtrWord`/`ptrIndex_asPtrWord`, `GoFV/Proof/PtrAddr.lean`).
Without the window rule a non-nil word could step into the nil window, where the source's
`NilCheck` panics but a target with the check removed does not. `EqPtr`/`NeqPtr` compare block
and offset (pointers into different allocations are never equal; `Ptr.eq_iff`), so
`EqPtr (ConstNil) p` is `!IsNonNil p`.
`Convert` ptr→uintptr is `poison` unless the pointer is `Ptr.convertible` (inside its window,
its block number small enough for the address encoding, not a frame temporary or global);
then `Ptr.ofAddr` of its address is the pointer again (`Ptr.ofAddr_addr`,
`GoFV/Proof/PtrAddr.lean`), so the integer `Convert (Convert p)` reads as `p` wherever a
pointer is read (`convert_asPtrWord`). It is not `p` itself, and the two are not related by
`Sem.Refines`: `generic.rules:1072` (`Convert (Convert p)` → `p`) is no longer in the proven
rule set (#290 tracks refinement modulo pointer-word equivalence, which would restore it).
The checkers that compare pointers structurally require pointer-typed values, since an
integer-shaped retype of a non-`convertible` pointer reads back as a different pointer:
`RewriteCheck.baseBlk?` (`LocalAddr`/`Addr`), `baseSameB`'s `AddPtr`/`PtrIndex` arm and the
`OffPtr`s of `segTiles`. Go types these values as pointers anyway.
Consequence: `generic.rules:1071/1075` (`Convert (Add (Convert p) off)` → `AddPtr p off`) do
not refine when `off` leaves the allocation — the source's integer arithmetic lands, through
`Ptr.ofAddr`, in some other block, while the target's `AddPtr` is `poison`. Go makes that case
undefined (unsafe rule 3), but the model's integers carry no provenance, so the source cannot
be undefined there; these two rules stay outside the proven rule set. The corpus difftest
shows exactly this: 9 runtime helpers called with random offsets (`add`, `addb`,
`subtract1`, `(*gcBits).bitp/bytep`, `stackmapdata`, …) are `stuck` from `opt` on (2,600
section runs), while section 0 returns a pointer into another block. Why
provenance: `dse`, `dead auto elim`, `memcombine` and `writebarrier` (`IsStackAddr`,
`IsGlobalAddr`, `IsNewObject`, `disjoint`) reason "different autos/globals/new objects do not
alias"; with flat addresses an out-of-bounds offset could land in another object and those
passes would be unsound. With provenance, an access must lie inside its own allocation.

**Frame temporaries** (#31): a `PAUTO` whose address the function does not convert to an
integer (`Tables.forgeable`: the exporter's `addrconv` flag, export format 3; parameters and
results always forgeable) lives in `Blk.temp act name` instead of `Blk.local act name`. The flag
is computed once from the `start` section: the variable's `LocalAddr` reaches a `Convert` to an
integer backwards through the non-memory arguments of any value except `Load`/`Dereference`,
calls included (so `uintptr(unsafe.Pointer(&x))`, and the frontend's own conversions: a `range`
over an array iterates its copy with `uintptr` arithmetic, `runtime.dumpScanStats`; `append`
into a stack buffer passes the buffer to `runtime.growsliceBuf` and converts the slice pointer
it gets back to compare it with the stack bounds).
Before format 3 the criterion was `addrtaken`, which made every address-taken variable
forgeable. A conversion the function cannot see (the address stored to memory, or passed to a
callee that converts it) is not flagged: converting such an integer back gives a pointer into
no allocation, so the run is less defined than the machine (never wrong). A `Blk.temp` has
the same concrete address, but `Ptr.ofAddr` never returns it (`Ptr.ofAddr_ne_temp`): an integer
converted to a pointer that lands there points into no allocation (a load is `poison`, a store
`stuck`). Go forbids forging such pointers (unsafe rules 3–6; stacks move), and the flags live
in the function's shared aux table, so every section agrees. This makes `dead auto elim`
provable: an eliminated store to an auto can only be observed through a pointer derived from its
`LocalAddr`, and contracts that only follow the pointers they are given (`Env.FrameSafe`,
`Sem/FrameSafe.lean`) cannot see it.
Likewise for the split slots `decompose` adds to the tables (#17): their frame blocks are
frame temporaries no value names, so running the input in the extended tables changes nothing
observable for contracts that cannot tell whether temporaries they get no pointer to exist
(`Env.TempOblivious`, memories compared after `Mem.erase`; `GoFV.Proof.run_tabsAgreeMod`).

### 3.4 Memory

Memory-typed SSA values (`InitMem`, `Store`, `Move`, `Zero`, `VarDef`, calls' last result,
memory `Phi`s, …) evaluate to **snapshots**:

```lean
inductive Byte | b (x : BitVec 8) | frag (p : Ptr) (i : Fin 8) | poison
structure Alloc where base size : Nat; kind : AllocKind; live : Bool
  -- AllocKind: global (sym, readonly) | code (sym) | param/result/auto (frame, ir.Name) |
  --            outargs (frame) | heap
structure Mem where allocs : List Alloc; bytes : Nat → Nat → Byte; next : Nat; rt : RtState
```

A `Load p m` reads snapshot `m` — the one its memory argument names — not "the current
memory". This makes memory ops order-independent exactly as the SSA is: the scheduler (later)
must put a `Load` before any `Store` that consumes the same memory, and the semantics does not
care where it is placed. Persistent snapshots are cheap in Lean (functional updates); the
executable `Mem` can use a `Std.HashMap` per allocation with a `@[csimp]`-free functional API.

- **Globals**: one allocation per `*obj.LSym` referenced by an `Addr` (exported `sym` lines):
  `SRODATA` symbols are read-only with their `data` bytes and `reloc` lines turned into
  pointer fragments (itabs, type descriptors, string data); other data symbols start with
  their contents if exported, otherwise their bytes come from the environment (`Env.globals`).
  Stores to read-only allocations are `stuck`. `SB` is a pseudo-value only used as the base of
  `Addr`; `Addr {sym} SB` = `ptr ⟨alloc sym, 0⟩`.
- **Stack**: at function entry, one allocation per `ir.Name` of class `PAUTO` referenced by any
  value or slot of the function (export `aux name` lines), one per `PPARAM`/`PPARAMOUT`, and
  (post `expand calls`) an outgoing-arguments area that `SP` points to. `LocalAddr {n} SP mem`
  = `ptr ⟨alloc n, 0⟩` (the memory argument only orders it). All frame allocations die at
  return. Frame layout (`FrameOffset`) is not semantic: offsets between different autos are not
  observable through provenance.
- **Auto contents**: initially `poison` bytes. `VarDef {n} mem` resets the bytes of `n` to
  `poison` (the variable is "about to be initialised", gO 562); this is what lets `dse` drop
  stores shadowed by a `VarDef` (`deadstore.go:54,282`). `VarLive`, `KeepAlive`,
  `PubBarrier`, `PrefetchCache*` are the identity on memory (`KeepAlive` still forces arg 0);
  `WBend` frees the write-barrier buffer (§9.6).
- **Heap**: only runtime contracts allocate (`newobject`, `makeslice`, `growslice`, …; §5),
  zeroed.
- **Access rule** (as clifv): a load/store of `n` bytes at `⟨a, off⟩` is valid iff allocation
  `a` is live, `off + n ≤ size`, `off + n < 2^64` (no access wraps around the address space:
  offsets add mod 2^64, so without the bound an allocation of 2^64 bytes or more would let
  `p` and `p + k` straddle the wrap, and `memcombine`'s wide access at `p` would not cover its
  narrow ones; issue #35) and `off + n` is inside the block's address window
  (`Blk.endsInWindow`: `off + n ≤ window` for blocks with one, §3.3; issue #151). The window
  bound makes every byte of a valid access addressable by an in-window pointer, so
  `OffPtr [o] p` into a valid access of `p` is not `poison`: a struct `Load` splits into field
  `Load`s (`rewriteStructLoad`, dec's string/slice/interface splits) for every memory, not only
  for allocations smaller than their window. Invalid **load** = `poison` (loads are pure in Go SSA:
  `deadcode` deletes unused loads, so a load can never be the source of a panic; nil
  dereference panics come only from `NilCheck`, §6). Invalid **store/move/zero** = `stuck`.
  No alignment requirement for plain accesses (arm64 `unalignedOK`); atomics must be naturally
  aligned (`stuck` otherwise).
- **Typed load/store**: a `Load` of type `T` reads `T.size` bytes and decodes them by
  `Layout` into a `Val` of shape `T` (composites before `decompose`: strings, slices,
  interfaces, structs, arrays of length 1). Integer and float pieces are little-endian
  (`Config.BigEndian = false`). A pointer piece decodes from 8 consecutive `frag p 0..7`;
  decoding an integer from fragments uses the concrete address; decoding a pointer from
  concrete bytes goes through the uintptr→ptr rule; any `poison` byte makes the piece `poison`.
  `Store {T}` encodes symmetrically (`poison` pieces store `poison` bytes). A `Load`
  decodes with `decodeLoad` (`Mem.load`): as `decode`, except that an aggregate whose bytes
  (fields and padding, at least one byte) are all `poison` loads as `poison`, at every
  aggregate level. So a stored `poison` aggregate loads back as `poison` (Load-of-Store
  forwarding of strings, interfaces, flat structs, #151), and a struct load still equals the
  `StructMake` of its field loads (`rewriteStructLoad`), since a field load applies the same
  check to the field's bytes. `decode` itself (register pieces `ofPieces`/`toPieces`, ABI
  arguments and results) keeps decoding such bytes to an aggregate of `poison` fields. A
  `Load` of a non-SSA-able type (only after `expand calls` retypes `Dereference` to `Load`,
  `expand_calls.go` `rewriteCallArgs`; it then only feeds a `Move`) yields a `blob`, like
  `Dereference`.
- **Move** `{T} [n] dst src mem` copies `n` bytes with memmove semantics (all loads before all
  stores: correct for exact overlap and for the inline-memmove rules' overlapping moves, gO
  390-401); `Zero [n]` writes `n` zero bytes. `StoreWB`/`MoveWB`/`ZeroWB` have the semantics of
  `Store`/`Move`/`Zero`: the write barrier only informs the GC, which the semantics does not
  model (the barrier calls inserted by `writebarrier` are §5 contracts that only touch the
  runtime's buffer).

### 3.5 Poison, Unknown, uninitialised values

Partial pure operations (division by zero, shifts with a false `bounded` flag, `Ctz*NonZero`
of 0, `Slicemask` of a negative, a bad uintptr→ptr) and reads of uninitialised or invalid
memory yield `poison` instead of failing. `Unknown` (gO 560, values in dead code) is `poison`.
Pure ops propagate `poison` (any `poison` argument → `poison` result), except `CondSelect`,
whose unselected arm may be `poison` (`branchelim` speculates both arms), and `AndB`/`OrB`,
which are *parallel*: `AndB` is `false` as soon as one side is `false` and `OrB` is `true` as
soon as one side is `true`, whatever the other side is (`poison` included); otherwise they are
`poison` unless both sides are booleans. This is hardware's `&&`/`||` on 0/1 registers, and it
is what makes `phiopt`'s `c ? true : x` → `OrB c x` and `c ? x : false` → `AndB c x` refine
when the arm not taken (`x`) is `poison`; `fuse comparisons` likewise evaluates its second
comparison speculatively in `OrB`/`AndB`.

Consumers of `AndB`/`OrB` on the source side, for which the parallel form makes the source
more defined (each still refines):
- **generic.rules 321-388** (`AndB`/`OrB` of two comparisons of the same `x` with constants,
  or `Neq64F x x` with a comparison of `x`): both sides are `poison` exactly when `x` is, so
  ⟦lhs⟧ is the same under the strict and the parallel form. Rules with `AndB` only on the
  right-hand side (1600-1628, `MemEq` splits) get a more defined target. The commutativity of
  `AndB`/`OrB` used for `commute` patterns is re-proved (`Proof/Rules/Comm.lean`).
- **generic cse** orders the arguments of commutative ops; `AndB`/`OrB` stay commutative
  (`andB_swap`/`orB_swap` re-proved in `Proof/Pass/CSEComm.lean`).
- **sccp** folds through the rules on constant arguments; constants are never `poison`.
- **prove** does not decompose `AndB`/`OrB` (no `OpAndB`/`OpOrB` in `prove.go`): a branch on
  one gives a fact about that value only.
- **known bits**: one side known `false` (`true`) makes `AndB` (`OrB`) known `false` (`true`),
  which is now the exact result rather than a refinement of `poison`.
- **fuse comparisons** builds `OrB`/`AndB` (target side only; needs the parallel form).

`poison` becomes `stuck` at the **observation points**: a branch on it (`If`, `JumpTable`),
the address of a store/move/zero, a `NilCheck` argument, a call target, arguments and memory
passed to an environment contract, and function results. `poison` may be stored to and copied
through memory (`Byte.poison`).

Refinement `Val.Refines src tgt`: `src = poison` or `src = tgt` (lifted pointwise through
`tuple`/`agg` and memories). Every rule lemma is `Refines ⟦lhs⟧ ⟦rhs⟧`. Memories
(`Mem.Refines`): the same allocations (blocks, order, sizes, writability), heap and activation
counters, and
byte-wise refinement — a `poison` source byte is refined by any byte, every other byte is
equal. Outcomes (`OutcomeRefines act`, `act` the run's activation; 0 for `run`): a stuck,
out-of-fuel or otherwise undefined source is refined by anything; `returned` needs equal
results (`finish` rejects poison results) and `Mem.Refines` of the final memories; `panicked`
needs the same `Panic` and `Mem.Refines` of the memories without the run's frames (§6).

Why poison rather than `stuck` for partial ops: Go's passes delete and speculate pure values
(`deadcode`, `branchelim`, `phiopt`, `cse` across branches, `tighten` later) without regard to
their partiality; with `stuck`, deleting a dead `Div` would turn a stuck source into a
returning target (fine) but hoisting one into a `CondSelect` arm would make a returning source
stuck in the target (a false negative for `branchelim`). Poison keeps every such pass provable
while observation points still demand defined values. Go itself never relies on these values:
the frontend guards division (`ssagen/ssa.go:5590` `intDivide` → `panicdivide`), negative
shift counts (`panicshift`) and indexing (`IsInBounds` → `PanicBounds`).

### 3.6 Evaluating a function

Generic SSA is **unscheduled**: `b.Values` order carries no meaning (`compile.go:83-91`
shuffles it under `-d=ssa/check/on`). `run` therefore never follows `b.Values` order:

1. **Entry**: allocate the frame (3.4), bind parameters (§5), enter `f.Entry`.
2. **Enter block `b` from predecessor edge `i`**: evaluate all `Phi`s of `b` *in parallel*
   from argument `i` (values of the previous activation), then evaluate every other value of
   `b` eagerly in a dependency order. Pure values (`evalPure`) are total, so their relative
   order is irrelevant.
3. **Roots** — values that can fail or act on the environment: calls (`call: true` in
   `genericOps`: `*Call`, `*LECall`, `PanicBounds`, `PanicExtend`), `NilCheck`
   (`nilCheck: true`), `hasSideEffects` ops (atomics, prefetch, barrier), and stores
   (observation of the address). They are exactly the values `deadcode` keeps regardless of
   uses (`deadcode.go:113`) plus the stores the memory chain reaches. A well-formed block has
   a single memory chain (#8), which totally orders calls and stores; `NilCheck`s are ordered
   only by their arguments. Fixed tie-break, matching the stock scheduler's priorities
   (`schedule.go`, `ScoreNilCheck` before memory ops): among the ready roots the one of least
   **rank** runs next, rank = (priority, value ID) with a `NilCheck` before the other roots
   (#96). The rank makes the sequence of roots a function of their dependencies alone, so a
   pass that keeps the roots, their IDs and the dependencies between them keeps the order in
   which they run — in particular which `NilCheck` panics first (`GoFV.Proof.sched_transfer`).
4. **Terminator** (§7) chooses the successor or ends the activation.

Values of `b` keep the values of `b`'s latest activation; SSA dominance guarantees a use in a
later block sees the right ones. (A lazy, demand-driven evaluation is equivalent on
well-formed SSA and is a possible implementation strategy if eager evaluation is too slow on
big functions.)

## 4. Per-family semantics of pure ops

### 4.1 Integer arithmetic and bits
`Add/Sub/Mul/Neg` mod 2^w; `And/Or/Xor/Com` bitwise; `Hmul{32,64}[u]` = high half of the
2w-bit signed/unsigned product; `Mul{32,64}uhilo` = tuple (hi, lo); `Mul{32,64}uover` = (lo,
lo ≠ exact); `Add64carry x y c` = (x+y+c mod 2^64, carry), `Sub64borrow` = (x−y−c, borrow),
`c ∉ {0,1}` ⇒ poison (gO 583-584 "must be 0 or 1"). `Ctz` (ctz 0 = w), `BitLen` (0 ↦ 0),
`PopCount`, `Bswap`, `BitRev`; their result width is the value's type (`Int` on arm64:
`generic.rules:167` folds `Ctz64` to `Const64` when `PtrSize == 8`). `RotateLeftN x y` rotates by
`y mod N` for any width/sign of `y` (gO 259-262). `Min64/Max64[u]`.

### 4.2 Division
Truncated division as in the Go spec. Signed: `MIN / −1 = MIN`, `MIN % −1 = 0` (Go spec; the
rules fold with Go's own `/` and `%`, `generic.rules:218`); the `Div{16,32,64}`/`Mod{…}` auxint
flag (gO 70, 82) promises "divisor ≠ −1 or dividend ≠ MIN" — a broken promise ⇒ poison (it is
set by `prove`, whose proof obligation this is). Divisor 0 ⇒ poison (frontend-guarded).
`Div128u hi lo y` = (q, r) of the 128-bit dividend; `y = 0` or `hi ≥ y` ⇒ poison
(`math/bits.Div64` panics before reaching it). `Avg64u x y` = ⌊(x+y)/2⌋ computed in 65 bits;
`x < y` ⇒ poison (gO 65 "can assume arg0 >= arg1"; only `divmod` creates it, under that
condition).

### 4.3 Shifts
`AxB`: A-bit value, B-bit amount, amount unsigned (gO 107-111). Amount ≥ A: `Lsh`, `RshU` give
0, `Rsh` gives the sign fill (Go spec; `generic.rules:497`). auxint 1 ("bounded", set by
`prove` and rules) with amount ≥ A ⇒ poison — the flag lets lowering drop the range fix-up,
after which arm64 would shift by `amount mod A`.

### 4.4 Comparisons, booleans, select
`Eq/Neq` on bits, `Less/Leq` signed, `…U` unsigned, results `bool`. `EqPtr/NeqPtr` §3.3.
`EqInter/NeqInter/EqSlice/NeqSlice` compare the first word (`generic.rules:790-792`: itab /
slice pointer; the frontend uses them only when one side is nil, gO 169). `AndB/OrB/EqB/NeqB/Not`
on `bool`, both sides evaluated. `CondSelect x y c` = `c ? x : y` (§3.5). `IsNonNil p` = p ≠ nil;
`IsInBounds i n` = `0 ≤ i < n`, `IsSliceInBounds` = `0 ≤ i ≤ n` (unsigned compares, `n ≥ 0`
guaranteed, gO 502-503). `SpectreIndex/SpectreSliceIndex` = arg0 if in range else 0.

### 4.5 Integer conversions
`SignExt`, `ZeroExt`, `Trunc` (low bits), `CvtBoolToUint8` (0/1), `Slicemask` (0 ↦ 0,
positive ↦ −1, negative ⇒ poison, gO 588).

### 4.6 Floats (phase P4)
IEEE 754 binary32/binary64 on bit patterns, round to nearest even, the arm64 NaN rules with
`FPCR = 0` (first signalling NaN quietened, else first quiet NaN, else default NaN) — exactly
clifv's choice (`FV/Clif/FSem.lean`, `docs/plans/floats.md`), by a port of clifv's `FV/Float`
ASL library (`GoFV/SSA/Sem/Float/*`, namespace `GoFV.IEEE`). One deviation from the hardware:
the ops Go marks commutative (`Add/Mul/Eq/Neq{32,64}F`) take their operands in the order of
their encodings (`FOps.ordered`), so that two NaN operands of the same kind give the same NaN
in either order (arm64 picks the first; `cse` sorts commutative arguments by value ID, §9.4).
Specifics: `Neg/Abs/Copysign` touch the sign bit only (`Copysign x y` = `|x|` with `y`'s
sign); `Sqrt`, `Floor/Ceil/Trunc/Round/RoundToEven` (gO 268-286; `Round` = ties away from
zero); `FMA` single rounding with the gO 306-315 zero-sign rules; `Min/Max{32,64}F` are Go's
`min`/`max` (NaN if any argument is NaN, −0 < +0); comparisons are unordered on NaN
(`Neq` true, others false). `Cvt{32,64}to{32,64}F`, `Cvt64Uto*F` round to nearest even;
`Cvt32Fto64F` exact; `Cvt64Fto32F` rounds. Float → integer truncates toward zero; NaN and
out-of-range results are implementation-defined in the Go spec and are fixed to arm64's
`FCVTZS/FCVTZU` (saturate, NaN ↦ 0) — the rules only fold in range (`generic.rules:53,56`),
so this choice is consistent with them and with the native oracle. `Round32F/Round64F` are the
identity (values are already exact bit patterns). `Const32F` auxints hold the float64 bits of
a float32-exact value (gO 347); constants are never NaN (gO 342-346).

### 4.7 Composites
`StringMake/SliceMake/IMake/ComplexMake/StructMake/ArrayMake1` build `agg` (a string or slice
with an invalid length is `poison` once retyped at its shape, §3.2); `StringPtr/Len`,
`SlicePtr/Len/Cap`, `SlicePtrUnchecked`, `ITab/IData`, `ComplexReal/Imag`, `StructSelect [i]`,
`ArraySelect [i]` project. `ConstString {s}` = (pointer to the string's read-only data symbol,
`len s`) — the exporter writes the data symbol name (`str` aux); `ConstNil`, `ConstSlice`
(nil, 0, 0), `ConstInterface` (nil, nil), `Empty`.

### 4.8 Tuples, results
`Select0/Select1/MakeTuple` on `tuple`; `SelectN [i]` projects a call's `RESULTS` tuple (pre-
expand: Go-typed results, memory last; post-expand: register pieces, memory last);
`SelectNAddr [i]` is the address of stack-assigned result `i` in the outgoing-arguments area
(§5): a call's tuple carries, after its memory, the addresses of its results (`poison` for
register results), so `SelectNAddr` is a pure op of its argument (`evalValue` never looks at
other values of the function; `poison` for a register result); a tuple has the shape of its type when its first components do
(`Val.hasTyPre`). `MakeResult` builds the `Ret` control (§7).

### 4.9 Pseudo and out-of-phase ops
`Copy` identity; `Phi` §3.6; `Convert` §3.3 (memory argument only orders it). `InlMark` no
effect. `Last` (rulegen-only), `FwdRef` (SSA construction only), `Invalid`, `StoreReg`/
`LoadReg` (regalloc only) are `stuck` if met. `GetG`, `GetClosurePtr`, `GetCallerPC`,
`GetCallerSP`, `HasCPUFeature` read activation/environment state (§5). `Clobber*` (clobberdead
debug flag) and the SIMD ops are out of scope.

## 5. Calls and the environment

```lean
structure Contract where   -- trusted behaviour of a callee at the Go-typed level
  call : (args : List Val) → (closure : Option Val) → Mem → COutcome
inductive COutcome | returned (results : List Val) (m : Mem) | panicked (e : Panic) (m : Mem)
                   | stuck (msg : String)
structure Env where
  funcs   : String → Option Func        -- program functions, run by `run` itself (recursion bounded by fuel)
  extern  : String → Option Contract    -- runtime and other callees without SSA
  globals : String → Option GlobalInit  -- data of non-rodata globals (sizes from the export)
  codeSym : Nat → Option String         -- allocation of a code symbol → function name
```

Program functions take precedence over contracts (as clifv's `Clif.run`). The common
interface is the **Go-typed** argument and result lists, so pre- and post-`expand calls` code
call the same contracts:

- **Before `expand calls`**: `StaticLECall {AuxCall} args… mem` passes Go-typed values
  (composites as `agg`; non-SSA-able arguments as `blob`s made by `Dereference`, gO 435-440),
  retyped at the shapes of the ABI's input parameters (§9.3);
  the result is `tuple (results ++ [mem, addrs])`, read by `SelectN`; stack-assigned results
  are also stored in the caller's outgoing-arguments area, at the addresses `addrs`
  (`SelectNAddr`, §4.8).
  `ClosureLECall code ctx args… mem`: `code` is a pointer into a `code` allocation resolved by
  `Env.codeSym`, `ctx` becomes the callee's `GetClosurePtr`. `InterLECall code args… mem`: the
  code pointer was loaded from an itab in read-only data (pointer fragments from `reloc` lines).
  `TailLECall*` end the activation (§7).
- **After `expand calls`**: `StaticCall {AuxCall} regargs… mem`: the `AuxCall` ABI info
  (exported `abiparam` lines: per parameter its registers or stack offset) decodes the
  Go-typed arguments from the register pieces and from the stack-assigned bytes stored at
  `SP+offset` in the outgoing-arguments area; after the callee returns, results are encoded
  back (register pieces into the `RESULTS` tuple, stack results into the outgoing area). In
  both forms the callee sees that area poisoned, and the call is `stuck` unless the slots of
  its stack-assigned arguments are writable (`outargsOK`, §9.3). The
  function's own parameters likewise arrive as `ArgIntReg/ArgFloatReg {name+off} [regindex]`
  pieces (arm64 ABIInternal: 16 integer, 16 float registers, export `config abi1 16:16:8`) and
  `Arg {name} [off]` pieces; its results leave through `MakeResult` pieces plus stores to the
  results area. `ABI0` calls (assembly) have no registers (`abi0 0:0:8`).
- `expand calls`' proof then reduces to the ABI encode/decode round-trip plus value
  correspondence, and the `Contract` stays untouched.

Initial contract set (P3; extend from the corpus' call-target histogram the exporter can
produce): `runtime.newobject`, `makeslice`, `growslice`, `memmove`, `typedmemmove`,
`memclrNoHeapPointers`, `memequal*`, `concatstrings`/`slicebytetostring`/
`stringtoslicebyte`, `convT*`, panicking entry points (`panicdivide`, `panicshift`,
`panicwrap`, `panicnildottype`, `panicdottype*`, `gopanic`, `panicmem`: `panicked`),
`gcWriteBarrier` (the `WB` op: a pure op that allocates the write-barrier buffer `Blk.wbuf`,
§9.6), `wbZero`/`wbMove` (no memory effect), `goschedguarded`
(identity; only with `GOEXPERIMENT=preemptibleloops`). Maps, channels, goroutines, `select`,
reflection: `stuck` (no contract) until needed. `GetG` returns a pointer to an opaque `g`
allocation owned by the environment.

## 6. Panics and nil checks

```lean
inductive Panic
  | bounds (kind : Nat) (x y : Int)   -- PanicBounds: kind = ssa.BoundsKind auxint (op.go:470-489); also the PanicBoundsC/CC aux forms
  | nilDeref                          -- NilCheck of nil
  | divide | shift                    -- runtime.panicdivide / panicshift contracts
  | value (v : Val)                   -- gopanic with a payload (P3)
  | runtime (name : String)           -- any other panicking contract
```

`NilCheck p mem` (a root): `p` points into no allocation (`Blk.nil`, any offset; for a
`uintptr` argument, `Ptr.ofAddr x` does) ⇒ `panicked nilDeref`; `p` poison ⇒ `stuck`; otherwise
its value is `p`. (Since P3: a check of `nil + k` panics too, like the machine's load in page 0,
so a pointer that passed a check is not nil-derived and `OffPtr`/`AddPtr` of it keep it so,
which `nilcheckelim` relies on, `nilcheck.go:59`; `GoFV.Proof.evalOp_nilCheck_blk`.) `PanicBounds [kind] idx len mem` ⇒ `panicked (bounds kind idx len)`; the block
after it is an `Exit` block. Recovery (`recover` in a deferred call) is P5: until then a
`panicked` outcome ends the run. Its memory is compared (`Mem.Refines`) after dropping the
frames the run created (`Mem.dropFrames act`: the allocations `.local a _` and `.outargs a`
with `a ≥ act` — the run's own activation and its callees', which get fresh numbers
`Mem.nextAct`): a deferred function with `recover` could observe heap, globals and the
caller's memory (also through pointer arguments), which must still refine, while the
unwound frames are unobservable — this is what lets `dead auto elim` and `nilcheckelim` drop
or move stores to frame slots before a panic. **P5** (recover) must narrow this to the
frames actually unwound up to the recovering activation (a recovering function's own frame
and open-coded defer slots stay observable).

## 7. Block kinds

| Kind | Controls / succs (gO 732-754) | Semantics |
| --- | --- | --- |
| `Plain` | – / 1 | go to `Succs[0]` |
| `If` | bool / 2 | `true` → `Succs[0]`, `false` → `Succs[1]`, poison → `stuck`; `Likely` has no semantics |
| `First` | – / 2 | always `Succs[0]` (transient state for deadcode) |
| `JumpTable` | int / n | index read unsigned; `< n` → that successor, otherwise `stuck` (the frontend range-checks first) |
| `Ret` | `MakeResult` / 0 | `returned` with the Go-typed results: pre-expand the `MakeResult` args except the last (non-SSA-able results as `blob`s from `Dereference`); post-expand decoded from register pieces + results area by `f.OwnAux`; memory = last arg minus the frame |
| `RetJmp` | tail call / 0 | the activation's outcome is the tail callee's outcome |
| `Exit` | memory of a non-returning call / 0 | reaching the terminator means the call returned: `stuck` (contracts of panicking functions never return) |
| `Defer` | the `deferproc` call / 2 | P5: the call registers the deferred closure in `Mem.rt`; `Succs[0]` normally, `Succs[1]` when the runtime reports a recovered panic. Before P5: `Succs[0]` only, recovery `stuck` |

## 8. Outcome, fuel, entry point

```lean
inductive Outcome
  | returned (results : List Val) (mem : Mem)
  | panicked (e : Panic) (mem : Mem)
  | stuck (msg : String)
  | outOfFuel
def run (env : Env) (f : Func) (args : List Val) (closure : Option Val) (mem : Mem)
    (fuel : Nat) : Outcome
```

Fuel counts block entries and calls (clifv counts statements; per-block is enough here since
pure evaluation within a block terminates structurally). `runLoop` is structurally recursive
on fuel; calls to program functions recurse with the remaining fuel (no well-founded
recursion — LEARNINGS). `args` are Go-typed per `f.Type`; the frame and the results area are
allocated in `mem` and freed before returning.

## 9. Phased subset

| Phase | Ops (table column "phase") | Blocks | Passes whose proofs it enables |
| --- | --- | --- | --- |
| **P1** integer/bool/control | int arithmetic, division, shifts, compares, bool, `CondSelect`, int conversions, bit ops, int/bool constants, `Phi`, `Copy`, tuples, `IsInBounds`/`IsSliceInBounds`/`PanicBounds`; `Arg` of scalar params; `InitMem`/`MakeResult` with memory as an opaque token | `Plain`, `If`, `First`, `JumpTable`, `Ret`, `Exit` | copyelim/phielim, deadcode, short circuit, opt (integer rules), zero arg cse, generic cse, phiopt, prove (integer facts), divisible, divmod, known bits, fuse, branchelim, sccp, check bce |
| **P2** memory, pointers, composites | `Load`/`Store`/`Move`/`Zero`, `Addr`/`LocalAddr`/`SP`/`SB`/`OffPtr`/`PtrIndex`/`AddPtr`, `NilCheck`, `VarDef`/`VarLive`/`KeepAlive`, `Convert`, strings/slices/interfaces/structs/arrays/complex (as ints until P4), `Dereference`, `MemEq`, `ConstString`/`ConstNil`/… | – | nilcheckelim, decompose user/builtin, dse, dead auto elim, memcombine, memory rules of opt |
| **P3** calls | `*LECall`, `*Call`, `SelectN`/`SelectNAddr`, `ArgIntReg`/`ArgFloatReg`, `GetG`/`GetClosurePtr`, write-barrier ops, runtime contracts | `RetJmp` | expand calls, writebarrier, insert resched checks, call-related rules (devirtualisation, `memmove` inlining) |
| **P4** floats | float ops and conversions (port of clifv `FV/Float`) | – | float rules, softfloat (a no-op on arm64) |
| **P5** rest | atomics (sequential semantics), `HasCPUFeature`, `GetCallerPC/SP`, prefetch/barrier, defer/recover | `Defer` | — |
| 32b | ops only `decompose builtin`'s dec64 rules (`RegSize == 4`) or 32-bit lowering produce | – | never on arm64 [INFERENCE from gO comments; confirm with the corpus op histogram] |

Each phase lands with the native difftest (#10): Go harnesses call corpus functions with
random and edge-case arguments under `qemu-aarch64-static`, print results or the recovered
panic, and `run` is executed on **every exported section** of the same function with the same
arguments. Disagreement between sections of one function localises a semantic bug (or a
miscompile) to one pass, before any proof exists.

### 9.1 P1 as implemented (#10)

Modules `GoFV/SSA/Sem/{Val,Int,Shift,Cmp,Conv,Pure,Env,Layout,Run}.lean`; entry point
`GoFV.SSA.run env tabs f args mem fuel` (`tabs`: the export tables of `f`'s section).

- **Value domain** P1 part: `int`, `bool`, `mem` (an opaque token `Mem` with no fields; P2
  replaces the structure), `tuple`, `poison`.
- **Out-of-phase ops.** A pure op outside P1 evaluates to `poison`; a root outside P1
  (`Store`, `NilCheck`, `VarDef`, calls without a contract, …) is `stuck`. Every function's
  section 0 has dead `SP`/`SB`/`LocalAddr` values, so out-of-phase pure values must not be
  `stuck`; since `poison` is refined by anything and pure ops are monotone in it, a P1 outcome
  that is `returned`/`panicked` is the outcome of the full semantics too, and roots run in
  memory-chain order, so no unmodelled effect can be skipped.
- **Evaluation order** (§3.6): `schedule` is Kahn's algorithm (`kahn`) over a block's
  non-`Phi` values (`schedNodes`: ID, arguments, priority); a ready pure value first, else the
  ready root of least rank (`SNode.rankLt`: priority, then ID; `isRoot`: `call`, `nilCheck`,
  `hasSideEffects`, `typ: Mem`, `VarLive`). Its output is validated by `schedValid` (every node
  once, each after its in-block arguments; pure nodes and nil checks as early as their arguments
  allow; `rankOK`: a root listed after a root of greater rank was not ready then), so proofs use
  that specification (`SchedSpec`), never the algorithm; the fallback `greedy` satisfies it too.
  On the corpus every block's Kahn schedule passes the validator (`sched-probe`: 2,933,048
  blocks). Computed once per block per run (`Ctx`); a cycle is `stuck`. The scheduler uses
  arrays indexed by value ID, not hash maps: the kernel cannot evaluate `Std.HashMap` (its
  `USize` arithmetic depends on the opaque `System.Platform.getNumBits`), and the proofs'
  non-vacuity witnesses evaluate `run` with `decide +kernel` (`GoFV/Proof/Witness/Clamp.lean`).
- **Arguments**: Go-typed scalar parameters; `Arg {n} [0]` and `ArgIntReg {n+0}` read
  parameter `n` (its index among `f.OwnAux`'s input ABI assignments), so the same arguments
  run before and after `expand calls`. Results: `MakeResult` arguments but the last (the
  memory); with scalar results these are the same Go-typed values in both forms.
- **Contracts** (`Env.p1`): `runtime.panicdivide`, `panicshift`, `panicoverflow` panic;
  called by `StaticLECall`/`StaticCall` with the memory as last argument.
- `PanicBounds` reads `x` signed for the signed kinds (`BoundsKind.Code`), and `Panic.message`
  reproduces the runtime's error text, so panics compare with native runs textually.
- `JumpTable`: index read unsigned; out of range is `stuck`.
- Shift amounts are capped at the width before shifting (same results; compiled code would
  otherwise build `x <<< 2^63`).
- `math/bits.Div64` is not an intrinsic on arm64 (a call), so `Div128u` is unreachable from
  arm64 code; its semantics (§4.2) is untested natively.

Difftest (`scripts/sem-difftest.sh`, `tools/semdiff/prog`, `lake exe sem-difftest`): 49
integer/bool functions (all widths, signed/unsigned division and remainder by variables and by
constants, variable and constant shifts, comparisons, short circuits, loops, jump table,
`math/bits` intrinsics, `min`/`max`, multi-results), 200 random/edge-case calls each, compiled
for linux/arm64 by the patched toolchain while exporting their SSA; native results under
`qemu-aarch64-static` against `run` on **every** exported section: see #10 for the counts.
`sem-difftest corpus` runs random calls on every corpus function with integer/bool signature
and checks that every section agrees with section 0 whenever section 0 is defined.

### 9.2 P2 as implemented (#10)

- **Values**: `ptr ⟨blk, off⟩` with `Blk` = `nil | global sym | local act name | outargs act |
  heap n` (provenance §3.3), `agg` (string, slice, interface, struct, `[1]T` fields), `blob`
  (other arrays), `empty`; memory snapshots `Mem` = allocations (`Array Byte`, writable flag)
  by block; `Byte` = concrete, pointer fragment `frag p i`, or poison.
- **Shapes** (`Ty`, `Sem/Layout.lean`) from the exported types: integer widths, `bool`, `ptr`
  (element size), `agg` (fields at exported offsets), `blob`, `empty`, `opaque` (floats and
  complex until P4, §9.4: loads give `poison`, stores write poison bytes); since #10's length
  change `str` and `slice` (element size), whose values have valid lengths (§3.2).
- **Concrete addresses**: heap block `n` at `(n+1)·2^40`, frame blocks at `2^62 + act·2^42 +
  name·2^24`, `nil` at 0; globals have none (comparisons with them are by block). `Convert`
  and `uintptr`-typed values use them; `Val.retype` turns a `uintptr`-typed pointer into its
  address and a pointer-typed integer into the pointer at that address.
- **Frame**: one allocation per `PAUTO`/`PPARAM`/`PPARAMOUT` name the section's tables define
  (not per referenced name: deleting values never changes the frame); a `PPARAM` holds its
  argument's bytes, the rest are poison; `VarDef` re-poisons. The frame is removed from the
  returned memory. `LocalAddr {n}` = `⟨local act n, 0⟩`, `SP` = `⟨outargs act, 0⟩`.
- **Arguments and results** are bytes: each Go-typed argument is encoded by its parameter's
  shape (`Frame.images`); `Arg {n} [off]` and `ArgIntReg {n+off}` decode a piece at `off`.
  `Ret`: before `expand calls` the `MakeResult` components are the Go-typed results; after it
  the register pieces (`leaves` of the result shapes, in ABI order) plus the `PPARAMOUT`
  variables of stack results. Both are reduced to bytes and decoded (`goResults`), so every
  section returns the same Go-typed values.
- **Roots**: `Store`/`StoreWB`, `Move`/`MoveWB` (memmove), `Zero`/`ZeroWB`, `VarDef`,
  `VarLive`, `KeepAlive`, `WBend` (identity), `NilCheck` (nil ⇒ `panicked nilDeref`;
  accepts a `uintptr`). An invalid or read-only write is `stuck`; an invalid read is `poison`;
  an empty access is always valid (Go copies and compares zero bytes at nil).
- **Globals** (`Env.globals`, `globalImage`): `SRODATA` symbols with their bytes and `R_ADDR`
  relocations as pointer fragments (an empty `data` without type or itab information, the
  `..stmp_N` of zero composite literals: `size` zero bytes, `rodataBytes?`), string data
  symbols from their names, and zeroed writable
  allocations for the other symbols an `Addr` names (sized by the pointee type).
  `ConstString` points to the string's data symbol.
- **Pure P2 ops**: `OffPtr`, `AddPtr`, `PtrIndex`, `SubPtr`, `EqPtr`/`NeqPtr`, `IsNonNil`,
  `Convert`, `Eq/NeqInter`, `Eq/NeqSlice`, composite make/select ops, `ConstNil`,
  `ConstSlice`, `ConstInterface`, `Empty`, `Load`, `Dereference`, `MemEq`, and the atomic
  loads (sequential semantics, P5 pulled forward because they only read).
- **Typing**: `evalValue` = `evalOp` (the op's raw result) followed by `Val.retype` at the
  value's type shape, for every op (§3.2), so every register is fixed by `retype` at its
  value's shape (`GoFV.Proof.evalValue_typed`).
- **Results**: `finish` rejects a `MakeResult` component that contains poison (deeply,
  including poison bytes of a blob) before decoding; so a defined source outcome's results
  are poison-free, refinement of them is equality, and `finish` preserves outcome refinement
  (`GoFV.Proof.finish_refines`).
- **Proof impact**: a nil `NilCheck` panics. With the first-ready (FIFO) tie-break of P2 the
  order of ready `NilCheck`s was not invariant under a change of dependencies, so
  `copyelim_refines`, `deadcode_refines` and `zcse_refines` took "no `NilCheck` in `f`"
  (`NoNil`). #96 replaced it by the rank tie-break; `sched_np_eq` (the roots run in the same
  sequence) and `sched_transfer` (what the target evaluates before the panicking root, the
  source evaluated before it) let those proofs drop `NoNil` and the `chained` fragment.
  `sched_transfer'` generalises the argument hypothesis to `Feeds` (an argument reaches its
  user directly, or through pure source nodes the target bypasses), as copyelim needs:
  `copyelim_refines` now takes only `EmptyFrag` (`GoFV/Proof/Pass/CopyElimRank.lean`:
  `sameNP_copy`, `depBack`, `feedsOf`), and `zcse_refines` nothing beyond its checker
  (`GoFV/Proof/Pass/ZCSERank.lean`: `sameNP`, `depBack`, `feeds`; the checker requires the
  redirected arguments to be pure and the entry's argument-free roots to stay put). The
  deadcode simulation (`refines_of_deadRel`) needs only `DeadRel`: the target keeps a closed
  subset of the block's nodes, and the source schedule restricted to it is a schedule of the
  target block (`GoFV/Proof/Pass/DeadRank.lean`: `schedSpec_restrict`, `sched_transfer_sub`).
- `run` stays free of `Std.HashMap` (the kernel evaluates the witnesses' runs), and every
  recursive definition on its path is structural.

Difftest additions (`tools/semdiff/prog/mem.go`): 38 functions on slices, strings, structs,
arrays (by value, local, result), pointers, linked lists, read-only tables (jump tables
lowered to `SRODATA` lookups, string tables with relocations), pointer comparison, aliasing,
writes through arguments (the harness prints the arguments again after the call), and
`unsafe.SliceData`/`StringData` of nil and empty values. The value syntax (Go-quoted strings,
`[…]`, `{…}`, `&…`, `nil`) is shared by `main.go` and `GoFVTest/SemDiff.lean`; arguments are
built as bytes with fresh heap allocations. `sem-difftest trace <file> <section> <args>`
prints every block entry and value of one run.

### 9.3 P3 as implemented (#10)

- **Environment** (`Sem/Env.lean`): `Env.extern : String → Option Contract` with
  `Contract := List Val → Option Val → Mem → COutcome` (Go-typed arguments, closure context,
  memory). The runtime contracts are `Env.runtime` (`Sem/Runtime.lean`): `newobject`,
  `makeslice` (+ `panicmakeslicelen/cap`), `growslice*` (runtime capacity growth and size
  classes), `moveSlice*`, the size-specialised `mallocgc*SC*`, `memmove`,
  `memclrNoHeapPointers`, `typedmemmove`, `typedslicecopy`, `memequal`, `convT*`,
  `concatstring*`, `slicebytetostring`, `stringtoslicebyte`, `print*` (no effect), and the
  panicking entry points (`panicdivide`, `panicshift`, `panicoverflow`, `panicdottype*`,
  `gopanic`, …). Type descriptors are read from memory (`Size_`, `PtrBytes`), laid out by the
  global image (`typeDescAlloc`); itab method entries are weak `R_ADDR` relocations
  (`RelocType(-32767)`); a code pointer is the start of a `global` function symbol.
- **Program functions** (`Env.withFuncs base funcs fuel d`): a callee with SSA runs as a new
  activation (`runActivation`: activation number `Mem.nextAct`, its frame and outgoing area
  allocated in the caller's memory, the closure context for `GetClosurePtr`, `finish` with the
  frame freed), at most `d` calls deep, `fuel` block entries each; deeper calls use `base`.
- **Calls** (`callOp`): `StaticLECall`/`ClosureLECall`/`InterLECall` pass Go-typed arguments,
  retyped at the shapes of the `AuxCall` ABI's input parameters (`retypeResults`, as the
  results; #28: an `unsafe.Pointer` passed to a `uintptr` parameter is its address, as the post
  form decodes it); `StaticCall`/`ClosureCall`/`InterCall` decode them from register pieces and
  the outgoing area by the `AuxCall` ABI (`decodeArgs`) and encode results back
  (`encodeResults`). The tuple is `results ++ [mem, addrs]`, `addrs` the stack results' addresses
  (`SelectNAddr`, §4.8). A
  poison argument is `stuck`; a contract's panic is the call's panic. The contract sees the
  caller's outgoing-arguments area poisoned (`Mem.poisonBlock (.outargs act)`), and in both
  forms the call is `stuck` unless the slots of its stack-assigned input parameters are
  writable in its memory (`outargsOK`, built on `Mem.canWrite`; #28): a run's frame always
  allocates the area, so post-`expand calls` stores of stack arguments into it cannot fail
  where the pre form's call succeeds. `Panicking op :=
  op.call ∨ op = NilCheck` (`GoFV.Proof.evalValue_panic_op`).
- **Frame state**: `GetCallerSP` = `2^62 + (act + 1)·2^42` (just above the activation's frame
  region); `GetClosurePtr` = the activation's closure context.
- **Not in P3** (`stuck`): `TailLECall*`, `GetG`, write-barrier ops (`WB`, `gcWriteBarrier`),
  channels, maps, `gorecover`/defer (P5), atomics other than loads (P5), `ArgFloatReg` (P4,
  §9.4), runtime entry points without a contract (`mcall`, `lock2`, `rand`, …).
- **NilCheck** panics on any pointer into `Blk.nil` (§6).

Difftest additions (`tools/semdiff/prog/calls.go`): 32 functions with static, closure,
interface, method-value and recursive calls, runtime allocation and growth, string building,
large (stack-assigned) results, and runtime panics. The native harness quotes strings byte by
byte (`quoteBytes`, as `goQuote`). `sem-difftest` loads the program's functions as callees
(`programEnv`). Results: native 119 functions, 11,900 calls, every section agrees with
native. Corpus (quick-v1, 20 calls per function): 4,380 supported signatures, 39,131 calls
defined at section 0 in 2,266 functions, 1,251,134 later-section runs agree, 0 differ, 1,058
stuck in 7 functions (the `nilcheckelim` gaps of §10).

### 9.4 P4 as implemented (#10)

- **Values**: a `float32`/`float64` is its IEEE bit pattern in `Val.int .w32`/`.w64`; the
  shapes of `FLOAT32`/`FLOAT64` are the integer shapes of their size, `COMPLEX64`/`COMPLEX128`
  are `agg`s of two (`Sem/Layout.lean`). Loads, stores, ABI pieces, `Copy` and bit casts
  (`math.Float64bits` is a store and a load) need no float case, and no proof that matches on
  `Val` or `Ty` changed. `Ty.opaque` remains only for structs without exported field offsets.
- **IEEE core** (`Sem/Float/{Basic,Round,Arith,Convert}.lean`): clifv's `FV/Float` ported
  (namespace `GoFV.IEEE`, Lean core only, kernel-reducible; `truncInt?`, CLIF-only, dropped).
  Its witnesses and 40 Go-op witnesses (`evalPure` on the ops below) are
  `GoFVTest/Float/Witness.lean` (`decide +kernel`).
- **Ops** (`Sem/Float.lean`, `FOps`; one `evalPure` arm each, monotone by
  `int1/int2/int3_mono`): every op is the AArch64 instruction `ARM64.rules` lowers it to, with
  `FPCR = 0` and RNE: `Add/Sub/Mul/Div/Neg{32,64}F`, `Sqrt`/`Sqrt32`, `Floor/Ceil/Trunc/Round/
  RoundToEven` (`FRINTM/P/Z/A/N`), `Abs`, `Copysign`, `FMA x y z` = `FMADDD z x y`,
  `Min/Max{32,64}F` (`FMIN/FMAX`), the comparisons, `Cvt*` (`SCVTF/UCVTF` round to nearest
  even; `FCVTZS/FCVTZU` truncate, saturate and map NaN to 0; `FCVT` between the formats),
  `Round32F/Round64F` (identity), `Const32F/Const64F` (auxint = float64 bits).
- **Commutativity** (§4.6): `cse` canonicalises the argument order of `Op.commutative` ops and
  the rules match them both ways; with arm64's first-NaN-wins rule `Add64F x y` and `Add64F y
  x` differ when both are NaNs of the same kind. The commutative float ops therefore order their
  operands by encoding; `GoFV.Proof.CSE.evalPure_swap` covers them (`FOps.ordered_comm`).
- **`ArgFloatReg {n+off}`** reads a parameter piece like `ArgIntReg` (`argFloat`); an
  ill-formed one (a name that is not a parameter) is `poison`, not `stuck`, so it evaluates like
  a pure value and the proofs' "not a parameter read" hypotheses (`≠ .Arg`, `≠ .ArgIntReg`) did
  not change. It is not a term op of the rewrite validator (`RewriteCheck.termOp`; droppable
  atom, `dropAtom`). Adapted: `CSE.evalOp_tail` (`≠ .ArgFloatReg`), `evalOp_total`,
  `evalOp_ok_id`, `evalOp_congr`, `evalOp_argless`, `evalPure_mono`, `evalPure_swap`.
- **Runtime**: `printfloat`, `printcomplex` (no effect). `complex128div` has no contract (the
  runtime's own compiled division is FMA-fused, see below).
- **Not modelled**: `lower` fuses `a + x*y` into `FMADD` (`ARM64.rules` `useFMA`, allowed by
  the Go spec), so native code may differ from the generic ops on such expressions; the passes
  up to `lower` never fuse. Difftest functions write such products as `float64(x*y)` (an
  explicit conversion rounds, `Round64F`, and blocks the fusion); complex multiplication and
  division are left out for the same reason.

Difftest additions (`tools/semdiff/prog/floats.go`): 80 functions on float32/float64
arithmetic, comparisons, conversions of every width and signedness (out-of-range and NaN
included), the math intrinsics, `min`/`max`, bit casts, constants and folding, loops over
float slices, structs and pointers with float fields, and complex values. Floats are written
as their bit patterns in hex on both sides (`0x3ff0000000000000`; the Go harness reads and
writes them through memory, since reflect's `SetFloat`/`Float` convert through float64 and
would quieten a float32 signalling NaN), complex numbers as `{re,im}`; random floats are
edge-biased (signed zeros, infinities, quiet and signalling NaNs with payloads, subnormals,
extremes, integer-conversion boundaries, ties). Results: #10.

### 9.5 P5 atomics as implemented (#10)

- **Atomic roots** (`Sem/Atomic.lean`, `atomicRoot`: `evalOp`'s last arm for every root that is
  not a call or a memory root of P2). `run` executes one goroutine, so an atomic op is its
  sequentially consistent single-threaded meaning: one read-modify-write of a naturally aligned
  location, ordered by the memory chain. `Atomic.info?` gives the read-modify-write and the
  location's shape of every `AtomicStore*`/`Exchange*`/`Add*`/`And*`/`Or*` (with the `*value`,
  `*Variant` and `Rel` forms: arm64's LSE instructions and acquire/release mean the same here);
  `Atomic.casWidth?` the width of `AtomicCompareAndSwap*`. Misaligned, invalid or read-only
  accesses are `stuck` (arm64 faults; the semantics has no fault outcome other than nil
  checks), a `poison` operand is stored as poison bytes like a plain `Store`, and a
  compare-and-swap on a `poison` comparison is `stuck` (it decides whether memory changes).
  `PubBarrier` and `PrefetchCache*` leave memory unchanged. The dispatch is on the number of
  arguments only, so refined arguments take the same arm (`GoFV.Proof.atomicRoot_mono`); no
  atomic root panics (`GoFV.Proof.atomicRoot_ne_panic`, used by `evalValue_panic_op`, so
  `Panicking` is unchanged). Any other root (`TailLECall*`, …) is `stuck` as before
  (`Atomic.modelled` names the ops `atomicRoot` evaluates).
- **`HasCPUFeature`** = `false`: on arm64 it only guards the LSE `*Variant` atomics, which mean
  the same as their base forms, so either branch computes the same (`evalPure`).
- **`GetG`** = a pointer to the environment's opaque `g` allocation (`.global "runtime.g"`,
  never nil, §5; nothing reads through it in P1–P5).
- Proofs: `GoFV.Proof.atomicRoot_sim` (`Proof/AtomicSim.lean`): an atomic root on memories
  related by any `AtomicSimRel` (loads and writes alike on the blocks its pointer arguments
  point into) returns alike; dead auto elim (`Mem.EqOff`, `DAE.atomicRoot_rel`,
  `DAE.atomicRoot_avoids`) and the extra-temporaries tables check (`EqX`; `stuckRoot` now
  excludes `Atomic.modelled` ops) instantiate it.
- Adapted: `evalOp_mono_same` (`atomicRoot_mono`), `evalValue_panic_op`, `CSE.evalOp_tail_ite`
  (its `isRoot` branch now names `atomicRoot`), `evalPure_mono` (`HasCPUFeature`, `GetG`),
  `DAE.evalOp_atomic` (now `= atomicRoot v argv`), `TabsMod.evalOp_notArm`.

Difftest additions (`tools/semdiff/prog/atomics.go`): 26 functions on `sync/atomic`'s
functions and typed wrappers (`Add`/`Swap`/`CompareAndSwap`/`Load`/`Store`/`And`/`Or` on 32-
and 64-bit, signed and unsigned, `Bool`, `Uintptr`), on locals, through pointers, slice
elements and struct fields, and CAS loops.

Results (`--n 100 --seed 3`): 225 functions, 22,500 calls; native agrees with every section on
22,498, every atomic function included. The 2 others are `makeBad(16, 2^32)`: a 4 GiB
`makeslice` above the executable model's allocation limit (`maxModelAlloc` = 2^24, `stuck`).

### 9.6 Write barriers (#36)

`writebarrier` expands a pointer store into a load of the GC's flag `runtime.writeBarrier`, a
branch to a buffer block that records the pointers for the GC (`WB`, buffer `Store`s, or the
`wbZero`/`wbMove` helpers for typed zeroing/copies), and the plain store followed by `WBend`.

- **Buffer** (`Blk.wbuf`, `Sem/Val.lean`): a block with no address and no window (not
  convertible: `Ptr.ofAddr` never returns it, so no program pointer reaches it). `WB [n] mem` is
  a pure op (not a root): `(⟨wbuf, 0⟩, mem with a fresh buffer of 8·n poison bytes)`
  (`wbOp`, `Mem.wbAlloc`); `WBend mem` frees it (`m.free .wbuf`), so the memory after a
  write-barrier sequence is the memory of the plain store, whichever branch ran.
- **Flag**: `runtime.writeBarrier` is read-only in the global image (`globalImage`, at least 4
  zero bytes): programs never write it, only the GC (an environment contract) may change it. The
  expansion must refine the plain store for either flag value; the loaded value is defined as
  long as its bytes are (`GoFV.Proof.WB.load_flag`).
- **Helpers**: `runtime.wbZero`, `runtime.wbMove` = `Runtime.wbHelper` (no effect the semantics
  models; the zeroing/copy is the sequence's own `Zero`/`Move`). Calls clobber the caller's
  outgoing-arguments area (`callOp`), so sequences with helper calls are outside the
  writebarrier proof for now (#36).

Difftest additions (`tools/semdiff/prog/wb.go`): 12 functions storing pointers into heap objects
and through pointers (list building, struct/string fields, struct copies and clears, pointer
slices and arrays, `append` of strings), so `writebarrier` expands them in the later sections.

Results (`--n 100 --seed 3`): 237 functions, 23,700 calls; native agrees with every section on
23,698, every write-barrier function included; the 2 others are `makeBad` (§9.5). Corpus
(`sem-difftest corpus 2 1`, quick-v3 plain): 0 differ; 2 calls (1 function) fewer are defined at
section 0 than on main: 6 more section-0 runs are stuck on a write to the now read-only flag
(the runtime functions that switch the GC phase write it).

## 10. Open questions and risks

- **NaN encodings and the rules** (P4): IEEE 754 and the Go spec leave the encoding of a NaN
  result unspecified, and Go's optimisations rely on it. `generic.rules:1325-1326`
  (`Mul{32,64}F x (Const [-1])` → `Neg{32,64}F x`) is not a refinement under the semantics:
  a NaN `x` keeps its sign (and is quietened) under `FMUL`, but has its sign flipped under
  `FNEG`. The native difftest shows it (`x * -1` on NaN inputs: section 0 differs from native
  and from every section after `opt`). The semantics stays faithful to arm64 and these rules
  stay out of the proven set (upstream-candidate issue with a reproducer; the Go spec may leave
  a NaN's sign unspecified). `cse`'s argument sorting of commutative float ops is the other such
  optimisation; the semantics absorbs it (§4.6).
- **`VarDef` and `generic.rules:2159`, a model gap** (found by P4: the floats made `test/gcgort.newStructT`
  defined): `(Zero [s] p (VarDef {x} (Zero [s] p _)))` → the `VarDef` drops the second `Zero`,
  i.e. assumes `VarDef` keeps the variable's contents, while the semantics makes `VarDef`
  re-poison the variable (§3.4: "about to be initialised"; stack slots are merged across
  disjoint live ranges, which start at `VarDef`). Under the semantics the rule is not a
  refinement (the target returns poison: a gap in `sem-difftest corpus`). This is a **model
  gap**, not a Go bug: natively the two `Zero`s are adjacent on the memory chain and nothing can
  clobber the slot in between; only the semantics' re-poisoning `VarDef` is stricter than what
  Go relies on. The rule stays out of the proven set.

- **`SlicePtr` non-nil** (gO 521-523, `nilcheck.go:57-59`): `nilcheckelim` treats
  `SlicePtr` as non-nil, but `EqSlice` (`generic.rules:792`) shows it is used on nil slices.
  A `NilCheck (SlicePtr s)` removed on that assumption is only sound if the frontend never
  nil-checks the pointer of a possibly-nil slice. **P2 difftest**: `*unsafe.SliceData(s)` of a
  nil slice panics natively and in every section (the frontend uses `SlicePtrUnchecked` there,
  which is not assumed non-nil); no corpus run showed a `SlicePtr` case.
- `nilcheck.go:59` also treats `AddPtr`/`OffPtr`/`Add64`/`Sub64` results as non-nil
  ("unsafe pointer arithmetic generates non-nil pointers", golang/go#27180, a deliberate
  choice). **Seen by P2**: in 5 runtime functions (`(*bitvector).ptrbit`, `bitCursor.write`,
  `dumpbv`, `(*rwmutex).rlock`, `restoreGsignalStack`) a random call whose section 0 panics in a `NilCheck` of `nil + k` is
  `stuck` from section 13 (`nilcheckelim`) on: the check is gone and the access through
  `nil + k` is invalid (a load is `poison`, a store `stuck`). The criterion of §1 does
  not catch it (only the target's defined runs carry obligations), but the machine behaves
  like section 0: the access faults in page 0 and the runtime panics. Consequence for the proofs: the
  `nilcheckelim` theorem must take "no pointer arithmetic on nil" as a hypothesis, or the
  semantics must make an access within the first page of `Blk.nil` panic like a `NilCheck`
  (then `Load` is no longer pure); decide when proving `nilcheckelim`. **P3**: a `NilCheck`
  of any pointer into `Blk.nil` panics (§6), so `NilCheck (OffPtr (NilCheck p))` chains are
  removable (ProofMem, #23); the eliminations of a check whose argument is arithmetic on an
  unchecked pointer remain a hypothesis of the proof. With the P3 `NilCheck`, the corpus shows
  such a gap in 7 runtime functions: `(*bitvector).ptrbit`, `bitCursor.write`, `dumpbv`
  above, and `argv_index`, `getGodebugEarly`, `goenvs_unix`, `sysargs`, whose section 0 now
  panics in the check of `nil + k`.
  **Decided (#23, P4): accesses into `Blk.nil` do not panic.** A panicking `Load` would not be
  pure (Go's `deadcode`/`cse`/speculation delete, merge and hoist loads; only `NilCheck` panics
  in generic SSA), and it would not make `nilcheckelim`'s `If (IsNonNil p)` edge fact sound:
  for `p = nil + k` the check panics while `IsNonNil p` holds, and without the check the panic
  moves past intervening roots or disappears. The edge fact needs "no pointer into `Blk.nil`
  but nil": a hypothesis, or a pointer model whose `Blk.nil` holds only nil (arithmetic leaving
  offset 0 and nonzero integer addresses below 2^40 are `poison`), offered on #23.
- Tie-break of §3.6 step 3: `writebarrier`'s `storeOrder` and the post-lower scheduler order
  `NilCheck`s by position with an unstable sort (see `docs/PASSES.md`, writebarrier); the
  semantics' choice (NilChecks first) must match the order the final code panics in for the
  difftest. **P2**: no disagreement in the difftest (nil arguments to functions that store
  before and after dereferencing) nor between sections in the corpus.
- `Move` with partial overlap outside the inline-memmove rules: memmove semantics may be more
  defined than lowering for large moves; check that no pass creates such a `Move`.
- Store of `poison`: allowed (poison bytes). If a pass proof needs stores to observe defined
  values, tighten it to `stuck`.
- `Unknown` as `poison` vs `stuck` — **answered by P1**: `poison`. In the corpus `Unknown`
  occurs only in the first three sections (before `early deadcode`; 298 files), and is used
  mostly by `Phi`s (8,969 uses), then `MakeResult` (768), `NilCheck` (144), …: a `stuck`
  `Unknown` would make section 0 stuck wherever such a dead-code value is computed eagerly.
- Result types narrower than the op — **found and answered by P1**: §3.2 (`Val.retype`).
- Interface method calls need itab layouts and method tables; `rtype`/`reloc` export lines
  must be enough to resolve `InterLECall` targets — otherwise `stuck`.
- **Pointer-shaped aggregates** (#17): a one-field struct or one-element array of a pointer has
  the shape `.agg [(0, .ptr _)] 8`, but Go represents it as the bare pointer
  (`dec.rules:119`/`:120`: `(StructMake x) && x.Type.IsPtrShaped() => x`, interface data words).
  Those two rules are false under the semantics (`.agg [p]` vs `p`), and the interface itab word
  is `.int .w64` while Go also types `ITab` as `*uint8`, so `ITab`/`IMake` with a pointer-typed
  itab fail the validator's shape checks. Model gap, not a Go bug; a later change could make
  `Val.retype` at a one-field pointer-shaped aggregate wrap/unwrap.

## 11. Per-op table

Generated by `tmp/optable.py` + `tmp/optable_md.py` (throwaway scripts of the PassSurvey agent,
reading `genericOps.go` and the four generic rule files) and annotated by hand-written family
notes; the op list itself is the source's.

Columns: **gO line** = line in `genericOps.go`; **args** = `argLength` (−1 variadic); **aux**
= `aux` kind (`Bool` flags are the "bounded"/"not −1" promises); **type** = fixed result type
if the op declares one, else the value's type; **flags**: `comm` commutative, `call`, `se`
`hasSideEffects`, `nil` `nilCheck`; **cat**: `pure` (`evalPure`), `mem` (reads or produces a
memory snapshot, or orders against one), `call` (root acting on the environment), `data`
(SSA plumbing); **phase** §9 (`—` out of scope or never evaluated, `32b` not produced for
arm64); **rules** = number of rules in `generic/dec/divisible/divmod.rules` whose left-hand
side is rooted at the op (after `|` alternation expansion), `f` when one of them matches
constant arguments (a constant-folding rule: an executable cross-check of the semantics
against Go's own evaluation).

| Op | gO line | args | aux | type | flags | cat | phase | rules | semantics / corners |
|---|---|---|---|---|---|---|---|---|---|
| Last | 20 | -1 |  |  |  | data | — | 0 | rulegen pseudo-op, never in a Func: stuck (§4.9) |
| Add8 | 25 | 2 |  |  | comm | pure | P1 | 23f | mod 2^w (§4.1) |
| Add16 | 26 | 2 |  |  | comm | pure | P1 | 23f | mod 2^w (§4.1) |
| Add32 | 27 | 2 |  |  | comm | pure | P1 | 23f | mod 2^w (§4.1) |
| Add64 | 28 | 2 |  |  | comm | pure | P1 | 23f | mod 2^w (§4.1) |
| AddPtr | 29 | 2 |  |  |  | pure | P1 | 2 | ptr + int, keeps provenance (§3.3) |
| Add32F | 30 | 2 |  |  | comm | pure | P4 | 1f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Add64F | 31 | 2 |  |  | comm | pure | P4 | 1f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Sub8 | 33 | 2 |  |  |  | pure | P1 | 17f | mod 2^w (§4.1) |
| Sub16 | 34 | 2 |  |  |  | pure | P1 | 17f | mod 2^w (§4.1) |
| Sub32 | 35 | 2 |  |  |  | pure | P1 | 17f | mod 2^w (§4.1) |
| Sub64 | 36 | 2 |  |  |  | pure | P1 | 17f | mod 2^w (§4.1) |
| SubPtr | 37 | 2 |  |  |  | pure | P1 | 0 | ptr − ptr → int via concrete addresses (§3.3) |
| Sub32F | 38 | 2 |  |  |  | pure | P4 | 1f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Sub64F | 39 | 2 |  |  |  | pure | P4 | 1f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Mul8 | 41 | 2 |  |  | comm | pure | P1 | 11f | mod 2^w (§4.1) |
| Mul16 | 42 | 2 |  |  | comm | pure | P1 | 11f | mod 2^w (§4.1) |
| Mul32 | 43 | 2 |  |  | comm | pure | P1 | 11f | mod 2^w (§4.1) |
| Mul64 | 44 | 2 |  |  | comm | pure | P1 | 11f | mod 2^w (§4.1) |
| Mul32F | 45 | 2 |  |  | comm | pure | P4 | 4f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Mul64F | 46 | 2 |  |  | comm | pure | P4 | 4f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Div32F | 48 | 2 |  |  |  | pure | P4 | 2f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Div64F | 49 | 2 |  |  |  | pure | P4 | 2f | IEEE binary32/64, RNE, arm64 NaN rules (§4.6) |
| Hmul32 | 51 | 2 |  |  | comm | pure | P1 | 0 | high w bits of the 2w-bit product, signed/unsigned (§4.1) |
| Hmul32u | 52 | 2 |  |  | comm | pure | P1 | 0 | high w bits of the 2w-bit product, signed/unsigned (§4.1) |
| Hmul64 | 53 | 2 |  |  | comm | pure | P1 | 0 | high w bits of the 2w-bit product, signed/unsigned (§4.1) |
| Hmul64u | 54 | 2 |  |  | comm | pure | P1 | 0 | high w bits of the 2w-bit product, signed/unsigned (§4.1) |
| Mul32uhilo | 56 | 2 |  | (UInt32,UInt32) | comm | pure | P1 | 1f | tuple (hi, lo) of the unsigned 2w product |
| Mul64uhilo | 57 | 2 |  | (UInt64,UInt64) | comm | pure | P1 | 1f | tuple (hi, lo) of the unsigned 2w product |
| Mul32uover | 59 | 2 |  | (UInt32,Bool) | comm | pure | P1 | 3f | tuple (lo, overflowed?) |
| Mul64uover | 60 | 2 |  | (UInt64,Bool) | comm | pure | P1 | 3f | tuple (lo, overflowed?) |
| Avg32u | 67 | 2 |  | UInt32 |  | pure | 32b | 0 | 32-bit only; ⌊(a+b)/2⌋ exact; a<b ⇒ poison (§4.2) |
| Avg64u | 68 | 2 |  | UInt64 |  | pure | P1 | 0 | ⌊(a+b)/2⌋ in 65 bits; a<b ⇒ poison (comment: may assume a≥b) (§4.2) |
| Div8 | 72 | 2 |  |  |  | pure | P1 | 5f | trunc. signed; y=0 ⇒ poison; MIN/−1 = MIN (§4.2) |
| Div8u | 73 | 2 |  |  |  | pure | P1 | 3f | unsigned; y=0 ⇒ poison (§4.2) |
| Div16 | 74 | 2 | Bool |  |  | pure | P1 | 5f | trunc. signed; y=0 ⇒ poison; MIN/−1 = MIN; auxint=1 and (MIN,−1) ⇒ poison (§4.2) |
| Div16u | 75 | 2 |  |  |  | pure | P1 | 7f | unsigned; y=0 ⇒ poison (§4.2) |
| Div32 | 76 | 2 | Bool |  |  | pure | P1 | 7f | trunc. signed; y=0 ⇒ poison; MIN/−1 = MIN; auxint=1 and (MIN,−1) ⇒ poison (§4.2) |
| Div32u | 77 | 2 |  |  |  | pure | P1 | 10f | unsigned; y=0 ⇒ poison (§4.2) |
| Div64 | 78 | 2 | Bool |  |  | pure | P1 | 7f | trunc. signed; y=0 ⇒ poison; MIN/−1 = MIN; auxint=1 and (MIN,−1) ⇒ poison (§4.2) |
| Div64u | 79 | 2 |  |  |  | pure | P1 | 6f | unsigned; y=0 ⇒ poison (§4.2) |
| Div128u | 80 | 3 |  |  |  | pure | P1 | 1f | (hi:lo)/y → (q, r); y=0 or hi≥y ⇒ poison (bits.Div64 guards) (§4.2) |
| Mod8 | 83 | 2 |  |  |  | pure | P1 | 4f | sign of dividend; y=0 ⇒ poison; MIN%−1 = 0 (§4.2) |
| Mod8u | 84 | 2 |  |  |  | pure | P1 | 3f | unsigned; y=0 ⇒ poison (§4.2) |
| Mod16 | 85 | 2 | Bool |  |  | pure | P1 | 4f | sign of dividend; y=0 ⇒ poison; MIN%−1 = 0; auxint=1 and y=−1 ⇒ poison (§4.2) |
| Mod16u | 86 | 2 |  |  |  | pure | P1 | 3f | unsigned; y=0 ⇒ poison (§4.2) |
| Mod32 | 87 | 2 | Bool |  |  | pure | P1 | 4f | sign of dividend; y=0 ⇒ poison; MIN%−1 = 0; auxint=1 and y=−1 ⇒ poison (§4.2) |
| Mod32u | 88 | 2 |  |  |  | pure | P1 | 3f | unsigned; y=0 ⇒ poison (§4.2) |
| Mod64 | 89 | 2 | Bool |  |  | pure | P1 | 5f | sign of dividend; y=0 ⇒ poison; MIN%−1 = 0; auxint=1 and y=−1 ⇒ poison (§4.2) |
| Mod64u | 90 | 2 |  |  |  | pure | P1 | 3f | unsigned; y=0 ⇒ poison (§4.2) |
| And8 | 92 | 2 |  |  | comm | pure | P1 | 12f | bitwise (§4.1) |
| And16 | 93 | 2 |  |  | comm | pure | P1 | 12f | bitwise (§4.1) |
| And32 | 94 | 2 |  |  | comm | pure | P1 | 12f | bitwise (§4.1) |
| And64 | 95 | 2 |  |  | comm | pure | P1 | 12f | bitwise (§4.1) |
| Or8 | 97 | 2 |  |  | comm | pure | P1 | 20f | bitwise (§4.1) |
| Or16 | 98 | 2 |  |  | comm | pure | P1 | 20f | bitwise (§4.1) |
| Or32 | 99 | 2 |  |  | comm | pure | P1 | 20f | bitwise (§4.1) |
| Or64 | 100 | 2 |  |  | comm | pure | P1 | 20f | bitwise (§4.1) |
| Xor8 | 102 | 2 |  |  | comm | pure | P1 | 17f | bitwise (§4.1) |
| Xor16 | 103 | 2 |  |  | comm | pure | P1 | 17f | bitwise (§4.1) |
| Xor32 | 104 | 2 |  |  | comm | pure | P1 | 17f | bitwise (§4.1) |
| Xor64 | 105 | 2 |  |  | comm | pure | P1 | 17f | bitwise (§4.1) |
| Lsh8x8 | 112 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh8x16 | 113 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh8x32 | 114 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh8x64 | 115 | 2 | Bool |  |  | pure | P1 | 10f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh16x8 | 116 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh16x16 | 117 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh16x32 | 118 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh16x64 | 119 | 2 | Bool |  |  | pure | P1 | 10f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh32x8 | 120 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh32x16 | 121 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh32x32 | 122 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh32x64 | 123 | 2 | Bool |  |  | pure | P1 | 10f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh64x8 | 124 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh64x16 | 125 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh64x32 | 126 | 2 | Bool |  |  | pure | P1 | 3f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Lsh64x64 | 127 | 2 | Bool |  |  | pure | P1 | 10f | amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8x8 | 129 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8x16 | 130 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8x32 | 131 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8x64 | 132 | 2 | Bool |  |  | pure | P1 | 5f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16x8 | 133 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16x16 | 134 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16x32 | 135 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16x64 | 136 | 2 | Bool |  |  | pure | P1 | 6f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32x8 | 137 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32x16 | 138 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32x32 | 139 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32x64 | 140 | 2 | Bool |  |  | pure | P1 | 7f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64x8 | 141 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64x16 | 142 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64x32 | 143 | 2 | Bool |  |  | pure | P1 | 3f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64x64 | 144 | 2 | Bool |  |  | pure | P1 | 8f | arithmetic; amount unsigned; ≥A ⇒ sign fill; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8Ux8 | 146 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8Ux16 | 147 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8Ux32 | 148 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh8Ux64 | 149 | 2 | Bool |  |  | pure | P1 | 9f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16Ux8 | 150 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16Ux16 | 151 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16Ux32 | 152 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh16Ux64 | 153 | 2 | Bool |  |  | pure | P1 | 10f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32Ux8 | 154 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32Ux16 | 155 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32Ux32 | 156 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh32Ux64 | 157 | 2 | Bool |  |  | pure | P1 | 11f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64Ux8 | 158 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64Ux16 | 159 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64Ux32 | 160 | 2 | Bool |  |  | pure | P1 | 3f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Rsh64Ux64 | 161 | 2 | Bool |  |  | pure | P1 | 12f | logical; amount unsigned; ≥A ⇒ 0; auxint=1 and ≥A ⇒ poison (§4.3) |
| Eq8 | 164 | 2 |  | Bool | comm | pure | P1 | 19 | bit equality → Bool |
| Eq16 | 165 | 2 |  | Bool | comm | pure | P1 | 19 | bit equality → Bool |
| Eq32 | 166 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| Eq64 | 167 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| EqPtr | 168 | 2 |  | Bool | comm | pure | P1 | 18f | concrete address equality (§3.3) |
| EqInter | 169 | 2 |  | Bool |  | pure | P1 | 1 | compares itab words (generic.rules:790); frontend guarantees one side nil |
| EqSlice | 170 | 2 |  | Bool |  | pure | P1 | 1 | compares ptr words (generic.rules:792); frontend guarantees one side nil |
| Eq32F | 171 | 2 |  | Bool | comm | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Eq64F | 172 | 2 |  | Bool | comm | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Neq8 | 174 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| Neq16 | 175 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| Neq32 | 176 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| Neq64 | 177 | 2 |  | Bool | comm | pure | P1 | 17 | bit equality → Bool |
| NeqPtr | 178 | 2 |  | Bool | comm | pure | P1 | 18f | concrete address equality (§3.3) |
| NeqInter | 179 | 2 |  | Bool |  | pure | P1 | 1 | compares itab words (generic.rules:790); frontend guarantees one side nil |
| NeqSlice | 180 | 2 |  | Bool |  | pure | P1 | 1 | compares ptr words (generic.rules:792); frontend guarantees one side nil |
| Neq32F | 181 | 2 |  | Bool | comm | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Neq64F | 182 | 2 |  | Bool | comm | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Less8 | 184 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Less8U | 185 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Less16 | 186 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Less16U | 187 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Less32 | 188 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Less32U | 189 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Less64 | 190 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Less64U | 191 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Less32F | 192 | 2 |  | Bool |  | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Less64F | 193 | 2 |  | Bool |  | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Leq8 | 195 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Leq8U | 196 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Leq16 | 197 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Leq16U | 198 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Leq32 | 199 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Leq32U | 200 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Leq64 | 201 | 2 |  | Bool |  | pure | P1 | 9f | signed compare |
| Leq64U | 202 | 2 |  | Bool |  | pure | P1 | 6f | unsigned compare |
| Leq32F | 203 | 2 |  | Bool |  | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| Leq64F | 204 | 2 |  | Bool |  | pure | P4 | 1f | IEEE compare; NaN unordered (Neq true, others false) (§4.6) |
| CondSelect | 209 | 3 |  |  |  | pure | P1 | 25 | arg2 ? arg0 : arg1; unselected arm may be poison (§3.5) |
| AndB | 212 | 2 |  | Bool | comm | pure | P1 | 17 | Bool, parallel: `false` if either side is `false`, even `poison` (§3.5) |
| OrB | 213 | 2 |  | Bool | comm | pure | P1 | 27 | Bool, parallel: `true` if either side is `true`, even `poison` (§3.5) |
| EqB | 214 | 2 |  | Bool | comm | pure | P1 | 5f | Bool, both args evaluated (no short circuit) |
| NeqB | 215 | 2 |  | Bool | comm | pure | P1 | 5f | Bool, both args evaluated (no short circuit) |
| Not | 216 | 1 |  | Bool |  | pure | P1 | 7f | Bool, both args evaluated (no short circuit) |
| Neg8 | 219 | 1 |  |  |  | pure | P1 | 6f | mod 2^w / bitwise not (§4.1) |
| Neg16 | 220 | 1 |  |  |  | pure | P1 | 6f | mod 2^w / bitwise not (§4.1) |
| Neg32 | 221 | 1 |  |  |  | pure | P1 | 6f | mod 2^w / bitwise not (§4.1) |
| Neg64 | 222 | 1 |  |  |  | pure | P1 | 6f | mod 2^w / bitwise not (§4.1) |
| Neg32F | 223 | 1 |  |  |  | pure | — | 1f | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Neg64F | 224 | 1 |  |  |  | pure | — | 1f | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Com8 | 226 | 1 |  |  |  | pure | P1 | 3 | mod 2^w / bitwise not (§4.1) |
| Com16 | 227 | 1 |  |  |  | pure | P1 | 3 | mod 2^w / bitwise not (§4.1) |
| Com32 | 228 | 1 |  |  |  | pure | P1 | 3 | mod 2^w / bitwise not (§4.1) |
| Com64 | 229 | 1 |  |  |  | pure | P1 | 3 | mod 2^w / bitwise not (§4.1) |
| Ctz8 | 231 | 1 |  |  |  | pure | P1 | 2f | trailing zeros, ctz 0 = w; result type is v.Type (Int on arm64) |
| Ctz16 | 232 | 1 |  |  |  | pure | P1 | 2f | trailing zeros, ctz 0 = w; result type is v.Type (Int on arm64) |
| Ctz32 | 233 | 1 |  |  |  | pure | P1 | 2f | trailing zeros, ctz 0 = w; result type is v.Type (Int on arm64) |
| Ctz64 | 234 | 1 |  |  |  | pure | P1 | 2f | trailing zeros, ctz 0 = w; result type is v.Type (Int on arm64) |
| Ctz64On32 | 235 | 2 |  |  |  | pure | 32b | 0 | 32-bit only |
| Ctz8NonZero | 236 | 1 |  |  |  | pure | P1 | 0 | arg=0 ⇒ poison |
| Ctz16NonZero | 237 | 1 |  |  |  | pure | P1 | 0 | arg=0 ⇒ poison |
| Ctz32NonZero | 238 | 1 |  |  |  | pure | P1 | 0 | arg=0 ⇒ poison |
| Ctz64NonZero | 239 | 1 |  |  |  | pure | P1 | 0 | arg=0 ⇒ poison |
| BitLen8 | 240 | 1 |  |  |  | pure | P1 | 2f | w − clz; BitLen 0 = 0 |
| BitLen16 | 241 | 1 |  |  |  | pure | P1 | 2f | w − clz; BitLen 0 = 0 |
| BitLen32 | 242 | 1 |  |  |  | pure | P1 | 2f | w − clz; BitLen 0 = 0 |
| BitLen64 | 243 | 1 |  |  |  | pure | P1 | 2f | w − clz; BitLen 0 = 0 |
| Bswap16 | 245 | 1 |  |  |  | pure | P1 | 0 | byte swap |
| Bswap32 | 246 | 1 |  |  |  | pure | P1 | 0 | byte swap |
| Bswap64 | 247 | 1 |  |  |  | pure | P1 | 0 | byte swap |
| BitRev8 | 249 | 1 |  |  |  | pure | P1 | 0 | bit reverse |
| BitRev16 | 250 | 1 |  |  |  | pure | P1 | 0 | bit reverse |
| BitRev32 | 251 | 1 |  |  |  | pure | P1 | 0 | bit reverse |
| BitRev64 | 252 | 1 |  |  |  | pure | P1 | 0 | bit reverse |
| PopCount8 | 254 | 1 |  |  |  | pure | P1 | 2f | population count |
| PopCount16 | 255 | 1 |  |  |  | pure | P1 | 2f | population count |
| PopCount32 | 256 | 1 |  |  |  | pure | P1 | 2f | population count |
| PopCount64 | 257 | 1 |  |  |  | pure | P1 | 2f | population count |
| RotateLeft64 | 263 | 2 |  |  |  | pure | P1 | 10 | rotate by amount mod w (any amount width/sign) |
| RotateLeft32 | 264 | 2 |  |  |  | pure | P1 | 10 | rotate by amount mod w (any amount width/sign) |
| RotateLeft16 | 265 | 2 |  |  |  | pure | P1 | 10 | rotate by amount mod w (any amount width/sign) |
| RotateLeft8 | 266 | 2 |  |  |  | pure | P1 | 10 | rotate by amount mod w (any amount width/sign) |
| Sqrt | 274 | 1 |  |  |  | pure | P4 | 1 | IEEE sqrt (§4.6) |
| Sqrt32 | 275 | 1 |  |  |  | pure | P4 | 0 | IEEE sqrt (§4.6) |
| Floor | 282 | 1 |  |  |  | pure | P4 | 1f | float64 round-to-integral (§4.6) |
| Ceil | 283 | 1 |  |  |  | pure | P4 | 1f | float64 round-to-integral (§4.6) |
| Trunc | 284 | 1 |  |  |  | pure | P4 | 1f | float64 round-to-integral (§4.6) |
| Round | 285 | 1 |  |  |  | pure | P4 | 0 | float64 round-to-integral (§4.6) |
| RoundToEven | 286 | 1 |  |  |  | pure | P4 | 1f | float64 round-to-integral (§4.6) |
| Abs | 289 | 1 |  |  |  | pure | P4 | 0 | sign bit only (§4.6) |
| Copysign | 290 | 2 |  |  |  | pure | P4 | 0 | sign bit only (§4.6) |
| Min64 | 293 | 2 |  |  |  | pure | P1 | 0 | integer min/max |
| Max64 | 294 | 2 |  |  |  | pure | P1 | 0 | integer min/max |
| Min64u | 295 | 2 |  |  |  | pure | P1 | 0 | integer min/max |
| Max64u | 296 | 2 |  |  |  | pure | P1 | 0 | integer min/max |
| Min64F | 299 | 2 |  |  |  | pure | P4 | 0 | Go min/max: NaN if any NaN, −0 < +0 (§4.6) |
| Min32F | 300 | 2 |  |  |  | pure | P4 | 0 | Go min/max: NaN if any NaN, −0 < +0 (§4.6) |
| Max64F | 301 | 2 |  |  |  | pure | P4 | 0 | Go min/max: NaN if any NaN, −0 < +0 (§4.6) |
| Max32F | 302 | 2 |  |  |  | pure | P4 | 0 | Go min/max: NaN if any NaN, −0 < +0 (§4.6) |
| FMA | 316 | 3 |  |  |  | pure | P4 | 0 | fused a*b+c, single rounding (§4.6) |
| Phi | 319 | -1 |  |  |  | data | P1 | 5f | value of the arg for the entry edge; parallel (§3.6) |
| Copy | 320 | 1 |  |  |  | data | P1 | 0 | identity |
| Convert | 329 | 2 |  |  |  | mem | P2 | 3 | ptr↔uintptr; int→ptr recovers provenance (§3.3) |
| ConstBool | 333 | 0 | Bool |  |  | pure | P1 | 0 | auxint 0/1 |
| ConstString | 334 | 0 | String |  |  | pure | P2 | 4 | aux string → (rodata ptr, len); needs symbol data (§3.4) |
| ConstNil | 335 | 0 |  | BytePtr |  | pure | P2 | 0 | nil pointer |
| Const8 | 336 | 0 | Int8 |  |  | pure | P1 | 0 | auxint sign-extended, low w bits |
| Const16 | 337 | 0 | Int16 |  |  | pure | P1 | 0 | auxint sign-extended, low w bits |
| Const32 | 338 | 0 | Int32 |  |  | pure | P1 | 0 | auxint sign-extended, low w bits |
| Const64 | 341 | 0 | Int64 |  |  | pure | P1 | 0 | auxint sign-extended, low w bits |
| Const32F | 347 | 0 | Float32 |  |  | pure | P4 | 0 | auxint = float64 bits of a float32-exact value; no NaN |
| Const64F | 348 | 0 | Float64 |  |  | pure | P4 | 0 | auxint = float64 bits; no NaN |
| ConstInterface | 349 | 0 |  |  |  | pure | P2 | 1 | nil interface / nil slice |
| ConstSlice | 350 | 0 |  |  |  | pure | P2 | 2 | nil interface / nil slice |
| InitMem | 353 | 0 |  |  |  | mem | P2 | 0 | entry memory of the activation (§3.4) |
| Arg | 354 | 0 | SymOff |  |  | pure | P2 | 0 | pre-expand: (part of) a Go-typed parameter, aux=*ir.Name, auxint=offset (§5) |
| ArgIntReg | 358 | 0 | NameOffsetInt8 |  |  | pure | P3 | 0 | post-expand: register parameter piece (§5) |
| ArgFloatReg | 359 | 0 | NameOffsetInt8 |  |  | pure | P3 | 0 | post-expand: register parameter piece (§5) |
| Addr | 366 | 1 | Sym |  |  | pure | P1 | 0 | address of global aux *obj.LSym (arg0=SB) |
| LocalAddr | 367 | 2 | Sym |  |  | mem | P2 | 0 | address of auto aux *ir.Name (arg0=SP, arg1=mem orders it) (§3.4) |
| SP | 369 | 0 |  |  |  | pure | P2 | 0 | frame pointer of the activation (outgoing args area post-expand) |
| SB | 370 | 0 |  | Uintptr |  | pure | P2 | 0 | static base; only used as Addr base |
| Invalid | 371 | 0 |  |  |  | data | — | 0 | stuck if evaluated |
| SPanchored | 372 | 2 |  | Uintptr |  | mem | P2 | 0 | = arg0 (arg1 orders it) |
| Load | 375 | 2 |  |  |  | mem | P2 | 40 | typed load of v.Type from snapshot arg1; invalid address ⇒ poison (§3.4) |
| Dereference | 376 | 2 |  |  |  | mem | P2 | 0 | byte blob of a non-SSA-able value (call args/results only) (§5) |
| Store | 377 | 3 | Typ | Mem |  | mem | P2 | 29 | store aux type's bytes; invalid address ⇒ stuck (§3.4) |
| LoadMasked8 | 381 | 3 |  |  |  | mem | — | 0 | SIMD-only masked access; out of scope |
| LoadMasked16 | 382 | 3 |  |  |  | mem | — | 0 | SIMD-only masked access; out of scope |
| LoadMasked32 | 383 | 3 |  |  |  | mem | — | 0 | SIMD-only masked access; out of scope |
| LoadMasked64 | 384 | 3 |  |  |  | mem | — | 0 | SIMD-only masked access; out of scope |
| StoreMasked8 | 385 | 4 | Typ | Mem |  | mem | — | 0 | SIMD-only masked access; out of scope |
| StoreMasked16 | 386 | 4 | Typ | Mem |  | mem | — | 0 | SIMD-only masked access; out of scope |
| StoreMasked32 | 387 | 4 | Typ | Mem |  | mem | — | 0 | SIMD-only masked access; out of scope |
| StoreMasked64 | 388 | 4 | Typ | Mem |  | mem | — | 0 | SIMD-only masked access; out of scope |
| Move | 402 | 3 | TypSize | Mem |  | mem | P2 | 25 | memmove auxint bytes (overlap: loads before stores) (§3.4) |
| Zero | 403 | 2 | TypSize | Mem |  | mem | P2 | 6 | write auxint zero bytes (§3.4) |
| StoreWB | 407 | 3 | Typ | Mem |  | mem | P3 | 0 | as Store/Move/Zero (write barrier is GC-only) (§3.4) |
| MoveWB | 408 | 3 | TypSize | Mem |  | mem | P3 | 0 | as Store/Move/Zero (write barrier is GC-only) (§3.4) |
| ZeroWB | 409 | 2 | TypSize | Mem |  | mem | P3 | 0 | as Store/Move/Zero (write barrier is GC-only) (§3.4) |
| WBend | 410 | 1 |  | Mem |  | mem | P3 | 0 | frees the write-barrier buffer `Blk.wbuf` (§9.6) |
| WB | 416 | 1 | Int64 | (BytePtr,Mem) |  | mem | P3 | 0 | pure: (`⟨wbuf,0⟩`, mem with a fresh poison buffer of 8·auxint bytes) (§9.6) |
| HasCPUFeature | 418 | 0 | Sym | bool |  | pure | P5 | 0 | reads runtime feature flag: Env (P5) |
| PanicBounds | 425 | 3 | Int64 | Mem | call | call | P1 | 0 | outcome panicked(bounds kind=auxint, idx, len) (§6) |
| PanicExtend | 426 | 4 | Int64 | Mem | call | call | 32b | 0 | 32-bit only; as PanicBounds with 64-bit index |
| ClosureCall | 452 | -1 | CallOff |  | call | call | P3 | 0 | post-expand call: ABI decode → Env/program callee → ABI encode (§5) |
| StaticCall | 453 | -1 | CallOff |  | call | call | P3 | 1 | post-expand call: ABI decode → Env/program callee → ABI encode (§5) |
| InterCall | 454 | -1 | CallOff |  | call | call | P3 | 0 | post-expand call: ABI decode → Env/program callee → ABI encode (§5) |
| TailCall | 455 | -1 | CallOff |  | call | call | P3 | 0 | post-expand tail call; RetJmp control (§5, §7) |
| TailCallInter | 456 | -1 | CallOff |  | call | call | P3 | 0 | post-expand tail call; RetJmp control (§5, §7) |
| ClosureLECall | 458 | -1 | CallOff |  | call | call | P3 | 0 | pre-expand call on Go-typed values (§5) |
| StaticLECall | 459 | -1 | CallOff |  | call | call | P3 | 23 | pre-expand call on Go-typed values (§5) |
| InterLECall | 460 | -1 | CallOff |  | call | call | P3 | 1 | pre-expand call on Go-typed values (§5) |
| TailLECall | 461 | -1 | CallOff |  | call | call | P3 | 0 | pre-expand tail call (§5, §7) |
| TailLECallInter | 462 | -1 | CallOff |  | call | call | P3 | 0 | pre-expand tail call (§5, §7) |
| SignExt8to16 | 465 | 1 |  | Int16 |  | pure | P1 | 3f | sign extension |
| SignExt8to32 | 466 | 1 |  | Int32 |  | pure | P1 | 3f | sign extension |
| SignExt8to64 | 467 | 1 |  | Int64 |  | pure | P1 | 3f | sign extension |
| SignExt16to32 | 468 | 1 |  | Int32 |  | pure | P1 | 2f | sign extension |
| SignExt16to64 | 469 | 1 |  | Int64 |  | pure | P1 | 2f | sign extension |
| SignExt32to64 | 470 | 1 |  | Int64 |  | pure | P1 | 2f | sign extension |
| ZeroExt8to16 | 471 | 1 |  | UInt16 |  | pure | P1 | 2f | zero extension |
| ZeroExt8to32 | 472 | 1 |  | UInt32 |  | pure | P1 | 2f | zero extension |
| ZeroExt8to64 | 473 | 1 |  | UInt64 |  | pure | P1 | 2f | zero extension |
| ZeroExt16to32 | 474 | 1 |  | UInt32 |  | pure | P1 | 2f | zero extension |
| ZeroExt16to64 | 475 | 1 |  | UInt64 |  | pure | P1 | 2f | zero extension |
| ZeroExt32to64 | 476 | 1 |  | UInt64 |  | pure | P1 | 2f | zero extension |
| Trunc16to8 | 477 | 1 |  |  |  | pure | P1 | 4f | keep low bits |
| Trunc32to8 | 478 | 1 |  |  |  | pure | P1 | 4f | keep low bits |
| Trunc32to16 | 479 | 1 |  |  |  | pure | P1 | 6f | keep low bits |
| Trunc64to8 | 480 | 1 |  |  |  | pure | P1 | 4f | keep low bits |
| Trunc64to16 | 481 | 1 |  |  |  | pure | P1 | 6f | keep low bits |
| Trunc64to32 | 482 | 1 |  |  |  | pure | P1 | 8f | keep low bits |
| Cvt32to32F | 484 | 1 |  |  |  | pure | P4 | 1f | signed int → float, RNE |
| Cvt32to64F | 485 | 1 |  |  |  | pure | P4 | 1f | signed int → float, RNE |
| Cvt64to32F | 486 | 1 |  |  |  | pure | P4 | 1f | signed int → float, RNE |
| Cvt64to64F | 487 | 1 |  |  |  | pure | P4 | 1f | signed int → float, RNE |
| Cvt32Fto32 | 488 | 1 |  |  |  | pure | P4 | 1f | trunc toward 0; NaN/out of range: arm64 FCVTZS (saturate, NaN→0) (§4.6) |
| Cvt32Fto64 | 489 | 1 |  |  |  | pure | P4 | 1f | trunc toward 0; NaN/out of range: arm64 FCVTZS (saturate, NaN→0) (§4.6) |
| Cvt64Fto32 | 490 | 1 |  |  |  | pure | P4 | 1f | trunc toward 0; NaN/out of range: arm64 FCVTZS (saturate, NaN→0) (§4.6) |
| Cvt64Fto64 | 491 | 1 |  |  |  | pure | P4 | 1f | trunc toward 0; NaN/out of range: arm64 FCVTZS (saturate, NaN→0) (§4.6) |
| Cvt32Fto64F | 492 | 1 |  |  |  | pure | P4 | 1f | exact widening (sNaN quietened) |
| Cvt64Fto32F | 493 | 1 |  |  |  | pure | P4 | 2f | RNE narrowing |
| CvtBoolToUint8 | 494 | 1 |  |  |  | pure | P1 | 2f | 0/1 |
| Round32F | 497 | 1 |  |  |  | pure | P4 | 1 | identity on exact bit patterns (forces rounding on x87-like targets) |
| Round64F | 498 | 1 |  |  |  | pure | P4 | 1 | identity on exact bit patterns (forces rounding on x87-like targets) |
| IsNonNil | 501 | 1 |  | Bool |  | pure | P2 | 5f | ptr ≠ nil |
| IsInBounds | 502 | 2 |  | Bool |  | pure | P2 | 29f | 0 ≤ a < b (unsigned a < b; b ≥ 0 guaranteed) |
| IsSliceInBounds | 503 | 2 |  | Bool |  | pure | P2 | 8f | 0 ≤ a ≤ b (unsigned a ≤ b) |
| NilCheck | 504 | 2 |  |  | nil | mem | P2 | 8 | root: arg0 = nil ⇒ panicked(nil deref), else arg0 (§6) |
| GetG | 507 | 1 |  |  |  | mem | P3 | 0 | current g pointer: Env-provided opaque pointer (P3) |
| GetClosurePtr | 508 | 0 |  |  |  | pure | P2 | 0 | closure context of the activation (entry state) |
| GetCallerPC | 509 | 0 |  |  |  | pure | P3 | 0 | Env-provided opaque (P5) |
| GetCallerSP | 510 | 1 |  |  |  | mem | P3 | 0 | Env-provided opaque (P5) |
| PtrIndex | 513 | 2 |  |  |  | pure | P2 | 2 | ptr + sizeof(elem(v.Type))·idx, keeps provenance |
| OffPtr | 514 | 1 | Int64 |  |  | pure | P2 | 2 | ptr + auxint, keeps provenance |
| SliceMake | 517 | 3 |  |  |  | pure | P2 | 2 | slice (ptr, len, cap) |
| SlicePtr | 518 | 1 |  | BytePtr |  | pure | P2 | 3 | ptr field; nilcheckelim assumes non-nil (open: §10) |
| SliceLen | 519 | 1 |  |  |  | pure | P2 | 7 | len/cap field |
| SliceCap | 520 | 1 |  |  |  | pure | P2 | 7 | len/cap field |
| SlicePtrUnchecked | 524 | 1 |  |  |  | pure | P2 | 1 | ptr field, may be nil |
| ComplexMake | 527 | 2 |  |  |  | pure | P1 | 0 | complex (re, im) |
| ComplexReal | 528 | 1 |  |  |  | pure | P1 | 3 | component |
| ComplexImag | 529 | 1 |  |  |  | pure | P1 | 3 | component |
| StringMake | 532 | 2 |  |  |  | pure | P2 | 0 | string (ptr, len) |
| StringPtr | 533 | 1 |  | BytePtr |  | pure | P2 | 3 | component |
| StringLen | 534 | 1 |  | Int |  | pure | P2 | 3 | component |
| IMake | 537 | 2 |  |  |  | pure | P2 | 4 | interface (itab/type word, data word) |
| ITab | 538 | 1 |  | Uintptr |  | pure | P2 | 2 | component |
| IData | 539 | 1 |  |  |  | pure | P2 | 2 | component |
| StructMake | 542 | -1 |  |  |  | pure | P2 | 1 | struct of the args (field order) |
| StructSelect | 543 | 1 | Int64 |  |  | pure | P2 | 9 | field auxint |
| ArrayMake1 | 546 | 1 |  |  |  | pure | P2 | 1 | 1-element array |
| ArraySelect | 547 | 1 | Int64 |  |  | pure | P2 | 6 | element auxint |
| StoreReg | 553 | 1 |  |  |  | pure | — | 0 | regalloc only; identity |
| LoadReg | 554 | 1 |  |  |  | pure | — | 0 | regalloc only; identity |
| FwdRef | 557 | 0 | Sym |  |  | data | — | 0 | SSA construction only; stuck |
| Unknown | 560 | 0 |  |  |  | data | P1 | 0 | poison (§3.5) |
| VarDef | 562 | 1 | Sym | Mem |  | mem | P2 | 0 | mem: bytes of auto aux become uninitialised (poison) (§3.4) |
| VarLive | 564 | 1 | Sym |  |  | mem | P2 | 0 | identity on mem |
| KeepAlive | 565 | 2 |  | Mem |  | mem | P2 | 0 | identity on mem (arg0 must be evaluated) |
| InlMark | 569 | 1 | Int32 | Void |  | pure | P2 | 0 | no effect (Void) |
| Int64Make | 572 | 2 |  | UInt64 |  | pure | 32b | 0 | 32-bit (dec64) only |
| Int64Hi | 573 | 1 |  | UInt32 |  | pure | 32b | 0 | 32-bit (dec64) only |
| Int64Lo | 574 | 1 |  | UInt32 |  | pure | 32b | 0 | 32-bit (dec64) only |
| Add32carry | 576 | 2 |  | (UInt32,Flags) | comm | pure | 32b | 0 | 32-bit (dec64) only; Flags tuple |
| Add32withcarry | 577 | 3 |  |  | comm | pure | 32b | 0 | 32-bit (dec64) only; Flags tuple |
| Add32carrywithcarry | 578 | 3 |  | (UInt32,Flags) | comm | pure | 32b | 0 | 32-bit (dec64) only; Flags tuple |
| Sub32carry | 580 | 2 |  | (UInt32,Flags) |  | pure | 32b | 0 | 32-bit (dec64) only; Flags tuple |
| Sub32withcarry | 581 | 3 |  |  |  | pure | 32b | 0 | 32-bit (dec64) only; Flags tuple |
| Add64carry | 583 | 3 |  | (UInt64,UInt64) | comm | pure | P1 | 1f | (x+y+c mod 2^64, carry); c∉{0,1} ⇒ poison |
| Sub64borrow | 584 | 3 |  | (UInt64,UInt64) |  | pure | P1 | 0 | (x−y−c mod 2^64, borrow); c∉{0,1} ⇒ poison |
| Signmask | 586 | 1 |  | Int32 |  | pure | 32b | 0 | 32-bit only |
| Zeromask | 587 | 1 |  | UInt32 |  | pure | 32b | 0 | 32-bit only |
| Slicemask | 588 | 1 |  |  |  | pure | P1 | 4f | 0 if 0, −1 if >0; <0 ⇒ poison (comment: undef) |
| SpectreIndex | 590 | 2 |  |  |  | pure | P2 | 0 | arg0 if in range else 0 |
| SpectreSliceIndex | 591 | 2 |  |  |  | pure | P2 | 0 | arg0 if in range else 0 |
| Cvt32Uto32F | 593 | 1 |  |  |  | pure | 32b | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt32Uto64F | 594 | 1 |  |  |  | pure | 32b | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt32Fto32U | 595 | 1 |  |  |  | pure | 32b | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt64Fto32U | 596 | 1 |  |  |  | pure | 32b | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt64Uto32F | 597 | 1 |  |  |  | pure | P4 | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt64Uto64F | 598 | 1 |  |  |  | pure | P4 | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt32Fto64U | 599 | 1 |  |  |  | pure | P4 | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Cvt64Fto64U | 600 | 1 |  |  |  | pure | P4 | 0 | unsigned conversions (32U forms 32-bit only); out of range: arm64 (§4.6) |
| Select0 | 603 | 1 |  |  |  | pure | P1 | 2 | tuple component |
| Select1 | 604 | 1 |  |  |  | pure | P1 | 1 | tuple component |
| MakeTuple | 605 | 2 |  |  |  | pure | P1 | 0 | tuple |
| SelectN | 606 | 1 | Int64 |  |  | pure | P2 | 10 | member auxint of a call Result / Results tuple |
| SelectNAddr | 607 | 1 | Int64 |  |  | pure | P2 | 0 | address of result auxint of a pre-expand call (§5) |
| MakeResult | 608 | -1 |  |  |  | pure | P2 | 0 | Ret control: results + mem (§7) |
| AtomicLoad8 | 614 | 2 |  | (UInt8,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicLoad32 | 615 | 2 |  | (UInt32,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicLoad64 | 616 | 2 |  | (UInt64,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicLoadPtr | 617 | 2 |  | (BytePtr,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicLoadAcq32 | 618 | 2 |  | (UInt32,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicLoadAcq64 | 619 | 2 |  | (UInt64,Mem) |  | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore8 | 620 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore32 | 621 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore64 | 622 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStorePtrNoWB | 623 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStoreRel32 | 624 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStoreRel64 | 625 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange8 | 626 | 3 |  | (UInt8,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange32 | 627 | 3 |  | (UInt32,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange64 | 628 | 3 |  | (UInt64,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAdd32 | 629 | 3 |  | (UInt32,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAdd64 | 630 | 3 |  | (UInt64,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicCompareAndSwap32 | 631 | 4 |  | (Bool,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicCompareAndSwap64 | 632 | 4 |  | (Bool,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicCompareAndSwapRel32 | 633 | 4 |  | (Bool,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd8 | 636 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr8 | 637 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd32 | 638 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr32 | 639 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd64value | 642 | 3 |  | (Uint64, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd32value | 643 | 3 |  | (Uint32, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd8value | 644 | 3 |  | (Uint8, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr64value | 645 | 3 |  | (Uint64, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr32value | 646 | 3 |  | (Uint32, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr8value | 647 | 3 |  | (Uint8, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore8Variant | 654 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore32Variant | 655 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicStore64Variant | 656 | 3 |  | Mem | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAdd32Variant | 658 | 3 |  | (UInt32,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAdd64Variant | 659 | 3 |  | (UInt64,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange8Variant | 660 | 3 |  | (UInt8,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange32Variant | 661 | 3 |  | (UInt32,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicExchange64Variant | 662 | 3 |  | (UInt64,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicCompareAndSwap32Variant | 663 | 4 |  | (Bool,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicCompareAndSwap64Variant | 664 | 4 |  | (Bool,Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd64valueVariant | 665 | 3 |  | (Uint64, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr64valueVariant | 666 | 3 |  | (Uint64, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd32valueVariant | 667 | 3 |  | (Uint32, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr32valueVariant | 668 | 3 |  | (Uint32, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicAnd8valueVariant | 669 | 3 |  | (Uint8, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| AtomicOr8valueVariant | 670 | 3 |  | (Uint8, Mem) | se | mem | P5 | 0 | sequential (single-thread) load/store/RMW; misaligned ⇒ stuck (P5) |
| PubBarrier | 673 | 1 |  |  | se | mem | P5 | 0 | identity on mem |
| Clobber | 676 | 0 | SymOff | Void |  | pure | — | 0 | clobberdead debug flag only; out of scope |
| ClobberReg | 677 | 0 |  | Void |  | pure | — | 0 | clobberdead debug flag only; out of scope |
| PrefetchCache | 680 | 2 |  |  | se | mem | P5 | 0 | identity on mem |
| PrefetchCacheStreamed | 681 | 2 |  |  | se | mem | P5 | 0 | identity on mem |
| MemEq | 684 | 4 |  | Bool | comm | mem | P2 | 11 | runtime.memequal(arg0, arg1, arg2) on snapshot arg3 |
| Empty | 687 | 0 |  |  |  | pure | P2 | 0 | zero-sized value |
| ZeroSIMD | 690 | 0 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt16toMask8x16 | 693 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt32toMask8x32 | 694 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt64toMask8x64 | 695 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask16x8 | 696 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt16toMask16x16 | 697 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt32toMask16x32 | 698 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask32x4 | 699 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask32x8 | 700 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt16toMask32x16 | 701 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask64x2 | 702 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask64x4 | 703 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| Cvt8toMask64x8 | 704 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask8x16to16 | 707 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask8x32to32 | 708 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask8x64to64 | 709 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask16x8to8 | 710 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask16x16to16 | 711 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask16x32to32 | 712 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask32x4to8 | 713 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask32x8to8 | 714 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask32x16to16 | 715 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask64x2to8 | 716 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask64x4to8 | 717 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| CvtMask64x8to8 | 718 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsZeroVec | 721 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat32x4 | 724 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat32x8 | 725 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat32x16 | 726 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat64x2 | 727 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat64x4 | 728 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
| IsNaNFloat64x8 | 729 | 1 |  |  |  | pure | — | 0 | SIMD; out of scope (GOEXPERIMENT=simd only) |
