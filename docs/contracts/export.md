# Contract: per-pass SSA export (`gofv-ssa` v1)

Owner: Exporter (issue #4). Consumers: LeanIR (parser/printer, #21), RulesExport (#22), every
pass port (G4). Changing the format bumps the version in the first line and is announced on #4.

The patched `go1.27.3` compiler (`patches/go/*.patch`, built by `scripts/build-go.sh` into
`third_party/go-build`) writes, for each selected function, the complete SSA state the
machine-independent passes can observe:

- section 0, `start`: the function as `ssagen` hands it to `ssa.Compile`, i.e. the input of
  `number lines`;
- one section after every pass that runs, from `number lines` up to and including the last pass
  before `lower` (so the last section is the input of `lower`). Passes that are disabled
  (`insert resched checks` unless `GOEXPERIMENT=preemptibleloops`; `cpufeatures`,
  `rewrite tern` without `GOEXPERIMENT=simd`) or skipped (non-required passes under `-N`) have no
  section. Each section names its pass, so the pass list is self-describing.

Parity of a Lean pass `p` is checked as: parse sections `0..k-1` (definitions accumulate, see
below), take the state of section `k-1`, run `p`, compare with section `k`.

## Switching it on

| Variable | Meaning |
| --- | --- |
| `GOFV_SSA_EXPORT=<dir>` | enable; files go under `<dir>` (created if missing) |
| `GOFV_SSA_PKG=<regexp>` | only packages whose import path matches (unanchored; default all) |
| `GOFV_SSA_FUNC=<regexp>` | only functions whose `<pkgpath>.<f.Name>` matches (unanchored; default all) |
| `GOFV_SSA_GOTEXT=1` | also write Go's own `f.String()` after each section to `<file>.txt` (printer cross-check) |

Without `GOFV_SSA_EXPORT` the patched compiler behaves exactly like the stock one. With it,
the exporter only reads compiler state: it never calls caching accessors (`f.Postorder()`,
`f.Idom()`, …), never computes type sizes (`types.CalcSize` is disabled in the backend), and
never creates symbols, so the compiled code is unchanged.

One file per function: `<dir>/<pkgpath>/<name>,<abi>.ssa`, where `<pkgpath>` keeps its `/`
as directory separators and `<name>` is `f.Name` with every byte outside `[A-Za-z0-9._-]`
written as `%XX` (two upper-case hex digits); `<abi>` is `f.ABISelf.Which()` (0 = ABI0,
1 = ABIInternal). `main` packages of different programs collide, so drive one program per
export directory (`scripts/export-corpus.sh` does). If a name repeats within one compile the
second file gets `#2` before `.ssa`, and so on.

The output is deterministic: the same compile produces byte-identical files (checked by
`scripts/export-corpus.sh --check-determinism`).

## Lexical format

- ASCII text, `\n` line ends, no trailing spaces, no blank lines. One record per line; the first
  token is the record tag.
- Tokens are separated by one space. A token starting with `"` is a string: it runs to the next
  unescaped `"` and may contain spaces. Inside a string, bytes 0x20–0x7e except `"` and `\` are
  literal; every other byte is written `\xHH` (two lower-case hex digits), `"` as `\"`, `\` as
  `\\`. Strings are byte strings (Go strings need not be UTF-8).
- Integers are decimal, signed where the Go field is signed. `-` means "none" (nil pointer, empty
  list). `?` means "not available" (see `size` below).
- References carry a one-letter prefix: `v<ID>` value, `b<ID>` block, `t<n>` type, `a<n>` aux,
  `s<n>` local slot, `p<n>` position base. Value and block IDs are the Go IDs. Type, aux, slot
  and position-base numbers are per-file table indices (`t`, `a`, `s` from 1, assigned in
  first-use order while the sections are written; `p` is the Go `XPos` index itself).
- Lists are comma-separated without spaces (`v3,v4`); the empty list is `-`.
- A position `pos` is `p<index>:<line>:<col>:<stmt>:<xlogue>`, the fields of Go's
  `src.XPos{index, lico}`: `lico = line<<12 | col<<4 | xlogue<<2 | stmt` (`lineBits = 20`,
  `colBits = 8`). `stmt`: 0 `PosDefaultStmt`, 1 `PosIsStmt`, 2 `PosNotStmt`. `XPos.Before`
  compares `(index, lico)` lexicographically; `SameFileAndLine` compares `index` and `line`.
  `p0:0:0:0:0` is `src.NoXPos`.

## File layout

```
gofv-ssa 1
pkg "<base.Ctxt.Pkgpath>"
func "<f.Name>" <abi> <nosplit 0|1> <pgohot 0|1>
config <key> <value>                  (one line per key; table below)
<section 0>
<section 1>
…
typeorder <group> <group> …
eof
```

A section:

```
pass <k> "<pass name>"                  (k = 0 for "start")
<definitions: posbase / type / field / aux / abiparam / reloc / rtype / slot lines>
f <entry b> <type t> <ownaux a> <vid.last> <bid.last>
b …                                   (one per block, in f.Blocks order)
v …                                   (the block's values, in b.Values order, right after their b line)
…
names <s,…>                           (f.Names, in order)
named <s> <v,…>                       (f.NamedValues[*s] for each s in f.Names, in that order)
namedx <slot> <v,…>                   (NamedValues keys not in f.Names, if any; inline slot, see below)
splits <entries>                      (f.CanonicalLocalSplits)
canon <entries>                       (f.CanonicalLocalSlots)
consts <entries>                      (f.constants)
freev <v,…>                           (f.freeValues free list, head first)
freeb <b,…>                           (f.freeBlocks free list, head first)
cache <name> <payload>                (f.cached*, only those that are non-nil)
end
```

### Definitions (tables)

Every type, aux object, local slot and position base referenced by a section is defined before
the `f` line of the first section that references it (references inside definitions are
defined earlier in the same section or before). A definition stays valid for later sections.
Aux objects that Go mutates in place (an `*AuxCall` whose `Fn` is rewritten by
`devirtLECall`, `expand calls` filling in ABI data, …) are **redefined** with the same number
in every section where their content differs from the last definition; a reader keeps the
latest one. Identity is Go identity: two references share a number iff the Go values are
`==` (pointer identity for pointer-typed aux, value equality for `stringAux` and friends, pointer
identity for `*types.Type` and `*LocalSlot`). This is what `Value.Aux != w.Aux`,
`v.Type == w.Type` and CSE's `auxmap` observe.

Objects first created by pass `k` are numbered while section `k` is written (block order, then
value order, then names, …), so a Lean pass creating new objects must match them to section
`k`'s definitions by content (or up to renaming), not by number.

`posbase p<index> "<abs filename>" <line> <col> <inl>`: the `src.PosBase` of `XPos` index
`<index>` (`base.Ctxt.PosTable`): absolute file name, base line/column (line directives), and
`InliningIndex()` (−1 if not inlined; `deadcode` keeps an `InlMark` iff some live position has
its `AuxInt` as inlining index).

`type t<n> <kind> <size> <align> <ptrdata> <flags> "<t.String()>" <kind-specific>`

- `kind`: `types.Kind` without the `T` prefix (`INT8`, `PTR`, `STRUCT`, `SSA`, `TUPLE`,
  `RESULTS`, `FUNC`, …).
- `size`, `align`, `ptrdata`: `t.Size()`, `t.Alignment()`, `types.PtrDataSize(t)`, or `?` when
  the size was never calculated by the compiler (`widthCalculated()` false); `ptrdata` is `?`
  as well for `SSA`/`TUPLE`/`RESULTS` kinds.
- `flags`: comma list from `hasptr` (`t.HasPointers()`), `notinheap`, `noalg`, `shape`,
  `direct` (`types.IsDirectIface`), `comparable` (`types.IsComparable`), `named`
  (`t.Sym() != nil`), `emptyiface`, `variadic`; or `-`. Size-dependent flags (`hasptr`) are
  only present when `size` is known.
- kind-specific tail:
  - `PTR`, `SLICE`: `t<elem>`
  - `ARRAY`: `t<elem> <NumElem>`
  - `STRUCT`: `<nfields>`, followed by that many `field` lines
  - `FUNC`: `<nrecv> <nparams> <nresults>`, followed by that many `field` lines (receiver,
    params, results, in that order; offsets are those of the FuncArgs structs)
  - `TUPLE`: `t<first> t<second>`
  - `RESULTS`: `<n> <t,…>`
  - all others (scalars, `STRING`, `UNSAFEPTR`, `INTER`, `MAP`, `CHAN`, `SSA`): nothing. Map,
    chan and interface internals are not exported (no in-scope pass inspects them); `SSA`
    types (`mem`, `flags`, `void`, `int128`, `vec128`, …) are identified by their string.

`field <i> "<name>" t<type> <offset> <embedded 0|1>`: field `i` of the preceding `type`
(`Field.Sym.Name`, or `""` if none; `offset` is `?` when not calculated).

`typeorder` (once, at the end of the file) lists every type of the file in ascending
`types.(*Type).Compare` order; a group `t3=t9` holds types that compare `CMPeq`. Since `Compare`
is a total preorder, the order restricted to the types of any section is that section's order,
so a Lean `cmpTyp` is just a rank comparison. (CSE's `cmpVal` and `copyCompatibleType` use
`Compare`.)

`aux a<n> <tag> "<fmt %v>" <tag-specific>`, where `<fmt %v>` is Go's `fmt.Sprint(aux)` (what
`LongString` prints inside `{…}`):

| Go type | tag | tail |
| --- | --- | --- |
| `*ir.Name` | `name` | `"<n.Sym().Name>" <class> t<type> <frameoffset> <flags> <pos>` — `class` is `ir.Class.String()` (`PAUTO`, `PPARAM`, `PPARAMOUT`, `PEXTERN`, `PFUNC`, …); flags from `addrtaken`, `used`, `autotmp`, `nonmergeable`, `opendeferslot`, `readonly`, `escnever`/`escheap`/`escnone` |
| `*obj.LSym` | `sym` | `"<name>" <abi> <SymKind> <size> <flags> <typeinfo t\|-> <itabinfo t\|-> <data> <nrelocs>`, followed by `nrelocs` `reloc` lines and, when `typeinfo` is set, one `rtype` line |
| `stringAux` | `str` | `"<s>" "<StringData symbol name>"` |
| `*AuxCall` | `call` | `<fn a\|-> <abi\|-> <nin> <nout> <spilloff> <spillsize> <inregs> <outregs>`, followed by `nin + nout` `abiparam` lines (`abi` is `abiInfo.Config().Which()`; with `abiInfo == nil` the tail is `<fn> - 0 0 0 0 0 0`) |
| `*AuxNameOffset` | `nameoff` | `a<name> <offset>` |
| `*types.Type` | `type` | `t<type>` |
| `int64Aux` | `int` | `<n>` |
| `auxMark` | `mark` | |
| `PanicBoundsC` | `pbc` | `<C>` |
| `PanicBoundsCC` | `pbcc` | `<Cx> <Cy>` |
| anything else | `unknown` | `"<%T>"` (a gap; counted by the stats tool, must stay at 0) |

`sym` details: `abi` is `lsym.ABI()`; `SymKind` is `objabi.SymKind.String()` (e.g. `SRODATA`,
`Sxxx` when not yet laid out); `flags` from `dupok`, `local`, `static`, `contentaddressable`,
`wrapper`, `abiwrapper`, `noptr`; `data` is `lsym.P` as lower-case hex (`-` if empty) and is
only written when `SymKind` is `SRODATA` (the only case `symIsRO`, `read8..64`, `isFixedLoad`
read it), else `-`. `typeinfo`/`itabinfo` are the types of `lsym.TypeInfo()`/`lsym.ItabInfo()`.

`reloc <off> <siz> <type> <add> "<target name>" <target abi>`: `objabi.RelocType.String()`
(`R_ADDR`, `R_WEAKADDR`, …); target name `""` if nil.

`rtype <size> <ptrdata> <hash> <abikind> "<gcdata sym>" "<elem type sym>"`: what
`rewriteFixedLoad` folds a load from a type descriptor to — `t.Size()`,
`types.PtrDataSize(t)`, `int32(types.TypeHash(t))`, `int8(reflectdata.ABIKindOfType(t))`, the
name of `reflectdata.GCSym(t, true)` and, for pointer types, the name of
`reflectdata.TypeLinksym(t.Elem())` (else `""`). The names are computed without the side
effects of those functions. Fields that need an uncalculated size are `?`.

`abiparam <in|out> <i> t<type> <name a|-> <regs> <offset>`: `ABIParamAssignment` `i`:
`Type`, `Name`, `Registers` (comma list of `abi.RegIndex`, `-` if on stack) and the raw
`offset` field (stack offset, or spill offset for register parameters).

`slot s<n> a<name> t<type> <off> <splitof s|-> <splitoffset>`: a `*LocalSlot` (`N`, `Type`,
`Off`, `SplitOf`, `SplitOffset`).

### Function, blocks, values

`f <entry b> t<f.Type> <f.OwnAux a> <f.vid.last> <f.bid.last>`: `vid.last`/`bid.last` are the
last IDs handed out (the next fresh ID is one more); together with `freev`/`freeb` they
determine every ID a pass allocates (`newValue` pops `freeValues` first; `NewBlock` pops
`freeBlocks` first).

`b b<ID> <kind> <pos> <likely> <auxint> <aux a|-> <controls v,…> <succs> <preds>`

- `kind`: `BlockKind.String()` (`Plain`, `If`, `Defer`, `Ret`, `RetJmp`, `Exit`, `JumpTable`,
  `First`).
- `likely`: `BranchPrediction` (−1, 0, 1).
- `succs`, `preds`: `b<ID>:<i>` per edge in order, `i` = the edge's reverse index (`Edge.i`).
- Fields that the generic passes never set (`CPUfeatures`, `FlagsLiveAtEnd`, `Hotness`) are
  not exported; the exporter writes `warn "<block>: ..."` if one is non-zero.

`v v<ID> <op> t<type> <auxint> <aux a|-> <pos> <uses> <args v,…>`

- `op`: `Op.String()` (generic op name, `Add64`, `Phi`, `InitMem`, … — the Lean constructor).
- `auxint`: `v.AuxInt` as signed int64 (floats are `math.Float64bits`, as in Go).
- `uses`: `v.Uses` (redundant: equals the number of occurrences in `Args` and `Controls`;
  exported so a reader can check its own count).
- The value's block is the preceding `b` line.

`names`, `named`, `namedx`: `f.Names` order and `f.NamedValues`. `namedx` writes its slot
inline as `<a name>/<t type>/<off>/<splitof s|->/<splitoffset>` (keys sorted by that tuple).

`splits <entries>`: `f.CanonicalLocalSplits`, one entry `s<parent>/<off>/t<type>=s<slot>` per
map entry, sorted by (parent, off, type). `canon <entries>`: `f.CanonicalLocalSlots`,
`a<name>/t<type>/<off>/<splitof>/<splitoffset>=s<slot>`, sorted. These decide whether
`decompose` creates new autos (`fe.SplitSlot`) or reuses earlier splits.

`consts <entries>`: `f.constants`, one entry `<key>=<v,…>` per non-empty line, keys ascending,
values in slice order (the order `constVal` scans). `v.InCache` is exactly membership here.
Keys for zero-valued `ConstNil`/`ConstSlice`/`ConstString`/`ConstInterface` are Go's magic
constants (`constNilMagic` = 1111, …).

`cache` lines (only for non-nil caches; they survive passes that do not call
`invalidateCFG`, e.g. `swapSuccessors`, so a later pass can see a stale one):

- `cache postorder <b,…>`
- `cache idom <b<ID>:b<idom>|b<ID>:-,…>` (indexed by block ID; only blocks of `f.Blocks`)
- `cache sdom <b<ID>:<parent>:<child>:<sibling>:<entry>:<exit>,…>`
- `cache loopnest` (presence only; contents not exported — see gaps)
- `cache linestarts <index>:<first>:<last>,…`: the per-file line ranges of
  `f.cachedLineStarts` (built by `number lines`, used as scratch by later passes; its entries
  are empty between passes, which the exporter checks with a `warn`).

`warn "<text>"` may appear anywhere in a section: an invariant the exporter expected did not
hold (e.g. a value's `Block` field differs from the block listing it). The stats tool counts
them.

## Fixed configuration (`config` lines)

Everything else the in-scope passes read outside `Func` is constant for the corpus and recorded
in `config` lines so a mismatch is visible:

| key | source | corpus value |
| --- | --- | --- |
| `arch` | `Config.arch` | `arm64` |
| `goos` | `buildcfg.GOOS` | `linux` |
| `ptrsize`, `regsize` | `Config.PtrSize/RegSize` | 8, 8 |
| `bigendian`, `unalignedok`, `havecondselect`, `havebswap64/32/16`, `hasgreg` | `Config` | 0,1,1,1/1/1,1 |
| `softfloat`, `race`, `optimize` | `Config` | 0, 0, 1 |
| `fixedframesize`, `archalign` | `ctxt.Arch.FixedFrameSize`, `Alignment` | 8, 1 |
| `flagshared`, `flagdynlink` | `ctxt.Flag_shared/Flag_dynlink` | 0, 0 |
| `usewb` | `fe.UseWriteBarrier()` (`base.Flag.WB`) | 1 |
| `debugnil` | `fe.Debug_checknil()` (`base.Debug.Nil`) | 0 |
| `checkenabled` | `ssa.checkEnabled` (must be 0: it shuffles `b.Values`) | 0 |
| `exp.cgocheck2`, `exp.preemptibleloops`, `exp.simd` | `buildcfg.Experiment` | 0, 0, 0 |
| `abi0`, `abi1` | `<intregs>:<floatregs>:<localsoffset>` of `Config.ABI0/ABI1` | `0:0:8`, `16:16:8` |
| `abiself`, `abidefault` | `f.ABISelf/ABIDefault.Which()` | per function |
| `syslook.<name>` | `fe.Syslook(name)` symbol names (`writeBarrier`, `wbZero`, `wbMove`, `cgoCheckPtrWrite`, `cgoCheckMemmove`, `goschedguarded`) | `runtime.writeBarrier`, … |
| `zerobase` | `ir.Syms.Zerobase` | `runtime.zerobase` |
| `rttype.<field>` | `<offset>:t<type>` of the `rttype.Type` fields used by `isFixedLoad` (`Size_`, `PtrBytes`, `Hash`, `Kind_`, `GCData`) and `rttype.PtrType` `Elem` | |
| `mulrecipes` | keys `x:cost` of `Config.mulRecipes` (the recipe builders are arch code the port reproduces) | |

Per-pass debug flags (`-d=ssa/<pass>/debug`) are 0; logging (`f.pass.debug`, `Warnl`, rule
logging) has no effect on the SSA.

## Not exported (known gaps)

These are either derivable, constant, or not read by any pass in scope. A pass port that needs
one of them must raise it on #4.

- `f.cachedLoopnest` contents (only presence). `loopnestfor` is deterministic in the CFG; a
  stale loop nest across passes is not expected (every in-scope pass that changes the CFG
  calls `invalidateCFG`), the presence flag lets a port check its assumption.
- `f.auxmap` (CSE's aux ids): it is nil until `generic cse`, the only in-scope reader, which
  fills it in value order; a port reproduces it.
- `f.Cache` (scratch slices, posets, `Cache.values` storage): no observable state.
- `f.HTMLWriter`, `ruleMatches`, `dumpFileSeq`, `PrintOrHtmlSSA`: debugging only.
- `f.RegAlloc`, `tempRegs`, `RegArgs`, `CloSlot`, `scheduled`, `laidout`, `maxCPUFeatures`,
  `DeferReturn`: unset or unread before `lower`.
- `ir.Name` details beyond the listed flags (positions of definitions, `Curfn`, closure vars,
  `Heapaddr`, …): read by `ssagen`, not by the passes. New autos made by `decompose`
  (`fe.SplitSlot`) get `Sym.Name = parent + suffix`, `Class = PAUTO`, `used`, `escnever`;
  the port creates them with those fields.
- Map, chan, interface type internals and method sets.
- `LSym.P` of non-`SRODATA` symbols.
- ABI analysis of new calls (`writebarrier`'s `wbZero`/`wbMove`/`cgoCheck*` calls get an
  `AuxCall` from `ABIDefault.ABIAnalyzeTypes`): the result appears in the next section; the
  port reimplements the analysis from `abi1`.
- Side effects outside the SSA (`reflectdata.MarkTypeSymUsedInInterface`,
  `fe.Func().SetWBPos`, `StringData` creating the data symbol, warnings): they do not change
  the SSA of this or any other function.
