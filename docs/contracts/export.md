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
| `GOFV_SSA_GOTEXT=1` | also write `<file>.txt`: for each section a line `pass <k> "<name>"` followed by Go's own `f.String()` verbatim (printer cross-check; debugging only — `f.String()` runs `findlive`, which uses the compiler's scratch caches, so do not combine it with parity runs) |

Without `GOFV_SSA_EXPORT` the patched compiler behaves exactly like the stock one. With it,
the exporter only reads compiler state: it never calls caching accessors (`f.Postorder()`,
`f.Idom()`, …), never computes type sizes (`types.CalcSize` is disabled in the backend), and
never creates symbols, so the compiled code is unchanged.

One file per function: `<dir>/<pkgpath>/<name>,<abi>.ssa`, where `<pkgpath>` keeps its `/`
as directory separators and `<name>` is `f.Name` with every byte outside `[A-Za-z0-9._-]`
written as `%XX` (two upper-case hex digits); `<abi>` is `f.ABISelf.Which()` (0 = ABI0,
1 = ABIInternal). `main` packages of different programs collide, so drive one program per
export directory (`scripts/export-corpus.sh` does). If the escaped name is longer than 160
bytes (generic instantiations), it is cut to its first 120 bytes followed by `~` and the first
16 hex digits of the SHA-256 of `f.Name` (the `func` line has the full name). If a name
repeats within one compile the second file gets `#2` before `.ssa`, and so on.

The output is deterministic: the same compile produces byte-identical files (checked by
`scripts/export-corpus.sh --check-determinism`), also under the backend's concurrent
compilation (`-c`). State that other functions' concurrent compilation mutates (kind, size and
contents of symbols that are not yet read-only data; frame offsets of callees' parameter names)
is deliberately not exported; no pass reads it.

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
- Flag lists are comma lists of the flag names that are set, always in the order the flag
  names are listed in this document; `-` when none is set.
- A position `pos` is `p<index>:<line>:<col>:<stmt>:<xlogue>`, the fields of Go's
  `src.XPos{index, lico}`: `lico = line<<12 | col<<4 | xlogue<<2 | stmt` (`lineBits = 20`,
  `colBits = 8`). `stmt` is the raw field: 0 `PosDefaultStmt`, 1 `PosIsStmt`, 2 `PosNotStmt`
  (Go's `IsStmt()` reports `PosNotStmt` for `lico == 0`, i.e. `…:0:0:0:0`, whose raw field is
  0; `withStmt` leaves `lico == 0` unchanged). `XPos.Before`
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
typs <Name=t,…>                       (section 0 only)
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
cache <name> <payload>                (f.cached*, f.auxmap: only those that are non-nil)
warn "<text>"                         (zero or more)
end
```

Presence: `typs` is present in section 0 only. `f`, `names`, `splits`, `canon`, `consts`, `freev`, `freeb` are always present
(payload `-` when empty). `named` has one line per `f.Names` entry (none iff `names -`);
`namedx` zero or more lines; each `cache <name>` line is present iff that cache is non-nil, in
the order `postorder`, `idom`, `sdom`, `loopnest`, `auxmap`, `linestarts`. All `warn` lines of
a section come together just before `end`, in emission order.

### Definitions (tables)

Every type, aux object, local slot and position base referenced by a section is defined before
the `f` line of the first section that references it. A definition refers to objects defined
earlier, or (only for recursive types, e.g. `type T struct{ next *T }`) to objects whose
definition follows later in the same definition block; a reader resolves references after
reading a section's whole definition block. A definition stays valid for later sections.
Aux objects that Go mutates in place (an `*AuxCall` whose `Fn` is rewritten by
`devirtLECall`, `expand calls` filling in ABI data, …) are **redefined** with the same number
in every section where their content differs from the last definition; a reader keeps the
latest one. Identity is Go identity: two references share a number iff the Go values are
`==` (pointer identity for pointer-typed aux and `*LocalSlot`, value equality for `stringAux`
and friends). This is what `Value.Aux != w.Aux` and CSE's `auxmap` observe.

Types are the exception: they are numbered by **type identity and spelling**, not by
pointer. The compiler sometimes holds several identical `*types.Type` objects with the same
spelling (two `[2]int`, say), and which one a value or call signature ends up with depends on
the concurrent compilation of other functions, so pointer identity is not reproducible. Two
types share a number iff they have the same kind, the same `LinkString()` (unique per
identical type, local types included), the same `notinheap`/`noalg`/`shape` flags and the same
`t.String()`; `SSA` pseudo-types by name; `TUPLE`/`RESULTS` by their component numbers.
Including `String()` keeps apart the distinct objects that passes do compare by pointer and
that are deterministic: `zcse` keys zero-argument values on the type pointer, and `byte` vs
`uint8`, `*byte` vs `*uint8`, `rune` vs `int32`, `any` vs `interface {}` are distinct objects
(issue #52). A `*types.Type` used as aux is numbered by its type number (one aux number per
type number). A pass port compares types by number; `Compare`-based comparisons use
`typeorder`, where such spellings fall into one `=` group.

Objects first created by pass `k` are numbered while section `k` is written (block order, then
value order, then names, …), so a Lean pass creating new objects must match them to section
`k`'s definitions by content (or up to renaming), not by number.

`posbase p<index> "<abs filename>" <line> <col> <inl>`: the `src.PosBase` of `XPos` index
`<index>` (index 0, the nil base, has no definition) (`base.Ctxt.PosTable`): absolute file name, base line/column (line directives), and
`InliningIndex()` (−1 if not inlined; `deadcode` keeps an `InlMark` iff some live position has
its `AuxInt` as inlining index).

`type t<n> <kind> <size> <align> <ptrdata> <flags> "<t.String()>" "<types.TypeSymName(t)>" <kind-specific>`

`TypeSymName` is the name of the type's descriptor symbol without the `type:` prefix (what
`reflectdata.TypeLinksym(t)` returns is the `LSym` named `type:<TypeSymName>`, used by
`writebarrier` and `rewriteFixedLoad`); `""` for `SSA`/`TUPLE`/`RESULTS` types.

- `kind`: `types.Kind.String()` (`INT8`, `PTR`, `STRUCT`, `SSA`, `TUPLE`, `RESULTS`, `FUNC`,
  …; Go's `TINT8` etc.).
- `size`, `align`, `ptrdata`: `t.Size()`, `t.Alignment()`, `types.PtrDataSize(t)`, or `?` when
  the size was never calculated by the compiler (`widthCalculated()` false; e.g. element types
  only reached through a pointer); `ptrdata` is `?` as well for `SSA`/`TUPLE`/`RESULTS`
  kinds. Flags `hasptr`, `direct`, `comparable` and the `TypeSymName` string need a calculated
  size; when it is `?` they are absent / `""`.
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
(`Field.Sym.Name`, or `""` if none; `offset` is `?` when the type's size is not calculated or
the field offset is `BADWIDTH`, as for most `FUNC` parameters).

`typs <Name=t,…>` (section 0 only): the types rules and passes name directly: the
`Config.Types` fields (`typ.*` in rules) `Bool`, `Int8`, `Int16`, `Int32`, `Int64`, `UInt8`,
`UInt16`, `UInt32`, `UInt64`, `Int`, `Float32`, `Float64`, `UInt`, `Uintptr`, `String`,
`BytePtr`, `Int32Ptr`, `UInt32Ptr`, `IntPtr`, `UintptrPtr`, `Float32Ptr`, `Float64Ptr`,
`BytePtrPtr`, then `Complex64`, `Complex128`, `UnsafePtr` (`types.Types[k]`) and the SSA
pseudo-types `Mem`, `Flags`, `Void`, `Int128`, `ResultMem` (`types.TypeMem`, …), in that
order. `types.Types[k]` for the other basic kinds are the `Config.Types` entries.

`typeorder` (once, at the end of the file) lists every type of the file in ascending
`types.(*Type).Compare` order; a group `t3=t9` holds types that compare `CMPeq`. Since `Compare`
is a total preorder, the order restricted to the types of any section is that section's order,
so a Lean `cmpTyp` is just a rank comparison. (CSE's `cmpVal` and `copyCompatibleType` use
`Compare`.)

`aux a<n> <tag> "<fmt %v>" <tag-specific>`, where `<fmt %v>` is Go's `fmt.Sprint(aux)` (what
`LongString` prints inside `{…}`):

| Go type | tag | tail |
| --- | --- | --- |
| `*ir.Name` | `name` | `"<n.Sym().Name>" <class> t<type> <frameoffset> <esc> <flags> <pos>` — `class` is `ir.Class.String()` (`PAUTO`, `PPARAM`, `PPARAMOUT`, `PEXTERN`, `PFUNC`, …); `esc` is `n.Esc()` (0 `EscUnknown`, 1 `EscNone`, 2 `EscHeap`, 3 `EscNever`); flags `addrtaken`, `used`, `autotmp`, `nonmergeable`, `opendeferslot`, `readonly`; `pos` is `n.Pos()` |
| `*obj.LSym` | `sym` | `"<name>" <abi> <SymKind\|-> <size> <flags> <typeinfo t\|-> <itabinfo t\|-> <data> <nrelocs>`, followed by `nrelocs` `reloc` lines and, when `typeinfo` is set, one `rtype` line |
| `stringAux` | `str` | `"<s>" "<StringData symbol name>"` |
| `*AuxCall` | `call` | `<fn a\|-> <abi\|-> <nin> <nout> <spilloff> <spillsize> <inregs> <outregs>`, followed by `nin + nout` `abiparam` lines (`abi` is `abiInfo.Config().Which()`; with `abiInfo == nil` the tail is `<fn> - 0 0 0 0 0 0`) |
| `*AuxNameOffset` | `nameoff` | `a<name> <offset>` |
| `*types.Type` | `type` | `t<type>` |
| `int64Aux` | `int` | `<n>` |
| `auxMark` | `mark` | |
| `PanicBoundsC` | `pbc` | `<C>` |
| `PanicBoundsCC` | `pbcc` | `<Cx> <Cy>` |
| anything else | `unknown` | `"<%T>"` (a gap; counted by the stats tool, must stay at 0) |

`sym` details: `abi` is `lsym.ABI()`. Kind, size, flags, data and relocations are only exported
for read-only data, i.e. when `lsym.Type == objabi.SRODATA` (the only kind any in-scope pass
tests: `symIsRO`, `symIsROZero`, `isFixedLoad`, `read8..64`, `IsReadOnlyGlobalAddr`); then
`SymKind` is `SRODATA`, `size` is `lsym.Size` and `flags` are `dupok`, `local`, `static`,
`contentaddressable`, `wrapper`, `abiwrapper`. For every other symbol the line has
`- 0 -` there (`STEXT` sizes etc. change while other functions are assembled concurrently); `data` is `lsym.P` as lower-case hex (`-` if empty) and is
only written when `SymKind` is `SRODATA` (the only case `symIsRO`, `read8..64`, `isFixedLoad`
read it), else `-`. `typeinfo`/`itabinfo` are the types of `lsym.TypeInfo()`/`lsym.ItabInfo()`.

`reloc <off> <siz> <type> <add> "<target name>" <target abi>`: `objabi.RelocType.String()`
(`R_ADDR`, `R_WEAKADDR`, …); target name `""` if nil. Relocations are written only for
`SRODATA` symbols (`nrelocs` is 0 otherwise).

`rtype <size> <ptrdata> <hash> <abikind> "<gcdata sym>" "<elem type sym>"`: what
`rewriteFixedLoad` folds a load from a type descriptor to — `t.Size()`,
`types.PtrDataSize(t)`, `int32(types.TypeHash(t))`, `int8(reflectdata.ABIKindOfType(t))`, the
name of `reflectdata.GCSym(t, true)` and, for pointer types, the name of
`reflectdata.TypeLinksym(t.Elem())` (else `""`). The names are computed without the side
effects of those functions. Fields that need an uncalculated size are `?`.

`abiparam <in|out> <i> t<type> <name a|-> <regs> <offset>`: `ABIParamAssignment` `i`:
`Type`, `Name`, `Registers` (comma list of `abi.RegIndex`, `-` if on stack) and the raw
`offset` field (stack offset, or spill offset for register parameters; −1 when unset). `Name`
is exported only for `f.OwnAux` (`ParamAssignmentForArgName`, the only reader); for calls it
is `-` (callee names belong to functions compiled concurrently).

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
- `cache auxmap <a:id,…>`: `f.auxmap` (CSE's aux numbering, which persists across `cse`
  runs), sorted by id
- `cache linestarts <entry>,…`: `f.cachedLineStarts`, built by `number lines` and used by later
  passes as their `pendingLines` scratch map. One entry per file index, ascending:
  `<index>:<first>:<last>` (the line range of that file's `biasedSparseMap`) followed by zero or
  more `:<line>=<val>` (entries left over from the previous pass, in the sparse map's dense
  order — passes do not always clear it), or `<index>:-` for an empty range.

`warn "<text>"`: an invariant the exporter expected did not hold (e.g. a value's `Block` field
differs from the block listing it). Written just before `end`; `finish` may add `warn` lines
before `typeorder`. The stats tool counts them; the corpus must have none.

## Fixed configuration (`config` lines)

Everything else the in-scope passes read outside `Func` is constant for the corpus and recorded
in `config <key> <value>` lines, one per key, in exactly this order (values as exported for the
corpus):

| key | source | corpus value |
| --- | --- | --- |
| `arch` | `Config.arch` | `arm64` |
| `goos` | `buildcfg.GOOS` | `linux` |
| `ptrsize` | `Config.PtrSize` | 8 |
| `regsize` | `Config.RegSize` | 8 |
| `bigendian` | `Config.BigEndian` | 0 |
| `unalignedok` | `Config.unalignedOK` | 1 |
| `havecondselect` | `Config.haveCondSelect` | 1 |
| `havebswap64`, `havebswap32`, `havebswap16` | `Config.haveBswap*` | 1, 1, 1 |
| `hasgreg` | `Config.hasGReg` | 1 |
| `softfloat` | `Config.SoftFloat` | 0 |
| `race` | `Config.Race` | 0 |
| `optimize` | `Config.optimize` (`-N` off) | 1 |
| `fixedframesize` | `ctxt.Arch.FixedFrameSize` | 8 |
| `archalign` | `ctxt.Arch.Alignment` | 1 |
| `flagshared`, `flagdynlink` | `ctxt.Flag_shared`, `ctxt.Flag_dynlink` | 0, 0 |
| `usewb` | `fe.UseWriteBarrier()` (`base.Flag.WB`) | 1 |
| `debugnil` | `fe.Debug_checknil()` (`base.Debug.Nil`) | 0 |
| `checkenabled` | `ssa.checkEnabled` (must be 0: it shuffles `b.Values`) | 0 |
| `localpkg` | `types.LocalPkg.Path`, a string (`writebarrier` special-cases `runtime`) | the package path |
| `exp.cgocheck2`, `exp.preemptibleloops`, `exp.simd` | `buildcfg.Experiment` | 0, 0, 0 |
| `abi0`, `abi1` | `<intregs>:<floatregs>:<localsoffset>` of `Config.ABI0`, `Config.ABI1` | `0:0:8`, `16:16:8` |
| `abiself`, `abidefault` | `f.ABISelf.Which()`, `f.ABIDefault.Which()` | per function, `abidefault` 1 |
| `syslook.writeBarrier`, `syslook.wbZero`, `syslook.wbMove`, `syslook.cgoCheckPtrWrite`, `syslook.cgoCheckMemmove`, `syslook.goschedguarded` | name of `fe.Syslook(name)`, a string | `"runtime.writeBarrier"`, … |
| `zerobase` | name of `ir.Syms.Zerobase`, a string | `"runtime.zerobase"` |
| `rttype.Size_`, `rttype.PtrBytes`, `rttype.Hash`, `rttype.Kind_`, `rttype.GCData`, `rttype.PtrType.Elem` | `<offset>:<kind>:<size>` of the runtime type descriptor fields `isFixedLoad` folds (`copyCompatibleType` needs kind and size) | `0:UINTPTR:8`, `8:UINTPTR:8`, `16:UINT32:4`, `23:UINT8:1`, `32:PTR:8`, `48:PTR:8` |

`Config.mulRecipes` (used by the `canMulStrengthReduce` rules) is not exported: it is built
deterministically by `config.go` from arm64 instruction costs, which the port reproduces.

Per-pass debug flags (`-d=ssa/<pass>/debug`) are 0; logging (`f.pass.debug`, `Warnl`, rule
logging) has no effect on the SSA.

## Not exported (known gaps)

These are either derivable, constant, or not read by any pass in scope. A pass port that needs
one of them must raise it on #4.

- `f.cachedLoopnest` contents (only presence). `loopnestfor` is deterministic in the CFG; a
  stale loop nest across passes is not expected (every in-scope pass that changes the CFG
  calls `invalidateCFG`), the presence flag lets a port check its assumption.
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
- Kind, size, flags, data and relocations of symbols that are not (yet) `SRODATA`, and the
  `ir.Name`s of callee parameters in call `AuxCall`s (see `sym` and `abiparam`).
- `f.pass` other than its name: the section name is the pass name (rules depend on it, e.g.
  some `Mul` rules fire only when `pass.name != "opt"`); `pass.debug`/`stats` are 0.
- Side effects outside the SSA (`reflectdata.MarkTypeSymUsedInInterface`,
  `fe.Func().SetWBPos`, `StringData` creating the data symbol, warnings): they do not change
  the SSA of this or any other function.

## Building and the corpus

- `scripts/build-go.sh` builds the patched toolchain into `third_party/go-build` (fresh copy of
  the pin, `patches/go/*.patch`, `make.bash` under `memcap`); `--compile` re-patches and
  rebuilds only `cmd/compile`; `--diff` prints the current patch (to refresh
  `patches/go/0001-gofv-ssa-export.patch` after editing `third_party/go-build`).
- `scripts/export-corpus.sh [--check-determinism]` exports the corpus for `linux/arm64`
  (`-trimpath`, fresh build cache): the std packages listed in the script (one unit `std`),
  every `// run` program without build constraints in `test/*.go` and `test/ken/*.go` (one unit
  each; those that do not build are listed as `skip`), and `examples/*/main.go`. Dumps go to
  `../gofv-corpus/<pin12>/plain/<set>/<unit>/…` and `<set>.tar.zst`, outside git; the committed
  `corpus/manifest.txt` lists every unit with its file count and digest, and the
  `tools/ssastats` table (functions, values, per pass how many functions changed).
