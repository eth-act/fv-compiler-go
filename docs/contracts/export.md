# Contract: per-pass SSA export (`gofv-ssa` v5)

Owner: Exporter (issue #4; format 5: #379). Consumers: LeanIR (parser/printer, #21), RulesExport
(#22), every pass port (G4, H*). Changing the format bumps the version in the first line and is
announced on #4. v3 (#31) adds the `addrconv` name flag. v4 (#10) adds the `deferbits` name flag
and also marks `addrconv` from pointers passed at integer-typed call parameters. v5 (#379, Phase 2)
adds the sections of the lowered passes (`lower` … `trim`) with their state: machine ops and
block kinds, the cached loop nest, `flagslive`/`hotness`/`fstate`/`regalloc`/`tempregs`, the
`callreg` sub-line of `call` aux values, the `typelink` line and the machine `config` keys
(section "Format 5"). The sections before `lower` are byte-identical to v4's. The parser reads
v2–v4 files too.

The patched `go1.27.3` compiler (`patches/go/*.patch`, built by `scripts/build-go.sh` into
`third_party/go-build`) writes, for each selected function, the complete SSA state the passes
up to `trim` can observe:

- section 0, `start`: the function as `ssagen` hands it to `ssa.Compile`, i.e. the input of
  `number lines`;
- one section after every pass that runs, from `number lines` up to and including `trim`, the
  last pass of `ssa.Compile` (v4 stopped before `lower`: its last section was the input of
  `lower`). Passes that are disabled (`insert resched checks` unless
  `GOEXPERIMENT=preemptibleloops`; `cpufeatures`, `rewrite tern` without `GOEXPERIMENT=simd`) or
  skipped (non-required passes under `-N`) have no section; `merge conditional branches` is
  commented out of the pass list in go1.27.3. Each section names its pass, so the pass list is
  self-describing. `GoFV.SSA.loweredPasses` lists the passes from `lower` on.

Parity of a Lean pass `p` is checked as: parse sections `0..k-1` (definitions accumulate, see
below), take the state of section `k-1`, run `p`, compare with section `k`. The Phase 1 tools
(`pass-parity` without lowered instances, `gofv-ssa-opt`, `ssa-check`, `sem-difftest`,
`analysis-difftest`) read files with `parseExportUntil "lower"`, which skips the lowered
sections unparsed.

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
repeats within one compile (e.g. generic instantiations compiled twice), every file of that
name is called `<name>,<abi>#<h>.ssa` instead, with `<h>` the first 16 hex digits of the SHA-256
of the file's contents (the order of concurrent compilation must not decide the names).

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
gofv-ssa 5
pkg "<base.Ctxt.Pkgpath>"
func "<f.Name>" <abi> <nosplit 0|1> <pgohot 0|1>
config <key> <value>                  (one line per key; table below)
<section 0>
<section 1>
…
frontend
<definitions>                          (the frontend block, see below)
end
warn "<text>"                         (zero or more)
ptrcache <t,…>
typelink <group,…>                    (v5)
typecmp t<a> t<b> <lt|eq|gt>           (zero or more)
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
freev <v,…>                           (f.freeValues free list, head first; sorted once f.RegAlloc is set)
freeb <b,…>                           (f.freeBlocks free list, head first)
cache <name> <payload>                (f.cached*, f.auxmap: only those that are non-nil)
flagslive <b,…>                       (v5, zero or one)
hotness <b:h,…>                       (v5, zero or one)
fstate <flags>                        (v5, zero or one)
regalloc <len> <v:loc,…>              (v5, zero or one)
tempregs <v:reg,…>                    (v5, zero or one)
zvar <v:class,…>                      (zero or one; see below)
warn "<text>"                         (zero or more)
end
```

Presence: `typs` is present in section 0 only. `f`, `names`, `splits`, `canon`, `consts`, `freev`, `freeb` are always present
(payload `-` when empty). `named` has one line per `f.Names` entry (none iff `names -`);
`namedx` zero or more lines; each `cache <name>` line is present iff that cache is non-nil, in
the order `postorder`, `idom`, `sdom`, `loopnest`, `auxmap`, `linestarts`. The v5 lines
`flagslive` … `tempregs` are present iff non-empty (section "Format 5"). `zvar` is present iff
non-empty. All `warn` lines of a section come together just before `end`, in emission order.

`zvar <v<ID>:<class>,…>`: type-object classes for `zcse`, which keys zero-argument values on
the `*types.Type` **pointer**. Types are numbered by identity (above), but the backend creates
a fresh `*T` object on every `types.NewPtr` whose element has no cached pointer type
(`types.NewPtrCacheEnabled` is false while the backend runs), so zero-argument values of one
type number can carry distinct type objects that `zcse` does not merge. Class 0 is the
number's **canonical** object: for a pointer type the element's cached pointer type
(`t.Elem()`'s `cache.ptr`; a pointer object is non-canonical when that is nil or another
object), for any other type the first object met among the section's zero-argument values
(`opcodeTable[op].argLen == 0`; blocks, then values). Every zero-argument value whose object is
non-canonical is listed, in section order, with its class `1, 2, …`: one class per distinct
non-canonical object of its type number, in order of first appearance. `zvar` is an oracle
hint (`PassEnv.zvar`), not part of the function: parity does not compare it, and passes need
not produce it; the chained pipeline (#101) tracks object identity itself, with `ptrcache`.
(Numbering every type by pointer instead would be faithful everywhere but is not
deterministic: shared objects built concurrently differ between runs, and 6,388 of the 9,297
quick-corpus functions have value types with several objects of one identity.)

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

`typeorder` (once, at the end of the file) lists every type of the file sorted by
`types.(*Type).Compare` (Go's `sort.SliceStable`); a group `t3=t9` holds types adjacent in that
order that compare `CMPeq`. `Compare` is not a total preorder (`*byte` is `CMPeq` `*uint8` by
the byte/uint8 special case, while `cmpsym` orders names by length first, so `*abi.Kind` sorts
between them, #68), so before it the exporter writes one `typecmp t<a> t<b> <o>` line (`a < b`
by number, `o` = `Compare(a, b)`) for every pair of the file's types whose `Compare` differs
from the comparison of their group ranks. `Compare(a, b)` is the `typecmp` entry if present,
else the rank comparison (`GoFV.SSA.TypeOrder`). (CSE's `cmpVal`, the constant cache and
`copyCompatibleType` use `Compare`.)

`aux a<n> <tag> "<fmt %v>" <tag-specific>`, where `<fmt %v>` is Go's `fmt.Sprint(aux)` (what
`LongString` prints inside `{…}`):

| Go type | tag | tail |
| --- | --- | --- |
| `*ir.Name` | `name` | `"<n.Sym().Name>" <class> t<type> <frameoffset> <esc> <flags> <pos>` — `class` is `ir.Class.String()` (`PAUTO`, `PPARAM`, `PPARAMOUT`, `PEXTERN`, `PFUNC`, …); `esc` is `n.Esc()` (0 `EscUnknown`, 1 `EscNone`, 2 `EscHeap`, 3 `EscNever`); flags `addrtaken`, `used`, `autotmp`, `nonmergeable`, `opendeferslot`, `readonly`, `addrconv` (v3: the name's `LocalAddr` reaches a `Convert` to an integer, or, from v4, a pointer-shaped argument of a `StaticLECall`/`TailLECall`/`InterLECall`/`TailLECallInter`/`ClosureLECall` at an integer-typed parameter (`AuxCall.TypeOfArg`; an implicit conversion: `runtime.deferprocStack(d uintptr)` gets the `_defer` temp's address), backwards through the non-memory arguments of every value except `Load`/`Dereference`, calls included; computed once from the function the exporter starts with, i.e. section 0, and the same in every section; `gofvAddrConv`), `deferbits` (v4: the name is ssagen's open-coded defer bitmask `deferBitsTemp`: a `PAUTO` autotmp addrtaken `uint8` name, not `opendeferslot`, that is the aux of a `VarLive` in the function the exporter starts with, i.e. section 0; the same in every section; `gofvDeferBits`. Functions that defer only through `deferproc` have none); `pos` is `n.Pos()` |
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

`callreg <inputs> <outputs> <clobbers> <flags>` (v5; at most one, after the `abiparam` lines of
a `call` definition): the `regInfo` that `AuxCall.Reg` (calls) and `AuxCall.ResultReg`
(`f.OwnAux`, for `MakeResult`) cache in the `AuxCall` when `regalloc` asks for it. Inputs and
outputs are `<idx>:<mask>` lists (`-` if empty), `clobbers` a mask, flags `clobbersarg0`,
`clobbersarg1`. Absent while the cache is nil or empty (every section before `regalloc`); the
aux is redefined in the section where it fills. Masks are `regMask` as lower-case hex, bit `i` =
register number `i` (`v2` digits followed by `v1` zero-padded to 16 digits when `v2 ≠ 0`; `0`
when empty). A port derives the same constraints from `abiparam` and `intparamregs`/
`floatparamregs`; this line is the oracle.

`slot s<n> a<name> t<type> <off> <splitof s|-> <splitoffset>`: a `*LocalSlot` (`N`, `Type`,
`Off`, `SplitOf`, `SplitOffset`).

### Function, blocks, values

`f <entry b> t<f.Type> <f.OwnAux a> <f.vid.last> <f.bid.last>`: `vid.last`/`bid.last` are the
last IDs handed out (the next fresh ID is one more); together with `freev`/`freeb` they
determine every ID a pass allocates (`newValue` pops `freeValues` first; `NewBlock` pops
`freeBlocks` first).

`b b<ID> <kind> <pos> <likely> <auxint> <aux a|-> <controls v,…> <succs> <preds>`

- `kind`: `BlockKind.String()` for the generic kinds (`Plain`, `If`, `Defer`, `Ret`, `RetJmp`,
  `Exit`, `JumpTable`, `First`); for machine kinds (v5) the architecture prefix of the Go
  constant followed by `String()`: `ARM64EQ`, `ARM64TBZ` (`auxint` = the bit number),
  `ARM64LTnoov`, `ARM64JUMPTABLE` (`aux` = the `<fn>.jump<bid>` symbol of `makeJumpTableSym`, a
  `sym` aux that is not `SRODATA`), … (`BlockKind.exportName`).
- `likely`: `BranchPrediction` (−1, 0, 1).
- `succs`, `preds`: `b<ID>:<i>` per edge in order, `i` = the edge's reverse index (`Edge.i`).
- `FlagsLiveAtEnd` and `Hotness` are the section's `flagslive` and `hotness` lines (v5);
  `CPUfeatures` (SIMD only) is not exported: the exporter writes `warn "<block>: ..."` if it is
  non-zero.

`v v<ID> <op> t<type> <auxint> <aux a|-> <pos> <uses> <args v,…>`

- `op`: `Op.String()` for generic ops and `OpInvalid` (`Add64`, `Phi`, `InitMem`, …); for
  machine ops (v5) the architecture prefix of the Go constant followed by `String()`
  (`ARM64ADD`, `ARM64MOVDload`, `ARM64LoweredNilCheck`, `ARM64CALLstatic`; `Op.exportName`, the
  Lean constructor name).
- `auxint`: `v.AuxInt` as signed int64 (floats are `math.Float64bits`, as in Go). For ops with
  `auxType` `CCop` (`ARM64CSEL`, `ARM64CSINC`, `ARM64CSETM`, `ARM64CCMP`, …) it is the condition's
  raw Go opcode number (`Op(v.AuxInt)`, the pin's `opGen.go` order including the ops of the
  other architectures and SIMD; `Op.ofGoNum?`/`Op.goNum`). `ARM64BitField`,
  `ARM64ConditionalParams`, `FlagConstant`, `SymValAndOff` auxints are raw too.
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
- `cache loopnest <len> <irreducible 0|1> <loops> <b2l>` (v5; `f.cachedLoopnest`, built by
  `loopnestfor` when `f.loopnest()` finds no cached nest — in `tighten`, `likelyadjust`,
  `regalloc` and `loop rotate`; `loop invariant` builds its own nest without caching it — and
  kept across passes that do not invalidate the CFG): `len` is `len(b2l)` (the block count when
  the nest was built), `loops` the `loopnest.loops` in order as
  `b<header>:<outer>:<nBlocks>:<depth>:<isInner 0|1>:<containsUnavoidableCall 0|1>` (`outer` the
  index of the outer loop in `loops`, `-` for none; `containsUnavoidableCall` is filled in by
  `regalloc`), `b2l` the non-nil entries `b<ID>:<loop index>` ascending (stale entries for freed
  blocks included). `po` and `sdom` of the nest are the postorder and dominator tree when it was
  built; every pass that invalidates those also drops the nest (`invalidateCFG`). No v4 file
  has a `cache loopnest` line.
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

## Format 5: state of the lowered passes

After the `cache` lines, each present only when not empty, in this order:

- `flagslive <b,…>`: the blocks with `FlagsLiveAtEnd` (set by `flagalloc`), ascending ID.
- `hotness <b<ID>:<h>,…>`: non-zero `Block.Hotness` bit sets (`HotNotFlowIn` 1, `HotInitial` 2,
  `HotPgo` 4; set by `loop rotate`), ascending ID.
- `fstate <flags>`: `scheduled` (`f.scheduled`, set by `schedule`), `laidout` (`f.laidout`, set
  by `layout`).
- `regalloc <len> <v<ID>:<loc>,…>`: `f.RegAlloc` (set by `regalloc`, read by every later pass):
  its length and every non-nil entry, ascending ID (entries of freed values stay: `freeValue`
  does not clear them). `<loc>` is a register name (`R0`, `F3`, `g`, `ZERO`, `SP`, …:
  `Register.String()`, the names of `config registers`), `@<slot>` for a `LocalSlot` (inline
  slot as in `namedx`; the autos `stackalloc`/`regalloc` create with `f.NewLocal` are `name` aux
  values `.autotmp_<n>`, `PAUTO`, defined on first use), `(<r>;<r>)` for a `LocPair` and
  `[<r>;…]` for a `LocResults` (`-` for a nil element; `[]` empty).
- `tempregs <v<ID>:<reg>,…>`: `f.tempRegs`, ascending ID (present iff the map is non-nil).

Value free list: once `f.RegAlloc` is set (the `regalloc` section and later) `freev` is written
sorted by ID instead of in list order. `regalloc` frees its unused copies while ranging over a
Go map (`regalloc.go`, "Erase any copies we never used"), so the list order differs between
runs; no later pass in scope allocates values, and parity compares this canonical form.

`typelink <group,…>` (once per file, after `ptrcache`; `-` if empty): groups `t3=t9` of type
numbers that share a `LinkString()` (groups of one omitted; ordered by first number, members
ascending). `stackalloc` keys its reusable slots by `LinkString` (`stackalloc.go`, issue 65783),
which identifies types that the numbering keeps apart by spelling (`byte`/`uint8`). Absent in v4
files (`ExportFile.typeLink` is then empty).

Other state the lowered passes read is static (`opcodeTable` `regInfo`, `asm`, `faultOnNilArg0`,
… and the ARM64 rules: `tools/opsgen`, `tools/rules2lean`) or a `config` line (below).

## Pointer cache (`ptrcache`)

`ptrcache <t,…>` (once per file, after the file-level `warn` lines; `-` if empty): the type
numbers whose canonical object (the object the definition is rendered from) has a cached
pointer type, i.e. for which the backend's `types.NewPtr` returns a shared object instead of a
fresh one (rules' `t.PtrTo()`, decompose's `Split*`). Pointer caches are filled only before the
backend runs, so one line describes every section. `PassEnv.ptrCache : TypeRef → Bool`.

## Frontend block

After the last section, `frontend`, then definition lines (same records as in a section's
definition block), then `end`. It defines the objects reachable from the frontend that a pass
can reach without any section referencing them: `rewriteFixedLoad` folds a load from a
read-only symbol to its relocation target (`Addr {r.Sym}`), and the rewrite loop can then fold
a load from that target too (nested generic dictionaries, e.g.
`internal/synctest..dict.Associate[sync.WaitGroup]` → `internal/abi..dict.Escape[*sync.WaitGroup]`
→ `type:*sync.WaitGroup`, #62). The block holds the closure, over `R_ADDR`/`R_WEAKADDR`
relocations, of every exported `SRODATA` generic dictionary (`..dict.` in the name): every
target not defined by a section is defined here (with its own types), and targets that are
themselves `SRODATA` dictionaries are followed. Other targets (type descriptors, itabs) are
defined but not followed. The block is always present (possibly empty). Its numbers continue
the file's tables; `ExportFile.frontendTables` (final tables plus the block) is what
`PassEnv.frontend` holds.

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
| `registers` (v5) | `Config.registers` in number order: `<name>:<objNum>,…` (`num` = position) | `R0:8192,…,R17:8209,R19:8211,…,g:8220,R29:8221,R30:8222,ZERO:8223,SP:8383,F0:8224,…,SB:0` |
| `gpregmask`, `fpregmask`, `fp32regmask`, `fp64regmask`, `simdregmask`, `specialregmask` (v5) | `Config.*RegMask` (hex masks as in `callreg`) | `13ffffff`, `7fffffff80000000`, `0`, `0`, `7fffffff80000000`, `0` |
| `intparamregs`, `floatparamregs` (v5) | `Config.intParamRegs`, `Config.floatParamRegs` (register numbers) | `0,…,15`, `31,…,46` |
| `fpreg`, `linkreg` (v5) | `Config.FPReg`, `Config.LinkReg` | -1, 28 |
| `framepointer` (v5) | `buildcfg.FramePointerEnabled` (`regalloc` reserves the frame pointer) | 1 |
| `clobberdeadreg` (v5) | `base.Flag.ClobberDeadReg` | 0 |
| `flagN` (v5) | `base.Flag.N` (`tighten` tests it directly) | 0 |
| `fmahash` (v5) | `base.FmaHash != nil` (the ARM64 rules' `useFMA`) | 0 |

`Config.mulRecipes` (used by the `canMulStrengthReduce` rules) is not exported: it is built
deterministically by `config.go` from arm64 instruction costs, which the port reproduces.

Per-pass debug flags (`-d=ssa/<pass>/debug`) are 0; logging (`f.pass.debug`, `Warnl`, rule
logging) has no effect on the SSA.

## Not exported (known gaps)

These are either derivable, constant, or not read by any pass in scope. A pass port that needs
one of them must raise it on #4.

- `f.Cache` (scratch slices, posets, `Cache.values` storage, `stackAllocState`, regalloc's
  scratch): no observable state.
- `f.HTMLWriter`, `ruleMatches`, `dumpFileSeq`, `PrintOrHtmlSSA`: debugging only.
- `f.RegArgs`, `CloSlot`, `maxCPUFeatures`, `DeferReturn`, `Block.CPUfeatures`: read by
  `ssagen`/`genssa` (Phase 3) or SIMD only; `ctxt.Flag_locationlists` (debug info, genssa).
- The `loopnest`'s `po`/`sdom` (see `cache loopnest`) and `f` fields.
- `ir.Name` frame offsets of autos (`AllocFrame` runs after `ssa.Compile`).
- `len(curfn.Dcl)`, which numbers the autos `regalloc`/`stackalloc` create with `f.NewLocal`
  (`.autotmp_<n>`, `typecheck.TempAt`): the port takes it as `PassEnv.dclLen` (the driver from
  the frontend, parity from the stock section's first new auto; `docs/PARITY.md`).
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
- Type pointer identity beyond `zvar`: types are numbered by identity and spelling; a pass
  that compares `*types.Type` pointers of values other than `zcse`'s zero-argument keys would
  need more (none in scope does).
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
  `tools/ssastats` table (functions, values, per pass how many functions changed). This is the
  quick corpus, the per-PR parity gate. Each export is a new version directory published by an
  atomic symlink switch (`docs/PARITY.md`, "Corpus versions").
- `scripts/export-corpus.sh --corpus full [--check-determinism]` exports the nightly corpus
  (#63), published as `../gofv-corpus/<pin12>/full/` (`plain/`, `*.tar.zst`; manifest
  `corpus/manifest-full.txt`): every package of `go list std` (unit `stdall`), every non-main
  package of `go list cmd` (unit `cmd`) and every command of cmd (units `cmdmain/<path>`, their
  packages are all `main`). `scripts/parity.sh --corpus full` runs the registered passes on it.
