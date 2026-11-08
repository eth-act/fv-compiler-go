# Contract: per-pass SSA export (`gofv-ssa` v5.1) and Phase 3 export (`gofv-prog 3`)

Owner: Exporter (issue #4; format 5: #379). Consumers: LeanIR (parser/printer, #21), RulesExport
(#22), every pass port (G4, H*). Changing the format bumps the version in the first line and is
announced on #4. v3 (#31) adds the `addrconv` name flag. v4 (#10) adds the `deferbits` name flag
and also marks `addrconv` from pointers passed at integer-typed call parameters. v5 (#379, Phase 2)
adds the sections of the lowered passes (`lower` … `trim`) with their state: machine ops and
block kinds, the cached loop nest, `flagslive`/`hotness`/`fstate`/`regalloc`/`tempregs`, the
`callreg` sub-line of `call` aux values, the `typelink` line and the machine `config` keys
(section "Format 5"). The sections before `lower` are byte-identical to v4's. v5.1 (#386) adds
one line per section, `dcllen` (section "Format 5.1"). The parser reads v2–v5 files too.

Phase 3 (#546, I1 #547) adds a second format in a separate file next to each `.ssa` file: the
`gofv-prog` record (`<name>,<abi>.prog`) with the frame layout, the inputs `genssa` reads, the
Prog list after `genssa` and the assembled function (section "Phase 3: `gofv-prog 3`" below).
It leaves the `.ssa` files byte-identical. Version 2 (#549, I3) adds what the `genssa` port
reads besides the SSA (section "Version 2"). Version 3 (#550, #551) adds the text symbol's
relocations and the operands' symbol alignments at the `prog0` cut, `BuildFuncDebug`'s result
and the `dwarf` section (section "Version 3").

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
gofv-ssa 5.1
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
dcllen <n>                            (v5.1)
zvar <v:class,…>                      (zero or one; see below)
warn "<text>"                         (zero or more)
end
```

Presence: `typs` is present in section 0 only. `f`, `names`, `splits`, `canon`, `consts`, `freev`, `freeb` are always present
(payload `-` when empty). `named` has one line per `f.Names` entry (none iff `names -`);
`namedx` zero or more lines; each `cache <name>` line is present iff that cache is non-nil, in
the order `postorder`, `idom`, `sdom`, `loopnest`, `auxmap`, `linestarts`. The v5 lines
`flagslive` … `tempregs` are present iff non-empty (section "Format 5"). `dcllen` is always
present in v5.1 (section "Format 5.1"). `zvar` is present iff non-empty. All `warn` lines of a section come together just before `end`, in emission order.

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
read it), else `-`. `typeinfo`/`itabinfo` are the types of `lsym.TypeInfo()`/`lsym.ItabInfo()`,
except for a type descriptor whose `TypeInfo` was set while functions are compiled concurrently
(`base.Ctxt.InParallel`): its object is that of whichever function called
`reflectdata.TypeLinksym` first (`[4]byte` or `[4]uint8`; with or without a cached pointer type,
so `ptrcache` changed too), so the export has the type this function asked for: its first
`TypeLinksym` argument (`ssagen` `reflectType`, `writebarrier`, the pointer element in
`rewriteFixedLoad`; the driver's importer), recorded in `Func.gofvTypeInfo` (#426). The passes
read only identity properties of the type, which all these objects share. A concurrently set
`TypeInfo` that the function did not ask for is exported as is, with a `warn` (none in the corpus).

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

## Format 5.1: `len(curfn.Dcl)`

The first line is `gofv-ssa 5.1`. Each section has, after the lowered-pass lines and before `zvar`,
`dcllen <n>`: `len(curfn.Dcl)` when the section was written (`f.fe.Func().Dcl`). Every new auto
appends to `Dcl` (`fe.SplitSlot` of a non-address-taken `PAUTO`, `f.NewLocal`), and `f.NewLocal`
(`stackalloc`, the `regalloc` shuffle, `writebarrier`) names its auto `.autotmp_<len(Dcl)>`
(`typecheck.TempAt`), so a pass's input section's `dcllen` is the pass's `PassEnv.dclLen`. Like
`zvar` it describes frontend state, not the function; a chained pipeline computes it as the input
section's `dcllen` plus the `name` aux values the passes create (`GoFVTest.Driver.newAutos`), and
the driver's importer compares it with the compiler's after an import. The Lean parser returns it
next to the `ExportFile` (`GoFV.SSA.ExportExt`, `parseExportExt`), so that `Section` and
`ExportFile`, which every pass and proof module imports, are unchanged. Absent before v5.1.

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
  `f.RegArgs` and `Flag_locationlists` are in the `.prog` file (`regargs`, `config`).
- The `loopnest`'s `po`/`sdom` (see `cache loopnest`) and `f` fields.
- `ir.Name` frame offsets of autos (`AllocFrame` runs after `ssa.Compile`; they are in the
  `.prog` file's `frame` section).
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

## Phase 3: `gofv-prog 3`

Owner: Phase3IO (I1 #547; tracking #546; `docs/PASSES3.md` §2); version 2: Phase3Gen (I3 #549);
version 3: Phase3Asm2 (I4 #550, I5 #551).
Consumers: `GoFV.Asm` (`GoFV/Asm/{As,Prog,Parse,Print}.lean`, I2 #548), the `asm-check` round
trip, the I3 port's input (`GoFV.Gen.Env`) and the `gen-parity` check, and the I4 port
(`GoFV.Asm.flush`, input `prog0`, checked against `asm` by `asm-parity`, `docs/PARITY.md`) and
the I5 ports (`GoFV.Dwarf`, checked against `dwarf` by `dwarf-parity`). A change bumps the
version on the first line and is announced on #546. The parser reads only the current version.

For every function whose `.ssa` file the exporter writes (same selection, `GOFV_SSA_EXPORT`,
`GOFV_SSA_PKG`, `GOFV_SSA_FUNC`), the patched compiler writes a companion file with the same
stem and the extension `.prog`: `<name>,<abi>.prog` next to `<name>,<abi>.ssa`, or
`<name>,<abi>#<h>.prog` when the `.ssa` file is `<name>,<abi>#<h>.ssa` (`<h>` is the hash of
the `.ssa` file's contents, so the pair stays together; a `.prog` written before a later
function of the same stem appeared is renamed with its `.ssa` file). Functions that
`ssagen.Compile` rejects for their frame size (`>= 1<<30`) have a `.ssa` file and no `.prog`
file. The exporter (`ssagen/export_prog_gofv.go`, hooks in `ssagen/pgen.go` and, for the
open-coded defers, `ssagen/ssa.go` `buildssa`; accessors
`FuncInfo.GOFVSpills`, `InlMark.GOFVMark`, `InlTree.GOFVNodes` in `cmd/internal/obj`) only reads
compiler state: it creates no symbol, computes no type size (types whose size or whose inline
parts' sizes are not calculated are written with `?`), and never sets `Debugasm` (`-S` disables
Prog reuse and sorts `LSym.R` in place, `docs/PASSES3.md` §2), so the object code is unchanged.

### Cut points

| section | written | form (`docs/PASSES3.md` §0) |
| --- | --- | --- |
| `frame` | when `AllocFrame` ends (input recorded when it starts) | L2 → L2f (A1, A2) |
| `genin` | in `ssagen.Compile`, after `buildssa` and the first frame-size check, before `objw.NewProgs` and `genssa` | genssa's frontend inputs |
| `prog0` | after `genssa` returns (after `defframe`), before the frame-size check and `Flush` | P0 |
| `asm` | at the end of `ssagen.Compile`: after `Flush` (`Flushplist`: `linkpatch`, `progedit`, `preprocess`, `span7`, `linkpcln`, `populateDWARF`), `weakenGlobalMapInitRelocs` and `fieldtrack` | M |
| `dwarf` | `populateDWARF`'s state when `dwarfgen.Info` has returned, before the DIE writer runs (v3); its symbols at the end of `ssagen.Compile` | D |

The lexical format is the one above ("Lexical format"): strings, decimal integers, `-` for none
and empty lists, comma lists, positions `p<index>:<line>:<col>:<stmt>:<xlogue>`. Additionally:
`_` is a nil entry inside a list and the zero `Addr`; hex is lower-case (`<bytes>`: two digits
per byte, `-` when empty; `<hexnum>`: a number without leading zeros).

### File layout

```
gofv-prog 3
pkg "<base.Ctxt.Pkgpath>"
func "<f.Name>" <abi>
config <key> <value>                  (one line per key; table below)
frame
<definitions>
in <n> <off> <flags>                  (fn.Dcl when AllocFrame starts, in order)
out <n> <off> <flags>                 (fn.Dcl after AllocFrame)
opt <n> <off> <flags>                 (FuncDebug.OptDcl: the unused tail AllocFrame cut off)
merge <leader n> <followers n,…>      (MergeLocals partitions, leaders in Dcl order)
stack <stksize> <stkptrsize> <stkalign>
warn "<text>"                         (zero or more)
end
genin
<definitions>
curfn <pos> <hasdefer 0|1> <opendeferdisallowed 0|1>
wrapped "<name>" <abi>                (when curfn.WrappedFunc != nil)
opendefer <deferBitsTemp n> <closure slots n,…>   (when buildssa emitted open-coded defer info)
regargs <reg>:<offset>:<t>,…          (f.RegArgs when genssa starts)
text <y> <Args> <Locals> <FuncID> <FuncFlag> <StartLine> <attr hexnum>   (the text symbol's FuncInfo header)
warn "<text>"
end
prog0
<definitions>
p …                                   (the Prog list from pp.Text along Link, the final AEND placeholder included)
<funcinfo>
needzero <n,…>                        (Dcl names with Needzero after liveness, Dcl order)
regargs <reg>:<offset>:<t>,…          (f.RegArgs: obj register, frame offset, type)
text <size> <align> <bytes> <nrelocs> (v3: LSym.Size, Align, P, R of the text symbol at the cut)
reloc …                               (nrelocs lines: the frontend's and the SSA passes' markers)
symalign <y>:<align>,…                (v3: LSym.Align of the Prog operands' symbols, nonzero ones)
autot <y,…>                           (v3: FuncInfo.Autot, the autos' type symbols recorded for DWARF)
dbgentry <EntryID>|-                  (v3: BuildFuncDebug's result, section "DWARF" below)
dbgslot <k> <n> <t> <off>
dbgvar <k> <n> <slot,…>
dbgloc <VarID> <entry,…>
dbgregout <n,…>
dbgpc <b>:<v>:<id>,…
warn "<text>"
end
asm
<definitions>
p …                                   (the text symbol's Prog list, fn.LSym.Func().Text along Link)
<funcinfo>
text <size> <align> <bytes> <nrelocs> (LSym.Size, Align, P of the text symbol)
reloc …                               (nrelocs lines: LSym.R in append order)
pcln <pcsp y> <pcfile y> <pcline y> <pcinline y> <pcdata y|_,…> <funcdata y|_,…>
usedfiles <i,…>                       (Pcln.UsedFiles, ascending)
inltree <i> <parent> <pos> <func y|-> "<name>" <parentpc>   (Pcln.InlTree, the local tree, i = 0, 1, …)
data <y> <kind> <size> <align> <attr hexnum> <bytes> <nrelocs>   (zero or more; reloc lines follow)
warn "<text>"
end
dwarf                                 (v3; section "DWARF" below)
<definitions>
dwfn …                                (when populateDWARF ran; then the dwarfgen.Info inputs:)
dwdcl …
dwclosure …
dwmark …
dwparents …
dwparams …
dwprecursor …
dwinlfn …
dwinldcl …
dwname …
var …
scope …
inlcall …
dieref …
dieoff …
data …
warn "<text>"
end
eof
```

`<funcinfo>` is the text symbol with its `FuncInfo` at that cut:

```
fn <y> <Args> <Locals> <FuncID> <FuncFlag> <StartLine> <attr hexnum>
spill <addr> <reg> <reg2> <spill as> <unspill as>   (FuncInfo spills, RegSpill, in order)
inlmark @<prog> <global inlining index>             (FuncInfo.InlMarks, in order)
jumptable <y> <@prog,…>                             (FuncInfo.JumpTables: symbol, targets)
funcaux <GCArgs> <GCLocals> <StackObjects> <OpenCodedDeferInfo> <ArgInfo> <ArgLiveInfo> <WrapInfo>   (y or -)
```

`attr` is the raw `LSym.Attribute` (`uint32`, ABI bits included).

### Definitions

As in `.ssa` sections, a section's definition lines come right after its header, and every
object is defined before the first line that references it; numbers are per file, from 1, in
first-use order (`p` is the `XPos` index itself, `i` the global inlining index), and a
definition stays valid in later sections. Within a block, a definition follows those it
references.

- `type t<n> <size> <align> <ptrdata> <hasptr 0|1> <ptrmask> "<t.String()>"`: `t.Size()`,
  `t.Alignment()`, `types.PtrDataSize(t)`, `t.HasPointers()` and the pointer bitmap of
  `typebits.Set(t, 0, ·)` over `ptrdata / 8` words (bit `i` = word `i`, bytes little-endian;
  `-` when `ptrdata` is 0). All five are `?` when the size of `t` or of a type stored inline in
  it is not calculated. Types are numbered by the definition text (identical text, one number):
  the frame and liveness steps read only these facts, and backend type objects are not
  reproducible by pointer (see "Definitions (tables)").
- `name n<k> "<Sym().Name>" <class> t<type> <esc> "<linkname>" <linkabi> <a<aux>|->`: an
  `*ir.Name` (`ir.Class.String()`: `PAUTO`, `PPARAM`, `PPARAMOUT`), numbered by identity;
  `esc` is `n.Esc()` (0 `EscUnknown`, 1 `EscNone`, 2 `EscHeap`, 3 `EscNever`); `linkname` and
  `linkabi` are the name and ABI of the symbol `n.Linksym()` resolves to (`Sym.Linkname`, else
  `Pkg.Prefix` + `.` (`:` for the reserved `go`/`type` prefixes) + `Sym.Name`; ABIInternal for
  function symbols), computed without a lookup; `a<aux>` is the number of the same object in the
  companion `.ssa` file's aux table (`-` when that file never references it), which links the
  frame's names to the SSA's (names are not unique by symbol, class and type: inlined copies).
  Its frame offset and flags are written per cut (`in`/`out`/`opt` lines): `off` is
  `FrameOffset()` (for parameters the ABI offset, for an open-defer slot before `AllocFrame` its
  defer index); `flags` from `used`, `addrtaken`, `needzero`, `opendeferslot`, `nonmergeable`,
  `autotmp`, `outregs` (`IsOutputParamInRegisters`), `heapaddr` (`Heapaddr != nil`),
  `outheapaddr` (`IsOutputParamHeapAddr`), in that order.
- `sym y<k> "<name>" <abi>`: an `*obj.LSym`, numbered by identity (`LSym.ABI()`). Contents are
  written only in `data` lines (below) and the `text` line.
- `posbase p<index> "<abs filename>" <line> <col> <inl> <fileindex> "<filename>" "<pos filename>"
  <pos line> <pos col>`: as in `.ssa` files plus `FileIndex()` (the file number `pcfile` uses; `?`
  if the base is not registered) and (v3) `Filename()` (what `RelFilename` reports) and the
  base's own position `Pos()`: `RelFilename()`, `Line()`, `Col()` (`src.Pos.Before` compares
  `Pos().RelFilename()`; `RelLine`/`RelCol` subtract `Pos().Line()`/`Col()`; a `//line` base's
  position is the directive's).
- `inl i<k> <parent i|-> <pos> <func y|-> "<name>"`: node `k` of the global inlining tree
  (`base.Ctxt.InlTree`: parent, call position, inlined function, bare name), defined with its
  parents before the first `posbase` whose `inl` is `k`.

### Progs

`p <id> <pc> <spadj> <isize> <optab> <pool @id|-> <as> <scond> <from> <reg> <rest> <to> <regto2> <mark> <pos>`

- `id`: the Prog's stable ID. In `prog0` it is the Prog's `Pc` there (`objw` numbers every Prog
  it allocates, including those `defframe` appends, in allocation order, so IDs are unique and
  not in list order). In `asm` the Progs of `prog0` keep their ID; Progs the assembler added
  (`progedit` constants, `preprocess` prologue/epilogue/stack check, `span7` pools and
  veneers) get the next IDs (from `pp.PC`) in list order. A Prog referenced by a branch,
  `Pool`, an inline mark or a jump table but not in the list gets a fresh ID and a `warn`.
- `pc`, `spadj`, `isize`, `optab`, `scond`, `reg`, `regto2`, `mark`: the Go fields (`Optab` is
  the 1-based index into the sorted `optab` that `oplook` caches; 0 before `span7`; `Pc` is
  the byte offset after `span7`).
- `as`: `As.String()` (`TEXT`, `PCDATA`, `MOVD`, `CALL`, …; `GoFV.Asm.As`, generated by
  `tools/asgen`).
- `<from>`, `<to>`, and each `RestArgs` entry `<pos>:<addr>` (`pos` = `obj.Source` 0 or
  `obj.Destination` 1; `-` for no `RestArgs`) are an `obj.Addr`:
  `<type>/<reg>/<index>/<scale>/<name>/<class>/<offset>/<sym y|->/<val>` with `type` the
  `TYPE_` name without prefix (`NONE`, `BRANCH`, `TEXTSIZE`, `MEM`, `CONST`, `FCONST`, `SCONST`,
  `REG`, `ADDR`, `SHIFT`, `REGREG`, `REGREG2`, `INDIR`, `REGLIST`, `SPECIAL`), `name` the
  `NAME_` name (`NONE`, `EXTERN`, `STATIC`, `AUTO`, `PARAM`, `GOTREF`, `TOCREF`), registers as
  obj numbers (`REG_R0 = 8192`, …, with arrangement/extension bits), `class` the cached operand
  class (`aclass + 1`, 0 before assembly), and `val` the `Val` field: `-` (nil), `@<id>` (a
  branch target `*Prog`), `i<n>` (`int32`, `TEXTSIZE`'s argument size), `f<hexnum>` (a
  `float64`'s raw bits), `s<bytes>` (a string). The zero `Addr` is `_` (and only `_`).
- `pos`: `Prog.Pos`.

### Data symbols (`data`)

`data <y> <SymKind.String()> <Size> <Align> <attr> <P> <nrelocs>`, then `nrelocs` lines
`reloc <off> <siz> <RelocType.String()> <add> <sym y|->` (append order), for every symbol of
the file, in number order, that is one of the function's metadata symbols (the `funcaux`
symbols, the `pcln` symbols, the jump tables) or an assembler constant (name starting with
`$`: `$f64.<bits>`, `$i64.…`), except the text symbol itself (the `text` line). These are the
stack maps (`gclocals·…`: two `uint32` counts, then the bit vectors, `docs/PASSES3.md` §1.6),
stack objects, argument info, open-defer info, wrapper info, pc-value tables (pcsp, pcfile,
pcline, pcinline, pcdata: zig-zag value deltas, pc deltas in units of 4) and jump-table
words, as they are when the function's `Compile` ends: shared, content-addressed symbols
(`gclocals·`, `.wrapinfo`, constants) have deterministic contents; their kind and size are set
only later, per package, by `addGCLocals` (`gc/obj.go`), so `Sxxx 0` is what a funcdata symbol
shows here.

### DWARF (v3: `dbg*` lines of `prog0`, the `dwarf` section)

`BuildFuncDebug` (E1, `ssa/debug.go`) runs inside `genssa`; its result, `curfn.DebugInfo`
(`ssa.FuncDebug`), is in `prog0` (`dbgentry -` and no other `dbg` line when it is not set):

- `dbgentry <EntryID>`; `dbgslot <k> <n> <t> <off>`: `Slots[k]` (`N`, `Type`, `Off`; the
  splitting is in the `.ssa` file's slot table); `dbgvar <k> <n> <slot,…>`: `Vars[k]` and
  `VarSlots[k]`; `dbgloc <VarID> <entry,…>`: every nonempty `LocationLists[VarID]`, an entry
  `<StartBlock>:<StartValue>:<EndBlock>:<EndValue>:<Expr hex|->` (SSA coordinates; the value
  IDs `BlockStart` -10000, `BlockEnd` -20000, `FuncEnd` -30000); `dbgregout <n,…>`:
  `RegOutputParams`;
- `dbgpc <b>:<v>:<id>,…`: `GetPC(b, v)` at the cut for every list endpoint but `FuncEnd` and the
  entry block's `BlockStart`. `Prog.Pc` is still the Prog's number there, so this is the ID of
  the Prog whose final `Pc` the endpoint takes (`bstart`, `valueToProgAfter`); a Prog the
  assembler drops (the trailing `AEND`) keeps that number as its `Pc`.

The `dwarf` section has `populateDWARF`'s `dwarf.FnState` as `dwarfgen.Info` (E2) leaves it,
recorded by a hook before `PutAbstractFunc`/`PutConcreteFunc`/`PutDefaultFunc` run (they sort
inlined calls' variables and mark empty calls in place), and the function's DWARF symbols at the
end of `Compile`. It is empty when `populateDWARF` did not run.

- `dwfn <info y> <loc y|-> <ranges y> <absfn y|-> <lines y> "<Name>" <file>:<line> <External>
  <wrapper> <UseBASEntries> <DwTextCount>`: the symbols (`dwarfSym`), `TrimInlineHash(s.Name)`,
  `StartPos` as `FileIndex()`:`RelLine()`, `!s.Static()`, `s.Wrapper()`,
  `ctxt.UseBASEntries`, `ctxt.DwTextCount` (the `R_DWTXTADDR_U*` size depends on it).
- `dwarfgen.Info`'s inputs besides the frame, `prog0` (`autot`, `dbg*`, the text relocations)
  and the final Progs, written at the end of `Compile` (the facts are fixed by then; `Info` has
  computed the type sizes it needs). They read only state the function owns: other functions
  are compiled concurrently, and their backends write their names' facts (`Used`,
  `FrameOffset`, `Heapaddr`, `IsOutputParamInRegisters`, `Class`), so reading them makes the
  export nondeterministic. `dwdcl <n,…>` (`fn.Dcl`); `dwclosure <Needctxt()>
  <n>:<offset>,…` (the closure variables' offsets, `NewClosureStructIter`, with their `Heapaddr`
  names at the same offsets); `dwmark <pos> <scope>` (`fn.Marks`); `dwparents <scope,…>`
  (`fn.Parents`); `dwparams <n|_,…>` (`fn.Type().RecvParamsResults()` names, `_` when not an
  `*ir.Name`); `dwprecursor <fn y> <absfn y> <n,…>` (the precursor's `Inl.Dcl` of the function
  itself when it was inlined, with `AbsFuncDwarfSym`); `dwinlfn <fn y> <absfn y>` for every
  other function of the file's inlining nodes, then `dwinldcl <fn y> "<Sym().Name>"
  <IsUntyped> <Pos>` for each name of its precursor's `Inl.Dcl`, in order (all `preInliningDcls`
  and `makePreinlineDclMap` read of them); `dwname <n> <ONAME> <Used> <IsAutoTmp> <InlFormal>
  <InlLocal> <DictIndex> <FrameOffset> <IsOutputParamInRegisters> <Heapaddr n|-> <canonical
  pos|-> "<TypeSymName>"|? <IsUntyped> <TSSA> <CanSSA|?> <Pos>` for every name of `fn.Dcl`,
  the closure variables, the parameters, the function's own `dwprecursor` names, `OptDcl`,
  `Vars`, `RegOutputParams` and their `Heapaddr` names. `<canonical pos>` is
  `Canonical().Pos()` when `Canonical()` is another name (a captured variable's declaration in
  the enclosing function, `declPos`). `TypeSymName` and `CanSSA` are written only for names
  `Info` may make a variable of (`shouldEmitDwarfVar`, or an `OptDcl` name) whose type's size
  is computed, `?` otherwise.
- `var <k> <Scope> "<Name>" <Tag> <WithLoclist> <IsReturnValue> <IsInlFormal> <DictIndex>
  <StackOffset> <Type y|-> "<DeclFile>" <DeclLine> <DeclCol> <InlIndex> <ChildIndex>
  <IsInAbstract> <ClosureOffset> <list>`: every distinct `*dwarf.Var` of the scopes and inlined
  calls once (`k` = 0, 1, …, the scopes' first; identity matters: `putscope` skips the inlined
  calls' variables); `list` is `-` (`PutLocationList` nil), `v<VarID>` (the closure writes
  `LocationLists[VarID]`) or `e<entry,…>` (a list `dwarfgen` built itself, the heap
  dereference of a conservative variable), recorded by a hook in `dwarfgen`.
- `scope <k> <Parent> <ranges> <vars k,…>`, `inlcall <k> <InlIndex> <file>:<line> <AbsFunSym
  y|-> <Children,…> <Root> <ranges> <vars k,…>`: `Scopes` and `InlCalls.Calls` in order;
  `ranges` is `<Start>:<End>,…` (`-` when empty), `CallPos` as `FileIndex()`:`RelLine()`.
- `dieref <y> <reloc index> <tgt y> <dclidx>`: every `ReferenceChildDIE` on the function's
  DWARF symbols (relocation of `y` refers to child `dclidx` of the abstract function `tgt`).
  `ReferenceChildDIE` adds the child's offset to the relocation's `Add` right away when the
  target's offsets are already registered, which depends on which function finished first; the
  `data` lines therefore write those `Add`s without it (the value before any fixup), and
  `DwarfFixupTable.Finalize` adds the offsets later for the package.
- `dieoff <absfn y> <ChildIndex>:<offset>,…`: `RegisterChildDIEOffsets` of the abstract
  function written by this function.
- `data` lines (format as in `asm`) for the info, loc, ranges, line and abstract-function
  symbols that exist, at the end of `Compile`. The info symbol starts with `dwarfgen.Info`'s
  `R_USETYPE` relocations.

Not recorded: `BuildFuncDebug`'s fresh-value allocation (the IDs of the `ArgIntReg`/`ArgFloatReg`
values `PopulateABIInRegArgOps` adds come from the free list, which the `.ssa` file sorts; they
only index `valueNames` and their list entries start at `BlockStart`, so the lists do not
depend on them).

### Configuration (`config` lines)

| key | source | corpus value |
| --- | --- | --- |
| `arch` | `base.Ctxt.Arch.Name` | `arm64` |
| `goarm64` | `buildcfg.GOARM64.String()` | `"v8.0"` |
| `experiments` | `buildcfg.Experiment.Enabled()`, comma-joined | `"regabiwrappers,regabiargs,dwarf5,jsonv2,greenteagc,randomizedheapbase64,sizespecializedmalloc"` |
| `flagshared`, `flagdynlink`, `flaglinkshared` | `base.Ctxt.Flag_*` | 0, 0, 0 |
| `locationlists` | `base.Ctxt.Flag_locationlists` | 1 |
| `optimize` | `base.Ctxt.Flag_optimize` | 1 |
| `maymorestack` | `base.Ctxt.Flag_maymorestack` | `""` |
| `mergelocals` | `base.Debug.MergeLocals` | 1 |
| `flagN` | `base.Flag.N` | 0 |
| `clobberdead`, `clobberdeadreg` | `base.Flag.ClobberDead*` | 0, 0 |
| `compilingruntime` | `base.Flag.CompilingRuntime` | 1 for the runtime packages (`objabi.LookupPkgSpecial`; in the quick corpus `runtime` and `internal/bytealg`), else 0 |
| `gendwarfinl` | `base.Flag.GenDwarfInl` | 2 |
| `debugasm` | `base.Ctxt.Debugasm` (`-S`; must be 0) | 0 |
| `mergelocalshash` (v2) | `base.Debug.MergeLocalsHash` (MergeLocals' hash bisection selector) | `""` |

### Version 2

Version 2 (#549) records what the I3 port (`GoFV.Gen`, `docs/PASSES3.md` A1–C6) reads besides
the SSA after `trim` and the frame's `Dcl`, so that the port's input is the `.ssa` file plus the
`frame` input and `genin` sections:

- the `name` line's `esc`, `linkname`/`linkabi` and the `.ssa` aux link, and the `heapaddr`,
  `outheapaddr` flags (liveness reads `Esc`, `Heapaddr`, `IsOutputParamHeapAddr`; `AddAux`
  writes `n.Linksym()`);
- the `genin` section: `curfn.Pos()` (the `TEXT` position, the frameless-leaf `NOP`),
  `HasDefer()` and `OpenCodedDeferDisallowed()` (liveness), the symbol of `WrappedFunc`
  (`emitWrappedFuncInfo`), `buildssa`'s open-coded defers (`emitOpenDeferInfo`: the
  `deferBitsTemp` and closure slot names, recorded by a hook right after it), `f.RegArgs`
  (its `buildssa` result, consumed by the first `ArgIntReg` in `genssa`) and the text
  symbol's `FuncInfo` header (set by `InitTextSym`);
- `config mergelocalshash`.

Everything else in the file is as in version 1; the `.ssa` files are unchanged (quick-v9 has
the same `.ssa` files as quick-v8).

### Version 3

Version 3 (#550, #551) records what the I4 port needed beyond version 2 to be byte-exact and the
I5 cut points: the text symbol's `Size`, `Align`, `P` and `R` at the `prog0` cut (`R` holds the
zero-size marker relocations, `R_USEIFACE`, `R_USEIFACEMETHOD`, `R_USENAMEDMETHOD`, that walk,
`reflectdata` and the SSA rewrite rules put on the function before `Flushplist` appends the
assembler's), `symalign` (`Optab.size` reads `LSym.Align` of a `C_ADDR` operand's symbol, e.g. a
`.stmp_` symbol of alignment 1), the position bases' `Filename()` and `Pos()`, `autot`, the
`dbg*` lines and the `dwarf` section (hooks
`obj.GOFVPopulateDWARF`, `GOFVChildDIERef`, `GOFVChildDIEOffsets` in `obj/dwarf.go` and
`ssa.GOFVDwarfVarList` in `dwarfgen`, nil unless `GOFV_SSA_EXPORT` is set). The `.ssa` files are
unchanged.

### Determinism

The `.prog` files are byte-identical across exports (`scripts/export-corpus.sh
--check-determinism` compares them with the `.ssa` files). Functions compile concurrently; the
file writes only per-function state, symbols by name and ABI, and contents of symbols that are
the function's own or content-addressed.

### Not exported yet

From the `docs/PASSES3.md` §2 list, the first version leaves out: the intermediate graphs
inside `Flushplist` (after `linkpatch`/`progedit` and after `preprocess`, before `span7`
strips the packed `extrasize`); MergeLocals' candidates, evictions and intervals; liveness's
`Map.Vals`/`UnsafeVals`/`UnsafeBlocks`/`DeferReturn`, the partially live arguments and the
argument-liveness maps (their results are in the PCDATA Progs, `needzero`, the `defframe`
spills and the metadata symbols); `bstart` and `valueToProgAfter` (beyond the location list endpoints, `dbgpc`); the package-level
DWARF (abstract functions of inlined functions of other packages, `DwarfFixupTable.Finalize`)
and the package-level writer (F1, F2). They are added with a
version bump when I3–I5 need them.

### Reading it in Lean

`GoFV.Asm.parseProgFile : ByteArray → Except String ProgFile` and
`GoFV.Asm.printProgFile : ProgFile → String` (`GoFV/Asm/Parse.lean`, `GoFV/Asm/Print.lean`;
the IR is `GoFV/Asm/Prog.lean`, the opcodes `GoFV/Asm/As.lean`, generated by
`scripts/gen-asm.sh`). The parser is strict, so print ∘ parse is the identity on every file it
accepts; `lake exe asm-check <dir>` checks that on a corpus and that no file has a `warn` line
(`--hist FILE` writes the `oplook` histogram of the assembled Progs).

`scripts/gen-asm.sh` (`tools/asgen`, which type-checks the pinned sources with `go/types` and
never copies a value by hand) also generates the static data the ports read:
`GoFV/Asm/Reg.lean` (`GoFV.Asm.ARM64`: every integer constant of `cmd/internal/obj/arm64`'s
`a.out.go` and `sysRegEnc.go` — obj register numbers `REG_R0 = 8192` …, `REGSP`, `REGTMP`,
arrangement/extension bits, `SPOP_*` conditions, `C_*` operand classes), `GoFV/Asm/OpAsm.lean`
(`GoFV.Asm.opAsm : Op → As`, the `ssa.Op → obj.As` map `opcodeTable[op].asm`; `condBits`,
`blockJump`, `leJumps`, `gtJumps` of `compile/internal/arm64/ssa.go`) and `GoFV/Asm/Abi.lean`
(`GoFV.Asm.Abi`: the runtime-metadata constants of `internal/abi`: `PCDATA_*`, `FUNCDATA_*`,
unsafe-point values, `FuncID`/`FuncFlag`, the bounds-check codes and limits, `TraceArgs*`).
For I4 it generates `GoFV/Asm/Optab.lean` (`GoFV.Asm.ARM64`: the integer constants of
`arm64/asm7.go`, `optab` in the order `buildop` leaves it — `slices.SortFunc` with `ocmp`, run
by the generator after it checks that its `slices` sort is the pinned tree's, so `Prog.Optab = k`
is `optab[k - 1]` —, `oprange` from `buildop`'s loop and `switch`, the LSE atomic opcode maps and
the special-operand tables) and `GoFV/Asm/ObjConst.lean` (`GoFV.Asm.Obj`: the integer constants
of `cmd/internal/obj/link.go`, e.g. the `Attr*` bits, and the `objabi` relocation types with
`relocTypeNum`).

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
  `corpus/manifest.txt` lists every unit with its `.ssa` file count and digest and its `.prog`
  file count and digest (from quick-v8), the total bytes of each kind (`bytes` line), and the
  `tools/ssastats` table (functions, values, per pass how many functions changed). This is the
  quick corpus, the per-PR parity gate. Each export is a new version directory published by an
  atomic symlink switch (`docs/PARITY.md`, "Corpus versions").
- `scripts/export-corpus.sh --corpus full [--check-determinism]` exports the nightly corpus
  (#63), published as `../gofv-corpus/<pin12>/full/` (`plain/`, `*.tar.zst`; manifest
  `corpus/manifest-full.txt`): every package of `go list std` (unit `stdall`), every non-main
  package of `go list cmd` (unit `cmd`) and every command of cmd (units `cmdmain/<path>`, their
  packages are all `main`). `scripts/parity.sh --corpus full` runs the registered passes on it.
