import GoFV.Proof.Gen.G65
import GoFV.Proof.Witness.GenG2
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G65 of the genssa validator on `init.func82` of `test/gcgort`

`test/gcgort/main/init.func82,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`), loaded on P0'
(`p0PrimeSyms`, as `gen-check` runs G56 to G65):

```go
t: func() {
	u := float64(1.01)
	for i := 0; i < mods; i++ {
		u *= 1.01
		runtime.Gosched()
	}
},
```

`u` lives in the frame across the call (aux 3, `NAME_AUTO` `-8`, not converted to an integer: a
`temp` block). The loop body `b5` reloads it: value 1, `v21 = FMOVDload {u} [0] v2 v36`
(`FMOVD u-8(SP), F1`). G64 loads a float through a register or of a global only (`v21: access of a
frame variable`), so `checkG64` rejects the function; `checkG65` accepts it with the PC table `tab`
and the class table `kt`. The function needs no G48 mode (`needs48 lc = false`).

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g65_facts`),
`stepLoc` runs `v21` from a state `s0` whose memory holds `u = 1.01` (bits `X`) and the constant
symbol `$f64.3ff028f5c28f5c29` to `X` in `F1`. `FLoadPre` holds because the read finds the 8 valid
bytes of `u`, no pointer (`preF`). On a framed activation with `G49Env` (the globals at `symA`,
`u`'s block at `SP + 16`, the spill slot at `SP + 8`; not G48's mode, `outSP = false`), from a
machine `m0` holding `u`'s bytes at `SP + 16` and every V register 0, `g65_value` at the mode
`false` relates that step to the machine, which runs the `FMOVD` (`genG65_witness`): the machine's
`V1` holds `X` in its low 64 bits.
-/

namespace GoFV.Proof.Witness.GenG65

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/gcgort/main/init.func82,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "init.func82" 1 0 0
config arch arm64
config goos linux
config ptrsize 8
config regsize 8
config bigendian 0
config unalignedok 1
config havecondselect 1
config havebswap64 1
config havebswap32 1
config havebswap16 1
config hasgreg 1
config softfloat 0
config race 0
config optimize 1
config fixedframesize 8
config archalign 1
config flagshared 0
config flagdynlink 0
config usewb 1
config debugnil 0
config checkenabled 0
config localpkg "main"
config exp.cgocheck2 0
config exp.preemptibleloops 0
config exp.simd 0
config abi0 0:0:8
config abi1 16:16:8
config abiself 1
config abidefault 1
config syslook.writeBarrier "runtime.writeBarrier"
config syslook.wbZero "runtime.wbZero"
config syslook.wbMove "runtime.wbMove"
config syslook.cgoCheckPtrWrite "runtime.cgoCheckPtrWrite"
config syslook.cgoCheckMemmove "runtime.cgoCheckMemmove"
config syslook.goschedguarded "runtime.goschedguarded"
config zerobase "runtime.zerobase"
config rttype.Size_ 0:UINTPTR:8
config rttype.PtrBytes 8:UINTPTR:8
config rttype.Hash 16:UINT32:4
config rttype.Kind_ 23:UINT8:1
config rttype.GCData 32:PTR:8
config rttype.PtrType.Elem 48:PTR:8
config registers R0:8192,R1:8193,R2:8194,R3:8195,R4:8196,R5:8197,R6:8198,R7:8199,R8:8200,R9:8201,R10:8202,R11:8203,R12:8204,R13:8205,R14:8206,R15:8207,R16:8208,R17:8209,R19:8211,R20:8212,R21:8213,R22:8214,R23:8215,R24:8216,R25:8217,R26:8218,g:8220,R29:8221,R30:8222,ZERO:8223,SP:8383,F0:8224,F1:8225,F2:8226,F3:8227,F4:8228,F5:8229,F6:8230,F7:8231,F8:8232,F9:8233,F10:8234,F11:8235,F12:8236,F13:8237,F14:8238,F15:8239,F16:8240,F17:8241,F18:8242,F19:8243,F20:8244,F21:8245,F22:8246,F23:8247,F24:8248,F25:8249,F26:8250,F27:8251,F28:8252,F29:8253,F30:8254,F31:8255,SB:0
config gpregmask 13ffffff
config fpregmask 7fffffff80000000
config fp32regmask 0
config fp64regmask 0
config simdregmask 7fffffff80000000
config specialregmask 0
config intparamregs 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
config floatparamregs 31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46
config fpreg -1
config linkreg 28
config framepointer 1
config clobberdeadreg 0
config flagN 0
config fmahash 0
pass 0 "start"
type t1 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
aux a2 sym "main.init.func82" "main.init.func82" 1 - 0 - - - - 0
aux a1 call "AuxCall{main.init.func82}" a2 1 0 0 8 0 0 0
type t2 BOOL 1 1 0 comparable,named "bool" "bool"
type t3 INT8 1 1 0 comparable,named "int8" "int8"
type t4 INT16 2 2 0 comparable,named "int16" "int16"
type t5 INT32 4 4 0 comparable,named "int32" "int32"
type t6 INT64 8 8 0 comparable,named "int64" "int64"
type t7 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t8 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t9 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t10 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t7
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t5
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t9
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t15
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t12
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
posbase p2 "./gcgort.go" 1 1 -1
posbase p288 "./gcgort.go" 1 1 214
aux a3 name ".autotmp_4" ".autotmp_4" PAUTO t13 0 3 addrtaken,used,autotmp,nonmergeable p288:903:37:0:0
aux a4 type "float64" t13
type t37 STRUCT 16 8 0 comparable,named "runtime.stack" "runtime.stack" 2
field 0 "lo" t15 0 0
field 1 "hi" t15 8 0
type t40 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t39 STRUCT 96 8 88 hasptr,comparable,named "runtime._panic" "runtime._panic" 14
field 0 "arg" t40 0 0
field 1 "link" t38 16 0
field 2 "startPC" t15 24 0
field 3 "startSP" t27 32 0
field 4 "pc" t15 40 0
field 5 "sp" t27 48 0
field 6 "fp" t27 56 0
field 7 "retpc" t15 64 0
field 8 "deferBitsPtr" t17 72 0
field 9 "slotsPtr" t27 80 0
field 10 "recovered" t2 88 0
field 11 "repanicked" t2 89 0
field 12 "goexit" t2 90 0
field 13 "deferreturn" t2 91 0
type t38 PTR 8 8 8 hasptr,direct,comparable "*runtime._panic" "*runtime._panic" t39
type t46 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t45 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.UnsafePointer" "internal/runtime/atomic.UnsafePointer" 2
field 0 "noCopy" t46 0 0
field 1 "value" t27 0 0
type t44 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime._defer]" "internal/runtime/atomic.Pointer[runtime._defer]" 1
field 0 "u" t45 0 0
type t43 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime._defer]" "*internal/runtime/atomic.Pointer[runtime._defer]" t44
type t42 STRUCT 48 8 48 hasptr,named "runtime._defer" "runtime._defer" 7
field 0 "heap" t2 0 0
field 1 "rangefunc" t2 1 0
field 2 "sp" t15 8 0
field 3 "pc" t15 16 0
field 4 "fn" t1 24 0
field 5 "link" t41 32 0
field 6 "head" t43 40 0
type t41 PTR 8 8 8 hasptr,direct,comparable "*runtime._defer" "*runtime._defer" t42
type t50 UINTPTR 8 8 0 comparable,named "runtime.guintptr" "runtime.guintptr"
type t49 STRUCT 48 8 32 hasptr,comparable,named "runtime.gobuf" "runtime.gobuf" 6
field 0 "sp" t15 0 0
field 1 "pc" t15 8 0
field 2 "g" t50 16 0
field 3 "ctxt" t27 24 0
field 4 "lr" t15 32 0
field 5 "bp" t15 40 0
type t51 STRUCT 40 8 0 comparable,named "runtime.gsignalStack" "runtime.gsignalStack" 4
field 0 "stack" t37 0 0
field 1 "stackguard0" t15 16 0
field 2 "stackguard1" t15 24 0
field 3 "stktopsp" t15 32 0
type t52 ARRAY 8 4 0 comparable,named "runtime.sigset" "runtime.sigset" t9 2
type t53 ARRAY 48 8 0 comparable "[6]uintptr" "[6]uintptr" t15 6
type t54 UINTPTR 8 8 0 comparable,named "runtime.puintptr" "runtime.puintptr"
type t55 UINT32 4 4 0 comparable,named "runtime.throwType" "runtime.throwType"
type t56 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t46 0 0
field 1 "value" t9 0 0
type t60 STRUCT 24 8 0 comparable,named "runtime.sysmontick" "runtime.sysmontick" 4
field 0 "schedtick" t9 0 0
field 1 "syscalltick" t9 4 0
field 2 "schedwhen" t6 8 0
field 3 "syscallwhen" t6 16 0
type t61 UINTPTR 8 8 0 comparable,named "runtime.muintptr" "runtime.muintptr"
type t65 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t64 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t65 0 0
type t70 STRUCT 16 8 0 notinheap,comparable,named "runtime.mSpanList" "runtime.mSpanList" 3
field 0 "_" t64 0 0
field 1 "first" t67 0 0
field 2 "last" t67 8 0
type t69 PTR 8 8 0 comparable "*runtime.mSpanList" "*runtime.mSpanList" t70
type t71 UINTPTR 8 8 0 comparable,named "runtime.gclinkptr" "runtime.gclinkptr"
type t73 STRUCT 1 1 0 notinheap,comparable,named "runtime.gcBits" "runtime.gcBits" 2
field 0 "_" t64 0 0
field 1 "x" t7 0 0
type t72 PTR 8 8 0 comparable "*runtime.gcBits" "*runtime.gcBits" t73
type t74 UINT8 1 1 0 comparable,named "runtime.spanClass" "runtime.spanClass"
type t76 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t46 0 0
field 1 "value" t7 0 0
type t75 STRUCT 1 1 0 comparable,named "runtime.mSpanStateBox" "runtime.mSpanStateBox" 1
field 0 "s" t76 0 0
type t78 STRUCT 0 1 0 comparable,named "runtime.lockRankStruct" "runtime.lockRankStruct" 0
type t77 STRUCT 8 8 0 comparable,named "runtime.mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t78 0 1
field 1 "key" t15 0 0
type t81 UINT8 1 1 0 comparable,named "byte" "uint8"
type t80 STRUCT 24 8 0 notinheap,comparable,named "runtime.special" "runtime.special" 4
field 0 "_" t64 0 0
field 1 "next" t79 0 0
field 2 "offset" t15 8 0
field 3 "kind" t81 16 0
type t79 PTR 8 8 0 comparable "*runtime.special" "*runtime.special" t80
type t83 STRUCT 8 8 0 comparable,named "runtime.offAddr" "runtime.offAddr" 1
field 0 "a" t15 0 0
type t82 STRUCT 16 8 0 comparable,named "runtime.addrRange" "runtime.addrRange" 2
field 0 "base" t83 0 0
field 1 "limit" t83 8 0
type t86 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t87 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t88 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t27 ? 0
field 1 "" t27 ? 0
field 2 "" t2 ? 0
type t89 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t81
type t90 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t91 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t85 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t15 0 0
field 1 "PtrBytes" t15 8 0
field 2 "Hash" t9 16 0
field 3 "TFlag" t86 20 0
field 4 "Align_" t7 21 0
field 5 "FieldAlign_" t7 22 0
field 6 "Kind_" t87 23 0
field 7 "Equal" t88 24 0
field 8 "GCData" t89 32 0
field 9 "Str" t90 40 0
field 10 "PtrToThis" t91 44 0
type t84 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t85
type t68 STRUCT 160 8 160 hasptr,notinheap,comparable,named "runtime.mspan" "runtime.mspan" 28
field 0 "_" t64 0 0
field 1 "next" t67 0 0
field 2 "prev" t67 8 0
field 3 "list" t69 16 0
field 4 "startAddr" t15 24 0
field 5 "npages" t15 32 0
field 6 "manualFreeList" t71 40 0
field 7 "freeindex" t8 48 0
field 8 "nelems" t8 50 0
field 9 "freeIndexForScan" t8 52 0
field 10 "allocCache" t10 56 0
field 11 "allocBits" t72 64 0
field 12 "gcmarkBits" t72 72 0
field 13 "pinnerBits" t72 80 0
field 14 "sweepgen" t9 88 0
field 15 "divMul" t9 92 0
field 16 "allocCount" t8 96 0
field 17 "spanclass" t74 98 0
field 18 "state" t75 99 0
field 19 "needzero" t7 100 0
field 20 "isUserArenaChunk" t2 101 0
field 21 "allocCountBeforeCache" t8 102 0
field 22 "elemsize" t15 104 0
field 23 "limit" t15 112 0
field 24 "speciallock" t77 120 0
field 25 "specials" t79 128 0
field 26 "userArenaChunkFree" t82 136 0
field 27 "largeType" t84 152 0
type t67 PTR 8 8 0 comparable "*runtime.mspan" "*runtime.mspan" t68
type t66 ARRAY 1088 8 0 comparable "[136]*runtime.mspan" "[136]*runtime.mspan" t67 136
type t92 ARRAY 1088 8 0 comparable "[136]runtime.gclinkptr" "[136]runtime.gclinkptr" t71 136
type t94 STRUCT 16 8 0 comparable,named "runtime.stackfreelist" "runtime.stackfreelist" 2
field 0 "list" t71 0 0
field 1 "size" t15 8 0
type t93 ARRAY 64 8 0 comparable "[4]runtime.stackfreelist" "[4]runtime.stackfreelist" t94 4
type t63 STRUCT 2296 8 0 notinheap,comparable,named "runtime.mcache" "runtime.mcache" 11
field 0 "_" t64 0 0
field 1 "nextSample" t6 0 0
field 2 "memProfRate" t11 8 0
field 3 "scanAlloc" t15 16 0
field 4 "tiny" t15 24 0
field 5 "tinyoffset" t15 32 0
field 6 "tinyAllocs" t15 40 0
field 7 "alloc" t66 48 0
field 8 "reusableNoscan" t92 1136 0
field 9 "stackcache" t93 2224 0
field 10 "flushGen" t56 2288 0
type t62 PTR 8 8 0 comparable "*runtime.mcache" "*runtime.mcache" t63
type t95 STRUCT 24 8 0 comparable,named "runtime.pageCache" "runtime.pageCache" 3
field 0 "base" t15 0 0
field 1 "cache" t10 8 0
field 2 "scav" t10 16 0
type t98 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime.m]" "internal/runtime/atomic.Pointer[runtime.m]" 1
field 0 "u" t45 0 0
type t97 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime.m]" "*internal/runtime/atomic.Pointer[runtime.m]" t98
type t96 STRUCT 8 8 8 hasptr,direct,comparable,named "runtime.mWeakPointer" "runtime.mWeakPointer" 1
field 0 "m" t97 0 0
type t99 SLICE 24 8 8 hasptr "[]*runtime._defer" "[]*runtime._defer" t41
type t100 ARRAY 256 8 256 hasptr,comparable "[32]*runtime._defer" "[32]*runtime._defer" t41 32
type t101 ARRAY 2048 8 0 comparable "[256]runtime.guintptr" "[256]runtime.guintptr" t50 256
type t102 STRUCT 16 8 0 comparable,named "runtime.gList" "runtime.gList" 2
field 0 "head" t50 0 0
field 1 "size" t5 8 0
type t106 STRUCT 16 8 8 hasptr,comparable,named "runtime.maybeTraceablePtr" "runtime.maybeTraceablePtr" 2
field 0 "vp" t27 0 0
field 1 "vu" t15 8 0
type t107 STRUCT 16 8 8 hasptr,comparable,named "runtime.maybeTraceableChan" "runtime.maybeTraceableChan" 1
field 0 "maybeTraceablePtr" t106 0 1
type t105 STRUCT 104 8 96 hasptr,comparable,named "runtime.sudog" "runtime.sudog" 14
field 0 "g" t35 0 0
field 1 "next" t104 8 0
field 2 "prev" t104 16 0
field 3 "elem" t106 24 0
field 4 "acquiretime" t6 40 0
field 5 "releasetime" t6 48 0
field 6 "ticket" t9 56 0
field 7 "isSelect" t2 60 0
field 8 "success" t2 61 0
field 9 "waiters" t8 62 0
field 10 "parent" t104 64 0
field 11 "waitlink" t104 72 0
field 12 "waittail" t104 80 0
field 13 "c" t107 88 0
type t104 PTR 8 8 8 hasptr,direct,comparable "*runtime.sudog" "*runtime.sudog" t105
type t103 SLICE 24 8 8 hasptr "[]*runtime.sudog" "[]*runtime.sudog" t104
type t108 ARRAY 1024 8 1024 hasptr,comparable "[128]*runtime.sudog" "[128]*runtime.sudog" t104 128
type t110 ARRAY 1024 8 0 comparable "[128]*runtime.mspan" "[128]*runtime.mspan" t67 128
type t109 STRUCT 1032 8 0 comparable "struct { runtime.len int; runtime.buf [128]*runtime.mspan }" "struct { runtime.len int; runtime.buf [128]*runtime.mspan }" 2
field 0 "len" t11 0 0
field 1 "buf" t110 8 0
type t113 SLICE 24 8 8 hasptr "[]unsafe.Pointer" "[]unsafe.Pointer" t27
type t114 ARRAY 40 8 40 hasptr,comparable "[5]unsafe.Pointer" "[5]unsafe.Pointer" t27 5
type t112 STRUCT 64 8 64 hasptr,named "runtime.pinner" "runtime.pinner" 2
field 0 "refs" t113 0 0
field 1 "refStore" t114 24 0
type t111 PTR 8 8 8 hasptr,direct,comparable "*runtime.pinner" "*runtime.pinner" t112
type t117 ARRAY 12 4 0 comparable "[3]atomic.Uint32" "[3]internal/runtime/atomic.Uint32" t56 3
type t118 ARRAY 16 8 0 comparable "[2]uint64" "[2]uint64" t10 2
type t116 STRUCT 32 8 0 comparable,named "runtime.traceSchedResourceState" "runtime.traceSchedResourceState" 2
field 0 "statusTraced" t117 0 0
field 1 "seq" t118 16 0
type t115 STRUCT 64 8 0 comparable,named "runtime.pTraceState" "runtime.pTraceState" 6
field 0 "traceSchedResourceState" t116 0 1
field 1 "mSyscallID" t6 32 0
field 2 "maySweep" t2 40 0
field 3 "inSweep" t2 41 0
field 4 "swept" t15 48 0
field 5 "reclaimed" t15 56 0
type t121 STRUCT 0 1 0 notinheap,comparable,named "runtime.notInHeap" "runtime.notInHeap" 1
field 0 "_" t64 0 0
type t120 PTR 8 8 0 comparable "*runtime.notInHeap" "*runtime.notInHeap" t121
type t119 STRUCT 16 8 0 comparable,named "runtime.persistentAlloc" "runtime.persistentAlloc" 2
field 0 "base" t120 0 0
field 1 "off" t15 8 0
type t123 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t122 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t46 0 0
field 1 "_" t123 0 0
field 2 "value" t6 0 0
type t125 STRUCT 8 8 0 comparable,named "atomic.Uint64" "internal/runtime/atomic.Uint64" 3
field 0 "noCopy" t46 0 0
field 1 "_" t123 0 0
field 2 "value" t10 0 0
type t124 STRUCT 8 8 0 comparable,named "runtime.limiterEvent" "runtime.limiterEvent" 1
field 0 "stamp" t125 0 0
type t126 INT 8 8 0 comparable,named "runtime.gcMarkWorkerMode" "runtime.gcMarkWorkerMode"
type t129 STRUCT 16 8 0 comparable,named "runtime.lfnode" "runtime.lfnode" 2
field 0 "next" t10 0 0
field 1 "pushcnt" t15 8 0
type t128 STRUCT 32 8 0 comparable,named "runtime.gcBgMarkWorkerNode" "runtime.gcBgMarkWorkerNode" 3
field 0 "node" t129 0 0
field 1 "gp" t50 16 0
field 2 "m" t61 24 0
type t127 PTR 8 8 8 hasptr,direct,comparable "*runtime.gcBgMarkWorkerNode" "*runtime.gcBgMarkWorkerNode" t128
type t133 STRUCT 24 8 0 comparable,named "runtime.workbufhdr" "runtime.workbufhdr" 2
field 0 "node" t129 0 0
field 1 "nobj" t11 16 0
type t134 ARRAY 2024 8 0 comparable "[253]uintptr" "[253]uintptr" t15 253
type t132 STRUCT 2048 8 0 notinheap,comparable,named "runtime.workbuf" "runtime.workbuf" 3
field 0 "_" t64 0 0
field 1 "workbufhdr" t133 0 1
field 2 "obj" t134 24 0
type t131 PTR 8 8 0 comparable "*runtime.workbuf" "*runtime.workbuf" t132
type t137 UINTPTR 8 8 0 comparable,named "runtime.objptr" "runtime.objptr"
type t136 ARRAY 2048 8 0 comparable "[256]runtime.objptr" "[256]runtime.objptr" t137 256
type t141 STRUCT 16 8 0 comparable,named "runtime.listNodeManual" "runtime.listNodeManual" 2
field 0 "prev" t15 0 0
field 1 "next" t15 8 0
type t142 STRUCT 1 1 0 comparable,named "atomic.Bool" "internal/runtime/atomic.Bool" 1
field 0 "u" t76 0 0
type t143 PTR 8 8 8 hasptr,direct,comparable "*runtime.objptr" "*runtime.objptr" t137
type t140 STRUCT 56 8 56 hasptr,notinheap,comparable,named "runtime.spanSPMC" "runtime.spanSPMC" 8
field 0 "_" t64 0 0
field 1 "allnode" t141 0 0
field 2 "dead" t142 16 0
field 3 "prev" t45 24 0
field 4 "head" t56 32 0
field 5 "tail" t56 36 0
field 6 "cap" t9 40 0
field 7 "ring" t143 48 0
type t139 PTR 8 8 0 comparable "*runtime.spanSPMC" "*runtime.spanSPMC" t140
type t138 STRUCT 16 8 16 hasptr,comparable "struct { runtime.head *runtime.spanSPMC; runtime.tail atomic.UnsafePointer }" "struct { runtime.head *runtime.spanSPMC; runtime.tail internal/runtime/atomic.UnsafePointer }" 2
field 0 "head" t139 0 0
field 1 "tail" t45 8 0
type t135 STRUCT 2080 8 2080 hasptr,comparable,named "runtime.spanQueue" "runtime.spanQueue" 5
field 0 "head" t9 0 0
field 1 "tail" t9 4 0
field 2 "ring" t136 8 0
field 3 "putsSinceDrain" t11 2056 0
field 4 "chain" t138 2064 0
type t145 ARRAY 8192 8 0 comparable "[1024]uintptr" "[1024]uintptr" t15 1024
type t144 PTR 8 8 8 hasptr,direct,comparable "*[1024]uintptr" "*[1024]uintptr" t145
type t147 STRUCT 40 8 0 comparable,named "runtime.sizeClassScanStats" "runtime.sizeClassScanStats" 5
field 0 "spansDenseScanned" t10 0 0
field 1 "spanObjsDenseScanned" t10 8 0
field 2 "spansSparseScanned" t10 16 0
field 3 "spanObjsSparseScanned" t10 24 0
field 4 "sparseObjsScanned" t10 32 0
type t146 ARRAY 2720 8 0 comparable "[68]runtime.sizeClassScanStats" "[68]runtime.sizeClassScanStats" t147 68
type t130 STRUCT 4856 8 2112 hasptr,comparable,named "runtime.gcWork" "runtime.gcWork" 10
field 0 "id" t5 0 0
field 1 "wbuf1" t131 8 0
field 2 "wbuf2" t131 16 0
field 3 "spanq" t135 24 0
field 4 "ptrBuf" t144 2104 0
field 5 "bytesMarked" t10 2112 0
field 6 "heapScanWork" t6 2120 0
field 7 "flushedWork" t2 2128 0
field 8 "mayNeedWorker" t2 2129 0
field 9 "stats" t146 2136 0
type t149 ARRAY 4096 8 0 comparable "[512]uintptr" "[512]uintptr" t15 512
type t148 STRUCT 4112 8 0 comparable,named "runtime.wbBuf" "runtime.wbBuf" 3
field 0 "next" t15 0 0
field 1 "end" t15 8 0
field 2 "buf" t149 16 0
type t155 FUNC 8 8 8 hasptr,direct "func(any, uintptr, int64)" "func(interface {}, uintptr, int64)" 0 3 0
field 0 "arg" t40 ? 0
field 1 "seq" t15 ? 0
field 2 "delay" t6 ? 0
type t156 PTR 8 8 8 hasptr,direct,comparable "*runtime.timers" "*runtime.timers" t150
type t157 STRUCT 4 4 0 comparable,named "atomic.Int32" "internal/runtime/atomic.Int32" 2
field 0 "noCopy" t46 0 0
field 1 "value" t5 0 0
type t154 STRUCT 96 8 80 hasptr,named "runtime.timer" "runtime.timer" 15
field 0 "mu" t77 0 0
field 1 "astate" t76 8 0
field 2 "state" t7 9 0
field 3 "isChan" t2 10 0
field 4 "isFake" t2 11 0
field 5 "blocked" t9 12 0
field 6 "rand" t9 16 0
field 7 "when" t6 24 0
field 8 "period" t6 32 0
field 9 "f" t155 40 0
field 10 "arg" t40 48 0
field 11 "seq" t15 64 0
field 12 "ts" t156 72 0
field 13 "sendLock" t77 80 0
field 14 "isSending" t157 88 0
type t153 PTR 8 8 8 hasptr,direct,comparable "*runtime.timer" "*runtime.timer" t154
type t152 STRUCT 16 8 8 hasptr,comparable,named "runtime.timerWhen" "runtime.timerWhen" 2
field 0 "timer" t153 0 0
field 1 "when" t6 8 0
type t151 SLICE 24 8 8 hasptr "[]runtime.timerWhen" "[]runtime.timerWhen" t152
type t150 STRUCT 64 8 16 hasptr,named "runtime.timers" "runtime.timers" 7
field 0 "mu" t77 0 0
field 1 "heap" t151 8 0
field 2 "len" t56 32 0
field 3 "zombies" t157 36 0
field 4 "raceCtx" t15 40 0
field 5 "minWhenHeap" t122 48 0
field 6 "minWhenModified" t122 56 0
type t160 STRUCT 32 8 0 notinheap,comparable,named "runtime.cleanupBlockHeader" "runtime.cleanupBlockHeader" 4
field 0 "_" t64 0 0
field 1 "lfnode" t129 0 1
field 2 "alllink" t158 16 0
field 3 "n" t9 24 0
type t165 STRUCT 8 8 0 comparable,named "runtime.funcval" "runtime.funcval" 1
field 0 "fn" t15 0 0
type t164 PTR 8 8 8 hasptr,direct,comparable "*runtime.funcval" "*runtime.funcval" t165
type t163 FUNC 8 8 8 hasptr,direct "func(*runtime.funcval, unsafe.Pointer)" "func(*runtime.funcval, unsafe.Pointer)" 0 2 0
field 0 "" t164 ? 0
field 1 "" t27 ? 0
type t162 STRUCT 24 8 24 hasptr,named "runtime.cleanupFn" "runtime.cleanupFn" 3
field 0 "call" t163 0 0
field 1 "fn" t164 8 0
field 2 "arg" t27 16 0
type t161 ARRAY 480 8 480 hasptr "[20]runtime.cleanupFn" "[20]runtime.cleanupFn" t162 20
type t159 STRUCT 512 8 512 hasptr,notinheap,named "runtime.cleanupBlock" "runtime.cleanupBlock" 2
field 0 "cleanupBlockHeader" t160 0 1
field 1 "cleanups" t161 32 0
type t158 PTR 8 8 0 comparable "*runtime.cleanupBlock" "*runtime.cleanupBlock" t159
type t168 ARRAY 16 1 0 comparable "[16]byte" "[16]uint8" t81 16
type t167 STRUCT 512 1 0 comparable,named "runtime.xRegs" "runtime.xRegs" 32
field 0 "V0" t168 0 0
field 1 "V1" t168 16 0
field 2 "V2" t168 32 0
field 3 "V3" t168 48 0
field 4 "V4" t168 64 0
field 5 "V5" t168 80 0
field 6 "V6" t168 96 0
field 7 "V7" t168 112 0
field 8 "V8" t168 128 0
field 9 "V9" t168 144 0
field 10 "V10" t168 160 0
field 11 "V11" t168 176 0
field 12 "V12" t168 192 0
field 13 "V13" t168 208 0
field 14 "V14" t168 224 0
field 15 "V15" t168 240 0
field 16 "V16" t168 256 0
field 17 "V17" t168 272 0
field 18 "V18" t168 288 0
field 19 "V19" t168 304 0
field 20 "V20" t168 320 0
field 21 "V21" t168 336 0
field 22 "V22" t168 352 0
field 23 "V23" t168 368 0
field 24 "V24" t168 384 0
field 25 "V25" t168 400 0
field 26 "V26" t168 416 0
field 27 "V27" t168 432 0
field 28 "V28" t168 448 0
field 29 "V29" t168 464 0
field 30 "V30" t168 480 0
field 31 "V31" t168 496 0
type t170 STRUCT 512 1 0 notinheap,comparable,named "runtime.xRegState" "runtime.xRegState" 2
field 0 "_" t64 0 0
field 1 "regs" t167 0 0
type t169 PTR 8 8 0 comparable "*runtime.xRegState" "*runtime.xRegState" t170
type t166 STRUCT 520 8 0 comparable,named "runtime.xRegPerP" "runtime.xRegPerP" 2
field 0 "scratch" t167 0 0
field 1 "cache" t169 512 0
type t59 STRUCT 14320 8 13688 hasptr,named "runtime.p" "runtime.p" 46
field 0 "id" t5 0 0
field 1 "status" t9 4 0
field 2 "link" t54 8 0
field 3 "schedtick" t9 16 0
field 4 "syscalltick" t9 20 0
field 5 "sysmontick" t60 24 0
field 6 "m" t61 48 0
field 7 "mcache" t62 56 0
field 8 "pcache" t95 64 0
field 9 "raceprocctx" t15 88 0
field 10 "oldm" t96 96 0
field 11 "deferpool" t99 104 0
field 12 "deferpoolbuf" t100 128 0
field 13 "goidcache" t10 384 0
field 14 "goidcacheend" t10 392 0
field 15 "runqhead" t9 400 0
field 16 "runqtail" t9 404 0
field 17 "runq" t101 408 0
field 18 "runnext" t50 2456 0
field 19 "gFree" t102 2464 0
field 20 "sudogcache" t103 2480 0
field 21 "sudogbuf" t108 2504 0
field 22 "mspancache" t109 3528 0
field 23 "pinnerCache" t111 4560 0
field 24 "trace" t115 4568 0
field 25 "palloc" t119 4632 0
field 26 "gcAssistTime" t6 4648 0
field 27 "gcFractionalMarkTime" t122 4656 0
field 28 "limiterEvent" t124 4664 0
field 29 "gcMarkWorkerMode" t126 4672 0
field 30 "gcMarkWorkerStartTime" t6 4680 0
field 31 "nextGCMarkWorker" t127 4688 0
field 32 "gcw" t130 4696 0
field 33 "wbBuf" t148 9552 0
field 34 "runSafePointFn" t9 13664 0
field 35 "statsSeq" t56 13668 0
field 36 "timers" t150 13672 0
field 37 "cleanups" t158 13736 0
field 38 "cleanupsQueued" t10 13744 0
field 39 "maxStackScanDelta" t6 13752 0
field 40 "scannedStackSize" t10 13760 0
field 41 "scannedStacks" t10 13768 0
field 42 "preempt" t2 13776 0
field 43 "gcStopTime" t6 13784 0
field 44 "goroutinesCreated" t10 13792 0
field 45 "xRegs" t166 13800 0
type t58 PTR 8 8 8 hasptr,direct,comparable "*runtime.p" "*runtime.p" t59
type t57 SLICE 24 8 8 hasptr "[]*runtime.p" "[]*runtime.p" t58
type t172 ARRAY 256 8 0 comparable,named "runtime.cgoCallers" "runtime.cgoCallers" t15 32
type t171 PTR 8 8 8 hasptr,direct,comparable "*runtime.cgoCallers" "*runtime.cgoCallers" t172
type t173 STRUCT 8 8 0 comparable,named "runtime.note" "runtime.note" 1
field 0 "key" t15 0 0
type t174 ARRAY 256 8 0 comparable "[32]uintptr" "[32]uintptr" t15 32
type t175 STRUCT 16 8 0 comparable,named "runtime.mWaitList" "runtime.mWaitList" 2
field 0 "next" t61 0 0
field 1 "startTicks" t6 8 0
type t177 SLICE 24 8 8 hasptr "[]uintptr" "[]uintptr" t15
type t176 STRUCT 56 8 16 hasptr,named "runtime.mLockProfile" "runtime.mLockProfile" 6
field 0 "waitTime" t122 0 0
field 1 "stack" t177 8 0
field 2 "cycles" t6 32 0
field 3 "cyclesLost" t6 40 0
field 4 "haveStack" t2 48 0
field 5 "disabled" t2 49 0
type t178 FUNC 8 8 8 hasptr,direct "func(*runtime.g, unsafe.Pointer) bool" "func(*runtime.g, unsafe.Pointer) bool" 0 2 1
field 0 "" t35 ? 0
field 1 "" t27 ? 0
field 2 "" t2 ? 0
type t179 UINT8 1 1 0 comparable,named "runtime.traceBlockReason" "runtime.traceBlockReason"
type t186 UINT64 8 8 0 comparable,named "runtime.traceTime" "runtime.traceTime"
type t185 STRUCT 32 8 0 comparable,named "runtime.traceBufHeader" "runtime.traceBufHeader" 4
field 0 "link" t183 0 0
field 1 "lastTime" t186 8 0
field 2 "pos" t11 16 0
field 3 "lenPos" t11 24 0
type t187 ARRAY 65504 1 0 comparable "[65504]byte" "[65504]uint8" t81 65504
type t184 STRUCT 65536 8 0 notinheap,comparable,named "runtime.traceBuf" "runtime.traceBuf" 3
field 0 "_" t64 0 0
field 1 "traceBufHeader" t185 0 1
field 2 "arr" t187 32 0
type t183 PTR 8 8 0 comparable "*runtime.traceBuf" "*runtime.traceBuf" t184
type t182 ARRAY 16 8 0 comparable "[2]*runtime.traceBuf" "[2]*runtime.traceBuf" t183 2
type t181 ARRAY 32 8 0 comparable "[2][2]*runtime.traceBuf" "[2][2]*runtime.traceBuf" t182 2
type t180 STRUCT 72 8 48 hasptr,comparable,named "runtime.mTraceState" "runtime.mTraceState" 6
field 0 "writing" t142 0 0
field 1 "buf" t181 8 0
field 2 "link" t47 40 0
field 3 "reentered" t9 48 0
field 4 "entryGen" t15 56 0
field 5 "oldthrowsplit" t2 64 0
type t188 STRUCT 0 1 0 comparable,named "runtime.winlibcall" "runtime.winlibcall" 0
type t192 STRUCT 24 8 0 comparable,named "runtime.pcvalueCacheEnt" "runtime.pcvalueCacheEnt" 4
field 0 "targetpc" t15 0 0
field 1 "off" t9 8 0
field 2 "val" t5 12 0
field 3 "valPC" t15 16 0
type t191 ARRAY 192 8 0 comparable "[8]runtime.pcvalueCacheEnt" "[8]runtime.pcvalueCacheEnt" t192 8
type t190 ARRAY 384 8 0 comparable "[2][8]runtime.pcvalueCacheEnt" "[2][8]runtime.pcvalueCacheEnt" t191 2
type t189 STRUCT 392 8 0 comparable,named "runtime.pcvalueCache" "runtime.pcvalueCache" 2
field 0 "entries" t190 0 0
field 1 "inUse" t11 384 0
type t193 STRUCT 0 1 0 comparable,named "runtime.dlogPerM" "runtime.dlogPerM" 0
type t194 STRUCT 24 8 0 comparable,named "runtime.mOS" "runtime.mOS" 5
field 0 "profileTimer" t5 0 0
field 1 "profileTimerValid" t142 4 0
field 2 "needPerThreadSyscall" t76 5 0
field 3 "vgetrandomState" t15 8 0
field 4 "waitsema" t9 16 0
type t196 ARRAY 256 8 0 comparable "[32]uint64" "[32]uint64" t10 32
type t197 ARRAY 32 8 0 comparable "[4]uint64" "[4]uint64" t10 4
type t195 STRUCT 304 8 0 comparable,named "chacha8rand.State" "internal/chacha8rand.State" 5
field 0 "buf" t196 0 0
field 1 "seed" t197 256 0
field 2 "i" t9 288 0
field 3 "n" t9 292 0
field 4 "c" t9 296 0
type t200 INT64 8 8 0 comparable,named "runtime.lockRank" "runtime.lockRank"
type t199 STRUCT 16 8 0 comparable,named "runtime.heldLockInfo" "runtime.heldLockInfo" 2
field 0 "lockAddr" t15 0 0
field 1 "rank" t200 8 0
type t198 ARRAY 160 8 0 comparable "[10]runtime.heldLockInfo" "[10]runtime.heldLockInfo" t199 10
type t48 STRUCT 1832 8 1832 hasptr,named "runtime.m" "runtime.m" 75
field 0 "g0" t35 0 0
field 1 "morebuf" t49 8 0
field 2 "divmod" t9 56 0
field 3 "procid" t10 64 0
field 4 "gsignal" t35 72 0
field 5 "goSigStack" t51 80 0
field 6 "sigmask" t52 120 0
field 7 "tls" t53 128 0
field 8 "mstartfn" t1 176 0
field 9 "curg" t35 184 0
field 10 "caughtsig" t50 192 0
field 11 "signalSecret" t2 200 0
field 12 "p" t54 208 0
field 13 "nextp" t54 216 0
field 14 "oldp" t54 224 0
field 15 "id" t6 232 0
field 16 "mallocing" t5 240 0
field 17 "throwing" t55 244 0
field 18 "preemptoff" t16 248 0
field 19 "locks" t5 264 0
field 20 "dying" t5 268 0
field 21 "profilehz" t5 272 0
field 22 "spinning" t2 276 0
field 23 "blocked" t2 277 0
field 24 "newSigstack" t2 278 0
field 25 "printlock" t3 279 0
field 26 "incgo" t2 280 0
field 27 "isextra" t2 281 0
field 28 "isExtraInC" t2 282 0
field 29 "isExtraInSig" t2 283 0
field 30 "freeWait" t56 284 0
field 31 "needextram" t2 288 0
field 32 "g0StackAccurate" t2 289 0
field 33 "traceback" t7 290 0
field 34 "allpSnapshot" t57 296 0
field 35 "ncgocall" t10 320 0
field 36 "ncgo" t5 328 0
field 37 "cgoCallersUse" t56 332 0
field 38 "cgoCallers" t171 336 0
field 39 "park" t173 344 0
field 40 "alllink" t47 352 0
field 41 "schedlink" t61 360 0
field 42 "idleNode" t141 368 0
field 43 "lockedg" t50 384 0
field 44 "createstack" t174 392 0
field 45 "lockedExt" t9 648 0
field 46 "lockedInt" t9 652 0
field 47 "mWaitList" t175 656 0
field 48 "ditEnabled" t2 672 0
field 49 "mLockProfile" t176 680 0
field 50 "profStack" t177 736 0
field 51 "waitunlockf" t178 760 0
field 52 "waitlock" t27 768 0
field 53 "waitTraceSkip" t11 776 0
field 54 "waitTraceBlockReason" t179 784 0
field 55 "syscalltick" t9 788 0
field 56 "freelink" t47 792 0
field 57 "trace" t180 800 0
field 58 "libcallpc" t15 872 0
field 59 "libcallsp" t15 880 0
field 60 "libcallg" t50 888 0
field 61 "winsyscall" t188 896 0
field 62 "vdsoSP" t15 896 0
field 63 "vdsoPC" t15 904 0
field 64 "preemptGen" t56 912 0
field 65 "signalPending" t56 916 0
field 66 "pcvalueCache" t189 920 0
field 67 "dlogPerM" t193 1312 1
field 68 "mOS" t194 1312 1
field 69 "chacha8" t195 1336 0
field 70 "cheaprand" t9 1640 0
field 71 "cheaprand64" t10 1648 0
field 72 "locksHeldLen" t11 1656 0
field 73 "locksHeld" t198 1664 0
field 74 "self" t96 1824 0
type t47 PTR 8 8 8 hasptr,direct,comparable "*runtime.m" "*runtime.m" t48
type t201 UINT8 1 1 0 comparable,named "runtime.waitReason" "runtime.waitReason"
type t202 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t81
type t205 STRUCT 40 8 8 hasptr,named "runtime.ancestorInfo" "runtime.ancestorInfo" 3
field 0 "pcs" t177 0 0
field 1 "goid" t10 24 0
field 2 "gopc" t15 32 0
type t204 SLICE 24 8 8 hasptr "[]runtime.ancestorInfo" "[]runtime.ancestorInfo" t205
type t203 PTR 8 8 8 hasptr,direct,comparable "*[]runtime.ancestorInfo" "*[]runtime.ancestorInfo" t204
type t206 STRUCT 4 4 0 comparable,named "runtime.goroutineProfileStateHolder" "runtime.goroutineProfileStateHolder" 2
field 0 "noCopy" t46 0 0
field 1 "value" t9 0 0
type t209 FUNC 8 8 8 hasptr,direct "func(*runtime.coro)" "func(*runtime.coro)" 0 1 0
field 0 "" t207 ? 0
type t208 STRUCT 32 8 24 hasptr,named "runtime.coro" "runtime.coro" 5
field 0 "gp" t50 0 0
field 1 "f" t209 8 0
field 2 "mp" t47 16 0
field 3 "lockedExt" t9 24 0
field 4 "lockedInt" t9 28 0
type t207 PTR 8 8 8 hasptr,direct,comparable "*runtime.coro" "*runtime.coro" t208
type t211 STRUCT 144 8 112 hasptr,named "runtime.synctestBubble" "runtime.synctestBubble" 12
field 0 "mu" t77 0 0
field 1 "timers" t150 8 0
field 2 "id" t10 72 0
field 3 "now" t6 80 0
field 4 "root" t35 88 0
field 5 "waiter" t35 96 0
field 6 "main" t35 104 0
field 7 "waiting" t2 112 0
field 8 "done" t2 113 0
field 9 "total" t11 120 0
field 10 "running" t11 128 0
field 11 "active" t11 136 0
type t210 PTR 8 8 8 hasptr,direct,comparable "*runtime.synctestBubble" "*runtime.synctestBubble" t211
type t212 STRUCT 8 8 0 comparable,named "runtime.xRegPerG" "runtime.xRegPerG" 1
field 0 "state" t169 0 0
type t213 STRUCT 32 8 0 comparable,named "runtime.gTraceState" "runtime.gTraceState" 1
field 0 "traceSchedResourceState" t116 0 1
type t36 STRUCT 456 8 400 hasptr,named "runtime.g" "runtime.g" 65
field 0 "stack" t37 0 0
field 1 "stackguard0" t15 16 0
field 2 "stackguard1" t15 24 0
field 3 "_panic" t38 32 0
field 4 "_defer" t41 40 0
field 5 "m" t47 48 0
field 6 "sched" t49 56 0
field 7 "syscallsp" t15 104 0
field 8 "syscallpc" t15 112 0
field 9 "syscallbp" t15 120 0
field 10 "stktopsp" t15 128 0
field 11 "param" t27 136 0
field 12 "atomicstatus" t56 144 0
field 13 "stackLock" t9 148 0
field 14 "goid" t10 152 0
field 15 "schedlink" t50 160 0
field 16 "waitsince" t6 168 0
field 17 "waitreason" t201 176 0
field 18 "preempt" t2 177 0
field 19 "preemptStop" t2 178 0
field 20 "preemptShrink" t2 179 0
field 21 "asyncSafePoint" t2 180 0
field 22 "paniconfault" t2 181 0
field 23 "gcscandone" t2 182 0
field 24 "throwsplit" t2 183 0
field 25 "activeStackChans" t2 184 0
field 26 "parkingOnChan" t142 185 0
field 27 "inMarkAssist" t2 186 0
field 28 "coroexit" t2 187 0
field 29 "raceignore" t3 188 0
field 30 "nocgocallback" t2 189 0
field 31 "tracking" t2 190 0
field 32 "trackingSeq" t7 191 0
field 33 "trackingStamp" t6 192 0
field 34 "runnableTime" t6 200 0
field 35 "lockedm" t61 208 0
field 36 "fipsIndicator" t7 216 0
field 37 "fipsOnlyBypass" t2 217 0
field 38 "ditWanted" t2 218 0
field 39 "syncSafePoint" t2 219 0
field 40 "runningCleanups" t142 220 0
field 41 "sig" t9 224 0
field 42 "secret" t5 228 0
field 43 "writebuf" t202 232 0
field 44 "sigcode0" t15 256 0
field 45 "sigcode1" t15 264 0
field 46 "sigpc" t15 272 0
field 47 "parentGoid" t10 280 0
field 48 "gopc" t15 288 0
field 49 "ancestors" t203 296 0
field 50 "startpc" t15 304 0
field 51 "racectx" t15 312 0
field 52 "waiting" t104 320 0
field 53 "cgoCtxt" t177 328 0
field 54 "labels" t27 352 0
field 55 "timer" t153 360 0
field 56 "sleepWhen" t6 368 0
field 57 "selectDone" t56 376 0
field 58 "goroutineProfiled" t206 380 0
field 59 "coroarg" t207 384 0
field 60 "bubble" t210 392 0
field 61 "xRegs" t212 400 0
field 62 "trace" t213 408 0
field 63 "gcAssistBytes" t6 440 0
field 64 "valgrindStackID" t15 448 0
type t35 PTR 8 8 8 hasptr,direct,comparable "*runtime.g" "*runtime.g" t36
type t34 FUNC 8 8 8 hasptr,direct "func(*runtime.g)" "func(*runtime.g)" 0 1 0
field 0 "gp" t35 ? 0
type t33 PTR 8 8 8 hasptr,direct,comparable "*func(*runtime.g)" "*func(*runtime.g)" t34
aux a5 sym "runtime.gosched_m\xc2\xb7f" "runtime.gosched_m\xc2\xb7f" 0 - 0 - - - - 0
posbase p289 "runtime/proc.go" 1 1 215
aux a7 sym "runtime.mcall" "runtime.mcall" 1 - 0 - - - - 0
aux a6 call "AuxCall{runtime.mcall}" a7 1 1 0 8 8 1 0
abiparam in 0 t34 - 0 0
aux a8 name "~r0" "~r0" PAUTO t23 0 1 - p288:903:16:0:0
slot s1 a8 t23 0 - 0
aux a9 name "a" "a" PAUTO t23 0 1 used p2:903:4:0:0
slot s2 a9 t23 0 - 0
aux a10 name "i" "i" PAUTO t11 0 1 used p2:905:8:0:0
slot s3 a10 t11 0 - 0
f b1 t1 a1 37 8
typs Bool=t2,Int8=t3,Int16=t4,Int32=t5,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Plain p2:903:48:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p2:905:4:0:0 0 0 - - b3:0 b1:0
v v9 Copy t23 0 - p2:903:6:2:0 2 v8
v v11 Copy t28 0 - p2:904:4:2:0 2 v7
v v12 NilCheck t23 0 - p2:904:4:0:0 1 v9,v11
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v11
b b3 If p2:905:20:0:0 1 0 - v17 b4:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:0:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 2 v13,v30
v v37 Phi t23 0 - p2:905:18:0:0 1 v9,v18
b b4 Plain p289:402:15:0:0 0 0 - - b7:0 b3:0
v v18 Copy t23 0 - p2:906:5:2:0 3 v37
v v19 Copy t28 0 - p2:906:5:2:0 4 v36
v v20 NilCheck t23 0 - p2:906:5:0:0 1 v18,v19
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v19
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v18,v19
v v24 Store t28 0 a4 p2:906:8:0:0 3 v23,v22,v19
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v26 InlMark t30 216 - p289:402:15:1:0 0 v24
b b5 Plain p2:905:27:0:0 0 0 - - b3:1 b8:0
v v31 Copy t11 0 - p2:905:27:2:0 1 v15
v v33 Add64 t11 0 - p2:905:27:0:0 1 v31,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v34 Copy t28 0 - p2:909:3:2:0 1 v36
v v35 MakeResult t32 0 - p2:909:3:0:0 1 v34
b b7 Plain p2:907:20:0:0 0 0 - - b8:0 b4:0
v v28 Copy t28 0 - p289:403:7:2:0 1 v24
v v29 StaticLECall t32 8 a6 p289:403:7:0:0 1 v27,v28
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b8 Plain p2:905:27:2:0 0 0 - - b5:0 b7:0
names s1,s2,s3
named s1 v8,v9
named s2 v9,v18,v37
named s3 v14,v15,v31,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 37 8
b b1 Plain p2:903:48:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 b1:0
v v9 Copy t23 0 - p2:903:6:2:0 2 v8
v v11 Copy t28 0 - p2:904:4:2:0 2 v7
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v9,v11
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v11
b b3 If p2:905:20:0:0 1 0 - v17 b4:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 2 v13,v30
v v37 Phi t23 0 - p2:905:18:0:0 1 v9,v18
b b4 Plain p289:402:15:0:0 0 0 - - b7:0 b3:0
v v18 Copy t23 0 - p2:906:5:2:0 3 v37
v v19 Copy t28 0 - p2:906:5:2:0 4 v36
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v18,v19
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v19
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v18,v19
v v24 Store t28 0 a4 p2:906:8:0:0 3 v23,v22,v19
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v26 InlMark t30 216 - p289:402:15:1:0 0 v24
b b5 Plain p2:905:27:0:0 0 0 - - b3:1 b8:0
v v31 Copy t11 0 - p2:905:27:2:0 1 v15
v v33 Add64 t11 0 - p2:905:27:1:0 1 v31,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v34 Copy t28 0 - p2:909:3:2:0 1 v36
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v34
b b7 Plain p2:907:20:1:0 0 0 - - b8:0 b4:0
v v28 Copy t28 0 - p289:403:7:2:0 1 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v28
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b8 Plain p2:907:20:1:0 0 0 - - b5:0 b7:0
names s1,s2,s3
named s1 v8,v9
named s2 v9,v18,v37
named s3 v14,v15,v31,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev -
freeb -
cache postorder b5,b8,b7,b4,b6,b3,b2,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 37 8
b b1 Plain p2:903:48:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 4 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 6 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 b1:0
v v9 Copy t23 0 - p2:903:6:2:0 0 v8
v v11 Copy t28 0 - p2:904:4:2:0 0 v7
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v8,v7
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b4:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 3 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 7 v13,v30
v v37 Copy t23 0 - p2:905:18:0:0 0 v8
b b4 Plain p289:402:15:0:0 0 0 - - b7:0 b3:0
v v18 Copy t23 0 - p2:906:5:2:0 0 v8
v v19 Copy t28 0 - p2:906:5:2:0 0 v36
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v8,v36
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v8,v36
v v24 Store t28 0 a4 p2:906:8:0:0 4 v23,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v26 InlMark t30 216 - p289:402:15:1:0 0 v24
b b5 Plain p2:905:27:0:0 0 0 - - b3:1 b8:0
v v31 Copy t11 0 - p2:905:27:2:0 0 v15
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v34 Copy t28 0 - p2:909:3:2:0 0 v36
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
b b7 Plain p2:907:20:1:0 0 0 - - b8:0 b4:0
v v28 Copy t28 0 - p289:403:7:2:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b8 Plain p2:907:20:1:0 0 0 - - b5:0 b7:0
names s1,s2,s3
named s1 v8,v8
named s2 v8,v8,v8
named s3 v14,v15,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev -
freeb -
cache postorder b5,b8,b7,b4,b6,b3,b2,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 37 8
b b1 Plain p2:903:48:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 3 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 b1:0
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v8,v7
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b4:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 5 v13,v30
b b4 Plain p289:402:15:1:0 0 0 - - b7:0 b3:0
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v8,v36
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v8,v36
v v24 Store t28 0 a4 p2:906:8:0:0 2 v23,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
b b5 Plain p2:905:27:0:0 0 0 - - b3:1 b8:0
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
b b7 Plain p2:907:20:1:0 0 0 - - b8:0 b4:0
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b8 Plain p2:907:20:1:0 0 0 - - b5:0 b7:0
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb -
cache postorder b5,b8,b7,b4,b6,b3,b2,b1
cache linestarts 2:903:909,289:402:403:402=3
dcllen 5
end
pass 4 "short circuit"
f b2 t1 a1 37 8
b b1 BlockInvalid p2:903:48:1:0 0 0 - - - -
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 3 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v8,v7
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 5 v13,v30
b b4 BlockInvalid p289:402:15:1:0 0 0 - - - -
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v8,v36
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v8,v36
v v24 Store t28 0 a4 p2:906:8:0:0 2 v23,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
b b7 BlockInvalid p2:907:20:1:0 0 0 - - - -
b b8 BlockInvalid p2:907:20:1:0 0 0 - - - -
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb -
cache linestarts 2:903:909,289:402:403:402=3
dcllen 5
end
pass 5 "decompose user"
f b2 t1 a1 37 8
b b1 BlockInvalid p2:903:48:1:0 0 0 - - - -
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 3 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v8,v7
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 5 v13,v30
b b4 BlockInvalid p289:402:15:1:0 0 0 - - - -
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v8,v36
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v8,v36
v v24 Store t28 0 a4 p2:906:8:0:0 2 v23,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
b b7 BlockInvalid p2:907:20:1:0 0 0 - - - -
b b8 BlockInvalid p2:907:20:1:0 0 0 - - - -
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb -
cache linestarts 2:903:909,289:402:403:402=3
dcllen 5
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 3 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v12 NilCheck t23 0 - p2:904:4:1:0 1 v8,v7
v v13 Store t28 0 a4 p2:904:7:0:0 1 v12,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 5 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v20 NilCheck t23 0 - p2:906:5:1:0 1 v8,v36
v v21 Load t13 0 - p2:906:5:0:0 1 v20,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v23 NilCheck t23 0 - p2:906:5:0:0 1 v8,v36
v v24 Store t28 0 a4 p2:906:8:0:0 2 v23,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 7 "opt"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v8,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v8,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v8,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 8 "zero arg cse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v8,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v8,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v8,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 9 "opt deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 1 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v8,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v8,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v8,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 10 "generic cse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 0 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 11 "phiopt"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 2 v6,v5,v1
v v8 LocalAddr t23 0 a3 p288:903:37:2:0 0 v2,v7
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s1,s2,s3
named s1 v8
named s2 v8
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 12 "gcse deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 13 "nilcheckelim"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 14 "prove"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 15 "divisible"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 16 "divmod"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 17 "middle opt"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 18 "known bits"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 19 "early fuse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticLECall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 20 "expand calls"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 21 "decompose builtin"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 22 "softfloat"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 23 "branchelim"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 24 "late opt"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 25 "dead auto elim"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v8,v23,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 26 "sccp"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
v v8 ConstBool t2 1 - p2:905:18:1:0 0 -
v v23 Const64 t11 1 - p2:905:27:1:0 0 -
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 27 "generic deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 28 "late fuse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 29 "check bce"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 1 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 4 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Store t28 0 a4 p288:903:37:2:0 1 v6,v5,v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 30 "dse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 0 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Copy t28 0 - p288:903:37:2:0 1 v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 31 "memcombine"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 0 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Copy t28 0 - p288:903:37:2:0 1 v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 32 "writebarrier"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v5 Const64F t13 0 - p0:0:0:0:0 0 -
v v10 Const64F t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 Const64 t11 0 - p0:0:0:0:0 1 -
v v16 Const64 t11 8 - p0:0:0:0:0 1 -
v v32 Const64 t11 1 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v6 LocalAddr t23 0 a3 p288:903:37:2:0 3 v2,v1
v v27 Addr t33 0 a5 p0:0:0:0:0 1 v3
v v7 Copy t28 0 - p288:903:37:2:0 1 v1
v v13 Store t28 0 a4 p2:904:7:1:0 1 v6,v10,v7
b b3 If p2:905:20:0:0 1 0 - v17 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v17 Less64 t2 0 - p2:905:18:1:0 1 v15,v16
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 Load t13 0 - p2:906:5:1:0 1 v6,v36
v v33 Add64 t11 0 - p2:905:27:1:0 1 v15,v32
v v22 Mul64F t13 0 - p2:906:8:0:0 1 v21,v10
v v24 Store t28 0 a4 p2:906:8:0:0 2 v6,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 StaticCall t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts 0=v5,v14,1=v32,8=v16,4607227454796291113=v10
freev v23,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:905=0,289:402:403
dcllen 5
end
pass 33 "lower"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64MOVDconst t11 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 34 "addressing modes"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64MOVDconst t11 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 35 "late lower"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 36 "pair"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v4 InlMark t30 214 - p2:903:48:1:0 0 v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:903=0,289:402:403
dcllen 5
end
pass 38 "lowered cse"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:903=0,289:402:403
dcllen 5
end
pass 39 "elim unread autos"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:903=0,289:402:403
dcllen 5
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909:903=0,289:402:403
dcllen 5
end
pass 41 "lowered deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 42 "checkLower"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 43 "loop invariant"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 45 "tighten"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 46 "late deadcode"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 47 "critical"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 48 "phi tighten"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 49 "likelyadjust"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
dcllen 5
end
pass 50 "layout"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v10,v1
v v27 ARM64MOVDaddr t33 0 a5 p0:0:0:0:0 1 v3
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v14,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v10
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v27,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v15
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v4,v17,v7,v6,v32,v16,v5,v8,v20,v12,v28,v34,v31,v26,v19,v18,v37,v11,v9
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:0 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
aux a6 call "AuxCall{runtime.mcall}" a7 1 1 0 8 8 1 0
abiparam in 0 t34 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64FMOVDconst t13 4607227454796291113 - p2:904:7:2:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v4,v1
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v32 Copy t11 0 - p2:905:18:2:0 1 v14
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v32,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v7 StoreReg t11 0 - p2:905:18:0:0 1 v15
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v4
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v17 ARM64MOVDaddr t33 0 a5 p289:403:7:2:0 1 v3
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v17,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v6 LoadReg t11 0 - p2:905:27:2:0 1 v7
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v6
v v16 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 0 -
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v5,v8,v9,v11,v12,v18,v19,v20,v26,v28,v31,v34,v37
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b3,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b3:-:-:14:17,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:1 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
fstate scheduled,laidout
regalloc 34 v2:SP,v3:SB,v4:F0,v6:R1,v7:@a10/t11/0/-/0,v14:ZERO,v15:R0,v16:F0,v17:R0,v21:F1,v22:F0,v29:[],v32:R0,v33:R0
dcllen 5
end
pass 55 "loop rotate"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64FMOVDconst t13 4607227454796291113 - p2:904:7:2:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v4,v1
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v32 Copy t11 0 - p2:905:18:2:0 1 v14
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v7 StoreReg t11 0 - p2:905:18:0:0 1 v15
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v4
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v17 ARM64MOVDaddr t33 0 a5 p289:403:7:2:0 1 v3
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v17,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v6 LoadReg t11 0 - p2:905:27:2:0 1 v7
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v6
v v16 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 0 -
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v32,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v5,v8,v9,v11,v12,v18,v19,v20,v26,v28,v31,v34,v37
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b5:b3,b3:b2,b6:b3
cache sdom b2:-:b3:-:2:23,b5:b3:-:-:14:17,b3:b2:b6:-:5:20,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:1 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
hotness b5:3
fstate scheduled,laidout
regalloc 34 v2:SP,v3:SB,v4:F0,v6:R1,v7:@a10/t11/0/-/0,v14:ZERO,v15:R0,v16:F0,v17:R0,v21:F1,v22:F0,v29:[],v32:R0,v33:R0
dcllen 5
end
pass 56 "trim"
f b2 t1 a1 37 8
b b2 Plain p2:905:4:1:0 0 0 - - b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64FMOVDconst t13 4607227454796291113 - p2:904:7:2:0 2 -
v v13 ARM64FMOVDstore t28 0 a3 p2:904:7:1:0 1 v2,v4,v1
v v14 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v32 Copy t11 0 - p2:905:18:2:0 1 v14
b b5 Plain p2:907:20:1:0 0 0 - - b3:1 b3:0
v v7 StoreReg t11 0 - p2:905:18:0:0 1 v15
v v21 ARM64FMOVDload t13 0 a3 p2:906:5:1:0 1 v2,v36
v v22 ARM64FMULD t13 0 - p2:906:8:0:0 1 v21,v4
v v24 ARM64FMOVDstore t28 0 a3 p2:906:8:0:0 2 v2,v22,v36
v v25 InlMark t30 215 - p2:907:20:1:0 0 v24
v v17 ARM64MOVDaddr t33 0 a5 p289:403:7:2:0 1 v3
v v29 ARM64CALLstatic t32 8 a6 p289:403:7:1:0 1 v17,v24
v v30 SelectN t28 0 - p289:403:7:0:0 1 v29
v v6 LoadReg t11 0 - p2:905:27:2:0 1 v7
v v33 ARM64ADDconst t11 1 - p2:905:27:1:0 1 v6
v v16 ARM64FMOVDconst t13 4607227454796291113 - p0:0:0:0:0 0 -
b b3 ARM64LT p2:905:20:0:0 1 0 - v23 b5:0,b6:0 b2:0,b5:0
v v15 Phi t11 0 - p2:905:18:0:0 2 v32,v33
v v36 Phi t28 0 - p2:905:18:0:0 3 v13,v30
v v23 ARM64CMPconst t29 8 - p2:905:18:1:0 1 v15
b b6 Ret p2:909:3:0:0 0 0 - v35 - b3:1
v v35 MakeResult t32 0 - p2:909:3:1:0 1 v36
names s3
named s3 v14,v15,v33
splits -
canon a8/t23/0/-/0=s1,a9/t23/0/-/0=s2,a10/t11/0/-/0=s3
consts -
freev v5,v8,v9,v11,v12,v18,v19,v20,v26,v28,v31,v34,v37
freeb b8,b7,b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b5:b3,b3:b2,b6:b3
cache sdom b2:-:b3:-:2:23,b5:b3:-:-:14:17,b3:b2:b6:-:5:20,b6:b3:-:b5:8:11
cache loopnest 9 0 b3:-:2:1:1:1 b3:0,b5:0
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:903:909,289:402:403
hotness b5:3
fstate scheduled,laidout
regalloc 34 v2:SP,v3:SB,v4:F0,v6:R1,v7:@a10/t11/0/-/0,v14:ZERO,v15:R0,v16:F0,v17:R0,v21:F1,v22:F0,v29:[],v32:R0,v33:R0
dcllen 5
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t24,t25,t26,t81,t89,t202
typelink t7=t81,t17=t89,t28=t32
typecmp t7 t87 gt
typeorder t3,t7=t81,t87,t86,t74,t201,t179,t4,t8,t5,t90,t91,t9,t55,t6,t200,t10,t186,t11,t126,t14,t137,t15,t50,t61,t54,t71,t25,t26,t12,t13,t2,t17=t89,t18,t19,t20,t143,t21,t22,t23,t24,t33,t203,t144,t171,t35,t47,t58,t207,t84,t67,t104,t153,t41,t38,t72,t62,t111,t156,t164,t79,t131,t139,t183,t69,t120,t169,t158,t210,t127,t97,t43,t1,t34,t209,t163,t178,t88,t155,t202,t177,t57,t103,t99,t151,t204,t113,t118,t182,t181,t190,t117,t197,t93,t114,t53,t191,t198,t168,t161,t196,t174,t100,t146,t110,t108,t92,t66,t134,t136,t101,t149,t145,t187,t52,t172,t109,t138,t36,t48,t59,t194,t65,t208,t173,t85,t142,t102,t49,t68,t77,t37,t105,t154,t148,t167,t195,t157,t122,t76,t42,t39,t73,t130,t129,t63,t112,t150,t56,t125,t46,t165,t83,t80,t132,t123,t193,t140,t184,t212,t166,t82,t162,t70,t175,t121,t95,t135,t152,t170,t64,t60,t188,t133,t213,t180,t115,t205,t159,t51,t199,t124,t176,t96,t189,t75,t94,t45,t141,t78,t211,t185,t192,t119,t106,t160,t128,t107,t147,t98,t116,t44,t206,t40,t16,t27,t28,t30,t29,t31,t32
eof
"#

/-- `test/gcgort/main/init.func82,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "init.func82" 1
config arch arm64
config goarm64 "v8.0"
config experiments "regabiwrappers,regabiargs,dwarf5,jsonv2,greenteagc,randomizedheapbase64,sizespecializedmalloc"
config flagshared 0
config flagdynlink 0
config flaglinkshared 0
config locationlists 1
config optimize 1
config maymorestack ""
config mergelocals 1
config flagN 0
config clobberdead 0
config clobberdeadreg 0
config compilingruntime 0
config gendwarfinl 2
config debugasm 0
config mergelocalshash ""
frame
type t1 8 8 8 1 01 "*float64"
name n1 "a" PAUTO t1 1 "main.a" 0 a9
type t2 8 8 0 0 - "int"
name n2 "i" PAUTO t2 1 "main.i" 0 a10
name n3 "~r0" PAUTO t1 1 "main.~r0" 0 a8
name n4 ".autotmp_3" PAUTO t1 3 "main..autotmp_3" 0 -
type t3 8 8 0 0 - "float64"
name n5 ".autotmp_4" PAUTO t3 3 "main..autotmp_4" 0 a3
in n1 0 used
in n2 0 used
in n3 0 -
in n4 0 used,autotmp
in n5 0 used,addrtaken,nonmergeable,autotmp
out n5 -8 used,addrtaken,nonmergeable,autotmp
out n2 -16 used
opt n4 0 autotmp
opt n1 0 -
opt n3 0 -
stack 16 0 8
end
genin
posbase p2 "./gcgort.go" 1 1 -1 1 "./gcgort.go" "./gcgort.go" 1 1
sym y1 "main.init.func82" 1
curfn p2:902:13:0:0 0 0
regargs -
text y1 0 0 0 0 902 208080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main..autotmp_4" 0
sym y4 "main.i" 0
sym y5 "runtime.gosched_m\xc2\xb7f" 0
sym y6 "runtime.Gosched" 1
inl i215 - p2:907:20:0:0 y6 "Gosched"
posbase p289 "runtime/proc.go" 1 1 215 2 "runtime/proc.go" "runtime/proc.go" 1 1
sym y7 "runtime.mcall" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i0 0 0 p2:902:13:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:902:13:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:902:13:0:0
p 3 3 0 0 0 - FMOVD 0 FCONST/0/0/0/NONE/0/0/-/f3ff028f5c28f5c29 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:904:7:1:0
p 4 4 0 0 0 - FMOVD 0 REG/8224/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y3/- 0 0 p2:904:7:2:0
p 5 5 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:905:18:1:0
p 6 6 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@18 0 0 p2:905:4:2:0
p 7 7 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-16/y4/- 0 0 p2:905:18:2:0
p 8 8 0 0 0 - FMOVD 0 MEM/8383/0/0/AUTO/0/-8/y3/- 0 - REG/8225/0/0/NONE/0/0/-/- 0 0 p2:906:5:1:0
p 9 9 0 0 0 - FMULD 0 REG/8224/0/0/NONE/0/0/-/- 8225 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:906:8:2:0
p 10 10 0 0 0 - FMOVD 0 REG/8224/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y3/- 0 0 p2:906:8:2:0
p 11 11 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2:907:20:1:0
p 12 12 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p289:403:7:1:0
p 13 13 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p289:403:7:1:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p289:403:7:1:0
p 15 15 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-16/y4/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:905:27:1:0
p 16 16 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:905:27:2:0
p 17 17 0 0 0 - FMOVD 0 FCONST/0/0/0/NONE/0/0/-/f3ff028f5c28f5c29 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:905:27:2:0
p 18 18 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/8/-/- 8192 - _ 0 0 p2:905:18:1:0
p 19 19 0 0 0 - BLT 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@7 0 0 p2:905:20:2:0
p 20 20 0 0 0 - RET 0 _ 0 - _ 0 0 p2:909:3:0:0
p 21 21 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 902 208080
inlmark @11 215
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 2
dbgslot 0 n2 t2 0
dbgvar 0 n2 0
dbgloc 0 2:32:-1:-30000:50
dbgregout -
dbgpc 2:32:6
end
asm
sym y8 "$f64.3ff028f5c28f5c29" 0
sym y9 "runtime.morestack_noctxt" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i0 0 0 p2:902:13:0:0
p 22 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:902:13:0:0
p 23 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:902:13:0:0
p 24 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:902:13:0:0
p 25 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@38 0 0 p2:902:13:0:0
p 26 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:902:13:0:0
p 27 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p2:902:13:0:1
p 28 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:902:13:0:0
p 29 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:902:13:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:902:13:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:902:13:0:0
p 30 24 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:902:13:0:0
p 3 24 0 0 162 - FMOVD 0 MEM/0/0/0/EXTERN/110/0/y8/f3ff028f5c28f5c29 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:904:7:1:0
p 31 32 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:904:7:1:0
p 4 32 0 0 140 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y3/- 0 0 p2:904:7:2:0
p 5 36 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:905:18:1:0
p 6 40 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/18/-/@18 0 0 p2:905:4:2:0
p 7 44 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/48/-16/y4/- 0 0 p2:905:18:2:0
p 8 48 0 0 153 - FMOVD 0 MEM/0/0/0/AUTO/47/-8/y3/- 0 - REG/8225/0/0/NONE/5/0/-/- 0 0 p2:906:5:1:0
p 9 52 0 0 112 - FMULD 0 REG/8224/0/0/NONE/5/0/-/- 8225 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:906:8:2:0
p 10 56 0 0 140 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y3/- 0 0 p2:906:8:2:0
p 11 60 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:907:20:1:0
p 12 64 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p289:403:7:1:0
p 13 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p289:403:7:1:0
p 14 72 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p289:403:7:1:0
p 15 76 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/48/-16/y4/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:905:27:1:0
p 16 80 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:905:27:2:0
p 32 84 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:905:27:2:0
p 17 84 0 0 162 - FMOVD 0 MEM/0/0/0/EXTERN/110/0/y8/f3ff028f5c28f5c29 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:905:27:2:0
p 33 92 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:905:27:2:0
p 18 92 0 0 96 - CMP 0 CONST/0/0/0/NONE/17/8/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:905:18:1:0
p 19 96 0 0 80 - BLT 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/7/-/@7 0 0 p2:905:20:2:0
p 20 100 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:909:3:0:0
p 34 104 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:909:3:0:0
p 35 108 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:909:3:0:0
p 36 112 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:909:3:0:0
p 37 112 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:902:13:0:0
p 38 112 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:902:13:0:0
p 39 112 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:902:13:0:0
p 40 116 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p2:902:13:0:0
p 41 120 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:902:13:0:0
p 42 120 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@22 0 0 p2:902:13:0:0
fn y1 0 40 0 0 902 208080
inlmark @11 215
funcaux y2 y2 - - - - -
text 128 0 900b40f9ff6330eb49030054fe0f1df8fd831ff8fd2300d11b000090600340fde01300fde0031faa0d000014e00f00f9e11340fd2008601ee01300fd1f2003d5000000900000009100000094e10f40f9200400911b000090600340fd1f2000f16bfeff54fd835ff8fe0743f8c0035fd6e3031eaa00000094e2ffff1700000000 5
reloc 24 8 R_ARM64_PCREL_LDST64 0 y8
reloc 64 8 R_ADDRARM64 0 y5
reloc 72 4 R_CALLARM64 0 y7
reloc 84 8 R_ARM64_PCREL_LDST64 0 y8
reloc 116 4 R_CALLARM64 0 y9
pcln y12 y13 y14 y15 y10,y11 y2,y2
usedfiles 1,2
inltree 0 -1 p2:907:20:0:0 y6 "Gosched" 60
data y2 Sxxx 0 4 8000 0100000000000000 0
data y8 SRODATA 8 8 8800 295c8fc2f528f03f 0
data y10 SRODATA 19 1 28000 0001010202030302040d050206050102020200 0
data y11 SRODATA 7 1 28000 0012020a010400 0
data y12 SRODATA 7 1 28000 020460175f0500 0
data y13 SRODATA 7 1 28000 04100203010d00 0
data y14 SRODATA 22 1 28000 8e0e060403020302030201ef0703ec070608030d0400 0
data y15 SRODATA 7 1 28000 00100203010d00 0
end
dwarf
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "main.init.func82.1" 1
inl i214 - p2:903:48:0:0 y20 "init.func82.1"
posbase p288 "./gcgort.go" 1 1 214 1 "./gcgort.go" "./gcgort.go" 1 1
sym y21 "go:info.main.init.func82.1$abstract" 0
sym y22 "go:info.runtime.Gosched$abstract" 0
sym y23 "go:info.int" 0
dwfn y16 y17 y18 - y19 "main.init.func82" 1:902 1 0 1 221
dwdcl n5,n2
dwclosure 0 -
dwmark p2:905:4:0:0 1
dwmark p2:908:4:0:0 0
dwparents 0
dwparams -
dwinlfn y20 y21
dwinlfn y6 y22
dwinldcl y20 "~r0" 0 p2:903:16:0:0
dwname n5 1 1 1 0 0 0 -8 0 - - ? 0 0 ? p288:903:37:0:0
dwname n2 1 1 0 0 0 0 -16 0 - - "int" 0 0 1 p2:905:8:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "*float64" 0 0 1 p288:903:37:0:0
dwname n1 1 0 0 0 0 0 0 0 - - "*float64" 0 0 1 p2:903:4:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "*float64" 0 0 1 p288:903:16:0:0
var 0 0 "i" 52 1 0 0 0 -24 y23 "./gcgort.go" 905 8 0 0 0 0 v0
scope 0 0 0:128 -
scope 1 0 36:64,76:100 0
inlcall 0 215 1:907 y22 - 1 64:76 -
data y16 SDWARFFCN 67 0 0 036d61696e2e696e69742e66756e6338320000008001019c020000008607010c000000002769008907000000000000000000090000000000000000020000008b070000 6
reloc 18 2 R_DWTXTADDR_U2 0 y1
reloc 32 4 R_DWARFSECREF 0 y18
reloc 41 4 R_DWARFSECREF 0 y23
reloc 45 4 R_DWARFSECREF 0 y17
reloc 51 4 R_DWARFSECREF 0 y22
reloc 55 4 R_DWARFSECREF 10 y18
data y17 SDWARFLOC 10 0 0 01000004288001015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y18 SDWARFRANGE 17 0 0 010000042440044c640001000004404c00 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 11 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFLINES 60 0 0 00090200000000000000000402038007140a8789065f063806370660063706600403038c7c33040203f1038c063706870637063b037d830210000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 to G65). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `init.func82`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G65's check runs on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

/-- P0'. -/
def ps : Array GoFV.Asm.Prog :=
  match stIn with
  | .ok x => x.2.1
  | .error _ => #[]

def bs : ID → Option Nat :=
  match stIn with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

def g : G2In :=
  match stIn with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG65` gives. -/
def tab : PcTab := (match checkG65 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG65` gives. -/
def kt : KTab := (match checkG65 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b5`, the loop body, whose value 1 is `v21 = FMOVDload {u} [0] v2 v36`. -/
def blk : Block := (lc.ctx.f.block? 5).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 32-byte frame with 8 bytes of extra
space, every symbol at `symA`; `NAME_AUTO` `-8` (`u`) is `SP + 16`, `-16` (the spill slot) `SP + 8`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- `ι`: GenG2's (the nil block, the globals at `symA`), and `u`'s block of activation 0
(`temp 0 3`) at `SP + 16`. -/
def ι65 (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 3 then some (GenG2.sp0 + 16) else GenG2.ι b

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the home
slot at its frame operand and the PC table of `checkG65`; not G48's mode (`outSP = false`). -/
def E : MatchEnv :=
  { lc, ι := ι65, sp := GenG2.sp0,
    slot := fun k =>
      if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The float constant symbol of `1.01`. -/
def cName : String := "$f64.3ff028f5c28f5c29"

/-- Its allocation: the eight little-endian bytes of `1.01`'s bits, read-only. -/
def cAl : Alloc := roAlloc (leBytesU8 0x3ff028f5c28f5c29 8)

/-- The bits of `u` before the multiplication: `1.01`. -/
def X : BitVec 64 := 0x3ff028f5c28f5c29

/-- `u`'s block: the eight little-endian bytes of `X`, writable. -/
def uAl : Alloc := { data := Array.ofFn (n := 8) fun i => .b (BitVec.ofNat 8 (X.toNat / 256 ^ i.val)) }

/-- The Phase 1 memory before `v21`: the constant symbol, read-only, and `u` holding `X`. -/
def mem1 : Mem := { blocks := #[(.global cName, cAl), (.temp 0 3, uAl)] }

/-- `u`'s address: its block at offset 0. -/
def pU : Ptr := ⟨.temp 0 3, 0⟩

/-- Byte `k` of `X`, little-endian (0 past the eighth). -/
def xByte : Nat → BitVec 8
  | 0 => 0x29 | 1 => 0x5c | 2 => 0x8f | 3 => 0xc2 | 4 => 0xf5 | 5 => 0x28 | 6 => 0xf0 | 7 => 0x3f
  | _ => 0

/-- The machine memory before `v21`: `1.01`'s bits, little-endian, at `symA` and at `SP + 16`, 0
elsewhere. -/
def M1 : Memory := fun y =>
  if y - GenG2.symA < 8 then xByte (y - GenG2.symA).toNat
  else if y - (GenG2.sp0 + 16) < 8 then xByte (y - (GenG2.sp0 + 16)).toNat
  else 0

/-- The `runLoc` state before `v21`: every register `poison`, no slot, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v21`: the activation's `g` and `FP`, every V register 0, the PC of `v21`,
the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 5 1,
    mem := M1 }

/-- The home slots have at most 8 bytes and lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    decide ((E.lc.slotTy k).size ≤ 8) &&
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- The home slots lie below `u`'s block. -/
def slotsBelow : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (frameOff L nc off + 8 ≤ 16)
    | none => true

/-- `F1` (Go register 32) holds `X`. -/
def f1Is (s : LocState) : Bool :=
  match (s.regs[32]? : Option Val) with
  | some (Val.int .w64 x) => x == X
  | _ => false

theorem f1Is_spec {s : LocState} (h : f1Is s = true) : s.regs[32]? = some (.int .w64 X) := by
  unfold f1Is at h
  split at h
  · rename_i x hx
    simp only [beq_iff_eq] at h
    subst h
    exact hx
  · cases h

/-- A value that is no pointer. -/
def notPtr : Val → Bool
  | .ptr _ => false
  | _ => true

theorem notPtr_spec {x : Val} (h : notPtr x = true) : ∀ q, x ≠ .ptr q := by
  intro q hq
  subst hq
  cases h

/-- What compiled evaluation checks on `init.func82`: it holds an arm64 op; on P0', `checkG65`
accepts it with `tab` and `kt` and `checkG64` does not (G64 has no float load of a frame variable);
the only accessed frame variable is `u` (aux 3, `NAME_AUTO` `-8`, not converted to an integer, a
`temp` block), of activation 0, at `frameOff 16`; its home slots fit below `u`; it needs no G48
mode; `b5` holds `v21` (`FMOVDload`) at index 1, where G35's table is empty; `v21` accesses `u` at
offset 0 (`frameVar?`); the float constant symbols among G2's symbols are `$f64.3ff0…` alone, with
`cAl`; `mem1` reads 8 bytes at `u`, no pointer at `v21`'s shape; `stepLoc` runs `v21` from `s0` to
`X` in `F1` (Go register 32). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG65 lc0 ps bs g).toOption == some (tab, kt) && (checkG64 lc0 ps bs g).toOption.isNone &&
    accessedVars lc == [3] && varOp g 3 == some (.AUTO, -8) && !lc.ctx.tabs.forgeable 3 &&
    lc.ctx.act == 0 && decide (frameOff L .AUTO (-8) = 16) && slotsFit && slotsBelow &&
    needs48 lc == false &&
    lc.ctx.f.blocks.toList.contains 5 && (lc.ctx.f.block? 5).isSome &&
    (lc.ctx.f.value? 21).isSome && blk.values[1]? == some 21 &&
    (val 21).op == .ARM64FMOVDload && (val 21).auxInt.toInt == 0 &&
    (match frameVar? lc g (val 21) with | .ok (some (3, -8)) => true | _ => false) &&
    constRo (symNames g) == [(cName, cAl)] &&
    uL35 lc (uIn35 lc 5) blk 1 == [] &&
    (mem1.read pU 8).isSome &&
    notPtr ((Arm64.loadN (lc.ty (val 21).id) 8 false mem1 pU).retypeL (lc.ty (val 21).id)) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 21)) f1Is

theorem g65_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG65 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG64 lc0 ps bs g).toOption = none ∧
      accessedVars lc = [3] ∧ varOp g 3 = some (.AUTO, -8) ∧ lc.ctx.tabs.forgeable 3 = false ∧
      lc.ctx.act = 0 ∧ frameOff L .AUTO (-8) = 16 ∧ slotsFit = true ∧ slotsBelow = true ∧
      needs48 lc = false ∧
      5 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 5 = some blk ∧
      lc.ctx.f.value? 21 = some (val 21) ∧ blk.values[1]? = some 21 ∧
      (val 21).op = .ARM64FMOVDload ∧ (val 21).auxInt.toInt = 0 ∧
      frameVar? lc g (val 21) = .ok (some (3, -8)) ∧
      constRo (symNames g) = [(cName, cAl)] ∧
      uL35 lc (uIn35 lc 5) blk 1 = [] ∧
      (mem1.read pU 8).isSome = true ∧
      notPtr ((Arm64.loadN (lc.ty (val 21).id) 8 false mem1 pU).retypeL (lc.ty (val 21).id)) =
        true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 21)) f1Is = true := by
  have hf := g65_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none, decide_eq_true_eq, Bool.not_eq_true'] at hf
  obtain ⟨hl, hres, h64, hav, hvo, hfg, hact, hoff, hfit, hbelow, h48, hm5, hbs, hvs, hi1, hop,
    hai, hfv, hro, hu1, hrd, hnp, hrun⟩ := hf
  refine ⟨hl, ?_, h64, hav, hvo, hfg, hact, hoff, hfit, hbelow, h48, hm5, ?_, ?_, hi1, hop, hai,
    ?_, hro, hu1, hrd, hnp, hrun⟩
  · revert hres; cases checkG65 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]
  · revert hfv
    split
    · rename_i h; intro _; exact h
    · intro h; cases h

/-! ## The activation -/

theorem ι65_temp : ι65 (.temp 0 3) = some (GenG2.sp0 + 16) := by simp [ι65]

theorem ι65_ne {b : Blk} (h : b ≠ .temp 0 3) : ι65 b = GenG2.ι b := by simp [ι65, h]

theorem ι65_glob (name : String) : ι65 (.global name) = some GenG2.symA := by
  rw [ι65_ne (by nofun)]
  rfl

theorem addrAgree65 : AddrAgree ι65 := by
  intro b n a hb ha hnt
  rw [ι65_ne (hnt 0 3)] at ha
  exact GenG2.addrAgree b n a hb ha hnt

theorem g65Env (hc : checkG65 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : accessedVars lc = [3]) (hvo : varOp g 3 = some (.AUTO, -8))
    (hfg : lc.ctx.tabs.forgeable 3 = false) (hact : lc.ctx.act = 0)
    (hoff : frameOff L .AUTO (-8) = 16) (hfit : slotsFit = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG65L_spec hl (checkG65_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree65
            glob := fun _ name _ _ => ι65_glob name.toStringLossy
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -, -⟩ :=
                checkG65L_spec hl (checkG65_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk nc off hs => by simp [E, hk, hs]
            extra := by show 0 ≤ (8 : Int); decide
            frame := by
              refine ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
                by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off hk => ?_⟩
              simp only [E] at hk
              split at hk
              · rename_i hmem
                obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
                have := List.all_eq_true.1 hfit k hmem
                simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
                exact this.2
              · cases hk }
          vars := by
            intro x hx o ho _
            rw [hav, List.mem_singleton] at hx
            subst hx
            rw [hvo] at ho
            cases ho
            rw [hact, hoff]
            show ι65 (.temp 0 3) = some (GenG2.sp0 + BitVec.ofInt 64 16)
            rw [ι65_temp]
            rfl }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx nc o ho _ hf
    rw [hav, List.mem_singleton] at hx
    subst hx
    rw [hfg] at hf
    cases hf

/-! ## The memory and the state -/

theorem cAl_size : cAl.data.size = 8 := by
  simp [cAl, roAlloc, leBytesU8]

theorem uAl_size : uAl.data.size = 8 := by
  simp [uAl]

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    (b = .global cName ∧ al = cAl) ∨ (b = .temp 0 3 ∧ al = uAl) := by
  simpa [mem1] using h

/-- `M1` holds `X` little-endian at `symA` and at `SP + 16`. -/
theorem m1_bytesA : ∀ i, i < 8 →
    M1 (GenG2.symA + BitVec.ofNat 64 i) = BitVec.ofNat 8 (X.toNat / 256 ^ i) := by
  decide

theorem m1_bytesU : ∀ i, i < 8 →
    M1 (GenG2.sp0 + 16 + BitVec.ofNat 64 i) = BitVec.ofNat 8 (X.toNat / 256 ^ i) := by
  decide

theorem uAl_get {i : Nat} (hi : i < uAl.data.size) :
    uAl.data[i] = .b (BitVec.ofNat 8 (X.toNat / 256 ^ i)) := by
  simp [uAl]

/-- `mem1` injected into `M1` by `ι65`: the constant's bytes at `symA`, `u`'s at `SP + 16`. -/
theorem memInj1 : MemInj ι65 mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨GenG2.symA, ι65_glob _, fun _ => by decide, ?_⟩
      rw [cAl_size]
      decide
    · refine ⟨GenG2.sp0 + 16, ι65_temp, fun _ => by decide, ?_⟩
      rw [uAl_size]
      decide
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases mem1_blocks h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · rw [ι65_glob] at ha
      rw [ι65_temp] at ha'
      cases ha; cases ha'
      rw [cAl_size, uAl_size]
      decide
    · rw [ι65_temp] at ha
      rw [ι65_glob] at ha'
      cases ha; cases ha'
      rw [cAl_size, uAl_size]
      decide
    · exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [ι65_glob] at ha
      cases ha
      have hi8 : i < 8 := cAl_size ▸ hi
      have hb : cAl.data[i]? = some (.b (BitVec.ofNat 8 (0x3ff028f5c28f5c29 / 256 ^ i))) :=
        roAlloc_byte hi8
      rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at hb
      change ByteRel ι65 cAl.data[i] _
      rw [hb]
      exact (m1_bytesA i hi8).symm
    · rw [ι65_temp] at ha
      cases ha
      change ByteRel ι65 (uAl.data[i]'hi) _
      rw [uAl_get hi]
      exact (m1_bytesU i (uAl_size ▸ hi)).symm

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 (hbelow : slotsBelow = true) (hfit : slotsFit = true) :
    SepFrom ι65 (StkAt E) mem1 := by
  intro b al a h ha y hy
  have hsp : E.sp.toNat = 0x7fff0000 := rfl
  have hsp0 : GenG2.sp0.toNat = 0x7fff0000 := rfl
  rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [ι65_glob] at ha
    cases ha
    have hA : GenG2.symA.toNat = 0x10000000000 := rfl
    rw [hA, cAl_size]
    rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -, h2⟩
    · rw [hsp] at h2; omega
    · simp only [E] at hk
      split at hk
      · rename_i hmem
        obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
        have h1 := List.all_eq_true.1 hbelow k hmem
        have h3 := List.all_eq_true.1 hfit k hmem
        simp only [hso, decide_eq_true_eq, Bool.and_eq_true] at h1 h3
        simp only [hsp, hsp0] at h2 h3
        omega
      · cases hk
  · rw [ι65_temp] at ha
    cases ha
    have hU : (GenG2.sp0 + 16).toNat = 0x7fff0010 := rfl
    rw [hU, uAl_size]
    rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -, h2⟩
    · rw [hsp] at h2; omega
    · simp only [E] at hk
      split at hk
      · rename_i hmem
        obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
        have h1 := List.all_eq_true.1 hbelow k hmem
        have h3 := List.all_eq_true.1 hfit k hmem
        simp only [hso, decide_eq_true_eq, Bool.and_eq_true] at h1 h3
        simp only [hsp, hsp0] at h2 h3
        omega
      · cases hk

/-- The constant symbol is in `mem1`, read-only: `RoPre56` at `s0`. -/
theorem ro0 (hro : constRo (symNames g) = [(cName, cAl)]) : RoPre56 g s0 := by
  intro mm hmm
  change Val.mem mem1 = Val.mem mm at hmm
  cases hmm
  rw [hro]
  intro n a h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, by simp [mem1, Mem.find?]⟩

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 5 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E]; decide,
    by simp only [MState.word, readMem, m0, M1, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g65Inv0 (hbelow : slotsBelow = true) (hfit : slotsFit = true) :
    G3Inv E lc (kAt lc kt 5 blk 1) s0 false where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1 hbelow hfit⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v21`: `FMOVDload {u} [0] v2 v36` (`FMOVD u-8(SP), F1`) -/

/-- `FLoadPre` on `v21`: it reads the 8 valid bytes of `u`, no pointer at its shape. -/
theorem preF (hop : (val 21).op = .ARM64FMOVDload) (hai : (val 21).auxInt.toInt = 0)
    (hact : lc.ctx.act = 0) (hfv : frameVar? lc g (val 21) = .ok (some (3, -8)))
    (hrd : (mem1.read pU 8).isSome = true)
    (hnp : notPtr ((Arm64.loadN (lc.ty (val 21).id) 8 false mem1 pU).retypeL
      (lc.ty (val 21).id)) = true) :
    FLoadPre lc s0 (val 21) := by
  intro _ a x _ _
  have hF := frameVar?_spec hfv
  have hsym : symAddr lc.ctx (val 21) x = some pU := by
    rw [symAddr_var hF.aux hF.var hF.temp, hact, hai]
    rfl
  have hb : fBytes (val 21).op = 8 := by rw [hop]; rfl
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrd
  refine ⟨pU, mem1, bs, hsym, rfl, ?_, ?_⟩
  · rw [hb]; exact hbs
  · rw [hb]; exact notPtr_spec hnp

/-- The per-value premises of G54 on `v21`, `FMOVDload`: `FLoadPre` (`preF`); no other applies. -/
theorem pre54 (hop : (val 21).op = .ARM64FMOVDload) (hF : FLoadPre lc s0 (val 21)) :
    G54Pre lc s0 (val 21) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDload → (val 21).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hF⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ _ hl; rw [hop] at hl; simp [fp2Of] at hl
  · intro _ _ _ _ hl; rw [hop] at hl; simp [fp3Of] at hl
  · intro _ _ _ _ hpo; rw [hop] at hpo; simp [pairOp50] at hpo
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- **G65 on `init.func82` of `test/gcgort`** (`v21 = FMOVDload {u} [0] v2 v36`, the float load
`FMOVD u-8(SP), F1` of the frame variable `u` in `t: func() { u := float64(1.01); for … { u *=
1.01; runtime.Gosched() } }`): `checkG64` rejects the function and `checkG65` accepts it. From a
state whose memory holds `u = 1.01` and the constant symbol, where `FLoadPre` holds (the 8 bytes of
`u` are valid and hold no pointer), `stepLoc` runs `v21` to `X` in `F1`, and `g65_value` (at the
mode `false`, the function needing no G48 mode) relates it to a machine run from `m0`, which holds
`u`'s bytes at `SP + 16` and every V register 0, to a state whose `V1` holds `X` in its low word,
under an activation extending `E` that is again a `G49Env`. -/
theorem genG65_witness :
    (checkG64 lc0 ps bs g).toOption = none ∧ (val 21).op = .ARM64FMOVDload ∧
      FLoadPre lc s0 (val 21) ∧ (m0.v 1).setWidth 64 = 0 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 21) = .ok s1 ∧
        s1.regs[32]? = some (.int .w64 X) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 5 2 m1 ∧ (m1.v 1).setWidth 64 = X := by
  obtain ⟨hl, hc, h64, hav, hvo, hfg, hact, hoff, hfit, hbelow, h48, hm5, hb, hv21, hi1, hop,
    hai, hfv, hro, hu1, hrd, hnp, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr32 := f1Is_spec hr
  have hE := g65Env hc hl hav hvo hfg hact hoff hfit
  have hF := preF hop hai hact hfv hrd hnp
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDload → (val 21).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g65_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 5 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm5
  have hb0 : lc0.ctx.f.block? 5 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 21 = some (val 21) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv21
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g65_value (H := GenG2.H0) (env := GenG2.env)
    (osp := false) hc hE hl0 hm0 hb0 hi1 hv0 (by rw [hop]; rfl) locMatch0 (g65Inv0 hbelow hfit)
    (fun h => by cases h) (fun h => by cases h)
    (fun h => by
      have h' : needs48 lc = true := h
      rw [h48] at h'
      cases h')
    (by change UOKL m0 (uL35 lc (uIn35 lc 5) blk 1); rw [hu1]; intro e he; cases he)
    (pre54 hop hF) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => by cases h) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide)))
    ⟨fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩ hs1
  have hV : (m1.v 1).setWidth 64 = X := (hm1'.regs 32 _ hr32).2 1 rfl
  exact ⟨h64, hop, hF, rfl, s1, E1, m1, hs1, hr32, hx1, hE1, hp1, hm1', hV⟩

end GoFV.Proof.Witness.GenG65
