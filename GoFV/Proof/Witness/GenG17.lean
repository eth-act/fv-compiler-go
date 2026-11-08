import GoFV.Proof.Gen.G17
import GoFV.Proof.Witness.GenG16

/-!
# Non-vacuity witness: slice G17 of the genssa validator on `runtime.getm`

`std/std/runtime/getm,1.ssa` and `…,1.prog` of the corpus `gofv-corpus/2aae1000ea1d/quick-v10/plain`,
embedded verbatim (`fSsa`, `fProg`): `getm` (`runtime/proc.go`),
`return uintptr(unsafe.Pointer(getg().m))`.

`checkG16` rejects it (`v6 = GetG`); `checkG17` accepts it with the PC table `tab` and the class
table `kt`. Block `b1`: `v1 = InitMem`, `v6 = GetG v1` (`g`), `v9 = MOVDload [48] v6 v1` (`R0`),
`v11 = Convert v9 v1`, `v12 = MakeResult v11 v1`; `Ret`. Its Progs: `MOVD 48(g), R0`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g17_facts`),
`stepLoc` runs `v6` and the `g` register then holds the pointer to the start of the global
`runtime.g`. On a framed activation with `G10Env` whose injection puts `runtime.g` at the
goroutine `gA` in `X28` (`GetGOK`), `g17_value` runs `v6` (no code) and gives the state before
`v9`, the `g` register related to `X28` (`genG17_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG17

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/getm,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "getm" 1 0 0
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
config localpkg "runtime"
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
type t2 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t1 FUNC 8 8 8 hasptr,direct "func() uintptr" "func() uintptr" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "runtime.getm" "runtime.getm" 1 - 0 - - - - 0
posbase p43 "runtime/proc.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p43:2733:13:0:0
aux a1 call "AuxCall{runtime.getm}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 INT 8 8 0 comparable,named "int" "int"
type t13 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t14 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t2
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t35 STRUCT 16 8 0 comparable,named "stack" "runtime.stack" 2
field 0 "lo" t2 0 0
field 1 "hi" t2 8 0
type t38 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t37 STRUCT 96 8 88 hasptr,comparable,named "_panic" "runtime._panic" 14
field 0 "arg" t38 0 0
field 1 "link" t36 16 0
field 2 "startPC" t2 24 0
field 3 "startSP" t27 32 0
field 4 "pc" t2 40 0
field 5 "sp" t27 48 0
field 6 "fp" t27 56 0
field 7 "retpc" t2 64 0
field 8 "deferBitsPtr" t17 72 0
field 9 "slotsPtr" t27 80 0
field 10 "recovered" t3 88 0
field 11 "repanicked" t3 89 0
field 12 "goexit" t3 90 0
field 13 "deferreturn" t3 91 0
type t36 PTR 8 8 8 hasptr,direct,comparable "*_panic" "*runtime._panic" t37
type t41 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
type t45 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t44 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.UnsafePointer" "internal/runtime/atomic.UnsafePointer" 2
field 0 "noCopy" t45 0 0
field 1 "value" t27 0 0
type t43 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime._defer]" "internal/runtime/atomic.Pointer[runtime._defer]" 1
field 0 "u" t44 0 0
type t42 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime._defer]" "*internal/runtime/atomic.Pointer[runtime._defer]" t43
type t40 STRUCT 48 8 48 hasptr,named "_defer" "runtime._defer" 7
field 0 "heap" t3 0 0
field 1 "rangefunc" t3 1 0
field 2 "sp" t2 8 0
field 3 "pc" t2 16 0
field 4 "fn" t41 24 0
field 5 "link" t39 32 0
field 6 "head" t42 40 0
type t39 PTR 8 8 8 hasptr,direct,comparable "*_defer" "*runtime._defer" t40
type t49 UINTPTR 8 8 0 comparable,named "guintptr" "runtime.guintptr"
type t48 STRUCT 48 8 32 hasptr,comparable,named "gobuf" "runtime.gobuf" 6
field 0 "sp" t2 0 0
field 1 "pc" t2 8 0
field 2 "g" t49 16 0
field 3 "ctxt" t27 24 0
field 4 "lr" t2 32 0
field 5 "bp" t2 40 0
type t50 STRUCT 40 8 0 comparable,named "gsignalStack" "runtime.gsignalStack" 4
field 0 "stack" t35 0 0
field 1 "stackguard0" t2 16 0
field 2 "stackguard1" t2 24 0
field 3 "stktopsp" t2 32 0
type t51 ARRAY 8 4 0 comparable,named "sigset" "runtime.sigset" t10 2
type t52 ARRAY 48 8 0 comparable "[6]uintptr" "[6]uintptr" t2 6
type t53 UINTPTR 8 8 0 comparable,named "puintptr" "runtime.puintptr"
type t54 UINT32 4 4 0 comparable,named "throwType" "runtime.throwType"
type t55 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t45 0 0
field 1 "value" t10 0 0
type t59 STRUCT 24 8 0 comparable,named "sysmontick" "runtime.sysmontick" 4
field 0 "schedtick" t10 0 0
field 1 "syscalltick" t10 4 0
field 2 "schedwhen" t7 8 0
field 3 "syscallwhen" t7 16 0
type t60 UINTPTR 8 8 0 comparable,named "muintptr" "runtime.muintptr"
type t64 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t63 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t64 0 0
type t69 STRUCT 16 8 0 notinheap,comparable,named "mSpanList" "runtime.mSpanList" 3
field 0 "_" t63 0 0
field 1 "first" t66 0 0
field 2 "last" t66 8 0
type t68 PTR 8 8 0 comparable "*mSpanList" "*runtime.mSpanList" t69
type t70 UINTPTR 8 8 0 comparable,named "gclinkptr" "runtime.gclinkptr"
type t72 STRUCT 1 1 0 notinheap,comparable,named "gcBits" "runtime.gcBits" 2
field 0 "_" t63 0 0
field 1 "x" t8 0 0
type t71 PTR 8 8 0 comparable "*gcBits" "*runtime.gcBits" t72
type t73 UINT8 1 1 0 comparable,named "spanClass" "runtime.spanClass"
type t75 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t45 0 0
field 1 "value" t8 0 0
type t74 STRUCT 1 1 0 comparable,named "mSpanStateBox" "runtime.mSpanStateBox" 1
field 0 "s" t75 0 0
type t77 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t76 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t77 0 1
field 1 "key" t2 0 0
type t80 UINT8 1 1 0 comparable,named "byte" "uint8"
type t79 STRUCT 24 8 0 notinheap,comparable,named "special" "runtime.special" 4
field 0 "_" t63 0 0
field 1 "next" t78 0 0
field 2 "offset" t2 8 0
field 3 "kind" t80 16 0
type t78 PTR 8 8 0 comparable "*special" "*runtime.special" t79
type t82 STRUCT 8 8 0 comparable,named "offAddr" "runtime.offAddr" 1
field 0 "a" t2 0 0
type t81 STRUCT 16 8 0 comparable,named "addrRange" "runtime.addrRange" 2
field 0 "base" t82 0 0
field 1 "limit" t82 8 0
type t85 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t86 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t87 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t27 ? 0
field 1 "" t27 ? 0
field 2 "" t3 ? 0
type t88 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t80
type t89 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t90 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t84 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t2 0 0
field 1 "PtrBytes" t2 8 0
field 2 "Hash" t10 16 0
field 3 "TFlag" t85 20 0
field 4 "Align_" t8 21 0
field 5 "FieldAlign_" t8 22 0
field 6 "Kind_" t86 23 0
field 7 "Equal" t87 24 0
field 8 "GCData" t88 32 0
field 9 "Str" t89 40 0
field 10 "PtrToThis" t90 44 0
type t83 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t84
type t67 STRUCT 160 8 160 hasptr,notinheap,comparable,named "mspan" "runtime.mspan" 28
field 0 "_" t63 0 0
field 1 "next" t66 0 0
field 2 "prev" t66 8 0
field 3 "list" t68 16 0
field 4 "startAddr" t2 24 0
field 5 "npages" t2 32 0
field 6 "manualFreeList" t70 40 0
field 7 "freeindex" t9 48 0
field 8 "nelems" t9 50 0
field 9 "freeIndexForScan" t9 52 0
field 10 "allocCache" t11 56 0
field 11 "allocBits" t71 64 0
field 12 "gcmarkBits" t71 72 0
field 13 "pinnerBits" t71 80 0
field 14 "sweepgen" t10 88 0
field 15 "divMul" t10 92 0
field 16 "allocCount" t9 96 0
field 17 "spanclass" t73 98 0
field 18 "state" t74 99 0
field 19 "needzero" t8 100 0
field 20 "isUserArenaChunk" t3 101 0
field 21 "allocCountBeforeCache" t9 102 0
field 22 "elemsize" t2 104 0
field 23 "limit" t2 112 0
field 24 "speciallock" t76 120 0
field 25 "specials" t78 128 0
field 26 "userArenaChunkFree" t81 136 0
field 27 "largeType" t83 152 0
type t66 PTR 8 8 0 comparable "*mspan" "*runtime.mspan" t67
type t65 ARRAY 1088 8 0 comparable "[136]*mspan" "[136]*runtime.mspan" t66 136
type t91 ARRAY 1088 8 0 comparable "[136]gclinkptr" "[136]runtime.gclinkptr" t70 136
type t93 STRUCT 16 8 0 comparable,named "stackfreelist" "runtime.stackfreelist" 2
field 0 "list" t70 0 0
field 1 "size" t2 8 0
type t92 ARRAY 64 8 0 comparable "[4]stackfreelist" "[4]runtime.stackfreelist" t93 4
type t62 STRUCT 2296 8 0 notinheap,comparable,named "mcache" "runtime.mcache" 11
field 0 "_" t63 0 0
field 1 "nextSample" t7 0 0
field 2 "memProfRate" t12 8 0
field 3 "scanAlloc" t2 16 0
field 4 "tiny" t2 24 0
field 5 "tinyoffset" t2 32 0
field 6 "tinyAllocs" t2 40 0
field 7 "alloc" t65 48 0
field 8 "reusableNoscan" t91 1136 0
field 9 "stackcache" t92 2224 0
field 10 "flushGen" t55 2288 0
type t61 PTR 8 8 0 comparable "*mcache" "*runtime.mcache" t62
type t94 STRUCT 24 8 0 comparable,named "pageCache" "runtime.pageCache" 3
field 0 "base" t2 0 0
field 1 "cache" t11 8 0
field 2 "scav" t11 16 0
type t97 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime.m]" "internal/runtime/atomic.Pointer[runtime.m]" 1
field 0 "u" t44 0 0
type t96 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime.m]" "*internal/runtime/atomic.Pointer[runtime.m]" t97
type t95 STRUCT 8 8 8 hasptr,direct,comparable,named "mWeakPointer" "runtime.mWeakPointer" 1
field 0 "m" t96 0 0
type t98 SLICE 24 8 8 hasptr "[]*_defer" "[]*runtime._defer" t39
type t99 ARRAY 256 8 256 hasptr,comparable "[32]*_defer" "[32]*runtime._defer" t39 32
type t100 ARRAY 2048 8 0 comparable "[256]guintptr" "[256]runtime.guintptr" t49 256
type t101 STRUCT 16 8 0 comparable,named "gList" "runtime.gList" 2
field 0 "head" t49 0 0
field 1 "size" t6 8 0
type t105 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceablePtr" "runtime.maybeTraceablePtr" 2
field 0 "vp" t27 0 0
field 1 "vu" t2 8 0
type t106 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceableChan" "runtime.maybeTraceableChan" 1
field 0 "maybeTraceablePtr" t105 0 1
type t104 STRUCT 104 8 96 hasptr,comparable,named "sudog" "runtime.sudog" 14
field 0 "g" t33 0 0
field 1 "next" t103 8 0
field 2 "prev" t103 16 0
field 3 "elem" t105 24 0
field 4 "acquiretime" t7 40 0
field 5 "releasetime" t7 48 0
field 6 "ticket" t10 56 0
field 7 "isSelect" t3 60 0
field 8 "success" t3 61 0
field 9 "waiters" t9 62 0
field 10 "parent" t103 64 0
field 11 "waitlink" t103 72 0
field 12 "waittail" t103 80 0
field 13 "c" t106 88 0
type t103 PTR 8 8 8 hasptr,direct,comparable "*sudog" "*runtime.sudog" t104
type t102 SLICE 24 8 8 hasptr "[]*sudog" "[]*runtime.sudog" t103
type t107 ARRAY 1024 8 1024 hasptr,comparable "[128]*sudog" "[128]*runtime.sudog" t103 128
type t109 ARRAY 1024 8 0 comparable "[128]*mspan" "[128]*runtime.mspan" t66 128
type t108 STRUCT 1032 8 0 comparable "struct { len int; buf [128]*mspan }" "struct { runtime.len int; runtime.buf [128]*runtime.mspan }" 2
field 0 "len" t12 0 0
field 1 "buf" t109 8 0
type t112 SLICE 24 8 8 hasptr "[]unsafe.Pointer" "[]unsafe.Pointer" t27
type t113 ARRAY 40 8 40 hasptr,comparable "[5]unsafe.Pointer" "[5]unsafe.Pointer" t27 5
type t111 STRUCT 64 8 64 hasptr,named "pinner" "runtime.pinner" 2
field 0 "refs" t112 0 0
field 1 "refStore" t113 24 0
type t110 PTR 8 8 8 hasptr,direct,comparable "*pinner" "*runtime.pinner" t111
type t116 ARRAY 12 4 0 comparable "[3]atomic.Uint32" "[3]internal/runtime/atomic.Uint32" t55 3
type t117 ARRAY 16 8 0 comparable "[2]uint64" "[2]uint64" t11 2
type t115 STRUCT 32 8 0 comparable,named "traceSchedResourceState" "runtime.traceSchedResourceState" 2
field 0 "statusTraced" t116 0 0
field 1 "seq" t117 16 0
type t114 STRUCT 64 8 0 comparable,named "pTraceState" "runtime.pTraceState" 6
field 0 "traceSchedResourceState" t115 0 1
field 1 "mSyscallID" t7 32 0
field 2 "maySweep" t3 40 0
field 3 "inSweep" t3 41 0
field 4 "swept" t2 48 0
field 5 "reclaimed" t2 56 0
type t120 STRUCT 0 1 0 notinheap,comparable,named "notInHeap" "runtime.notInHeap" 1
field 0 "_" t63 0 0
type t119 PTR 8 8 0 comparable "*notInHeap" "*runtime.notInHeap" t120
type t118 STRUCT 16 8 0 comparable,named "persistentAlloc" "runtime.persistentAlloc" 2
field 0 "base" t119 0 0
field 1 "off" t2 8 0
type t122 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t121 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t45 0 0
field 1 "_" t122 0 0
field 2 "value" t7 0 0
type t124 STRUCT 8 8 0 comparable,named "atomic.Uint64" "internal/runtime/atomic.Uint64" 3
field 0 "noCopy" t45 0 0
field 1 "_" t122 0 0
field 2 "value" t11 0 0
type t123 STRUCT 8 8 0 comparable,named "limiterEvent" "runtime.limiterEvent" 1
field 0 "stamp" t124 0 0
type t125 INT 8 8 0 comparable,named "gcMarkWorkerMode" "runtime.gcMarkWorkerMode"
type t128 STRUCT 16 8 0 comparable,named "lfnode" "runtime.lfnode" 2
field 0 "next" t11 0 0
field 1 "pushcnt" t2 8 0
type t127 STRUCT 32 8 0 comparable,named "gcBgMarkWorkerNode" "runtime.gcBgMarkWorkerNode" 3
field 0 "node" t128 0 0
field 1 "gp" t49 16 0
field 2 "m" t60 24 0
type t126 PTR 8 8 8 hasptr,direct,comparable "*gcBgMarkWorkerNode" "*runtime.gcBgMarkWorkerNode" t127
type t132 STRUCT 24 8 0 comparable,named "workbufhdr" "runtime.workbufhdr" 2
field 0 "node" t128 0 0
field 1 "nobj" t12 16 0
type t133 ARRAY 2024 8 0 comparable "[253]uintptr" "[253]uintptr" t2 253
type t131 STRUCT 2048 8 0 notinheap,comparable,named "workbuf" "runtime.workbuf" 3
field 0 "_" t63 0 0
field 1 "workbufhdr" t132 0 1
field 2 "obj" t133 24 0
type t130 PTR 8 8 0 comparable "*workbuf" "*runtime.workbuf" t131
type t136 UINTPTR 8 8 0 comparable,named "objptr" "runtime.objptr"
type t135 ARRAY 2048 8 0 comparable "[256]objptr" "[256]runtime.objptr" t136 256
type t140 STRUCT 16 8 0 comparable,named "listNodeManual" "runtime.listNodeManual" 2
field 0 "prev" t2 0 0
field 1 "next" t2 8 0
type t141 STRUCT 1 1 0 comparable,named "atomic.Bool" "internal/runtime/atomic.Bool" 1
field 0 "u" t75 0 0
type t142 PTR 8 8 8 hasptr,direct,comparable "*objptr" "*runtime.objptr" t136
type t139 STRUCT 56 8 56 hasptr,notinheap,comparable,named "spanSPMC" "runtime.spanSPMC" 8
field 0 "_" t63 0 0
field 1 "allnode" t140 0 0
field 2 "dead" t141 16 0
field 3 "prev" t44 24 0
field 4 "head" t55 32 0
field 5 "tail" t55 36 0
field 6 "cap" t10 40 0
field 7 "ring" t142 48 0
type t138 PTR 8 8 0 comparable "*spanSPMC" "*runtime.spanSPMC" t139
type t137 STRUCT 16 8 16 hasptr,comparable "struct { head *spanSPMC; tail atomic.UnsafePointer }" "struct { runtime.head *runtime.spanSPMC; runtime.tail internal/runtime/atomic.UnsafePointer }" 2
field 0 "head" t138 0 0
field 1 "tail" t44 8 0
type t134 STRUCT 2080 8 2080 hasptr,comparable,named "spanQueue" "runtime.spanQueue" 5
field 0 "head" t10 0 0
field 1 "tail" t10 4 0
field 2 "ring" t135 8 0
field 3 "putsSinceDrain" t12 2056 0
field 4 "chain" t137 2064 0
type t144 ARRAY 8192 8 0 comparable "[1024]uintptr" "[1024]uintptr" t2 1024
type t143 PTR 8 8 8 hasptr,direct,comparable "*[1024]uintptr" "*[1024]uintptr" t144
type t146 STRUCT 40 8 0 comparable,named "sizeClassScanStats" "runtime.sizeClassScanStats" 5
field 0 "spansDenseScanned" t11 0 0
field 1 "spanObjsDenseScanned" t11 8 0
field 2 "spansSparseScanned" t11 16 0
field 3 "spanObjsSparseScanned" t11 24 0
field 4 "sparseObjsScanned" t11 32 0
type t145 ARRAY 2720 8 0 comparable "[68]sizeClassScanStats" "[68]runtime.sizeClassScanStats" t146 68
type t129 STRUCT 4856 8 2112 hasptr,comparable,named "gcWork" "runtime.gcWork" 10
field 0 "id" t6 0 0
field 1 "wbuf1" t130 8 0
field 2 "wbuf2" t130 16 0
field 3 "spanq" t134 24 0
field 4 "ptrBuf" t143 2104 0
field 5 "bytesMarked" t11 2112 0
field 6 "heapScanWork" t7 2120 0
field 7 "flushedWork" t3 2128 0
field 8 "mayNeedWorker" t3 2129 0
field 9 "stats" t145 2136 0
type t148 ARRAY 4096 8 0 comparable "[512]uintptr" "[512]uintptr" t2 512
type t147 STRUCT 4112 8 0 comparable,named "wbBuf" "runtime.wbBuf" 3
field 0 "next" t2 0 0
field 1 "end" t2 8 0
field 2 "buf" t148 16 0
type t154 FUNC 8 8 8 hasptr,direct "func(any, uintptr, int64)" "func(interface {}, uintptr, int64)" 0 3 0
field 0 "arg" t38 ? 0
field 1 "seq" t2 ? 0
field 2 "delay" t7 ? 0
type t155 PTR 8 8 8 hasptr,direct,comparable "*timers" "*runtime.timers" t149
type t156 STRUCT 4 4 0 comparable,named "atomic.Int32" "internal/runtime/atomic.Int32" 2
field 0 "noCopy" t45 0 0
field 1 "value" t6 0 0
type t153 STRUCT 96 8 80 hasptr,named "timer" "runtime.timer" 15
field 0 "mu" t76 0 0
field 1 "astate" t75 8 0
field 2 "state" t8 9 0
field 3 "isChan" t3 10 0
field 4 "isFake" t3 11 0
field 5 "blocked" t10 12 0
field 6 "rand" t10 16 0
field 7 "when" t7 24 0
field 8 "period" t7 32 0
field 9 "f" t154 40 0
field 10 "arg" t38 48 0
field 11 "seq" t2 64 0
field 12 "ts" t155 72 0
field 13 "sendLock" t76 80 0
field 14 "isSending" t156 88 0
type t152 PTR 8 8 8 hasptr,direct,comparable "*timer" "*runtime.timer" t153
type t151 STRUCT 16 8 8 hasptr,comparable,named "timerWhen" "runtime.timerWhen" 2
field 0 "timer" t152 0 0
field 1 "when" t7 8 0
type t150 SLICE 24 8 8 hasptr "[]timerWhen" "[]runtime.timerWhen" t151
type t149 STRUCT 64 8 16 hasptr,named "timers" "runtime.timers" 7
field 0 "mu" t76 0 0
field 1 "heap" t150 8 0
field 2 "len" t55 32 0
field 3 "zombies" t156 36 0
field 4 "raceCtx" t2 40 0
field 5 "minWhenHeap" t121 48 0
field 6 "minWhenModified" t121 56 0
type t159 STRUCT 32 8 0 notinheap,comparable,named "cleanupBlockHeader" "runtime.cleanupBlockHeader" 4
field 0 "_" t63 0 0
field 1 "lfnode" t128 0 1
field 2 "alllink" t157 16 0
field 3 "n" t10 24 0
type t164 STRUCT 8 8 0 comparable,named "funcval" "runtime.funcval" 1
field 0 "fn" t2 0 0
type t163 PTR 8 8 8 hasptr,direct,comparable "*funcval" "*runtime.funcval" t164
type t162 FUNC 8 8 8 hasptr,direct "func(*funcval, unsafe.Pointer)" "func(*runtime.funcval, unsafe.Pointer)" 0 2 0
field 0 "" t163 ? 0
field 1 "" t27 ? 0
type t161 STRUCT 24 8 24 hasptr,named "cleanupFn" "runtime.cleanupFn" 3
field 0 "call" t162 0 0
field 1 "fn" t163 8 0
field 2 "arg" t27 16 0
type t160 ARRAY 480 8 480 hasptr "[20]cleanupFn" "[20]runtime.cleanupFn" t161 20
type t158 STRUCT 512 8 512 hasptr,notinheap,named "cleanupBlock" "runtime.cleanupBlock" 2
field 0 "cleanupBlockHeader" t159 0 1
field 1 "cleanups" t160 32 0
type t157 PTR 8 8 0 comparable "*cleanupBlock" "*runtime.cleanupBlock" t158
type t167 ARRAY 16 1 0 comparable "[16]byte" "[16]uint8" t80 16
type t166 STRUCT 512 1 0 comparable,named "xRegs" "runtime.xRegs" 32
field 0 "V0" t167 0 0
field 1 "V1" t167 16 0
field 2 "V2" t167 32 0
field 3 "V3" t167 48 0
field 4 "V4" t167 64 0
field 5 "V5" t167 80 0
field 6 "V6" t167 96 0
field 7 "V7" t167 112 0
field 8 "V8" t167 128 0
field 9 "V9" t167 144 0
field 10 "V10" t167 160 0
field 11 "V11" t167 176 0
field 12 "V12" t167 192 0
field 13 "V13" t167 208 0
field 14 "V14" t167 224 0
field 15 "V15" t167 240 0
field 16 "V16" t167 256 0
field 17 "V17" t167 272 0
field 18 "V18" t167 288 0
field 19 "V19" t167 304 0
field 20 "V20" t167 320 0
field 21 "V21" t167 336 0
field 22 "V22" t167 352 0
field 23 "V23" t167 368 0
field 24 "V24" t167 384 0
field 25 "V25" t167 400 0
field 26 "V26" t167 416 0
field 27 "V27" t167 432 0
field 28 "V28" t167 448 0
field 29 "V29" t167 464 0
field 30 "V30" t167 480 0
field 31 "V31" t167 496 0
type t169 STRUCT 512 1 0 notinheap,comparable,named "xRegState" "runtime.xRegState" 2
field 0 "_" t63 0 0
field 1 "regs" t166 0 0
type t168 PTR 8 8 0 comparable "*xRegState" "*runtime.xRegState" t169
type t165 STRUCT 520 8 0 comparable,named "xRegPerP" "runtime.xRegPerP" 2
field 0 "scratch" t166 0 0
field 1 "cache" t168 512 0
type t58 STRUCT 14320 8 13688 hasptr,named "p" "runtime.p" 46
field 0 "id" t6 0 0
field 1 "status" t10 4 0
field 2 "link" t53 8 0
field 3 "schedtick" t10 16 0
field 4 "syscalltick" t10 20 0
field 5 "sysmontick" t59 24 0
field 6 "m" t60 48 0
field 7 "mcache" t61 56 0
field 8 "pcache" t94 64 0
field 9 "raceprocctx" t2 88 0
field 10 "oldm" t95 96 0
field 11 "deferpool" t98 104 0
field 12 "deferpoolbuf" t99 128 0
field 13 "goidcache" t11 384 0
field 14 "goidcacheend" t11 392 0
field 15 "runqhead" t10 400 0
field 16 "runqtail" t10 404 0
field 17 "runq" t100 408 0
field 18 "runnext" t49 2456 0
field 19 "gFree" t101 2464 0
field 20 "sudogcache" t102 2480 0
field 21 "sudogbuf" t107 2504 0
field 22 "mspancache" t108 3528 0
field 23 "pinnerCache" t110 4560 0
field 24 "trace" t114 4568 0
field 25 "palloc" t118 4632 0
field 26 "gcAssistTime" t7 4648 0
field 27 "gcFractionalMarkTime" t121 4656 0
field 28 "limiterEvent" t123 4664 0
field 29 "gcMarkWorkerMode" t125 4672 0
field 30 "gcMarkWorkerStartTime" t7 4680 0
field 31 "nextGCMarkWorker" t126 4688 0
field 32 "gcw" t129 4696 0
field 33 "wbBuf" t147 9552 0
field 34 "runSafePointFn" t10 13664 0
field 35 "statsSeq" t55 13668 0
field 36 "timers" t149 13672 0
field 37 "cleanups" t157 13736 0
field 38 "cleanupsQueued" t11 13744 0
field 39 "maxStackScanDelta" t7 13752 0
field 40 "scannedStackSize" t11 13760 0
field 41 "scannedStacks" t11 13768 0
field 42 "preempt" t3 13776 0
field 43 "gcStopTime" t7 13784 0
field 44 "goroutinesCreated" t11 13792 0
field 45 "xRegs" t165 13800 0
type t57 PTR 8 8 8 hasptr,direct,comparable "*p" "*runtime.p" t58
type t56 SLICE 24 8 8 hasptr "[]*p" "[]*runtime.p" t57
type t171 ARRAY 256 8 0 comparable,named "cgoCallers" "runtime.cgoCallers" t2 32
type t170 PTR 8 8 8 hasptr,direct,comparable "*cgoCallers" "*runtime.cgoCallers" t171
type t172 STRUCT 8 8 0 comparable,named "note" "runtime.note" 1
field 0 "key" t2 0 0
type t173 ARRAY 256 8 0 comparable "[32]uintptr" "[32]uintptr" t2 32
type t174 STRUCT 16 8 0 comparable,named "mWaitList" "runtime.mWaitList" 2
field 0 "next" t60 0 0
field 1 "startTicks" t7 8 0
type t176 SLICE 24 8 8 hasptr "[]uintptr" "[]uintptr" t2
type t175 STRUCT 56 8 16 hasptr,named "mLockProfile" "runtime.mLockProfile" 6
field 0 "waitTime" t121 0 0
field 1 "stack" t176 8 0
field 2 "cycles" t7 32 0
field 3 "cyclesLost" t7 40 0
field 4 "haveStack" t3 48 0
field 5 "disabled" t3 49 0
type t177 FUNC 8 8 8 hasptr,direct "func(*g, unsafe.Pointer) bool" "func(*runtime.g, unsafe.Pointer) bool" 0 2 1
field 0 "" t33 ? 0
field 1 "" t27 ? 0
field 2 "" t3 ? 0
type t178 UINT8 1 1 0 comparable,named "traceBlockReason" "runtime.traceBlockReason"
type t185 UINT64 8 8 0 comparable,named "traceTime" "runtime.traceTime"
type t184 STRUCT 32 8 0 comparable,named "traceBufHeader" "runtime.traceBufHeader" 4
field 0 "link" t182 0 0
field 1 "lastTime" t185 8 0
field 2 "pos" t12 16 0
field 3 "lenPos" t12 24 0
type t186 ARRAY 65504 1 0 comparable "[65504]byte" "[65504]uint8" t80 65504
type t183 STRUCT 65536 8 0 notinheap,comparable,named "traceBuf" "runtime.traceBuf" 3
field 0 "_" t63 0 0
field 1 "traceBufHeader" t184 0 1
field 2 "arr" t186 32 0
type t182 PTR 8 8 0 comparable "*traceBuf" "*runtime.traceBuf" t183
type t181 ARRAY 16 8 0 comparable "[2]*traceBuf" "[2]*runtime.traceBuf" t182 2
type t180 ARRAY 32 8 0 comparable "[2][2]*traceBuf" "[2][2]*runtime.traceBuf" t181 2
type t179 STRUCT 72 8 48 hasptr,comparable,named "mTraceState" "runtime.mTraceState" 6
field 0 "writing" t141 0 0
field 1 "buf" t180 8 0
field 2 "link" t46 40 0
field 3 "reentered" t10 48 0
field 4 "entryGen" t2 56 0
field 5 "oldthrowsplit" t3 64 0
type t187 STRUCT 0 1 0 comparable,named "winlibcall" "runtime.winlibcall" 0
type t191 STRUCT 24 8 0 comparable,named "pcvalueCacheEnt" "runtime.pcvalueCacheEnt" 4
field 0 "targetpc" t2 0 0
field 1 "off" t10 8 0
field 2 "val" t6 12 0
field 3 "valPC" t2 16 0
type t190 ARRAY 192 8 0 comparable "[8]pcvalueCacheEnt" "[8]runtime.pcvalueCacheEnt" t191 8
type t189 ARRAY 384 8 0 comparable "[2][8]pcvalueCacheEnt" "[2][8]runtime.pcvalueCacheEnt" t190 2
type t188 STRUCT 392 8 0 comparable,named "pcvalueCache" "runtime.pcvalueCache" 2
field 0 "entries" t189 0 0
field 1 "inUse" t12 384 0
type t192 STRUCT 0 1 0 comparable,named "dlogPerM" "runtime.dlogPerM" 0
type t193 STRUCT 24 8 0 comparable,named "mOS" "runtime.mOS" 5
field 0 "profileTimer" t6 0 0
field 1 "profileTimerValid" t141 4 0
field 2 "needPerThreadSyscall" t75 5 0
field 3 "vgetrandomState" t2 8 0
field 4 "waitsema" t10 16 0
type t195 ARRAY 256 8 0 comparable "[32]uint64" "[32]uint64" t11 32
type t196 ARRAY 32 8 0 comparable "[4]uint64" "[4]uint64" t11 4
type t194 STRUCT 304 8 0 comparable,named "chacha8rand.State" "internal/chacha8rand.State" 5
field 0 "buf" t195 0 0
field 1 "seed" t196 256 0
field 2 "i" t10 288 0
field 3 "n" t10 292 0
field 4 "c" t10 296 0
type t199 INT64 8 8 0 comparable,named "lockRank" "runtime.lockRank"
type t198 STRUCT 16 8 0 comparable,named "heldLockInfo" "runtime.heldLockInfo" 2
field 0 "lockAddr" t2 0 0
field 1 "rank" t199 8 0
type t197 ARRAY 160 8 0 comparable "[10]heldLockInfo" "[10]runtime.heldLockInfo" t198 10
type t47 STRUCT 1832 8 1832 hasptr,named "m" "runtime.m" 75
field 0 "g0" t33 0 0
field 1 "morebuf" t48 8 0
field 2 "divmod" t10 56 0
field 3 "procid" t11 64 0
field 4 "gsignal" t33 72 0
field 5 "goSigStack" t50 80 0
field 6 "sigmask" t51 120 0
field 7 "tls" t52 128 0
field 8 "mstartfn" t41 176 0
field 9 "curg" t33 184 0
field 10 "caughtsig" t49 192 0
field 11 "signalSecret" t3 200 0
field 12 "p" t53 208 0
field 13 "nextp" t53 216 0
field 14 "oldp" t53 224 0
field 15 "id" t7 232 0
field 16 "mallocing" t6 240 0
field 17 "throwing" t54 244 0
field 18 "preemptoff" t16 248 0
field 19 "locks" t6 264 0
field 20 "dying" t6 268 0
field 21 "profilehz" t6 272 0
field 22 "spinning" t3 276 0
field 23 "blocked" t3 277 0
field 24 "newSigstack" t3 278 0
field 25 "printlock" t4 279 0
field 26 "incgo" t3 280 0
field 27 "isextra" t3 281 0
field 28 "isExtraInC" t3 282 0
field 29 "isExtraInSig" t3 283 0
field 30 "freeWait" t55 284 0
field 31 "needextram" t3 288 0
field 32 "g0StackAccurate" t3 289 0
field 33 "traceback" t8 290 0
field 34 "allpSnapshot" t56 296 0
field 35 "ncgocall" t11 320 0
field 36 "ncgo" t6 328 0
field 37 "cgoCallersUse" t55 332 0
field 38 "cgoCallers" t170 336 0
field 39 "park" t172 344 0
field 40 "alllink" t46 352 0
field 41 "schedlink" t60 360 0
field 42 "idleNode" t140 368 0
field 43 "lockedg" t49 384 0
field 44 "createstack" t173 392 0
field 45 "lockedExt" t10 648 0
field 46 "lockedInt" t10 652 0
field 47 "mWaitList" t174 656 0
field 48 "ditEnabled" t3 672 0
field 49 "mLockProfile" t175 680 0
field 50 "profStack" t176 736 0
field 51 "waitunlockf" t177 760 0
field 52 "waitlock" t27 768 0
field 53 "waitTraceSkip" t12 776 0
field 54 "waitTraceBlockReason" t178 784 0
field 55 "syscalltick" t10 788 0
field 56 "freelink" t46 792 0
field 57 "trace" t179 800 0
field 58 "libcallpc" t2 872 0
field 59 "libcallsp" t2 880 0
field 60 "libcallg" t49 888 0
field 61 "winsyscall" t187 896 0
field 62 "vdsoSP" t2 896 0
field 63 "vdsoPC" t2 904 0
field 64 "preemptGen" t55 912 0
field 65 "signalPending" t55 916 0
field 66 "pcvalueCache" t188 920 0
field 67 "dlogPerM" t192 1312 1
field 68 "mOS" t193 1312 1
field 69 "chacha8" t194 1336 0
field 70 "cheaprand" t10 1640 0
field 71 "cheaprand64" t11 1648 0
field 72 "locksHeldLen" t12 1656 0
field 73 "locksHeld" t197 1664 0
field 74 "self" t95 1824 0
type t46 PTR 8 8 8 hasptr,direct,comparable "*m" "*runtime.m" t47
type t200 UINT8 1 1 0 comparable,named "waitReason" "runtime.waitReason"
type t201 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t80
type t204 STRUCT 40 8 8 hasptr,named "ancestorInfo" "runtime.ancestorInfo" 3
field 0 "pcs" t176 0 0
field 1 "goid" t11 24 0
field 2 "gopc" t2 32 0
type t203 SLICE 24 8 8 hasptr "[]ancestorInfo" "[]runtime.ancestorInfo" t204
type t202 PTR 8 8 8 hasptr,direct,comparable "*[]ancestorInfo" "*[]runtime.ancestorInfo" t203
type t205 STRUCT 4 4 0 comparable,named "goroutineProfileStateHolder" "runtime.goroutineProfileStateHolder" 2
field 0 "noCopy" t45 0 0
field 1 "value" t10 0 0
type t208 FUNC 8 8 8 hasptr,direct "func(*coro)" "func(*runtime.coro)" 0 1 0
field 0 "" t206 ? 0
type t207 STRUCT 32 8 24 hasptr,named "coro" "runtime.coro" 5
field 0 "gp" t49 0 0
field 1 "f" t208 8 0
field 2 "mp" t46 16 0
field 3 "lockedExt" t10 24 0
field 4 "lockedInt" t10 28 0
type t206 PTR 8 8 8 hasptr,direct,comparable "*coro" "*runtime.coro" t207
type t210 STRUCT 144 8 112 hasptr,named "synctestBubble" "runtime.synctestBubble" 12
field 0 "mu" t76 0 0
field 1 "timers" t149 8 0
field 2 "id" t11 72 0
field 3 "now" t7 80 0
field 4 "root" t33 88 0
field 5 "waiter" t33 96 0
field 6 "main" t33 104 0
field 7 "waiting" t3 112 0
field 8 "done" t3 113 0
field 9 "total" t12 120 0
field 10 "running" t12 128 0
field 11 "active" t12 136 0
type t209 PTR 8 8 8 hasptr,direct,comparable "*synctestBubble" "*runtime.synctestBubble" t210
type t211 STRUCT 8 8 0 comparable,named "xRegPerG" "runtime.xRegPerG" 1
field 0 "state" t168 0 0
type t212 STRUCT 32 8 0 comparable,named "gTraceState" "runtime.gTraceState" 1
field 0 "traceSchedResourceState" t115 0 1
type t34 STRUCT 456 8 400 hasptr,named "g" "runtime.g" 65
field 0 "stack" t35 0 0
field 1 "stackguard0" t2 16 0
field 2 "stackguard1" t2 24 0
field 3 "_panic" t36 32 0
field 4 "_defer" t39 40 0
field 5 "m" t46 48 0
field 6 "sched" t48 56 0
field 7 "syscallsp" t2 104 0
field 8 "syscallpc" t2 112 0
field 9 "syscallbp" t2 120 0
field 10 "stktopsp" t2 128 0
field 11 "param" t27 136 0
field 12 "atomicstatus" t55 144 0
field 13 "stackLock" t10 148 0
field 14 "goid" t11 152 0
field 15 "schedlink" t49 160 0
field 16 "waitsince" t7 168 0
field 17 "waitreason" t200 176 0
field 18 "preempt" t3 177 0
field 19 "preemptStop" t3 178 0
field 20 "preemptShrink" t3 179 0
field 21 "asyncSafePoint" t3 180 0
field 22 "paniconfault" t3 181 0
field 23 "gcscandone" t3 182 0
field 24 "throwsplit" t3 183 0
field 25 "activeStackChans" t3 184 0
field 26 "parkingOnChan" t141 185 0
field 27 "inMarkAssist" t3 186 0
field 28 "coroexit" t3 187 0
field 29 "raceignore" t4 188 0
field 30 "nocgocallback" t3 189 0
field 31 "tracking" t3 190 0
field 32 "trackingSeq" t8 191 0
field 33 "trackingStamp" t7 192 0
field 34 "runnableTime" t7 200 0
field 35 "lockedm" t60 208 0
field 36 "fipsIndicator" t8 216 0
field 37 "fipsOnlyBypass" t3 217 0
field 38 "ditWanted" t3 218 0
field 39 "syncSafePoint" t3 219 0
field 40 "runningCleanups" t141 220 0
field 41 "sig" t10 224 0
field 42 "secret" t6 228 0
field 43 "writebuf" t201 232 0
field 44 "sigcode0" t2 256 0
field 45 "sigcode1" t2 264 0
field 46 "sigpc" t2 272 0
field 47 "parentGoid" t11 280 0
field 48 "gopc" t2 288 0
field 49 "ancestors" t202 296 0
field 50 "startpc" t2 304 0
field 51 "racectx" t2 312 0
field 52 "waiting" t103 320 0
field 53 "cgoCtxt" t176 328 0
field 54 "labels" t27 352 0
field 55 "timer" t152 360 0
field 56 "sleepWhen" t7 368 0
field 57 "selectDone" t55 376 0
field 58 "goroutineProfiled" t205 380 0
field 59 "coroarg" t206 384 0
field 60 "bubble" t209 392 0
field 61 "xRegs" t211 400 0
field 62 "trace" t212 408 0
field 63 "gcAssistBytes" t7 440 0
field 64 "valgrindStackID" t2 448 0
type t33 PTR 8 8 8 hasptr,direct,comparable "*g" "*runtime.g" t34
type t213 PTR 8 8 8 hasptr,direct,comparable "**m" "**runtime.m" t46
type t214 RESULTS ? ? ? - "uintptr,mem" "" 2 t2,t28
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t2,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t2 0 - p0:0:0:0:0 1 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 GetG t33 0 - p43:2734:36:0:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v10 Copy t27 0 - p43:2734:38:2:0 1 v9
v v11 Convert t2 0 - p43:2734:31:0:0 1 v10,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t2 0 - p0:0:0:0:0 1 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v10 Copy t27 0 - p43:2734:38:2:0 1 v9
v v11 Convert t2 0 - p43:2734:31:0:0 1 v10,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t2 0 - p0:0:0:0:0 1 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 2 v8,v1
v v10 Copy t27 0 - p43:2734:38:2:0 0 v9
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts 0=v5
freev -
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v7 NilCheck t33 0 - p43:2734:38:0:0 1 v6,v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v7
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 43:2734:2734
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v7,v10,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 20 "expand calls"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
v v7 SB t2 0 - p0:0:0:0:0 0 -
v v10 SP t2 0 - p0:0:0:0:0 1 -
v v5 LocalAddr t21 0 a3 p43:2734:2:0:0 0 v10,v1
names -
splits -
canon -
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
v v7 SB t2 0 - p0:0:0:0:0 0 -
v v10 SP t2 0 - p0:0:0:0:0 1 -
v v5 LocalAddr t21 0 a3 p43:2734:2:0:0 0 v10,v1
names -
splits -
canon -
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
v v7 SB t2 0 - p0:0:0:0:0 0 -
v v10 SP t2 0 - p0:0:0:0:0 1 -
v v5 LocalAddr t21 0 a3 p43:2734:2:0:0 0 v10,v1
names -
splits -
canon -
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
v v7 SB t2 0 - p0:0:0:0:0 0 -
v v10 SP t2 0 - p0:0:0:0:0 1 -
v v5 LocalAddr t21 0 a3 p43:2734:2:0:0 0 v10,v1
names -
splits -
canon -
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v8 OffPtr t213 48 - p43:2734:38:0:0 1 v6
v v9 Load t46 0 - p43:2734:38:0:0 1 v8,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v8,v5,v10,v7,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.getm}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
regalloc 13 v6:g,v9:R0,v11:R0,v12:[]
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
regalloc 13 v6:g,v9:R0,v11:R0,v12:[]
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p43:2734:36:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 GetG t33 0 - p43:2734:36:1:0 1 v1
v v9 ARM64MOVDload t46 48 - p43:2734:38:0:0 1 v6,v1
v v11 Convert t2 0 - p43:2734:31:0:0 1 v9,v1
v v12 MakeResult t214 0 - p43:2734:2:0:0 1 v11,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 43:2734:2734
fstate scheduled,laidout
regalloc 13 v6:g,v9:R0,v11:R0,v12:[]
dcllen 1
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27,t33,t34,t35,t36,t37,t38,t39,t40,t41,t42,t43,t44,t45,t46,t47,t48,t49,t50,t51,t53,t55,t57,t58,t59,t60,t62,t66,t67,t69,t71,t72,t74,t75,t76,t78,t79,t80,t81,t83,t84,t88,t89,t91,t94,t97,t99,t100,t101,t103,t104,t105,t106,t107,t111,t113,t115,t118,t119,t120,t121,t123,t124,t127,t128,t129,t131,t133,t134,t136,t139,t140,t141,t142,t144,t145,t147,t148,t149,t151,t153,t156,t158,t160,t161,t163,t164,t165,t166,t169,t171,t172,t173,t175,t176,t183,t186,t188,t190,t191,t194,t201,t203,t205,t207,t210,t212
typelink t8=t80,t17=t88,t28=t32
typecmp t80 t86 lt
typeorder t4,t86,t8=t80,t85,t73,t200,t178,t5,t9,t6,t89,t90,t10,t54,t7,t199,t11,t185,t12,t125,t15,t136,t2,t49,t60,t53,t70,t25,t26,t13,t14,t3,t17=t88,t18,t19,t20,t142,t21,t22,t23,t24,t213,t202,t143,t170,t33,t46,t57,t206,t83,t66,t103,t152,t39,t36,t71,t61,t110,t155,t163,t78,t130,t138,t182,t68,t119,t168,t157,t209,t126,t96,t42,t41,t1,t208,t162,t177,t87,t154,t201,t176,t56,t102,t98,t150,t203,t112,t117,t181,t180,t189,t116,t196,t92,t113,t52,t190,t197,t167,t160,t195,t173,t99,t145,t109,t107,t91,t65,t133,t135,t100,t148,t144,t186,t51,t171,t108,t137,t34,t47,t58,t193,t64,t207,t172,t84,t141,t101,t48,t67,t76,t35,t104,t153,t147,t166,t194,t156,t121,t75,t40,t37,t72,t129,t128,t62,t111,t149,t55,t124,t45,t164,t82,t79,t131,t122,t192,t139,t183,t211,t165,t81,t161,t69,t174,t120,t94,t134,t151,t169,t63,t59,t187,t132,t212,t179,t114,t204,t158,t50,t198,t123,t175,t95,t188,t74,t93,t44,t140,t77,t210,t184,t191,t118,t105,t159,t127,t106,t146,t97,t115,t43,t205,t38,t16,t27,t28,t30,t29,t31,t32,t214
eof
"#

/-- `std/std/runtime/getm,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "getm" 1
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
config compilingruntime 1
config gendwarfinl 2
config debugasm 0
config mergelocalshash ""
frame
type t1 8 8 0 0 - "uintptr"
name n1 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a3
in n1 0 outregs
opt n1 0 outregs
stack 0 0 8
end
genin
posbase p43 "runtime/proc.go" 1 1 -1 42 "runtime/proc.go" "runtime/proc.go" 1 1
sym y1 "runtime.getm" 1
curfn p43:2733:6:0:0 0 0
regargs -
text y1 0 0 0 0 2733 280080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 0 p43:2733:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p43:2733:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p43:2733:6:0:0
p 3 3 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p43:2734:36:1:0
p 4 4 0 0 0 - MOVD 0 MEM/8220/0/0/NONE/0/48/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p43:2734:36:1:0
p 5 5 0 0 0 - RET 0 _ 0 - _ 0 0 p43:2734:36:2:0
p 6 6 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 2733 280080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgregout n1
dbgpc -
end
asm
sym y3 "" 0
sym y4 "" 0
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 2 p43:2733:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p43:2733:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p43:2733:6:0:0
p 3 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p43:2734:36:1:0
p 4 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/48/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p43:2734:36:1:0
p 5 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p43:2734:36:2:0
fn y1 0 0 0 0 2733 2800c8
funcaux y2 y2 - - - - -
text 16 0 801b40f9c0035fd60000000000000000 0
pcln y4 y5 y6 y7 y3 y2,y2
usedfiles 42
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SRODATA 3 1 28000 010400 0
data y4 SRODATA 3 1 28000 020400 0
data y5 SRODATA 3 1 28000 560400 0
data y6 SRODATA 4 1 28000 de2a0400 0
data y7 SRODATA 3 1 28000 000400 0
end
dwarf
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "go:info.uintptr" 0
sym y13 "type:uintptr" 0
dwfn y8 y9 y10 - y11 "runtime.getm" 42:2733 1 0 1 4262
dwdcl -
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 0 0 0 0 0 0 1 - - "uintptr" 0 0 1 p43:2733:13:0:0
var 0 0 "~r0" 5 1 1 0 0 0 y12 "runtime/proc.go" 2733 13 0 0 0 0 -
scope 0 0 - 0
data y8 SDWARFFCN 40 0 0 0372756e74696d652e6765746d00000010019c2b000000ad15012e7e72300001ad15000000000000 3
reloc 0 0 R_USETYPE 0 y13
reloc 14 2 R_DWTXTADDR_U2 0 y1
reloc 34 4 R_DWARFSECREF 0 y12
data y9 SDWARFLOC 0 0 0 - 0
data y10 SDWARFRANGE 0 0 0 - 0
data y11 SDWARFLINES 24 0 0 0009020000000000000000042b03a815140637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `getm` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

def lc : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

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

/-- The PC table `checkG17` gives (block `b1`: `v6` at the no-op Progs from 3, `v9`'s `MOVD`
after them, then `RET`). -/
def tab : PcTab := [(1, [3, 3, 3, 5, 5, 5])]

/-- The class table `checkG17` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot)]

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The goroutine's address. -/
def gA : BitVec 64 := 0x9000

/-- `ι`: `nil` at 0, the global `runtime.g` (`GetG`'s block) at the goroutine `gA`, every other
global at `symA`. -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global n => if n = "runtime.g" then some gA else some GenG2.symA
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = gA`, saved `LR` and `FP` 0) with the PC table of
`checkG17`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := gA, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v6`: every register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v6`: `X28` the goroutine `gA`, the activation's `FP`, the PC of `v6`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then gA else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 1, mem := fun _ => 0 }

/-- The `g` register (Go register 26) holds the pointer to the start of `runtime.g`. -/
def gIs (s : LocState) : Bool :=
  match (s.regs[26]? : Option Val) with
  | some (Val.ptr p) => p.blk == .global "runtime.g" && p.off == 0
  | _ => false

theorem gIs_spec {s : LocState} (h : gIs s = true) :
    s.regs[26]? = some (.ptr ⟨.global "runtime.g", 0⟩) := by
  unfold gIs at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hp]
    obtain ⟨b, o⟩ := p
    simp only at h
    rw [h.1, h.2]
  · cases h

/-- What compiled evaluation checks on `getm`: `checkG17` accepts it with `tab` and `kt` and
`checkG16` does not; it accesses no frame variable, has no home slot and no symbol named
`runtime.g`; `b1` holds `v6` at index 1, a `GetG`; `stepLoc` runs `v6` from `s0` and the `g`
register then holds the pointer to `runtime.g`. -/
def gFacts : Bool :=
  (checkG17 lc ps bs g).toOption == some (tab, kt) && (checkG16 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    g.syms.all (fun y => y.1.toStringLossy != "runtime.g") &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 6).isSome && blk1.values[1]? == some 6 && (val 6).op == .GetG &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 6)) gIs

theorem g17_facts : gFacts = true := by
  native_decide

/-- The facts of `g17_facts` as hypotheses. -/
theorem facts :
    checkG17 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧
      g.syms.all (fun y => y.1.toStringLossy != "runtime.g") = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk1 ∧
      lc.ctx.f.value? 6 = some (val 6) ∧ blk1.values[1]? = some 6 ∧ (val 6).op = .GetG ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 6)) gIs = true := by
  have hf := g17_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hsy⟩, hm1⟩, hb1s⟩, hv6⟩, hi1⟩, hop⟩, hrun⟩ := hf
  refine ⟨?_, hav, hsl, hsy, hm1, ?_, ?_, hi1, hop, hrun⟩
  · revert hres; cases checkG17 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv6
    simp [val, hv]

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k => simp [ι] at ha
  | _ => simp [ι] at ha <;> simp [Blk.base?] at hb

theorem g17Env (hc : checkG17 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true)
    (hsy : g.syms.all (fun y => y.1.toStringLossy != "runtime.g") = true) :
    G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG17_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := addrAgree
        glob := by
          intro y name abi hy
          have hn := Array.all_eq_true.1 hsy y (Array.getElem?_eq_some_iff.1 hy).1
          simp only [(Array.getElem?_eq_some_iff.1 hy).2, bne_iff_ne, ne_eq] at hn
          have hs : L.sym y = GenG2.symA := rfl
          rw [hs]
          simp [E, ι, hn]
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG17_spec hc
          intro y
          have hs : L.sym y = GenG2.symA := rfl
          rw [hs]
          refine ⟨by decide, fun p hp => ?_⟩
          exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
        calls := fun h => by cases h
        slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
        extra := by decide
        frame := ⟨by decide, by decide, fun k off h => by cases h⟩ }
      vars := by
        intro x hx
        simp [List.isEmpty_iff.1 hav] at hx }
    wbs := fun h => by cases h }
  icalls := fun h => by cases h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g17Inv0 : G3Inv E lc (kAt lc kt 1 blk1 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G17 on `getm`**: from the state before `v6` with every register `poison`, `X28` the
goroutine `gA` and `ι` putting `runtime.g` there (`GetGOK`), `g17_value` runs `GetG` (no code) and
gives the state before `v9`, with the `g` register holding the pointer to `runtime.g`, related to
`X28` under an activation that extends `E` and is a `G10Env`. -/
theorem genG17_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 6) = .ok s1 ∧
      s1.regs[26]? = some (.ptr ⟨.global "runtime.g", 0⟩) ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 1 2 m1 ∧ G3Inv E' lc (kAt lc kt 1 blk1 2) s1 := by
  obtain ⟨hc, hav, hsl, hsy, hm1, hb, hv6, hi1, hop, hrun⟩ := facts
  obtain ⟨s1, hs1, hg⟩ := GenG1.okThen_spec hrun
  have hE := g17Env hc hav hsl hsy
  have hne : ∀ o : Op, o ≠ .GetG → (val 6).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g17_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm1 hb hi1 hv6 (by rw [hop]; rfl) locMatch0 g17Inv0
    ⟨⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; rfl)
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _,
      fun h => absurd h (hne _ (by decide))⟩,
      fun _ _ _ _ hl => by rw [hop] at hl; simp [loadIdxOp?] at hl⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ => by simp [E, ι]) hs1
  exact ⟨s1, E1, m1, hs1, gIs_spec hg, hx1, hE1, hp1, hm1', hinv1⟩

end GoFV.Proof.Witness.GenG17
