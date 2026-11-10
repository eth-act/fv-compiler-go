import GoFV.Proof.Gen.G57b
import GoFV.Gen.Check55
import GoFV.Proof.Witness.GenG37

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG57b2

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/mallocgcSmallNoscanReuse,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "mallocgcSmallNoscanReuse" 1 0 0
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
type t5 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t4 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t5 0 0
type t6 INT64 8 8 0 comparable,named "int64" "int64"
type t7 INT 8 8 0 comparable,named "int" "int"
type t8 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t13 STRUCT 16 8 0 notinheap,comparable,named "mSpanList" "runtime.mSpanList" 3
field 0 "_" t4 0 0
field 1 "first" t10 0 0
field 2 "last" t10 8 0
type t12 PTR 8 8 0 comparable "*mSpanList" "*runtime.mSpanList" t13
type t14 UINTPTR 8 8 0 comparable,named "gclinkptr" "runtime.gclinkptr"
type t15 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t16 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t19 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t18 STRUCT 1 1 0 notinheap,comparable,named "gcBits" "runtime.gcBits" 2
field 0 "_" t4 0 0
field 1 "x" t19 0 0
type t17 PTR 8 8 0 comparable "*gcBits" "*runtime.gcBits" t18
type t20 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t21 UINT8 1 1 0 comparable,named "spanClass" "runtime.spanClass"
type t24 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t23 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t24 0 0
field 1 "value" t19 0 0
type t22 STRUCT 1 1 0 comparable,named "mSpanStateBox" "runtime.mSpanStateBox" 1
field 0 "s" t23 0 0
type t25 BOOL 1 1 0 comparable,named "bool" "bool"
type t27 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t26 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t27 0 1
field 1 "key" t8 0 0
type t30 UINT8 1 1 0 comparable,named "byte" "uint8"
type t29 STRUCT 24 8 0 notinheap,comparable,named "special" "runtime.special" 4
field 0 "_" t4 0 0
field 1 "next" t28 0 0
field 2 "offset" t8 8 0
field 3 "kind" t30 16 0
type t28 PTR 8 8 0 comparable "*special" "*runtime.special" t29
type t32 STRUCT 8 8 0 comparable,named "offAddr" "runtime.offAddr" 1
field 0 "a" t8 0 0
type t31 STRUCT 16 8 0 comparable,named "addrRange" "runtime.addrRange" 2
field 0 "base" t32 0 0
field 1 "limit" t32 8 0
type t35 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t36 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t38 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t37 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t38 ? 0
field 1 "" t38 ? 0
field 2 "" t25 ? 0
type t39 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t30
type t40 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t41 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t34 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t8 0 0
field 1 "PtrBytes" t8 8 0
field 2 "Hash" t20 16 0
field 3 "TFlag" t35 20 0
field 4 "Align_" t19 21 0
field 5 "FieldAlign_" t19 22 0
field 6 "Kind_" t36 23 0
field 7 "Equal" t37 24 0
field 8 "GCData" t39 32 0
field 9 "Str" t40 40 0
field 10 "PtrToThis" t41 44 0
type t33 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t34
type t11 STRUCT 160 8 160 hasptr,notinheap,comparable,named "mspan" "runtime.mspan" 28
field 0 "_" t4 0 0
field 1 "next" t10 0 0
field 2 "prev" t10 8 0
field 3 "list" t12 16 0
field 4 "startAddr" t8 24 0
field 5 "npages" t8 32 0
field 6 "manualFreeList" t14 40 0
field 7 "freeindex" t15 48 0
field 8 "nelems" t15 50 0
field 9 "freeIndexForScan" t15 52 0
field 10 "allocCache" t16 56 0
field 11 "allocBits" t17 64 0
field 12 "gcmarkBits" t17 72 0
field 13 "pinnerBits" t17 80 0
field 14 "sweepgen" t20 88 0
field 15 "divMul" t20 92 0
field 16 "allocCount" t15 96 0
field 17 "spanclass" t21 98 0
field 18 "state" t22 99 0
field 19 "needzero" t19 100 0
field 20 "isUserArenaChunk" t25 101 0
field 21 "allocCountBeforeCache" t15 102 0
field 22 "elemsize" t8 104 0
field 23 "limit" t8 112 0
field 24 "speciallock" t26 120 0
field 25 "specials" t28 128 0
field 26 "userArenaChunkFree" t31 136 0
field 27 "largeType" t33 152 0
type t10 PTR 8 8 0 comparable "*mspan" "*runtime.mspan" t11
type t9 ARRAY 1088 8 0 comparable "[136]*mspan" "[136]*runtime.mspan" t10 136
type t42 ARRAY 1088 8 0 comparable "[136]gclinkptr" "[136]runtime.gclinkptr" t14 136
type t44 STRUCT 16 8 0 comparable,named "stackfreelist" "runtime.stackfreelist" 2
field 0 "list" t14 0 0
field 1 "size" t8 8 0
type t43 ARRAY 64 8 0 comparable "[4]stackfreelist" "[4]runtime.stackfreelist" t44 4
type t45 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t24 0 0
field 1 "value" t20 0 0
type t3 STRUCT 2296 8 0 notinheap,comparable,named "mcache" "runtime.mcache" 11
field 0 "_" t4 0 0
field 1 "nextSample" t6 0 0
field 2 "memProfRate" t7 8 0
field 3 "scanAlloc" t8 16 0
field 4 "tiny" t8 24 0
field 5 "tinyoffset" t8 32 0
field 6 "tinyAllocs" t8 40 0
field 7 "alloc" t9 48 0
field 8 "reusableNoscan" t42 1136 0
field 9 "stackcache" t43 2224 0
field 10 "flushGen" t45 2288 0
type t2 PTR 8 8 0 comparable "*mcache" "*runtime.mcache" t3
type t1 FUNC 8 8 8 hasptr,direct "func(*mcache, *mspan, spanClass, uintptr, bool) unsafe.Pointer" "func(*runtime.mcache, *runtime.mspan, runtime.spanClass, uintptr, bool) unsafe.Pointer" 0 5 1
field 0 "c" t2 ? 0
field 1 "span" t10 ? 0
field 2 "spc" t21 ? 0
field 3 "size" t8 ? 0
field 4 "needzero" t25 ? 0
field 5 "" t38 ? 0
aux a2 sym "runtime.mallocgcSmallNoscanReuse" "runtime.mallocgcSmallNoscanReuse" 1 - 0 - - - - 0
posbase p53 "runtime/malloc.go" 1 1 -1
aux a3 name "c" "c" PPARAM t2 0 1 used p53:1462:31:0:0
aux a4 name "span" "span" PPARAM t10 8 1 used p53:1462:42:0:0
aux a5 name "spc" "spc" PPARAM t21 16 1 used p53:1462:55:0:0
aux a6 name "size" "size" PPARAM t8 24 1 used p53:1462:70:0:0
aux a7 name "needzero" "needzero" PPARAM t25 32 1 used p53:1462:84:0:0
aux a8 name "~r0" "~r0" PPARAMOUT t38 0 1 - p53:1462:99:0:0
aux a1 call "AuxCall{runtime.mallocgcSmallNoscanReuse}" a2 1 5 1 8 40 5 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t10 a4 1 8
abiparam in 2 t21 a5 2 16
abiparam in 3 t8 a6 3 24
abiparam in 4 t25 a7 4 32
abiparam out 0 t38 a8 0 -1
type t46 INT8 1 1 0 comparable,named "int8" "int8"
type t47 INT16 2 2 0 comparable,named "int16" "int16"
type t48 INT32 4 4 0 comparable,named "int32" "int32"
type t49 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t50 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t51 UINT 8 8 0 comparable,named "uint" "uint"
type t52 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t53 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t19
type t54 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t48
type t55 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t20
type t56 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t7
type t57 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t8
type t58 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t49
type t59 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t50
type t60 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t53
type t61 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t62 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t63 SSA ? ? ? - "mem" ""
type t64 SSA ? ? ? - "flags" ""
type t65 SSA ? ? ? - "void" ""
type t66 SSA 16 8 ? - "int128" ""
type t67 RESULTS ? ? ? - "mem" "" 1 t63
type t68 PTR 8 8 8 hasptr,direct,comparable "**mcache" "**runtime.mcache" t2
type t69 PTR 8 8 8 hasptr,direct,comparable "**mspan" "**runtime.mspan" t10
type t70 PTR 8 8 8 hasptr,direct,comparable "*spanClass" "*runtime.spanClass" t21
type t71 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t25
type t72 PTR 8 8 8 hasptr,direct,comparable "*unsafe.Pointer" "*unsafe.Pointer" t38
aux a9 sym "runtime.gcBlackenEnabled" "runtime.gcBlackenEnabled" 0 - 0 - - - - 0
type t75 STRUCT 16 8 0 comparable,named "stack" "runtime.stack" 2
field 0 "lo" t8 0 0
field 1 "hi" t8 8 0
type t78 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t77 STRUCT 96 8 88 hasptr,comparable,named "_panic" "runtime._panic" 14
field 0 "arg" t78 0 0
field 1 "link" t76 16 0
field 2 "startPC" t8 24 0
field 3 "startSP" t38 32 0
field 4 "pc" t8 40 0
field 5 "sp" t38 48 0
field 6 "fp" t38 56 0
field 7 "retpc" t8 64 0
field 8 "deferBitsPtr" t53 72 0
field 9 "slotsPtr" t38 80 0
field 10 "recovered" t25 88 0
field 11 "repanicked" t25 89 0
field 12 "goexit" t25 90 0
field 13 "deferreturn" t25 91 0
type t76 PTR 8 8 8 hasptr,direct,comparable "*_panic" "*runtime._panic" t77
type t81 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
type t84 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.UnsafePointer" "internal/runtime/atomic.UnsafePointer" 2
field 0 "noCopy" t24 0 0
field 1 "value" t38 0 0
type t83 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime._defer]" "internal/runtime/atomic.Pointer[runtime._defer]" 1
field 0 "u" t84 0 0
type t82 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime._defer]" "*internal/runtime/atomic.Pointer[runtime._defer]" t83
type t80 STRUCT 48 8 48 hasptr,named "_defer" "runtime._defer" 7
field 0 "heap" t25 0 0
field 1 "rangefunc" t25 1 0
field 2 "sp" t8 8 0
field 3 "pc" t8 16 0
field 4 "fn" t81 24 0
field 5 "link" t79 32 0
field 6 "head" t82 40 0
type t79 PTR 8 8 8 hasptr,direct,comparable "*_defer" "*runtime._defer" t80
type t88 UINTPTR 8 8 0 comparable,named "guintptr" "runtime.guintptr"
type t87 STRUCT 48 8 32 hasptr,comparable,named "gobuf" "runtime.gobuf" 6
field 0 "sp" t8 0 0
field 1 "pc" t8 8 0
field 2 "g" t88 16 0
field 3 "ctxt" t38 24 0
field 4 "lr" t8 32 0
field 5 "bp" t8 40 0
type t89 STRUCT 40 8 0 comparable,named "gsignalStack" "runtime.gsignalStack" 4
field 0 "stack" t75 0 0
field 1 "stackguard0" t8 16 0
field 2 "stackguard1" t8 24 0
field 3 "stktopsp" t8 32 0
type t90 ARRAY 8 4 0 comparable,named "sigset" "runtime.sigset" t20 2
type t91 ARRAY 48 8 0 comparable "[6]uintptr" "[6]uintptr" t8 6
type t92 UINTPTR 8 8 0 comparable,named "puintptr" "runtime.puintptr"
type t93 UINT32 4 4 0 comparable,named "throwType" "runtime.throwType"
type t97 STRUCT 24 8 0 comparable,named "sysmontick" "runtime.sysmontick" 4
field 0 "schedtick" t20 0 0
field 1 "syscalltick" t20 4 0
field 2 "schedwhen" t6 8 0
field 3 "syscallwhen" t6 16 0
type t98 UINTPTR 8 8 0 comparable,named "muintptr" "runtime.muintptr"
type t99 STRUCT 24 8 0 comparable,named "pageCache" "runtime.pageCache" 3
field 0 "base" t8 0 0
field 1 "cache" t16 8 0
field 2 "scav" t16 16 0
type t102 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime.m]" "internal/runtime/atomic.Pointer[runtime.m]" 1
field 0 "u" t84 0 0
type t101 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime.m]" "*internal/runtime/atomic.Pointer[runtime.m]" t102
type t100 STRUCT 8 8 8 hasptr,direct,comparable,named "mWeakPointer" "runtime.mWeakPointer" 1
field 0 "m" t101 0 0
type t103 SLICE 24 8 8 hasptr "[]*_defer" "[]*runtime._defer" t79
type t104 ARRAY 256 8 256 hasptr,comparable "[32]*_defer" "[32]*runtime._defer" t79 32
type t105 ARRAY 2048 8 0 comparable "[256]guintptr" "[256]runtime.guintptr" t88 256
type t106 STRUCT 16 8 0 comparable,named "gList" "runtime.gList" 2
field 0 "head" t88 0 0
field 1 "size" t48 8 0
type t110 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceablePtr" "runtime.maybeTraceablePtr" 2
field 0 "vp" t38 0 0
field 1 "vu" t8 8 0
type t111 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceableChan" "runtime.maybeTraceableChan" 1
field 0 "maybeTraceablePtr" t110 0 1
type t109 STRUCT 104 8 96 hasptr,comparable,named "sudog" "runtime.sudog" 14
field 0 "g" t73 0 0
field 1 "next" t108 8 0
field 2 "prev" t108 16 0
field 3 "elem" t110 24 0
field 4 "acquiretime" t6 40 0
field 5 "releasetime" t6 48 0
field 6 "ticket" t20 56 0
field 7 "isSelect" t25 60 0
field 8 "success" t25 61 0
field 9 "waiters" t15 62 0
field 10 "parent" t108 64 0
field 11 "waitlink" t108 72 0
field 12 "waittail" t108 80 0
field 13 "c" t111 88 0
type t108 PTR 8 8 8 hasptr,direct,comparable "*sudog" "*runtime.sudog" t109
type t107 SLICE 24 8 8 hasptr "[]*sudog" "[]*runtime.sudog" t108
type t112 ARRAY 1024 8 1024 hasptr,comparable "[128]*sudog" "[128]*runtime.sudog" t108 128
type t114 ARRAY 1024 8 0 comparable "[128]*mspan" "[128]*runtime.mspan" t10 128
type t113 STRUCT 1032 8 0 comparable "struct { len int; buf [128]*mspan }" "struct { runtime.len int; runtime.buf [128]*runtime.mspan }" 2
field 0 "len" t7 0 0
field 1 "buf" t114 8 0
type t117 SLICE 24 8 8 hasptr "[]unsafe.Pointer" "[]unsafe.Pointer" t38
type t118 ARRAY 40 8 40 hasptr,comparable "[5]unsafe.Pointer" "[5]unsafe.Pointer" t38 5
type t116 STRUCT 64 8 64 hasptr,named "pinner" "runtime.pinner" 2
field 0 "refs" t117 0 0
field 1 "refStore" t118 24 0
type t115 PTR 8 8 8 hasptr,direct,comparable "*pinner" "*runtime.pinner" t116
type t121 ARRAY 12 4 0 comparable "[3]atomic.Uint32" "[3]internal/runtime/atomic.Uint32" t45 3
type t122 ARRAY 16 8 0 comparable "[2]uint64" "[2]uint64" t16 2
type t120 STRUCT 32 8 0 comparable,named "traceSchedResourceState" "runtime.traceSchedResourceState" 2
field 0 "statusTraced" t121 0 0
field 1 "seq" t122 16 0
type t119 STRUCT 64 8 0 comparable,named "pTraceState" "runtime.pTraceState" 6
field 0 "traceSchedResourceState" t120 0 1
field 1 "mSyscallID" t6 32 0
field 2 "maySweep" t25 40 0
field 3 "inSweep" t25 41 0
field 4 "swept" t8 48 0
field 5 "reclaimed" t8 56 0
type t125 STRUCT 0 1 0 notinheap,comparable,named "notInHeap" "runtime.notInHeap" 1
field 0 "_" t4 0 0
type t124 PTR 8 8 0 comparable "*notInHeap" "*runtime.notInHeap" t125
type t123 STRUCT 16 8 0 comparable,named "persistentAlloc" "runtime.persistentAlloc" 2
field 0 "base" t124 0 0
field 1 "off" t8 8 0
type t127 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t126 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t24 0 0
field 1 "_" t127 0 0
field 2 "value" t6 0 0
type t129 STRUCT 8 8 0 comparable,named "atomic.Uint64" "internal/runtime/atomic.Uint64" 3
field 0 "noCopy" t24 0 0
field 1 "_" t127 0 0
field 2 "value" t16 0 0
type t128 STRUCT 8 8 0 comparable,named "limiterEvent" "runtime.limiterEvent" 1
field 0 "stamp" t129 0 0
type t130 INT 8 8 0 comparable,named "gcMarkWorkerMode" "runtime.gcMarkWorkerMode"
type t133 STRUCT 16 8 0 comparable,named "lfnode" "runtime.lfnode" 2
field 0 "next" t16 0 0
field 1 "pushcnt" t8 8 0
type t132 STRUCT 32 8 0 comparable,named "gcBgMarkWorkerNode" "runtime.gcBgMarkWorkerNode" 3
field 0 "node" t133 0 0
field 1 "gp" t88 16 0
field 2 "m" t98 24 0
type t131 PTR 8 8 8 hasptr,direct,comparable "*gcBgMarkWorkerNode" "*runtime.gcBgMarkWorkerNode" t132
type t137 STRUCT 24 8 0 comparable,named "workbufhdr" "runtime.workbufhdr" 2
field 0 "node" t133 0 0
field 1 "nobj" t7 16 0
type t138 ARRAY 2024 8 0 comparable "[253]uintptr" "[253]uintptr" t8 253
type t136 STRUCT 2048 8 0 notinheap,comparable,named "workbuf" "runtime.workbuf" 3
field 0 "_" t4 0 0
field 1 "workbufhdr" t137 0 1
field 2 "obj" t138 24 0
type t135 PTR 8 8 0 comparable "*workbuf" "*runtime.workbuf" t136
type t141 UINTPTR 8 8 0 comparable,named "objptr" "runtime.objptr"
type t140 ARRAY 2048 8 0 comparable "[256]objptr" "[256]runtime.objptr" t141 256
type t145 STRUCT 16 8 0 comparable,named "listNodeManual" "runtime.listNodeManual" 2
field 0 "prev" t8 0 0
field 1 "next" t8 8 0
type t146 STRUCT 1 1 0 comparable,named "atomic.Bool" "internal/runtime/atomic.Bool" 1
field 0 "u" t23 0 0
type t147 PTR 8 8 8 hasptr,direct,comparable "*objptr" "*runtime.objptr" t141
type t144 STRUCT 56 8 56 hasptr,notinheap,comparable,named "spanSPMC" "runtime.spanSPMC" 8
field 0 "_" t4 0 0
field 1 "allnode" t145 0 0
field 2 "dead" t146 16 0
field 3 "prev" t84 24 0
field 4 "head" t45 32 0
field 5 "tail" t45 36 0
field 6 "cap" t20 40 0
field 7 "ring" t147 48 0
type t143 PTR 8 8 0 comparable "*spanSPMC" "*runtime.spanSPMC" t144
type t142 STRUCT 16 8 16 hasptr,comparable "struct { head *spanSPMC; tail atomic.UnsafePointer }" "struct { runtime.head *runtime.spanSPMC; runtime.tail internal/runtime/atomic.UnsafePointer }" 2
field 0 "head" t143 0 0
field 1 "tail" t84 8 0
type t139 STRUCT 2080 8 2080 hasptr,comparable,named "spanQueue" "runtime.spanQueue" 5
field 0 "head" t20 0 0
field 1 "tail" t20 4 0
field 2 "ring" t140 8 0
field 3 "putsSinceDrain" t7 2056 0
field 4 "chain" t142 2064 0
type t149 ARRAY 8192 8 0 comparable "[1024]uintptr" "[1024]uintptr" t8 1024
type t148 PTR 8 8 8 hasptr,direct,comparable "*[1024]uintptr" "*[1024]uintptr" t149
type t151 STRUCT 40 8 0 comparable,named "sizeClassScanStats" "runtime.sizeClassScanStats" 5
field 0 "spansDenseScanned" t16 0 0
field 1 "spanObjsDenseScanned" t16 8 0
field 2 "spansSparseScanned" t16 16 0
field 3 "spanObjsSparseScanned" t16 24 0
field 4 "sparseObjsScanned" t16 32 0
type t150 ARRAY 2720 8 0 comparable "[68]sizeClassScanStats" "[68]runtime.sizeClassScanStats" t151 68
type t134 STRUCT 4856 8 2112 hasptr,comparable,named "gcWork" "runtime.gcWork" 10
field 0 "id" t48 0 0
field 1 "wbuf1" t135 8 0
field 2 "wbuf2" t135 16 0
field 3 "spanq" t139 24 0
field 4 "ptrBuf" t148 2104 0
field 5 "bytesMarked" t16 2112 0
field 6 "heapScanWork" t6 2120 0
field 7 "flushedWork" t25 2128 0
field 8 "mayNeedWorker" t25 2129 0
field 9 "stats" t150 2136 0
type t153 ARRAY 4096 8 0 comparable "[512]uintptr" "[512]uintptr" t8 512
type t152 STRUCT 4112 8 0 comparable,named "wbBuf" "runtime.wbBuf" 3
field 0 "next" t8 0 0
field 1 "end" t8 8 0
field 2 "buf" t153 16 0
type t159 FUNC 8 8 8 hasptr,direct "func(any, uintptr, int64)" "func(interface {}, uintptr, int64)" 0 3 0
field 0 "arg" t78 ? 0
field 1 "seq" t8 ? 0
field 2 "delay" t6 ? 0
type t160 PTR 8 8 8 hasptr,direct,comparable "*timers" "*runtime.timers" t154
type t161 STRUCT 4 4 0 comparable,named "atomic.Int32" "internal/runtime/atomic.Int32" 2
field 0 "noCopy" t24 0 0
field 1 "value" t48 0 0
type t158 STRUCT 96 8 80 hasptr,named "timer" "runtime.timer" 15
field 0 "mu" t26 0 0
field 1 "astate" t23 8 0
field 2 "state" t19 9 0
field 3 "isChan" t25 10 0
field 4 "isFake" t25 11 0
field 5 "blocked" t20 12 0
field 6 "rand" t20 16 0
field 7 "when" t6 24 0
field 8 "period" t6 32 0
field 9 "f" t159 40 0
field 10 "arg" t78 48 0
field 11 "seq" t8 64 0
field 12 "ts" t160 72 0
field 13 "sendLock" t26 80 0
field 14 "isSending" t161 88 0
type t157 PTR 8 8 8 hasptr,direct,comparable "*timer" "*runtime.timer" t158
type t156 STRUCT 16 8 8 hasptr,comparable,named "timerWhen" "runtime.timerWhen" 2
field 0 "timer" t157 0 0
field 1 "when" t6 8 0
type t155 SLICE 24 8 8 hasptr "[]timerWhen" "[]runtime.timerWhen" t156
type t154 STRUCT 64 8 16 hasptr,named "timers" "runtime.timers" 7
field 0 "mu" t26 0 0
field 1 "heap" t155 8 0
field 2 "len" t45 32 0
field 3 "zombies" t161 36 0
field 4 "raceCtx" t8 40 0
field 5 "minWhenHeap" t126 48 0
field 6 "minWhenModified" t126 56 0
type t164 STRUCT 32 8 0 notinheap,comparable,named "cleanupBlockHeader" "runtime.cleanupBlockHeader" 4
field 0 "_" t4 0 0
field 1 "lfnode" t133 0 1
field 2 "alllink" t162 16 0
field 3 "n" t20 24 0
type t169 STRUCT 8 8 0 comparable,named "funcval" "runtime.funcval" 1
field 0 "fn" t8 0 0
type t168 PTR 8 8 8 hasptr,direct,comparable "*funcval" "*runtime.funcval" t169
type t167 FUNC 8 8 8 hasptr,direct "func(*funcval, unsafe.Pointer)" "func(*runtime.funcval, unsafe.Pointer)" 0 2 0
field 0 "" t168 ? 0
field 1 "" t38 ? 0
type t166 STRUCT 24 8 24 hasptr,named "cleanupFn" "runtime.cleanupFn" 3
field 0 "call" t167 0 0
field 1 "fn" t168 8 0
field 2 "arg" t38 16 0
type t165 ARRAY 480 8 480 hasptr "[20]cleanupFn" "[20]runtime.cleanupFn" t166 20
type t163 STRUCT 512 8 512 hasptr,notinheap,named "cleanupBlock" "runtime.cleanupBlock" 2
field 0 "cleanupBlockHeader" t164 0 1
field 1 "cleanups" t165 32 0
type t162 PTR 8 8 0 comparable "*cleanupBlock" "*runtime.cleanupBlock" t163
type t172 ARRAY 16 1 0 comparable "[16]byte" "[16]uint8" t30 16
type t171 STRUCT 512 1 0 comparable,named "xRegs" "runtime.xRegs" 32
field 0 "V0" t172 0 0
field 1 "V1" t172 16 0
field 2 "V2" t172 32 0
field 3 "V3" t172 48 0
field 4 "V4" t172 64 0
field 5 "V5" t172 80 0
field 6 "V6" t172 96 0
field 7 "V7" t172 112 0
field 8 "V8" t172 128 0
field 9 "V9" t172 144 0
field 10 "V10" t172 160 0
field 11 "V11" t172 176 0
field 12 "V12" t172 192 0
field 13 "V13" t172 208 0
field 14 "V14" t172 224 0
field 15 "V15" t172 240 0
field 16 "V16" t172 256 0
field 17 "V17" t172 272 0
field 18 "V18" t172 288 0
field 19 "V19" t172 304 0
field 20 "V20" t172 320 0
field 21 "V21" t172 336 0
field 22 "V22" t172 352 0
field 23 "V23" t172 368 0
field 24 "V24" t172 384 0
field 25 "V25" t172 400 0
field 26 "V26" t172 416 0
field 27 "V27" t172 432 0
field 28 "V28" t172 448 0
field 29 "V29" t172 464 0
field 30 "V30" t172 480 0
field 31 "V31" t172 496 0
type t174 STRUCT 512 1 0 notinheap,comparable,named "xRegState" "runtime.xRegState" 2
field 0 "_" t4 0 0
field 1 "regs" t171 0 0
type t173 PTR 8 8 0 comparable "*xRegState" "*runtime.xRegState" t174
type t170 STRUCT 520 8 0 comparable,named "xRegPerP" "runtime.xRegPerP" 2
field 0 "scratch" t171 0 0
field 1 "cache" t173 512 0
type t96 STRUCT 14320 8 13688 hasptr,named "p" "runtime.p" 46
field 0 "id" t48 0 0
field 1 "status" t20 4 0
field 2 "link" t92 8 0
field 3 "schedtick" t20 16 0
field 4 "syscalltick" t20 20 0
field 5 "sysmontick" t97 24 0
field 6 "m" t98 48 0
field 7 "mcache" t2 56 0
field 8 "pcache" t99 64 0
field 9 "raceprocctx" t8 88 0
field 10 "oldm" t100 96 0
field 11 "deferpool" t103 104 0
field 12 "deferpoolbuf" t104 128 0
field 13 "goidcache" t16 384 0
field 14 "goidcacheend" t16 392 0
field 15 "runqhead" t20 400 0
field 16 "runqtail" t20 404 0
field 17 "runq" t105 408 0
field 18 "runnext" t88 2456 0
field 19 "gFree" t106 2464 0
field 20 "sudogcache" t107 2480 0
field 21 "sudogbuf" t112 2504 0
field 22 "mspancache" t113 3528 0
field 23 "pinnerCache" t115 4560 0
field 24 "trace" t119 4568 0
field 25 "palloc" t123 4632 0
field 26 "gcAssistTime" t6 4648 0
field 27 "gcFractionalMarkTime" t126 4656 0
field 28 "limiterEvent" t128 4664 0
field 29 "gcMarkWorkerMode" t130 4672 0
field 30 "gcMarkWorkerStartTime" t6 4680 0
field 31 "nextGCMarkWorker" t131 4688 0
field 32 "gcw" t134 4696 0
field 33 "wbBuf" t152 9552 0
field 34 "runSafePointFn" t20 13664 0
field 35 "statsSeq" t45 13668 0
field 36 "timers" t154 13672 0
field 37 "cleanups" t162 13736 0
field 38 "cleanupsQueued" t16 13744 0
field 39 "maxStackScanDelta" t6 13752 0
field 40 "scannedStackSize" t16 13760 0
field 41 "scannedStacks" t16 13768 0
field 42 "preempt" t25 13776 0
field 43 "gcStopTime" t6 13784 0
field 44 "goroutinesCreated" t16 13792 0
field 45 "xRegs" t170 13800 0
type t95 PTR 8 8 8 hasptr,direct,comparable "*p" "*runtime.p" t96
type t94 SLICE 24 8 8 hasptr "[]*p" "[]*runtime.p" t95
type t176 ARRAY 256 8 0 comparable,named "cgoCallers" "runtime.cgoCallers" t8 32
type t175 PTR 8 8 8 hasptr,direct,comparable "*cgoCallers" "*runtime.cgoCallers" t176
type t177 STRUCT 8 8 0 comparable,named "note" "runtime.note" 1
field 0 "key" t8 0 0
type t178 ARRAY 256 8 0 comparable "[32]uintptr" "[32]uintptr" t8 32
type t179 STRUCT 16 8 0 comparable,named "mWaitList" "runtime.mWaitList" 2
field 0 "next" t98 0 0
field 1 "startTicks" t6 8 0
type t181 SLICE 24 8 8 hasptr "[]uintptr" "[]uintptr" t8
type t180 STRUCT 56 8 16 hasptr,named "mLockProfile" "runtime.mLockProfile" 6
field 0 "waitTime" t126 0 0
field 1 "stack" t181 8 0
field 2 "cycles" t6 32 0
field 3 "cyclesLost" t6 40 0
field 4 "haveStack" t25 48 0
field 5 "disabled" t25 49 0
type t182 FUNC 8 8 8 hasptr,direct "func(*g, unsafe.Pointer) bool" "func(*runtime.g, unsafe.Pointer) bool" 0 2 1
field 0 "" t73 ? 0
field 1 "" t38 ? 0
field 2 "" t25 ? 0
type t183 UINT8 1 1 0 comparable,named "traceBlockReason" "runtime.traceBlockReason"
type t190 UINT64 8 8 0 comparable,named "traceTime" "runtime.traceTime"
type t189 STRUCT 32 8 0 comparable,named "traceBufHeader" "runtime.traceBufHeader" 4
field 0 "link" t187 0 0
field 1 "lastTime" t190 8 0
field 2 "pos" t7 16 0
field 3 "lenPos" t7 24 0
type t191 ARRAY 65504 1 0 comparable "[65504]byte" "[65504]uint8" t30 65504
type t188 STRUCT 65536 8 0 notinheap,comparable,named "traceBuf" "runtime.traceBuf" 3
field 0 "_" t4 0 0
field 1 "traceBufHeader" t189 0 1
field 2 "arr" t191 32 0
type t187 PTR 8 8 0 comparable "*traceBuf" "*runtime.traceBuf" t188
type t186 ARRAY 16 8 0 comparable "[2]*traceBuf" "[2]*runtime.traceBuf" t187 2
type t185 ARRAY 32 8 0 comparable "[2][2]*traceBuf" "[2][2]*runtime.traceBuf" t186 2
type t184 STRUCT 72 8 48 hasptr,comparable,named "mTraceState" "runtime.mTraceState" 6
field 0 "writing" t146 0 0
field 1 "buf" t185 8 0
field 2 "link" t85 40 0
field 3 "reentered" t20 48 0
field 4 "entryGen" t8 56 0
field 5 "oldthrowsplit" t25 64 0
type t192 STRUCT 0 1 0 comparable,named "winlibcall" "runtime.winlibcall" 0
type t196 STRUCT 24 8 0 comparable,named "pcvalueCacheEnt" "runtime.pcvalueCacheEnt" 4
field 0 "targetpc" t8 0 0
field 1 "off" t20 8 0
field 2 "val" t48 12 0
field 3 "valPC" t8 16 0
type t195 ARRAY 192 8 0 comparable "[8]pcvalueCacheEnt" "[8]runtime.pcvalueCacheEnt" t196 8
type t194 ARRAY 384 8 0 comparable "[2][8]pcvalueCacheEnt" "[2][8]runtime.pcvalueCacheEnt" t195 2
type t193 STRUCT 392 8 0 comparable,named "pcvalueCache" "runtime.pcvalueCache" 2
field 0 "entries" t194 0 0
field 1 "inUse" t7 384 0
type t197 STRUCT 0 1 0 comparable,named "dlogPerM" "runtime.dlogPerM" 0
type t198 STRUCT 24 8 0 comparable,named "mOS" "runtime.mOS" 5
field 0 "profileTimer" t48 0 0
field 1 "profileTimerValid" t146 4 0
field 2 "needPerThreadSyscall" t23 5 0
field 3 "vgetrandomState" t8 8 0
field 4 "waitsema" t20 16 0
type t200 ARRAY 256 8 0 comparable "[32]uint64" "[32]uint64" t16 32
type t201 ARRAY 32 8 0 comparable "[4]uint64" "[4]uint64" t16 4
type t199 STRUCT 304 8 0 comparable,named "chacha8rand.State" "internal/chacha8rand.State" 5
field 0 "buf" t200 0 0
field 1 "seed" t201 256 0
field 2 "i" t20 288 0
field 3 "n" t20 292 0
field 4 "c" t20 296 0
type t204 INT64 8 8 0 comparable,named "lockRank" "runtime.lockRank"
type t203 STRUCT 16 8 0 comparable,named "heldLockInfo" "runtime.heldLockInfo" 2
field 0 "lockAddr" t8 0 0
field 1 "rank" t204 8 0
type t202 ARRAY 160 8 0 comparable "[10]heldLockInfo" "[10]runtime.heldLockInfo" t203 10
type t86 STRUCT 1832 8 1832 hasptr,named "m" "runtime.m" 75
field 0 "g0" t73 0 0
field 1 "morebuf" t87 8 0
field 2 "divmod" t20 56 0
field 3 "procid" t16 64 0
field 4 "gsignal" t73 72 0
field 5 "goSigStack" t89 80 0
field 6 "sigmask" t90 120 0
field 7 "tls" t91 128 0
field 8 "mstartfn" t81 176 0
field 9 "curg" t73 184 0
field 10 "caughtsig" t88 192 0
field 11 "signalSecret" t25 200 0
field 12 "p" t92 208 0
field 13 "nextp" t92 216 0
field 14 "oldp" t92 224 0
field 15 "id" t6 232 0
field 16 "mallocing" t48 240 0
field 17 "throwing" t93 244 0
field 18 "preemptoff" t52 248 0
field 19 "locks" t48 264 0
field 20 "dying" t48 268 0
field 21 "profilehz" t48 272 0
field 22 "spinning" t25 276 0
field 23 "blocked" t25 277 0
field 24 "newSigstack" t25 278 0
field 25 "printlock" t46 279 0
field 26 "incgo" t25 280 0
field 27 "isextra" t25 281 0
field 28 "isExtraInC" t25 282 0
field 29 "isExtraInSig" t25 283 0
field 30 "freeWait" t45 284 0
field 31 "needextram" t25 288 0
field 32 "g0StackAccurate" t25 289 0
field 33 "traceback" t19 290 0
field 34 "allpSnapshot" t94 296 0
field 35 "ncgocall" t16 320 0
field 36 "ncgo" t48 328 0
field 37 "cgoCallersUse" t45 332 0
field 38 "cgoCallers" t175 336 0
field 39 "park" t177 344 0
field 40 "alllink" t85 352 0
field 41 "schedlink" t98 360 0
field 42 "idleNode" t145 368 0
field 43 "lockedg" t88 384 0
field 44 "createstack" t178 392 0
field 45 "lockedExt" t20 648 0
field 46 "lockedInt" t20 652 0
field 47 "mWaitList" t179 656 0
field 48 "ditEnabled" t25 672 0
field 49 "mLockProfile" t180 680 0
field 50 "profStack" t181 736 0
field 51 "waitunlockf" t182 760 0
field 52 "waitlock" t38 768 0
field 53 "waitTraceSkip" t7 776 0
field 54 "waitTraceBlockReason" t183 784 0
field 55 "syscalltick" t20 788 0
field 56 "freelink" t85 792 0
field 57 "trace" t184 800 0
field 58 "libcallpc" t8 872 0
field 59 "libcallsp" t8 880 0
field 60 "libcallg" t88 888 0
field 61 "winsyscall" t192 896 0
field 62 "vdsoSP" t8 896 0
field 63 "vdsoPC" t8 904 0
field 64 "preemptGen" t45 912 0
field 65 "signalPending" t45 916 0
field 66 "pcvalueCache" t193 920 0
field 67 "dlogPerM" t197 1312 1
field 68 "mOS" t198 1312 1
field 69 "chacha8" t199 1336 0
field 70 "cheaprand" t20 1640 0
field 71 "cheaprand64" t16 1648 0
field 72 "locksHeldLen" t7 1656 0
field 73 "locksHeld" t202 1664 0
field 74 "self" t100 1824 0
type t85 PTR 8 8 8 hasptr,direct,comparable "*m" "*runtime.m" t86
type t205 UINT8 1 1 0 comparable,named "waitReason" "runtime.waitReason"
type t206 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t30
type t209 STRUCT 40 8 8 hasptr,named "ancestorInfo" "runtime.ancestorInfo" 3
field 0 "pcs" t181 0 0
field 1 "goid" t16 24 0
field 2 "gopc" t8 32 0
type t208 SLICE 24 8 8 hasptr "[]ancestorInfo" "[]runtime.ancestorInfo" t209
type t207 PTR 8 8 8 hasptr,direct,comparable "*[]ancestorInfo" "*[]runtime.ancestorInfo" t208
type t210 STRUCT 4 4 0 comparable,named "goroutineProfileStateHolder" "runtime.goroutineProfileStateHolder" 2
field 0 "noCopy" t24 0 0
field 1 "value" t20 0 0
type t213 FUNC 8 8 8 hasptr,direct "func(*coro)" "func(*runtime.coro)" 0 1 0
field 0 "" t211 ? 0
type t212 STRUCT 32 8 24 hasptr,named "coro" "runtime.coro" 5
field 0 "gp" t88 0 0
field 1 "f" t213 8 0
field 2 "mp" t85 16 0
field 3 "lockedExt" t20 24 0
field 4 "lockedInt" t20 28 0
type t211 PTR 8 8 8 hasptr,direct,comparable "*coro" "*runtime.coro" t212
type t215 STRUCT 144 8 112 hasptr,named "synctestBubble" "runtime.synctestBubble" 12
field 0 "mu" t26 0 0
field 1 "timers" t154 8 0
field 2 "id" t16 72 0
field 3 "now" t6 80 0
field 4 "root" t73 88 0
field 5 "waiter" t73 96 0
field 6 "main" t73 104 0
field 7 "waiting" t25 112 0
field 8 "done" t25 113 0
field 9 "total" t7 120 0
field 10 "running" t7 128 0
field 11 "active" t7 136 0
type t214 PTR 8 8 8 hasptr,direct,comparable "*synctestBubble" "*runtime.synctestBubble" t215
type t216 STRUCT 8 8 0 comparable,named "xRegPerG" "runtime.xRegPerG" 1
field 0 "state" t173 0 0
type t217 STRUCT 32 8 0 comparable,named "gTraceState" "runtime.gTraceState" 1
field 0 "traceSchedResourceState" t120 0 1
type t74 STRUCT 456 8 400 hasptr,named "g" "runtime.g" 65
field 0 "stack" t75 0 0
field 1 "stackguard0" t8 16 0
field 2 "stackguard1" t8 24 0
field 3 "_panic" t76 32 0
field 4 "_defer" t79 40 0
field 5 "m" t85 48 0
field 6 "sched" t87 56 0
field 7 "syscallsp" t8 104 0
field 8 "syscallpc" t8 112 0
field 9 "syscallbp" t8 120 0
field 10 "stktopsp" t8 128 0
field 11 "param" t38 136 0
field 12 "atomicstatus" t45 144 0
field 13 "stackLock" t20 148 0
field 14 "goid" t16 152 0
field 15 "schedlink" t88 160 0
field 16 "waitsince" t6 168 0
field 17 "waitreason" t205 176 0
field 18 "preempt" t25 177 0
field 19 "preemptStop" t25 178 0
field 20 "preemptShrink" t25 179 0
field 21 "asyncSafePoint" t25 180 0
field 22 "paniconfault" t25 181 0
field 23 "gcscandone" t25 182 0
field 24 "throwsplit" t25 183 0
field 25 "activeStackChans" t25 184 0
field 26 "parkingOnChan" t146 185 0
field 27 "inMarkAssist" t25 186 0
field 28 "coroexit" t25 187 0
field 29 "raceignore" t46 188 0
field 30 "nocgocallback" t25 189 0
field 31 "tracking" t25 190 0
field 32 "trackingSeq" t19 191 0
field 33 "trackingStamp" t6 192 0
field 34 "runnableTime" t6 200 0
field 35 "lockedm" t98 208 0
field 36 "fipsIndicator" t19 216 0
field 37 "fipsOnlyBypass" t25 217 0
field 38 "ditWanted" t25 218 0
field 39 "syncSafePoint" t25 219 0
field 40 "runningCleanups" t146 220 0
field 41 "sig" t20 224 0
field 42 "secret" t48 228 0
field 43 "writebuf" t206 232 0
field 44 "sigcode0" t8 256 0
field 45 "sigcode1" t8 264 0
field 46 "sigpc" t8 272 0
field 47 "parentGoid" t16 280 0
field 48 "gopc" t8 288 0
field 49 "ancestors" t207 296 0
field 50 "startpc" t8 304 0
field 51 "racectx" t8 312 0
field 52 "waiting" t108 320 0
field 53 "cgoCtxt" t181 328 0
field 54 "labels" t38 352 0
field 55 "timer" t157 360 0
field 56 "sleepWhen" t6 368 0
field 57 "selectDone" t45 376 0
field 58 "goroutineProfiled" t210 380 0
field 59 "coroarg" t211 384 0
field 60 "bubble" t214 392 0
field 61 "xRegs" t216 400 0
field 62 "trace" t217 408 0
field 63 "gcAssistBytes" t6 440 0
field 64 "valgrindStackID" t8 448 0
type t73 PTR 8 8 8 hasptr,direct,comparable "*g" "*runtime.g" t74
type t220 ARRAY 3 1 0 comparable "[3]byte" "[3]uint8" t30 3
type t219 STRUCT 16 8 0 comparable "struct { enabled bool; pad [3]byte; alignme uint64 }" "struct { runtime.enabled bool; runtime.pad [3]uint8; runtime.alignme uint64 }" 3
field 0 "enabled" t25 0 0
field 1 "pad" t220 1 0
field 2 "alignme" t16 8 0
type t218 PTR 8 8 8 hasptr,direct,comparable "*struct { enabled bool; pad [3]byte; alignme uint64 }" "*struct { runtime.enabled bool; runtime.pad [3]uint8; runtime.alignme uint64 }" t219
aux a10 sym "runtime.writeBarrier" "runtime.writeBarrier" 0 - 0 - - - - 0
posbase p7683 "runtime/malloc.go" 1 1 7406
type t221 PTR 8 8 8 hasptr,direct,comparable "**m" "**runtime.m" t85
type t222 PTR 8 8 8 hasptr,direct,comparable "**g" "**runtime.g" t73
type t223 PTR 8 8 8 hasptr,direct,comparable "*int64" "*int64" t6
aux a11 type "int64" t6
aux a13 sym "runtime.memclrNoHeapPointers" "runtime.memclrNoHeapPointers" 1 - 0 - - - - 0
aux a12 call "AuxCall{runtime.memclrNoHeapPointers}" a13 1 2 0 8 16 2 0
abiparam in 0 t38 - 0 0
abiparam in 1 t8 - 1 8
type t224 RESULTS ? ? ? - "unsafe.Pointer,mem" "" 2 t38,t63
aux a15 sym "runtime.gcmarknewobject" "runtime.gcmarknewobject" 1 - 0 - - - - 0
aux a14 call "AuxCall{runtime.gcmarknewobject}" a15 1 2 0 8 16 2 0
abiparam in 0 t10 - 0 0
abiparam in 1 t8 - 1 8
slot s1 a3 t2 0 - 0
slot s2 a4 t10 0 - 0
slot s3 a5 t21 0 - 0
slot s4 a6 t8 0 - 0
slot s5 a7 t25 0 - 0
posbase p7682 "runtime/malloc.go" 1 1 7405
aux a16 name "s" "s" PAUTO t10 0 1 used p7682:2028:37:0:0
slot s6 a16 t10 0 - 0
aux a17 name "~r0" "~r0" PAUTO t14 0 1 - p7682:2028:63:0:0
slot s7 a17 t14 0 - 0
aux a18 name "~r1" "~r1" PAUTO t10 0 1 - p7682:2028:74:0:0
slot s8 a18 t10 0 - 0
aux a19 name "v" "v" PAUTO t14 0 1 used p53:1465:2:0:0
slot s9 a19 t14 0 - 0
aux a20 name "x" "x" PAUTO t38 0 1 used p53:1466:2:0:0
slot s10 a20 t38 0 - 0
aux a21 name "size" "size" PAUTO t8 0 1 used p7683:1852:22:0:0
slot s11 a21 t8 0 - 0
aux a22 name "assistG" "assistG" PAUTO t73 0 1 used p7683:1854:2:0:0
slot s12 a22 t73 0 - 0
f b1 t1 a1 87 11
typs Bool=t25,Int8=t46,Int16=t47,Int32=t48,Int64=t6,UInt8=t19,UInt16=t15,UInt32=t20,UInt64=t16,Int=t7,Float32=t49,Float64=t50,UInt=t51,Uintptr=t8,String=t52,BytePtr=t53,Int32Ptr=t54,UInt32Ptr=t55,IntPtr=t56,UintptrPtr=t57,Float32Ptr=t58,Float64Ptr=t59,BytePtrPtr=t60,Complex64=t61,Complex128=t62,UnsafePtr=t38,Mem=t63,Flags=t64,Void=t65,Int128=t66,ResultMem=t67
b b1 Plain p53:1465:33:1:0 0 0 - - b2:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 8 -
v v2 SP t8 0 - p0:0:0:0:0 6 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t68 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t69 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t70 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t57 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t71 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t72 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p53:1462:6:2:0 0 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v12 Arg t21 0 a5 p53:1462:6:2:0 0 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 2 -
v v15 ConstNil t38 0 - p0:0:0:0:0 0 -
v v16 Const64 t7 0 - p0:0:0:0:0 0 -
v v17 InlMark t65 7405 - p53:1465:33:1:0 0 v1
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 b1:0
v v19 Copy t14 0 - p53:1465:10:2:0 1 v18
v v20 Copy t10 0 - p53:1465:10:2:0 2 v11
v v21 Copy t63 0 - p53:1466:22:2:0 4 v1
v v22 Convert t38 0 - p53:1466:22:0:0 2 v19,v21
v v24 Load t20 0 - p53:1474:22:0:0 1 v23,v21
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v58 b9:0,b8:0 b2:1,b7:0
v v58 Phi t25 0 - p53:1480:2:0:0 1 v14,v87
v v79 Phi t38 0 - p53:1480:2:0:0 2 v22,v80
v v82 Phi t10 0 - p53:1480:2:0:0 1 v20,v83
v v84 Phi t63 0 - p53:1480:2:0:0 2 v21,v57
v v85 Phi t8 0 - p53:1480:2:0:0 1 v13,v86
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b5:0 b2:0
v v27 Copy t8 0 - p53:1475:18:2:0 2 v13
v v28 Copy t63 0 - p53:1475:18:2:0 8 v21
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v28
v v30 GetG t73 0 - p7683:1854:17:0:0 3 v28
v v31 NilCheck t73 0 - p7683:1855:12:0:0 1 v30,v28
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v28
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v28
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v28
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 Plain p53:1475:18:0:0 0 0 - - b7:0 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v48 Phi t63 0 - p7683:1859:24:0:0 4 v28,v40
v v49 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v48
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v48
v v52 Copy t8 0 - p7683:1859:33:2:0 1 v27
v v53 Copy t6 0 - p7683:1859:33:2:0 1 v52
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v53
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v48
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v48
v v80 Copy t38 0 - p53:1504:33:2:0 1 v22
v v83 Copy t10 0 - p53:1504:18:2:0 1 v20
v v86 Copy t8 0 - p53:1481:23:2:0 1 v27
v v87 Copy t25 0 - p53:1480:2:2:0 1 v14
b b6 Plain p7683:1856:20:0:0 0 0 - - b5:1 b4:0
v v39 Copy t73 0 - p7683:1856:20:2:0 1 v30
v v40 Copy t63 0 - p7683:1856:20:2:0 5 v28
v v41 NilCheck t73 0 - p7683:1856:20:0:0 1 v39,v40
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v40
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v40
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v40
b b7 Plain p53:1480:2:2:0 0 0 - - b3:1 b5:0
b b8 If p53:1499:17:0:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:0:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:0:0 3 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:0:0 1 v67,v65
v v78 Phi t38 0 - p53:1485:20:0:0 2 v79,v59
v v81 Copy t10 0 - p53:1504:18:2:0 1 v82
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v59 Copy t38 0 - p53:1481:23:2:0 2 v79
v v60 Copy t8 0 - p53:1481:23:2:0 1 v85
v v61 Copy t63 0 - p53:1481:23:2:0 1 v84
v v62 StaticLECall t67 16 a12 p53:1481:23:0:0 1 v59,v60,v61
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v75 Phi t38 0 - p53:1506:2:0:0 1 v78,v70
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:0:0 1 v75,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v69 Copy t10 0 - p53:1504:18:2:0 1 v81
v v70 Copy t38 0 - p53:1504:33:2:0 2 v78
v v71 Copy t63 0 - p53:1504:33:2:0 2 v65
v v72 Convert t8 0 - p53:1504:33:0:0 1 v70,v71
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v69,v72,v71
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v10
named s2 v11,v20,v69,v81,v82,v83
named s3 v12
named s4 v13,v27,v60,v85,v86
named s5 v14,v58,v87
named s6 v11
named s7 v18,v19
named s8 v11,v20
named s9 v19
named s10 v22,v59,v70,v75,v78,v79,v80
named s11 v27,v52
named s12 v30,v39,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v16,v18,v25,3344556677=v15,v37
freev -
freeb -
dcllen 17
end
pass 1 "number lines"
f b1 t1 a1 87 11
b b1 Plain p53:1465:33:1:0 0 0 - - b2:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 8 -
v v2 SP t8 0 - p0:0:0:0:0 6 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t68 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t69 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t70 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t57 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t71 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t72 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p53:1462:6:2:0 0 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v12 Arg t21 0 a5 p53:1462:6:2:0 0 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 2 -
v v15 ConstNil t38 0 - p0:0:0:0:0 0 -
v v16 Const64 t7 0 - p0:0:0:0:0 0 -
v v17 InlMark t65 7405 - p53:1465:33:1:0 0 v1
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 b1:0
v v19 Copy t14 0 - p53:1465:10:2:0 1 v18
v v20 Copy t10 0 - p53:1465:10:2:0 2 v11
v v21 Copy t63 0 - p53:1466:22:2:0 4 v1
v v22 Convert t38 0 - p53:1466:22:1:0 2 v19,v21
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v21
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v58 b9:0,b8:0 b2:1,b7:0
v v58 Phi t25 0 - p53:1480:2:1:0 1 v14,v87
v v79 Phi t38 0 - p53:1480:2:0:0 2 v22,v80
v v82 Phi t10 0 - p53:1480:2:0:0 1 v20,v83
v v84 Phi t63 0 - p53:1480:2:0:0 2 v21,v57
v v85 Phi t8 0 - p53:1480:2:0:0 1 v13,v86
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b5:0 b2:0
v v27 Copy t8 0 - p53:1475:18:2:0 2 v13
v v28 Copy t63 0 - p53:1475:18:2:0 8 v21
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v28
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v28
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v28
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v28
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v28
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v28
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 Plain p53:1475:18:1:0 0 0 - - b7:0 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v48 Phi t63 0 - p7683:1859:24:0:0 4 v28,v40
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v48
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v48
v v52 Copy t8 0 - p7683:1859:33:2:0 1 v27
v v53 Copy t6 0 - p7683:1859:33:2:0 1 v52
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v53
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v48
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v48
v v80 Copy t38 0 - p53:1504:33:2:0 1 v22
v v83 Copy t10 0 - p53:1504:18:2:0 1 v20
v v86 Copy t8 0 - p53:1481:23:2:0 1 v27
v v87 Copy t25 0 - p53:1480:2:2:0 1 v14
b b6 Plain p7683:1856:20:0:0 0 0 - - b5:1 b4:0
v v39 Copy t73 0 - p7683:1856:20:2:0 1 v30
v v40 Copy t63 0 - p7683:1856:20:2:0 5 v28
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v39,v40
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v40
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v40
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v40
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b5:0
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:0:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 3 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
v v78 Phi t38 0 - p53:1485:20:1:0 2 v79,v59
v v81 Copy t10 0 - p53:1504:18:2:0 1 v82
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v59 Copy t38 0 - p53:1481:23:2:0 2 v79
v v60 Copy t8 0 - p53:1481:23:2:0 1 v85
v v61 Copy t63 0 - p53:1481:23:2:0 1 v84
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v59,v60,v61
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v75 Phi t38 0 - p53:1506:2:0:0 1 v78,v70
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v75,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v69 Copy t10 0 - p53:1504:18:2:0 1 v81
v v70 Copy t38 0 - p53:1504:33:2:0 2 v78
v v71 Copy t63 0 - p53:1504:33:2:0 2 v65
v v72 Convert t8 0 - p53:1504:33:1:0 1 v70,v71
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v69,v72,v71
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v10
named s2 v11,v20,v69,v81,v82,v83
named s3 v12
named s4 v13,v27,v60,v85,v86
named s5 v14,v58,v87
named s6 v11
named s7 v18,v19
named s8 v11,v20
named s9 v19
named s10 v22,v59,v70,v75,v78,v79,v80
named s11 v27,v52
named s12 v30,v39,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v16,v18,v25,3344556677=v15,v37
freev -
freeb -
cache postorder b10,b11,b8,b9,b3,b7,b5,b6,b4,b2,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 87 11
b b1 Plain p53:1465:33:1:0 0 0 - - b2:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 28 -
v v2 SP t8 0 - p0:0:0:0:0 6 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t68 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t69 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t70 0 a5 p0:0:0:0:0 0 v2,v1
v v7 LocalAddr t57 0 a6 p0:0:0:0:0 0 v2,v1
v v8 LocalAddr t71 0 a7 p0:0:0:0:0 0 v2,v1
v v9 LocalAddr t72 0 a8 p0:0:0:0:0 0 v2,v1
v v10 Arg t2 0 a3 p53:1462:6:2:0 0 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 6 -
v v12 Arg t21 0 a5 p53:1462:6:2:0 0 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 8 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 3 -
v v15 ConstNil t38 0 - p0:0:0:0:0 0 -
v v16 Const64 t7 0 - p0:0:0:0:0 0 -
v v17 InlMark t65 7405 - p53:1465:33:1:0 0 v1
v v18 Const64 t14 0 - p0:0:0:0:0 2 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 b1:0
v v19 Copy t14 0 - p53:1465:10:2:0 0 v18
v v20 Copy t10 0 - p53:1465:10:2:0 0 v11
v v21 Copy t63 0 - p53:1466:22:2:0 0 v1
v v22 Convert t38 0 - p53:1466:22:1:0 9 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v58 Copy t25 0 - p53:1480:2:1:0 0 v14
v v79 Copy t38 0 - p53:1480:2:0:0 0 v22
v v82 Copy t10 0 - p53:1480:2:0:0 0 v11
v v84 Phi t63 0 - p53:1480:2:0:0 3 v1,v57
v v85 Copy t8 0 - p53:1480:2:0:0 0 v13
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b5:0 b2:0
v v27 Copy t8 0 - p53:1475:18:2:0 0 v13
v v28 Copy t63 0 - p53:1475:18:2:0 0 v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 4 v1
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v1
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 Plain p53:1475:18:1:0 0 0 - - b7:0 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v48 Copy t63 0 - p7683:1859:24:0:0 0 v1
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v52 Copy t8 0 - p7683:1859:33:2:0 0 v13
v v53 Copy t6 0 - p7683:1859:33:2:0 0 v13
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
v v80 Copy t38 0 - p53:1504:33:2:0 0 v22
v v83 Copy t10 0 - p53:1504:18:2:0 0 v11
v v86 Copy t8 0 - p53:1481:23:2:0 0 v13
v v87 Copy t25 0 - p53:1480:2:2:0 0 v14
b b6 Plain p7683:1856:20:0:0 0 0 - - b5:1 b4:0
v v39 Copy t73 0 - p7683:1856:20:2:0 0 v30
v v40 Copy t63 0 - p7683:1856:20:2:0 0 v1
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v30,v1
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b5:0
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:0:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 5 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
v v78 Copy t38 0 - p53:1485:20:1:0 0 v22
v v81 Copy t10 0 - p53:1504:18:2:0 0 v11
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v59 Copy t38 0 - p53:1481:23:2:0 0 v22
v v60 Copy t8 0 - p53:1481:23:2:0 0 v13
v v61 Copy t63 0 - p53:1481:23:2:0 0 v84
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v75 Copy t38 0 - p53:1506:2:0:0 0 v22
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v69 Copy t10 0 - p53:1504:18:2:0 0 v11
v v70 Copy t38 0 - p53:1504:33:2:0 0 v22
v v71 Copy t63 0 - p53:1504:33:2:0 0 v65
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v10
named s2 v11,v11,v11,v11,v11,v11
named s3 v12
named s4 v13,v13,v13,v13,v13
named s5 v14,v14,v14
named s6 v11
named s7 v18,v18
named s8 v11,v11
named s9 v18
named s10 v22,v22,v22,v22,v22,v22,v22
named s11 v13,v13
named s12 v30,v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v16,v18,v25,3344556677=v15,v37
freev -
freeb -
cache postorder b10,b11,b8,b9,b3,b7,b5,b6,b4,b2,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 3 "early deadcode"
f b1 t1 a1 87 11
b b1 Plain p53:1465:33:1:0 0 0 - - b2:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 17 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 b1:0
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b5:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v1
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 Plain p53:1475:18:1:0 0 0 - - b7:0 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b6 Plain p7683:1856:20:0:0 0 0 - - b5:1 b4:0
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v30,v1
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b5:0
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,3344556677=v37
freev v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b8,b9,b3,b7,b5,b6,b4,b2,b1
cache linestarts 53:1465:1506:1465=0,7683:1854:1859
dcllen 17
end
pass 4 "short circuit"
f b2 t1 a1 87 11
b b1 BlockInvalid p53:1465:33:1:0 0 0 - - - -
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 17 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v1
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 BlockInvalid p53:1475:18:1:0 0 0 - - - -
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v30,v1
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,3344556677=v37
freev v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache linestarts 53:1465:1506:1465=0,7683:1854:1859
dcllen 17
end
pass 5 "decompose user"
f b2 t1 a1 87 11
b b1 BlockInvalid p53:1465:33:1:0 0 0 - - - -
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 17 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v1
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b5 BlockInvalid p53:1475:18:1:0 0 0 - - - -
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v30,v1
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,3344556677=v37
freev v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache linestarts 53:1465:1506:1465=0,7683:1854:1859
dcllen 17
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 17 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v37 ConstNil t73 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v31 NilCheck t73 0 - p7683:1855:12:1:0 1 v30,v1
v v32 OffPtr t221 48 - p7683:1855:12:0:0 1 v31
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 NeqPtr t25 0 - p7683:1855:20:0:0 1 v36,v37
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v41 NilCheck t73 0 - p7683:1856:20:1:0 1 v30,v1
v v42 OffPtr t221 48 - p7683:1856:20:0:0 1 v41
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,3344556677=v37
freev v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 7 "opt"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 15 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v42 OffPtr t221 48 - p7683:1856:20:1:0 1 v30
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 8 "zero arg cse"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 15 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v42 OffPtr t221 48 - p7683:1856:20:1:0 1 v30
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 9 "opt deadcode"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 15 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 1 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v42 OffPtr t221 48 - p7683:1856:20:1:0 1 v30
v v43 Load t85 0 - p7683:1856:20:0:0 1 v42,v1
v v44 NilCheck t85 0 - p7683:1856:22:0:0 1 v43,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 1 v44
v v46 Load t73 0 - p7683:1856:22:0:0 1 v45,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v46
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 1 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 1 v55
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v56,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 10 "generic cse"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 15 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 2 v30
v v33 Load t85 0 - p7683:1855:12:0:0 2 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 2 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 2 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v42 OffPtr t221 48 - p7683:1856:20:2:0 0 v30
v v43 Load t85 0 - p7683:1856:20:2:0 0 v32,v1
v v44 NilCheck t85 0 - p7683:1856:22:1:0 0 v33,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 0 v34
v v46 Load t73 0 - p7683:1856:22:0:0 0 v35,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v36
v v49 NilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 0 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 0 v49
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 11 "phiopt"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 15 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 3 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 2 v30
v v33 Load t85 0 - p7683:1855:12:0:0 2 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 2 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 2 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v42 OffPtr t221 48 - p7683:1856:20:2:0 0 v30
v v43 Load t85 0 - p7683:1856:20:2:0 0 v32,v1
v v44 NilCheck t85 0 - p7683:1856:22:1:0 0 v33,v1
v v45 OffPtr t222 184 - p7683:1856:22:0:0 0 v34
v v46 Load t73 0 - p7683:1856:22:0:0 0 v35,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v36
v v49 NilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 0 v47,v1
v v56 OffPtr t223 440 - p7683:1859:9:0:0 0 v49
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v46,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 12 "gcse deadcode"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 13 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 2 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v44 NilCheck t85 0 - p7683:1856:22:1:0 0 v33,v1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v36
v v49 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v49
v v51 Load t6 0 - p7683:1859:9:0:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v55 NilCheck t73 0 - p7683:1859:9:0:0 0 v47,v1
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 13 "nilcheckelim"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 2 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v44 Copy t85 0 - p7683:1856:22:1:0 0 v34
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v49 Copy t73 0 - p7683:1859:9:1:0 1 v55
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v49
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 14 "prove"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 2 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:0:0 0 0 - - b7:1 b4:0
v v44 Copy t85 0 - p7683:1856:22:1:0 0 v34
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:0:0 1 v47,v1
v v49 Copy t73 0 - p7683:1859:9:1:0 1 v55
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v49
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 15 "divisible"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v49,v44,v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 16 "divmod"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v49,v44,v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 17 "middle opt"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v49,v44,v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 18 "known bits"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v49,v44,v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 19 "early fuse"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 Arg t10 0 a4 p53:1462:6:2:0 1 -
v v13 Arg t8 0 a6 p53:1462:6:2:0 2 -
v v14 Arg t25 0 a7 p53:1462:6:2:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticLECall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticLECall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v49,v44,v56,v46,v45,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 20 "expand calls"
aux a23 nameoff "span+0" a4 0
aux a24 nameoff "size+0" a6 0
aux a25 nameoff "needzero+0" a7 0
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
v v49 SP t8 0 - p0:0:0:0:0 4 -
v v44 OffPtr t69 0 - p0:0:0:0:0 0 v49
v v56 OffPtr t57 0 - p0:0:0:0:0 0 v49
v v46 OffPtr t71 0 - p0:0:0:0:0 0 v49
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 2 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
v v45 LocalAddr t72 0 a8 p53:1506:2:1:0 0 v49,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,v44,v56,v46
freev v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 21 "decompose builtin"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
v v49 SP t8 0 - p0:0:0:0:0 4 -
v v44 OffPtr t69 0 - p0:0:0:0:0 0 v49
v v56 OffPtr t57 0 - p0:0:0:0:0 0 v49
v v46 OffPtr t71 0 - p0:0:0:0:0 0 v49
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 2 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
v v45 LocalAddr t72 0 a8 p53:1506:2:1:0 0 v49,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,v44,v56,v46
freev v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 22 "softfloat"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
v v49 SP t8 0 - p0:0:0:0:0 4 -
v v44 OffPtr t69 0 - p0:0:0:0:0 0 v49
v v56 OffPtr t57 0 - p0:0:0:0:0 0 v49
v v46 OffPtr t71 0 - p0:0:0:0:0 0 v49
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 2 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
v v45 LocalAddr t72 0 a8 p53:1506:2:1:0 0 v49,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,v44,v56,v46
freev v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 23 "branchelim"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
v v49 SP t8 0 - p0:0:0:0:0 4 -
v v44 OffPtr t69 0 - p0:0:0:0:0 0 v49
v v56 OffPtr t57 0 - p0:0:0:0:0 0 v49
v v46 OffPtr t71 0 - p0:0:0:0:0 0 v49
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 2 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
v v45 LocalAddr t72 0 a8 p53:1506:2:1:0 0 v49,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18,v44,v56,v46
freev v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 24 "late opt"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 25 "dead auto elim"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 26 "sccp"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 27 "generic deadcode"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 28 "late fuse"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 29 "check bce"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 30 "dse"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 31 "memcombine"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 32 "writebarrier"
f b2 t1 a1 87 11
b b2 If p53:1474:25:0:0 0 0 - v26 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 Const64 t14 0 - p0:0:0:0:0 1 -
v v25 Const32 t20 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v23 Addr t55 0 a9 p0:0:0:0:0 1 v3
v v66 Addr t218 0 a10 p0:0:0:0:0 1 v3
v v24 Load t20 0 - p53:1474:22:1:0 1 v23,v1
v v26 Neq32 t25 0 - p53:1474:22:0:0 1 v24,v25
b b3 If p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 If p7683:1855:23:0:0 0 0 - v38 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v32 OffPtr t221 48 - p7683:1855:12:1:0 1 v30
v v33 Load t85 0 - p7683:1855:12:0:0 1 v32,v1
v v34 NilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v35 OffPtr t222 184 - p7683:1855:14:0:0 1 v34
v v36 Load t73 0 - p7683:1855:14:0:0 2 v35,v1
v v38 IsNonNil t25 0 - p7683:1855:20:0:0 1 v36
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 NilCheck t73 0 - p7683:1859:9:1:0 1 v47,v1
v v50 OffPtr t223 440 - p7683:1859:9:0:0 2 v55
v v51 Load t6 0 - p7683:1859:9:1:0 1 v50,v1
v v54 Add64 t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 Store t63 0 a11 p7683:1859:24:0:0 1 v50,v54,v1
b b8 If p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 PubBarrier t63 0 - p53:1485:20:1:0 4 v64
v v67 OffPtr t71 0 - p53:1499:17:0:0 1 v66
v v68 Load t25 0 - p53:1499:17:1:0 1 v67,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 StaticCall t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 StaticCall t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts 0=v25,v18
freev v45,v46,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 33 "lower"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64MOVDconst t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 34 "addressing modes"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64MOVDconst t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 35 "late lower"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 36 "pair"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 38 "lowered cse"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 39 "elim unread autos"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 41 "lowered deadcode"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 42 "checkLower"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 43 "loop invariant"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 45 "tighten"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache loopnest 12 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 46 "late deadcode"
f b2 t1 a1 87 11
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b7:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b4:1,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb b5,b1
cache postorder b10,b11,b8,b9,b3,b7,b6,b4,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8
cache sdom b2:-:b4:-:2:53,b3:b2:b9:-:23:50,b4:b2:b6:b3:5:20,b6:b4:-:b7:8:11,b7:b4:-:-:14:17,b8:b3:b11:-:32:47,b9:b3:-:b8:26:29,b10:b8:-:-:41:44,b11:b8:-:b10:35:38
cache loopnest 12 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 47 "critical"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 48 "phi tighten"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 0 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 0 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 49 "likelyadjust"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b3:b2,b4:b2,b6:b4,b7:b4,b8:b3,b9:b3,b10:b8,b11:b8,b5:b2,b1:b4,b12:b3,b13:b8
cache sdom b2:-:b5:-:2:77,b3:b2:b12:-:35:74,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b7:b4:-:-:26:29,b8:b3:b13:-:50:71,b9:b3:-:b8:44:47,b10:b8:-:-:65:68,b11:b8:-:b10:59:62,b5:b2:-:b4:5:8,b1:b4:-:b6:14:17,b12:b3:-:b9:38:41,b13:b8:-:b11:53:56
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
dcllen 17
end
pass 50 "layout"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v34 ARM64LoweredNilCheck t85 0 - p7683:1855:14:0:0 1 v33,v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v34,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 1 v30,v36
v v55 ARM64LoweredNilCheck t73 0 - p7683:1859:9:1:0 2 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v55,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v55,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate laidout
dcllen 17
end
pass 51 "schedule"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 11 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 2 v30,v1
v v34 ARM64LoweredNilCheck t65 0 - p7683:1855:14:0:0 0 v33,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 3 v30,v36
v v55 ARM64LoweredNilCheck t65 0 - p7683:1859:9:1:0 0 v47,v1
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
dcllen 17
end
pass 52 "late nilcheck"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 9 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v36
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
dcllen 17
end
pass 53 "flagalloc"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 1 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 9 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v22 Convert t38 0 - p53:1466:22:1:0 3 v18,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v30,v36
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v13,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v11,v72,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v67,v50,v46,v38,v35,v32,v45,v26,v66,v23,v25,v56,v44,v49,v43,v42,v41,v31,v37,v71,v70,v69,v75,v61,v60,v59,v81,v78,v40,v39,v87,v86,v83,v80,v53,v52,v48,v28,v27,v85,v82,v79,v58,v21,v20,v19,v17,v16,v15,v12,v10,v9,v8,v7,v6,v5,v4,v2
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
dcllen 17
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.mallocgcSmallNoscanReuse}" a2 1 5 1 8 40 5 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t10 a4 1 8
abiparam in 2 t21 a5 2 16
abiparam in 3 t8 a6 3 24
abiparam in 4 t25 a7 4 32
abiparam out 0 t38 a8 0 -1
callreg 0:1 - 0 -
aux a12 call "AuxCall{runtime.memclrNoHeapPointers}" a13 1 2 0 8 16 2 0
abiparam in 0 t38 - 0 0
abiparam in 1 t8 - 1 8
callreg 0:1,1:2 - 7fffffff97ffffff -
aux a14 call "AuxCall{runtime.gcmarknewobject}" a15 1 2 0 8 16 2 0
abiparam in 0 t10 - 0 0
abiparam in 1 t8 - 1 8
callreg 0:1,1:2 - 7fffffff97ffffff -
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 9 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v67 Copy t14 0 - p53:1466:22:2:0 1 v18
v v22 Convert t38 0 - p53:1466:22:1:0 4 v67,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
v v50 StoreReg t73 0 - p7683:1854:17:1:0 1 v30
v v23 LoadReg t73 0 - p7683:1859:24:2:0 1 v50
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v23,v36
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
v v38 StoreReg t38 0 - p53:1466:22:1:0 2 v22
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v35 StoreReg t10 0 - p53:1474:25:0:0 1 v11
v v46 Copy t8 0 - p53:1481:23:2:0 1 v13
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v46,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
v v25 LoadReg t38 0 - p53:1506:2:2:0 0 v38
v v56 LoadReg t10 0 - p53:1504:18:2:0 0 v35
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v45 Copy t8 0 - p53:1504:33:2:0 1 v72
v v26 Copy t10 0 - p53:1504:18:2:0 1 v11
v v66 Copy t8 0 - p53:1504:18:2:0 1 v45
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v26,v66,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
v v44 LoadReg t38 0 - p53:1506:2:2:0 0 v38
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v2,v4,v5,v6,v7,v8,v9,v10,v12,v15,v16,v17,v19,v20,v21,v27,v28,v31,v32,v37,v39,v40,v41,v42,v43,v48,v49,v52,v53,v58,v59,v60,v61,v69,v70,v71,v75,v78,v79,v80,v81,v82,v83,v85,v86,v87
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
regalloc 78 v3:SB,v11:R1,v13:R3,v14:R4,v18:ZERO,v22:R0,v23:R2,v24:R2,v25:R0,v26:R0,v30:g,v32:R2,v33:R2,v35:@a4/t10/0/-/0,v36:R2,v38:@a20/t38/0/-/0,v44:R0,v45:R2,v46:R1,v47:R2,v50:@a22/t73/0/-/0,v51:R5,v54:R5,v56:R1,v62:[],v66:R1,v67:R0,v68:R2,v72:R0,v73:[],v77:[]
dcllen 17
end
pass 55 "loop rotate"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b5:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 9 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v67 Copy t14 0 - p53:1466:22:2:0 1 v18
v v22 Convert t38 0 - p53:1466:22:1:0 4 v67,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b6:0,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b6 Plain p7683:1856:20:1:0 0 0 - - b7:1 b4:0
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
v v50 StoreReg t73 0 - p7683:1854:17:1:0 1 v30
v v23 LoadReg t73 0 - p7683:1859:24:2:0 1 v50
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b6:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v23,v36
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b5 Plain p53:1474:25:0:0 0 0 - - b3:0 b2:1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b12:0 b5:0,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
v v38 StoreReg t38 0 - p53:1466:22:1:0 2 v22
b b12 Plain p53:1480:2:0:0 0 0 - - b8:0 b3:1
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v35 StoreReg t10 0 - p53:1474:25:0:0 1 v11
v v46 Copy t8 0 - p53:1481:23:2:0 1 v13
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v46,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
v v25 LoadReg t38 0 - p53:1506:2:2:0 0 v38
v v56 LoadReg t10 0 - p53:1504:18:2:0 0 v35
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b13:0 b12:0,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b13 Plain p53:1499:17:1:0 0 0 - - b10:0 b8:1
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v45 Copy t8 0 - p53:1504:33:2:0 1 v72
v v26 Copy t10 0 - p53:1504:18:2:0 1 v11
v v66 Copy t8 0 - p53:1504:18:2:0 1 v45
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v26,v66,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
v v44 LoadReg t38 0 - p53:1506:2:2:0 0 v38
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b13:0,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v2,v4,v5,v6,v7,v8,v9,v10,v12,v15,v16,v17,v19,v20,v21,v27,v28,v31,v32,v37,v39,v40,v41,v42,v43,v48,v49,v52,v53,v58,v59,v60,v61,v69,v70,v71,v75,v78,v79,v80,v81,v82,v83,v85,v86,v87
freeb -
cache postorder b10,b11,b13,b8,b9,b12,b3,b7,b6,b1,b4,b5,b2
cache idom b2:-,b4:b2,b6:b4,b1:b4,b7:b4,b5:b2,b3:b2,b12:b3,b9:b3,b8:b3,b13:b8,b11:b8,b10:b8
cache sdom b2:-:b5:-:2:77,b4:b2:b1:b3:11:32,b6:b4:-:b7:20:23,b1:b4:-:b6:14:17,b7:b4:-:-:26:29,b5:b2:-:b4:5:8,b3:b2:b12:-:35:74,b12:b3:-:b9:38:41,b9:b3:-:b8:44:47,b8:b3:b13:-:50:71,b13:b8:-:b11:53:56,b11:b8:-:b10:59:62,b10:b8:-:-:65:68
cache loopnest 14 0 - -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
regalloc 78 v3:SB,v11:R1,v13:R3,v14:R4,v18:ZERO,v22:R0,v23:R2,v24:R2,v25:R0,v26:R0,v30:g,v32:R2,v33:R2,v35:@a4/t10/0/-/0,v36:R2,v38:@a20/t38/0/-/0,v44:R0,v45:R2,v46:R1,v47:R2,v50:@a22/t73/0/-/0,v51:R5,v54:R5,v56:R1,v62:[],v66:R1,v67:R0,v68:R2,v72:R0,v73:[],v77:[]
dcllen 17
end
pass 56 "trim"
f b2 t1 a1 87 13
b b2 ARM64NZW p53:1474:25:0:0 0 0 - v24 b4:0,b3:0 -
v v13 ArgIntReg t8 3 a24 p53:1474:25:0:0 2 -
v v11 ArgIntReg t10 1 a23 p53:1474:25:0:0 2 -
v v14 ArgIntReg t25 4 a25 p53:1474:25:0:0 1 -
v v3 SB t8 0 - p0:0:0:0:0 2 -
v v1 InitMem t63 0 - p0:0:0:0:0 9 -
v v18 ARM64ZERO t14 0 - p0:0:0:0:0 1 -
v v67 Copy t14 0 - p53:1466:22:2:0 1 v18
v v22 Convert t38 0 - p53:1466:22:1:0 4 v67,v1
v v24 ARM64MOVWUload t20 0 a9 p53:1474:22:1:0 1 v3,v1
b b4 ARM64NZ p7683:1855:23:0:0 0 0 - v36 b7:1,b1:0 b2:0
v v30 GetG t73 0 - p7683:1854:17:1:0 2 v1
v v33 ARM64MOVDload t85 48 - p7683:1855:12:1:0 1 v30,v1
v v29 InlMark t65 7406 - p53:1475:18:1:0 0 v1
v v36 ARM64MOVDload t73 184 - p7683:1855:14:0:0 2 v33,v1
b b1 Plain p7683:1855:23:0:0 0 0 - - b7:0 b4:1
v v50 StoreReg t73 0 - p7683:1854:17:1:0 1 v30
v v23 LoadReg t73 0 - p7683:1859:24:2:0 1 v50
b b7 Plain p53:1475:18:1:0 0 0 - - b3:1 b1:0,b4:0
v v47 Phi t73 0 - p7683:1859:24:0:0 2 v23,v36
v v51 ARM64MOVDload t6 440 - p7683:1859:9:1:0 1 v47,v1
v v54 ARM64ADD t6 0 - p7683:1859:24:0:0 1 v51,v13
v v57 ARM64MOVDstore t63 440 - p7683:1859:24:0:0 1 v47,v54,v1
b b3 ARM64TBNZ p53:1480:2:0:0 -1 0 - v14 b9:0,b8:0 b2:1,b7:0
v v84 Phi t63 0 - p53:1480:2:1:0 2 v1,v57
v v38 StoreReg t38 0 - p53:1466:22:1:0 2 v22
b b9 Plain p53:1481:23:0:0 0 0 - - b8:1 b3:0
v v35 StoreReg t10 0 - p53:1474:25:0:0 1 v11
v v46 Copy t8 0 - p53:1481:23:2:0 1 v13
v v62 ARM64CALLstatic t67 16 a12 p53:1481:23:1:0 1 v22,v46,v84
v v63 SelectN t63 0 - p53:1481:23:0:0 1 v62
v v25 LoadReg t38 0 - p53:1506:2:2:0 0 v38
v v56 LoadReg t10 0 - p53:1504:18:2:0 0 v35
b b8 ARM64TBNZ p53:1499:17:1:0 -1 0 - v68 b11:0,b10:0 b3:1,b9:0
v v64 Phi t63 0 - p53:1485:20:1:0 1 v84,v63
v v65 ARM64DMB t63 14 - p53:1485:20:1:0 4 v64
v v68 ARM64MOVBUload t25 0 a10 p53:1499:17:1:0 1 v3,v65
b b11 Plain p53:1504:33:0:0 0 0 - - b10:1 b8:0
v v72 Convert t8 0 - p53:1504:33:1:0 1 v22,v65
v v45 Copy t8 0 - p53:1504:33:2:0 1 v72
v v26 Copy t10 0 - p53:1504:18:2:0 1 v11
v v66 Copy t8 0 - p53:1504:18:2:0 1 v45
v v73 ARM64CALLstatic t67 16 a14 p53:1504:18:0:0 1 v26,v66,v65
v v74 SelectN t63 0 - p53:1504:18:0:0 1 v73
v v44 LoadReg t38 0 - p53:1506:2:2:0 0 v38
b b10 Ret p53:1506:2:1:0 0 0 - v77 - b8:1,b11:0
v v76 Phi t63 0 - p53:1506:2:0:0 1 v65,v74
v v77 MakeResult t224 0 - p53:1506:2:1:0 1 v22,v76
names s2,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s2 v11
named s4 v13
named s5 v14
named s6 v11
named s7 v18
named s8 v11
named s9 v18
named s10 v22
named s11 v13
named s12 v30,v47
splits -
canon a3/t2/0/-/0=s1,a4/t10/0/-/0=s2,a5/t21/0/-/0=s3,a6/t8/0/-/0=s4,a7/t25/0/-/0=s5,a16/t10/0/-/0=s6,a17/t14/0/-/0=s7,a18/t10/0/-/0=s8,a19/t14/0/-/0=s9,a20/t38/0/-/0=s10,a21/t8/0/-/0=s11,a22/t73/0/-/0=s12
consts -
freev v2,v4,v5,v6,v7,v8,v9,v10,v12,v15,v16,v17,v19,v20,v21,v27,v28,v31,v32,v37,v39,v40,v41,v42,v43,v48,v49,v52,v53,v58,v59,v60,v61,v69,v70,v71,v75,v78,v79,v80,v81,v82,v83,v85,v86,v87
freeb -
cache auxmap -:1,a4:2,a6:3,a7:4,a9:5,a10:6,a23:7,a24:8,a25:9
cache linestarts 53:1465:1506,7683:1854:1859
fstate scheduled,laidout
regalloc 78 v3:SB,v11:R1,v13:R3,v14:R4,v18:ZERO,v22:R0,v23:R2,v24:R2,v25:R0,v26:R0,v30:g,v32:R2,v33:R2,v35:@a4/t10/0/-/0,v36:R2,v38:@a20/t38/0/-/0,v44:R0,v45:R2,v46:R1,v47:R2,v50:@a22/t73/0/-/0,v51:R5,v54:R5,v56:R1,v62:[],v66:R1,v67:R0,v68:R2,v72:R0,v73:[],v77:[]
dcllen 17
end
frontend
end
ptrcache t3,t6,t7,t8,t10,t11,t13,t15,t16,t17,t18,t19,t20,t22,t23,t24,t25,t26,t28,t29,t30,t31,t33,t34,t38,t39,t40,t42,t45,t46,t47,t48,t49,t50,t51,t52,t53,t57,t60,t61,t62,t73,t74,t75,t76,t77,t78,t79,t80,t81,t82,t83,t84,t85,t86,t87,t88,t89,t90,t92,t95,t96,t97,t98,t99,t102,t104,t105,t106,t108,t109,t110,t111,t112,t116,t118,t120,t123,t124,t125,t126,t128,t129,t132,t133,t134,t136,t138,t139,t141,t144,t145,t146,t147,t149,t150,t152,t153,t154,t156,t158,t161,t163,t165,t166,t168,t169,t170,t171,t174,t176,t177,t178,t180,t181,t188,t191,t193,t195,t196,t199,t206,t208,t210,t212,t215,t217,t222
typelink t19=t30,t39=t53,t63=t67
typecmp t19 t30 eq
typeorder t46,t30,t36,t19,t35,t21,t205,t183,t47,t15,t48,t40,t41,t20,t93,t6,t204,t16,t190,t7,t130,t51,t141,t8,t88,t98,t92,t14,t61,t62,t49,t50,t25,t39=t53,t70,t54,t55,t223,t56,t147,t57,t58,t59,t71,t60,t222,t221,t69,t68,t207,t148,t175,t218,t73,t85,t95,t211,t33,t10,t108,t157,t79,t76,t17,t2,t115,t160,t168,t28,t135,t143,t187,t12,t124,t173,t162,t214,t131,t101,t82,t72,t81,t213,t167,t182,t37,t159,t1,t206,t181,t94,t107,t103,t155,t208,t117,t122,t186,t185,t194,t220,t121,t201,t43,t118,t91,t195,t202,t172,t165,t200,t178,t104,t150,t114,t112,t42,t9,t138,t140,t105,t153,t149,t191,t90,t176,t113,t142,t219,t74,t86,t96,t198,t5,t212,t177,t34,t146,t106,t87,t11,t26,t75,t109,t158,t152,t171,t199,t161,t126,t23,t80,t77,t18,t134,t133,t3,t116,t154,t45,t129,t24,t169,t32,t29,t136,t127,t197,t144,t188,t216,t170,t31,t166,t13,t179,t125,t99,t139,t156,t174,t4,t97,t192,t137,t217,t184,t119,t209,t163,t89,t203,t128,t180,t100,t193,t22,t44,t84,t145,t27,t215,t189,t196,t123,t110,t164,t132,t111,t151,t102,t120,t83,t210,t78,t52,t38,t63,t65,t64,t66,t67,t224
eof
"#

/-- `std/std/runtime/mallocgcSmallNoscanReuse,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "mallocgcSmallNoscanReuse" 1
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
type t1 8 8 0 0 - "*mcache"
name n1 "c" PPARAM t1 1 "runtime.c" 0 a3
type t2 8 8 0 0 - "*mspan"
name n2 "span" PPARAM t2 1 "runtime.span" 0 a4
type t3 1 1 0 0 - "spanClass"
name n3 "spc" PPARAM t3 1 "runtime.spc" 0 a5
type t4 8 8 0 0 - "uintptr"
name n4 "size" PPARAM t4 1 "runtime.size" 0 a6
type t5 1 1 0 0 - "bool"
name n5 "needzero" PPARAM t5 1 "runtime.needzero" 0 a7
type t6 8 8 8 1 01 "unsafe.Pointer"
name n6 "~r0" PPARAMOUT t6 1 "runtime.~r0" 0 a8
type t7 8 8 0 0 - "gclinkptr"
name n7 "v" PAUTO t7 1 "runtime.v" 0 a19
name n8 ".autotmp_7" PAUTO t7 1 "runtime..autotmp_7" 0 -
name n9 ".autotmp_8" PAUTO t2 1 "runtime..autotmp_8" 0 -
name n10 "x" PAUTO t6 1 "runtime.x" 0 a20
name n11 "c" PAUTO t1 1 "runtime.c" 0 -
name n12 "s" PAUTO t2 1 "runtime.s" 0 a16
name n13 "spc" PAUTO t3 1 "runtime.spc" 0 -
name n14 "~r0" PAUTO t7 1 "runtime.~r0" 0 a17
name n15 "~r1" PAUTO t2 1 "runtime.~r1" 0 a18
name n16 "size" PAUTO t4 1 "runtime.size" 0 a21
type t8 8 8 8 1 01 "*g"
name n17 "assistG" PAUTO t8 1 "runtime.assistG" 0 a22
in n1 0 used
in n2 8 used
in n3 16 used
in n4 24 used
in n5 32 used
in n6 0 outregs
in n7 0 used
in n8 0 used,autotmp
in n9 0 used,autotmp
in n10 0 used
in n11 0 -
in n12 0 used
in n13 0 -
in n14 0 -
in n15 0 -
in n16 0 used
in n17 0 used
out n1 0 used
out n2 8 used
out n3 16 used
out n4 24 used
out n5 32 used
out n17 -8 used
out n10 -16 used
opt n6 0 outregs
opt n8 0 autotmp
opt n9 0 autotmp
opt n11 0 -
opt n12 0 -
opt n16 0 -
opt n7 0 -
opt n14 0 -
opt n15 0 -
opt n13 0 -
stack 16 16 8
end
genin
posbase p53 "runtime/malloc.go" 1 1 -1 52 "runtime/malloc.go" "runtime/malloc.go" 1 1
sym y1 "runtime.mallocgcSmallNoscanReuse" 1
curfn p53:1462:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2,8194:16:t3,8195:24:t4,8196:32:t5
text y1 0 0 0 0 1462 200080
end
prog0
sym y2 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y3 "gclocals\xc2\xb7uyErKswt9xaZlSJpKX+aCg==" 0
sym y4 "runtime.mallocgcSmallNoscanReuse.arginfo1" 0
sym y5 "runtime.mallocgcSmallNoscanReuse.argliveinfo" 0
sym y6 "runtime.gcBlackenEnabled" 0
sym y7 "runtime.addAssistCredit" 1
inl i7406 - p53:1475:18:0:0 y7 "addAssistCredit"
posbase p7683 "runtime/malloc.go" 1 1 7406 52 "runtime/malloc.go" "runtime/malloc.go" 1 1
sym y8 "runtime.assistG" 0
sym y9 "runtime.x" 0
sym y10 "runtime.span" 0
sym y11 "runtime.memclrNoHeapPointers" 1
sym y12 "runtime.writeBarrier" 0
sym y13 "runtime.gcmarknewobject" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i40 0 0 p53:1462:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p53:1462:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p53:1462:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p53:1462:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p53:1462:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p53:1462:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p53:1466:22:2:0
p 7 7 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p53:1466:22:2:0
p 8 8 0 0 0 - MOVWU 0 MEM/0/0/0/EXTERN/0/0/y6/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p53:1474:22:1:0
p 9 9 0 0 0 - CBZW 0 REG/8194/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@19 0 0 p53:1474:25:2:0
p 10 10 0 0 0 - MOVD 0 MEM/8220/0/0/NONE/0/48/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p7683:1855:12:1:0
p 11 11 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p53:1475:18:1:0
p 12 12 0 0 0 - MOVD 0 MEM/8194/0/0/NONE/0/184/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p7683:1855:14:2:0
p 13 13 0 0 0 - CBNZ 0 REG/8194/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p7683:1855:23:2:0
p 14 14 0 0 0 - MOVD 0 REG/8220/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y8/- 0 0 p7683:1854:17:2:0
p 15 15 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y8/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p7683:1859:24:2:0
p 16 16 0 0 0 - MOVD 0 MEM/8194/0/0/NONE/0/440/-/- 0 - REG/8197/0/0/NONE/0/0/-/- 0 0 p7683:1859:9:1:0
p 17 17 0 0 0 - ADD 0 REG/8195/0/0/NONE/0/0/-/- 8197 - REG/8197/0/0/NONE/0/0/-/- 0 0 p7683:1859:24:2:0
p 18 18 0 0 0 - MOVD 0 REG/8197/0/0/NONE/0/0/-/- 0 - MEM/8194/0/0/NONE/0/440/-/- 0 0 p7683:1859:24:2:0
p 19 19 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-16/y9/- 0 0 p53:1466:22:2:0
p 20 20 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8196 - BRANCH/0/0/0/NONE/0/0/-/@28 0 0 p53:1480:2:2:0
p 21 21 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/8/y10/- 0 0 p53:1474:25:2:0
p 22 22 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/2/-/- 0 0 p53:1474:25:2:0
p 23 23 0 0 0 - MOVD 0 REG/8195/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p53:1481:23:1:0
p 24 24 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p53:1481:23:1:0
p 25 25 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y11/- 0 0 p53:1481:23:1:0
p 26 26 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-16/y9/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p53:1506:2:2:0
p 27 27 0 0 0 - MOVD 0 MEM/8383/0/0/PARAM/0/8/y10/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p53:1504:18:2:0
p 28 28 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p53:1481:23:2:0
p 29 29 0 0 0 - DMB 0 CONST/0/0/0/NONE/0/14/-/- 0 - _ 0 0 p53:1485:20:1:0
p 30 30 0 0 0 - MOVBU 0 MEM/0/0/0/EXTERN/0/0/y12/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p53:1499:17:1:0
p 31 31 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8194 - BRANCH/0/0/0/NONE/0/0/-/@37 0 0 p53:1499:17:2:0
p 32 32 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p53:1504:33:2:0
p 33 33 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p53:1504:18:2:0
p 34 34 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p53:1504:18:2:0
p 35 35 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y13/- 0 0 p53:1504:18:2:0
p 36 36 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-16/y9/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p53:1506:2:2:0
p 37 37 0 0 0 - RET 0 _ 0 - _ 0 0 p53:1506:2:1:0
p 38 38 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 1462 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVB MOVBU
spill MEM/8383/0/0/NONE/0/32/-/- 8195 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVB MOVBU
inlmark @11 7406
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n2 t2 0
dbgslot 1 n4 t4 0
dbgslot 2 n5 t5 0
dbgslot 3 n12 t2 0
dbgslot 4 n14 t7 0
dbgslot 5 n15 t2 0
dbgslot 6 n7 t7 0
dbgslot 7 n10 t6 0
dbgslot 8 n16 t4 0
dbgslot 9 n17 t8 0
dbgslot 10 n1 t1 0
dbgslot 11 n3 t3 0
dbgvar 0 n2 0
dbgvar 1 n4 1
dbgvar 2 n5 2
dbgvar 3 n12 3
dbgvar 4 n7 6
dbgvar 5 n10 7
dbgvar 6 n16 8
dbgvar 7 n17 9
dbgvar 8 n1 10
dbgvar 9 n3 11
dbgloc 0 2:-10000:9:46:51,9:46:8:-10000:9110,8:-10000:11:66:51
dbgloc 1 2:-10000:9:62:53
dbgloc 2 2:-10000:9:62:54
dbgloc 3 2:-10000:9:46:51,9:46:8:-10000:9110,8:-10000:11:66:51
dbgloc 4 2:67:-1:-30000:50
dbgloc 5 2:24:9:62:50,9:62:-1:-30000:9168
dbgloc 6 2:-10000:9:62:53
dbgloc 7 4:33:3:-10000:6c
dbgloc 8 2:-10000:2:67:50
dbgloc 9 2:-10000:2:24:52
dbgregout n6
dbgpc 9:46:24,8:-10000:28,11:66:35,9:62:26,2:67:8,2:24:9,4:33:11,3:-10000:19
end
asm
sym y14 "runtime.morestack_noctxt" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i40 0 0 p53:1462:6:0:0
p 39 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 40 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p53:1462:6:0:0
p 41 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p53:1462:6:0:0
p 42 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@51 0 0 p53:1462:6:0:0
p 43 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p53:1462:6:0:0
p 44 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p53:1462:6:0:1
p 45 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p53:1462:6:0:0
p 46 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p53:1462:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p53:1462:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p53:1462:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p53:1462:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p53:1462:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p53:1466:22:2:0
p 7 24 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p53:1466:22:2:0
p 8 28 0 0 397 - MOVWU 0 MEM/0/0/0/EXTERN/110/0/y6/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p53:1474:22:1:0
p 9 36 0 0 85 - CBZW 0 REG/8194/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/19/-/@19 0 0 p53:1474:25:2:0
p 10 40 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/48/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p7683:1855:12:1:0
p 11 44 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p53:1475:18:1:0
p 12 48 0 0 333 - MOVD 0 MEM/8194/0/0/NONE/87/184/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p7683:1855:14:2:0
p 13 52 0 0 85 - CBNZ 0 REG/8194/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p7683:1855:23:2:0
p 14 56 0 0 304 - MOVD 0 REG/8220/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y8/- 0 0 p7683:1854:17:2:0
p 15 60 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y8/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p7683:1859:24:2:0
p 16 64 0 0 333 - MOVD 0 MEM/8194/0/0/NONE/91/440/-/- 0 - REG/8197/0/0/NONE/2/0/-/- 0 0 p7683:1859:9:1:0
p 17 68 0 0 23 - ADD 0 REG/8195/0/0/NONE/2/0/-/- 8197 - REG/8197/0/0/NONE/2/0/-/- 0 0 p7683:1859:24:2:0
p 18 72 0 0 308 - MOVD 0 REG/8197/0/0/NONE/2/0/-/- 0 - MEM/8194/0/0/NONE/91/440/-/- 0 0 p7683:1859:24:2:0
p 19 76 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/48/-16/y9/- 0 0 p53:1466:22:2:0
p 20 80 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8196 - BRANCH/0/0/0/NONE/36/28/-/@28 0 0 p53:1480:2:2:0
p 21 84 0 0 304 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/47/8/y10/- 0 0 p53:1474:25:2:0
p 22 88 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/2/-/- 0 0 p53:1474:25:2:0
p 23 88 0 0 301 - MOVD 0 REG/8195/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p53:1481:23:1:0
p 24 92 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p53:1481:23:1:0
p 25 92 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y11/- 0 0 p53:1481:23:1:0
p 26 96 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/48/-16/y9/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p53:1506:2:2:0
p 27 100 0 0 329 - MOVD 0 MEM/0/0/0/PARAM/47/8/y10/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p53:1504:18:2:0
p 28 104 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p53:1481:23:2:0
p 29 104 0 0 104 - DMB 0 CONST/0/0/0/NONE/17/14/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p53:1485:20:1:0
p 30 108 0 0 299 - MOVBU 0 MEM/0/0/0/EXTERN/110/0/y12/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p53:1499:17:1:0
p 31 116 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8194 - BRANCH/0/0/0/NONE/36/37/-/@37 0 0 p53:1499:17:2:0
p 32 120 0 0 301 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p53:1504:33:2:0
p 33 124 0 0 301 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p53:1504:18:2:0
p 34 128 0 0 301 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p53:1504:18:2:0
p 35 132 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y13/- 0 0 p53:1504:18:2:0
p 36 136 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/48/-16/y9/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p53:1506:2:2:0
p 37 140 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p53:1506:2:1:0
p 47 144 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p53:1506:2:1:0
p 48 148 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p53:1506:2:1:0
p 49 152 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p53:1506:2:1:0
p 50 152 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p53:1462:6:0:0
p 51 152 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p53:1462:6:0:0
p 52 152 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p53:1462:6:0:0
p 53 156 0 0 282 - MOVB 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/24/-/- 0 0 p53:1462:6:0:0
p 54 160 0 0 308 - MOVD 0 REG/8195/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/86/32/-/- 0 0 p53:1462:6:0:0
p 55 164 0 0 282 - MOVB 0 REG/8196/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/40/-/- 0 0 p53:1462:6:0:0
p 56 168 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 57 172 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y14/- 0 0 p53:1462:6:0:0
p 58 176 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p53:1462:6:0:0
p 59 176 0 0 245 - LDP 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8193/-/- 0 0 p53:1462:6:0:0
p 60 180 0 0 294 - MOVBU 0 MEM/8383/0/0/NONE/87/24/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 61 184 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 62 188 0 0 294 - MOVBU 0 MEM/8383/0/0/NONE/87/40/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p53:1462:6:0:0
p 63 192 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@39 0 0 p53:1462:6:0:0
fn y1 40 40 0 0 1462 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
spill MEM/8383/0/0/NONE/0/24/-/- 8194 0 MOVB MOVBU
spill MEM/8383/0/0/NONE/0/32/-/- 8195 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/40/-/- 8196 0 MOVB MOVBU
inlmark @11 7406
funcaux y2 y3 - - y4 y5 -
text 208 0 900b40f9ff6330eb89040054fe0f1df8fd831ff8fd2300d1e0031faa1b000090620340b942010034821b40f91f2003d5425c40f9620000b5fc1300f9e21340f945dc40f9a500038b45dc00f9e00f00f9c4000036e12300f9e10303aa00000094e00f40f9e12340f9bf3e03d51b00009062034039c2000036e20300aae00301aae10302aa00000094e00f40f9fd835ff8fe0743f8c0035fd6e08700a9e2630039e31300f9e4a30039e3031eaa00000094e08740a9e2634039e31340f9e4a34039d0ffff17000000000000000000000000 5
reloc 28 8 R_ARM64_PCREL_LDST32 0 y6
reloc 92 4 R_CALLARM64 0 y11
reloc 108 8 R_ARM64_PCREL_LDST8 0 y12
reloc 132 4 R_CALLARM64 0 y13
reloc 172 4 R_CALLARM64 0 y14
pcln y19 y20 y21 y22 y15,y16,y17,y18 y2,y3,_,_,_,y4,y5
usedfiles 52
inltree 0 -1 p53:1475:18:0:0 y7 "addAssistCredit" 44
data y2 Sxxx 0 4 8000 0200000000000000 0
data y3 Sxxx 0 4 8000 02000000020000000001 0
data y4 SDATA 11 1 8000 00080808100118082001ff 0
data y5 SDATA 3 1 8000 000002 0
data y15 SRODATA 11 1 28000 0001010202030126020800 0
data y16 SRODATA 7 1 28000 0017040f030e00 0
data y17 SRODATA 0 1 28000 - 0
data y18 SRODATA 9 1 28000 000604100204011a00 0
data y19 SRODATA 7 1 28000 020460215f0f00 0
data y20 SRODATA 3 1 28000 6a3400 0
data y21 SRODATA 44 1 28000 ee160608011003fa0501f70501f8050201010a049106011c010b010e023201030125011c030a040404570e00 0
data y22 SRODATA 11 1 28000 000a020101010207012100 0
end
dwarf
sym y23 "" 0
sym y24 "" 0
sym y25 "" 0
sym y26 "" 0
sym y27 "runtime.(*mcache).nextReusableNoScan" 1
inl i7405 - p53:1465:33:0:0 y27 "(*mcache).nextReusableNoScan"
posbase p7682 "runtime/malloc.go" 1 1 7405 52 "runtime/malloc.go" "runtime/malloc.go" 1 1
sym y28 "go:info.runtime.(*mcache).nextReusableNoScan$abstract" 0
sym y29 "go:info.runtime.addAssistCredit$abstract" 0
sym y30 "go:info.*runtime.mcache" 0
sym y31 "go:info.*runtime.mspan" 0
sym y32 "go:info.runtime.spanClass" 0
sym y33 "go:info.uintptr" 0
sym y34 "go:info.bool" 0
sym y35 "go:info.unsafe.Pointer" 0
sym y36 "go:info.*runtime.g" 0
sym y37 "go:info.runtime.gclinkptr" 0
sym y38 "type:unsafe.Pointer" 0
dwfn y23 y24 y25 - y26 "runtime.mallocgcSmallNoscanReuse" 52:1462 1 0 1 4262
dwdcl n1,n2,n3,n4,n5,n17,n10
dwclosure 0 -
dwparents -
dwparams n1,n2,n3,n4,n5,n6
dwinlfn y27 y28
dwinlfn y7 y29
dwinldcl y27 "c" 0 p53:2028:7:0:0
dwinldcl y27 "s" 0 p53:2028:37:0:0
dwinldcl y27 "spc" 0 p53:2028:47:0:0
dwinldcl y27 "~r0" 0 p53:2028:63:0:0
dwinldcl y27 "~r1" 0 p53:2028:74:0:0
dwinldcl y7 "size" 0 p53:1852:22:0:0
dwinldcl y7 "assistG" 0 p53:1854:2:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.mcache" 0 0 1 p53:1462:31:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "*runtime.mspan" 0 0 1 p53:1462:42:0:0
dwname n3 1 1 0 0 0 0 16 0 - - "runtime.spanClass" 0 0 1 p53:1462:55:0:0
dwname n4 1 1 0 0 0 0 24 0 - - "uintptr" 0 0 1 p53:1462:70:0:0
dwname n5 1 1 0 0 0 0 32 0 - - "bool" 0 0 1 p53:1462:84:0:0
dwname n17 1 1 0 0 1 0 -8 0 - - "*runtime.g" 0 0 1 p7683:1854:2:0:0
dwname n10 1 1 0 0 0 0 -16 0 - - "unsafe.Pointer" 0 0 1 p53:1466:2:0:0
dwname n6 1 0 0 0 0 0 0 1 - - "unsafe.Pointer" 0 0 1 p53:1462:99:0:0
dwname n8 1 0 1 0 0 0 0 0 - - "runtime.gclinkptr" 0 0 1 p53:1465:10:0:0
dwname n9 1 0 1 0 0 0 0 0 - - "*runtime.mspan" 0 0 1 p53:1465:10:0:0
dwname n11 1 0 0 1 0 0 0 0 - - "*runtime.mcache" 0 0 1 p7682:2028:7:0:0
dwname n12 1 0 0 1 0 0 0 0 - - "*runtime.mspan" 0 0 1 p7682:2028:37:0:0
dwname n16 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p7683:1852:22:0:0
dwname n7 1 0 0 0 0 0 0 0 - - "runtime.gclinkptr" 0 0 1 p53:1465:2:0:0
dwname n14 1 0 0 1 0 0 0 0 - - "runtime.gclinkptr" 0 0 1 p7682:2028:63:0:0
dwname n15 1 0 0 1 0 0 0 0 - - "*runtime.mspan" 0 0 1 p7682:2028:74:0:0
dwname n13 1 0 0 1 0 0 0 0 - - "runtime.spanClass" 0 0 1 p7682:2028:47:0:0
var 0 0 "c" 5 1 0 0 0 8 y30 "runtime/malloc.go" 1462 31 0 0 0 0 v8
var 1 0 "span" 5 1 0 0 0 16 y31 "runtime/malloc.go" 1462 42 0 1 0 0 v0
var 2 0 "spc" 5 1 0 0 0 24 y32 "runtime/malloc.go" 1462 55 0 2 0 0 v9
var 3 0 "size" 5 1 0 0 0 32 y33 "runtime/malloc.go" 1462 70 0 3 0 0 v1
var 4 0 "needzero" 5 1 0 0 0 40 y34 "runtime/malloc.go" 1462 84 0 4 0 0 v2
var 5 0 "~r0" 5 1 1 0 0 0 y35 "runtime/malloc.go" 1462 99 0 5 0 0 -
var 6 0 "assistG" 52 1 0 0 0 -16 y36 "runtime/malloc.go" 1854 2 7407 1 1 0 v7
var 7 0 "x" 52 1 0 0 0 -24 y35 "runtime/malloc.go" 1466 2 0 6 0 0 v5
var 8 0 "s" 5 1 0 1 0 -8 y31 "runtime/malloc.go" 2028 37 7406 1 1 0 v3
var 9 0 "v" 52 1 0 0 0 -8 y37 "runtime/malloc.go" 1465 2 0 7 0 0 v4
var 10 0 "size" 5 1 0 1 0 -8 y33 "runtime/malloc.go" 1852 22 7407 0 1 0 v6
scope 0 0 - 0,1,2,3,4,5,6,7,8,9,10
inlcall 0 7406 52:1475 y29 - 1 40:44,48:76 6,10
inlcall 1 7405 52:1465 y28 - 1 - 8
dieref y23 19 y29 0
dieref y23 21 y29 1
data y23 SDWARFFCN 206 0 0 0372756e74696d652e6d616c6c6f636763536d616c6c4e6f7363616e5265757365000000d001019c35000000b60b012d630000b60b00000000000000002d7370616e0000b60b00000000000000002d7370630000b60b00000000000000002d73697a650000b60b00000000000000002d6e6565647a65726f0000b60b00000000000000002e7e72300001b60b0000000000277800ba0b0000000000000000277600b90b000000000000000009000000000000000035000000c30b2900000000000000002300000000000000000000 23
reloc 0 0 R_USETYPE 0 y38
reloc 34 2 R_DWTXTADDR_U2 0 y1
reloc 53 4 R_DWARFSECREF 0 y30
reloc 57 4 R_DWARFSECREF 0 y24
reloc 70 4 R_DWARFSECREF 0 y31
reloc 74 4 R_DWARFSECREF 9 y24
reloc 86 4 R_DWARFSECREF 0 y32
reloc 90 4 R_DWARFSECREF 30 y24
reloc 103 4 R_DWARFSECREF 0 y33
reloc 107 4 R_DWARFSECREF 39 y24
reloc 124 4 R_DWARFSECREF 0 y34
reloc 128 4 R_DWARFSECREF 48 y24
reloc 140 4 R_DWARFSECREF 0 y35
reloc 150 4 R_DWARFSECREF 0 y35
reloc 154 4 R_DWARFSECREF 57 y24
reloc 163 4 R_DWARFSECREF 0 y37
reloc 167 4 R_DWARFSECREF 73 y24
reloc 172 4 R_DWARFSECREF 0 y29
reloc 176 4 R_DWARFSECREF 0 y25
reloc 187 4 R_DWARFSECREF 0 y29
reloc 191 4 R_DWARFSECREF 83 y24
reloc 196 4 R_DWARFSECREF 0 y29
reloc 200 4 R_DWARFSECREF 92 y24
data y24 SDWARFLOC 101 0 0 01000004001c01500001000004005c0151045c680291100468840101510001000004002401520001000004006001530001000004006001540001000004246001500460d00102916800010000041cd001015000010000040060015300010000042c4c016c00 9
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 31 2 R_DWTXTADDR_U2 0 y1
reloc 40 2 R_DWTXTADDR_U2 0 y1
reloc 49 2 R_DWTXTADDR_U2 0 y1
reloc 58 2 R_DWTXTADDR_U2 0 y1
reloc 74 2 R_DWTXTADDR_U2 0 y1
reloc 84 2 R_DWTXTADDR_U2 0 y1
reloc 93 2 R_DWTXTADDR_U2 0 y1
data y25 SDWARFRANGE 10 0 0 01000004282c04304c00 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y26 SDWARFLINES 87 0 0 0009020000000000000000043503b00b140a87068b0603033c065f0603f8023c03887d330603f7023c5e3c0637063703fb7c5b03093c037e330603023c06031464350603713303093c065f3cb106370358830238000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.mallocgcSmallNoscanReuse`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context the checks run on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

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

/-- The index of `v65`'s `DMB $14` among the Progs (`kdOK` checks it). -/
def jD : Nat := 29

/-- A PC table for `b8` with `v65` (index 1) at its `DMB` and `v68` (index 2) after it. -/
def tab : PcTab := [(8, [29, 29, 30])]

/-- Every home past `lc.homes` is none, which `homeOK10` accepts. -/
theorem homeOK10_all {lc : LocCtx} (h : ∀ i, i < lc.homes.size → homeOK10 lc i = true) (i : Nat) :
    homeOK10 lc i = true := by
  by_cases hi : i < lc.homes.size
  · exact h i hi
  · have hh : lc.home i = none := by
      simp only [LocCtx.home]
      rw [getElem?_neg lc.homes i hi]
      rfl
    unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
    rw [hh]
    rfl

def blk : Block := (lc.ctx.f.block? 8).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 256-byte frame with 8 bytes of extra
space, every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 256 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map fun (nc, o) => frameOff L nc o
      else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v65`: every register `poison`, no live slot, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v65`: the activation's `g` and `FP`, the PC of `v65`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 8 1, mem := fun _ => 0 }

/-- The pattern of an accepted single-Prog value. -/
def patOf : Option (Except String VKind2) → Option Pat
  | some (.ok (.prog pat)) => some pat
  | _ => none

theorem patOf_some {o : Option (Except String VKind2)} {pat : Pat} (h : patOf o = some pat) :
    o = some (.ok (.prog pat)) := by
  unfold patOf at h
  split at h
  · cases h; rfl
  · cases h

/-- `vkind57b` accepts `v65` with a pattern the Prog at `jD` matches. -/
def kdOK : Bool := (patOf (vkind57b lc g (val 65))).any fun pat => (ps[jD]?).any pat.ok

/-- What compiled evaluation checks on `runtime.mallocgcSmallNoscanReuse`: it holds an arm64 op;
`checkG55` rejects it (`v65: op DMB`) and `vkind55` rejects `v65`, which `vkind57b` accepts with
the Prog at `jD`; the Progs have distinct IDs below `2^32`; every home is one G10 handles;
`checkFrame` passes; `b8` holds `v65` (`DMB`) at index 1; the function accesses no frame variable;
each home slot's frame operand lies 8 to 4096 bytes above `SP`; `v65` reads no register; and
`stepLoc` runs `v65` from `s0`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG55 lc0 ps bs g).toOption.isNone &&
    (vkind55 lc g (val 65)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.block? 8).isSome && (lc.ctx.f.value? 65).isSome && blk.values[1]? == some 65 &&
    (val 65).op == .ARM64DMB && (accessedVars lc).isEmpty &&
    (homeSlots lc).all (fun k => (g.slotOp k).all fun (nc, o) =>
      decide (8 ≤ frameOff L nc o ∧ frameOff L nc o ≤ 4096)) &&
    (kReads lc (val 65)).isEmpty &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 65)) fun _ => true

theorem g57b2_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (checkG55 lc0 ps bs g).toOption = none ∧
      (vkind55 lc g (val 65)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.block? 8 = some blk ∧ lc.ctx.f.value? 65 = some (val 65) ∧
      blk.values[1]? = some 65 ∧ (val 65).op = .ARM64DMB ∧ (accessedVars lc).isEmpty = true ∧
      (∀ k ∈ homeSlots lc, (g.slotOp k).all (fun (nc, o) =>
        decide (8 ≤ frameOff L nc o ∧ frameOff L nc o ≤ 4096)) = true) ∧
      (kReads lc (val 65)).isEmpty = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 65)) (fun _ => true) = true := by
  have hf := g57b2_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hf
  obtain ⟨hl, h55, h55v, hkd, hlt, hnd, hhome, hcf, hbs, hvs, hi1, hop, hav, hsl, hrd, hrun⟩ := hf
  refine ⟨hl, h55, h55v, hkd, hlt, hnd, homeOK10_all hhome, ?_, ?_, ?_, hi1, hop, hav, hsl, hrd,
    hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-- `vkind57b`'s pattern for `v65` and the Prog at `jD` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind57b lc g (val 65) = some (.ok (.prog pat)) ∧ (ps[jD]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

theorem frameOK57 (hsl : ∀ k ∈ homeSlots lc, (g.slotOp k).all (fun (nc, o) =>
      decide (8 ≤ frameOff L nc o ∧ frameOff L nc o ≤ 4096)) = true) : FrameOK E := by
  refine ⟨by decide, by decide, fun k off h => ?_⟩
  simp only [E] at h
  split at h
  · rename_i hk
    cases ho : g.slotOp k with
    | none => rw [ho] at h; cases h
    | some p =>
      obtain ⟨nc, o⟩ := p
      rw [ho] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have := hsl k hk
      rw [ho] at this
      simp only [Option.all_some, decide_eq_true_eq] at this
      have hsp : GenG2.sp0.toNat = 0x7fff0000 := by decide
      refine ⟨this.1, ?_⟩
      show GenG2.sp0.toNat + _ + 8 ≤ 2 ^ 64
      rw [hsp]
      omega
  · cases h

theorem g57b2Env (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hsl : ∀ k ∈ homeSlots lc, (g.slotOp k).all (fun (nc, o) =>
      decide (8 ≤ frameOff L nc o ∧ frameOff L nc o ≤ 4096)) = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG12.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk nc off ho => by simp [E, hk, ho]
            extra := by show 0 ≤ (8 : Int); decide
            frame := frameOK57 hsl }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

theorem locMatch0 : LocMatch E s0 8 1 m0 where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_replicate] at hv
    split at hv
    · cases hv; exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g57b2Inv0 : G3Inv E lc KMap.bot s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    simp only [s0, Array.getElem?_replicate] at hv
    split at hv
    · cases hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

/-- **G57, group B, on `runtime.mallocgcSmallNoscanReuse`** (`publicationBarrier()` after the
allocation, `DMB $14`): `v65` (`DMB [14] v64`), which `checkG55` rejects (`op DMB`, the function's
only blocker), is rejected by `vkind55` and accepted by `vkind57b`. From `s0`, `stepLoc` runs `v65`
back to `s0` (the memory unchanged, `stepLoc_dmb57`), and `vk57b_step` relates it to a machine run
of its `DMB` to a state related before `v68`, under an activation extending `E` that is again a
`G49Env`. -/
theorem genG57b2_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧ (vkind55 lc g (val 65)).toOption = none ∧
      ∃ E1 m1, stepLoc GenG2.env lc s0 (val 65) = .ok s0 ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s0 8 2 m1 := by
  obtain ⟨hl, h55, h55v, hkd, hlt, hnd, hhome, hcf, -, hv65, -, hop, hav, hsl, hrd, hrun⟩ := facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := g57b2Env hlt hav hsl
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind57b_spec hvk
  have hs10 : s1 = s0 := by
    cases hVK with
    | dmb _ hsz1 hmt hhn hma =>
      obtain ⟨a0, ha0, hamt, hah0⟩ := memArg_spec hma
      exact stepLoc_dmb57 hl htemp hop (arr1 hsz1 ha0) rfl (read_mem hl hah0 hamt rfl) hhn hmt hs1
    | prfm h => rw [hop] at h; cases h
    | store _ h => rw [hop] at h; rcases h with h | h <;> cases h
    | stp _ h => rw [hop] at h; simp [fstpOf] at h
  subst hs10
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jD (jD + 1) :=
    ⟨jD, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h1 (by omega)⟩
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 256 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), GenG12.addrAgree⟩
  have hj : E.pcOf 8 1 = pcAt GenG2.text ps.toList jD := rfl
  have hj' : E.pcOf 8 (1 + 1) = pcAt GenG2.text ps.toList (jD + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk57b_step (H := GenG2.H0) (L := []) (bid := 8)
    (i := 1) (j := jD) (j' := jD + 1) hE F hcf hv65 hVK hvs htemp hj hj'
    (fun rc hrc => by simp [List.isEmpty_iff.1 hrd] at hrc) locMatch0 g57b2Inv0 hs1
  exact ⟨h55, h55v, E1, m1, hs1, hx1, hE1, hp1, hm1⟩

end GoFV.Proof.Witness.GenG57b2
