import GoFV.Proof.Gen.G53
import GoFV.Proof.Witness.GenG49

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG53

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/%28%2AcpuStatsAggregate%29.compute,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*cpuStatsAggregate).compute" 1 0 0
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
type t5 INT64 8 8 0 comparable,named "int64" "int64"
type t4 STRUCT 88 8 0 comparable,named "cpuStats" "runtime.cpuStats" 11
field 0 "GCAssistTime" t5 0 0
field 1 "GCDedicatedTime" t5 8 0
field 2 "GCIdleTime" t5 16 0
field 3 "GCPauseTime" t5 24 0
field 4 "GCTotalTime" t5 32 0
field 5 "ScavengeAssistTime" t5 40 0
field 6 "ScavengeBgTime" t5 48 0
field 7 "ScavengeTotalTime" t5 56 0
field 8 "IdleTime" t5 64 0
field 9 "UserTime" t5 72 0
field 10 "TotalTime" t5 80 0
type t3 STRUCT 88 8 0 comparable,named "cpuStatsAggregate" "runtime.cpuStatsAggregate" 1
field 0 "cpuStats" t4 0 1
type t2 PTR 8 8 8 hasptr,direct,comparable "*cpuStatsAggregate" "*runtime.cpuStatsAggregate" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*cpuStatsAggregate) func()" "method(*runtime.cpuStatsAggregate) func()" 1 0 0
field 0 "a" t2 ? 0
aux a2 sym "runtime.(*cpuStatsAggregate).compute" "runtime.(*cpuStatsAggregate).compute" 1 - 0 - - - - 0
posbase p24 "runtime/metrics.go" 1 1 -1
aux a3 name "a" "a" PPARAM t2 0 1 used p24:747:7:0:0
aux a1 call "AuxCall{runtime.(*cpuStatsAggregate).compute}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t6 BOOL 1 1 0 comparable,named "bool" "bool"
type t7 INT8 1 1 0 comparable,named "int8" "int8"
type t8 INT16 2 2 0 comparable,named "int16" "int16"
type t9 INT32 4 4 0 comparable,named "int32" "int32"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t9
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t23 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t18
type t25 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t27 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t20
type t28 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t29 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t30 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t31 SSA ? ? ? - "mem" ""
type t32 SSA ? ? ? - "flags" ""
type t33 SSA ? ? ? - "void" ""
type t34 SSA 16 8 ? - "int128" ""
type t35 RESULTS ? ? ? - "mem" "" 1 t31
type t36 PTR 8 8 8 hasptr,direct,comparable "**cpuStatsAggregate" "**runtime.cpuStatsAggregate" t2
type t39 UINT64 8 8 0 comparable,named "lfstack" "runtime.lfstack"
type t42 UINT8 1 1 0 comparable,named "byte" "uint8"
type t41 ARRAY 128 1 0 comparable "[128]byte" "[128]uint8" t42 128
type t40 STRUCT 128 1 0 comparable,named "cpu.CacheLinePad" "internal/cpu.CacheLinePad" 1
field 0 "_" t41 0 0
type t45 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t44 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t45 0 1
field 1 "key" t18 0 0
type t48 STRUCT 0 1 0 notinheap,comparable,named "sys.nih" "internal/runtime/sys.nih" 0
type t47 STRUCT 0 1 0 notinheap,comparable,named "sys.NotInHeap" "internal/runtime/sys.NotInHeap" 1
field 0 "_" t48 0 0
type t51 PTR 8 8 0 comparable "*mSpanList" "*runtime.mSpanList" t46
type t52 UINTPTR 8 8 0 comparable,named "gclinkptr" "runtime.gclinkptr"
type t54 STRUCT 1 1 0 notinheap,comparable,named "gcBits" "runtime.gcBits" 2
field 0 "_" t47 0 0
field 1 "x" t10 0 0
type t53 PTR 8 8 0 comparable "*gcBits" "*runtime.gcBits" t54
type t55 UINT8 1 1 0 comparable,named "spanClass" "runtime.spanClass"
type t58 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t57 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t58 0 0
field 1 "value" t10 0 0
type t56 STRUCT 1 1 0 comparable,named "mSpanStateBox" "runtime.mSpanStateBox" 1
field 0 "s" t57 0 0
type t60 STRUCT 24 8 0 notinheap,comparable,named "special" "runtime.special" 4
field 0 "_" t47 0 0
field 1 "next" t59 0 0
field 2 "offset" t18 8 0
field 3 "kind" t42 16 0
type t59 PTR 8 8 0 comparable "*special" "*runtime.special" t60
type t62 STRUCT 8 8 0 comparable,named "offAddr" "runtime.offAddr" 1
field 0 "a" t18 0 0
type t61 STRUCT 16 8 0 comparable,named "addrRange" "runtime.addrRange" 2
field 0 "base" t62 0 0
field 1 "limit" t62 8 0
type t65 UINT8 1 1 0 comparable,named "abi.TFlag" "internal/abi.TFlag"
type t66 UINT8 1 1 0 comparable,named "abi.Kind" "internal/abi.Kind"
type t67 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "" t30 ? 0
field 1 "" t30 ? 0
field 2 "" t6 ? 0
type t68 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t42
type t69 INT32 4 4 0 comparable,named "abi.NameOff" "internal/abi.NameOff"
type t70 INT32 4 4 0 comparable,named "abi.TypeOff" "internal/abi.TypeOff"
type t64 STRUCT 48 8 40 hasptr,named "abi.Type" "internal/abi.Type" 11
field 0 "Size_" t18 0 0
field 1 "PtrBytes" t18 8 0
field 2 "Hash" t12 16 0
field 3 "TFlag" t65 20 0
field 4 "Align_" t10 21 0
field 5 "FieldAlign_" t10 22 0
field 6 "Kind_" t66 23 0
field 7 "Equal" t67 24 0
field 8 "GCData" t68 32 0
field 9 "Str" t69 40 0
field 10 "PtrToThis" t70 44 0
type t63 PTR 8 8 8 hasptr,direct,comparable "*abi.Type" "*internal/abi.Type" t64
type t50 STRUCT 160 8 160 hasptr,notinheap,comparable,named "mspan" "runtime.mspan" 28
field 0 "_" t47 0 0
field 1 "next" t49 0 0
field 2 "prev" t49 8 0
field 3 "list" t51 16 0
field 4 "startAddr" t18 24 0
field 5 "npages" t18 32 0
field 6 "manualFreeList" t52 40 0
field 7 "freeindex" t11 48 0
field 8 "nelems" t11 50 0
field 9 "freeIndexForScan" t11 52 0
field 10 "allocCache" t13 56 0
field 11 "allocBits" t53 64 0
field 12 "gcmarkBits" t53 72 0
field 13 "pinnerBits" t53 80 0
field 14 "sweepgen" t12 88 0
field 15 "divMul" t12 92 0
field 16 "allocCount" t11 96 0
field 17 "spanclass" t55 98 0
field 18 "state" t56 99 0
field 19 "needzero" t10 100 0
field 20 "isUserArenaChunk" t6 101 0
field 21 "allocCountBeforeCache" t11 102 0
field 22 "elemsize" t18 104 0
field 23 "limit" t18 112 0
field 24 "speciallock" t44 120 0
field 25 "specials" t59 128 0
field 26 "userArenaChunkFree" t61 136 0
field 27 "largeType" t63 152 0
type t49 PTR 8 8 0 comparable "*mspan" "*runtime.mspan" t50
type t46 STRUCT 16 8 0 notinheap,comparable,named "mSpanList" "runtime.mSpanList" 3
field 0 "_" t47 0 0
field 1 "first" t49 0 0
field 2 "last" t49 8 0
type t43 STRUCT 40 8 0 notinheap,comparable "struct { lock mutex; free mSpanList; busy mSpanList }" "struct { runtime.lock runtime.mutex; runtime.free runtime.mSpanList; runtime.busy runtime.mSpanList }" 3
field 0 "lock" t44 0 0
field 1 "free" t46 8 0
field 2 "busy" t46 24 0
type t71 SLICE 24 8 8 hasptr,named "pMask" "runtime.pMask" t12
type t73 STRUCT 24 8 0 comparable,named "listHeadManual" "runtime.listHeadManual" 3
field 0 "obj" t18 0 0
field 1 "initialized" t6 8 0
field 2 "nodeOffset" t18 16 0
type t72 STRUCT 32 8 0 comparable "struct { lock mutex; list listHeadManual }" "struct { runtime.lock runtime.mutex; runtime.list runtime.listHeadManual }" 2
field 0 "lock" t44 0 0
field 1 "list" t73 8 0
type t74 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t58 0 0
field 1 "value" t12 0 0
type t76 STRUCT 1 1 0 comparable,named "atomic.Bool" "internal/runtime/atomic.Bool" 1
field 0 "u" t57 0 0
type t75 STRUCT 16 8 0 comparable "struct { pending atomic.Bool; enabled bool; done bool; count int }" "struct { runtime.pending internal/runtime/atomic.Bool; runtime.enabled bool; runtime.done bool; runtime.count int }" 4
field 0 "pending" t76 0 0
field 1 "enabled" t6 1 0
field 2 "done" t6 2 0
field 3 "count" t14 8 0
type t80 STRUCT 16 8 0 comparable,named "stack" "runtime.stack" 2
field 0 "lo" t18 0 0
field 1 "hi" t18 8 0
type t83 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t82 STRUCT 96 8 88 hasptr,comparable,named "_panic" "runtime._panic" 14
field 0 "arg" t83 0 0
field 1 "link" t81 16 0
field 2 "startPC" t18 24 0
field 3 "startSP" t30 32 0
field 4 "pc" t18 40 0
field 5 "sp" t30 48 0
field 6 "fp" t30 56 0
field 7 "retpc" t18 64 0
field 8 "deferBitsPtr" t20 72 0
field 9 "slotsPtr" t30 80 0
field 10 "recovered" t6 88 0
field 11 "repanicked" t6 89 0
field 12 "goexit" t6 90 0
field 13 "deferreturn" t6 91 0
type t81 PTR 8 8 8 hasptr,direct,comparable "*_panic" "*runtime._panic" t82
type t86 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
type t89 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.UnsafePointer" "internal/runtime/atomic.UnsafePointer" 2
field 0 "noCopy" t58 0 0
field 1 "value" t30 0 0
type t88 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime._defer]" "internal/runtime/atomic.Pointer[runtime._defer]" 1
field 0 "u" t89 0 0
type t87 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime._defer]" "*internal/runtime/atomic.Pointer[runtime._defer]" t88
type t85 STRUCT 48 8 48 hasptr,named "_defer" "runtime._defer" 7
field 0 "heap" t6 0 0
field 1 "rangefunc" t6 1 0
field 2 "sp" t18 8 0
field 3 "pc" t18 16 0
field 4 "fn" t86 24 0
field 5 "link" t84 32 0
field 6 "head" t87 40 0
type t84 PTR 8 8 8 hasptr,direct,comparable "*_defer" "*runtime._defer" t85
type t93 UINTPTR 8 8 0 comparable,named "guintptr" "runtime.guintptr"
type t92 STRUCT 48 8 32 hasptr,comparable,named "gobuf" "runtime.gobuf" 6
field 0 "sp" t18 0 0
field 1 "pc" t18 8 0
field 2 "g" t93 16 0
field 3 "ctxt" t30 24 0
field 4 "lr" t18 32 0
field 5 "bp" t18 40 0
type t94 STRUCT 40 8 0 comparable,named "gsignalStack" "runtime.gsignalStack" 4
field 0 "stack" t80 0 0
field 1 "stackguard0" t18 16 0
field 2 "stackguard1" t18 24 0
field 3 "stktopsp" t18 32 0
type t95 ARRAY 8 4 0 comparable,named "sigset" "runtime.sigset" t12 2
type t96 ARRAY 48 8 0 comparable "[6]uintptr" "[6]uintptr" t18 6
type t97 UINTPTR 8 8 0 comparable,named "puintptr" "runtime.puintptr"
type t98 UINT32 4 4 0 comparable,named "throwType" "runtime.throwType"
type t102 STRUCT 24 8 0 comparable,named "sysmontick" "runtime.sysmontick" 4
field 0 "schedtick" t12 0 0
field 1 "syscalltick" t12 4 0
field 2 "schedwhen" t5 8 0
field 3 "syscallwhen" t5 16 0
type t103 UINTPTR 8 8 0 comparable,named "muintptr" "runtime.muintptr"
type t106 ARRAY 1088 8 0 comparable "[136]*mspan" "[136]*runtime.mspan" t49 136
type t107 ARRAY 1088 8 0 comparable "[136]gclinkptr" "[136]runtime.gclinkptr" t52 136
type t109 STRUCT 16 8 0 comparable,named "stackfreelist" "runtime.stackfreelist" 2
field 0 "list" t52 0 0
field 1 "size" t18 8 0
type t108 ARRAY 64 8 0 comparable "[4]stackfreelist" "[4]runtime.stackfreelist" t109 4
type t105 STRUCT 2296 8 0 notinheap,comparable,named "mcache" "runtime.mcache" 11
field 0 "_" t47 0 0
field 1 "nextSample" t5 0 0
field 2 "memProfRate" t14 8 0
field 3 "scanAlloc" t18 16 0
field 4 "tiny" t18 24 0
field 5 "tinyoffset" t18 32 0
field 6 "tinyAllocs" t18 40 0
field 7 "alloc" t106 48 0
field 8 "reusableNoscan" t107 1136 0
field 9 "stackcache" t108 2224 0
field 10 "flushGen" t74 2288 0
type t104 PTR 8 8 0 comparable "*mcache" "*runtime.mcache" t105
type t110 STRUCT 24 8 0 comparable,named "pageCache" "runtime.pageCache" 3
field 0 "base" t18 0 0
field 1 "cache" t13 8 0
field 2 "scav" t13 16 0
type t113 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime.m]" "internal/runtime/atomic.Pointer[runtime.m]" 1
field 0 "u" t89 0 0
type t112 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime.m]" "*internal/runtime/atomic.Pointer[runtime.m]" t113
type t111 STRUCT 8 8 8 hasptr,direct,comparable,named "mWeakPointer" "runtime.mWeakPointer" 1
field 0 "m" t112 0 0
type t114 SLICE 24 8 8 hasptr "[]*_defer" "[]*runtime._defer" t84
type t115 ARRAY 256 8 256 hasptr,comparable "[32]*_defer" "[32]*runtime._defer" t84 32
type t116 ARRAY 2048 8 0 comparable "[256]guintptr" "[256]runtime.guintptr" t93 256
type t117 STRUCT 16 8 0 comparable,named "gList" "runtime.gList" 2
field 0 "head" t93 0 0
field 1 "size" t9 8 0
type t121 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceablePtr" "runtime.maybeTraceablePtr" 2
field 0 "vp" t30 0 0
field 1 "vu" t18 8 0
type t122 STRUCT 16 8 8 hasptr,comparable,named "maybeTraceableChan" "runtime.maybeTraceableChan" 1
field 0 "maybeTraceablePtr" t121 0 1
type t120 STRUCT 104 8 96 hasptr,comparable,named "sudog" "runtime.sudog" 14
field 0 "g" t78 0 0
field 1 "next" t119 8 0
field 2 "prev" t119 16 0
field 3 "elem" t121 24 0
field 4 "acquiretime" t5 40 0
field 5 "releasetime" t5 48 0
field 6 "ticket" t12 56 0
field 7 "isSelect" t6 60 0
field 8 "success" t6 61 0
field 9 "waiters" t11 62 0
field 10 "parent" t119 64 0
field 11 "waitlink" t119 72 0
field 12 "waittail" t119 80 0
field 13 "c" t122 88 0
type t119 PTR 8 8 8 hasptr,direct,comparable "*sudog" "*runtime.sudog" t120
type t118 SLICE 24 8 8 hasptr "[]*sudog" "[]*runtime.sudog" t119
type t123 ARRAY 1024 8 1024 hasptr,comparable "[128]*sudog" "[128]*runtime.sudog" t119 128
type t125 ARRAY 1024 8 0 comparable "[128]*mspan" "[128]*runtime.mspan" t49 128
type t124 STRUCT 1032 8 0 comparable "struct { len int; buf [128]*mspan }" "struct { runtime.len int; runtime.buf [128]*runtime.mspan }" 2
field 0 "len" t14 0 0
field 1 "buf" t125 8 0
type t128 SLICE 24 8 8 hasptr "[]unsafe.Pointer" "[]unsafe.Pointer" t30
type t129 ARRAY 40 8 40 hasptr,comparable "[5]unsafe.Pointer" "[5]unsafe.Pointer" t30 5
type t127 STRUCT 64 8 64 hasptr,named "pinner" "runtime.pinner" 2
field 0 "refs" t128 0 0
field 1 "refStore" t129 24 0
type t126 PTR 8 8 8 hasptr,direct,comparable "*pinner" "*runtime.pinner" t127
type t132 ARRAY 12 4 0 comparable "[3]atomic.Uint32" "[3]internal/runtime/atomic.Uint32" t74 3
type t133 ARRAY 16 8 0 comparable "[2]uint64" "[2]uint64" t13 2
type t131 STRUCT 32 8 0 comparable,named "traceSchedResourceState" "runtime.traceSchedResourceState" 2
field 0 "statusTraced" t132 0 0
field 1 "seq" t133 16 0
type t130 STRUCT 64 8 0 comparable,named "pTraceState" "runtime.pTraceState" 6
field 0 "traceSchedResourceState" t131 0 1
field 1 "mSyscallID" t5 32 0
field 2 "maySweep" t6 40 0
field 3 "inSweep" t6 41 0
field 4 "swept" t18 48 0
field 5 "reclaimed" t18 56 0
type t136 STRUCT 0 1 0 notinheap,comparable,named "notInHeap" "runtime.notInHeap" 1
field 0 "_" t47 0 0
type t135 PTR 8 8 0 comparable "*notInHeap" "*runtime.notInHeap" t136
type t134 STRUCT 16 8 0 comparable,named "persistentAlloc" "runtime.persistentAlloc" 2
field 0 "base" t135 0 0
field 1 "off" t18 8 0
type t138 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t137 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t58 0 0
field 1 "_" t138 0 0
field 2 "value" t5 0 0
type t140 STRUCT 8 8 0 comparable,named "atomic.Uint64" "internal/runtime/atomic.Uint64" 3
field 0 "noCopy" t58 0 0
field 1 "_" t138 0 0
field 2 "value" t13 0 0
type t139 STRUCT 8 8 0 comparable,named "limiterEvent" "runtime.limiterEvent" 1
field 0 "stamp" t140 0 0
type t141 INT 8 8 0 comparable,named "gcMarkWorkerMode" "runtime.gcMarkWorkerMode"
type t144 STRUCT 16 8 0 comparable,named "lfnode" "runtime.lfnode" 2
field 0 "next" t13 0 0
field 1 "pushcnt" t18 8 0
type t143 STRUCT 32 8 0 comparable,named "gcBgMarkWorkerNode" "runtime.gcBgMarkWorkerNode" 3
field 0 "node" t144 0 0
field 1 "gp" t93 16 0
field 2 "m" t103 24 0
type t142 PTR 8 8 8 hasptr,direct,comparable "*gcBgMarkWorkerNode" "*runtime.gcBgMarkWorkerNode" t143
type t148 STRUCT 24 8 0 comparable,named "workbufhdr" "runtime.workbufhdr" 2
field 0 "node" t144 0 0
field 1 "nobj" t14 16 0
type t149 ARRAY 2024 8 0 comparable "[253]uintptr" "[253]uintptr" t18 253
type t147 STRUCT 2048 8 0 notinheap,comparable,named "workbuf" "runtime.workbuf" 3
field 0 "_" t47 0 0
field 1 "workbufhdr" t148 0 1
field 2 "obj" t149 24 0
type t146 PTR 8 8 0 comparable "*workbuf" "*runtime.workbuf" t147
type t152 UINTPTR 8 8 0 comparable,named "objptr" "runtime.objptr"
type t151 ARRAY 2048 8 0 comparable "[256]objptr" "[256]runtime.objptr" t152 256
type t156 STRUCT 16 8 0 comparable,named "listNodeManual" "runtime.listNodeManual" 2
field 0 "prev" t18 0 0
field 1 "next" t18 8 0
type t157 PTR 8 8 8 hasptr,direct,comparable "*objptr" "*runtime.objptr" t152
type t155 STRUCT 56 8 56 hasptr,notinheap,comparable,named "spanSPMC" "runtime.spanSPMC" 8
field 0 "_" t47 0 0
field 1 "allnode" t156 0 0
field 2 "dead" t76 16 0
field 3 "prev" t89 24 0
field 4 "head" t74 32 0
field 5 "tail" t74 36 0
field 6 "cap" t12 40 0
field 7 "ring" t157 48 0
type t154 PTR 8 8 0 comparable "*spanSPMC" "*runtime.spanSPMC" t155
type t153 STRUCT 16 8 16 hasptr,comparable "struct { head *spanSPMC; tail atomic.UnsafePointer }" "struct { runtime.head *runtime.spanSPMC; runtime.tail internal/runtime/atomic.UnsafePointer }" 2
field 0 "head" t154 0 0
field 1 "tail" t89 8 0
type t150 STRUCT 2080 8 2080 hasptr,comparable,named "spanQueue" "runtime.spanQueue" 5
field 0 "head" t12 0 0
field 1 "tail" t12 4 0
field 2 "ring" t151 8 0
field 3 "putsSinceDrain" t14 2056 0
field 4 "chain" t153 2064 0
type t159 ARRAY 8192 8 0 comparable "[1024]uintptr" "[1024]uintptr" t18 1024
type t158 PTR 8 8 8 hasptr,direct,comparable "*[1024]uintptr" "*[1024]uintptr" t159
type t161 STRUCT 40 8 0 comparable,named "sizeClassScanStats" "runtime.sizeClassScanStats" 5
field 0 "spansDenseScanned" t13 0 0
field 1 "spanObjsDenseScanned" t13 8 0
field 2 "spansSparseScanned" t13 16 0
field 3 "spanObjsSparseScanned" t13 24 0
field 4 "sparseObjsScanned" t13 32 0
type t160 ARRAY 2720 8 0 comparable "[68]sizeClassScanStats" "[68]runtime.sizeClassScanStats" t161 68
type t145 STRUCT 4856 8 2112 hasptr,comparable,named "gcWork" "runtime.gcWork" 10
field 0 "id" t9 0 0
field 1 "wbuf1" t146 8 0
field 2 "wbuf2" t146 16 0
field 3 "spanq" t150 24 0
field 4 "ptrBuf" t158 2104 0
field 5 "bytesMarked" t13 2112 0
field 6 "heapScanWork" t5 2120 0
field 7 "flushedWork" t6 2128 0
field 8 "mayNeedWorker" t6 2129 0
field 9 "stats" t160 2136 0
type t163 ARRAY 4096 8 0 comparable "[512]uintptr" "[512]uintptr" t18 512
type t162 STRUCT 4112 8 0 comparable,named "wbBuf" "runtime.wbBuf" 3
field 0 "next" t18 0 0
field 1 "end" t18 8 0
field 2 "buf" t163 16 0
type t169 FUNC 8 8 8 hasptr,direct "func(any, uintptr, int64)" "func(interface {}, uintptr, int64)" 0 3 0
field 0 "arg" t83 ? 0
field 1 "seq" t18 ? 0
field 2 "delay" t5 ? 0
type t170 PTR 8 8 8 hasptr,direct,comparable "*timers" "*runtime.timers" t164
type t171 STRUCT 4 4 0 comparable,named "atomic.Int32" "internal/runtime/atomic.Int32" 2
field 0 "noCopy" t58 0 0
field 1 "value" t9 0 0
type t168 STRUCT 96 8 80 hasptr,named "timer" "runtime.timer" 15
field 0 "mu" t44 0 0
field 1 "astate" t57 8 0
field 2 "state" t10 9 0
field 3 "isChan" t6 10 0
field 4 "isFake" t6 11 0
field 5 "blocked" t12 12 0
field 6 "rand" t12 16 0
field 7 "when" t5 24 0
field 8 "period" t5 32 0
field 9 "f" t169 40 0
field 10 "arg" t83 48 0
field 11 "seq" t18 64 0
field 12 "ts" t170 72 0
field 13 "sendLock" t44 80 0
field 14 "isSending" t171 88 0
type t167 PTR 8 8 8 hasptr,direct,comparable "*timer" "*runtime.timer" t168
type t166 STRUCT 16 8 8 hasptr,comparable,named "timerWhen" "runtime.timerWhen" 2
field 0 "timer" t167 0 0
field 1 "when" t5 8 0
type t165 SLICE 24 8 8 hasptr "[]timerWhen" "[]runtime.timerWhen" t166
type t164 STRUCT 64 8 16 hasptr,named "timers" "runtime.timers" 7
field 0 "mu" t44 0 0
field 1 "heap" t165 8 0
field 2 "len" t74 32 0
field 3 "zombies" t171 36 0
field 4 "raceCtx" t18 40 0
field 5 "minWhenHeap" t137 48 0
field 6 "minWhenModified" t137 56 0
type t174 STRUCT 32 8 0 notinheap,comparable,named "cleanupBlockHeader" "runtime.cleanupBlockHeader" 4
field 0 "_" t47 0 0
field 1 "lfnode" t144 0 1
field 2 "alllink" t172 16 0
field 3 "n" t12 24 0
type t179 STRUCT 8 8 0 comparable,named "funcval" "runtime.funcval" 1
field 0 "fn" t18 0 0
type t178 PTR 8 8 8 hasptr,direct,comparable "*funcval" "*runtime.funcval" t179
type t177 FUNC 8 8 8 hasptr,direct "func(*funcval, unsafe.Pointer)" "func(*runtime.funcval, unsafe.Pointer)" 0 2 0
field 0 "" t178 ? 0
field 1 "" t30 ? 0
type t176 STRUCT 24 8 24 hasptr,named "cleanupFn" "runtime.cleanupFn" 3
field 0 "call" t177 0 0
field 1 "fn" t178 8 0
field 2 "arg" t30 16 0
type t175 ARRAY 480 8 480 hasptr "[20]cleanupFn" "[20]runtime.cleanupFn" t176 20
type t173 STRUCT 512 8 512 hasptr,notinheap,named "cleanupBlock" "runtime.cleanupBlock" 2
field 0 "cleanupBlockHeader" t174 0 1
field 1 "cleanups" t175 32 0
type t172 PTR 8 8 0 comparable "*cleanupBlock" "*runtime.cleanupBlock" t173
type t182 ARRAY 16 1 0 comparable "[16]byte" "[16]uint8" t42 16
type t181 STRUCT 512 1 0 comparable,named "xRegs" "runtime.xRegs" 32
field 0 "V0" t182 0 0
field 1 "V1" t182 16 0
field 2 "V2" t182 32 0
field 3 "V3" t182 48 0
field 4 "V4" t182 64 0
field 5 "V5" t182 80 0
field 6 "V6" t182 96 0
field 7 "V7" t182 112 0
field 8 "V8" t182 128 0
field 9 "V9" t182 144 0
field 10 "V10" t182 160 0
field 11 "V11" t182 176 0
field 12 "V12" t182 192 0
field 13 "V13" t182 208 0
field 14 "V14" t182 224 0
field 15 "V15" t182 240 0
field 16 "V16" t182 256 0
field 17 "V17" t182 272 0
field 18 "V18" t182 288 0
field 19 "V19" t182 304 0
field 20 "V20" t182 320 0
field 21 "V21" t182 336 0
field 22 "V22" t182 352 0
field 23 "V23" t182 368 0
field 24 "V24" t182 384 0
field 25 "V25" t182 400 0
field 26 "V26" t182 416 0
field 27 "V27" t182 432 0
field 28 "V28" t182 448 0
field 29 "V29" t182 464 0
field 30 "V30" t182 480 0
field 31 "V31" t182 496 0
type t184 STRUCT 512 1 0 notinheap,comparable,named "xRegState" "runtime.xRegState" 2
field 0 "_" t47 0 0
field 1 "regs" t181 0 0
type t183 PTR 8 8 0 comparable "*xRegState" "*runtime.xRegState" t184
type t180 STRUCT 520 8 0 comparable,named "xRegPerP" "runtime.xRegPerP" 2
field 0 "scratch" t181 0 0
field 1 "cache" t183 512 0
type t101 STRUCT 14320 8 13688 hasptr,named "p" "runtime.p" 46
field 0 "id" t9 0 0
field 1 "status" t12 4 0
field 2 "link" t97 8 0
field 3 "schedtick" t12 16 0
field 4 "syscalltick" t12 20 0
field 5 "sysmontick" t102 24 0
field 6 "m" t103 48 0
field 7 "mcache" t104 56 0
field 8 "pcache" t110 64 0
field 9 "raceprocctx" t18 88 0
field 10 "oldm" t111 96 0
field 11 "deferpool" t114 104 0
field 12 "deferpoolbuf" t115 128 0
field 13 "goidcache" t13 384 0
field 14 "goidcacheend" t13 392 0
field 15 "runqhead" t12 400 0
field 16 "runqtail" t12 404 0
field 17 "runq" t116 408 0
field 18 "runnext" t93 2456 0
field 19 "gFree" t117 2464 0
field 20 "sudogcache" t118 2480 0
field 21 "sudogbuf" t123 2504 0
field 22 "mspancache" t124 3528 0
field 23 "pinnerCache" t126 4560 0
field 24 "trace" t130 4568 0
field 25 "palloc" t134 4632 0
field 26 "gcAssistTime" t5 4648 0
field 27 "gcFractionalMarkTime" t137 4656 0
field 28 "limiterEvent" t139 4664 0
field 29 "gcMarkWorkerMode" t141 4672 0
field 30 "gcMarkWorkerStartTime" t5 4680 0
field 31 "nextGCMarkWorker" t142 4688 0
field 32 "gcw" t145 4696 0
field 33 "wbBuf" t162 9552 0
field 34 "runSafePointFn" t12 13664 0
field 35 "statsSeq" t74 13668 0
field 36 "timers" t164 13672 0
field 37 "cleanups" t172 13736 0
field 38 "cleanupsQueued" t13 13744 0
field 39 "maxStackScanDelta" t5 13752 0
field 40 "scannedStackSize" t13 13760 0
field 41 "scannedStacks" t13 13768 0
field 42 "preempt" t6 13776 0
field 43 "gcStopTime" t5 13784 0
field 44 "goroutinesCreated" t13 13792 0
field 45 "xRegs" t180 13800 0
type t100 PTR 8 8 8 hasptr,direct,comparable "*p" "*runtime.p" t101
type t99 SLICE 24 8 8 hasptr "[]*p" "[]*runtime.p" t100
type t186 ARRAY 256 8 0 comparable,named "cgoCallers" "runtime.cgoCallers" t18 32
type t185 PTR 8 8 8 hasptr,direct,comparable "*cgoCallers" "*runtime.cgoCallers" t186
type t187 STRUCT 8 8 0 comparable,named "note" "runtime.note" 1
field 0 "key" t18 0 0
type t188 ARRAY 256 8 0 comparable "[32]uintptr" "[32]uintptr" t18 32
type t189 STRUCT 16 8 0 comparable,named "mWaitList" "runtime.mWaitList" 2
field 0 "next" t103 0 0
field 1 "startTicks" t5 8 0
type t191 SLICE 24 8 8 hasptr "[]uintptr" "[]uintptr" t18
type t190 STRUCT 56 8 16 hasptr,named "mLockProfile" "runtime.mLockProfile" 6
field 0 "waitTime" t137 0 0
field 1 "stack" t191 8 0
field 2 "cycles" t5 32 0
field 3 "cyclesLost" t5 40 0
field 4 "haveStack" t6 48 0
field 5 "disabled" t6 49 0
type t192 FUNC 8 8 8 hasptr,direct "func(*g, unsafe.Pointer) bool" "func(*runtime.g, unsafe.Pointer) bool" 0 2 1
field 0 "" t78 ? 0
field 1 "" t30 ? 0
field 2 "" t6 ? 0
type t193 UINT8 1 1 0 comparable,named "traceBlockReason" "runtime.traceBlockReason"
type t200 UINT64 8 8 0 comparable,named "traceTime" "runtime.traceTime"
type t199 STRUCT 32 8 0 comparable,named "traceBufHeader" "runtime.traceBufHeader" 4
field 0 "link" t197 0 0
field 1 "lastTime" t200 8 0
field 2 "pos" t14 16 0
field 3 "lenPos" t14 24 0
type t201 ARRAY 65504 1 0 comparable "[65504]byte" "[65504]uint8" t42 65504
type t198 STRUCT 65536 8 0 notinheap,comparable,named "traceBuf" "runtime.traceBuf" 3
field 0 "_" t47 0 0
field 1 "traceBufHeader" t199 0 1
field 2 "arr" t201 32 0
type t197 PTR 8 8 0 comparable "*traceBuf" "*runtime.traceBuf" t198
type t196 ARRAY 16 8 0 comparable "[2]*traceBuf" "[2]*runtime.traceBuf" t197 2
type t195 ARRAY 32 8 0 comparable "[2][2]*traceBuf" "[2][2]*runtime.traceBuf" t196 2
type t194 STRUCT 72 8 48 hasptr,comparable,named "mTraceState" "runtime.mTraceState" 6
field 0 "writing" t76 0 0
field 1 "buf" t195 8 0
field 2 "link" t90 40 0
field 3 "reentered" t12 48 0
field 4 "entryGen" t18 56 0
field 5 "oldthrowsplit" t6 64 0
type t202 STRUCT 0 1 0 comparable,named "winlibcall" "runtime.winlibcall" 0
type t206 STRUCT 24 8 0 comparable,named "pcvalueCacheEnt" "runtime.pcvalueCacheEnt" 4
field 0 "targetpc" t18 0 0
field 1 "off" t12 8 0
field 2 "val" t9 12 0
field 3 "valPC" t18 16 0
type t205 ARRAY 192 8 0 comparable "[8]pcvalueCacheEnt" "[8]runtime.pcvalueCacheEnt" t206 8
type t204 ARRAY 384 8 0 comparable "[2][8]pcvalueCacheEnt" "[2][8]runtime.pcvalueCacheEnt" t205 2
type t203 STRUCT 392 8 0 comparable,named "pcvalueCache" "runtime.pcvalueCache" 2
field 0 "entries" t204 0 0
field 1 "inUse" t14 384 0
type t207 STRUCT 0 1 0 comparable,named "dlogPerM" "runtime.dlogPerM" 0
type t208 STRUCT 24 8 0 comparable,named "mOS" "runtime.mOS" 5
field 0 "profileTimer" t9 0 0
field 1 "profileTimerValid" t76 4 0
field 2 "needPerThreadSyscall" t57 5 0
field 3 "vgetrandomState" t18 8 0
field 4 "waitsema" t12 16 0
type t210 ARRAY 256 8 0 comparable "[32]uint64" "[32]uint64" t13 32
type t211 ARRAY 32 8 0 comparable "[4]uint64" "[4]uint64" t13 4
type t209 STRUCT 304 8 0 comparable,named "chacha8rand.State" "internal/chacha8rand.State" 5
field 0 "buf" t210 0 0
field 1 "seed" t211 256 0
field 2 "i" t12 288 0
field 3 "n" t12 292 0
field 4 "c" t12 296 0
type t214 INT64 8 8 0 comparable,named "lockRank" "runtime.lockRank"
type t213 STRUCT 16 8 0 comparable,named "heldLockInfo" "runtime.heldLockInfo" 2
field 0 "lockAddr" t18 0 0
field 1 "rank" t214 8 0
type t212 ARRAY 160 8 0 comparable "[10]heldLockInfo" "[10]runtime.heldLockInfo" t213 10
type t91 STRUCT 1832 8 1832 hasptr,named "m" "runtime.m" 75
field 0 "g0" t78 0 0
field 1 "morebuf" t92 8 0
field 2 "divmod" t12 56 0
field 3 "procid" t13 64 0
field 4 "gsignal" t78 72 0
field 5 "goSigStack" t94 80 0
field 6 "sigmask" t95 120 0
field 7 "tls" t96 128 0
field 8 "mstartfn" t86 176 0
field 9 "curg" t78 184 0
field 10 "caughtsig" t93 192 0
field 11 "signalSecret" t6 200 0
field 12 "p" t97 208 0
field 13 "nextp" t97 216 0
field 14 "oldp" t97 224 0
field 15 "id" t5 232 0
field 16 "mallocing" t9 240 0
field 17 "throwing" t98 244 0
field 18 "preemptoff" t19 248 0
field 19 "locks" t9 264 0
field 20 "dying" t9 268 0
field 21 "profilehz" t9 272 0
field 22 "spinning" t6 276 0
field 23 "blocked" t6 277 0
field 24 "newSigstack" t6 278 0
field 25 "printlock" t7 279 0
field 26 "incgo" t6 280 0
field 27 "isextra" t6 281 0
field 28 "isExtraInC" t6 282 0
field 29 "isExtraInSig" t6 283 0
field 30 "freeWait" t74 284 0
field 31 "needextram" t6 288 0
field 32 "g0StackAccurate" t6 289 0
field 33 "traceback" t10 290 0
field 34 "allpSnapshot" t99 296 0
field 35 "ncgocall" t13 320 0
field 36 "ncgo" t9 328 0
field 37 "cgoCallersUse" t74 332 0
field 38 "cgoCallers" t185 336 0
field 39 "park" t187 344 0
field 40 "alllink" t90 352 0
field 41 "schedlink" t103 360 0
field 42 "idleNode" t156 368 0
field 43 "lockedg" t93 384 0
field 44 "createstack" t188 392 0
field 45 "lockedExt" t12 648 0
field 46 "lockedInt" t12 652 0
field 47 "mWaitList" t189 656 0
field 48 "ditEnabled" t6 672 0
field 49 "mLockProfile" t190 680 0
field 50 "profStack" t191 736 0
field 51 "waitunlockf" t192 760 0
field 52 "waitlock" t30 768 0
field 53 "waitTraceSkip" t14 776 0
field 54 "waitTraceBlockReason" t193 784 0
field 55 "syscalltick" t12 788 0
field 56 "freelink" t90 792 0
field 57 "trace" t194 800 0
field 58 "libcallpc" t18 872 0
field 59 "libcallsp" t18 880 0
field 60 "libcallg" t93 888 0
field 61 "winsyscall" t202 896 0
field 62 "vdsoSP" t18 896 0
field 63 "vdsoPC" t18 904 0
field 64 "preemptGen" t74 912 0
field 65 "signalPending" t74 916 0
field 66 "pcvalueCache" t203 920 0
field 67 "dlogPerM" t207 1312 1
field 68 "mOS" t208 1312 1
field 69 "chacha8" t209 1336 0
field 70 "cheaprand" t12 1640 0
field 71 "cheaprand64" t13 1648 0
field 72 "locksHeldLen" t14 1656 0
field 73 "locksHeld" t212 1664 0
field 74 "self" t111 1824 0
type t90 PTR 8 8 8 hasptr,direct,comparable "*m" "*runtime.m" t91
type t215 UINT8 1 1 0 comparable,named "waitReason" "runtime.waitReason"
type t216 SLICE 24 8 8 hasptr "[]byte" "[]uint8" t42
type t219 STRUCT 40 8 8 hasptr,named "ancestorInfo" "runtime.ancestorInfo" 3
field 0 "pcs" t191 0 0
field 1 "goid" t13 24 0
field 2 "gopc" t18 32 0
type t218 SLICE 24 8 8 hasptr "[]ancestorInfo" "[]runtime.ancestorInfo" t219
type t217 PTR 8 8 8 hasptr,direct,comparable "*[]ancestorInfo" "*[]runtime.ancestorInfo" t218
type t220 STRUCT 4 4 0 comparable,named "goroutineProfileStateHolder" "runtime.goroutineProfileStateHolder" 2
field 0 "noCopy" t58 0 0
field 1 "value" t12 0 0
type t223 FUNC 8 8 8 hasptr,direct "func(*coro)" "func(*runtime.coro)" 0 1 0
field 0 "" t221 ? 0
type t222 STRUCT 32 8 24 hasptr,named "coro" "runtime.coro" 5
field 0 "gp" t93 0 0
field 1 "f" t223 8 0
field 2 "mp" t90 16 0
field 3 "lockedExt" t12 24 0
field 4 "lockedInt" t12 28 0
type t221 PTR 8 8 8 hasptr,direct,comparable "*coro" "*runtime.coro" t222
type t225 STRUCT 144 8 112 hasptr,named "synctestBubble" "runtime.synctestBubble" 12
field 0 "mu" t44 0 0
field 1 "timers" t164 8 0
field 2 "id" t13 72 0
field 3 "now" t5 80 0
field 4 "root" t78 88 0
field 5 "waiter" t78 96 0
field 6 "main" t78 104 0
field 7 "waiting" t6 112 0
field 8 "done" t6 113 0
field 9 "total" t14 120 0
field 10 "running" t14 128 0
field 11 "active" t14 136 0
type t224 PTR 8 8 8 hasptr,direct,comparable "*synctestBubble" "*runtime.synctestBubble" t225
type t226 STRUCT 8 8 0 comparable,named "xRegPerG" "runtime.xRegPerG" 1
field 0 "state" t183 0 0
type t227 STRUCT 32 8 0 comparable,named "gTraceState" "runtime.gTraceState" 1
field 0 "traceSchedResourceState" t131 0 1
type t79 STRUCT 456 8 400 hasptr,named "g" "runtime.g" 65
field 0 "stack" t80 0 0
field 1 "stackguard0" t18 16 0
field 2 "stackguard1" t18 24 0
field 3 "_panic" t81 32 0
field 4 "_defer" t84 40 0
field 5 "m" t90 48 0
field 6 "sched" t92 56 0
field 7 "syscallsp" t18 104 0
field 8 "syscallpc" t18 112 0
field 9 "syscallbp" t18 120 0
field 10 "stktopsp" t18 128 0
field 11 "param" t30 136 0
field 12 "atomicstatus" t74 144 0
field 13 "stackLock" t12 148 0
field 14 "goid" t13 152 0
field 15 "schedlink" t93 160 0
field 16 "waitsince" t5 168 0
field 17 "waitreason" t215 176 0
field 18 "preempt" t6 177 0
field 19 "preemptStop" t6 178 0
field 20 "preemptShrink" t6 179 0
field 21 "asyncSafePoint" t6 180 0
field 22 "paniconfault" t6 181 0
field 23 "gcscandone" t6 182 0
field 24 "throwsplit" t6 183 0
field 25 "activeStackChans" t6 184 0
field 26 "parkingOnChan" t76 185 0
field 27 "inMarkAssist" t6 186 0
field 28 "coroexit" t6 187 0
field 29 "raceignore" t7 188 0
field 30 "nocgocallback" t6 189 0
field 31 "tracking" t6 190 0
field 32 "trackingSeq" t10 191 0
field 33 "trackingStamp" t5 192 0
field 34 "runnableTime" t5 200 0
field 35 "lockedm" t103 208 0
field 36 "fipsIndicator" t10 216 0
field 37 "fipsOnlyBypass" t6 217 0
field 38 "ditWanted" t6 218 0
field 39 "syncSafePoint" t6 219 0
field 40 "runningCleanups" t76 220 0
field 41 "sig" t12 224 0
field 42 "secret" t9 228 0
field 43 "writebuf" t216 232 0
field 44 "sigcode0" t18 256 0
field 45 "sigcode1" t18 264 0
field 46 "sigpc" t18 272 0
field 47 "parentGoid" t13 280 0
field 48 "gopc" t18 288 0
field 49 "ancestors" t217 296 0
field 50 "startpc" t18 304 0
field 51 "racectx" t18 312 0
field 52 "waiting" t119 320 0
field 53 "cgoCtxt" t191 328 0
field 54 "labels" t30 352 0
field 55 "timer" t167 360 0
field 56 "sleepWhen" t5 368 0
field 57 "selectDone" t74 376 0
field 58 "goroutineProfiled" t220 380 0
field 59 "coroarg" t221 384 0
field 60 "bubble" t224 392 0
field 61 "xRegs" t226 400 0
field 62 "trace" t227 408 0
field 63 "gcAssistBytes" t5 440 0
field 64 "valgrindStackID" t18 448 0
type t78 PTR 8 8 8 hasptr,direct,comparable "*g" "*runtime.g" t79
type t77 SLICE 24 8 8 hasptr "[]*g" "[]*runtime.g" t78
type t228 INT 8 8 0 comparable,named "gcMode" "runtime.gcMode"
type t230 STRUCT 24 8 0 comparable,named "gQueue" "runtime.gQueue" 3
field 0 "head" t93 0 0
field 1 "tail" t93 8 0
field 2 "size" t9 16 0
type t229 STRUCT 32 8 0 comparable "struct { lock mutex; q gQueue }" "struct { runtime.lock runtime.mutex; runtime.q runtime.gQueue }" 2
field 0 "lock" t44 0 0
field 1 "q" t230 8 0
type t231 STRUCT 24 8 0 comparable "struct { lock mutex; list gList }" "struct { runtime.lock runtime.mutex; runtime.list runtime.gList }" 2
field 0 "lock" t44 0 0
field 1 "list" t117 8 0
type t232 STRUCT 40 8 0 comparable "struct { block bool; lock mutex; q gQueue }" "struct { runtime.block bool; runtime.lock runtime.mutex; runtime.q runtime.gQueue }" 3
field 0 "block" t6 0 0
field 1 "lock" t44 8 0
field 2 "q" t230 16 0
type t38 STRUCT 1072 8 752 hasptr,notinheap,named "workType" "runtime.workType" 48
field 0 "full" t39 0 0
field 1 "_" t40 8 0
field 2 "empty" t39 136 0
field 3 "_" t40 144 0
field 4 "wbufSpans" t43 272 0
field 5 "_" t40 312 0
field 6 "spanqMask" t71 440 0
field 7 "_" t40 464 0
field 8 "spanSPMCs" t72 592 0
field 9 "bytesMarked" t13 624 0
field 10 "markrootNext" t74 632 0
field 11 "markrootJobs" t74 636 0
field 12 "nproc" t12 640 0
field 13 "tstart" t5 648 0
field 14 "nwait" t12 656 0
field 15 "nDataRoots" t14 664 0
field 16 "nBSSRoots" t14 672 0
field 17 "nSpanRoots" t14 680 0
field 18 "nStackRoots" t14 688 0
field 19 "nMaybeRunnableStackRoots" t14 696 0
field 20 "goroutineLeak" t75 704 0
field 21 "baseData" t12 720 0
field 22 "baseBSS" t12 724 0
field 23 "baseSpans" t12 728 0
field 24 "baseStacks" t12 732 0
field 25 "baseEnd" t12 736 0
field 26 "stackRoots" t77 744 0
field 27 "startSema" t12 768 0
field 28 "markDoneSema" t12 772 0
field 29 "bgMarkDone" t12 776 0
field 30 "mode" t228 784 0
field 31 "userForced" t6 792 0
field 32 "initialHeapLive" t13 800 0
field 33 "assistQueue" t229 808 0
field 34 "sweepWaiters" t231 840 0
field 35 "strongFromWeak" t232 864 0
field 36 "cycles" t74 904 0
field 37 "stwprocs" t9 908 0
field 38 "maxprocs" t9 912 0
field 39 "tSweepTerm" t5 920 0
field 40 "tMark" t5 928 0
field 41 "tMarkTerm" t5 936 0
field 42 "tEnd" t5 944 0
field 43 "pauseNS" t5 952 0
field 44 "heap0" t13 960 0
field 45 "heap1" t13 968 0
field 46 "heap2" t13 976 0
field 47 "cpuStats" t4 984 1
type t37 PTR 8 8 0 comparable "*workType" "*runtime.workType" t38
aux a4 sym "runtime.work" "runtime.work" 0 - 0 - - - - 0
type t233 PTR 8 8 8 hasptr,direct,comparable "*cpuStats" "*runtime.cpuStats" t4
aux a5 type "cpuStats" t4
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t6,Int8=t7,Int16=t8,Int32=t9,Int64=t5,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v2 SP t18 0 - p0:0:0:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:0:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:0:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v2 SP t18 0 - p0:0:0:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v2 SP t18 0 - p0:0:0:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache linestarts 24:748:754
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p24:747:6:2:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 20 "expand calls"
aux a6 nameoff "a+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
v v4 SP t18 0 - p0:0:0:0:0 1 -
v v2 OffPtr t36 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
v v4 SP t18 0 - p0:0:0:0:0 1 -
v v2 OffPtr t36 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
v v4 SP t18 0 - p0:0:0:0:0 1 -
v v2 OffPtr t36 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
v v4 SP t18 0 - p0:0:0:0:0 1 -
v v2 OffPtr t36 0 - p0:0:0:0:0 0 v4
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v6 Addr t37 0 a4 p0:0:0:0:0 1 v3
v v8 NilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 OffPtr t233 984 - p24:748:19:0:0 1 v6
v v9 OffPtr t233 0 - p24:748:3:0:0 1 v8
v v10 Move t31 88 a5 p24:748:13:0:0 1 v9,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3
cache linestarts 24:748:754
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v8 ARM64LoweredNilCheck t2 0 - p24:748:3:1:0 1 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v8,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 2 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v8 ARM64LoweredNilCheck t33 0 - p24:748:3:1:0 0 v5,v1
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:0:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:1:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v7 ARM64MOVDaddr t233 984 a4 p24:748:19:1:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v7,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v6,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t233 984 a4 p24:748:13:1:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v9,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
regalloc 10 v3:SB,v5:R0,v9:R1
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t233 984 a4 p24:748:13:1:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v9,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
regalloc 10 v3:SB,v5:R0,v9:R1
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p24:754:1:0:0 0 0 - v11 - -
v v5 ArgIntReg t2 0 a6 p24:754:1:0:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t233 984 a4 p24:748:13:1:0 1 v3
v v10 ARM64LoweredMove t31 88 - p24:748:13:0:0 1 v5,v9,v1
v v11 MakeResult t35 0 - p24:754:1:1:0 1 v10
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v6
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a4:3,a6:4
cache linestarts 24:748:754
fstate scheduled,laidout
regalloc 10 v3:SB,v5:R0,v9:R1
dcllen 1
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t24,t27,t28,t29,t30,t39,t42,t44,t46,t49,t50,t53,t54,t56,t57,t58,t59,t60,t61,t63,t64,t68,t69,t73,t74,t76,t78,t79,t80,t81,t82,t83,t84,t85,t86,t87,t88,t89,t90,t91,t92,t93,t94,t95,t97,t100,t101,t102,t103,t105,t107,t110,t113,t115,t116,t117,t119,t120,t121,t122,t123,t127,t129,t131,t134,t135,t136,t137,t139,t140,t143,t144,t145,t147,t149,t150,t152,t155,t156,t157,t159,t160,t162,t163,t164,t166,t168,t171,t173,t175,t176,t178,t179,t180,t181,t184,t186,t187,t188,t190,t191,t198,t201,t203,t205,t206,t209,t216,t218,t220,t222,t225,t227,t230
typelink t10=t42,t20=t68,t31=t35
typecmp t10 t66 gt
typeorder t7,t10=t42,t66,t65,t55,t215,t193,t8,t11,t9,t69,t70,t12,t98,t5,t214,t13,t39,t200,t14,t228,t141,t17,t152,t18,t93,t103,t97,t52,t28,t29,t15,t16,t6,t20=t68,t21,t22,t23,t157,t24,t25,t26,t27,t36,t217,t158,t185,t78,t90,t100,t221,t63,t49,t119,t167,t84,t81,t53,t104,t126,t170,t178,t59,t146,t233,t154,t197,t37,t51,t135,t183,t172,t224,t2,t142,t112,t87,t86,t223,t177,t192,t67,t169,t1,t216,t191,t77,t99,t118,t114,t165,t218,t128,t71,t133,t196,t195,t204,t132,t211,t108,t129,t96,t205,t212,t182,t175,t210,t188,t115,t160,t41,t125,t123,t107,t106,t149,t151,t116,t163,t159,t201,t95,t186,t124,t153,t229,t43,t231,t72,t232,t75,t79,t91,t101,t208,t48,t222,t187,t64,t76,t117,t92,t50,t44,t80,t120,t168,t162,t181,t209,t171,t137,t57,t85,t82,t230,t54,t145,t144,t105,t127,t164,t74,t140,t58,t179,t62,t60,t147,t138,t4,t207,t155,t198,t38,t226,t180,t61,t176,t46,t189,t136,t110,t150,t166,t184,t47,t102,t202,t148,t227,t194,t130,t219,t173,t94,t213,t139,t190,t111,t203,t40,t56,t109,t89,t73,t156,t45,t225,t199,t206,t134,t3,t121,t174,t143,t122,t161,t113,t131,t88,t220,t83,t19,t30,t31,t33,t32,t34,t35
eof
"#

/-- `std/std/runtime/%28%2AcpuStatsAggregate%29.compute,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*cpuStatsAggregate).compute" 1
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
type t1 8 8 8 1 01 "*cpuStatsAggregate"
name n1 "a" PPARAM t1 1 "runtime.a" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p24 "runtime/metrics.go" 1 1 -1 23 "runtime/metrics.go" "runtime/metrics.go" 1 1
sym y1 "runtime.(*cpuStatsAggregate).compute" 1
curfn p24:747:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 747 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*cpuStatsAggregate).compute.arginfo1" 0
sym y5 "runtime.(*cpuStatsAggregate).compute.argliveinfo" 0
sym y6 "runtime.work" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p24:747:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p24:747:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p24:747:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p24:747:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p24:747:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p24:747:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p24:748:13:1:0
p 7 7 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/984/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p24:748:13:1:0
p 8 8 0 0 0 - FLDPQ 0 MEM/8193/0/0/NONE/0/0/-/- 0 - REGREG/8240/0/0/NONE/0/8241/-/- 0 0 p24:748:13:2:0
p 9 9 0 0 0 - FSTPQ 0 REGREG/8240/0/0/NONE/0/8241/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p24:748:13:2:0
p 10 10 0 0 0 - FLDPQ 0 MEM/8193/0/0/NONE/0/32/-/- 0 - REGREG/8240/0/0/NONE/0/8241/-/- 0 0 p24:748:13:2:0
p 11 11 0 0 0 - FSTPQ 0 REGREG/8240/0/0/NONE/0/8241/-/- 0 - MEM/8192/0/0/NONE/0/32/-/- 0 0 p24:748:13:2:0
p 12 12 0 0 0 - FMOVQ 0 MEM/8193/0/0/NONE/0/64/-/- 0 - REG/8240/0/0/NONE/0/0/-/- 0 0 p24:748:13:2:0
p 13 13 0 0 0 - FMOVQ 0 REG/8240/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/64/-/- 0 0 p24:748:13:2:0
p 14 14 0 0 0 - MOVD 0 MEM/8193/0/0/NONE/0/80/-/- 0 - REG/8217/0/0/NONE/0/0/-/- 0 0 p24:748:13:2:0
p 15 15 0 0 0 - MOVD 0 REG/8217/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/80/-/- 0 0 p24:748:13:2:0
p 16 16 0 0 0 - RET 0 _ 0 - _ 0 0 p24:754:1:0:0
p 17 17 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 747 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:-1:-30000:50
dbgregout -
dbgpc -
end
asm
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p24:747:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p24:747:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p24:747:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p24:747:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p24:747:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p24:747:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p24:748:13:1:0
p 7 0 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/984/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p24:748:13:1:0
p 8 8 0 0 129 - FLDPQ 0 MEM/8193/0/0/NONE/77/0/-/- 0 - REGREG/8240/0/0/NONE/7/8241/-/- 0 0 p24:748:13:2:0
p 9 12 0 0 225 - FSTPQ 0 REGREG/8240/0/0/NONE/7/8241/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p24:748:13:2:0
p 10 16 0 0 129 - FLDPQ 0 MEM/8193/0/0/NONE/86/32/-/- 0 - REGREG/8240/0/0/NONE/7/8241/-/- 0 0 p24:748:13:2:0
p 11 20 0 0 225 - FSTPQ 0 REGREG/8240/0/0/NONE/7/8241/-/- 0 - MEM/8192/0/0/NONE/86/32/-/- 0 0 p24:748:13:2:0
p 12 24 0 0 180 - FMOVQ 0 MEM/8193/0/0/NONE/86/64/-/- 0 - REG/8240/0/0/NONE/5/0/-/- 0 0 p24:748:13:2:0
p 13 28 0 0 169 - FMOVQ 0 REG/8240/0/0/NONE/5/0/-/- 0 - MEM/8192/0/0/NONE/86/64/-/- 0 0 p24:748:13:2:0
p 14 32 0 0 333 - MOVD 0 MEM/8193/0/0/NONE/86/80/-/- 0 - REG/8217/0/0/NONE/2/0/-/- 0 0 p24:748:13:2:0
p 15 36 0 0 308 - MOVD 0 REG/8217/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/86/80/-/- 0 0 p24:748:13:2:0
p 16 40 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p24:754:1:0:0
fn y1 8 0 0 0 747 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 48 0 0100009021000091304440ad104400ad304441ad104401ad3010c03d1010803d392840f9192800f9c0035fd600000000 1
reloc 0 8 R_ADDRARM64 984 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y3,_,_,_,y4,y5
usedfiles 23
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y7 SRODATA 3 1 28000 010c00 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 3 1 28000 040c00 0
data y11 SRODATA 3 1 28000 020c00 0
data y12 SRODATA 3 1 28000 300c00 0
data y13 SRODATA 6 1 28000 da0b0a0c0200 0
data y14 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.runtime.(*cpuStatsAggregate).compute$abstract" 0
sym y19 "" 0
sym y20 "go:info.*runtime.cpuStatsAggregate" 0
dwfn y15 y16 y17 y18 y19 "runtime.(*cpuStatsAggregate).compute" 23:747 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y18 n1
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.cpuStatsAggregate" 0 0 1 p24:747:7:0:0
var 0 0 "a" 5 1 0 0 0 8 y20 "runtime/metrics.go" 747 7 0 0 1 0 v0
scope 0 0 - 0
dieref y15 2 y18 0
dieoff y18 0:42
data y15 SDWARFFCN 20 0 0 0600000000000030019c29000000000000000000 4
reloc 1 4 R_DWARFSECREF 0 y18
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y18
reloc 15 4 R_DWARFSECREF 0 y16
data y16 SDWARFLOC 9 0 0 010000040030015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y19 SDWARFLINES 29 0 0 0009020000000000000000041803e60514065f06080301640208000101 1
reloc 3 8 R_ADDR 0 y1
data y18 SDWARFABSFCN 51 0 1 0572756e74696d652e282a6370755374617473416767726567617465292e636f6d707574650001eb0501226100000000000000 1
reloc 46 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.(*cpuStatsAggregate).compute`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G53's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG53` gives (`b1`: `v9`'s `MOVD $runtime.work+984, R1` at Prog 7 after the
`PCDATA`s at 5 and 6, `v10`'s eight Progs from 8, then the `RET` at 16). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 8, 16, 16])]

/-- The class table `checkG53` gives. -/
def kt : KTab := (match checkG53 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1`, the destination (its Phase 1 address `2^41`). -/
def A : BitVec 64 := 0x20000000000

/-- The machine address of `heap 2`, the source (its Phase 1 address `3 * 2^40`). -/
def B : BitVec 64 := 0x30000000000

/-- `ι`: the nil block, the globals at `symA`, `heap 1` at `A` and `heap 2` at `B`. -/
def ι53 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .heap 1 => some 0x20000000000
  | .heap 2 => some 0x30000000000
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the two heap objects at `A` and `B` and the PC table of `checkG53`. -/
def E : MatchEnv :=
  { lc, ι := ι53, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The destination `a` (`v5`): the start of `heap 1`. -/
def pD : Ptr := ⟨.heap 1, 0⟩

/-- The source `&work.cpuStats` (`v9`): the start of `heap 2`. -/
def pS : Ptr := ⟨.heap 2, 0⟩

/-- Byte `i` of the source: `i + 1`, except bytes 5 to 7, 0 (so that its first word, below
`2^40`, encodes no pointer address). -/
def byteS (i : Nat) : BitVec 8 := if 5 ≤ i ∧ i < 8 then 0 else BitVec.ofNat 8 (i + 1)

/-- The 88 bytes of the source. -/
def srcB : Array Byte := Array.ofFn (n := 88) fun i => .b (byteS i.val)

/-- The Phase 1 memory before `v10`: `heap 1` 88 poison bytes, `heap 2` the 88 bytes `byteS`. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.replicate 88 .poison }),
      (.heap 2, { data := srcB })],
    nextHeap := 3 }

/-- The machine memory before `v10`: the bytes of `heap 2` at `B`, 0 elsewhere. -/
def M1 : Memory := fun y => if (y - B).toNat < 88 then byteS (y - B).toNat else 0

/-- The `runLoc` state before `v10`: `a` (`pD`, `v5`) in `R0`, `&work.cpuStats` (`pS`, `v9`) in
`R1`, every other register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pD else if i.val = 1 then .ptr pS else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v10`: `X0 = A`, `X1 = B`, the activation's `g` and `FP`, the PC of `v10`,
the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 1 then B else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 4, mem := M1 }

/-- The value is the 64-bit `w`. -/
def isW (w : BitVec 64) : Val → Bool
  | .int .w64 x => x == w
  | _ => false

theorem isW_spec {w : BitVec 64} {x : Val} (h : isW w x = true) : x = .int .w64 w := by
  unfold isW at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- The copy is valid: `mem1` has 88 readable bytes at `pS`, and writing them at `pD` succeeds. -/
def moveOK : Bool :=
  match mem1.read pS 88 with
  | some bs => (mem1.write pD bs).isSome
  | none => false

theorem moveOK_spec (h : moveOK = true) :
    ∃ bs mm', mem1.read pS 88 = some bs ∧ mem1.write pD bs = some mm' := by
  unfold moveOK at h
  split at h
  · rename_i bs hbs
    obtain ⟨mm', hw⟩ := Option.isSome_iff_exists.1 h
    exact ⟨bs, mm', hbs, hw⟩
  · cases h

/-- After the copy: the memory holds `srcB` at `pD`, and its first block is `heap 1`, whose first
byte is the source's first byte and whose first word encodes no pointer address. -/
def dstIs (s : LocState) : Bool :=
  match s.mem with
  | .mem mm => mm.read pD 88 == some srcB &&
      match mm.blocks[0]? with
      | some (b, al) => b == .heap 1 && al.data[0]? == some (.b (byteS 0)) &&
          (ptrWordAt? al.data 0).isNone
      | none => false
  | _ => false

theorem dstIs_spec {s : LocState} (h : dstIs s = true) :
    ∃ mm al, s.mem = .mem mm ∧ mm.read pD 88 = some srcB ∧ (Blk.heap 1, al) ∈ mm.blocks ∧
      al.data[0]? = some (.b (byteS 0)) ∧ ptrWordAt? al.data 0 = none := by
  unfold dstIs at h
  split at h
  · rename_i mm hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i b al hba
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h2
      obtain ⟨⟨rfl, h3⟩, h4⟩ := h2
      exact ⟨mm, al, hm, h1, Array.mem_of_getElem? hba, h3, h4⟩
    · cases h2
  · cases h

/-- What compiled evaluation checks on `runtime.(*cpuStatsAggregate).compute`: it holds an arm64
op; `checkG53` accepts it with `tab` and `kt` and `checkG52` does not; it accesses no frame variable
and has no home slot; `b1` holds `v10` (`LoweredMove [88] v5 v9 v1`) at index 4, where `R0` and
`R1` have class 64 and G35's table is empty; in `s0` its destination reads as the word `A` and its
source as `B` (a lowered function reads pointers as their addresses), the addresses of `pD` and
`pS`, where the copy of 88 bytes is valid; `stepLoc` runs `v10` from `s0` to a memory holding `srcB` at
`pD`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG53 lc0 ps bs g).toOption == some (tab, kt) && (checkG52 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 10).isSome && blk.values[4]? == some 10 &&
    (val 10).op == .ARM64LoweredMove && (val 10).args[0]? == some 5 &&
    (val 10).args[1]? == some 9 && (val 10).auxInt.toInt.toNat == 88 &&
    (kAt lc kt 1 blk 4).get 0 == some 64 && (kAt lc kt 1 blk 4).get 1 == some 64 &&
    uL35 lc (uIn35 lc 1) blk 4 == [] &&
    GenG1.okThen (s0.read lc 5) (isW A) && GenG1.okThen (s0.read lc 9) (isW B) &&
    Arm64.addr (.int .w64 A) 0 == some pD && Arm64.addr (.int .w64 B) 0 == some pS && moveOK &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) dstIs

theorem g53_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG53 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG52 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 10 = some (val 10) ∧ blk.values[4]? = some 10 ∧
      (val 10).op = .ARM64LoweredMove ∧ (val 10).args[0]? = some 5 ∧
      (val 10).args[1]? = some 9 ∧ (val 10).auxInt.toInt.toNat = 88 ∧
      (kAt lc kt 1 blk 4).get 0 = some 64 ∧ (kAt lc kt 1 blk 4).get 1 = some 64 ∧
      uL35 lc (uIn35 lc 1) blk 4 = [] ∧
      GenG1.okThen (s0.read lc 5) (isW A) = true ∧ GenG1.okThen (s0.read lc 9) (isW B) = true ∧
      Arm64.addr (.int .w64 A) 0 = some pD ∧ Arm64.addr (.int .w64 B) 0 = some pS ∧
      moveOK = true ∧ GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) dstIs = true := by
  have hf := g53_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h52, hav, hsl, hm1, hbs, hvs, hi4, hop, ha0, ha1, hn, hk0, hk1, hu4, hr5, hr9,
    hpd, hps, hmv, hrun⟩ := hf
  refine ⟨hl, ?_, h52, hav, hsl, hm1, ?_, ?_, hi4, hop, ha0, ha1, hn, hk0, hk1, hu4, hr5, hr9, hpd,
    hps, hmv, hrun⟩
  · revert hres; cases checkG53 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

/-- `ι53` puts every block with a Phase 1 address (`nil`, `heap 1`, `heap 2`) at it. -/
theorem addrAgree53 : AddrAgree ι53 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι53] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k =>
    simp only [Blk.base?_heap, Option.some.injEq] at hb
    subst hb
    unfold ι53 at ha
    split at ha <;> first | cases ha | skip
    all_goals simp_all
  | _ => simp [ι53] at ha <;> simp [Blk.base?] at hb

theorem g53Env (hc : checkG53 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
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
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
                checkG53L_spec hl (checkG53_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree53
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
                checkG53L_spec hl (checkG53_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by show 0 ≤ (8 : Int); decide
            frame := ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
              by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## The memory -/

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    (b = .heap 1 ∧ al = { data := Array.replicate 88 .poison }) ∨
      (b = .heap 2 ∧ al = { data := srcB }) := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `ι53`: `heap 1`'s poison bytes at `A`, `heap 2`'s bytes at `B`. -/
theorem memInj1 : MemInj ι53 mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
    · exact ⟨B, rfl, fun _ => by decide, by simp [B, srcB]⟩
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases mem1_blocks h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd rfl hne
    · simp only [ι53, Option.some.injEq] at ha ha'
      subst ha; subst ha'
      left; simp
    · simp only [ι53, Option.some.injEq] at ha ha'
      subst ha; subst ha'
      right; simp
    · exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [ByteRel]
    · have ha' : a = B := by simp [ι53] at ha; exact ha.symm
      subst ha'
      simp only [srcB, Array.size_ofFn] at hi
      have hd : (B + BitVec.ofNat 64 i - B).toNat = i := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
        omega
      simp [ByteRel, M1, srcB, hd, hi]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι53 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    rw [hsp] at h2
    rcases mem1_blocks h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have ha' : a = A := by simp [ι53] at ha; exact ha.symm
      subst ha'
      have hA : A.toNat = 0x20000000000 := rfl
      simp only [hA, Array.size_replicate]
      omega
    · have ha' : a = B := by simp [ι53] at ha; exact ha.symm
      subst ha'
      have hB : B.toNat = 0x30000000000 := rfl
      simp only [hB, srcB, Array.size_ofFn]
      omega
  · cases hk

/-! ## `v10`: `LoweredMove [88] v5 v9 v1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pD) ∨ (r = 1 ∧ x = .ptr pS) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 1 4 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨B, rfl, by decide⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E, B]; decide,
    by simp only [MState.word, readMem, m0, M1, E, B]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g53Inv0 (h0 : (kAt lc kt 1 blk 4).get 0 = some 64)
    (h1 : (kAt lc kt 1 blk 4).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 4) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G51 on `v10`, `LoweredMove`: none of them applies. -/
theorem pre51 (hop : (val 10).op = .ARM64LoweredMove) : G51Pre lc s0 (val 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64LoweredMove → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ _ hl; rw [hop] at hl; simp [fp2Of] at hl
  · intro _ _ _ _ hl; rw [hop] at hl; simp [fp3Of] at hl
  · intro _ _ _ _ hpo; rw [hop] at hpo; simp [pairOp50] at hpo
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))

/-- `Pre53a` on `v10`: its destination `pD` (`heap 1`) and source `pS` (`heap 2`) are distinct
blocks, and `mem1` has the 88 bytes to read at `pS` and to write at `pD`. -/
theorem pre53 (ha0 : (val 10).args[0]? = some 5) (ha1 : (val 10).args[1]? = some 9)
    (hn : (val 10).auxInt.toInt.toNat = 88) (hr5 : GenG1.okThen (s0.read lc 5) (isW A) = true)
    (hr9 : GenG1.okThen (s0.read lc 9) (isW B) = true)
    (hpd : Arm64.addr (.int .w64 A) 0 = some pD) (hps : Arm64.addr (.int .w64 B) 0 = some pS)
    (hmv : moveOK = true) :
    Pre53a lc s0 (val 10) := by
  intro _ d x a y hd hx ha hy
  rw [ha0] at hd
  cases hd
  rw [ha1] at ha
  cases ha
  obtain ⟨x', hx', hpx⟩ := GenG1.okThen_spec hr5
  obtain ⟨y', hy', hpy⟩ := GenG1.okThen_spec hr9
  rw [hx] at hx'
  cases hx'
  rw [hy] at hy'
  cases hy'
  rw [isW_spec hpx, isW_spec hpy]
  obtain ⟨bs, mm', hbs, hw⟩ := moveOK_spec hmv
  refine ⟨pD, pS, mem1, bs, mm', hpd, hps, rfl, by rw [hn]; exact hbs, hw,
    Or.inr (Or.inl (by decide))⟩

/-- **G53 on `runtime.(*cpuStatsAggregate).compute`** (`func (a *cpuStatsAggregate) compute() {
a.cpuStats = work.cpuStats }`, which on arm64 copies the 88 bytes of `work.cpuStats` with
`LoweredMove`): `b1` copies them (`v10`, `LoweredMove [88] v5 v9 v1`, `a` in `R0`,
`&work.cpuStats` in `R1`) with two `FLDPQ`/`FSTPQ` pairs, a `FMOVQ` pair and a `MOVD` pair, which
`checkG52` rejects (`v10: op LoweredMove`) and `checkG53` accepts. From `s0`, with the destination
`heap 1` (88 poison bytes) in `R0` and the source `heap 2` (the 88 bytes `srcB`) in `R1`,
`stepLoc` runs `v10` to a memory holding `srcB` at the destination, and `g53_value` relates it to a
machine state after `v10`'s code whose memory holds the source's first byte at the destination's
address `A`, under an activation extending `E` that is again a `G49Env`. -/
theorem genG53_witness :
    (checkG52 lc0 ps bs g).toOption = none ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 10) = .ok s1 ∧ s1.mem = .mem mm ∧
        mm.read pD 88 = some srcB ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 5 m1 ∧ m1.mem A = byteS 0 := by
  obtain ⟨hl, hc, h52, hav, hsl, hm1, hb, hv10, hi4, hop, ha0, ha1, hn, hk0, hk1, hu4, hr5, hr9,
    hpd, hps, hmv, hrun⟩ := facts
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hrd, hal, hal0, hpw⟩ := dstIs_spec hd
  have hE := g53Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredMove → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g53_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 10 = some (val 10) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv10
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g53_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi4 hv0 (by rw [hop]; rfl) locMatch0 (g53Inv0 hk0 hk1)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 4); rw [hu4]; intro e he; cases he)
    ⟨pre51 hop, pre53 ha0 ha1 hn hr5 hr9 hpd hps hmv⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  -- The first byte of `heap 1` after the copy, read through `MemInj`: no pointer word covers it.
  have hA : m1.mem A = byteS 0 := by
    obtain ⟨mm1, hmm1, hinj⟩ := hm1'.mem
    rw [hmm] at hmm1
    cases hmm1
    obtain ⟨W, hW⟩ := hinj.bytes
    obtain ⟨hw, -, hby⟩ := hW _ _ _ hal (hx1.2 (.heap 1) A rfl)
    obtain ⟨h0, hd0⟩ := Array.getElem?_eq_some_iff.1 hal0
    have hr := hby 0 h0 (fun o ho ho' => by
      obtain ⟨p, hp, -⟩ := hw o ho
      have : o = 0 := by omega
      subst this
      rw [hpw] at hp
      cases hp)
    rw [hd0, show A + BitVec.ofNat 64 0 = A by decide] at hr
    exact hr.symm
  exact ⟨h52, s1, mm, E1, m1, hs1, hmm, hrd, hx1, hE1, hp1, hm1', hA⟩

end GoFV.Proof.Witness.GenG53
