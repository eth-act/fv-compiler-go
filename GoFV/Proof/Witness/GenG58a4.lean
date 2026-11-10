import GoFV.Gen.Check57
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG58a4

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/%28%2Atimers%29.unlock,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*timers).unlock" 1 0 0
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
type t5 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t6 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t4 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t5 0 1
field 1 "key" t6 0 0
type t12 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t13 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 STRUCT 1 1 0 comparable,named "atomic.Uint8" "internal/runtime/atomic.Uint8" 2
field 0 "noCopy" t12 0 0
field 1 "value" t13 0 0
type t14 BOOL 1 1 0 comparable,named "bool" "bool"
type t15 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t16 INT64 8 8 0 comparable,named "int64" "int64"
type t18 INTER 16 8 16 hasptr,comparable,named,emptyiface "any" "interface {}"
type t17 FUNC 8 8 8 hasptr,direct "func(any, uintptr, int64)" "func(interface {}, uintptr, int64)" 0 3 0
field 0 "arg" t18 ? 0
field 1 "seq" t6 ? 0
field 2 "delay" t16 ? 0
type t20 INT32 4 4 0 comparable,named "int32" "int32"
type t19 STRUCT 4 4 0 comparable,named "atomic.Int32" "internal/runtime/atomic.Int32" 2
field 0 "noCopy" t12 0 0
field 1 "value" t20 0 0
type t10 STRUCT 96 8 80 hasptr,named "timer" "runtime.timer" 15
field 0 "mu" t4 0 0
field 1 "astate" t11 8 0
field 2 "state" t13 9 0
field 3 "isChan" t14 10 0
field 4 "isFake" t14 11 0
field 5 "blocked" t15 12 0
field 6 "rand" t15 16 0
field 7 "when" t16 24 0
field 8 "period" t16 32 0
field 9 "f" t17 40 0
field 10 "arg" t18 48 0
field 11 "seq" t6 64 0
field 12 "ts" t2 72 0
field 13 "sendLock" t4 80 0
field 14 "isSending" t19 88 0
type t9 PTR 8 8 8 hasptr,direct,comparable "*timer" "*runtime.timer" t10
type t8 STRUCT 16 8 8 hasptr,comparable,named "timerWhen" "runtime.timerWhen" 2
field 0 "timer" t9 0 0
field 1 "when" t16 8 0
type t7 SLICE 24 8 8 hasptr "[]timerWhen" "[]runtime.timerWhen" t8
type t21 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t12 0 0
field 1 "value" t15 0 0
type t23 STRUCT 0 8 0 comparable,named "atomic.align64" "internal/runtime/atomic.align64" 0
type t22 STRUCT 8 8 0 comparable,named "atomic.Int64" "internal/runtime/atomic.Int64" 3
field 0 "noCopy" t12 0 0
field 1 "_" t23 0 0
field 2 "value" t16 0 0
type t3 STRUCT 64 8 16 hasptr,named "timers" "runtime.timers" 7
field 0 "mu" t4 0 0
field 1 "heap" t7 8 0
field 2 "len" t21 32 0
field 3 "zombies" t19 36 0
field 4 "raceCtx" t6 40 0
field 5 "minWhenHeap" t22 48 0
field 6 "minWhenModified" t22 56 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*timers" "*runtime.timers" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*timers) func()" "method(*runtime.timers) func()" 1 0 0
field 0 "ts" t2 ? 0
aux a2 sym "runtime.(*timers).unlock" "runtime.(*timers).unlock" 1 - 0 - - - - 0
posbase p37 "runtime/time.go" 1 1 -1
aux a3 name "ts" "ts" PPARAM t2 0 1 used p37:191:7:0:0
aux a1 call "AuxCall{runtime.(*timers).unlock}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t24 INT8 1 1 0 comparable,named "int8" "int8"
type t25 INT16 2 2 0 comparable,named "int16" "int16"
type t26 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t27 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t28 INT 8 8 0 comparable,named "int" "int"
type t29 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t30 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t31 UINT 8 8 0 comparable,named "uint" "uint"
type t32 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t13
type t34 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t20
type t35 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t15
type t36 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t28
type t37 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t6
type t38 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t29
type t39 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t30
type t40 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t33
type t41 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t42 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t43 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t44 SSA ? ? ? - "mem" ""
type t45 SSA ? ? ? - "flags" ""
type t46 SSA ? ? ? - "void" ""
type t47 SSA 16 8 ? - "int128" ""
type t48 RESULTS ? ? ? - "mem" "" 1 t44
type t49 PTR 8 8 8 hasptr,direct,comparable "**timers" "**runtime.timers" t2
type t50 PTR 8 8 8 hasptr,direct,comparable "*[]timerWhen" "*[]runtime.timerWhen" t7
type t51 PTR 8 8 8 hasptr,direct,comparable "*atomic.Uint32" "*internal/runtime/atomic.Uint32" t21
posbase p3216 "internal/runtime/atomic/types.go" 1 1 2943
posbase p3217 "runtime/lock_spinbit.go" 1 1 2944
type t52 PTR 8 8 8 hasptr,direct,comparable "*mutex" "*runtime.mutex" t4
aux a5 sym "runtime.unlock2" "runtime.unlock2" 1 - 0 - - - - 0
aux a4 call "AuxCall{runtime.unlock2}" a5 1 1 0 8 8 1 0
abiparam in 0 t52 - 0 0
posbase p3218 "runtime/lockrank_off.go" 1 1 2945
slot s1 a3 t2 0 - 0
aux a6 name "atomic.u" "u" PAUTO t51 0 1 used p3216:213:7:0:0
slot s2 a6 t51 0 - 0
aux a7 name "atomic.value" "value" PAUTO t15 0 1 used p3216:213:24:0:0
slot s3 a7 t15 0 - 0
aux a8 name "l" "l" PAUTO t52 0 1 used p3217:269:13:0:0
slot s4 a8 t52 0 - 0
aux a9 name "l" "l" PAUTO t52 0 1 used p3218:35:21:0:0
slot s5 a9 t52 0 - 0
f b1 t1 a1 26 4
typs Bool=t14,Int8=t24,Int16=t25,Int32=t20,Int64=t16,UInt8=t13,UInt16=t26,UInt32=t15,UInt64=t27,Int=t28,Float32=t29,Float64=t30,UInt=t31,Uintptr=t6,String=t32,BytePtr=t33,Int32Ptr=t34,UInt32Ptr=t35,IntPtr=t36,UintptrPtr=t37,Float32Ptr=t38,Float64Ptr=t39,BytePtrPtr=t40,Complex64=t41,Complex128=t42,UnsafePtr=t43,Mem=t44,Flags=t45,Void=t46,Int128=t47,ResultMem=t48
b b1 Plain p37:199:14:0:0 0 0 - - b2:0 -
v v1 InitMem t44 0 - p0:0:0:0:0 7 -
v v2 SP t6 0 - p0:0:0:0:0 1 -
v v3 SB t6 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t49 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:0:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:1:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:0:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 1 v15,v12,v1
b b2 Plain p3217:270:16:0:0 0 0 - - b3:0 b1:0
v v17 Copy t2 0 - p37:201:12:2:0 1 v5
v v18 Copy t44 0 - p37:201:12:2:0 4 v16
v v19 NilCheck t2 0 - p37:201:12:0:0 1 v17,v18
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v18
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v18
v v23 StaticLECall t48 8 a4 p3218:36:9:0:0 1 v20,v18
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
b b3 Plain p37:202:1:0:0 0 0 - - b4:0 b2:0
b b4 Ret p37:202:1:0:0 0 0 - v26 - b3:0
v v25 Copy t44 0 - p37:202:1:2:0 1 v24
v v26 MakeResult t48 0 - p37:202:1:0:0 1 v25
names s1,s2,s3,s4,s5
named s1 v5,v17
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev -
freeb -
dcllen 7
end
pass 1 "number lines"
f b1 t1 a1 26 4
b b1 Plain p37:199:14:1:0 0 0 - - b2:0 -
v v1 InitMem t44 0 - p0:0:0:0:0 7 -
v v2 SP t6 0 - p0:0:0:0:0 1 -
v v3 SB t6 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t49 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 1 v15,v12,v1
b b2 Plain p3217:270:16:1:0 0 0 - - b3:0 b1:0
v v17 Copy t2 0 - p37:201:12:2:0 1 v5
v v18 Copy t44 0 - p37:201:12:2:0 4 v16
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v17,v18
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v18
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v18
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v18
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
b b3 Plain p37:202:1:1:0 0 0 - - b4:0 b2:0
b b4 Ret p37:202:1:0:0 0 0 - v26 - b3:0
v v25 Copy t44 0 - p37:202:1:2:0 1 v24
v v26 MakeResult t48 0 - p37:202:1:0:0 1 v25
names s1,s2,s3,s4,s5
named s1 v5,v17
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev -
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 26 4
b b1 Plain p37:199:14:1:0 0 0 - - b2:0 -
v v1 InitMem t44 0 - p0:0:0:0:0 7 -
v v2 SP t6 0 - p0:0:0:0:0 1 -
v v3 SB t6 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t49 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p37:191:6:2:0 4 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 5 v15,v12,v1
b b2 Plain p3217:270:16:1:0 0 0 - - b3:0 b1:0
v v17 Copy t2 0 - p37:201:12:2:0 0 v5
v v18 Copy t44 0 - p37:201:12:2:0 0 v16
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 2 v23
b b3 Plain p37:202:1:1:0 0 0 - - b4:0 b2:0
b b4 Ret p37:202:1:0:0 0 0 - v26 - b3:0
v v25 Copy t44 0 - p37:202:1:2:0 0 v24
v v26 MakeResult t48 0 - p37:202:1:0:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5,v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev -
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 3 "early deadcode"
f b1 t1 a1 26 4
b b1 Plain p37:199:14:1:0 0 0 - - b2:0 -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
b b2 Plain p3217:270:16:1:0 0 0 - - b3:0 b1:0
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
b b3 Plain p37:202:1:1:0 0 0 - - b4:0 b2:0
b b4 Ret p37:202:1:0:0 0 0 - v26 - b3:0
v v26 MakeResult t48 0 - p37:202:1:0:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb -
cache postorder b4,b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 4 "short circuit"
f b4 t1 a1 26 4
b b1 BlockInvalid p37:199:14:1:0 0 0 - - - -
b b2 BlockInvalid p3217:270:16:1:0 0 0 - - - -
b b3 BlockInvalid p37:202:1:1:0 0 0 - - - -
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb -
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 5 "decompose user"
f b4 t1 a1 26 4
b b1 BlockInvalid p37:199:14:1:0 0 0 - - - -
b b2 BlockInvalid p3217:270:16:1:0 0 0 - - - -
b b3 BlockInvalid p37:202:1:1:0 0 0 - - - -
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb -
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 6 "pre-opt deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 7 "opt"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 8 "zero arg cse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 9 "opt deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 1 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 1 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 10 "generic cse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 2 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 0 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v6
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 11 "phiopt"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 2 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 0 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v6
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 12 "gcse deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 Arg t2 0 a3 p37:191:6:2:0 3 -
v v6 NilCheck t2 0 - p37:199:28:1:0 2 v5,v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:0:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v10 NilCheck t2 0 - p37:199:4:0:0 0 v5,v1
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v6
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v14 NilCheck t51 0 - p3216:214:10:1:0 1 v11,v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:0:0 4 v15,v12,v1
v v19 NilCheck t2 0 - p37:201:12:1:0 1 v5,v16
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:0:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 13 "nilcheckelim"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v10 NilCheck t2 0 - p37:199:4:0:0 2 v5,v1
v v6 Copy t2 0 - p37:199:28:1:0 2 v10
v v14 Copy t51 0 - p3216:214:10:1:0 1 v11
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v6
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v19 Copy t2 0 - p37:201:12:1:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 14 "prove"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:0:0 2 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v6 Copy t2 0 - p37:199:28:1:0 2 v10
v v19 Copy t2 0 - p37:201:12:1:0 1 v10
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v6
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v6
v v20 OffPtr t52 0 - p37:201:12:0:0 1 v19
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v14 Copy t51 0 - p3216:214:10:1:0 1 v11
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 0 - p3216:214:10:0:0 1 v14
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 15 "divisible"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 0 - p3216:214:10:1:0 1 v11
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v14,v19,v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 16 "divmod"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v11 OffPtr t51 32 - p37:199:4:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 0 - p3216:214:10:1:0 1 v11
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v14,v19,v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 17 "middle opt"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v11,v14,v19,v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 18 "known bits"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v11,v14,v19,v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 19 "early fuse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 Arg t2 0 a3 p37:191:6:2:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticLECall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v11,v14,v19,v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 20 "expand calls"
aux a10 nameoff "ts+0" a3 0
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 1 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 Load t7 0 - p37:199:28:1:0 1 v7,v1
v v9 SliceLen t28 0 - p37:199:25:0:0 1 v8
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v9
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v11 SB t6 0 - p0:0:0:0:0 0 -
v v14 SP t6 0 - p0:0:0:0:0 1 -
v v19 OffPtr t49 0 - p0:0:0:0:0 0 v14
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts 0=v19
freev v6,v25,v18,v17,v4,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 21 "decompose builtin"
type t53 PTR 8 8 8 hasptr,direct,comparable "*timerWhen" "*runtime.timerWhen" t8
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 3 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 SliceMake t7 0 - p37:199:28:2:0 0 v6,v25,v17
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v11 SB t6 0 - p0:0:0:0:0 0 -
v v14 SP t6 0 - p0:0:0:0:0 1 -
v v19 OffPtr t49 0 - p0:0:0:0:0 0 v14
v v6 Load t53 0 - p37:199:28:1:0 1 v7,v1
v v25 Load t28 0 - p37:199:28:1:0 2 v18,v1
v v18 OffPtr t36 8 - p37:199:28:1:0 1 v7
v v17 Load t28 0 - p37:199:28:1:0 1 v4,v1
v v4 OffPtr t36 16 - p37:199:28:1:0 1 v7
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts 0=v19
freev v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 22 "softfloat"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 3 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 SliceMake t7 0 - p37:199:28:2:0 0 v6,v25,v17
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v11 SB t6 0 - p0:0:0:0:0 0 -
v v14 SP t6 0 - p0:0:0:0:0 1 -
v v19 OffPtr t49 0 - p0:0:0:0:0 0 v14
v v6 Load t53 0 - p37:199:28:1:0 1 v7,v1
v v25 Load t28 0 - p37:199:28:1:0 2 v18,v1
v v18 OffPtr t36 8 - p37:199:28:1:0 1 v7
v v17 Load t28 0 - p37:199:28:1:0 1 v4,v1
v v4 OffPtr t36 16 - p37:199:28:1:0 1 v7
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts 0=v19
freev v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 23 "branchelim"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 6 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v7 OffPtr t50 8 - p37:199:28:0:0 3 v10
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v8 SliceMake t7 0 - p37:199:28:2:0 0 v6,v25,v17
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v11 SB t6 0 - p0:0:0:0:0 0 -
v v14 SP t6 0 - p0:0:0:0:0 1 -
v v19 OffPtr t49 0 - p0:0:0:0:0 0 v14
v v6 Load t53 0 - p37:199:28:1:0 1 v7,v1
v v25 Load t28 0 - p37:199:28:1:0 2 v18,v1
v v18 OffPtr t36 8 - p37:199:28:1:0 1 v7
v v17 Load t28 0 - p37:199:28:1:0 1 v4,v1
v v4 OffPtr t36 16 - p37:199:28:1:0 1 v7
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts 0=v19
freev v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 24 "late opt"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202:199=4,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 25 "dead auto elim"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202:199=4,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 26 "sccp"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s2,s3,s4,s5
named s1 v5
named s2 v11
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202:199=4,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 27 "generic deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 28 "late fuse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 29 "check bce"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 30 "dse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 31 "memcombine"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 32 "writebarrier"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 NilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v20 OffPtr t52 0 - p37:201:12:1:0 1 v10
v v15 OffPtr t35 32 - p3216:214:10:1:0 1 v10
v v12 Trunc64to32 t15 0 - p37:199:25:0:0 1 v25
v v16 AtomicStore32 t44 0 - p3216:214:7:1:0 3 v15,v12,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 StaticCall t48 8 a4 p3218:36:9:1:0 1 v20,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 Load t28 0 - p37:199:28:1:0 1 v18,v1
v v18 OffPtr t36 16 - p37:199:28:2:0 1 v10
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 33 "lower"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 34 "addressing modes"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 35 "late lower"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 36 "pair"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1,s3,s4,s5
named s1 v5
named s3 v12
named s4 v20
named s5 v20
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 37 "lowered deadcode for cse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 38 "lowered cse"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 39 "elim unread autos"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 40 "tighten tuple selectors"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 41 "lowered deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 42 "checkLower"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 43 "loop invariant"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 44 "late phielim and copyelim"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 45 "tighten"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 46 "late deadcode"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 47 "critical"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 48 "phi tighten"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 49 "likelyadjust"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
dcllen 7
end
pass 50 "layout"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p37:199:4:1:0 3 v5,v1
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v10
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v10,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v10,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate laidout
dcllen 7
end
pass 51 "schedule"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 4 -
v v1 InitMem t44 0 - p0:0:0:0:0 4 -
v v10 ARM64LoweredNilCheck t46 0 - p37:199:4:1:0 0 v5,v1
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
dcllen 7
end
pass 52 "late nilcheck"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 3 -
v v1 InitMem t44 0 - p0:0:0:0:0 3 -
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
dcllen 7
end
pass 53 "flagalloc"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 3 -
v v1 InitMem t44 0 - p0:0:0:0:0 3 -
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v18,v12,v20,v4,v17,v6,v19,v14,v11,v8,v7,v9,v3,v2
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
dcllen 7
end
pass 54 "regalloc"
aux a4 call "AuxCall{runtime.unlock2}" a5 1 1 0 8 8 1 0
abiparam in 0 t52 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 3 -
v v1 InitMem t44 0 - p0:0:0:0:0 3 -
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v2,v3,v4,v6,v7,v8,v9,v11,v12,v14,v17,v18,v19,v20
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
regalloc 26 v5:R0,v15:R2,v23:[],v25:R1
dcllen 7
end
pass 55 "loop rotate"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 3 -
v v1 InitMem t44 0 - p0:0:0:0:0 3 -
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v2,v3,v4,v6,v7,v8,v9,v11,v12,v14,v17,v18,v19,v20
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
regalloc 26 v5:R0,v15:R2,v23:[],v25:R1
dcllen 7
end
pass 56 "trim"
f b4 t1 a1 26 4
b b4 Ret p37:202:1:0:0 0 0 - v26 - -
v v5 ArgIntReg t2 0 a10 p37:202:1:0:0 3 -
v v1 InitMem t44 0 - p0:0:0:0:0 3 -
v v25 ARM64MOVDload t28 16 - p37:199:28:1:0 1 v5,v1
v v15 ARM64ADDconst t35 32 - p3216:214:10:1:0 1 v5
v v13 InlMark t46 2943 - p37:199:14:0:0 0 v1
v v16 ARM64STLRW t44 0 - p3216:214:7:1:0 3 v15,v25,v1
v v21 InlMark t46 2944 - p37:201:8:1:0 0 v16
v v22 InlMark t46 2945 - p3217:270:16:1:0 0 v16
v v23 ARM64CALLstatic t48 8 a4 p3218:36:9:1:0 1 v5,v16
v v24 SelectN t44 0 - p3218:36:9:0:0 1 v23
v v26 MakeResult t48 0 - p37:202:1:1:0 1 v24
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1,a6/t51/0/-/0=s2,a7/t15/0/-/0=s3,a8/t52/0/-/0=s4,a9/t52/0/-/0=s5
consts -
freev v2,v3,v4,v6,v7,v8,v9,v11,v12,v14,v17,v18,v19,v20
freeb b3,b2,b1
cache postorder b4
cache idom b4:-
cache sdom b4:-:-:-:2:5
cache loopnest 5 0 - -
cache auxmap a3:1,-:2,a10:3
cache linestarts 37:199:202,3216:214:214,3217:270:270,3218:36:36
fstate scheduled,laidout
regalloc 26 v5:R0,v15:R2,v23:[],v25:R1
dcllen 7
end
frontend
end
ptrcache t3,t4,t6,t8,t10,t11,t12,t13,t14,t15,t16,t18,t19,t20,t21,t22,t24,t25,t26,t27,t28,t29,t30,t31,t32,t33,t37,t40,t41,t42,t43
typelink t44=t48
typeorder t24,t13,t25,t26,t20,t15,t16,t27,t28,t31,t6,t41,t42,t29,t30,t14,t33,t34,t35,t36,t37,t38,t39,t40,t49,t50,t52,t9,t2,t51,t53,t17,t1,t7,t4,t10,t19,t22,t11,t3,t21,t12,t23,t8,t5,t18,t32,t43,t44,t46,t45,t47,t48
eof
"#

/-- `std/std/runtime/%28%2Atimers%29.unlock,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*timers).unlock" 1
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
type t1 8 8 8 1 01 "*timers"
name n1 "ts" PPARAM t1 1 "runtime.ts" 0 a3
type t2 8 8 8 1 01 "*atomic.Uint32"
name n2 "u" PAUTO t2 1 "internal/runtime/atomic.u" 0 a6
type t3 4 4 0 0 - "uint32"
name n3 "value" PAUTO t3 1 "internal/runtime/atomic.value" 0 a7
type t4 8 8 8 1 01 "*mutex"
name n4 "l" PAUTO t4 1 "runtime.l" 0 a8
name n5 "l" PAUTO t4 1 "runtime.l" 0 a9
type t5 8 8 0 0 - "int"
name n6 ".autotmp_5" PAUTO t5 3 "runtime..autotmp_5" 0 -
type t6 8 8 8 1 01 "*uint32"
name n7 ".autotmp_6" PAUTO t6 3 "runtime..autotmp_6" 0 -
in n1 0 used
in n2 0 used
in n3 0 used
in n4 0 used
in n5 0 used
in n6 0 used,autotmp
in n7 0 used,autotmp
out n1 0 used
opt n7 0 autotmp
opt n4 0 -
opt n5 0 -
opt n2 0 -
opt n6 0 autotmp
opt n3 0 -
stack 0 0 8
end
genin
posbase p37 "runtime/time.go" 1 1 -1 36 "runtime/time.go" "runtime/time.go" 1 1
sym y1 "runtime.(*timers).unlock" 1
curfn p37:191:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 191 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*timers).unlock.arginfo1" 0
sym y5 "runtime.(*timers).unlock.argliveinfo" 0
sym y6 "internal/runtime/atomic.(*Uint32).Store" 1
inl i2943 - p37:199:14:0:0 y6 "(*Uint32).Store"
posbase p3216 "internal/runtime/atomic/types.go" 1 1 2943 4 "internal/runtime/atomic/types.go" "internal/runtime/atomic/types.go" 1 1
sym y7 "runtime.unlock" 1
inl i2944 - p37:201:8:0:0 y7 "unlock"
posbase p3217 "runtime/lock_spinbit.go" 1 1 2944 71 "runtime/lock_spinbit.go" "runtime/lock_spinbit.go" 1 1
sym y8 "runtime.unlockWithRank" 1
inl i2945 i2944 p3217:270:16:0:0 y8 "unlockWithRank"
posbase p3218 "runtime/lockrank_off.go" 1 1 2945 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
sym y9 "runtime.unlock2" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p37:191:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p37:191:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p37:191:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p37:191:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p37:191:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p37:191:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p37:199:28:1:0
p 7 7 0 0 0 - MOVD 0 MEM/8192/0/0/NONE/0/16/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p37:199:28:1:0
p 8 8 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/32/-/- 8192 - REG/8194/0/0/NONE/0/0/-/- 0 0 p3216:214:10:1:0
p 9 9 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 10 10 0 0 0 - STLRW 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8194/0/0/NONE/0/0/-/- 0 0 p3216:214:7:2:0
p 11 11 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p37:201:8:1:0
p 12 12 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p3217:270:16:1:0
p 13 13 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p3218:36:9:1:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p3218:36:9:1:0
p 15 15 0 0 0 - RET 0 _ 0 - _ 0 0 p37:202:1:0:0
p 16 16 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 191 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 2943
inlmark @11 2944
inlmark @12 2945
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 4
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 4:-10000:4:23:50
dbgregout -
dbgpc 4:23:15
end
asm
sym y10 "runtime.morestack_noctxt" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p37:191:6:0:0
p 17 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p37:191:6:0:0
p 18 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p37:191:6:0:0
p 19 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p37:191:6:0:0
p 20 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@29 0 0 p37:191:6:0:0
p 21 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p37:191:6:0:0
p 22 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p37:191:6:0:1
p 23 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p37:191:6:0:0
p 24 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p37:191:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p37:191:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p37:191:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p37:191:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p37:191:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p37:191:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p37:199:28:1:0
p 7 24 0 0 333 - MOVD 0 MEM/8192/0/0/NONE/86/16/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p37:199:28:1:0
p 8 28 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/32/-/- 8192 - REG/8194/0/0/NONE/2/0/-/- 0 0 p3216:214:10:1:0
p 9 32 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 10 32 0 0 424 - STLRW 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8194/0/0/NONE/77/0/-/- 0 0 p3216:214:7:2:0
p 11 36 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p37:201:8:1:0
p 12 40 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p3217:270:16:1:0
p 13 44 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p3218:36:9:1:0
p 14 44 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p3218:36:9:1:0
p 15 48 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p37:202:1:0:0
p 25 52 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p37:202:1:0:0
p 26 56 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p37:202:1:0:0
p 27 60 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p37:202:1:0:0
p 28 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p37:191:6:0:0
p 29 60 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p37:191:6:0:0
p 30 60 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p37:191:6:0:0
p 31 64 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p37:191:6:0:0
p 32 68 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y10/- 0 0 p37:191:6:0:0
p 33 72 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p37:191:6:0:0
p 34 72 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p37:191:6:0:0
p 35 76 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@17 0 0 p37:191:6:0:0
fn y1 8 24 0 0 191 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
inlmark @7 2943
inlmark @11 2944
inlmark @12 2945
funcaux y2 y3 - - y4 y5 -
text 80 0 900b40f9ff6330eba9010054fe0f1ef8fd831ff8fd2300d1010840f90280009141fc9f881f2003d51f2003d500000094fd835ff8fe0742f8c0035fd6e00700f9e3031eaa00000094e00740f9edffff17 2
reloc 44 4 R_CALLARM64 0 y9
reloc 68 4 R_CALLARM64 0 y10
pcln y15 y16 y17 y18 y11,y12,y13,y14 y2,y3,_,_,_,y4,y5
usedfiles 4,35,36,71
inltree 0 -1 p37:199:14:0:0 y6 "(*Uint32).Store" 24
inltree 1 -1 p37:201:8:0:0 y7 "unlock" 36
inltree 2 1 p3217:270:16:0:0 y8 "unlockWithRank" 40
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y11 SRODATA 11 1 28000 000101020203010c020200 0
data y12 SRODATA 7 1 28000 000b0404030500 0
data y13 SRODATA 0 1 28000 - 0
data y14 SRODATA 5 1 28000 0006040e00 0
data y15 SRODATA 7 1 28000 0204400a3f0600 0
data y16 SRODATA 13 1 28000 4a073f02400146014701020800 0
data y17 SRODATA 21 1 28000 80030610011e0219018a0101d30301cc0203150500 0
data y18 SRODATA 13 1 28000 00070202010104010201050800 0
end
dwarf
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "go:info.runtime.(*timers).unlock$abstract" 0
sym y23 "" 0
posbase p5 "internal/runtime/atomic/types.go" 1 1 -1 4 "internal/runtime/atomic/types.go" "internal/runtime/atomic/types.go" 1 1
posbase p72 "runtime/lock_spinbit.go" 1 1 -1 71 "runtime/lock_spinbit.go" "runtime/lock_spinbit.go" 1 1
posbase p36 "runtime/lockrank_off.go" 1 1 -1 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
sym y24 "go:info.internal/runtime/atomic.(*Uint32).Store$abstract" 0
sym y25 "go:info.runtime.unlock$abstract" 0
sym y26 "go:info.runtime.unlockWithRank$abstract" 0
sym y27 "go:info.*runtime.timers" 0
dwfn y19 y20 y21 y22 y23 "runtime.(*timers).unlock" 36:191 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y22 n1
dwinlfn y6 y24
dwinlfn y7 y25
dwinlfn y8 y26
dwinldcl y6 "u" 0 p5:213:7:0:0
dwinldcl y6 "value" 0 p5:213:24:0:0
dwinldcl y7 "l" 0 p72:269:13:0:0
dwinldcl y8 "l" 0 p36:35:21:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.timers" 0 0 1 p37:191:7:0:0
dwname n7 1 0 1 0 0 0 0 0 - - "*uint32" 0 0 1 p3216:214:7:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p3217:269:13:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p3218:35:21:0:0
dwname n2 1 0 0 1 0 0 0 0 - - "*internal/runtime/atomic.Uint32" 0 0 1 p3216:213:7:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p37:199:25:0:0
dwname n3 1 0 0 1 0 0 0 0 - - "uint32" 0 0 1 p3216:213:24:0:0
var 0 0 "ts" 5 1 0 0 0 8 y27 "runtime/time.go" 191 7 0 0 1 0 v0
scope 0 0 - 0
inlcall 0 2943 36:199 y24 - 1 28:32,32:36 -
inlcall 1 2944 36:201 y25 2 1 40:48 -
inlcall 2 2945 71:270 y26 - 0 44:48 -
dieref y19 2 y22 0
dieoff y22 0:30
data y19 SDWARFFCN 68 0 0 0600000000000050019c29000000000000000009000000000000000025000000c7010009000000000000000025000000c901090000000000000000480000008e02000000 10
reloc 1 4 R_DWARFSECREF 0 y22
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y22
reloc 15 4 R_DWARFSECREF 0 y20
reloc 20 4 R_DWARFSECREF 0 y24
reloc 24 4 R_DWARFSECREF 0 y21
reloc 36 4 R_DWARFSECREF 0 y25
reloc 40 4 R_DWARFSECREF 10 y21
reloc 51 4 R_DWARFSECREF 0 y26
reloc 55 4 R_DWARFSECREF 17 y21
data y20 SDWARFLOC 9 0 0 010000040030015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y21 SDWARFRANGE 24 0 0 010000041c200420240001000004283000010000042c3000 3
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 11 2 R_DWTXTADDR_U2 0 y1
reloc 18 2 R_DWTXTADDR_U2 0 y1
data y23 SDWARFLINES 61 0 0 0009020000000000000000042503b901140a8703038c0405030a3c0637042506037733044803c0003c0424039a7e33042503a1013c0379830214000101 1
reloc 3 8 R_ADDR 0 y1
data y22 SDWARFABSFCN 40 0 1 0572756e74696d652e282a74696d657273292e756e6c6f636b0001bf010122747300000000000000 1
reloc 35 4 R_DWARFSECREF 0 y27
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.(*timers).unlock`. -/
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

/-- The index of `v16`'s `STLRW R1, (R2)` among the Progs (`kdOK` checks it). -/
def jF : Nat := 10

/-- A PC table for `b4` with `v16` (index 5) at its `STLRW` and `v21` after it. -/
def tab : PcTab := [(4, List.replicate 6 10 ++ [11])]

/-- The class map before `v16`: `R1` (`v25`) and `R2` (`v15`) hold 64 bits. -/
def K0 : KMap := (KMap.bot.set! 1 (some 64)).set! 2 (some 64)

def blk : Block := (lc.ctx.f.block? 4).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 16-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1`, the `uint32` `v15` points to (its Phase 1 address `2^41`). -/
def A : BitVec 64 := 0x20000000000

/-- `ι`: the nil block, the globals at `symA`, `heap 1` at `A`. -/
def ι58 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .heap 1 => some 0x20000000000
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `A` and the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := ι58, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The location `v15` (`&ts.len`, a `*uint32`): the start of `heap 1`. -/
def pD : Ptr := ⟨.heap 1, 0⟩

/-- The `int` `v25` (`len(ts.heap)`) the 32-bit store-release stores: a word with a nonzero upper
half. -/
def yIn : BitVec 64 := 0x1122334455667788

/-- The Phase 1 memory before `v16`: `heap 1`, 8 poison bytes. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.replicate 8 .poison })], nextHeap := 2 }

/-- The `runLoc` state before `v16`: `v25` in `R1`, `v15` (`pD`) in `R2`, every other register
`poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 1 then .int .w64 yIn else if i.val = 2 then .ptr pD else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v16`: `X1 = yIn`, `X2 = A`, the activation's `g` and `FP`, the PC of
`v16`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 1 then yIn else if k = 2 then A else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 4 5, mem := fun _ => 0 }

/-- A home in a register (other than `ZR`) has a width class, for every home of `lc`. -/
def homesOK (lc : LocCtx) : Bool :=
  (List.range lc.homes.size).all fun i => match lc.home i with
    | some (.reg r) => r == zeroReg || (cls (lc.ty i)).isSome
    | _ => true

/-- After `v16`: the memory's first block is `heap 1`, with `yIn`'s low byte `0x88` at offset 0
and no pointer word starting at offset 0. -/
def memIs (s : LocState) : Bool :=
  match s.mem with
  | .mem mm =>
    match mm.blocks[0]? with
    | some (b, al) => b == .heap 1 && al.data[0]? == some (.b 0x88) &&
        (ptrWordAt? al.data 0).isNone
    | none => false
  | _ => false

theorem memIs_spec {s : LocState} (h : memIs s = true) :
    ∃ mm al, s.mem = .mem mm ∧ (Blk.heap 1, al) ∈ mm.blocks ∧ al.data[0]? = some (.b 0x88) ∧
      ptrWordAt? al.data 0 = none := by
  unfold memIs at h
  split at h
  · rename_i mm hm
    split at h
    · rename_i b al hba
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
      obtain ⟨⟨rfl, h0⟩, hp⟩ := h
      exact ⟨mm, al, hm, Array.mem_of_getElem? hba, h0, hp⟩
    · cases h
  · cases h

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

/-- `vkind58a` accepts `v16` with a pattern the Prog at `jF` matches. -/
def kdOK : Bool := (patOf (vkind58a lc g (val 16))).any fun pat => (ps[jF]?).any pat.ok

/-- What compiled evaluation checks on `runtime.(*timers).unlock`: it holds an arm64 op; G57's value
check `vkind57` rejects `v16` (`v16: STLRW widths`: the source `v25` is an `int`), which `vkind58a`
accepts with the Prog at `jF`; the Progs have distinct IDs below `2^32` and every register home
has a width class; `checkFrame` passes; `b4` holds `v16` at index 5; no frame variable is accessed
and there is no home slot; the class map `K0` holds `v16`'s reads; and `stepLoc` runs `v16` from
`s0` to a memory with `yIn`'s low byte at `heap 1`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (vkind57 lc g (val 16)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup && homesOK lc &&
    (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.value? 16).isSome && blk.values[5]? == some 16 && (val 16).op == .ARM64STLRW &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    (kReads lc (val 16)).all (fun rc => K0.get rc.1 == some rc.2) &&
    K0.get 1 == some 64 && K0.get 2 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 16)) memIs

theorem g58a4_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (vkind57 lc g (val 16)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧ homesOK lc = true ∧
      checkFrame lc g = .ok () ∧ lc.ctx.f.value? 16 = some (val 16) ∧
      blk.values[5]? = some 16 ∧ (val 16).op = .ARM64STLRW ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      (∀ rc ∈ kReads lc (val 16), K0.get rc.1 = some rc.2) ∧
      K0.get 1 = some 64 ∧ K0.get 2 = some 64 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 16)) memIs = true := by
  have hf := g58a4_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true] at hf
  obtain ⟨hl, h57, hkd, hlt, hnd, hho, hcf, hvs, hi, hop, hav, hsl, hrd, hk1, hk2, hrun⟩ := hf
  refine ⟨hl, h57, hkd, hlt, hnd, hho, ?_, ?_, hi, hop, hav, hsl, hrd, hk1, hk2, hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-- `vkind58a`'s pattern for `v16` and the Prog at `jF` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind58a lc g (val 16) = some (.ok (.prog pat)) ∧ (ps[jF]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

/-- `ι58` puts every block with a Phase 1 address (`nil`, `heap 1`) at it. -/
theorem addrAgree58 : AddrAgree ι58 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι58] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k =>
    simp only [Blk.base?_heap, Option.some.injEq] at hb
    subst hb
    unfold ι58 at ha
    split at ha <;> first | cases ha | skip
    all_goals simp_all
  | _ => simp [ι58] at ha <;> simp [Blk.base?] at hb

theorem clsReg0 {lc : LocCtx} (h : homesOK lc = true) :
    ∀ i r, lc.home i = some (.reg r) → r ≠ zeroReg → (cls (lc.ty i)).isSome = true := by
  intro i r hh hr
  by_cases hi : i < lc.homes.size
  · have := List.all_eq_true.1 h i (List.mem_range.2 hi)
    rw [hh] at this
    simp only [Bool.or_eq_true, beq_iff_eq, hr, false_or] at this
    exact this
  · have hn : lc.home i = none := by
      simp only [LocCtx.home]
      rw [getElem?_neg lc.homes i hi]
      rfl
    rw [hn] at hh
    cases hh

theorem env58 (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32)
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
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree58
            glob := fun _ _ _ _ => rfl
            syms := by
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
    b = .heap 1 ∧ al = { data := Array.replicate 8 .poison } := by
  simpa [mem1] using h

/-- `mem1` injected into the zero memory by `ι58`: `heap 1`'s poison bytes at `A`. -/
theorem memInj1 : MemInj ι58 mem1 (fun _ => 0) where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne _ _
    obtain ⟨rfl, -⟩ := mem1_blocks h
    obtain ⟨rfl, -⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h _ => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    simp [ByteRel]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι58 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    rw [hsp] at h2
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = A := by simp [ι58] at ha; exact ha.symm
    subst ha'
    have hA : A.toNat = 0x20000000000 := rfl
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

/-! ## `v16`: `STLRW R1, (R2)` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 1 ∧ x = .int .w64 yIn) ∨ (r = 2 ∧ x = .ptr pD) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · split at h
      · rename_i _ h2; exact Or.inr (Or.inl ⟨h2, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 4 5 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact .inl rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem inv0 (h1 : K0.get 1 = some 64) (h2 : K0.get 2 = some 64) : G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h1] at hc; cases hc; rfl
    · rw [h2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G58, group A, on `runtime.(*timers).unlock`** (`ts.len.Store(uint32(len(ts.heap)))`, whose
conversion lowering drops, so the 32-bit store-release `v16` (`STLRW v15 v25 v1`, `STLRW R1,
(R2)`) stores the `int` `v25`): `vkind57` rejects it (G32 asks the source of a 32-bit
store-release exactly 32 bits) and `vkind58a` accepts it. From `s0`, with `heap 1` (8
poison bytes) in `R2` and `0x1122334455667788` in `R1`, `stepLoc` runs `v16`, Phase 1's generic
atomic store of the operand fitted to the 32-bit location (`fitPiece`), to a memory with `0x88` at
`heap 1`; `vk58a_step` relates it to a machine state after the `STLRW` whose memory holds `0x88` at
`A`, under an activation extending `E` that is again a `G49Env`. -/
theorem genG58a4_witness :
    (vkind57 lc g (val 16)).toOption = none ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 16) = .ok s1 ∧ s1.mem = .mem mm ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 4 6 m1 ∧ m1.mem (A + BitVec.ofNat 64 0) = 0x88 := by
  obtain ⟨hl, h57, hkd, hlt, hnd, hho, hcf, hv, -, -, hav, hsl, hrd, hk1, hk2, hrun⟩ := facts
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hal, hal0, hpw⟩ := memIs_spec hd
  have hE := env58 hlt hav hsl
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList 0 E :=
    ⟨hl, fun i r hh hr => .inl (clsReg0 hho i r hh hr), hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), addrAgree58⟩
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind58a_spec hvk
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jF (jF + 1) :=
    ⟨jF, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have hj : E.pcOf 4 5 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 4 (5 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := vk58a_step (H := GenG2.H0) (env := GenG2.env)
    (L := []) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0 (inv0 hk1 hk2)
    (fun e he => by cases he) hs1
  -- Byte 0 of `heap 1` after the store, read through `MemInj`: no pointer word covers it.
  have hA : m1.mem (A + BitVec.ofNat 64 0) = 0x88 := by
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
    rw [hd0] at hr
    exact hr.symm
  exact ⟨h57, s1, mm, E1, m1, hs1, hmm, hx1, hE1, hp1, hm1', hA⟩

end GoFV.Proof.Witness.GenG58a4
