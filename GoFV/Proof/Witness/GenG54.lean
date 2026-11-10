import GoFV.Proof.Gen.G54
import GoFV.Proof.Witness.GenG53

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG54

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/%28%2AconsistentHeapStats%29.unsafeClear,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*consistentHeapStats).unsafeClear" 1 0 0
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
type t6 INT64 8 8 0 comparable,named "int64" "int64"
type t7 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t8 ARRAY 544 8 0 comparable "[68]uint64" "[68]uint64" t7 68
type t5 STRUCT 1168 8 0 comparable,named "heapStatsDelta" "runtime.heapStatsDelta" 12
field 0 "committed" t6 0 0
field 1 "released" t6 8 0
field 2 "inHeap" t6 16 0
field 3 "inStacks" t6 24 0
field 4 "inWorkBufs" t6 32 0
field 5 "tinyAllocCount" t7 40 0
field 6 "largeAlloc" t7 48 0
field 7 "largeAllocCount" t7 56 0
field 8 "smallAllocCount" t8 64 0
field 9 "largeFree" t7 608 0
field 10 "largeFreeCount" t7 616 0
field 11 "smallFreeCount" t8 624 0
type t4 ARRAY 3504 8 0 comparable "[3]heapStatsDelta" "[3]runtime.heapStatsDelta" t5 3
type t10 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t9 STRUCT 4 4 0 comparable,named "atomic.Uint32" "internal/runtime/atomic.Uint32" 2
field 0 "noCopy" t10 0 0
field 1 "value" t11 0 0
type t13 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t14 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t12 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t13 0 1
field 1 "key" t14 0 0
type t3 STRUCT 3520 8 0 comparable,named "consistentHeapStats" "runtime.consistentHeapStats" 3
field 0 "stats" t4 0 0
field 1 "gen" t9 3504 0
field 2 "noPLock" t12 3512 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*consistentHeapStats" "*runtime.consistentHeapStats" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*consistentHeapStats) func()" "method(*runtime.consistentHeapStats) func()" 1 0 0
field 0 "m" t2 ? 0
aux a2 sym "runtime.(*consistentHeapStats).unsafeClear" "runtime.(*consistentHeapStats).unsafeClear" 1 - 0 - - - - 0
posbase p33 "runtime/mstats.go" 1 1 -1
aux a3 name "m" "m" PPARAM t2 0 1 used p33:834:7:0:0
aux a1 call "AuxCall{runtime.(*consistentHeapStats).unsafeClear}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t15 BOOL 1 1 0 comparable,named "bool" "bool"
type t16 INT8 1 1 0 comparable,named "int8" "int8"
type t17 INT16 2 2 0 comparable,named "int16" "int16"
type t18 INT32 4 4 0 comparable,named "int32" "int32"
type t19 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t20 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t21 INT 8 8 0 comparable,named "int" "int"
type t22 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t23 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t24 UINT 8 8 0 comparable,named "uint" "uint"
type t25 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t26 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t19
type t27 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t18
type t28 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t29 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t21
type t30 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t14
type t31 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t22
type t32 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t23
type t33 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t26
type t34 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t35 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t36 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t37 SSA ? ? ? - "mem" ""
type t38 SSA ? ? ? - "flags" ""
type t39 SSA ? ? ? - "void" ""
type t40 SSA 16 8 ? - "int128" ""
type t41 RESULTS ? ? ? - "mem" "" 1 t37
type t42 PTR 8 8 8 hasptr,direct,comparable "**consistentHeapStats" "**runtime.consistentHeapStats" t2
type t43 PTR 8 8 8 hasptr,direct,comparable "*[3]heapStatsDelta" "*[3]runtime.heapStatsDelta" t4
type t44 PTR 8 8 8 hasptr,direct,comparable "*heapStatsDelta" "*runtime.heapStatsDelta" t5
type t45 SLICE 24 8 8 hasptr "[]heapStatsDelta" "[]runtime.heapStatsDelta" t5
aux a5 sym "runtime.memclrNoHeapPointers" "runtime.memclrNoHeapPointers" 1 - 0 - - - - 0
aux a4 call "AuxCall{runtime.memclrNoHeapPointers}" a5 1 2 0 8 16 2 0
abiparam in 0 t36 - 0 0
abiparam in 1 t14 - 1 8
slot s1 a3 t2 0 - 0
f b1 t1 a1 35 6
typs Bool=t15,Int8=t16,Int16=t17,Int32=t18,Int64=t6,UInt8=t19,UInt16=t20,UInt32=t11,UInt64=t7,Int=t21,Float32=t22,Float64=t23,UInt=t24,Uintptr=t14,String=t25,BytePtr=t26,Int32Ptr=t27,UInt32Ptr=t28,IntPtr=t29,UintptrPtr=t30,Float32Ptr=t31,Float64Ptr=t32,BytePtrPtr=t33,Complex64=t34,Complex128=t35,UnsafePtr=t36,Mem=t37,Flags=t38,Void=t39,Int128=t40,ResultMem=t41
b b1 Plain p33:835:20:0:0 0 0 - - b2:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v2 SP t14 0 - p0:0:0:0:0 1 -
v v3 SB t14 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t42 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v6 InlMark t39 8178 - p33:835:20:1:0 0 v1
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 b1:0
v v7 Copy t2 0 - p33:837:9:2:0 1 v5
v v8 Copy t37 0 - p33:837:9:2:0 5 v1
v v9 NilCheck t2 0 - p33:837:9:0:0 1 v7,v8
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v8
v v12 Copy t44 0 - p33:837:15:2:0 1 v11
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v12,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v16 Copy t37 0 - p33:837:15:2:0 1 v8
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v16
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v8,v33
v v35 MakeResult t41 0 - p33:838:1:0:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v22 Copy t45 0 - p33:837:7:2:0 2 v19
v v23 SliceLen t21 0 - p33:837:7:0:0 0 v22
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v22
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v26 Copy t36 0 - p33:837:7:2:0 1 v25
v v27 Copy t21 0 - p33:837:7:2:0 1 v20
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v27,v28
v v30 Copy t14 0 - p33:837:7:2:0 1 v29
v v31 Copy t37 0 - p33:837:7:2:0 1 v8
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v26,v30,v31
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5,v7
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev -
freeb -
dcllen 5
end
pass 1 "number lines"
f b1 t1 a1 35 6
b b1 Plain p33:835:20:0:0 0 0 - - b2:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v2 SP t14 0 - p0:0:0:0:0 1 -
v v3 SB t14 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t42 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v6 InlMark t39 8178 - p33:835:20:1:0 0 v1
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 b1:0
v v7 Copy t2 0 - p33:837:9:2:0 1 v5
v v8 Copy t37 0 - p33:837:9:2:0 5 v1
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v7,v8
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v8
v v12 Copy t44 0 - p33:837:15:2:0 1 v11
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v12,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v16 Copy t37 0 - p33:837:15:2:0 1 v8
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v16
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v8,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v22 Copy t45 0 - p33:837:7:2:0 2 v19
v v23 SliceLen t21 0 - p33:837:7:0:0 0 v22
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v22
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v26 Copy t36 0 - p33:837:7:2:0 1 v25
v v27 Copy t21 0 - p33:837:7:2:0 1 v20
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v27,v28
v v30 Copy t14 0 - p33:837:7:2:0 1 v29
v v31 Copy t37 0 - p33:837:7:2:0 1 v8
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v26,v30,v31
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5,v7
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev -
freeb -
cache postorder b5,b6,b3,b4,b2,b1
cache linestarts 33:835:838
dcllen 5
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 35 6
b b1 Plain p33:835:20:0:0 0 0 - - b2:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 10 -
v v2 SP t14 0 - p0:0:0:0:0 1 -
v v3 SB t14 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t42 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p33:834:6:2:0 2 -
v v6 InlMark t39 8178 - p33:835:20:1:0 0 v1
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 b1:0
v v7 Copy t2 0 - p33:837:9:2:0 0 v5
v v8 Copy t37 0 - p33:837:9:2:0 0 v1
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 2 v10,v1
v v12 Copy t44 0 - p33:837:15:2:0 0 v11
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 4 v11,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 3 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v16 Copy t37 0 - p33:837:15:2:0 0 v1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v22 Copy t45 0 - p33:837:7:2:0 0 v19
v v23 SliceLen t21 0 - p33:837:7:0:0 0 v19
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v25 PtrIndex t44 0 - p33:837:7:0:0 2 v24,v14
v v26 Copy t36 0 - p33:837:7:2:0 0 v25
v v27 Copy t21 0 - p33:837:7:2:0 0 v20
v v29 Mul64 t21 0 - p33:837:7:0:0 2 v20,v28
v v30 Copy t14 0 - p33:837:7:2:0 0 v29
v v31 Copy t37 0 - p33:837:7:2:0 0 v1
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v25,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5,v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev -
freeb -
cache postorder b5,b6,b3,b4,b2,b1
cache linestarts 33:835:838
dcllen 5
end
pass 3 "early deadcode"
f b1 t1 a1 35 6
b b1 Plain p33:835:20:1:0 0 0 - - b2:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 b1:0
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v11,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v20,v28
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v25,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev v31,v30,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb -
cache postorder b5,b6,b3,b4,b2,b1
cache linestarts 33:835:838:835=0
dcllen 5
end
pass 4 "short circuit"
f b2 t1 a1 35 6
b b1 BlockInvalid p33:835:20:1:0 0 0 - - - -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v11,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v20,v28
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v25,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev v31,v30,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb -
cache linestarts 33:835:838:835=0
dcllen 5
end
pass 5 "decompose user"
f b2 t1 a1 35 6
b b1 BlockInvalid p33:835:20:1:0 0 0 - - - -
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v11,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v20,v28
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v25,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev v31,v30,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb -
cache linestarts 33:835:838:835=0
dcllen 5
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 35 6
b b2 If p33:837:9:0:0 1 0 - v15 b3:0,b4:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 5 -
v v28 Const64 t21 1168 - p0:0:0:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v15 IsSliceInBounds t15 0 - p33:837:15:0:0 1 v14,v13
b b3 If p33:837:7:0:0 0 0 - v21 b6:0,b5:0 b2:0
v v18 Sub64 t21 0 - p33:837:15:0:0 2 v13,v14
v v19 SliceMake t45 0 - p33:837:15:0:0 2 v11,v18,v18
v v20 SliceLen t21 0 - p33:837:7:0:0 2 v19
v v21 Neq64 t15 0 - p33:837:7:0:0 1 v20,v14
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v25 PtrIndex t44 0 - p33:837:7:0:0 1 v24,v14
v v29 Mul64 t21 0 - p33:837:7:0:0 1 v20,v28
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v25,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13,1168=v28
freev v31,v30,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b1
cache linestarts 33:835:838
dcllen 5
end
pass 7 "opt"
f b2 t1 a1 35 6
b b2 First p33:837:9:0:0 1 0 - - b3:0,b4:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 1 -
v v14 Const64 t21 0 - p0:0:0:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
b b3 First p33:837:7:0:0 0 0 - - b6:0,b5:0 b2:0
v v18 Const64 t21 3 - p33:837:15:0:0 2 -
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v18,v18
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13
freev v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b1
cache linestarts 33:835:838
dcllen 5
end
pass 8 "zero arg cse"
f b2 t1 a1 35 6
b b2 First p33:837:9:0:0 1 0 - - b3:0,b4:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 5 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 3 -
v v14 Const64 t21 0 - p0:0:0:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
b b3 First p33:837:7:0:0 0 0 - - b6:0,b5:0 b2:0
v v18 Const64 t21 3 - p33:837:15:0:0 0 -
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b4 Exit p33:837:9:0:0 0 0 - v17 - b2:1
v v17 PanicBounds t37 6 - p33:837:15:0:0 1 v14,v13,v1
b b5 Ret p33:838:1:0:0 0 0 - v35 - b3:1,b6:0
v v34 Phi t37 0 - p33:838:1:0:0 1 v1,v33
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v34
b b6 Plain p33:837:7:0:0 0 0 - - b5:1 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v14,3=v13
freev v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b1
cache linestarts 33:835:838
dcllen 5
end
pass 9 "opt deadcode"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache linestarts 33:835:838
dcllen 5
end
pass 10 "generic cse"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 11 "phiopt"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 12 "gcse deadcode"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 NilCheck t43 0 - p33:837:15:0:0 1 v10,v1
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 13 "nilcheckelim"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v11 Copy t43 0 - p33:837:15:0:0 1 v10
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 14 "prove"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v11 Copy t43 0 - p33:837:15:0:0 1 v10
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v11,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 15 "divisible"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v11,v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 16 "divmod"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v11,v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 17 "middle opt"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v11,v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 18 "known bits"
f b2 t1 a1 35 6
b b2 Plain p33:837:9:0:0 0 0 - - b3:0 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
b b3 Plain p33:837:7:0:0 0 0 - - b6:0 b2:0
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
b b5 Ret p33:838:1:0:0 0 0 - v35 - b6:0
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 Plain p33:837:7:0:0 0 0 - - b5:0 b3:0
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v11,v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5,b6,b3,b2
cache idom b2:-,b3:b2,b5:b6,b6:b3
cache sdom b2:-:b3:-:2:23,b3:b2:b6:-:5:20,b5:b6:-:-:11:14,b6:b3:b5:-:8:17
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 19 "early fuse"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p33:834:6:2:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticLECall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3=v13
freev v11,v34,v17,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 20 "expand calls"
aux a6 nameoff "m+0" a3 0
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v19 SliceMake t45 0 - p33:837:15:0:0 1 v10,v13,v13
v v24 SlicePtr t44 0 - p33:837:7:0:0 1 v19
v v32 StaticCall t41 16 a4 p33:837:7:0:0 1 v24,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
v v11 SB t14 0 - p0:0:0:0:0 0 -
v v34 SP t14 0 - p0:0:0:0:0 1 -
v v17 OffPtr t42 0 - p0:0:0:0:0 0 v34
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v17,3=v13
freev v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 21 "decompose builtin"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 2 v9
v v19 SliceMake t45 0 - p33:837:15:0:0 0 v10,v13,v13
v v32 StaticCall t41 16 a4 p33:837:7:0:0 1 v10,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
v v11 SB t14 0 - p0:0:0:0:0 0 -
v v34 SP t14 0 - p0:0:0:0:0 1 -
v v17 OffPtr t42 0 - p0:0:0:0:0 0 v34
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v17,3=v13
freev v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 22 "softfloat"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 2 v9
v v19 SliceMake t45 0 - p33:837:15:0:0 0 v10,v13,v13
v v32 StaticCall t41 16 a4 p33:837:7:0:0 1 v10,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
v v11 SB t14 0 - p0:0:0:0:0 0 -
v v34 SP t14 0 - p0:0:0:0:0 1 -
v v17 OffPtr t42 0 - p0:0:0:0:0 0 v34
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v17,3=v13
freev v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 23 "branchelim"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v13 Const64 t21 3 - p0:0:0:0:0 2 -
v v29 Const64 t21 3504 - p33:837:7:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 2 v9
v v19 SliceMake t45 0 - p33:837:15:0:0 0 v10,v13,v13
v v32 StaticCall t41 16 a4 p33:837:7:0:0 1 v10,v29,v1
v v33 SelectN t37 0 - p33:837:7:0:0 1 v32
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
v v11 SB t14 0 - p0:0:0:0:0 0 -
v v34 SP t14 0 - p0:0:0:0:0 1 -
v v17 OffPtr t42 0 - p0:0:0:0:0 0 v34
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v17,3=v13
freev v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 24 "late opt"
aux a7 type "uint8" t19
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 25 "dead auto elim"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 26 "sccp"
f b5 t1 a1 35 6
b b2 BlockInvalid p33:837:9:0:0 0 0 - - - -
b b3 BlockInvalid p33:837:7:0:0 0 0 - - - -
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
b b6 BlockInvalid p33:837:7:0:0 0 0 - - - -
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 27 "generic deadcode"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 28 "late fuse"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 29 "check bce"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 30 "dse"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 31 "memcombine"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 32 "writebarrier"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 NilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v10 OffPtr t43 0 - p33:837:9:0:0 1 v9
v v33 Zero t37 3504 a7 p33:837:7:0:0 1 v10,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 33 "lower"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 34 "addressing modes"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 35 "late lower"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 36 "pair"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache auxmap a3:1,-:2
cache linestarts 33:835:838
dcllen 5
end
pass 38 "lowered cse"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 39 "elim unread autos"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 40 "tighten tuple selectors"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 41 "lowered deadcode"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 42 "checkLower"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 43 "loop invariant"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 44 "late phielim and copyelim"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 45 "tighten"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 46 "late deadcode"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 47 "critical"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 48 "phi tighten"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 49 "likelyadjust"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
dcllen 5
end
pass 50 "layout"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v9 ARM64LoweredNilCheck t2 0 - p33:837:9:1:0 1 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v9,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 2 -
v v1 InitMem t37 0 - p0:0:0:0:0 2 -
v v9 ARM64LoweredNilCheck t39 0 - p33:837:9:1:0 0 v5,v1
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:0:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 1 -
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:1:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 1 -
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:1:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v10,v17,v34,v11,v32,v19,v29,v13,v24,v18,v14,v30,v31,v25,v21,v20,v15,v28,v27,v26,v23,v22,v16,v12,v8,v7,v6,v4,v3,v2
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 1 -
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:1:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v34
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
regalloc 6 v5:R0
tempregs v33:R1
dcllen 5
end
pass 55 "loop rotate"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 1 -
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:1:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v34
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
regalloc 6 v5:R0
tempregs v33:R1
dcllen 5
end
pass 56 "trim"
f b5 t1 a1 35 6
b b5 Ret p33:838:1:0:0 0 0 - v35 - -
v v5 ArgIntReg t2 0 a6 p33:838:1:0:0 1 -
v v1 InitMem t37 0 - p0:0:0:0:0 1 -
v v33 ARM64LoweredZeroLoop t37 3504 - p33:837:7:1:0 1 v5,v1
v v35 MakeResult t41 0 - p33:838:1:1:0 1 v33
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v10,v11,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21,v22,v23,v24,v25,v26,v27,v28,v29,v30,v31,v32,v34
freeb b6,b3,b2,b4,b1
cache postorder b5
cache idom b5:-
cache sdom b5:-:-:-:2:5
cache loopnest 7 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 33:835:838
fstate scheduled,laidout
regalloc 6 v5:R0
tempregs v33:R1
dcllen 5
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t30,t33,t34,t35,t36
typelink t37=t41
typeorder t16,t19,t17,t20,t18,t11,t6,t7,t21,t24,t14,t34,t35,t22,t23,t15,t26,t27,t28,t29,t30,t31,t32,t33,t42,t43,t44,t2,t1,t45,t4,t8,t12,t9,t10,t5,t13,t3,t25,t36,t37,t39,t38,t40,t41
eof
"#

/-- `std/std/runtime/%28%2AconsistentHeapStats%29.unsafeClear,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*consistentHeapStats).unsafeClear" 1
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
type t1 8 8 8 1 01 "*consistentHeapStats"
name n1 "m" PPARAM t1 1 "runtime.m" 0 a3
type t2 24 8 8 1 01 "[]heapStatsDelta"
name n2 ".autotmp_1" PAUTO t2 3 "runtime..autotmp_1" 0 -
type t3 8 8 0 0 - "int"
name n3 ".autotmp_2" PAUTO t3 3 "runtime..autotmp_2" 0 -
type t4 8 8 8 1 01 "unsafe.Pointer"
name n4 ".autotmp_3" PAUTO t4 3 "runtime..autotmp_3" 0 -
type t5 8 8 0 0 - "uintptr"
name n5 ".autotmp_4" PAUTO t5 3 "runtime..autotmp_4" 0 -
in n1 0 used
in n2 0 used,autotmp
in n3 0 used,autotmp
in n4 0 used,autotmp
in n5 0 used,autotmp
out n1 0 used
opt n2 0 autotmp
opt n4 0 autotmp
opt n3 0 autotmp
opt n5 0 autotmp
stack 0 0 8
end
genin
posbase p33 "runtime/mstats.go" 1 1 -1 32 "runtime/mstats.go" "runtime/mstats.go" 1 1
sym y1 "runtime.(*consistentHeapStats).unsafeClear" 1
curfn p33:834:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 834 200080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*consistentHeapStats).unsafeClear.arginfo1" 0
sym y5 "runtime.(*consistentHeapStats).unsafeClear.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p33:834:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p33:834:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p33:834:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p33:834:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p33:834:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p33:834:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p33:837:7:1:0
p 7 7 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/54/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p33:837:7:1:0
p 8 8 0 0 0 - STP 32 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p33:837:7:2:0
p 9 9 0 0 0 - STP 32 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p33:837:7:2:0
p 10 10 0 0 0 - STP 32 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p33:837:7:2:0
p 11 11 0 0 0 - STP 32 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p33:837:7:2:0
p 12 12 0 0 0 - SUB 0 CONST/0/0/0/NONE/0/1/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p33:837:7:2:0
p 13 13 0 0 0 - CBNZ 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@8 0 0 p33:837:7:2:0
p 14 14 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p33:837:7:2:0
p 15 15 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/16/-/- 0 0 p33:837:7:2:0
p 16 16 0 0 0 - STP 0 REGREG/8223/0/0/NONE/0/8223/-/- 0 - MEM/8192/0/0/NONE/0/32/-/- 0 0 p33:837:7:2:0
p 17 17 0 0 0 - RET 0 _ 0 - _ 0 0 p33:838:1:0:0
p 18 18 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 834 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 5
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 5:-10000:-1:-30000:50
dbgregout -
dbgpc -
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p33:834:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p33:834:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p33:834:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p33:834:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p33:834:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p33:834:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p33:837:7:1:0
p 7 0 0 0 318 - MOVD 0 CONST/0/0/0/NONE/18/54/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p33:837:7:1:0
p 8 4 0 0 437 - STP 32 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p33:837:7:2:0
p 9 8 0 0 437 - STP 32 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p33:837:7:2:0
p 10 12 0 0 437 - STP 32 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p33:837:7:2:0
p 11 16 0 0 437 - STP 32 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p33:837:7:2:0
p 12 20 0 0 30 - SUB 0 CONST/0/0/0/NONE/17/1/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p33:837:7:2:0
p 13 24 0 0 85 - CBNZ 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/8/-/@8 0 0 p33:837:7:2:0
p 14 28 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p33:837:7:2:0
p 15 32 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/16/-/- 0 0 p33:837:7:2:0
p 16 36 0 0 436 - STP 0 REGREG/8223/0/0/NONE/7/8223/-/- 0 - MEM/8192/0/0/NONE/86/32/-/- 0 0 p33:837:7:2:0
p 17 40 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p33:838:1:0:0
fn y1 8 0 0 0 834 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 48 0 c10680d21f7c81a81f7c81a81f7c81a81f7c81a8210400d161ffffb51f7c00a91f7c01a91f7c02a9c0035fd600000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 32
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010c00 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040c00 0
data y10 SRODATA 3 1 28000 020c00 0
data y11 SRODATA 3 1 28000 420c00 0
data y12 SRODATA 6 1 28000 8c0d0a020200 0
data y13 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.*runtime.consistentHeapStats" 0
dwfn y14 y15 y16 - y17 "runtime.(*consistentHeapStats).unsafeClear" 32:834 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.consistentHeapStats" 0 0 1 p33:834:7:0:0
dwname n2 1 0 1 0 0 0 0 0 - - "[]runtime.heapStatsDelta" 0 0 1 p33:837:15:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p33:837:7:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p33:837:7:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p33:837:7:0:0
var 0 0 "m" 5 1 0 0 0 8 y18 "runtime/mstats.go" 834 7 0 0 0 0 v0
scope 0 0 - 0
data y14 SDWARFFCN 71 0 0 0372756e74696d652e282a636f6e73697374656e74486561705374617473292e756e73616665436c65617200000030019c21000000c206012d6d0000c206000000000000000000 3
reloc 44 2 R_DWTXTADDR_U2 0 y1
reloc 62 4 R_DWARFSECREF 0 y18
reloc 66 4 R_DWARFSECREF 0 y15
data y15 SDWARFLOC 9 0 0 010000040030015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 27 0 0 0009020000000000000000042103bf061406370608880208000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.(*consistentHeapStats).unsafeClear`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G54's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG54` gives (`b5`: `v33`'s Progs from 5, after the `PCDATA`s at 5 and 6 its
`MOVD $54, R1` at 7, the loop to the `CBNZ` at 13, the tail's three `STP`s; the `RET` at 17). -/
def tab : PcTab := [(5, [5, 5, 5, 17, 17])]

/-- The class table `checkG54` gives. -/
def kt : KTab := (match checkG54 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 5).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1`, the zeroed block (its Phase 1 address `2^41`). -/
def A : BitVec 64 := 0x20000000000

/-- `ι`: the nil block, the globals at `symA`, `heap 1` at `A`. -/
def ι54 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .heap 1 => some 0x20000000000
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the heap object at `A` and the PC table of `checkG54`. -/
def E : MatchEnv :=
  { lc, ι := ι54, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The pointer `m` (`v5`): the start of `heap 1`. -/
def pD : Ptr := ⟨.heap 1, 0⟩

/-- The Phase 1 memory before `v33`: `heap 1`, 3504 poison bytes. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.replicate 3504 .poison })], nextHeap := 2 }

/-- The machine memory before `v33`: 1 at the last of the 3504 bytes (so the zeroing is
visible there), 0 elsewhere. -/
def M1 : Memory := fun y => if y = A + 3503 then 1 else 0

/-- The `runLoc` state before `v33`: `m` (`pD`, `v5`) in `R0`, every other register `poison`, the
memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pD else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v33`: `X0 = A`, the activation's `g` and `FP`, the PC of `v33`, the memory
`M1`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 5 2, mem := M1 }

/-- The zeroing is valid: `mem1` has 3504 writable bytes at `pD`. -/
def zeroOK : Bool := (mem1.write pD (Array.replicate 3504 (.b 0))).isSome

theorem zeroOK_spec (h : zeroOK = true) :
    ∃ mm', mem1.write pD (Array.replicate 3504 (.b 0)) = some mm' :=
  Option.isSome_iff_exists.1 h

/-- After the zeroing: the memory holds 3504 zero bytes at `pD`, and its first block is `heap 1`,
whose last byte is 0 and starts no pointer word. -/
def dstIs (s : LocState) : Bool :=
  match s.mem with
  | .mem mm => mm.read pD 3504 == some (Array.replicate 3504 (.b 0)) &&
      match mm.blocks[0]? with
      | some (b, al) => b == .heap 1 && al.data[3503]? == some (.b 0) &&
          (ptrWordAt? al.data 3503).isNone && (ptrWordAt? al.data 3502).isNone &&
          (ptrWordAt? al.data 3501).isNone && (ptrWordAt? al.data 3500).isNone &&
          (ptrWordAt? al.data 3499).isNone && (ptrWordAt? al.data 3498).isNone &&
          (ptrWordAt? al.data 3497).isNone && (ptrWordAt? al.data 3496).isNone
      | none => false
  | _ => false

theorem dstIs_spec {s : LocState} (h : dstIs s = true) :
    ∃ mm al, s.mem = .mem mm ∧ mm.read pD 3504 = some (Array.replicate 3504 (.b 0)) ∧
      (Blk.heap 1, al) ∈ mm.blocks ∧ al.data[3503]? = some (.b 0) ∧
      ∀ o, 3496 ≤ o → o ≤ 3503 → ptrWordAt? al.data o = none := by
  unfold dstIs at h
  split at h
  · rename_i mm hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i b al hba
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h2
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨rfl, h3⟩, p0⟩, p1⟩, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩ := h2
      refine ⟨mm, al, hm, h1, Array.mem_of_getElem? hba, h3, fun o h1 h2 => ?_⟩
      have : o = 3496 ∨ o = 3497 ∨ o = 3498 ∨ o = 3499 ∨ o = 3500 ∨ o = 3501 ∨ o = 3502 ∨
          o = 3503 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
    · cases h2
  · cases h

/-- What compiled evaluation checks on `runtime.(*consistentHeapStats).unsafeClear`: it holds an
arm64 op; `checkG54` accepts it with `tab` and `kt` and `checkG53` does not; it accesses no frame
variable and has no home slot; `b5` holds `v33` (`LoweredZeroLoop [3504] v5 v1`) at index 2, where
`R0` has class 64 and G35's table is empty; in `s0` the pointer reads as the word `A` (a lowered
function reads pointers as their addresses), the address of `pD`, where the zeroing of 3504
bytes is valid; `stepLoc` runs `v33` from `s0` to a memory holding 3504 zeros at `pD`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG54 lc0 ps bs g).toOption == some (tab, kt) && (checkG53 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 5 && (lc.ctx.f.block? 5).isSome &&
    (lc.ctx.f.value? 33).isSome && blk.values[2]? == some 33 &&
    (val 33).op == .ARM64LoweredZeroLoop && (val 33).args[0]? == some 5 &&
    (val 33).auxInt.toInt.toNat == 3504 &&
    (kAt lc kt 5 blk 2).get 0 == some 64 &&
    uL35 lc (uIn35 lc 5) blk 2 == [] &&
    GenG1.okThen (s0.read lc 5) (GenG53.isW A) &&
    Arm64.addr (.int .w64 A) 0 == some pD && zeroOK &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 33)) dstIs

theorem g54_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG54 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG53 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      5 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 5 = some blk ∧
      lc.ctx.f.value? 33 = some (val 33) ∧ blk.values[2]? = some 33 ∧
      (val 33).op = .ARM64LoweredZeroLoop ∧ (val 33).args[0]? = some 5 ∧
      (val 33).auxInt.toInt.toNat = 3504 ∧
      (kAt lc kt 5 blk 2).get 0 = some 64 ∧
      uL35 lc (uIn35 lc 5) blk 2 = [] ∧
      GenG1.okThen (s0.read lc 5) (GenG53.isW A) = true ∧
      Arm64.addr (.int .w64 A) 0 = some pD ∧
      zeroOK = true ∧ GenG1.okThen (stepLoc GenG2.env lc s0 (val 33)) dstIs = true := by
  have hf := g54_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h53, hav, hsl, hm1, hbs, hvs, hi2, hop, ha0, hn, hk0, hu2, hr5, hpd, hz,
    hrun⟩ := hf
  refine ⟨hl, ?_, h53, hav, hsl, hm1, ?_, ?_, hi2, hop, ha0, hn, hk0, hu2, hr5, hpd, hz, hrun⟩
  · revert hres; cases checkG54 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

/-- `ι54` puts every block with a Phase 1 address (`nil`, `heap 1`) at it. -/
theorem addrAgree54 : AddrAgree ι54 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι54] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k =>
    simp only [Blk.base?_heap, Option.some.injEq] at hb
    subst hb
    unfold ι54 at ha
    split at ha <;> first | cases ha | skip
    all_goals simp_all
  | _ => simp [ι54] at ha <;> simp [Blk.base?] at hb

theorem g54Env (hc : checkG54 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -⟩ :=
                checkG54L_spec hl (checkG54_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree54
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -⟩ :=
                checkG54L_spec hl (checkG54_spec hc).2
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
    b = .heap 1 ∧ al = { data := Array.replicate 3504 .poison } := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `ι54`: `heap 1`'s poison bytes at `A`. -/
theorem memInj1 : MemInj ι54 mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    simp [ByteRel]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι54 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    rw [hsp] at h2
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = A := by simp [ι54] at ha; exact ha.symm
    subst ha'
    have hA : A.toNat = 0x20000000000 := rfl
    simp only [hA, Array.size_replicate]
    omega
  · cases hk

/-! ## `v33`: `LoweredZeroLoop [3504] v5 v1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pD) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 5 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E]; decide,
    by simp only [MState.word, readMem, m0, M1, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g54Inv0 (h0 : (kAt lc kt 5 blk 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 5 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G51 and `Pre53a` on `v33`, `LoweredZeroLoop`: none of them
applies. -/
theorem pre53 (hop : (val 33).op = .ARM64LoweredZeroLoop) : G53Pre lc s0 (val 33) := by
  have hne : ∀ o : Op, o ≠ .ARM64LoweredZeroLoop → (val 33).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩
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
  · intro h; exact absurd h (hne _ (by decide))

/-- `Pre54a` on `v33`: `mem1` has the 3504 bytes to zero at `pD`. -/
theorem pre54a (ha0 : (val 33).args[0]? = some 5) (hn : (val 33).auxInt.toInt.toNat = 3504)
    (hr5 : GenG1.okThen (s0.read lc 5) (GenG53.isW A) = true)
    (hpd : Arm64.addr (.int .w64 A) 0 = some pD) (hz : zeroOK = true) :
    Pre54a lc s0 (val 33) := by
  intro _ a x ha hx
  rw [ha0] at ha
  cases ha
  obtain ⟨x', hx', hpx⟩ := GenG1.okThen_spec hr5
  rw [hx] at hx'
  cases hx'
  rw [GenG53.isW_spec hpx]
  obtain ⟨mm', hw⟩ := zeroOK_spec hz
  exact ⟨pD, mem1, mm', hpd, rfl, by rw [hn]; exact hw⟩

/-- **G54 on `runtime.(*consistentHeapStats).unsafeClear`** (`func (m *consistentHeapStats)
unsafeClear() { clear(m.stats[:]) }`, which on arm64 zeroes the 3504 bytes of `m.stats` with
`LoweredZeroLoop`): `b5` zeroes them (`v33`, `LoweredZeroLoop [3504] v5 v1`, `m` in `R0`, the
counter the temporary `R1`) with 54 iterations of four `STP.P` and a tail of three `STP`s, which
`checkG53` rejects (`v33: temporary register`) and `checkG54` accepts. From `s0`, with `heap 1`
(3504 poison bytes) in `R0`, `stepLoc` runs `v33` to a memory holding 3504 zeros at `pD`, and
`g54_value` relates it to a machine state after `v33`'s code (the loop run to its end) whose
memory holds 0 at the last of the 3504 bytes, `A + 3503`, where `M1` held 1, under an activation
extending `E` that is again a `G49Env`. -/
theorem genG54_witness :
    (checkG53 lc0 ps bs g).toOption = none ∧ M1 (A + 3503) = 1 ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 33) = .ok s1 ∧ s1.mem = .mem mm ∧
        mm.read pD 3504 = some (Array.replicate 3504 (.b 0)) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 5 3 m1 ∧ m1.mem (A + 3503) = 0 := by
  obtain ⟨hl, hc, h53, hav, hsl, hm1, hb, hv33, hi2, hop, ha0, hn, hk0, hu2, hr5, hpd, hz,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hrd, hal, hal0, hpw⟩ := dstIs_spec hd
  have hE := g54Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64LoweredZeroLoop → (val 33).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g54_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 5 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 5 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 33 = some (val 33) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv33
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g54_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g54Inv0 hk0)
    (by change UOKL m0 (uL35 lc (uIn35 lc 5) blk 2); rw [hu2]; intro e he; cases he)
    ⟨pre53 hop, pre54a ha0 hn hr5 hpd hz, fun h => absurd h (hne _ (by decide))⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  -- The last byte of `heap 1` after the zeroing, read through `MemInj`: no pointer word covers it.
  have hA : m1.mem (A + 3503) = 0 := by
    obtain ⟨mm1, hmm1, hinj⟩ := hm1'.mem
    rw [hmm] at hmm1
    cases hmm1
    obtain ⟨W, hW⟩ := hinj.bytes
    obtain ⟨hw, -, hby⟩ := hW _ _ _ hal (hx1.2 (.heap 1) A rfl)
    obtain ⟨h0, hd0⟩ := Array.getElem?_eq_some_iff.1 hal0
    have hr := hby 3503 h0 (fun o ho ho' => by
      obtain ⟨p, hp, -⟩ := hw o ho
      rw [hpw o (by omega) (by omega)] at hp
      cases hp)
    rw [hd0, show A + BitVec.ofNat 64 3503 = A + 3503 by decide] at hr
    exact hr.symm
  exact ⟨h53, rfl, s1, mm, E1, m1, hs1, hmm, hrd, hx1, hE1, hp1, hm1', hA⟩

end GoFV.Proof.Witness.GenG54
