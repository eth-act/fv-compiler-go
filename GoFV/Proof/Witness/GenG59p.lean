import GoFV.Gen.Check58
import GoFV.Proof.Gen.G59p
import GoFV.Proof.Witness.GenG2
import GoFV.SSA.Sem.TyEq

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG59p

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/zerodivide/main/init.func33,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "init.func33" 1 0 0
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
aux a2 sym "main.init.func33" "main.init.func33" 1 - 0 - - - - 0
aux a1 call "AuxCall{main.init.func33}" a2 1 0 0 8 0 0 0
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
posbase p2 "./zerodivide.go" 1 1 -1
type t33 PTR 8 8 8 hasptr,direct,comparable "*complex128" "*complex128" t26
aux a3 sym "main.c" "main.c" 0 - 0 - - - - 0
aux a4 sym "main.d" "main.d" 0 - 0 - - - - 0
type t34 RESULTS ? ? ? - "complex128,mem" "" 2 t26,t28
aux a6 sym "runtime.complex128div" "runtime.complex128div" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.complex128div}" a6 1 2 1 8 32 4 2
abiparam in 0 t26 - 16,17 0
abiparam in 1 t26 - 18,19 16
abiparam out 0 t26 - 16,17 -1
aux a7 name ".autotmp_1" ".autotmp_1" PAUTO t26 0 3 addrtaken,used,autotmp p2:160:42:0:0
aux a8 type "complex128" t26
aux a9 sym "type:complex128" "type:complex128" 0 - 0 - t26 - - 0
rtype 16 0 -1988686580 16 "runtime.gcbits." ""
type t35 RESULTS ? ? ? - "unsafe.Pointer,mem" "" 2 t27,t28
aux a11 sym "runtime.convTnoptr" "runtime.convTnoptr" 1 - 0 - - - - 0
type t37 UINT8 1 1 0 comparable,named "byte" "uint8"
type t36 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t37
aux a10 call "AuxCall{runtime.convTnoptr}" a11 1 2 1 8 16 2 1
abiparam in 0 t36 - 0 0
abiparam in 1 t33 - 1 8
abiparam out 0 t27 - 0 -1
type t38 INTER 16 8 16 hasptr,comparable,emptyiface "interface {}" "interface {}"
type t39 PTR 8 8 8 hasptr,direct,comparable "*interface {}" "*interface {}" t38
aux a12 sym "main.tmp" "main.tmp" 0 - 0 - - - - 0
posbase p43 "./zerodivide.go" 1 1 31
aux a13 type "uintptr" t15
aux a14 type "*uint8" t17
aux a15 name "v" "v" PAUTO t38 0 1 used p43:110:10:0:0
slot s1 a15 t38 0 - 0
f b1 t1 a1 28 2
typs Bool=t2,Int8=t3,Int16=t4,Int32=t5,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Plain p2:160:39:0:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:0:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:1:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:0:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
b b2 Ret p2:160:47:0:0 0 0 - v28 - b1:0
v v27 Copy t28 0 - p2:160:47:2:0 1 v26
v v28 MakeResult t32 0 - p2:160:47:0:0 1 v27
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 28 2
b b1 Plain p2:160:39:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
b b2 Ret p2:160:47:0:0 0 0 - v28 - b1:0
v v27 Copy t28 0 - p2:160:47:2:0 1 v26
v v28 MakeResult t32 0 - p2:160:47:0:0 1 v27
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 28 2
b b1 Plain p2:160:39:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 2 v25,v24,v23
b b2 Ret p2:160:47:0:0 0 0 - v28 - b1:0
v v27 Copy t28 0 - p2:160:47:2:0 0 v26
v v28 MakeResult t32 0 - p2:160:47:0:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev -
freeb -
cache postorder b2,b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 28 2
b b1 Plain p2:160:39:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
b b2 Ret p2:160:47:0:0 0 0 - v28 - b1:0
v v28 MakeResult t32 0 - p2:160:47:0:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb -
cache postorder b2,b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 4 "short circuit"
f b2 t1 a1 28 2
b b1 BlockInvalid p2:160:39:1:0 0 0 - - - -
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb -
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 5 "decompose user"
f b2 t1 a1 28 2
b b1 BlockInvalid p2:160:39:1:0 0 0 - - - -
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb -
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 7 "opt"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 8 "zero arg cse"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 9 "opt deadcode"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 1 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v14,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 1 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v18,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 10 "generic cse"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 0 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 0 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 11 "phiopt"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 2 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v14 LocalAddr t33 0 a7 p2:160:42:2:0 0 v2,v12
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v18 Addr t17 0 a9 p0:0:0:0:0 0 v3
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 12 "gcse deadcode"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 13 "nilcheckelim"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 14 "prove"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 15 "divisible"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 16 "divmod"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 17 "middle opt"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 18 "known bits"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 19 "early fuse"
f b2 t1 a1 28 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 1 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 1 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticLECall t34 32 a5 p2:160:42:0:0 2 v5,v7,v1
v v9 SelectN t28 1 - p2:160:42:0:0 2 v8
v v10 SelectN t26 0 - p2:160:42:0:0 1 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticLECall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev v18,v14,v27
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 20 "expand calls"
type t40 RESULTS ? ? ? - "float64,float64,mem" "" 3 t13,t13,t28
f b2 t1 a1 31 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 1 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 1 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 Load t26 0 - p2:160:42:1:0 2 v4,v1
v v7 Load t26 0 - p2:160:42:0:0 2 v6,v1
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:0:0 3 v27,v29,v30,v31,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v10 ComplexMake t26 0 - p2:160:42:2:0 1 v18,v14
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 2 v2,v9
v v12 Store t28 0 a8 p2:160:42:2:0 1 v11,v10,v9
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v19 IMake t38 0 - p2:160:42:0:0 2 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v22 ITab t17 0 - p43:111:6:0:0 1 v19
v v24 IData t17 0 - p43:111:6:0:0 1 v19
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v22,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v24,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v27 ComplexReal t13 0 - p2:160:42:0:0 1 v5
v v29 ComplexImag t13 0 - p2:160:42:2:0 1 v5
v v30 ComplexReal t13 0 - p2:160:42:0:0 1 v7
v v31 ComplexImag t13 0 - p2:160:42:2:0 1 v7
names s1
named s1 v19
splits -
canon a15/t38/0/-/0=s1
consts -
freev -
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 3
end
pass 21 "decompose builtin"
aux a16 type "float64" t13
aux a17 name "v.type" "v.type" PAUTO t15 0 3 used p43:110:10:0:0
slot s2 a17 t15 0 s1 0
aux a18 name "v.data" "v.data" PAUTO t17 0 3 used p43:110:10:0:0
slot s3 a18 t17 0 s1 8
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 3 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 ComplexMake t26 0 - p2:160:42:1:0 0 v32,v33
v v7 ComplexMake t26 0 - p2:160:42:0:0 0 v35,v36
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:0:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v10 ComplexMake t26 0 - p2:160:42:2:0 0 v18,v14
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v19 IMake t38 0 - p2:160:42:0:0 0 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 2 v8
v v14 SelectN t13 1 - p2:160:42:2:0 2 v8
v v32 Load t13 0 - p2:160:42:1:0 2 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 2 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 2 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 2 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 22 "softfloat"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 3 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 ComplexMake t26 0 - p2:160:42:1:0 0 v32,v33
v v7 ComplexMake t26 0 - p2:160:42:0:0 0 v35,v36
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:0:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v10 ComplexMake t26 0 - p2:160:42:2:0 0 v18,v14
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v19 IMake t38 0 - p2:160:42:0:0 0 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 2 v8
v v14 SelectN t13 1 - p2:160:42:2:0 2 v8
v v32 Load t13 0 - p2:160:42:1:0 2 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 2 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 2 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 2 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 23 "branchelim"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 3 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v5 ComplexMake t26 0 - p2:160:42:1:0 0 v32,v33
v v7 ComplexMake t26 0 - p2:160:42:0:0 0 v35,v36
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:0:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v10 ComplexMake t26 0 - p2:160:42:2:0 0 v18,v14
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v19 IMake t38 0 - p2:160:42:0:0 0 v13,v17
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 2 v8
v v14 SelectN t13 1 - p2:160:42:2:0 2 v8
v v32 Load t13 0 - p2:160:42:1:0 2 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 2 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 2 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 2 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 24 "late opt"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 25 "dead auto elim"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 26 "sccp"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 27 "generic deadcode"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 28 "late fuse"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 29 "check bce"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 30 "dse"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 31 "memcombine"
f b2 t1 a1 39 2
b b2 Ret p2:160:47:0:0 0 0 - v28 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 1 v21
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v17 SelectN t27 0 - p2:160:42:0:0 1 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 1 v21,v13,v16
v v26 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v23
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v19,v10,v7,v5,v31,v30,v29,v27,v24,v22
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 32 "writebarrier"
aux a19 sym "runtime.writeBarrier" "runtime.writeBarrier" 0 - 0 - - - - 0
type t41 TUPLE ? ? ? - "*uintptr,mem" "" t21 t28
f b2 t1 a1 43 3
b b2 If p43:111:6:0:0 -1 0 - v5 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 Addr t33 0 a3 p0:0:0:0:0 2 v3
v v6 Addr t33 0 a4 p0:0:0:0:0 2 v3
v v13 Addr t17 0 a9 p0:0:0:0:0 2 v3
v v21 Addr t39 0 a12 p0:0:0:0:0 2 v3
v v25 OffPtr t24 8 - p43:111:6:0:0 2 v21
v v34 OffPtr t23 8 - p2:160:42:1:0 1 v4
v v37 OffPtr t23 8 - p2:160:42:0:0 1 v6
v v19 Addr t19 0 a19 p2:160:47:0:0 1 v3
v v10 Const32 t9 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v32 Load t13 0 - p2:160:42:1:0 1 v4,v1
v v33 Load t13 0 - p2:160:42:1:0 1 v34,v1
v v35 Load t13 0 - p2:160:42:0:0 1 v6,v1
v v36 Load t13 0 - p2:160:42:0:0 1 v37,v1
v v8 StaticCall t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 2 v8
v v11 LocalAddr t33 0 a7 p2:160:42:2:0 3 v2,v9
v v38 OffPtr t23 8 - p2:160:42:2:0 1 v11
v v39 Store t28 0 a16 p2:160:42:2:0 1 v11,v18,v9
v v12 Store t28 0 a16 p2:160:42:2:0 1 v38,v14,v39
v v15 StaticCall t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 Store t28 0 a13 p43:111:6:1:0 4 v21,v13,v16
v v7 Load t9 0 - p43:111:6:0:0 1 v19,v23
v v5 Neq32 t2 0 - p43:111:6:0:0 1 v7,v10
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 Load t15 0 - p43:111:6:0:0 1 v25,v23
v v30 WB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 2 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v24 OffPtr t21 0 - p43:111:6:0:0 1 v29
v v22 Store t28 0 a13 p43:111:6:0:0 1 v24,v17,v27
v v40 OffPtr t21 8 - p43:111:6:0:0 1 v29
v v41 Store t28 0 a13 p43:111:6:0:0 1 v40,v31,v22
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v41
v v43 Store t28 0 a14 p43:111:6:0:0 1 v25,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts 0=v10
freev -
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 33 "lower"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 9 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v32 ARM64FMOVDload t13 0 a3 p2:160:42:1:0 1 v3,v1
v v33 ARM64FMOVDload t13 8 a3 p2:160:42:1:0 1 v3,v1
v v35 ARM64FMOVDload t13 0 a4 p2:160:42:0:0 1 v3,v1
v v36 ARM64FMOVDload t13 8 a4 p2:160:42:0:0 1 v3,v1
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FMOVDstore t28 0 a7 p2:160:42:2:0 1 v2,v18,v9
v v12 ARM64FMOVDstore t28 8 a7 p2:160:42:2:0 1 v2,v14,v39
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 2 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64MOVDstore t28 0 - p43:111:6:0:0 1 v29,v17,v27
v v41 ARM64MOVDstore t28 8 - p43:111:6:0:0 1 v29,v31,v22
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v41
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v40,v24,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 34 "addressing modes"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 9 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v32 ARM64FMOVDload t13 0 a3 p2:160:42:1:0 1 v3,v1
v v33 ARM64FMOVDload t13 8 a3 p2:160:42:1:0 1 v3,v1
v v35 ARM64FMOVDload t13 0 a4 p2:160:42:0:0 1 v3,v1
v v36 ARM64FMOVDload t13 8 a4 p2:160:42:0:0 1 v3,v1
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FMOVDstore t28 0 a7 p2:160:42:2:0 1 v2,v18,v9
v v12 ARM64FMOVDstore t28 8 a7 p2:160:42:2:0 1 v2,v14,v39
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 2 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64MOVDstore t28 0 - p43:111:6:0:0 1 v29,v17,v27
v v41 ARM64MOVDstore t28 8 - p43:111:6:0:0 1 v29,v31,v22
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v41
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v40,v24,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 35 "late lower"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 9 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v32 ARM64FMOVDload t13 0 a3 p2:160:42:1:0 1 v3,v1
v v33 ARM64FMOVDload t13 8 a3 p2:160:42:1:0 1 v3,v1
v v35 ARM64FMOVDload t13 0 a4 p2:160:42:0:0 1 v3,v1
v v36 ARM64FMOVDload t13 8 a4 p2:160:42:0:0 1 v3,v1
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FMOVDstore t28 0 a7 p2:160:42:2:0 1 v2,v18,v9
v v12 ARM64FMOVDstore t28 8 a7 p2:160:42:2:0 1 v2,v14,v39
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 2 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64MOVDstore t28 0 - p43:111:6:0:0 1 v29,v17,v27
v v41 ARM64MOVDstore t28 8 - p43:111:6:0:0 1 v29,v31,v22
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v41
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v40,v24,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 36 "pair"
type t42 TUPLE ? ? ? - "float64,float64" "" t13 t13
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v12 Copy t28 0 - p2:160:42:2:0 1 v39
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v12
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
v v41 Copy t28 0 - p43:111:6:0:0 1 v22
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v41
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 38 "lowered cse"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 39 "elim unread autos"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 41 "lowered deadcode"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 42 "checkLower"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 43 "loop invariant"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 45 "tighten"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 46 "late deadcode"
f b2 t1 a1 44 3
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b2
cache idom b2:-,b1:b2,b3:b2
cache sdom b2:-:b1:-:2:17,b1:b2:-:b3:5:8,b3:b2:-:-:11:14
cache loopnest 4 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 47 "critical"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 48 "phi tighten"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 49 "likelyadjust"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b1:b2,b3:b2,b4:b2
cache sdom b2:-:b4:-:2:23,b1:b2:-:b3:11:14,b3:b2:-:-:17:20,b4:b2:-:b1:5:8
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
dcllen 5
end
pass 50 "layout"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate laidout
dcllen 5
end
pass 51 "schedule"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
dcllen 5
end
pass 52 "late nilcheck"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
dcllen 5
end
pass 53 "flagalloc"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v13 ARM64MOVDaddr t17 0 a9 p0:0:0:0:0 2 v3
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v11 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v13,v11,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v13,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v41,v12,v44,v5,v38,v10,v19,v37,v34,v25,v21,v6,v4
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
dcllen 5
end
pass 54 "regalloc"
aux a5 call "AuxCall{runtime.complex128div}" a6 1 2 1 8 32 4 2
abiparam in 0 t26 - 16,17 0
abiparam in 1 t26 - 18,19 16
abiparam out 0 t26 - 16,17 -1
callreg 0:80000000,1:100000000,2:200000000,3:400000000 0:80000000,1:100000000 7fffffff97ffffff -
aux a10 call "AuxCall{runtime.convTnoptr}" a11 1 2 1 8 16 2 1
abiparam in 0 t36 - 0 0
abiparam in 1 t33 - 1 8
abiparam out 0 t27 - 0 -1
callreg 0:1,1:2 0:1 7fffffff97ffffff -
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v41 ARM64MOVDaddr t17 0 a9 p2:160:42:2:0 1 v3
v v12 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v41,v12,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v44 ARM64MOVDaddr t17 0 a9 p43:111:6:2:0 1 v3
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v44,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v4,v5,v6,v10,v19,v21,v25,v34,v37,v38
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
regalloc 45 v2:SP,v3:SB,v7:R1,v8:[F0;F1],v12:R1,v14:F1,v15:[R0],v17:R0,v18:F0,v24:(F2;F3),v29:R25,v30:(R25;-),v31:R1,v32:F0,v33:F1,v35:F2,v36:F3,v40:(F0;F1),v41:R0,v44:R1
dcllen 5
end
pass 55 "loop rotate"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b4:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v41 ARM64MOVDaddr t17 0 a9 p2:160:42:2:0 1 v3
v v12 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v41,v12,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v44 ARM64MOVDaddr t17 0 a9 p43:111:6:2:0 1 v3
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v44,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b4 Plain p43:111:6:0:0 0 0 - - b3:0 b2:1
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b4:0,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v4,v5,v6,v10,v19,v21,v25,v34,v37,v38
freeb -
cache postorder b3,b1,b4,b2
cache idom b2:-,b4:b2,b1:b2,b3:b2
cache sdom b2:-:b4:-:2:23,b4:b2:-:b1:5:8,b1:b2:-:b3:11:14,b3:b2:-:-:17:20
cache loopnest 5 0 - -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
regalloc 45 v2:SP,v3:SB,v7:R1,v8:[F0;F1],v12:R1,v14:F1,v15:[R0],v17:R0,v18:F0,v24:(F2;F3),v29:R25,v30:(R25;-),v31:R1,v32:F0,v33:F1,v35:F2,v36:F3,v40:(F0;F1),v41:R0,v44:R1
dcllen 5
end
pass 56 "trim"
f b2 t1 a1 44 4
b b2 ARM64NZW p43:111:6:0:0 -1 0 - v7 b1:0,b3:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v24 ARM64FLDPD t42 0 a4 p2:160:42:0:0 2 v3,v1
v v35 Select0 t13 0 - p2:160:42:0:0 1 v24
v v36 Select1 t13 0 - p2:160:42:0:0 1 v24
v v40 ARM64FLDPD t42 0 a3 p2:160:42:1:0 2 v3,v1
v v32 Select0 t13 0 - p2:160:42:1:0 1 v40
v v33 Select1 t13 0 - p2:160:42:1:0 1 v40
v v8 ARM64CALLstatic t40 32 a5 p2:160:42:1:0 3 v32,v33,v35,v36,v1
v v18 SelectN t13 0 - p2:160:42:0:0 1 v8
v v14 SelectN t13 1 - p2:160:42:2:0 1 v8
v v9 SelectN t28 2 - p2:160:42:0:0 1 v8
v v39 ARM64FSTPD t28 0 a7 p2:160:42:2:0 1 v2,v18,v14,v9
v v41 ARM64MOVDaddr t17 0 a9 p2:160:42:2:0 1 v3
v v12 ARM64MOVDaddr t33 0 a7 p2:160:42:2:0 1 v2
v v15 ARM64CALLstatic t35 16 a10 p2:160:42:0:0 2 v41,v12,v39
v v17 SelectN t27 0 - p2:160:42:0:0 2 v15
v v16 SelectN t28 1 - p2:160:42:0:0 2 v15
v v20 InlMark t30 31 - p2:160:39:0:0 0 v16
v v44 ARM64MOVDaddr t17 0 a9 p43:111:6:2:0 1 v3
v v23 ARM64MOVDstore t28 0 a12 p43:111:6:1:0 4 v3,v44,v16
v v7 ARM64MOVWUload t9 0 a19 p43:111:6:0:0 1 v3,v23
b b1 Plain p43:111:6:0:0 0 0 - - b3:1 b2:0
v v31 ARM64MOVDload t15 8 a12 p43:111:6:0:0 1 v3,v23
v v30 ARM64LoweredWB t41 2 - p43:111:6:0:0 2 v23
v v29 Select0 t21 0 - p43:111:6:0:0 1 v30
v v27 Select1 t28 0 - p43:111:6:0:0 1 v30
v v22 ARM64STP t28 0 - p43:111:6:0:0 1 v29,v17,v31,v27
b b3 Ret p2:160:47:0:0 0 0 - v28 - b2:1,b1:0
v v42 Phi t28 0 - p43:111:6:2:0 1 v23,v22
v v43 ARM64MOVDstore t28 8 a12 p43:111:6:0:0 1 v3,v17,v42
v v26 WBend t28 0 - p43:111:6:2:0 1 v43
v v28 MakeResult t32 0 - p2:160:47:1:0 1 v26
names s2,s3
named s2 v13
named s3 v17
splits s1/0/t15=s2,s1/8/t17=s3
canon a15/t38/0/-/0=s1
consts -
freev v4,v5,v6,v10,v19,v21,v25,v34,v37,v38
freeb -
cache auxmap -:1,a3:2,a4:3,a7:4,a9:5,a12:6,a19:7
cache linestarts 2:160:160,43:111:111
fstate scheduled,laidout
regalloc 45 v2:SP,v3:SB,v7:R1,v8:[F0;F1],v12:R1,v14:F1,v15:[R0],v17:R0,v18:F0,v24:(F2;F3),v29:R25,v30:(R25;-),v31:R1,v32:F0,v33:F1,v35:F2,v36:F3,v40:(F0;F1),v41:R0,v44:R1
dcllen 5
end
frontend
end
ptrcache t4,t5,t6,t7,t9,t11,t12,t13,t15,t16,t17,t24,t36,t37,t38
typelink t7=t37,t17=t36,t28=t32
typeorder t3,t7=t37,t4,t8,t5,t9,t6,t10,t11,t14,t15,t25,t26,t12,t13,t2,t17=t36,t18,t19,t20,t21,t33,t22,t23,t24,t39,t1,t38,t16,t27,t28,t30,t29,t31,t42,t41,t32,t34,t35,t40
eof
"#

/-- `test/zerodivide/main/init.func33,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "init.func33" 1
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
type t1 16 8 16 1 02 "interface {}"
name n1 "v" PAUTO t1 1 "main.v" 0 a15
type t2 16 8 0 0 - "complex128"
name n2 ".autotmp_1" PAUTO t2 3 "main..autotmp_1" 0 a7
type t3 8 8 8 1 01 "unsafe.Pointer"
name n3 ".autotmp_2" PAUTO t3 3 "main..autotmp_2" 0 -
type t4 8 8 0 0 - "uintptr"
name n4 "v.type" PAUTO t4 3 "main.v.type" 0 a17
type t5 8 8 8 1 01 "*uint8"
name n5 "v.data" PAUTO t5 3 "main.v.data" 0 a18
in n1 0 used
in n2 0 used,addrtaken,autotmp
in n3 0 used,autotmp
in n4 0 used
in n5 0 used
out n2 -16 used,addrtaken,autotmp
opt n3 0 autotmp
opt n1 0 -
opt n5 0 -
opt n4 0 -
stack 16 0 8
end
genin
posbase p2 "./zerodivide.go" 1 1 -1 1 "./zerodivide.go" "./zerodivide.go" 1 1
sym y1 "main.init.func33" 1
curfn p2:160:27:0:0 0 0
regargs -
text y1 0 0 0 0 160 208080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.d" 0
sym y4 "main.c" 0
sym y5 "runtime.complex128div" 1
sym y6 "main..autotmp_1" 0
sym y7 "type:complex128" 0
sym y8 "runtime.convTnoptr" 1
sym y9 "main.use" 1
inl i31 - p2:160:39:0:0 y9 "use"
posbase p43 "./zerodivide.go" 1 1 31 1 "./zerodivide.go" "./zerodivide.go" 1 1
sym y10 "main.tmp" 0
sym y11 "runtime.writeBarrier" 0
sym y12 "runtime.gcWriteBarrier2" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i0 0 0 p2:160:27:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:160:27:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:160:27:0:0
p 3 3 0 0 0 - FLDPD 0 MEM/0/0/0/EXTERN/0/0/y3/- 0 - REGREG/8226/0/0/NONE/0/8227/-/- 0 0 p2:160:42:1:0
p 4 4 0 0 0 - FLDPD 0 MEM/0/0/0/EXTERN/0/0/y4/- 0 - REGREG/8224/0/0/NONE/0/8225/-/- 0 0 p2:160:42:2:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:160:42:1:0
p 6 6 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:160:42:1:0
p 7 7 0 0 0 - FSTPD 0 REGREG/8224/0/0/NONE/0/8225/-/- 0 - MEM/8383/0/0/AUTO/0/-16/y6/- 0 0 p2:160:42:2:0
p 8 8 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y7/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:160:42:2:0
p 9 9 0 0 0 - MOVD 0 ADDR/8383/0/0/AUTO/0/-16/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:160:42:2:0
p 10 10 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p2:160:42:2:0
p 11 11 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 12 12 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y7/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p43:111:6:1:0
p 13 13 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y10/- 0 0 p43:111:6:2:0
p 14 14 0 0 0 - MOVWU 0 MEM/0/0/0/EXTERN/0/0/y11/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p43:111:6:2:0
p 15 15 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p43:111:6:0:0
p 16 16 0 0 0 - CBZW 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@20 0 0 p43:111:6:2:0
p 17 17 0 0 0 - MOVD 0 MEM/0/0/0/EXTERN/0/8/y10/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p43:111:6:2:0
p 18 18 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y12/- 0 0 p43:111:6:2:0
p 19 19 0 0 0 - STP 0 REGREG/8192/0/0/NONE/0/8193/-/- 0 - MEM/8217/0/0/NONE/0/0/-/- 0 0 p43:111:6:2:0
p 20 20 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/8/y10/- 0 0 p43:111:6:2:0
p 21 21 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:160:47:0:0
p 22 22 0 0 0 - RET 0 _ 0 - _ 0 0 p2:160:47:0:0
p 23 23 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 160 208080
inlmark @3 31
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 1
reloc 0 0 R_USEIFACE 0 y7
symalign y2:4
autot -
dbgentry 2
dbgslot 0 n4 t4 0
dbgslot 1 n5 t5 0
dbgvar 0 n1 0,1
dbgloc 0 2:17:-1:-30000:9308509308
dbgregout -
dbgpc 2:17:11
end
asm
sym y13 "runtime.morestack_noctxt" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/64/-/i0 0 0 p2:160:27:0:0
p 24 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:160:27:0:0
p 25 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:160:27:0:0
p 26 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:160:27:0:0
p 27 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@42 0 0 p2:160:27:0:0
p 28 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:160:27:0:0
p 29 12 64 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-64/-/- 0 0 p2:160:27:0:1
p 30 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:160:27:0:0
p 31 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:160:27:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:160:27:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:160:27:0:0
p 32 24 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:160:27:0:0
p 3 24 0 0 251 - FLDPD 0 MEM/0/0/0/EXTERN/110/0/y3/- 0 - REGREG/8226/0/0/NONE/7/8227/-/- 0 0 p2:160:42:1:0
p 33 36 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:160:42:1:0
p 4 36 0 0 251 - FLDPD 0 MEM/0/0/0/EXTERN/110/0/y4/- 0 - REGREG/8224/0/0/NONE/7/8225/-/- 0 0 p2:160:42:2:0
p 34 48 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:160:42:2:0
p 5 48 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:160:42:1:0
p 6 48 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p2:160:42:1:0
p 7 52 0 0 428 - FSTPD 0 REGREG/8224/0/0/NONE/7/8225/-/- 0 - MEM/0/0/0/AUTO/48/-16/y6/- 0 0 p2:160:42:2:0
p 8 56 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y7/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:160:42:2:0
p 9 64 0 0 325 - MOVD 0 ADDR/0/0/0/AUTO/32/-16/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:160:42:2:0
p 10 68 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p2:160:42:2:0
p 11 72 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 12 72 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y7/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p43:111:6:1:0
p 35 80 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p43:111:6:1:0
p 13 80 0 0 313 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y10/- 0 0 p43:111:6:2:0
p 36 88 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p43:111:6:2:0
p 14 88 0 0 397 - MOVWU 0 MEM/0/0/0/EXTERN/110/0/y11/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p43:111:6:2:0
p 37 96 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p43:111:6:2:0
p 15 96 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p43:111:6:0:0
p 16 96 0 0 85 - CBZW 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/20/-/@20 0 0 p43:111:6:2:0
p 17 100 0 0 338 - MOVD 0 MEM/0/0/0/EXTERN/110/8/y10/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p43:111:6:2:0
p 18 108 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y12/- 0 0 p43:111:6:2:0
p 19 112 0 0 436 - STP 0 REGREG/8192/0/0/NONE/7/8193/-/- 0 - MEM/8217/0/0/NONE/77/0/-/- 0 0 p43:111:6:2:0
p 20 116 0 0 313 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/8/y10/- 0 0 p43:111:6:2:0
p 21 124 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:160:47:0:0
p 22 124 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:160:47:0:0
p 38 128 -64 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/64/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:160:47:0:0
p 39 132 64 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:160:47:0:0
p 40 136 -64 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:160:47:0:0
p 41 136 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:160:27:0:0
p 42 136 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:160:27:0:0
p 43 136 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:160:27:0:0
p 44 140 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y13/- 0 0 p2:160:27:0:0
p 45 144 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:160:27:0:0
p 46 144 64 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@24 0 0 p2:160:27:0:0
fn y1 0 56 0 0 160 208080
inlmark @3 31
funcaux y2 y2 - - - - -
text 160 0 900b40f9ff6330eb09040054fe0f1cf8fd831ff8fd2300d11b0000907b030091620f406d1b0000907b0300916007406d00000094e087026d0000009000000091e1a300910000009401000090210000911b000090610300f91b000090610340b9a10000341b000090610340f900000094200700a91b000090600300f9fd835ff8fe0744f8c0035fd6e3031eaa00000094dcffff17000000000000000000000000 13
reloc 0 0 R_USEIFACE 0 y7
reloc 24 8 R_ADDRARM64 0 y3
reloc 36 8 R_ADDRARM64 0 y4
reloc 48 4 R_CALLARM64 0 y5
reloc 56 8 R_ADDRARM64 0 y7
reloc 68 4 R_CALLARM64 0 y8
reloc 72 8 R_ADDRARM64 0 y7
reloc 80 8 R_ARM64_PCREL_LDST64 0 y10
reloc 88 8 R_ARM64_PCREL_LDST32 0 y11
reloc 100 8 R_ARM64_PCREL_LDST64 8 y10
reloc 108 4 R_CALLARM64 0 y12
reloc 116 8 R_ARM64_PCREL_LDST64 8 y10
reloc 140 4 R_CALLARM64 0 y13
pcln y16 y17 y18 y19 y14,y15 y2,y2
usedfiles 1
inltree 0 -1 p2:160:39:0:0 y9 "use" 24
data y2 Sxxx 0 4 8000 0100000000000000 0
data y14 SRODATA 25 1 28000 00010102020303030103060803020102040702030102020400 0
data y15 SRODATA 7 1 28000 000c0216010600 0
data y16 SRODATA 8 1 28000 020480011d7f0700 0
data y17 SRODATA 3 1 28000 042800 0
data y18 SRODATA 8 1 28000 c20212610d620900 0
data y19 SRODATA 7 1 28000 0012020d010900 0
end
dwarf
sym y20 "" 0
sym y21 "" 0
sym y22 "" 0
sym y23 "" 0
sym y24 "go:info.main.use$abstract" 0
sym y25 "go:info.interface {}" 0
dwfn y20 y21 y22 - y23 "main.init.func33" 1:160 1 0 1 46
dwdcl n2
dwclosure 0 -
dwparents -
dwparams -
dwinlfn y9 y24
dwinldcl y9 "v" 0 p2:110:10:0:0
dwname n2 1 1 1 0 0 0 -16 0 - - ? 0 0 ? p2:160:42:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p2:160:42:0:0
dwname n1 1 0 0 1 0 0 0 0 - - "interface {}" 0 0 1 p43:110:10:0:0
dwname n5 1 0 0 0 0 0 0 0 - - "*uint8" 0 0 1 p43:110:10:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "uintptr" 0 0 1 p43:110:10:0:0
var 0 0 "v" 5 1 0 1 0 -8 y25 "./zerodivide.go" 110 10 32 0 1 0 v0
scope 0 0 - 0
inlcall 0 31 1:160 y24 - 1 72:124 0
dieref y20 4 y24 0
data y20 SDWARFFCN 56 0 0 036d61696e2e696e69742e66756e6333330000a001019c02000000a0010109000000000000000002000000a0012900000000000000000000 6
reloc 0 0 R_USETYPE 0 y7
reloc 18 1 R_DWTXTADDR_U1 0 y1
reloc 31 4 R_DWARFSECREF 0 y24
reloc 35 4 R_DWARFSECREF 0 y22
reloc 46 4 R_DWARFSECREF 0 y24
reloc 50 4 R_DWARFSECREF 0 y21
data y21 SDWARFLOC 13 0 0 01000448a00105930850930800 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y22 SDWARFRANGE 6 0 0 010004487c00 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y23 SDWARFLINES 41 0 0 00090200000000000000000402039a01140a8706ff06870637060353d3065f0608032cdc0224000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.init.func33`. -/
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

/-- The index of `v24`'s `FLDPD main.d(SB), (F2, F3)` among the Progs (`kdOK` checks it). -/
def jF : Nat := 3

/-- A PC table for `b2` with `v24` (index 3) at its `FLDPD` and the value after it at the next
Prog. -/
def tab : PcTab := [(2, [3, 3, 3, 3, 4])]

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

/-- The class map before `v24`: `SB` (Go register 63) holds 64 bits. -/
def K0 : KMap := KMap.bot.set! 63 (some 64)

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 64-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 64 8 ps.toList

/-- `ι`: GenG2's (the globals at `symA`), and `.autotmp_1`'s block (aux 7, a `temp` block of
activation 0) at `SP + 40`. -/
def ι59 (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 7 then some (GenG2.sp0 + 40) else GenG2.ι b

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0), no home slot,
the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := ι59, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `float64` bits of `1.5`, `main.d`'s real part. -/
def c0 : BitVec 64 := 0x3ff8000000000000

/-- The `float64` bits of `2.5`, `main.d`'s imaginary part. -/
def c1 : BitVec 64 := 0x4004000000000000

/-- `main.d` at offset 0 (the real part). -/
def pD : Ptr := ⟨.global "main.d", 0⟩

/-- 8 bytes above (the imaginary part). -/
def pD8 : Ptr := ⟨.global "main.d", 8⟩

/-- Byte `i` of `main.d` (`complex(1.5, 2.5)`): the little-endian bytes of `c0`, then of `c1`. -/
def byteD (i : Nat) : BitVec 8 :=
  if i < 8 then c0.extractLsb' (8 * i) 8 else c1.extractLsb' (8 * (i - 8)) 8

/-- The 16 bytes of `main.d`. -/
def bytesD : Array Byte := Array.ofFn (n := 16) fun i => .b (byteD i.val)

/-- The Phase 1 memory: the global `main.d`. -/
def memD : Mem := { blocks := #[(.global "main.d", { data := bytesD })] }

/-- The machine memory: the bytes of `main.d` at `symA`, 0 elsewhere. -/
def MD : Memory := fun y =>
  if (y - GenG2.symA).toNat < 16 then byteD (y - GenG2.symA).toNat else 0

/-- The `runLoc` state before `v24`: every register `poison`, the memory `memD`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memD },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem memD }

/-- The machine before `v24`: the activation's `g` and `FP`, the PC of `v24`, the memory `MD`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 3, mem := MD }

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

/-- `vkind59p` accepts `v24` with a pattern the Prog at `jF` matches. -/
def kdOK : Bool := (patOf (vkind59p lc g (val 24))).any fun pat => (ps[jF]?).any pat.ok

/-- The value holds the 64-bit `w`. -/
def isI64 (w : BitVec 64) : Option Val → Bool
  | some (.int .w64 x) => x == w
  | _ => false

theorem isI64_spec {w : BitVec 64} {o : Option Val} (h : isI64 w o = true) :
    o = some (.int .w64 w) := by
  unfold isI64 at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `main.init.func33` (`test/zerodivide`): it holds an arm64
op; `checkG58` rejects it (`v24: pair load shape`) and `vkind58` rejects `v24`, which `vkind59p`
accepts with the Prog at `jF`; the Progs have distinct IDs below `2^32`; every home is one G10
handles; `checkFrame` passes; `v24` is `FLDPD {main.d} [0] v3 v1` of shape `(int64, int64)`; the
only accessed frame variable is `.autotmp_1` (aux 7), operand `NAME_AUTO -16`, a `temp` block of
activation 0, at `frameOff 40`; there is no home slot; `v24` reads its registers at the classes of
`K0`; `memD` reads 8 bytes at 0 and at 8, `c0` and `c1`; and `stepLoc` runs `v24` to `c0` in `F2`
(Go register 33) and `c1` in `F3` (34). -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG58 lc0 ps bs g).toOption.isNone &&
    (vkind58 lc g (val 24)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.value? 24).isSome && (val 24).id == 24 && (val 24).op == .ARM64FLDPD &&
    Ty.beq (lc.ty 24) (.tuple [.int .w64, .int .w64]) &&
    ((val 24).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) == some "main.d" &&
    (val 24).auxInt.toInt == 0 &&
    (memD.read pD 8).isSome && (memD.read pD8 8).isSome &&
    isI64 c0 (some ((Arm64.loadN (.int .w64) 8 false memD pD).retypeL (.int .w64))) &&
    isI64 c1 (some ((Arm64.loadN (.int .w64) 8 false memD pD8).retypeL (.int .w64))) &&
    accessedVars lc == [7] && varOp g 7 == some (.AUTO, -16) && !lc.ctx.tabs.forgeable 7 &&
    lc.ctx.act == 0 && (homeSlots lc).isEmpty && decide (frameOff L .AUTO (-16) = 40) &&
    (kReads lc (val 24)).all (fun rc => K0.get rc.1 == some rc.2) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 24))
      (fun s1 => isI64 c0 s1.regs[33]? && isI64 c1 s1.regs[34]?)

theorem g59p_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (checkG58 lc0 ps bs g).toOption = none ∧
      (vkind58 lc g (val 24)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.value? 24 = some (val 24) ∧ (val 24).id = 24 ∧ (val 24).op = .ARM64FLDPD ∧
      lc.ty 24 = .tuple [.int .w64, .int .w64] ∧
      ((val 24).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) = some "main.d" ∧
      (val 24).auxInt.toInt = 0 ∧
      (memD.read pD 8).isSome = true ∧ (memD.read pD8 8).isSome = true ∧
      (Arm64.loadN (.int .w64) 8 false memD pD).retypeL (.int .w64) = .int .w64 c0 ∧
      (Arm64.loadN (.int .w64) 8 false memD pD8).retypeL (.int .w64) = .int .w64 c1 ∧
      accessedVars lc = [7] ∧ varOp g 7 = some (.AUTO, -16) ∧ lc.ctx.tabs.forgeable 7 = false ∧
      lc.ctx.act = 0 ∧ (homeSlots lc).isEmpty = true ∧ frameOff L .AUTO (-16) = 40 ∧
      (∀ rc ∈ kReads lc (val 24), K0.get rc.1 = some rc.2) ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 24))
        (fun s1 => isI64 c0 s1.regs[33]? && isI64 c1 s1.regs[34]?) = true := by
  have hf := g59p_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hf
  obtain ⟨hl, h58, h58v, hkd, hlt, hnd, hhome, hcf, hvs, hid, hop, hty, hsy, hoff, hr0, hr1, hl0,
    hl1, hav, hvo, hfg, hact, hsl, hfo, hrd, hrun⟩ := hf
  refine ⟨hl, h58, h58v, hkd, hlt, hnd, homeOK10_all hhome, ?_, ?_, hid, hop, Ty.eq_of_beq hty,
    hsy, hoff, hr0, hr1, Option.some.inj (isI64_spec hl0), Option.some.inj (isI64_spec hl1), hav,
    hvo, hfg,
    hact, hsl, hfo, hrd, hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-- `vkind59p`'s pattern for `v24` and the Prog at `jF` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind59p lc g (val 24) = some (.ok (.prog pat)) ∧ (ps[jF]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

theorem ι59_temp : ι59 (.temp 0 7) = some (GenG2.sp0 + 40) := by simp [ι59]

theorem ι59_ne {b : Blk} (h : b ≠ .temp 0 7) : ι59 b = GenG2.ι b := by simp [ι59, h]

theorem ι59_glob (name : String) : ι59 (.global name) = some GenG2.symA := by
  simp [ι59, GenG2.ι]

theorem addrAgree59 : AddrAgree ι59 := by
  intro b n a hb ha hnt
  rw [ι59_ne (hnt 0 7)] at ha
  exact GenG2.addrAgree b n a hb ha hnt

theorem env59 (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : accessedVars lc = [7])
    (hvo : varOp g 7 = some (.AUTO, -16)) (hfg : lc.ctx.tabs.forgeable 7 = false)
    (hact : lc.ctx.act = 0) (hsl : (homeSlots lc).isEmpty = true)
    (hoff : frameOff L .AUTO (-16) = 40) : G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree59
            glob := fun _ name _ _ => ι59_glob name.toStringLossy
            syms := by
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
            intro x hx o ho _
            rw [hav, List.mem_singleton] at hx
            subst hx
            rw [hvo] at ho
            cases ho
            rw [hact, hoff]
            show ι59 (.temp 0 7) = some (GenG2.sp0 + BitVec.ofInt 64 40)
            rw [ι59_temp]
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

/-! ## The memory -/

theorem memD_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ memD.blocks) :
    b = .global "main.d" ∧ al = { data := bytesD } := by
  simpa [memD] using h

/-- `memD` injected into `MD` by `ι59`: `main.d`'s bytes at `symA`. -/
theorem memInjD : MemInj ι59 memD MD where
  nil := by simp [ι59, GenG2.ι]
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memD_blocks h
    exact ⟨GenG2.symA, ι59_glob _, fun _ => by decide, by simp [bytesD, GenG2.symA]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memD_blocks h
    obtain ⟨rfl, -⟩ := memD_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memD_blocks h
    rw [ι59_glob] at ha
    cases ha
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    have hi' : i < 16 := by simpa [bytesD] using hi
    have hd : (GenG2.symA + BitVec.ofNat 64 i - GenG2.symA).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, MD, hd, hi', bytesD]

theorem keysD : KeysNodup memD := by simp [KeysNodup, memD]

theorem sepD : SepFrom ι59 (StkAt E) memD := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := memD_blocks h
  rw [ι59_glob] at ha
  cases ha
  have hsp : E.sp.toNat = 0x7fff0000 := rfl
  have hA : GenG2.symA.toNat = 0x10000000000 := rfl
  simp only [hA, bytesD, Array.size_ofFn]
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -, h2⟩
  · rw [hsp] at h2
    omega
  · simp [E] at hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 2 3 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memD, rfl, memInjD⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, MD, E]; decide,
    by simp only [MState.word, readMem, m0, MD, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem inv0 : G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memD, rfl, keysD, sepD⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v24`: `FLDPD main.d(SB), (F2, F3)` -/

/-- `PairPre50` on `v24`: it reads 8 valid bytes of `main.d` at 0 and at 8, `c0` and `c1` at its
component shapes `int64`, no pointer. -/
theorem pre24 (hid : (val 24).id = 24) (hop : (val 24).op = .ARM64FLDPD)
    (hty : lc.ty 24 = .tuple [.int .w64, .int .w64])
    (hsy : ((val 24).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) = some "main.d")
    (hoff : (val 24).auxInt.toInt = 0)
    (hr0 : (memD.read pD 8).isSome = true) (hr1 : (memD.read pD8 8).isSome = true)
    (hl0 : (Arm64.loadN (.int .w64) 8 false memD pD).retypeL (.int .w64) = .int .w64 c0)
    (hl1 : (Arm64.loadN (.int .w64) 8 false memD pD8).retypeL (.int .w64) = .int .w64 c1) :
    PairPre50 lc s0 (val 24) := by
  intro as n sg fp hpo a x _ _
  rw [hop] at hpo
  simp only [pairOp50, ↓reduceIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hpo
  obtain ⟨-, rfl, -, rfl⟩ := hpo
  obtain ⟨y, hy, hsy'⟩ := Option.map_eq_some_iff.1 hsy
  obtain ⟨x', hx', hs'⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨name, abi⟩ := y
  simp only at hsy'
  have hpq := pairAddr_globN (a := x) (n := 8) hx' hs'
  rw [hsy', hoff] at hpq
  have hp : (⟨.global "main.d", BitVec.ofInt 64 (0 : Int)⟩ : Ptr) = pD := by
    simp only [pD]; decide
  have hq : (⟨.global "main.d", BitVec.ofInt 64 (0 : Int) + BitVec.ofNat 64 8⟩ : Ptr) = pD8 := by
    simp only [pD8]; decide
  rw [hp, hq] at hpq
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hr0
  obtain ⟨bs', hbs'⟩ := Option.isSome_iff_exists.1 hr1
  refine ⟨pD, pD8, memD, bs, bs', hpq, rfl, hbs, hbs', fun _ t0 t1 ht => ?_⟩
  rw [hid, hty] at ht
  simp only [Ty.tuple.injEq, List.cons.injEq, and_true] at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨fun r h => by (rw [hl0] at h; cases h), fun r h => by (rw [hl1] at h; cases h)⟩

/-- **G59, group P, on `main.init.func33`** (`test/zerodivide`: `use(d / c)` of the `complex128`
globals `main.d` and `main.c`, whose parts genssa loads with `FLDPD main.d(SB), (F2, F3)` for
`runtime.complex128div`): `b2`'s `v24` (`FLDPD {main.d} [0] v3 v1`, a float pair load of a global,
with an aux), which `checkG58` rejects (`v24: pair load shape`, as `vkind58`) and `vkind59p`
accepts. From `s0`, with `main.d = complex(1.5, 2.5)`, `stepLoc` runs `v24` to `c0` (the bits of
`1.5`) in `F2` and `c1` (the bits of `2.5`) in `F3`, and `vk59p_step` relates it to a machine run
of its `FLDPD` to a state whose `V2` and `V3` hold `c0` and `c1` in their low 64 bits, under an
activation extending `E` that is again a `G49Env`. -/
theorem genG59p_witness :
    (checkG58 lc0 ps bs g).toOption = none ∧ (vkind58 lc g (val 24)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 24) = .ok s1 ∧
        s1.regs[33]? = some (.int .w64 c0) ∧ s1.regs[34]? = some (.int .w64 c1) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 2 4 m1 ∧
        (m1.v 2).setWidth 64 = c0 ∧ (m1.v 3).setWidth 64 = c1 := by
  obtain ⟨hl, h58, h58v, hkd, hlt, hnd, hhome, hcf, hv, hid, hop, hty, hsy, hoff, hr0, hr1, hl0,
    hl1, hav, hvo, hfg, hact, hsl, hfo, hrd, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr33 := isI64_spec hr.1
  have hr34 := isI64_spec hr.2
  have hE := env59 hlt hav hvo hfg hact hsl hfo
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind59p_spec hvk
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jF (jF + 1) :=
    ⟨jF, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 64 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), addrAgree59⟩
  have hj : E.pcOf 2 3 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 2 (3 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk59p_step (H := GenG2.H0) (L := []) (bid := 2)
    (i := 3) (j := jF) (j' := jF + 1) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0 inv0
    (fun e he => by cases he) (pre24 hid hop hty hsy hoff hr0 hr1 hl0 hl1) hs1
  exact ⟨h58, h58v, s1, E1, m1, hs1, hr33, hr34, hx1, hE1, hp1, hm1,
    (hm1.regs 33 _ hr33).2 _ rfl, (hm1.regs 34 _ hr34).2 _ rfl⟩

end GoFV.Proof.Witness.GenG59p
