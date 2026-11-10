import GoFV.Proof.Gen.G57b
import GoFV.Gen.Check55
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG57b

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/gcgort/main/init.func95.1,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "init.func95.1" 1 0 0
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
aux a2 sym "main.init.func95.1" "main.init.func95.1" 1 - 0 - - - - 0
aux a1 call "AuxCall{main.init.func95.1}" a2 1 0 0 8 0 0 0
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
type t34 CHAN 8 8 8 hasptr,direct,comparable "chan complex64" "chan complex64"
type t33 PTR 8 8 8 hasptr,direct,comparable "*chan complex64" "*chan complex64" t34
type t35 PTR 8 8 8 hasptr,direct,comparable "*complex64" "*complex64" t25
aux a3 name ".autotmp_1" ".autotmp_1" PAUTO t25 0 3 addrtaken,used,autotmp p2:1050:19:0:0
aux a4 type "complex64" t25
type t36 CHAN 8 8 8 hasptr,direct,comparable "chan<- complex64" "chan<- complex64"
aux a6 sym "runtime.chansend1" "runtime.chansend1" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.chansend1}" a6 1 2 0 8 16 2 0
abiparam in 0 t36 - 0 0
abiparam in 1 t35 - 1 8
aux a7 name "a" "a" PAUTO t34 0 0 used p2:1050:17:0:0
slot s1 a7 t34 0 - 0
aux a8 name "i" "i" PAUTO t11 0 0 used p2:1050:48:0:0
slot s2 a8 t11 0 - 0
f b1 t1 a1 23 1
typs Bool=t2,Int8=t3,Int16=t4,Int32=t5,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:0:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v19 Copy t36 0 - p2:1050:19:2:0 1 v6
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v19,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev -
freeb -
dcllen 4
end
pass 1 "number lines"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v19 Copy t36 0 - p2:1050:19:2:0 1 v6
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v19,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 2 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v19 Copy t36 0 - p2:1050:19:2:0 0 v6
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev -
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 3 "early deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 4 "short circuit"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 5 "decompose user"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 7 "opt"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 8 "zero arg cse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 9 "opt deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 1 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 1 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v10
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 1 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v20,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache linestarts 2:1050:1050
dcllen 4
end
pass 10 "generic cse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 0 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 0 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 11 "phiopt"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 2 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v10 Cvt64to32F t12 0 - p2:1050:60:0:0 0 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 2 v17,v16,v1
v v20 LocalAddr t35 0 a3 p2:1050:19:2:0 0 v2,v18
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 12 "gcse deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 13 "nilcheckelim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 14 "prove"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 15 "divisible"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 16 "divmod"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 17 "middle opt"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 18 "known bits"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 19 "early fuse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticLECall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 20 "expand calls"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 2 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 2 v9,v9
v v12 ComplexReal t12 0 - p2:1050:39:0:0 1 v11
v v14 ComplexImag t12 0 - p2:1050:39:0:0 1 v11
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v12
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v14
v v16 ComplexMake t25 0 - p2:1050:39:0:0 1 v13,v15
v v18 Store t28 0 a4 p2:1050:19:2:0 1 v17,v16,v1
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v20 SB t15 0 - p0:0:0:0:0 0 -
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v10,v19,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 21 "decompose builtin"
aux a9 type "float32" t12
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 4 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 0 v9,v9
v v13 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v16 ComplexMake t25 0 - p2:1050:39:0:0 0 v13,v15
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v20 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 22 "softfloat"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 4 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 0 v9,v9
v v13 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v16 ComplexMake t25 0 - p2:1050:39:0:0 0 v13,v15
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v20 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 23 "branchelim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 4 v8
v v11 ComplexMake t25 0 - p2:1050:39:0:0 0 v9,v9
v v13 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 2 v9
v v16 ComplexMake t25 0 - p2:1050:39:0:0 0 v13,v15
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v20 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 24 "late opt"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 25 "dead auto elim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 26 "sccp"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 27 "generic deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 28 "late fuse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 29 "check bce"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 30 "dse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 31 "memcombine"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 32 "writebarrier"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 GetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v5 OffPtr t33 8 - p2:1050:8:0:0 1 v4
v v7 OffPtr t20 16 - p2:1050:8:0:0 1 v4
v v17 LocalAddr t35 0 a3 p2:1050:19:2:0 3 v2,v1
v v6 Load t34 0 - p2:1050:8:1:0 1 v5,v1
v v8 Load t11 0 - p2:1050:8:0:0 1 v7,v1
v v9 Cvt64to32F t12 0 - p2:1050:48:0:0 2 v8
v v13 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v15 Round32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Store t28 0 a9 p2:1050:19:2:0 1 v10,v15,v19
v v21 StaticCall t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v10 OffPtr t22 4 - p2:1050:19:2:0 1 v17
v v19 Store t28 0 a9 p2:1050:19:2:0 1 v17,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 33 "lower"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 ARM64MOVDload t34 8 - p2:1050:8:1:0 1 v4,v1
v v8 ARM64MOVDload t11 16 - p2:1050:8:0:0 1 v4,v1
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v18 ARM64FMOVSstore t28 4 a3 p2:1050:19:2:0 1 v2,v15,v19
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FMOVSstore t28 0 a3 p2:1050:19:2:0 1 v2,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v10,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 34 "addressing modes"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 ARM64MOVDload t34 8 - p2:1050:8:1:0 1 v4,v1
v v8 ARM64MOVDload t11 16 - p2:1050:8:0:0 1 v4,v1
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v18 ARM64FMOVSstore t28 4 a3 p2:1050:19:2:0 1 v2,v15,v19
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FMOVSstore t28 0 a3 p2:1050:19:2:0 1 v2,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v10,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 35 "late lower"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 2 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 ARM64MOVDload t34 8 - p2:1050:8:1:0 1 v4,v1
v v8 ARM64MOVDload t11 16 - p2:1050:8:0:0 1 v4,v1
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v18 ARM64FMOVSstore t28 4 a3 p2:1050:19:2:0 1 v2,v15,v19
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FMOVSstore t28 0 a3 p2:1050:19:2:0 1 v2,v13,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v10,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 36 "pair"
type t37 TUPLE ? ? ? - "chan complex64,int" "" t34 t11
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v18 Copy t28 0 - p2:1050:19:2:0 1 v19
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v18
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v15,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 1 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v15,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 38 "lowered cse"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 0 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 39 "elim unread autos"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 0 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 2 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v15 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 0 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 41 "lowered deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 42 "checkLower"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 43 "loop invariant"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 45 "tighten"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 46 "late deadcode"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 47 "critical"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 48 "phi tighten"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 49 "likelyadjust"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
dcllen 4
end
pass 50 "layout"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate laidout
dcllen 4
end
pass 51 "schedule"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
dcllen 4
end
pass 52 "late nilcheck"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
dcllen 4
end
pass 53 "flagalloc"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v17 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v17,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v15,v18,v7,v5,v20,v16,v11,v14,v12,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
dcllen 4
end
pass 54 "regalloc"
aux a5 call "AuxCall{runtime.chansend1}" a6 1 2 0 8 16 2 0
abiparam in 0 t36 - 0 0
abiparam in 1 t35 - 1 8
callreg 0:1,1:2 - 7fffffff97ffffff -
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v15 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v15,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v3,v5,v7,v11,v12,v14,v16,v18,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
regalloc 22 v2:SP,v4:R26,v6:R0,v8:R2,v9:F0,v10:(R0;R2),v13:F0,v15:R1,v21:[]
dcllen 4
end
pass 55 "loop rotate"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v15 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v15,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v3,v5,v7,v11,v12,v14,v16,v18,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
regalloc 22 v2:SP,v4:R26,v6:R0,v8:R2,v9:F0,v10:(R0;R2),v13:F0,v15:R1,v21:[]
dcllen 4
end
pass 56 "trim"
f b1 t1 a1 23 1
b b1 Ret p2:1050:65:0:0 0 0 - v23 - -
v v4 ARM64LoweredGetClosurePtr t17 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v10 ARM64LDP t37 8 - p2:1050:8:1:0 2 v4,v1
v v8 Select1 t11 0 - p2:1050:8:0:0 1 v10
v v6 Select0 t34 0 - p2:1050:8:1:0 1 v10
v v9 ARM64SCVTFS t12 0 - p2:1050:48:0:0 1 v8
v v13 ARM64LoweredRound32F t12 0 - p2:1050:39:0:0 2 v9
v v19 ARM64FSTPS t28 0 a3 p2:1050:19:2:0 1 v2,v13,v13,v1
v v15 ARM64MOVDaddr t35 0 a3 p2:1050:19:2:0 1 v2
v v21 ARM64CALLstatic t32 16 a5 p2:1050:19:0:0 1 v6,v15,v19
v v22 SelectN t28 0 - p2:1050:19:0:0 1 v21
v v23 MakeResult t32 0 - p2:1050:65:0:0 1 v22
names s1,s2
named s1 v6
named s2 v8
splits -
canon a7/t34/0/-/0=s1,a8/t11/0/-/0=s2
consts -
freev v3,v5,v7,v11,v12,v14,v16,v18,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2
cache linestarts 2:1050:1050
fstate scheduled,laidout
regalloc 22 v2:SP,v4:R26,v6:R0,v8:R2,v9:F0,v10:(R0;R2),v13:F0,v15:R1,v21:[]
dcllen 4
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t24,t25,t26
typelink t28=t32
typeorder t3,t7,t4,t8,t5,t9,t6,t10,t11,t14,t15,t25,t26,t12,t13,t2,t17,t18,t19,t20,t21,t35,t22,t23,t24,t33,t1,t36,t34,t16,t27,t28,t30,t29,t31,t37,t32
eof
"#

/-- `test/gcgort/main/init.func95.1,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "init.func95.1" 1
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
type t1 8 4 0 0 - "complex64"
name n1 ".autotmp_0" PAUTO t1 3 "main..autotmp_0" 0 -
name n2 ".autotmp_1" PAUTO t1 3 "main..autotmp_1" 0 a3
type t2 8 8 8 1 01 "chan complex64"
name n3 "a" PAUTO t2 0 "main.a" 0 a7
type t3 8 8 0 0 - "int"
name n4 "i" PAUTO t3 0 "main.i" 0 a8
in n1 0 used,autotmp
in n2 0 used,addrtaken,autotmp
in n3 0 used
in n4 0 used
out n2 -8 used,addrtaken,autotmp
opt n3 0 -
opt n4 0 -
opt n1 0 autotmp
stack 8 0 8
end
genin
posbase p2 "./gcgort.go" 1 1 -1 1 "./gcgort.go" "./gcgort.go" 1 1
sym y1 "main.init.func95.1" 1
curfn p2:1050:8:0:0 0 0
regargs -
text y1 0 0 0 0 1050 2080a0
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main..autotmp_1" 0
sym y4 "runtime.chansend1" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i0 0 0 p2:1050:8:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:1050:8:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:1050:8:0:0
p 3 3 0 0 0 - LDP 0 MEM/8218/0/0/NONE/0/8/-/- 0 - REGREG/8192/0/0/NONE/0/8194/-/- 0 0 p2:1050:8:1:0
p 4 4 0 0 0 - SCVTFS 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:1050:8:2:0
p 5 5 0 0 0 - FSTPS 0 REGREG/8224/0/0/NONE/0/8224/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y3/- 0 0 p2:1050:19:2:0
p 6 6 0 0 0 - MOVD 0 ADDR/8383/0/0/AUTO/0/-8/y3/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:1050:19:2:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:1050:19:2:0
p 8 8 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:1050:19:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p2:1050:65:0:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 1050 2080a0
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgslot 0 n3 t2 0
dbgslot 1 n4 t3 0
dbgvar 0 n3 0
dbgvar 1 n4 1
dbgloc 0 1:9:1:21:50
dbgloc 1 1:9:1:21:52
dbgregout -
dbgpc 1:9:5,1:21:9
end
asm
sym y5 "runtime.morestack" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i0 0 0 p2:1050:8:0:0
p 11 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:1050:8:0:0
p 12 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:1050:8:0:0
p 13 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:1050:8:0:0
p 14 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@23 0 0 p2:1050:8:0:0
p 15 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:1050:8:0:0
p 16 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p2:1050:8:0:1
p 17 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:1050:8:0:0
p 18 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:1050:8:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:1050:8:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:1050:8:0:0
p 3 24 0 0 245 - LDP 0 MEM/8218/0/0/NONE/87/8/-/- 0 - REGREG/8192/0/0/NONE/7/8194/-/- 0 0 p2:1050:8:1:0
p 4 28 0 0 418 - SCVTFS 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:1050:8:2:0
p 5 32 0 0 445 - FSTPS 0 REGREG/8224/0/0/NONE/7/8224/-/- 0 - MEM/0/0/0/AUTO/47/-8/y3/- 0 0 p2:1050:19:2:0
p 6 36 0 0 325 - MOVD 0 ADDR/0/0/0/AUTO/32/-8/y3/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:1050:19:2:0
p 7 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:1050:19:2:0
p 8 40 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y4/- 0 0 p2:1050:19:2:0
p 9 44 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:1050:65:0:0
p 19 48 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:1050:65:0:0
p 20 52 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:1050:65:0:0
p 21 56 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:1050:65:0:0
p 22 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:1050:8:0:0
p 23 56 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:1050:8:0:0
p 24 56 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:1050:8:0:0
p 25 60 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y5/- 0 0 p2:1050:8:0:0
p 26 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:1050:8:0:0
p 27 64 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@11 0 0 p2:1050:8:0:0
fn y1 0 40 0 0 1050 2080a0
funcaux y2 y2 - - - - -
text 80 0 900b40f9ff6330eb89010054fe0f1df8fd831ff8fd2300d1408b40a94000229ee003042de183009100000094fd835ff8fe0743f8c0035fd6e3031eaa00000094f0ffff17000000000000000000000000 2
reloc 40 4 R_CALLARM64 0 y4
reloc 60 4 R_CALLARM64 0 y5
pcln y8 y9 y10 y11 y6,y7 y2,y2
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y6 SRODATA 11 1 28000 00010102020b0102020400 0
data y7 SRODATA 7 1 28000 000a0204010600 0
data y8 SRODATA 7 1 28000 020460095f0700 0
data y9 SRODATA 3 1 28000 041400 0
data y10 SRODATA 4 1 28000 b6101400 0
data y11 SRODATA 3 1 28000 001400 0
end
dwarf
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.chan complex64" 0
sym y17 "go:info.int" 0
dwfn y12 y13 y14 - y15 "main.init.func95.1" 1:1050 1 0 1 221
dwdcl n2
dwclosure 1 n3:8,n4:16
dwparents -
dwparams -
dwname n2 1 1 1 0 0 0 -8 0 - - ? 0 0 ? p2:1050:19:0:0
dwname n3 1 0 0 0 0 0 0 0 - p2:1048:4:0:0 "chan complex64" 0 0 1 p2:1050:17:0:0
dwname n4 1 0 0 0 0 0 0 0 - p2:1049:8:0:0 "int" 0 0 1 p2:1050:48:0:0
dwname n1 1 0 1 0 0 0 0 0 - - "complex64" 0 0 1 p2:1050:39:0:0
var 0 0 "a" 52 1 0 0 0 -8 y16 "./gcgort.go" 1050 17 0 0 0 8 v0
var 1 0 "i" 52 1 0 0 0 -8 y17 "./gcgort.go" 1050 48 0 1 0 16 v1
scope 0 0 - 0,1
data y12 SDWARFFCN 61 0 0 036d61696e2e696e69742e66756e6339352e3100000050019c020000009a08012561009a080000000008000000002569009a0800000000100000000000 5
reloc 20 2 R_DWTXTADDR_U2 0 y1
reloc 37 4 R_DWARFSECREF 0 y16
reloc 42 4 R_DWARFSECREF 0 y13
reloc 51 4 R_DWARFSECREF 0 y17
reloc 56 4 R_DWARFSECREF 9 y13
data y13 SDWARFLOC 18 0 0 01000004202c01500001000004202c015200 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y14 SDWARFRANGE 0 0 0 - 0
data y15 SDWARFLINES 28 0 0 00090200000000000000000402039408140a8706af06af0224000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.init.func95.1`. -/
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

/-- The index of `v19`'s `FSTPS (F0, F0), .autotmp_1-8(AUTO)` among the Progs (`kdOK` checks it). -/
def jF : Nat := 5

/-- A PC table for `b1` with `v19` (index 8) at its `FSTPS` and `v15` (index 9) after it. -/
def tab : PcTab := [(1, [5, 5, 5, 5, 5, 5, 5, 5, 5, 6])]

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

/-- The class map before `v19`: `F0` (Go register 31) holds a 32-bit value, `SP` (30) 64 bits. -/
def K0 : KMap := (KMap.bot.set! 31 (some 32)).set! 30 (some 64)

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 32-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- `ι`: GenG2's, and `.autotmp_1`'s block (aux 3, a `temp` block) of activation 0 at `SP + 16`. -/
def ι57 (b : Blk) : Option (BitVec 64) :=
  if b = .temp 0 3 then some (GenG2.sp0 + 16) else GenG2.ι b

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0), no home slot,
the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := ι57, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The memory: `.autotmp_1`'s block (a `complex64`), 8 poison bytes. -/
def mem1 : Mem := { blocks := #[(.temp 0 3, { data := Array.replicate 8 .poison })] }

/-- The `float32` bits of `1.5`. -/
def xv : BitVec 32 := 0x3fc00000

/-- The `runLoc` state before `v19`: `v13 = float32(i)` in `F0` (Go register 31), every other
register `poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 31 then .int .w32 xv else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v19`: `V0` holds `xv`, the activation's `g` and `FP`, the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun k => if k = 0 then xv.setWidth 128 else 0,
    nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 8, mem := fun _ => 0 }

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

/-- `vkind57b` accepts `v19` with a pattern the Prog at `jF` matches. -/
def kdOK : Bool := (patOf (vkind57b lc g (val 19))).any fun pat => (ps[jF]?).any pat.ok

/-- What compiled evaluation checks on `main.init.func95.1` (`test/gcgort`): it holds an arm64
op; `checkG55` rejects it (first at `v13: op LoweredRound32F`) and `vkind55`
rejects `v19`, which `vkind57b` accepts with the Prog at `jF`; the Progs have distinct IDs below
`2^32`; every home is one G10 handles; `checkFrame` passes; `b1` holds `v19` (`FSTPS`) at index 8;
the only accessed frame variable is `.autotmp_1` (aux 3), operand `NAME_AUTO -8`, a `temp` block
of activation 0, at `frameOff 16`; there is no home slot; `v19` reads `F0` at class 32; and
`stepLoc` runs `v19`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG55 lc0 ps bs g).toOption.isNone &&
    (vkind55 lc g (val 19)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 19).isSome && blk.values[8]? == some 19 &&
    (val 19).op == .ARM64FSTPS &&
    accessedVars lc == [3] && varOp g 3 == some (.AUTO, -8) && !lc.ctx.tabs.forgeable 3 &&
    lc.ctx.act == 0 && (homeSlots lc).isEmpty && decide (frameOff L .AUTO (-8) = 16) &&
    (kReads lc (val 19)).all (fun rc => K0.get rc.1 == some rc.2) && K0.get 31 == some 32 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 19)) fun _ => true

theorem g57b_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (checkG55 lc0 ps bs g).toOption = none ∧
      (vkind55 lc g (val 19)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.block? 1 = some blk ∧ lc.ctx.f.value? 19 = some (val 19) ∧
      blk.values[8]? = some 19 ∧ (val 19).op = .ARM64FSTPS ∧
      accessedVars lc = [3] ∧ varOp g 3 = some (.AUTO, -8) ∧ lc.ctx.tabs.forgeable 3 = false ∧
      lc.ctx.act = 0 ∧ (homeSlots lc).isEmpty = true ∧ frameOff L .AUTO (-8) = 16 ∧
      (∀ rc ∈ kReads lc (val 19), K0.get rc.1 = some rc.2) ∧ K0.get 31 = some 32 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 19)) (fun _ => true) = true := by
  have hf := g57b_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hf
  obtain ⟨hl, h55, h55v, hkd, hlt, hnd, hhome, hcf, hbs, hvs, hi8, hop, hav, hvo, hfg, hact, hsl,
    hoff, hrd, hk31, hrun⟩ := hf
  refine ⟨hl, h55, h55v, hkd, hlt, hnd, homeOK10_all hhome, ?_, ?_, ?_, hi8, hop, hav, hvo, hfg,
    hact, hsl, hoff, hrd, hk31, hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-- `vkind57b`'s pattern for `v19` and the Prog at `jF` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind57b lc g (val 19) = some (.ok (.prog pat)) ∧ (ps[jF]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

theorem ι57_temp : ι57 (.temp 0 3) = some (GenG2.sp0 + 16) := by simp [ι57]

theorem ι57_ne {b : Blk} (h : b ≠ .temp 0 3) : ι57 b = GenG2.ι b := by simp [ι57, h]

theorem addrAgree57 : AddrAgree ι57 := by
  intro b n a hb ha hnt
  rw [ι57_ne (hnt 0 3)] at ha
  exact GenG2.addrAgree b n a hb ha hnt

theorem g57bEnv (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : accessedVars lc = [3])
    (hvo : varOp g 3 = some (.AUTO, -8)) (hfg : lc.ctx.tabs.forgeable 3 = false)
    (hact : lc.ctx.act = 0) (hsl : (homeSlots lc).isEmpty = true)
    (hoff : frameOff L .AUTO (-8) = 16) : G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree57
            glob := fun _ _ _ _ => by simp [E, ι57, GenG2.ι]; rfl
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
            show ι57 (.temp 0 3) = some (GenG2.sp0 + BitVec.ofInt 64 16)
            rw [ι57_temp]
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

theorem memInj1 : MemInj ι57 mem1 (fun _ => 0) where
  nil := by simp [ι57, GenG2.ι]
  mapped := by
    intro b al h
    simp [mem1] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨GenG2.sp0 + 16, ι57_temp, fun _ => by decide, by decide⟩
  inj := by
    intro b al b' al' a a' h h' hne
    simp [mem1] at h h'
    exact absurd (h.1.trans h'.1.symm) hne
  bytes := ⟨fun _ _ => False, by
    intro b al a h _
    simp [mem1] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]⟩

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι57 (StkAt E) mem1 := by
  intro b al a hb hι y hy
  simp [mem1] at hb
  obtain ⟨rfl, rfl⟩ := hb
  rw [ι57_temp] at hι
  cases hι
  rcases hy with ⟨-, h1, h2⟩ | ⟨k, off, h, -⟩
  · simp only [E, GenG2.sp0] at h1 h2
    simp only [GenG2.sp0, Array.size_replicate]
    rintro ⟨h3, -⟩
    have : (0x7fff0000 + 16 : BitVec 64).toNat = 0x7fff0010 := by decide
    rw [this] at h3
    have : (0x7fff0000 : BitVec 64).toNat = 0x7fff0000 := by decide
    rw [this] at h2
    omega
  · simp [E] at h

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 31 ∧ x = .int .w32 xv) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 8 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => by simp [objX?] at hk, fun k hk => ?_⟩
      simp only [objV?] at hk
      cases hk
      show (m0.v (BitVec.ofNat 5 (31 - 31))).setWidth 32 = xv
      simp only [m0]
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g57bInv0 (h31 : K0.get 31 = some 32) : G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h31] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G57, group B, on `main.init.func95.1`** (`test/gcgort`: `ch <- complex(float32(i),
float32(i))`, which stores the `complex64` into the temporary `.autotmp_1` and passes its address
to `runtime.chansend1`): `v19` (`FSTPS {.autotmp_1} SP v13 v13`, genssa's `FSTPS (F0, F0),
.autotmp_1-8(AUTO)`) is rejected by `vkind55` (`frame variable aux on FSTPS`) and accepted by
`vkind57b` (`checkG55` rejects the function, first at `v13`'s `LoweredRound32F`). From `s0`, with
`float32(1.5)` in `F0`
and the variable's `temp` block in memory, `stepLoc` runs `v19`, and `vk57b_step` relates it to a
machine run of its `FSTPS` to a state related before `v15`, under an activation extending `E` that
is again a `G49Env`. -/
theorem genG57b_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧ (vkind55 lc g (val 19)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 19) = .ok s1 ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 9 m1 := by
  obtain ⟨hl, h55, h55v, hkd, hlt, hnd, hhome, hcf, -, hv19, -, -, hav, hvo, hfg, hact, hsl,
    hoff, hrd, hk31, hrun⟩ := facts
  obtain ⟨s1, hs1, -⟩ := GenG1.okThen_spec hrun
  have hE := g57bEnv hlt hav hvo hfg hact hsl hoff
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind57b_spec hvk
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jF (jF + 1) :=
    ⟨jF, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), addrAgree57⟩
  have hj : E.pcOf 1 8 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 1 (8 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk57b_step (H := GenG2.H0) (L := []) (bid := 1)
    (i := 8) (j := jF) (j' := jF + 1) hE F hcf hv19 hVK hvs htemp hj hj' hrd locMatch0
    (g57bInv0 hk31) hs1
  exact ⟨h55, h55v, s1, E1, m1, hs1, hx1, hE1, hp1, hm1⟩

end GoFV.Proof.Witness.GenG57b
