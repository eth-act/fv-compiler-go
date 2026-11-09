import GoFV.Proof.Gen.G50
import GoFV.Proof.Witness.GenG47

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG50

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/c128equal,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "c128equal" 1 0 0
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
type t2 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(unsafe.Pointer, unsafe.Pointer) bool" "func(unsafe.Pointer, unsafe.Pointer) bool" 0 2 1
field 0 "p" t2 ? 0
field 1 "q" t2 ? 0
field 2 "" t3 ? 0
aux a2 sym "runtime.c128equal" "runtime.c128equal" 1 - 0 - - - - 0
posbase p96 "runtime/alg.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p96:302:16:0:0
aux a4 name "q" "q" PPARAM t2 8 1 used p96:302:19:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p96:302:37:0:0
aux a1 call "AuxCall{runtime.c128equal}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 8
abiparam out 0 t3 a5 0 -1
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
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t33 PTR 8 8 8 hasptr,direct,comparable "*unsafe.Pointer" "*unsafe.Pointer" t2
type t34 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
type t35 PTR 8 8 8 hasptr,direct,comparable "*complex128" "*complex128" t27
type t36 RESULTS ? ? ? - "bool,mem" "" 2 t3,t28
slot s1 a3 t2 0 - 0
slot s2 a4 t2 0 - 0
f b1 t1 a1 23 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t2,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 Copy t35 0 - p96:303:24:2:0 1 v7
v v11 NilCheck t35 0 - p96:303:9:0:0 1 v10,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v13 Copy t35 0 - p96:303:45:2:0 1 v8
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v13,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 Copy t35 0 - p96:303:24:2:0 1 v7
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v10,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v13 Copy t35 0 - p96:303:45:2:0 1 v8
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v13,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t16 0 - p0:0:0:0:0 3 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t34 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p96:302:6:2:0 2 -
v v8 Arg t2 0 a4 p96:302:6:2:0 2 -
v v9 ConstBool t3 0 - p0:0:0:0:0 0 -
v v10 Copy t35 0 - p96:303:24:2:0 0 v7
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v13 Copy t35 0 - p96:303:45:2:0 0 v8
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev -
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 96:303:303
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 Arg t2 0 a3 p96:302:6:2:0 1 -
v v8 Arg t2 0 a4 p96:302:6:2:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v13,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "p+0" a3 0
aux a7 nameoff "q+0" a4 0
f b1 t1 a1 23 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v12 Load t27 0 - p96:303:9:0:0 2 v11,v1
v v15 Load t27 0 - p96:303:30:0:0 2 v14,v1
v v16 ComplexReal t14 0 - p96:303:27:0:0 1 v12
v v17 ComplexReal t14 0 - p96:303:27:0:0 1 v15
v v19 ComplexImag t14 0 - p96:303:27:0:0 1 v12
v v20 ComplexImag t14 0 - p96:303:27:0:0 1 v15
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v16,v17
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v19,v20
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v13 SB t16 0 - p0:0:0:0:0 0 -
v v10 SP t16 0 - p0:0:0:0:0 2 -
v v9 OffPtr t33 0 - p0:0:0:0:0 0 v10
v v6 LocalAddr t34 0 a5 p96:303:2:0:0 0 v10,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v12 ComplexMake t27 0 - p96:303:9:0:0 0 v5,v4
v v15 ComplexMake t27 0 - p96:303:30:0:0 0 v2,v24
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v13 SB t16 0 - p0:0:0:0:0 0 -
v v10 SP t16 0 - p0:0:0:0:0 2 -
v v9 OffPtr t33 0 - p0:0:0:0:0 0 v10
v v6 LocalAddr t34 0 a5 p96:303:2:0:0 0 v10,v1
v v5 Load t14 0 - p96:303:9:0:0 2 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 2 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 2 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 2 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v12 ComplexMake t27 0 - p96:303:9:0:0 0 v5,v4
v v15 ComplexMake t27 0 - p96:303:30:0:0 0 v2,v24
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v13 SB t16 0 - p0:0:0:0:0 0 -
v v10 SP t16 0 - p0:0:0:0:0 2 -
v v9 OffPtr t33 0 - p0:0:0:0:0 0 v10
v v6 LocalAddr t34 0 a5 p96:303:2:0:0 0 v10,v1
v v5 Load t14 0 - p96:303:9:0:0 2 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 2 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 2 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 2 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v12 ComplexMake t27 0 - p96:303:9:0:0 0 v5,v4
v v15 ComplexMake t27 0 - p96:303:30:0:0 0 v2,v24
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v13 SB t16 0 - p0:0:0:0:0 0 -
v v10 SP t16 0 - p0:0:0:0:0 2 -
v v9 OffPtr t33 0 - p0:0:0:0:0 0 v10
v v6 LocalAddr t34 0 a5 p96:303:2:0:0 0 v10,v1
v v5 Load t14 0 - p96:303:9:0:0 2 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 2 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 2 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 2 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts 0=v9
freev v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 NilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 NilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 Eq64F t3 0 - p96:303:27:0:0 1 v5,v2
v v21 Eq64F t3 0 - p96:303:27:0:0 1 v4,v24
v v22 AndB t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Load t14 0 - p96:303:9:0:0 1 v11,v1
v v4 Load t14 0 - p96:303:9:0:0 1 v3,v1
v v3 OffPtr t24 8 - p96:303:9:0:0 1 v11
v v2 Load t14 0 - p96:303:30:0:0 1 v14,v1
v v24 Load t14 0 - p96:303:30:0:0 1 v25,v1
v v25 OffPtr t24 8 - p96:303:30:0:0 1 v14
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v6,v9,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 ARM64FMOVDload t14 0 - p96:303:9:0:0 1 v11,v1
v v4 ARM64FMOVDload t14 8 - p96:303:9:0:0 1 v11,v1
v v2 ARM64FMOVDload t14 0 - p96:303:30:0:0 1 v14,v1
v v24 ARM64FMOVDload t14 8 - p96:303:30:0:0 1 v14,v1
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v25,v3,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 ARM64FMOVDload t14 0 - p96:303:9:0:0 1 v11,v1
v v4 ARM64FMOVDload t14 8 - p96:303:9:0:0 1 v11,v1
v v2 ARM64FMOVDload t14 0 - p96:303:30:0:0 1 v14,v1
v v24 ARM64FMOVDload t14 8 - p96:303:30:0:0 1 v14,v1
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v25,v3,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 2 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 2 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 ARM64FMOVDload t14 0 - p96:303:9:0:0 1 v11,v1
v v4 ARM64FMOVDload t14 8 - p96:303:9:0:0 1 v11,v1
v v2 ARM64FMOVDload t14 0 - p96:303:30:0:0 1 v14,v1
v v24 ARM64FMOVDload t14 8 - p96:303:30:0:0 1 v14,v1
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v25,v3,v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 36 "pair"
type t37 TUPLE ? ? ? - "float64,float64" "" t14 t14
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 96:303:303
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v11 ARM64LoweredNilCheck t35 0 - p96:303:9:1:0 1 v7,v1
v v14 ARM64LoweredNilCheck t35 0 - p96:303:30:0:0 1 v8,v1
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v11,v1
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 2 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v11 ARM64LoweredNilCheck t30 0 - p96:303:9:1:0 0 v7,v1
v v14 ARM64LoweredNilCheck t30 0 - p96:303:30:0:0 0 v8,v1
v v25 ARM64FLDPD t37 0 - p96:303:9:0:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v25 ARM64FLDPD t37 0 - p96:303:9:1:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v25 ARM64FLDPD t37 0 - p96:303:9:1:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v13,v15,v12,v20,v19,v17,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.c128equal}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t2 a4 1 8
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v25 ARM64FLDPD t37 0 - p96:303:9:1:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v12,v13,v15,v16,v17,v19,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
regalloc 26 v2:F2,v3:(F2;F3),v4:F1,v5:F0,v7:R0,v8:R1,v18:R1,v21:R2,v22:R0,v23:[],v24:F3,v25:(F0;F1)
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v25 ARM64FLDPD t37 0 - p96:303:9:1:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v12,v13,v15,v16,v17,v19,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
regalloc 26 v2:F2,v3:(F2;F3),v4:F1,v5:F0,v7:R0,v8:R1,v18:R1,v21:R2,v22:R0,v23:[],v24:F3,v25:(F0;F1)
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 25 1
b b1 Ret p96:303:45:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a6 p96:303:45:1:0 1 -
v v8 ArgIntReg t2 1 a7 p96:303:45:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v25 ARM64FLDPD t37 0 - p96:303:9:1:0 2 v7,v1
v v4 Select1 t14 0 - p96:303:9:0:0 1 v25
v v5 Select0 t14 0 - p96:303:9:0:0 1 v25
v v3 ARM64FLDPD t37 0 - p96:303:30:0:0 2 v8,v1
v v2 Select0 t14 0 - p96:303:30:0:0 1 v3
v v24 Select1 t14 0 - p96:303:30:0:0 1 v3
v v6 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v5,v2
v v18 ARM64Equal t3 0 - p96:303:27:0:0 1 v6
v v9 ARM64FCMPD t29 0 - p96:303:27:0:0 1 v4,v24
v v21 ARM64Equal t3 0 - p96:303:27:0:0 1 v9
v v22 ARM64AND t3 0 - p96:303:27:0:0 1 v18,v21
v v23 MakeResult t36 0 - p96:303:2:0:0 1 v22,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t2/0/-/0=s2
consts -
freev v10,v12,v13,v15,v16,v17,v19,v20
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 96:303:303
fstate scheduled,laidout
regalloc 26 v2:F2,v3:(F2;F3),v4:F1,v5:F0,v7:R0,v8:R1,v18:R1,v21:R2,v22:R0,v23:[],v24:F3,v25:(F0;F1)
dcllen 3
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t22,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t26,t27,t13,t14,t3,t18,t19,t20,t21,t22,t35,t23,t24,t34,t25,t33,t1,t17,t2,t28,t30,t29,t31,t37,t32,t36
eof
"#

/-- `std/std/runtime/c128equal,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "c128equal" 1
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
type t1 8 8 8 1 01 "unsafe.Pointer"
name n1 "p" PPARAM t1 1 "runtime.p" 0 a3
name n2 "q" PPARAM t1 1 "runtime.q" 0 a4
type t2 1 1 0 0 - "bool"
name n3 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a5
in n1 0 used
in n2 8 used
in n3 0 outregs
out n1 0 used
out n2 8 used
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p96 "runtime/alg.go" 1 1 -1 93 "runtime/alg.go" "runtime/alg.go" 1 1
sym y1 "runtime.c128equal" 1
curfn p96:302:6:0:0 0 0
regargs 8192:0:t1,8193:8:t1
text y1 0 0 0 0 302 200080
end
prog0
sym y2 "gclocals\xc2\xb7TswRR9Pia9Wsluv5u1sUnA==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.c128equal.arginfo1" 0
sym y5 "runtime.c128equal.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p96:302:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p96:302:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p96:302:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p96:302:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p96:302:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p96:302:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p96:303:9:1:0
p 7 7 0 0 0 - FLDPD 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REGREG/8224/0/0/NONE/0/8225/-/- 0 0 p96:303:9:1:0
p 8 8 0 0 0 - FLDPD 0 MEM/8193/0/0/NONE/0/0/-/- 0 - REGREG/8226/0/0/NONE/0/8227/-/- 0 0 p96:303:30:2:0
p 9 9 0 0 0 - FCMPD 0 REG/8226/0/0/NONE/0/0/-/- 8224 - _ 0 0 p96:303:27:2:0
p 10 10 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/128/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p96:303:27:2:0
p 11 11 0 0 0 - FCMPD 0 REG/8227/0/0/NONE/0/0/-/- 8225 - _ 0 0 p96:303:27:2:0
p 12 12 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/128/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p96:303:27:2:0
p 13 13 0 0 0 - AND 0 REG/8194/0/0/NONE/0/0/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p96:303:27:2:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p96:303:45:2:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 302 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t1 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgloc 0 1:-10000:1:22:50
dbgloc 1 1:-10000:1:18:51
dbgregout n3
dbgpc 1:22:14,1:18:11
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p96:302:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p96:302:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p96:302:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p96:302:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p96:302:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p96:302:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p96:303:9:1:0
p 7 0 0 0 245 - FLDPD 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REGREG/8224/0/0/NONE/7/8225/-/- 0 0 p96:303:9:1:0
p 8 4 0 0 245 - FLDPD 0 MEM/8193/0/0/NONE/77/0/-/- 0 - REGREG/8226/0/0/NONE/7/8227/-/- 0 0 p96:303:30:2:0
p 9 8 0 0 114 - FCMPD 0 REG/8226/0/0/NONE/5/0/-/- 8224 - NONE/0/0/0/NONE/1/0/-/- 0 0 p96:303:27:2:0
p 10 12 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/128/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p96:303:27:2:0
p 11 16 0 0 114 - FCMPD 0 REG/8227/0/0/NONE/5/0/-/- 8225 - NONE/0/0/0/NONE/1/0/-/- 0 0 p96:303:27:2:0
p 12 20 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/128/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p96:303:27:2:0
p 13 24 0 0 49 - AND 0 REG/8194/0/0/NONE/2/0/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p96:303:27:2:0
p 14 28 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p96:303:45:2:0
fn y1 16 0 0 0 302 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
text 32 0 0004406d220c406d0020621ee1179f9a2020631ee2179f9a2000028ac0035fd6 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 93
data y2 Sxxx 0 4 8000 02000000020000000300 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080808ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010800 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040800 0
data y10 SRODATA 3 1 28000 020800 0
data y11 SRODATA 4 1 28000 bc010800 0
data y12 SRODATA 4 1 28000 e0040800 0
data y13 SRODATA 3 1 28000 000800 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.unsafe.Pointer" 0
sym y19 "go:info.bool" 0
sym y20 "type:bool" 0
dwfn y14 y15 y16 - y17 "runtime.c128equal" 93:302 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p96:302:16:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "unsafe.Pointer" 0 0 1 p96:302:19:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p96:302:37:0:0
var 0 0 "p" 5 1 0 0 0 8 y18 "runtime/alg.go" 302 16 0 0 0 0 v0
var 1 0 "q" 5 1 0 0 0 16 y18 "runtime/alg.go" 302 19 0 1 0 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y19 "runtime/alg.go" 302 37 0 2 0 0 -
scope 0 0 - 0,1,2
data y14 SDWARFFCN 73 0 0 0372756e74696d652e63313238657175616c00000020019c5e000000ae02012d700000ae0200000000000000002d710000ae0200000000000000002e7e72300001ae02000000000000 7
reloc 0 0 R_USETYPE 0 y20
reloc 19 2 R_DWTXTADDR_U2 0 y1
reloc 37 4 R_DWARFSECREF 0 y18
reloc 41 4 R_DWARFSECREF 0 y15
reloc 51 4 R_DWARFSECREF 0 y18
reloc 55 4 R_DWARFSECREF 9 y15
reloc 67 4 R_DWARFSECREF 0 y19
data y15 SDWARFLOC 18 0 0 01000004001c015000010000040010015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000045e03a902140637021c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.c128equal`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G50's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG50` gives (`b1`: `v25`'s `FLDPD (R0), (F0, F1)` at Prog 7 after the
`PCDATA`s at 5 and 6, `v4`'s `FLDPD (R1), (F2, F3)` at 8, the compares, `CSET`s and `AND`, then the
`RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 8, 8, 8, 9, 9, 9, 10, 11, 12, 13, 14, 14])]

/-- The class table `checkG50` gives. -/
def kt : KTab := (match checkG50 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The machine address of `heap 1` (`GenG12.ι`). -/
def A : BitVec 64 := 0x20000000000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `A` and the PC table of `checkG50`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The bits of `1.5`, the real part. -/
def re : BitVec 64 := 0x3ff8000000000000

/-- The bits of `2.5`, the imaginary part. -/
def im : BitVec 64 := 0x4004000000000000

/-- The complex number `p` points to: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- Its imaginary part, 8 bytes above. -/
def pQ : Ptr := ⟨.heap 1, 8⟩

/-- The bytes of `heap 1`: `1.5 + 2.5i` (little-endian `re` at offset 0, `im` at offset 8). -/
def byteF (i : Nat) : BitVec 8 :=
  if i = 6 then 0xf8 else if i = 7 then 0x3f else if i = 14 then 0x04 else if i = 15 then 0x40
  else 0

/-- The Phase 1 memory before `v25`: `heap 1` a block of 16 bytes `byteF`. -/
def mem1 : Mem :=
  { blocks := #[(.heap 1, { data := Array.ofFn (n := 16) fun i => .b (byteF i.val) })],
    nextHeap := 2 }

/-- The machine memory before `v25`: the bytes of `heap 1` at `A`, 0 elsewhere. -/
def M1 : Memory := fun y => if (y - A).toNat < 16 then byteF (y - A).toNat else 0

/-- The `runLoc` state before `v25`: the pointer `p` (`pB`, `v7`) in `R0`, every other register
`poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pB else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v25`: `X0` the address `A` of `p`, the V registers 0, the activation's `g`
and `FP`, the PC of `v25`, the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 3, mem := M1 }

/-- The value is the 64-bit `w`. -/
def isW (w : BitVec 64) : Val → Bool
  | .int .w64 x => x == w
  | _ => false

theorem isW_spec {w : BitVec 64} {x : Val} (h : isW w x = true) : x = .int .w64 w := by
  unfold isW at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- The register holds the 64-bit `w`. -/
def isWO (w : BitVec 64) : Option Val → Bool
  | some x => isW w x
  | none => false

theorem isWO_spec {w : BitVec 64} {o : Option Val} (h : isWO w o = true) :
    o = some (.int .w64 w) := by
  unfold isWO at h
  split at h
  · rw [isW_spec h]
  · cases h

/-- `v25`'s addresses in `s0`: its argument read as a value whose `pairAddr` at 8-byte elements is
`(pB, pQ)`. -/
def pairIsPQ (s : LocState) : Bool :=
  GenG1.okThen (s.read lc 7) fun x => pairAddr lc.ctx (val 25) 8 x == some (pB, pQ)

theorem pairIsPQ_spec {s : LocState} (h : pairIsPQ s = true) :
    ∃ x, s.read lc 7 = .ok x ∧ pairAddr lc.ctx (val 25) 8 x = some (pB, pQ) := by
  obtain ⟨x, hx, h1⟩ := GenG1.okThen_spec h
  exact ⟨x, hx, by simpa using h1⟩

/-- What compiled evaluation checks on `runtime.c128equal`: it holds an arm64 op; `checkG50`
accepts it with `tab` and `kt` and `checkG47` does not; it accesses no frame variable and has no
home slot; `b1` holds `v25` (`FLDPD v7 v1`, of type `(float64, float64)`, in `(F0, F1)`) at index
3, where `R0` has class 64 and G35's table is empty; in `s0` its addresses are `pB` and `pQ`, where
`mem1` has 8 readable bytes each, read at the component shapes as `re` and `im`; `stepLoc` runs
`v25` from `s0` to `F0 = re`, `F1 = im`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG50 lc0 ps bs g).toOption == some (tab, kt) && (checkG47 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 25).isSome && blk.values[3]? == some 25 &&
    (val 25).op == .ARM64FLDPD && (val 25).args[0]? == some 7 &&
    (kAt lc kt 1 blk 3).get 0 == some 64 && uL35 lc (uIn35 lc 1) blk 3 == [] &&
    pairIsPQ s0 && (mem1.read pB 8).isSome && (mem1.read pQ 8).isSome &&
    isW re ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 0) 8 false mem1 pB).retypeL
      (Arm64.tupleTy (lc.ty (val 25).id) 0)) &&
    isW im ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 1) 8 false mem1 pQ).retypeL
      (Arm64.tupleTy (lc.ty (val 25).id) 1)) &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 25))
      (fun s1 => isWO re s1.regs[31]? && isWO im s1.regs[32]?)

theorem g50_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG50 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG47 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 25 = some (val 25) ∧ blk.values[3]? = some 25 ∧
      (val 25).op = .ARM64FLDPD ∧ (val 25).args[0]? = some 7 ∧
      (kAt lc kt 1 blk 3).get 0 = some 64 ∧ uL35 lc (uIn35 lc 1) blk 3 = [] ∧
      pairIsPQ s0 = true ∧ (mem1.read pB 8).isSome = true ∧ (mem1.read pQ 8).isSome = true ∧
      isW re ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 0) 8 false mem1 pB).retypeL
        (Arm64.tupleTy (lc.ty (val 25).id) 0)) = true ∧
      isW im ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 1) 8 false mem1 pQ).retypeL
        (Arm64.tupleTy (lc.ty (val 25).id) 1)) = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 25))
        (fun s1 => isWO re s1.regs[31]? && isWO im s1.regs[32]?) = true := by
  have hf := g50_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h47, hav, hsl, hm1, hbs, hvs, hi3, hop, ha0, hk0, hu3, hq, hrp, hrq, hre, him,
    hrun⟩ := hf
  refine ⟨hl, ?_, h47, hav, hsl, hm1, ?_, ?_, hi3, hop, ha0, hk0, hu3, hq, hrp, hrq, hre, him,
    hrun⟩
  · revert hres; cases checkG50 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g50Env (hc : checkG50 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
    (hav : (accessedVars lc).isEmpty = true) (hsl : (homeSlots lc).isEmpty = true) :
    G28Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          lcEq := rfl
          link := rfl
          pcOf := rfl
          retOut := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG50L_spec hl (checkG50_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG50L_spec hl (checkG50_spec hc).2
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
  memeqs := fun h => by cases h

/-! ## The memory -/

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .heap 1 ∧ al = { data := Array.ofFn (n := 16) fun i => .b (byteF i.val) } := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `GenG12.ι`: `heap 1`'s bytes at `A`. -/
theorem memInj1 : MemInj GenG12.ι mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := mem1_blocks h
    obtain ⟨rfl, -⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_ofFn] at hi
    have hd : (A + BitVec.ofNat 64 i - A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, M1, hd, hi]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom GenG12.ι (StkAt E) mem1 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := mem1_blocks h
  have ha' : a = A := by simp [GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_ofFn]
    omega
  · cases hk

/-! ## `v25`: `FLDPD (R0), (F0, F1)` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pB) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 3 m0 where
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
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E, A]; decide,
    by simp only [MState.word, readMem, m0, M1, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g50Inv0 (h0 : (kAt lc kt 1 blk 3).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G46 on `v25`, `FLDPD`: none of them applies. -/
theorem pre46 (hop : (val 25).op = .ARM64FLDPD) : G46Pre lc s0 (val 25) := by
  have hne : ∀ o : Op, o ≠ .ARM64FLDPD → (val 25).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩
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

/-- `v25` reads 8 valid bytes of `heap 1` at `pB` and at `pQ`, read at its component shapes as the
bits of `1.5` and `2.5`, no pointer. -/
theorem pairPre0 (hop : (val 25).op = .ARM64FLDPD) (ha0 : (val 25).args[0]? = some 7)
    (hq : pairIsPQ s0 = true) (hrp : (mem1.read pB 8).isSome = true)
    (hrq : (mem1.read pQ 8).isSome = true)
    (hre : isW re ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 0) 8 false mem1 pB).retypeL
      (Arm64.tupleTy (lc.ty (val 25).id) 0)) = true)
    (him : isW im ((Arm64.loadN (Arm64.tupleTy (lc.ty (val 25).id) 1) 8 false mem1 pQ).retypeL
      (Arm64.tupleTy (lc.ty (val 25).id) 1)) = true) :
    PairPre50 lc s0 (val 25) := by
  intro as n sg fp hpo a x ha hx
  have hpo' := hpo
  rw [hop] at hpo'
  simp only [pairOp50, reduceCtorEq, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpo'
  obtain ⟨-, rfl, -, rfl⟩ := hpo'
  rw [ha0] at ha
  cases ha
  obtain ⟨x', hx', hp⟩ := pairIsPQ_spec hq
  rw [hx] at hx'
  cases hx'
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrp
  obtain ⟨bs', hbs'⟩ := Option.isSome_iff_exists.1 hrq
  refine ⟨pB, pQ, mem1, bs, bs', hp, rfl, hbs, hbs', fun _ t0 t1 hty => ⟨fun r hr => ?_,
    fun r hr => ?_⟩⟩
  · have ht : Arm64.tupleTy (lc.ty (val 25).id) 0 = t0 := by rw [hty]; rfl
    have h' := isW_spec hre
    rw [ht] at h'
    rw [h'] at hr
    cases hr
  · have ht : Arm64.tupleTy (lc.ty (val 25).id) 1 = t1 := by rw [hty]; rfl
    have h' := isW_spec him
    rw [ht] at h'
    rw [h'] at hr
    cases hr

/-- **G50 on `runtime.c128equal`** (`func c128equal(p, q unsafe.Pointer) bool { return
*(*complex128)(p) == *(*complex128)(q) }`): `b1` loads `*p` (`v25`, `FLDPD v7 v1`, of type
`(float64, float64)`, in `(F0, F1)`) with the pair load `FLDPD (R0), (F0, F1)`, which `checkG47`
rejects and `checkG50` accepts. From `s0`, with `p` (`heap 1`) in `R0` and `*p = 1.5 + 2.5i`,
`stepLoc` runs `v25` to `F0 = 1.5`, `F1 = 2.5` (their bits), and `g50_value` relates it to a machine
state after `v25`'s code whose `V0` and `V1` hold those bits in their low 64, under an activation
extending `E` that is again a `G28Env`. -/
theorem genG50_witness :
    (checkG47 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 25) = .ok s1 ∧
        s1.regs[31]? = some (.int .w64 re) ∧ s1.regs[32]? = some (.int .w64 im) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 4 m1 ∧ (m1.v 0).setWidth 64 = re ∧ (m1.v 1).setWidth 64 = im := by
  obtain ⟨hl, hc, h47, hav, hsl, hm1, hb, hv25, hi3, hop, ha0, hk0, hu3, hq, hrp, hrq, hre, him,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr0 := isWO_spec hr.1
  have hr1 := isWO_spec hr.2
  have hE := g50Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FLDPD → (val 25).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g50_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 25 = some (val 25) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv25
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g50_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi3 hv0 (by rw [hop]; rfl) locMatch0 (g50Inv0 hk0)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 3); rw [hu3]; intro e he; cases he)
    ⟨pre46 hop, pairPre0 hop ha0 hq hrp hrq hre him⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h47, s1, E1, m1, hs1, hr0, hr1, hx1, hE1, hp1, hm1', ?_, ?_⟩
  · exact (hm1'.regs 31 _ hr0).2 0 (by simp [objV?])
  · exact (hm1'.regs 32 _ hr1).2 1 (by simp [objV?])

end GoFV.Proof.Witness.GenG50
