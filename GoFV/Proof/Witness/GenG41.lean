import GoFV.Proof.Gen.G41
import GoFV.Proof.Witness.GenG37

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG41

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/traceNextGen,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "traceNextGen" 1 0 0
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
type t1 FUNC 8 8 8 hasptr,direct "func(uintptr) uintptr" "func(uintptr) uintptr" 0 1 1
field 0 "gen" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "runtime.traceNextGen" "runtime.traceNextGen" 1 - 0 - - - - 0
posbase p87 "runtime/trace.go" 1 1 -1
aux a3 name "gen" "gen" PPARAM t2 0 1 used p87:856:19:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p87:856:32:0:0
aux a1 call "AuxCall{runtime.traceNextGen}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
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
type t33 RESULTS ? ? ? - "uintptr,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 17 3
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t2,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:0:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v13 Copy t2 0 - p87:863:13:2:0 1 v6
v v15 Add64 t2 0 - p87:863:13:0:0 1 v13,v14
v v16 Copy t28 0 - p87:863:2:2:0 1 v1
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v16
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v11 Copy t28 0 - p87:861:3:2:0 1 v1
v v12 MakeResult t33 0 - p87:861:3:0:0 1 v10,v11
names s1
named s1 v6,v13
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v7,1=v14,4=v10
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v13 Copy t2 0 - p87:863:13:2:0 1 v6
v v15 Add64 t2 0 - p87:863:13:1:0 1 v13,v14
v v16 Copy t28 0 - p87:863:2:2:0 1 v1
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v16
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v11 Copy t28 0 - p87:861:3:2:0 1 v1
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v11
names s1
named s1 v6,v13
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v7,1=v14,4=v10
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p87:856:6:2:0 3 -
v v7 Const64 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v13 Copy t2 0 - p87:863:13:2:0 0 v6
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v16 Copy t28 0 - p87:863:2:2:0 0 v1
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v11 Copy t28 0 - p87:861:3:2:0 0 v1
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6,v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v7,1=v14,4=v10
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 87:857:863
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 Arg t2 0 a3 p87:856:6:2:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v11,v16,v13,v7,v5,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "gen+0" a3 0
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v11 SB t2 0 - p0:0:0:0:0 0 -
v v16 SP t2 0 - p0:0:0:0:0 3 -
v v13 OffPtr t21 0 - p0:0:0:0:0 0 v16
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
v v7 LocalAddr t21 0 a4 p87:863:2:0:0 0 v16,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v5 LocalAddr t21 0 a4 p87:861:3:1:0 0 v16,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v13,1=v14,4=v10
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v11 SB t2 0 - p0:0:0:0:0 0 -
v v16 SP t2 0 - p0:0:0:0:0 3 -
v v13 OffPtr t21 0 - p0:0:0:0:0 0 v16
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
v v7 LocalAddr t21 0 a4 p87:863:2:0:0 0 v16,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v5 LocalAddr t21 0 a4 p87:861:3:1:0 0 v16,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v13,1=v14,4=v10
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v11 SB t2 0 - p0:0:0:0:0 0 -
v v16 SP t2 0 - p0:0:0:0:0 3 -
v v13 OffPtr t21 0 - p0:0:0:0:0 0 v16
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
v v7 LocalAddr t21 0 a4 p87:863:2:0:0 0 v16,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v5 LocalAddr t21 0 a4 p87:861:3:1:0 0 v16,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v13,1=v14,4=v10
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
v v11 SB t2 0 - p0:0:0:0:0 0 -
v v16 SP t2 0 - p0:0:0:0:0 3 -
v v13 OffPtr t21 0 - p0:0:0:0:0 0 v16
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
v v7 LocalAddr t21 0 a4 p87:863:2:0:0 0 v16,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v5 LocalAddr t21 0 a4 p87:861:3:1:0 0 v16,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,0=v13,1=v14,4=v10
freev v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 17 3
b b1 If p87:857:12:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v8 Const64 t2 -1 - p0:0:0:0:0 1 -
v v10 Const64 t2 4 - p0:0:0:0:0 1 -
v v14 Const64 t2 1 - p0:0:0:0:0 1 -
v v9 Eq64 t3 0 - p87:857:9:1:0 1 v6,v8
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 Add64 t2 0 - p87:863:13:1:0 1 v6,v14
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -1=v8,1=v14,4=v10
freev v5,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 87:857:863
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v10 ARM64MOVDconst t2 4 - p0:0:0:0:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v10,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v14,v8,v7,v13,v16,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.traceNextGen}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v9 ARM64MOVDconst t2 4 - p87:861:3:2:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v9,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v11,v13,v14,v16
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
regalloc 18 v6:R0,v9:R0,v12:[],v15:R0,v17:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v9 ARM64MOVDconst t2 4 - p87:861:3:2:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v9,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v11,v13,v14,v16
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
regalloc 18 v6:R0,v9:R0,v12:[],v15:R0,v17:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 17 3
b b1 ARM64EQ p87:857:12:0:0 0 0 - v5 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a5 p87:857:12:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v5 ARM64CMNconst t29 1 - p87:857:9:1:0 1 v6
b b3 Ret p87:861:10:1:0 0 0 - v12 - b1:0
v v9 ARM64MOVDconst t2 4 - p87:861:3:2:0 1 -
v v12 MakeResult t33 0 - p87:861:3:1:0 1 v9,v1
b b2 Ret p87:863:15:1:0 0 0 - v17 - b1:1
v v15 ARM64ADDconst t2 1 - p87:863:13:1:0 1 v6
v v17 MakeResult t33 0 - p87:863:2:0:0 1 v15,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v7,v8,v11,v13,v14,v16
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b3:b1,b2:b1
cache sdom b1:-:b2:-:2:17,b3:b1:-:-:11:14,b2:b1:-:b3:5:8
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 87:857:863
fstate scheduled,laidout
regalloc 18 v6:R0,v9:R0,v12:[],v15:R0,v17:[]
dcllen 2
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t2,t25,t26,t13,t14,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `std/std/runtime/traceNextGen,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "traceNextGen" 1
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
name n1 "gen" PPARAM t1 1 "runtime.gen" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p87 "runtime/trace.go" 1 1 -1 85 "runtime/trace.go" "runtime/trace.go" 1 1
sym y1 "runtime.traceNextGen" 1
curfn p87:856:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 856 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.traceNextGen.arginfo1" 0
sym y4 "runtime.traceNextGen.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p87:856:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p87:856:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p87:856:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p87:856:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p87:856:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p87:856:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p87:857:9:1:0
p 7 7 0 0 0 - CMN 0 CONST/0/0/0/NONE/0/1/-/- 8192 - _ 0 0 p87:857:9:1:0
p 8 8 0 0 0 - BNE 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@11 0 0 p87:857:12:2:0
p 9 9 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/4/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p87:861:3:1:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p87:861:10:2:0
p 11 11 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p87:863:13:1:0
p 12 12 0 0 0 - RET 0 _ 0 - _ 0 0 p87:863:15:2:0
p 13 13 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 856 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:3:9:50
dbgregout n2
dbgpc 3:9:10
end
asm
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p87:856:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p87:856:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p87:856:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p87:856:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p87:856:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p87:856:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p87:857:9:1:0
p 7 0 0 0 96 - CMN 0 CONST/0/0/0/NONE/17/1/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p87:857:9:1:0
p 8 4 0 0 80 - BNE 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/11/-/@11 0 0 p87:857:12:2:0
p 9 8 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/4/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p87:861:3:1:0
p 10 12 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p87:861:10:2:0
p 11 16 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p87:863:13:1:0
p 12 20 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p87:863:15:2:0
fn y1 8 0 0 0 856 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 32 0 1f0400b161000054e0037eb2c0035fd600040091c0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 85
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 3 1 28000 010800 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040800 0
data y9 SRODATA 3 1 28000 020800 0
data y10 SRODATA 4 1 28000 ac010800 0
data y11 SRODATA 8 1 28000 b40d020802040400 0
data y12 SRODATA 3 1 28000 000800 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.runtime.traceNextGen$abstract" 0
sym y17 "" 0
sym y18 "go:info.uintptr" 0
sym y19 "type:uintptr" 0
dwfn y13 y14 y15 y16 y17 "runtime.traceNextGen" 85:856 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uintptr" 0 0 1 p87:856:19:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uintptr" 0 0 1 p87:856:32:0:0
var 0 0 "gen" 5 1 0 0 0 8 y18 "runtime/trace.go" 856 19 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y18 "runtime/trace.go" 856 32 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:26
data y13 SDWARFFCN 33 0 0 0600000000000020019c2900000000000000002e7e72300001d806000000000000 6
reloc 0 0 R_USETYPE 0 y19
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y16
reloc 15 4 R_DWARFSECREF 0 y14
reloc 27 4 R_DWARFSECREF 0 y18
data y14 SDWARFLOC 9 0 0 01000004000c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 32 0 0 0009020000000000000000045603d306140637063b063706390637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 37 0 1 0572756e74696d652e74726163654e65787447656e0001d806012267656e00000000000000 1
reloc 32 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `traceNextGen`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G41's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG41` gives (`b1`: `v6`, `v1`, `v5`, then the branch). -/
def tab : PcTab := [(1, [5, 5, 5, 8]), (3, [9, 10, 10]), (2, [11, 12, 12])]

/-- The class table `checkG41` gives. -/
def kt : KTab := (match checkG41 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG41`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v5`: `gen = -1` (`v6`) in `R0`, every other register `poison`, the
empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 (-1) else .poison,
    flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v5`: `X0 = -1`, the activation's `g` and `FP`, the PC of `v5`, a zero
memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then -1 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The flags have `Z` set. -/
def zSet : Val → Bool
  | .agg [_, .bool true, _, _, _] => true
  | _ => false

theorem zSet_spec {f : Val} (h : zSet f = true) :
    ∃ n c v g, f = .agg [n, .bool true, c, v, g] := by
  unfold zSet at h
  split at h
  · rename_i n c v g; exact ⟨n, c, v, g, rfl⟩
  · cases h

/-- The result is an integer. -/
def isInt : Res Val → Bool
  | .ok (.int _ _) => true
  | _ => false

theorem isInt_spec {r : Res Val} (h : isInt r = true) : ∃ w i, r = .ok (.int w i) := by
  unfold isInt at h
  split at h
  · rename_i w i; exact ⟨w, i, rfl⟩
  · cases h

/-- Reading `v6` from `s0` gives an integer. -/
def readInt : Bool := isInt (s0.read lc 6)

theorem readInt_spec (h : readInt = true) : ∃ w i, s0.read lc 6 = .ok (.int w i) :=
  isInt_spec h

/-- What compiled evaluation checks on `traceNextGen`: it holds an arm64 op; `checkG41` accepts it
with `tab` and `kt` and `checkG40` does not; it accesses no frame variable and has no home slot;
`b1` holds `v5` (`CMNconst [1] v6`) at index 2, where `R0` has class 64 and G35's table is empty;
`stepLoc` runs `v5` from `s0` to flags with `Z` set; reading `v6` from `s0` gives an integer. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG41 lc0 ps bs g).toOption == some (tab, kt) && (checkG40 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 5).isSome && blk.values[2]? == some 5 && (val 5).op == .ARM64CMNconst &&
    (val 5).args[0]? == some 6 && (kAt lc kt 1 blk 2).get 0 == some 64 &&
    uL35 lc (uIn35 lc 1) blk 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 5)) (fun s1 => zSet s1.flags) && readInt

theorem g41_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG41 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG40 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 5 = some (val 5) ∧ blk.values[2]? = some 5 ∧
      (val 5).op = .ARM64CMNconst ∧ (val 5).args[0]? = some 6 ∧
      (kAt lc kt 1 blk 2).get 0 = some 64 ∧ uL35 lc (uIn35 lc 1) blk 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 5)) (fun s1 => zSet s1.flags) = true ∧
      readInt = true := by
  have hf := g41_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h40, hav, hsl, hm1, hbs, hvs, hi2, hop, ha0, hk0, hu2, hrun, hri⟩ := hf
  refine ⟨hl, ?_, h40, hav, hsl, hm1, ?_, ?_, hi2, hop, ha0, hk0, hu2, hrun, hri⟩
  · revert hres; cases checkG41 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g41Env (hc : checkG41 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              checkG41L_spec hl (checkG41_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG41L_spec hl (checkG41_spec hc).2
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

/-! ## `v5`: `CMN $1, R0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 (-1)) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h1; exact Or.inl ⟨h1, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 0 = -1 by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g41Inv0 (h0 : (kAt lc kt 1 blk 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v5`, `CMNconst`: G38's do not apply, and `CmpPre` holds (`gen` is
an integer, no pointer). -/
theorem pre5 (hop : (val 5).op = .ARM64CMNconst) (ha0 : (val 5).args[0]? = some 6)
    (hri : readInt = true) :
    G41Pre lc s0 (val 5) := by
  have hne : ∀ o : Op, o ≠ .ARM64CMNconst → (val 5).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro h; rcases h with h | h <;> exact absurd h (hne _ (by decide))
  · intro _ _ _ hl; rw [hop] at hl; cases hl
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro h; exact absurd h (hne _ (by decide))
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl
  · intro _ _ hl; rw [hop] at hl; cases hl
  · intro _ a x ha hx p hp
    rw [ha0] at ha
    cases ha
    subst hp
    obtain ⟨w, i, hr⟩ := readInt_spec hri
    rw [hr] at hx
    cases hx

/-- **G41 on `runtime.traceNextGen`**: `b1` compares `gen` (`v6`, `-1` in `R0`) with `-1` by
`CMN $1, R0` (`v5`, `CMNconst`), which `checkG40` rejects and `checkG41` accepts. From `s0`,
where `gen` is an integer (`CmpPre`), `stepLoc` runs `v5` to flags with `Z` set, and
`g41_value` relates the result to a machine state after `v5`'s code whose `Z` is set, under an
activation extending `E` that is again a `G28Env`. -/
theorem genG41_witness :
    (checkG40 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 5) = .ok s1 ∧
        (∃ n c v gf, s1.flags = .agg [n, .bool true, c, v, gf]) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧ m1.nzcv.z = true := by
  obtain ⟨hl, hc, h40, hav, hsl, hm1, hb, hv5, hi2, hop, ha0, hk0, hu2, hrun, hri⟩ := facts
  obtain ⟨s1, hs1, hz⟩ := GenG1.okThen_spec hrun
  obtain ⟨n, c, v, gf, hf⟩ := zSet_spec hz
  have hE := g41Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64CMNconst → (val 5).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g41_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 5 = some (val 5) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv5
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g41_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g41Inv0 hk0)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 2); rw [hu2]; intro e he; cases he)
    (pre5 hop ha0 hri)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h40, s1, E1, m1, hs1, ⟨n, c, v, gf, hf⟩, hx1, hE1, hp1, hm1', ?_⟩
  have hfl := hm1'.flags
  rw [hf] at hfl
  simp only [FlagsRel, BitRel] at hfl
  exact hfl.2.1.symm

end GoFV.Proof.Witness.GenG41
