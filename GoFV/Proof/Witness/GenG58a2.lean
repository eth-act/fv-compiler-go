import GoFV.Gen.Check57
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG58a2

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/copy/main/u16,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "u16" 1 0 0
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t3 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t1 FUNC 8 8 8 hasptr,direct "func(int) uint16" "func(int) uint16" 0 1 1
field 0 "ii" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "main.u16" "main.u16" 1 - 0 - - - - 0
posbase p2 "./copy.go" 1 1 -1
aux a3 name "ii" "ii" PPARAM t2 0 1 used p2:41:10:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p2:41:18:0:0
aux a1 call "AuxCall{main.u16}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t2
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint16" "*uint16" t3
type t34 RESULTS ? ? ? - "uint16,mem" "" 2 t3,t28
slot s1 a3 t2 0 - 0
aux a5 name "i" "i" PAUTO t3 0 1 used p2:42:6:0:0
slot s2 a5 t3 0 - 0
f b1 t1 a1 16 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t3,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v7 Const16 t3 0 - p0:0:0:0:0 0 -
v v8 Trunc64to16 t3 0 - p2:42:17:0:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:0:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:0:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:0:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v7,8=v13,26=v10,97=v9
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v7 Const16 t3 0 - p0:0:0:0:0 0 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v7,8=v13,26=v10,97=v9
freev -
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v7 Const16 t3 0 - p0:0:0:0:0 0 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v7,8=v13,26=v10,97=v9
freev -
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,26=v10,97=v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,26=v10,97=v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,26=v10,97=v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 1 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v10 Const16 t3 26 - p0:0:0:0:0 1 -
v v11 Mod16u t3 0 - p2:43:13:1:0 1 v8,v10
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 0 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,26=v10,97=v9
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache linestarts 2:42:45
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 16 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 2 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Div16u t3 0 - p2:43:13:1:0 1 v8,v4
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v10,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 18 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 0 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 18 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 18 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 18 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 Arg t2 0 a3 p2:41:6:2:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "ii+0" a3 0
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
v v19 SB t15 0 - p0:0:0:0:0 0 -
v v20 SP t15 0 - p0:0:0:0:0 2 -
v v21 OffPtr t20 0 - p0:0:0:0:0 0 v20
v v22 LocalAddr t33 0 a4 p2:45:2:1:0 0 v20,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v21,8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
v v19 SB t15 0 - p0:0:0:0:0 0 -
v v20 SP t15 0 - p0:0:0:0:0 2 -
v v21 OffPtr t20 0 - p0:0:0:0:0 0 v20
v v22 LocalAddr t33 0 a4 p2:45:2:1:0 0 v20,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v21,8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
v v19 SB t15 0 - p0:0:0:0:0 0 -
v v20 SP t15 0 - p0:0:0:0:0 2 -
v v21 OffPtr t20 0 - p0:0:0:0:0 0 v20
v v22 LocalAddr t33 0 a4 p2:45:2:1:0 0 v20,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v21,8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
v v19 SB t15 0 - p0:0:0:0:0 0 -
v v20 SP t15 0 - p0:0:0:0:0 2 -
v v21 OffPtr t20 0 - p0:0:0:0:0 0 v20
v v22 LocalAddr t33 0 a4 p2:45:2:1:0 0 v20,v1
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 0=v21,8=v13,97=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 Const16 t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 1 -
v v9 Const16 t3 97 - p0:0:0:0:0 1 -
v v13 Const64 t14 8 - p0:0:0:0:0 1 -
v v8 Trunc64to16 t3 0 - p2:42:17:1:0 2 v6
v v5 Trunc64to16 t3 0 - p2:43:13:1:0 1 v10
v v7 Mul16 t3 0 - p2:43:13:1:0 1 v5,v4
v v11 Sub16 t3 0 - p2:43:13:1:0 1 v8,v7
v v12 Add16 t3 0 - p2:43:10:0:0 2 v9,v11
v v14 Lsh16x64 t3 1 - p2:44:9:1:0 1 v12,v13
v v15 Or16 t3 0 - p2:44:4:0:0 1 v12,v14
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 Rsh64Ux64 t11 1 - p2:43:13:1:0 1 v3,v18
v v3 Mul64 t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ZeroExt16to64 t11 0 - p2:43:13:1:0 1 v8
v v17 Const64 t11 80660 - p2:43:13:1:0 1 -
v v18 Const64 t11 21 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts 8=v13,97=v9
freev v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45:42=1:43=1
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45:42=1:43=1
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v8,v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:42:45
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v4 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v17 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v17
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v4
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v18,v14,v7,v5,v8,v13,v9,v22,v21,v20,v19
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.u16}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v18 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v18
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v14 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v14
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v5,v7,v8,v9,v13,v19,v20,v21,v22
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
regalloc 19 v2:R1,v3:R1,v6:R0,v10:R1,v11:R1,v12:R1,v14:R2,v15:R0,v16:[],v18:R2
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v18 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v18
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v14 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v14
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v5,v7,v8,v9,v13,v19,v20,v21,v22
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
regalloc 19 v2:R1,v3:R1,v6:R0,v10:R1,v11:R1,v12:R1,v14:R2,v15:R0,v16:[],v18:R2
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 22 1
b b1 Ret p2:45:2:1:0 0 0 - v16 - -
v v6 ArgIntReg t2 0 a6 p2:45:2:1:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 ARM64MOVHUreg t11 0 - p2:43:13:1:0 1 v6
v v18 ARM64MOVDconst t11 80660 - p2:43:13:1:0 1 -
v v3 ARM64MUL t11 0 - p2:43:13:1:0 1 v2,v18
v v10 ARM64SRLconst t11 21 - p2:43:13:1:0 1 v3
v v14 ARM64MOVDconst t3 26 - p2:43:13:1:0 1 -
v v11 ARM64MSUBW t3 0 - p2:43:13:1:0 1 v6,v10,v14
v v12 ARM64ADDconst t3 97 - p2:43:10:0:0 2 v11
v v15 ARM64ORshiftLL t3 8 - p2:44:4:1:0 1 v12,v12
v v16 MakeResult t34 0 - p2:45:2:1:0 1 v15,v1
names s1,s2
named s1 v6
named s2 v12,v15
splits -
canon a3/t2/0/-/0=s1,a5/t3/0/-/0=s2
consts -
freev v5,v7,v8,v9,v13,v19,v20,v21,v22
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a6:3
cache linestarts 2:42:45
fstate scheduled,laidout
regalloc 19 v2:R1,v3:R1,v6:R0,v10:R1,v11:R1,v12:R1,v14:R2,v15:R0,v16:[],v18:R2
dcllen 3
end
frontend
end
ptrcache t2,t6,t7,t8,t9,t10,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t5,t9,t6,t3,t7,t10,t8,t11,t2,t14,t15,t25,t26,t12,t13,t4,t17,t33,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `test/copy/main/u16,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "u16" 1
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
type t1 8 8 0 0 - "int"
name n1 "ii" PPARAM t1 1 "main.ii" 0 a3
type t2 2 2 0 0 - "uint16"
name n2 "~r0" PPARAMOUT t2 1 "main.~r0" 0 a4
name n3 "i" PAUTO t2 1 "main.i" 0 a5
in n1 0 used
in n2 0 outregs
in n3 0 used
out n1 0 used
opt n3 0 -
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./copy.go" 1 1 -1 1 "./copy.go" "./copy.go" 1 1
sym y1 "main.u16" 1
curfn p2:41:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 41 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.u16.arginfo1" 0
sym y4 "main.u16.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:41:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:41:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:41:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:41:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:41:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:41:6:2:0
p 6 6 0 0 0 - MOVHU 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:43:13:1:0
p 7 7 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/80660/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:43:13:2:0
p 8 8 0 0 0 - MUL 0 REG/8194/0/0/NONE/0/0/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:43:13:2:0
p 9 9 0 0 0 - LSR 0 CONST/0/0/0/NONE/0/21/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:43:13:2:0
p 10 10 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/26/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:43:13:2:0
p 11 11 0 0 0 - MSUBW 0 REG/8193/0/0/NONE/0/0/-/- 8192 0:REG/8194/0/0/NONE/0/0/-/- REG/8193/0/0/NONE/0/0/-/- 0 0 p2:43:13:2:0
p 12 12 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/97/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:43:10:2:0
p 13 13 0 0 0 - ORR 0 SHIFT/0/0/0/NONE/0/73728/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:44:4:1:0
p 14 14 0 0 0 - RET 0 _ 0 - _ 0 0 p2:45:2:1:0
p 15 15 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 41 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n3 t2 0
dbgvar 0 n1 0
dbgvar 1 n3 1
dbgloc 0 1:-10000:1:15:50
dbgloc 1 1:12:-1:-30000:51
dbgregout n2
dbgpc 1:15:14,1:12:13
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:41:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:41:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:41:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:41:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:41:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:41:6:2:0
p 6 0 0 0 343 - MOVHU 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:43:13:1:0
p 7 4 0 0 320 - MOVD 0 CONST/0/0/0/NONE/25/80660/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:43:13:2:0
p 8 12 0 0 404 - MUL 0 REG/8194/0/0/NONE/2/0/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:43:13:2:0
p 9 16 0 0 274 - LSR 0 CONST/0/0/0/NONE/18/21/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:43:13:2:0
p 10 20 0 0 318 - MOVD 0 CONST/0/0/0/NONE/18/26/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:43:13:2:0
p 11 24 0 0 275 - MSUBW 0 REG/8193/0/0/NONE/2/0/-/- 8192 0:REG/8194/0/0/NONE/2/0/-/- REG/8193/0/0/NONE/2/0/-/- 0 0 p2:43:13:2:0
p 12 28 0 0 31 - ADD 0 CONST/0/0/0/NONE/18/97/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:43:10:2:0
p 13 32 0 0 51 - ORR 0 SHIFT/0/0/0/NONE/8/73728/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:44:4:1:0
p 14 36 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:45:2:1:0
fn y1 8 0 0 0 41 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 48 0 013c40d3826287d22200a0f2217c029b21fc55d3420380d24180011b21840191202001aac0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040c00 0
data y9 SRODATA 3 1 28000 020c00 0
data y10 SRODATA 3 1 28000 040c00 0
data y11 SRODATA 7 1 28000 58080201020300 0
data y12 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.main.u16$abstract" 0
sym y17 "" 0
sym y18 "go:info.int" 0
sym y19 "go:info.uint16" 0
sym y20 "type:uint16" 0
dwfn y13 y14 y15 y16 y17 "main.u16" 1:41 1 0 1 22
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "int" 0 0 1 p2:41:10:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "uint16" 0 0 1 p2:42:6:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint16" 0 0 1 p2:41:18:0:0
var 0 0 "ii" 5 1 0 0 0 8 y18 "./copy.go" 41 10 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "./copy.go" 41 18 0 1 0 0 -
var 2 0 "i" 52 1 0 0 0 -8 y19 "./copy.go" 42 6 0 2 1 0 v1
scope 0 0 - 0,1,2
dieref y13 3 y16 0
dieref y13 6 y16 2
dieoff y16 0:13,2:22
data y13 SDWARFFCN 40 0 0 06000000000030019c2900000000000000002e7e7230000129000000000023000000000000000000 8
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y16
reloc 14 4 R_DWARFSECREF 0 y14
reloc 25 4 R_DWARFSECREF 0 y19
reloc 31 4 R_DWARFSECREF 0 y16
reloc 35 4 R_DWARFSECREF 8 y14
data y14 SDWARFLOC 16 0 0 01000400240150000100042030015100 2
reloc 1 1 R_DWTXTADDR_U1 0 y1
reloc 9 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 27 0 0 00090200000000000000000402032514063706083838020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 31 0 1 056d61696e2e753136000129012269690000000000002169002a0000000000 2
reloc 18 4 R_DWARFSECREF 0 y18
reloc 26 4 R_DWARFSECREF 0 y19
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.u16`. -/
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

/-- The index of `v11`'s `MSUBW R1, R0, R2, R1` among the Progs (`kdOK` checks it). -/
def jF : Nat := 11

/-- A PC table for `b1` with `v11` (index 7) at its Prog and the value after it at the next. -/
def tab : PcTab := [(1, List.replicate 8 11 ++ [12])]

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

/-- The class map before `v11`: the classes of its arguments' registers. -/
def K0 : KMap := (((KMap.bot.set! 0 (some 64)).set! 1 (some 64)).set! 2 (some 16))

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 16-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, no home slot, the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v11`: its arguments in their registers, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 1000 else if i.val = 1 then .int .w64 38 else if i.val = 2 then .int .w16 26 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v11`: the arguments' words, the activation's `g` and `FP`, the PC of
`v11`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 1000 else if k = 1 then 38 else if k = 2 then 26 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 7, mem := fun _ => 0 }

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

/-- `vkind58a` accepts `v11` with a pattern the Prog at `jF` matches. -/
def kdOK : Bool := (patOf (vkind58a lc g (val 11))).any fun pat => (ps[jF]?).any pat.ok

/-- The register value `.int .w16 12`. -/
def isRes : Option Val → Bool
  | some (.int .w16 x) => x == 12
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w16 12) := by
  unfold isRes at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `main.u16`: it holds an arm64 op; G57's value check
`vkind57` rejects `v11` (MSUBW), which `vkind58a` accepts with the Prog at `jF`; the Progs
have distinct IDs below `2^32`; every home is one G10 handles; `checkFrame` passes; `b1` holds
`v11` at index 7; no frame variable is accessed and there is no home slot; `v11` reads its
registers at the classes of `K0`; and `stepLoc` runs `v11` to `.int .w16 12` in its register. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (vkind57 lc g (val 11)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 11).isSome && blk.values[7]? == some 11 &&
    (val 11).op == .ARM64MSUBW && (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    (kReads lc (val 11)).all (fun rc => K0.get rc.1 == some rc.2) && K0.get 0 == some 64 && K0.get 1 == some 64 && K0.get 2 == some 16 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) (fun s1 => isRes s1.regs[1]?)

theorem g58a2_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (vkind57 lc g (val 11)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.value? 11 = some (val 11) ∧ blk.values[7]? = some 11 ∧
      (val 11).op = .ARM64MSUBW ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧
      (∀ rc ∈ kReads lc (val 11), K0.get rc.1 = some rc.2) ∧ (K0.get 0 = some 64 ∧ K0.get 1 = some 64 ∧ K0.get 2 = some 16) ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) (fun s1 => isRes s1.regs[1]?) = true := by
  have hf := g58a2_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hf
  obtain ⟨hl, h57, hkd, hlt, hnd, hhome, hcf, -, hvs, hi, hop, hav, hsl, hrd, hrest⟩ := hf
  refine ⟨hl, h57, hkd, hlt, hnd, homeOK10_all hhome, ?_, ?_, hi, hop, hav, hsl, hrd, ?_⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]
  · simpa only [and_assoc] using hrest

/-- `vkind58a`'s pattern for `v11` and the Prog at `jF` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind58a lc g (val 11) = some (.ok (.prog pat)) ∧ (ps[jF]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

theorem env58 (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG2.addrAgree
            glob := fun _ _ _ _ => rfl
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
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## `v11`: `MSUBW R1, R0, R2, R1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 1000) ∨ (r = 1 ∧ x = .int .w64 38) ∨ (r = 2 ∧ x = .int .w16 26) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases h0 : r = 0
    · subst h0; simp
    ·
      by_cases h1 : r = 1
      · subst h1; simp
      ·
        by_cases h2 : r = 2
        · subst h2; simp
        · simp [h0, h1, h2]
  · cases h

theorem locMatch0 : LocMatch E s0 1 7 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact .inl (by simp only [m0]; decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact .inl (by simp only [m0]; decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x _).setWidth _ = _; simp only [m0]; decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem inv0 (hk0 : K0.get 0 = some 64) (hk1 : K0.get 1 = some 64) (hk2 : K0.get 2 = some 16) :
    G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [hk0] at hc; cases hc; rfl
    · rw [hk1] at hc; cases hc; rfl
    · rw [hk2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G58, group A, on `main.u16`** (which computes `uint16(x) % 26` of its `int` argument `x` by
`MSUBW` of `x`, the quotient `v10` and the `uint16` constant 26 `v14`, a `uint16` result: `checkG57`
asks the arguments of a `MSUBW` at least 32 bits (`v11: MSUBW widths`) and `vkind58a` accepts it
(the low 16 bits of `a - x·y` read only the low 16 bits of its arguments). From `s0`, with `x =
1000`, `v10 = 38`, `v14 = 26` in `R0`, `R1`, `R2`, `stepLoc` runs `v11` to 12, and `vk58a_step`
relates it to a machine run of its Prog to a state with `X1`'s low halfword 12, under an activation
extending `E` that is again a `G49Env`.) -/
theorem genG58a2_witness :
    (vkind57 lc g (val 11)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 11) = .ok s1 ∧ s1.regs[1]? = some (.int .w16 12) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 8 m1 ∧
        (m1.x 1).setWidth 16 = 12 := by
  obtain ⟨hl, h57, hkd, hlt, hnd, hhome, hcf, hv, -, -, hav, hsl, hrd, ⟨hk0, hk1, hk2⟩, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isRes_spec hr
  have hE := env58 hlt hav hsl
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind58a_spec hvk
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jF (jF + 1) :=
    ⟨jF, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), GenG2.addrAgree⟩
  have hj : E.pcOf 1 7 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 1 (7 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk58a_step (H := GenG2.H0) (L := []) (bid := 1)
    (i := 7) (j := jF) (j' := jF + 1) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0
    (inv0 hk0 hk1 hk2) (fun e he => by cases he) hs1
  refine ⟨h57, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1, ?_⟩
  exact (hm1.regs 1 _ hr1).1 _ (by simp [objX?])

end GoFV.Proof.Witness.GenG58a2
