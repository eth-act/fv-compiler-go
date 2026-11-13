import GoFV.Proof.Gen.G44
import GoFV.Proof.Witness.GenG43

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG44

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/math/Float64frombits,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "math"
func "Float64frombits" 1 0 0
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
config localpkg "math"
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t3 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t1 FUNC 8 8 8 hasptr,direct "func(uint64) float64" "func(uint64) float64" 0 1 1
field 0 "b" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "math.Float64frombits" "math.Float64frombits" 1 - 0 - - - - 0
posbase p53 "math/unsafe.go" 1 1 -1
aux a3 name "b" "b" PPARAM t2 0 1 addrtaken,used p53:41:22:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p53:41:32:0:0
aux a1 call "AuxCall{math.Float64frombits}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 16 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 INT 8 8 0 comparable,named "int" "int"
type t13 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t15
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t3
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t2
aux a5 type "uint64" t2
type t34 RESULTS ? ? ? - "float64,mem" "" 2 t3,t28
f b1 t1 a1 13 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t2,Int=t12,Float32=t13,Float64=t3,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:0:0 3 v4,v6,v1
v v8 Const64F t3 0 - p0:0:0:0:0 0 -
v v9 Copy t27 0 - p53:41:76:2:0 1 v4
v v10 Copy t23 0 - p53:41:75:2:0 1 v9
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v10,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts 0=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v8 Const64F t3 0 - p0:0:0:0:0 0 -
v v9 Copy t27 0 - p53:41:76:2:0 1 v4
v v10 Copy t23 0 - p53:41:75:2:0 1 v9
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v10,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts 0=v8
freev -
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 4 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v8 Const64F t3 0 - p0:0:0:0:0 0 -
v v9 Copy t27 0 - p53:41:76:2:0 0 v4
v v10 Copy t23 0 - p53:41:75:2:0 0 v4
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v4,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts 0=v8
freev -
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v4,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v4,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v4,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v11 NilCheck t23 0 - p53:41:49:0:0 1 v4,v7
v v12 Load t3 0 - p53:41:49:0:0 1 v11,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache linestarts 53:41:41
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p53:41:6:2:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v11,v10,v9,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 20 "expand calls"
aux a6 nameoff "b+0" a3 0
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
v v11 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t33 0 - p0:0:0:0:0 0 v2
v v9 LocalAddr t23 0 a4 p53:41:42:0:0 0 v2,v7
names -
splits -
canon -
consts 0=v10
freev v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
v v11 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t33 0 - p0:0:0:0:0 0 v2
v v9 LocalAddr t23 0 a4 p53:41:42:0:0 0 v2,v7
names -
splits -
canon -
consts 0=v10
freev v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
v v11 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t33 0 - p0:0:0:0:0 0 v2
v v9 LocalAddr t23 0 a4 p53:41:42:0:0 0 v2,v7
names -
splits -
canon -
consts 0=v10
freev v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 3 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
v v11 SB t15 0 - p0:0:0:0:0 0 -
v v10 OffPtr t33 0 - p0:0:0:0:0 0 v2
v v9 LocalAddr t23 0 a4 p53:41:42:0:0 0 v2,v7
names -
splits -
canon -
consts 0=v10
freev v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 2 v2,v1
v v7 Store t28 0 a5 p53:41:6:1:0 2 v4,v6,v1
v v12 Load t3 0 - p53:41:49:0:0 1 v4,v7
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2
cache linestarts 53:41:41
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 2 -
v v7 ARM64MOVDstore t28 0 a3 p53:41:6:1:0 1 v2,v6,v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v7 Copy t28 0 - p53:41:6:1:0 1 v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v7 Copy t28 0 - p53:41:6:1:0 1 v1
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v7
names -
splits -
canon -
consts -
freev v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v7,v2,v4,v9,v10,v11,v8,v5,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{math.Float64frombits}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 16 -1
callreg 0:80000000 - 0 -
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
regalloc 14 v6:R0,v12:F0,v13:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
regalloc 14 v6:R0,v12:F0,v13:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 13 1
b b1 Ret p53:41:76:1:0 0 0 - v13 - -
v v6 ArgIntReg t2 0 a6 p53:41:76:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v12 ARM64FMOVDgpfp t3 0 - p53:41:49:0:0 1 v6
v v13 MakeResult t34 0 - p53:41:42:0:0 1 v12,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v11
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a3:2,a6:3
cache linestarts 53:41:41
fstate scheduled,laidout
regalloc 14 v6:R0,v12:F0,v13:[]
dcllen 2
end
frontend
end
ptrcache t2,t3,t6,t7,t8,t9,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t5,t9,t6,t10,t7,t11,t8,t2,t12,t14,t15,t25,t26,t13,t3,t4,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/math/Float64frombits,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "math"
func "Float64frombits" 1
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
type t1 8 8 0 0 - "uint64"
name n1 "b" PPARAM t1 1 "math.b" 0 a3
type t2 8 8 0 0 - "float64"
name n2 "~r0" PPARAMOUT t2 1 "math.~r0" 0 a4
in n1 0 used,addrtaken
in n2 0 outregs
out n1 0 used,addrtaken
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p53 "math/unsafe.go" 1 1 -1 52 "math/unsafe.go" "math/unsafe.go" 1 1
sym y1 "math.Float64frombits" 1
curfn p53:41:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 41 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math.Float64frombits.arginfo1" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p53:41:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p53:41:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p53:41:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p53:41:6:0:0
p 4 4 0 0 0 - FMOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p53:41:49:1:0
p 5 5 0 0 0 - RET 0 _ 0 - _ 0 0 p53:41:76:2:0
p 6 6 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 41 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:-1:-30000:50
dbgregout n2
dbgpc -
end
asm
sym y4 "" 0
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p53:41:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p53:41:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p53:41:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p53:41:6:0:0
p 4 0 0 0 136 - FMOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p53:41:49:1:0
p 5 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p53:41:76:2:0
fn y1 8 0 0 0 41 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 - -
text 16 0 0000679ec0035fd60000000000000000 0
pcln y4 y5 y6 y7 - y2,y2,_,_,_,y3
usedfiles 52
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SRODATA 3 1 28000 020400 0
data y5 SRODATA 3 1 28000 6a0400 0
data y6 SRODATA 3 1 28000 540400 0
data y7 SRODATA 3 1 28000 000400 0
end
dwarf
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "go:info.math.Float64frombits$abstract" 0
sym y12 "" 0
sym y13 "go:info.uint64" 0
sym y14 "go:info.float64" 0
sym y15 "type:float64" 0
dwfn y8 y9 y10 y11 y12 "math.Float64frombits" 52:41 1 0 1 177
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y11 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint64" 0 0 1 p53:41:22:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "float64" 0 0 1 p53:41:32:0:0
var 0 0 "b" 5 1 0 0 0 8 y13 "math/unsafe.go" 41 22 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y14 "math/unsafe.go" 41 32 0 1 0 0 -
scope 0 0 - 0,1
dieref y8 3 y11 0
dieoff y11 0:25
data y8 SDWARFFCN 32 0 0 0600000000000010019c2900000000000000002e7e7230000129000000000000 6
reloc 0 0 R_USETYPE 0 y15
reloc 1 4 R_DWARFSECREF 0 y11
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y11
reloc 15 4 R_DWARFSECREF 0 y9
reloc 26 4 R_DWARFSECREF 0 y14
data y9 SDWARFLOC 9 0 0 010000040010015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y10 SDWARFRANGE 0 0 0 - 0
data y12 SDWARFLINES 23 0 0 000902000000000000000004350323140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y11 SDWARFABSFCN 34 0 1 056d6174682e466c6f6174363466726f6d6269747300012901226200000000000000 1
reloc 29 4 R_DWARFSECREF 0 y13
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `Float64frombits`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G44's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG44` gives (`b1`: `v6`, `v1`, `v12` at Prog 4, `v13`, then the `RET`). -/
def tab : PcTab := [(1, [4, 4, 4, 5, 5])]

/-- The class table `checkG44` gives. -/
def kt : KTab := (match checkG44 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG44`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The bits of `1.0`. -/
def one : BitVec 64 := 0x3ff0000000000000

/-- The `runLoc` state before `v12`: `b = 0x3ff0000000000000` (`v6`) in `R0`, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w64 one else .poison,
    flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v12`: `X0` holds `b`, the V registers 0, the activation's `g` and `FP`,
the PC of `v12`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then one else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 64-bit `one`. -/
def isOne : Option Val → Bool
  | some (.int .w64 x) => x == one
  | _ => false

theorem isOne_spec {o : Option Val} (h : isOne o = true) : o = some (.int .w64 one) := by
  unfold isOne at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `Float64frombits`: it holds an arm64 op; `checkG44`
accepts it with `tab` and `kt` and `checkG43` does not; it accesses no frame variable and has no
home slot; `b1` holds `v12` (`FMOVDgpfp v6`, of type `float64`, in `F0`) at index 2, where `R0` has
class 64 and G35's table is empty; `stepLoc` runs `v12` from `s0` to `F0 = one`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG44 lc0 ps bs g).toOption == some (tab, kt) && (checkG43 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 12).isSome && blk.values[2]? == some 12 && (val 12).op == .ARM64FMOVDgpfp &&
    (kAt lc kt 1 blk 2).get 0 == some 64 && uL35 lc (uIn35 lc 1) blk 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) (fun s1 => isOne s1.regs[31]?)

theorem g44_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG44 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG43 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 12 = some (val 12) ∧ blk.values[2]? = some 12 ∧
      (val 12).op = .ARM64FMOVDgpfp ∧
      (kAt lc kt 1 blk 2).get 0 = some 64 ∧ uL35 lc (uIn35 lc 1) blk 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 12)) (fun s1 => isOne s1.regs[31]?) = true := by
  have hf := g44_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h43, hav, hsl, hm1, hbs, hvs, hi2, hop, hk0, hu2, hrun⟩ := hf
  refine ⟨hl, ?_, h43, hav, hsl, hm1, ?_, ?_, hi2, hop, hk0, hu2, hrun⟩
  · revert hres; cases checkG44 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g44Env (hc : checkG44 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              checkG44L_spec hl (checkG44_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG44L_spec hl (checkG44_spec hc).2
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

/-! ## `v12`: `FMOVD R0, F0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 one) ∨ x = .poison := by
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
      exact .inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g44Inv0 (h0 : (kAt lc kt 1 blk 2).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v12`, `FMOVDgpfp`: none of G44's applies. -/
theorem pre12 (hop : (val 12).op = .ARM64FMOVDgpfp) : G44Pre lc s0 (val 12) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDgpfp → (val 12).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
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

/-- **G44 on `math.Float64frombits`**: `b1` moves the `uint64` argument `b` (`v6`, in `R0`) to the
`float64` result in `F0` (`v12`, `FMOVDgpfp`, `FMOVD R0, F0`), which `checkG43` rejects (its
result is in a V register) and `checkG44` accepts. From `s0`, `b = 0x3ff0000000000000` (the bits
of `1.0`), `stepLoc` runs `v12` to `F0 = 0x3ff0000000000000`, and `g44_value` relates it to a
machine state after `v12`'s code whose `V0` holds those bits in its low 64, under an activation
extending `E` that is again a `G28Env`. -/
theorem genG44_witness :
    (checkG43 lc0 ps bs g).toOption = none ∧ m0.x 0 = one ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 12) = .ok s1 ∧
        s1.regs[31]? = some (.int .w64 one) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧ (m1.v 0).setWidth 64 = one := by
  obtain ⟨hl, hc, h43, hav, hsl, hm1, hb, hv12, hi2, hop, hk0, hu2, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isOne_spec hr
  have hE := g44Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDgpfp → (val 12).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g44_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 12 = some (val 12) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv12
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g44_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g44Inv0 hk0)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 2); rw [hu2]; intro e he; cases he)
    (pre12 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h43, rfl, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', ?_⟩
  exact (hm1'.regs 31 _ hr1).2 0 (by simp [objV?])

end GoFV.Proof.Witness.GenG44
