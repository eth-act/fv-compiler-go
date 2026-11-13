import GoFV.Proof.Gen.G56
import GoFV.Proof.Witness.GenG54
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG56

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/float64Inf,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "float64Inf" 1 0 0
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
type t2 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t1 FUNC 8 8 8 hasptr,direct "func() float64" "func() float64" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "runtime.float64Inf" "runtime.float64Inf" 1 - 0 - - - - 0
posbase p131 "runtime/histogram.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p131:155:19:0:0
aux a1 call "AuxCall{runtime.float64Inf}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 16 -1
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
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t15
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t2
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t11
aux a4 name "inf" "inf" PAUTO t11 0 1 addrtaken,used p131:156:2:0:0
aux a5 type "uint64" t11
type t34 RESULTS ? ? ? - "float64,mem" "" 2 t2,t28
f b1 t1 a1 14 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t2,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64F t2 0 - p0:0:0:0:0 0 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:0:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v10 Copy t27 0 - p131:157:36:2:0 1 v9
v v11 Copy t23 0 - p131:157:35:2:0 1 v10
v v12 NilCheck t23 0 - p131:157:9:0:0 1 v11,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 0=v5,9218868437227405312=v6
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64F t2 0 - p0:0:0:0:0 0 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v10 Copy t27 0 - p131:157:36:2:0 1 v9
v v11 Copy t23 0 - p131:157:35:2:0 1 v10
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v11,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 0=v5,9218868437227405312=v6
freev -
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64F t2 0 - p0:0:0:0:0 0 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 3 v2,v8
v v10 Copy t27 0 - p131:157:36:2:0 0 v9
v v11 Copy t23 0 - p131:157:35:2:0 0 v9
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v9,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 0=v5,9218868437227405312=v6
freev -
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v9,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v9,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v9,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 4 v7,v6,v1
v v9 LocalAddr t33 0 a4 p131:157:36:0:0 1 v2,v8
v v12 NilCheck t23 0 - p131:157:9:1:0 1 v9,v8
v v13 Load t2 0 - p131:157:9:0:0 1 v12,v8
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache linestarts 131:156:157
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v12,v9,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 20 "expand calls"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 2 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
v v12 SB t15 0 - p0:0:0:0:0 0 -
v v9 LocalAddr t23 0 a3 p131:157:2:0:0 0 v2,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 2 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
v v12 SB t15 0 - p0:0:0:0:0 0 -
v v9 LocalAddr t23 0 a3 p131:157:2:0:0 0 v2,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 2 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
v v12 SB t15 0 - p0:0:0:0:0 0 -
v v9 LocalAddr t23 0 a3 p131:157:2:0:0 0 v2,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 2 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
v v12 SB t15 0 - p0:0:0:0:0 0 -
v v9 LocalAddr t23 0 a3 p131:157:2:0:0 0 v2,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 1 v2,v1
v v8 Store t28 0 a5 p131:156:6:1:0 1 v7,v6,v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 0 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 0 v2,v1
v v8 Copy t28 0 - p131:156:6:1:0 1 v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 9218868437227405312 - p0:0:0:0:0 0 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v7 LocalAddr t33 0 a4 p131:156:6:0:0 0 v2,v1
v v8 Copy t28 0 - p131:156:6:1:0 1 v1
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v8
names -
splits -
canon -
consts 9218868437227405312=v6
freev v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 Const64F t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157:156=0
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v13 ARM64FMOVDconst t2 9218868437227405312 - p131:157:9:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v13,v1
names -
splits -
canon -
consts -
freev v8,v7,v6,v2,v9,v12,v11,v10,v5,v4,v3
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.float64Inf}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 16 -1
callreg 0:80000000 - 0 -
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64FMOVDconst t2 9218868437227405312 - p131:157:2:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
regalloc 15 v8:F0,v14:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64FMOVDconst t2 9218868437227405312 - p131:157:2:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
regalloc 15 v8:F0,v14:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 14 1
b b1 Ret p131:157:36:1:0 0 0 - v14 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64FMOVDconst t2 9218868437227405312 - p131:157:2:1:0 1 -
v v14 MakeResult t34 0 - p131:157:2:0:0 1 v8,v1
names -
splits -
canon -
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1,a4:2
cache linestarts 131:156:157
fstate scheduled,laidout
regalloc 15 v8:F0,v14:[]
dcllen 2
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t14,t15,t25,t26,t13,t2,t3,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/runtime/float64Inf,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "float64Inf" 1
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
type t1 8 8 0 0 - "float64"
name n1 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a3
type t2 8 8 0 0 - "uint64"
name n2 "inf" PAUTO t2 1 "runtime.inf" 0 a4
in n1 0 outregs
in n2 0 used,addrtaken
opt n2 0 addrtaken
opt n1 0 outregs
stack 0 0 8
end
genin
posbase p131 "runtime/histogram.go" 1 1 -1 128 "runtime/histogram.go" "runtime/histogram.go" 1 1
sym y1 "runtime.float64Inf" 1
curfn p131:155:6:0:0 0 0
regargs -
text y1 0 0 0 0 155 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 0 p131:155:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p131:155:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p131:155:6:0:0
p 3 3 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p131:157:2:1:0
p 4 4 0 0 0 - FMOVD 0 FCONST/0/0/0/NONE/0/0/-/f7ff0000000000000 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p131:157:2:1:0
p 5 5 0 0 0 - RET 0 _ 0 - _ 0 0 p131:157:36:2:0
p 6 6 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 155 201080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgregout n1
dbgpc -
end
asm
sym y3 "$f64.7ff0000000000000" 0
sym y4 "" 0
sym y5 "" 0
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i0 0 2 p131:155:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p131:155:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p131:155:6:0:0
p 3 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p131:157:2:1:0
p 4 0 0 0 162 - FMOVD 0 MEM/0/0/0/EXTERN/110/0/y3/f7ff0000000000000 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p131:157:2:1:0
p 5 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p131:157:36:2:0
fn y1 0 0 0 0 155 2010c8
funcaux y2 y2 - - - - -
text 16 0 1b000090600340fdc0035fd600000000 1
reloc 0 8 R_ARM64_PCREL_LDST64 0 y3
pcln y5 y6 y7 y8 y4 y2,y2
usedfiles 128
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SRODATA 8 8 8800 000000000000f07f 0
data y4 SRODATA 3 1 28000 010400 0
data y5 SRODATA 3 1 28000 020400 0
data y6 SRODATA 4 1 28000 82020400 0
data y7 SRODATA 4 1 28000 bc020400 0
data y8 SRODATA 3 1 28000 000400 0
end
dwarf
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "go:info.runtime.float64Inf$abstract" 0
sym y13 "" 0
sym y14 "go:info.float64" 0
sym y15 "go:info.uint64" 0
sym y16 "type:float64" 0
sym y17 "type:uint64" 0
dwfn y9 y10 y11 y12 y13 "runtime.float64Inf" 128:155 1 0 1 4262
dwdcl -
dwclosure 0 -
dwparents -
dwparams n1
dwprecursor y1 y12 n1,n2
dwname n2 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p131:156:2:0:0
dwname n1 1 0 0 0 0 0 0 1 - - "float64" 0 0 1 p131:155:19:0:0
var 0 0 "~r0" 5 1 1 0 0 0 y14 "runtime/histogram.go" 155 19 0 0 0 0 -
var 1 0 "inf" 52 1 0 0 0 0 y15 "runtime/histogram.go" 156 2 0 1 1 0 -
scope 0 0 - 0,1
dieref y9 5 y12 1
dieoff y12 1:24
data y9 SDWARFFCN 30 0 0 0600000000000010019c2e7e723000019b01000000000024000000000000 6
reloc 0 0 R_USETYPE 0 y16
reloc 0 0 R_USETYPE 0 y17
reloc 1 4 R_DWARFSECREF 0 y12
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 18 4 R_DWARFSECREF 0 y14
reloc 24 4 R_DWARFSECREF 0 y12
data y10 SDWARFLOC 0 0 0 - 0
data y11 SDWARFRANGE 0 0 0 - 0
data y13 SDWARFLINES 25 0 0 000902000000000000000004810103970114065f0208000101 1
reloc 3 8 R_ADDR 0 y1
data y12 SDWARFABSFCN 36 0 1 0572756e74696d652e666c6f61743634496e6600019b010121696e66009c010000000000 1
reloc 31 4 R_DWARFSECREF 0 y15
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56): genssa's `FMOVD $(+Inf), F0` becomes the load `FMOVD $f64.7ff0000000000000(SB), F0`
(+Inf is no `FMOV` immediate), the symbol added to G2's symbols. -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `runtime.float64Inf`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G56's check runs on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

/-- P0'. -/
def ps : Array GoFV.Asm.Prog :=
  match stIn with
  | .ok x => x.2.1
  | .error _ => #[]

def bs : ID → Option Nat :=
  match stIn with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

/-- G2's inputs with the constant symbol. -/
def g : G2In :=
  match stIn with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG56` gives. -/
def tab : PcTab := (match checkG56 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG56` gives. -/
def kt : KTab := (match checkG56 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The float constant symbol of +Inf. -/
def cName : String := "$f64.7ff0000000000000"

/-- Its allocation: the eight little-endian bytes of +Inf's bits, read-only. -/
def cAl : Alloc := roAlloc (leBytesU8 0x7ff0000000000000 8)

/-- `ι`: the nil block, the globals at `symA`. -/
def ι56 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG56`. -/
def E : MatchEnv :=
  { lc, ι := ι56, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The Phase 1 memory before `v8`: the constant symbol, read-only. -/
def mem1 : Mem := { blocks := #[(.global cName, cAl)] }

/-- The machine memory before `v8`: +Inf's bits, little-endian, at `symA`, 0 elsewhere. -/
def M1 : Memory := fun y =>
  if y = GenG2.symA + 6 then 0xf0 else if y = GenG2.symA + 7 then 0x7f else 0

/-- The `runLoc` state before `v8`: every register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v8`: the activation's `g` and `FP`, every V register 0, the PC of `v8`,
the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 1, mem := M1 }

/-- `F0` (Go register 31) holds +Inf's bits. -/
def f0Is (s : LocState) : Bool :=
  match (s.regs[31]? : Option Val) with
  | some (Val.int .w64 x) => x == 0x7ff0000000000000
  | _ => false

theorem f0Is_spec {s : LocState} (h : f0Is s = true) :
    s.regs[31]? = some (.int .w64 0x7ff0000000000000) := by
  unfold f0Is at h
  split at h
  · rename_i x hx
    simp only [beq_iff_eq] at h
    subst h
    exact hx
  · cases h

/-- What compiled evaluation checks on `runtime.float64Inf`: it holds an arm64 op; on P0',
`checkG56` accepts it with `tab` and `kt` and `checkG55` does not (its constant is a load); it
accesses no frame variable and has no home slot; `b1` holds `v8` (`FMOVDconst [+Inf]`) at index 1,
where G35's table is empty; the float constant symbols among G2's symbols are `$f64.7ff…` alone,
with `cAl`; `stepLoc` runs `v8` from `s0` to a state with +Inf's bits in `F0` (Go register 31). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG56 lc0 ps bs g).toOption == some (tab, kt) && (checkG55 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 8).isSome && blk.values[1]? == some 8 &&
    (val 8).op == .ARM64FMOVDconst &&
    constRo (symNames g) == [(cName, cAl)] &&
    uL35 lc (uIn35 lc 1) blk 1 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) f0Is

theorem g56_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG56 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG55 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 8 = some (val 8) ∧ blk.values[1]? = some 8 ∧
      (val 8).op = .ARM64FMOVDconst ∧
      constRo (symNames g) = [(cName, cAl)] ∧
      uL35 lc (uIn35 lc 1) blk 1 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 8)) f0Is = true := by
  have hf := g56_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h54, hav, hsl, hm1, hbs, hvs, hi1, hop, hro, hu1, hrun⟩ := hf
  refine ⟨hl, ?_, h54, hav, hsl, hm1, ?_, ?_, hi1, hop, hro, hu1, hrun⟩
  · revert hres; cases checkG56 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

/-- `ι56` puts the only block with a Phase 1 address (`nil`) at it. -/
theorem addrAgree56 : AddrAgree ι56 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι56] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | _ => simp [ι56] at ha <;> simp [Blk.base?] at hb

theorem g56Env (hc : checkG56 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
                checkG56L_spec hl (checkG56_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree56
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -⟩ :=
                checkG56L_spec hl (checkG56_spec hc).2
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

theorem cAl_size : cAl.data.size = 8 := by
  simp [cAl, roAlloc, leBytesU8]

/-- `M1` holds +Inf's bits little-endian at `symA`. -/
theorem m1_bytes : ∀ i, i < 8 →
    M1 (GenG2.symA + BitVec.ofNat 64 i) = BitVec.ofNat 8 (0x7ff0000000000000 / 256 ^ i) := by
  decide

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .global cName ∧ al = cAl := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `ι56`: the constant's bytes at `symA`. -/
theorem memInj1 : MemInj ι56 mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    refine ⟨GenG2.symA, rfl, fun _ => by decide, ?_⟩
    rw [cAl_size]
    decide
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = GenG2.symA := by simp [ι56] at ha; exact ha.symm
    subst ha'
    have hi8 : i < 8 := cAl_size ▸ hi
    have hb : cAl.data[i]? = some (.b (BitVec.ofNat 8 (0x7ff0000000000000 / 256 ^ i))) :=
      roAlloc_byte hi8
    rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at hb
    change ByteRel ι56 cAl.data[i] _
    rw [hb]
    exact (m1_bytes i hi8).symm

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom ι56 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    rw [hsp] at h2
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = GenG2.symA := by simp [ι56] at ha; exact ha.symm
    subst ha'
    have hA : GenG2.symA.toNat = 0x10000000000 := rfl
    simp only [hA, cAl_size]
    omega
  · cases hk

/-- The constant symbol is in `mem1`, read-only: `RoPre56` at `s0`. -/
theorem ro0 (hro : constRo (symNames g) = [(cName, cAl)]) : RoPre56 g s0 := by
  intro mm hmm
  change Val.mem mem1 = Val.mem mm at hmm
  cases hmm
  rw [hro]
  intro n a h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, by simp [mem1, Mem.find?]⟩

/-! ## `v8`: `FMOVDconst [+Inf]` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 1 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E]; decide,
    by simp only [MState.word, readMem, m0, M1, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g56Inv0 : G3Inv E lc (kAt lc kt 1 blk 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G54 on `v8`, `FMOVDconst`: none of them applies. -/
theorem pre54 (hop : (val 8).op = .ARM64FMOVDconst) : G54Pre lc s0 (val 8) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDconst → (val 8).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩, fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩
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

/-- **G56 on `runtime.float64Inf`** (`func float64Inf() float64 { var inf uint64 = 0x7FF0000000000000;
return *(*float64)(unsafe.Pointer(&inf)) }`, `v8: FMOVDconst [+Inf]` in `F0`): +Inf is no `FMOV`
immediate, so on P0' its Prog is the load `FMOVD $f64.7ff0000000000000(SB), F0`, which `checkG55`
rejects and `checkG56` accepts. From `s0`, whose memory has the constant symbol (`RoPre56`, as
`lreach_roMem` gives), with every V register 0 in `m0` and the constant's bytes at the symbol's
linked address, `stepLoc` runs `v8` and `g56_value` relates it to a machine state after the load
with +Inf's bits in `V0`'s low word, under an activation extending `E` that is again a `G49Env`. -/
theorem genG56_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧ (m0.v 0).setWidth 64 = 0 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 8) = .ok s1 ∧
        s1.regs[31]? = some (.int .w64 0x7ff0000000000000) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 2 m1 ∧ (m1.v 0).setWidth 64 = 0x7ff0000000000000 := by
  obtain ⟨hl, hc, h54, hav, hsl, hm1, hb, hv8, hi1, hop, hro, hu1, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr31 := f0Is_spec hr
  have hE := g56Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDconst → (val 8).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g56_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 8 = some (val 8) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv8
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g56_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi1 hv0 (by rw [hop]; rfl) locMatch0 g56Inv0
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 1); rw [hu1]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hV : (m1.v 0).setWidth 64 = 0x7ff0000000000000 :=
    (hm1'.regs 31 _ hr31).2 0 rfl
  exact ⟨h54, rfl, s1, E1, m1, hs1, hr31, hx1, hE1, hp1, hm1', hV⟩

end GoFV.Proof.Witness.GenG56
