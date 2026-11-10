import GoFV.Gen.Check57
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG58a

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/math/bits/ReverseBytes16,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "math/bits"
func "ReverseBytes16" 1 0 0
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
config localpkg "math/bits"
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
type t2 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t1 FUNC 8 8 8 hasptr,direct "func(uint16) uint16" "func(uint16) uint16" 0 1 1
field 0 "x" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "math/bits.ReverseBytes16" "math/bits.ReverseBytes16" 1 - 0 - - - - 0
posbase p2 "math/bits/bits.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p2:276:21:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:276:31:0:0
aux a1 call "AuxCall{math/bits.ReverseBytes16}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t10 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint16" "*uint16" t2
type t34 RESULTS ? ? ? - "uint16,mem" "" 2 t2,t28
slot s1 a3 t2 0 - 0
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t2,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v7 Const16 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:0:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v7 Const16 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t33 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v7 Const16 t2 0 - p0:0:0:0:0 0 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev -
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 2 -
v v8 Const64 t14 8 - p0:0:0:0:0 2 -
v v9 Rsh16Ux64 t2 0 - p2:277:10:1:0 1 v6,v8
v v10 Lsh16x64 t2 0 - p2:277:17:0:0 1 v6,v8
v v11 Or16 t2 0 - p2:277:14:0:0 1 v9,v10
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:277:277
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:276:6:2:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v10,v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "x+0" a3 0
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v9 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v9
v v5 LocalAddr t33 0 a4 p2:277:2:0:0 0 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v9 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v9
v v5 LocalAddr t33 0 a4 p2:277:2:0:0 0 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v9 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v9
v v5 LocalAddr t33 0 a4 p2:277:2:0:0 0 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
v v10 SB t15 0 - p0:0:0:0:0 0 -
v v9 SP t15 0 - p0:0:0:0:0 2 -
v v7 OffPtr t33 0 - p0:0:0:0:0 0 v9
v v5 LocalAddr t33 0 a4 p2:277:2:0:0 0 v9,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,8=v8
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v8 Const64 t14 8 - p0:0:0:0:0 1 -
v v11 RotateLeft16 t2 0 - p2:277:14:1:0 1 v6,v8
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 8=v8
freev v5,v7,v9,v10,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:277:277
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v16,v15,v14,v13,v2,v3,v4,v10,v9,v7,v5,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{math/bits.ReverseBytes16}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v13,v14,v15,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
regalloc 13 v6:R0,v11:R0,v12:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v13,v14,v15,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
regalloc 13 v6:R0,v11:R0,v12:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 16 1
b b1 Ret p2:277:19:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:277:19:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v11 ARM64REV16W t2 0 - p2:277:14:1:0 1 v6
v v12 MakeResult t34 0 - p2:277:2:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7,v8,v9,v10,v13,v14,v15,v16
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:277:277
fstate scheduled,laidout
regalloc 13 v6:R0,v11:R0,v12:[]
dcllen 2
end
frontend
end
ptrcache t5,t6,t7,t8,t9,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t2,t6,t9,t7,t10,t11,t14,t15,t25,t26,t12,t13,t3,t17,t33,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/math/bits/ReverseBytes16,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "math/bits"
func "ReverseBytes16" 1
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
type t1 2 2 0 0 - "uint16"
name n1 "x" PPARAM t1 1 "math/bits.x" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "math/bits.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "math/bits/bits.go" 1 1 -1 1 "math/bits/bits.go" "math/bits/bits.go" 1 1
sym y1 "math/bits.ReverseBytes16" 1
curfn p2:276:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 276 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math/bits.ReverseBytes16.arginfo1" 0
sym y4 "math/bits.ReverseBytes16.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:276:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:276:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:276:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:276:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:276:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:276:6:2:0
p 6 6 0 0 0 - REV16W 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:277:14:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:277:19:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 276 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVH MOVHU
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:11:50
dbgregout n2
dbgpc 1:11:7
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:276:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:276:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:276:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:276:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:276:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:276:6:2:0
p 6 0 0 0 91 - REV16W 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:277:14:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:277:19:2:0
fn y1 8 0 0 0 276 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVH MOVHU
funcaux y2 y2 - - y3 y4 -
text 16 0 0004c05ac0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0002ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 040400 0
data y11 SRODATA 4 1 28000 ac040400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.uint16" 0
sym y18 "type:uint16" 0
dwfn y13 y14 y15 - y16 "math/bits.ReverseBytes16" 1:276 1 0 1 50
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint16" 0 0 1 p2:276:21:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint16" 0 0 1 p2:276:31:0:0
var 0 0 "x" 5 1 0 0 0 8 y17 "math/bits/bits.go" 276 21 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y17 "math/bits/bits.go" 276 31 0 1 0 0 -
scope 0 0 - 0,1
data y13 SDWARFFCN 65 0 0 036d6174682f626974732e5265766572736542797465733136000010019c020000009402012d780000940200000000000000002e7e723000019402000000000000 5
reloc 0 0 R_USETYPE 0 y18
reloc 26 1 R_DWTXTADDR_U1 0 y1
reloc 43 4 R_DWARFSECREF 0 y17
reloc 47 4 R_DWARFSECREF 0 y14
reloc 59 4 R_DWARFSECREF 0 y17
data y14 SDWARFLOC 8 0 0 0100040004015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y16 SDWARFLINES 24 0 0 00090200000000000000000402038f02140637020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `math/bits.ReverseBytes16`. -/
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

/-- The index of `v11`'s `REV16W R0, R0` among the Progs (`kdOK` checks it). -/
def jF : Nat := 6

/-- A PC table for `b1` with `v11` (index 2) at its Prog and the value after it at the next. -/
def tab : PcTab := [(1, List.replicate 3 6 ++ [7])]

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
def K0 : KMap := (KMap.bot.set! 0 (some 16))

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
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w16 0x1234 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v11`: the arguments' words, the activation's `g` and `FP`, the PC of
`v11`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x1234 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

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

/-- The register value `.int .w16 0x3412`. -/
def isRes : Option Val → Bool
  | some (.int .w16 x) => x == 0x3412
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w16 0x3412) := by
  unfold isRes at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `math/bits.ReverseBytes16`: it holds an arm64 op; G57's value check
`vkind57` rejects `v11` (REV16W), which `vkind58a` accepts with the Prog at `jF`; the Progs
have distinct IDs below `2^32`; every home is one G10 handles; `checkFrame` passes; `b1` holds
`v11` at index 2; no frame variable is accessed and there is no home slot; `v11` reads its
registers at the classes of `K0`; and `stepLoc` runs `v11` to `.int .w16 0x3412` in its register. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (vkind57 lc g (val 11)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 11).isSome && blk.values[2]? == some 11 &&
    (val 11).op == .ARM64REV16W && (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    (kReads lc (val 11)).all (fun rc => K0.get rc.1 == some rc.2) && K0.get 0 == some 16 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) (fun s1 => isRes s1.regs[0]?)

theorem g58a_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (vkind57 lc g (val 11)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.value? 11 = some (val 11) ∧ blk.values[2]? = some 11 ∧
      (val 11).op = .ARM64REV16W ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧
      (∀ rc ∈ kReads lc (val 11), K0.get rc.1 = some rc.2) ∧ (K0.get 0 = some 16) ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) (fun s1 => isRes s1.regs[0]?) = true := by
  have hf := g58a_facts
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

/-! ## `v11`: `REV16W R0, R0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w16 0x1234) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases h0 : r = 0
    · subst h0; simp
    · simp [h0]
  · cases h

theorem locMatch0 : LocMatch E s0 1 2 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
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

theorem inv0 (hk0 : K0.get 0 = some 16) :
    G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [hk0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G58, group A, on `math/bits.ReverseBytes16`** (`func ReverseBytes16(x uint16) uint16`, on
arm64 `REV16W R0, R0` of the 16-bit `x`: `checkG57` asks a `REV16W` argument of at least 32 bits
(`v11: REV16W widths`) and `vkind58a` accepts it (the low halfword of the result reads only the low
halfword). From `s0`, with `x = 0x1234` in `R0`, `stepLoc` runs `v11` to `0x3412`, and `vk58a_step`
relates it to a machine run of its Prog to a state with `X0`'s low halfword `0x3412`, under an
activation extending `E` that is again a `G49Env`.) -/
theorem genG58a_witness :
    (vkind57 lc g (val 11)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 11) = .ok s1 ∧ s1.regs[0]? = some (.int .w16 0x3412) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 3 m1 ∧
        (m1.x 0).setWidth 16 = 0x3412 := by
  obtain ⟨hl, h57, hkd, hlt, hnd, hhome, hcf, hv, -, -, hav, hsl, hrd, hk0, hrun⟩ :=
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
  have hj : E.pcOf 1 2 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 1 (2 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk58a_step (H := GenG2.H0) (L := []) (bid := 1)
    (i := 2) (j := jF) (j' := jF + 1) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0
    (inv0 hk0) (fun e he => by cases he) hs1
  refine ⟨h57, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1, ?_⟩
  exact (hm1.regs 0 _ hr1).1 _ (by simp [objX?])

end GoFV.Proof.Witness.GenG58a
