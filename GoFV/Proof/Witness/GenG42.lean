import GoFV.Proof.Gen.G42
import GoFV.Proof.Witness.GenG41

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG42

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/unicode/utf8/RuneStart,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "unicode/utf8"
func "RuneStart" 1 0 0
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
config localpkg "unicode/utf8"
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
type t2 UINT8 1 1 0 comparable,named "byte" "uint8"
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "func(byte) bool" "func(uint8) bool" 0 1 1
field 0 "b" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "unicode/utf8.RuneStart" "unicode/utf8.RuneStart" 1 - 0 - - - - 0
posbase p2 "unicode/utf8/utf8.go" 1 1 -1
aux a3 name "b" "b" PPARAM t2 0 1 used p2:457:16:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p2:457:24:0:0
aux a1 call "AuxCall{unicode/utf8.RuneStart}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
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
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
type t34 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t2
type t35 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
type t36 RESULTS ? ? ? - "bool,mem" "" 2 t3,t29
slot s1 a3 t2 0 - 0
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:0:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t35 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v7 ConstBool t3 0 - p0:0:0:0:0 0 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:457:457
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:457:6:2:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "b+0" a3 0
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t35 0 a4 p2:457:31:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t35 0 a4 p2:457:31:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t35 0 a4 p2:457:31:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v7 SB t16 0 - p0:0:0:0:0 0 -
v v5 SP t16 0 - p0:0:0:0:0 2 -
v v4 OffPtr t34 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t35 0 a4 p2:457:31:0:0 0 v5,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8,0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v8 Const8 t2 -64 - p0:0:0:0:0 1 -
v v10 Const8 t2 -128 - p0:0:0:0:0 1 -
v v9 And8 t2 0 - p2:457:39:1:0 1 v6,v8
v v11 Neq8 t3 0 - p2:457:45:0:0 1 v9,v10
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -128=v10,-64=v8
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:457:457
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v3,v9,v10,v8
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{unicode/utf8.RuneStart}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
regalloc 13 v4:R1,v6:R0,v11:R0,v12:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
regalloc 13 v4:R1,v6:R0,v11:R0,v12:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p2:457:48:1:0 0 0 - v12 - -
v v6 ArgIntReg t2 0 a5 p2:457:48:1:0 1 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v4 ARM64ANDconst t10 192 - p2:457:45:0:0 1 v6
v v2 ARM64CMPWconst t30 128 - p2:457:45:0:0 1 v4
v v11 ARM64NotEqual t3 0 - p2:457:45:1:0 1 v2
v v12 MakeResult t36 0 - p2:457:31:0:0 1 v11,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v8,v9,v10
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:457:457
fstate scheduled,laidout
regalloc 13 v4:R1,v6:R0,v11:R0,v12:[]
dcllen 2
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t12,t13,t14,t16,t17,t18,t25,t34
typelink t2=t8,t18=t34,t29=t33
typeorder t4,t2=t8,t5,t9,t6,t10,t7,t11,t12,t15,t16,t26,t27,t13,t14,t3,t18=t34,t19,t20,t21,t22,t23,t24,t35,t25,t1,t17,t28,t29,t31,t30,t32,t33,t36
eof
"#

/-- `std/std/unicode/utf8/RuneStart,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "unicode/utf8"
func "RuneStart" 1
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
type t1 1 1 0 0 - "byte"
name n1 "b" PPARAM t1 1 "unicode/utf8.b" 0 a3
type t2 1 1 0 0 - "bool"
name n2 "~r0" PPARAMOUT t2 1 "unicode/utf8.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "unicode/utf8/utf8.go" 1 1 -1 1 "unicode/utf8/utf8.go" "unicode/utf8/utf8.go" 1 1
sym y1 "unicode/utf8.RuneStart" 1
curfn p2:457:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 457 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "unicode/utf8.RuneStart.arginfo1" 0
sym y4 "unicode/utf8.RuneStart.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:457:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:457:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:457:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:457:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:457:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:457:6:2:0
p 6 6 0 0 0 - AND 0 CONST/0/0/0/NONE/0/192/-/- 8192 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:457:45:1:0
p 7 7 0 0 0 - CMPW 0 CONST/0/0/0/NONE/0/128/-/- 8193 - _ 0 0 p2:457:45:2:0
p 8 8 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/129/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:457:45:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p2:457:48:2:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 457 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVB MOVBU
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
dbgpc 1:11:9
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:457:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:457:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:457:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:457:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:457:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:457:6:2:0
p 6 0 0 0 53 - AND 0 CONST/0/0/0/NONE/17/192/-/- 8192 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:457:45:1:0
p 7 4 0 0 96 - CMPW 0 CONST/0/0/0/NONE/17/128/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:457:45:2:0
p 8 8 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/129/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:457:45:2:0
p 9 12 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:457:48:2:0
fn y1 8 0 0 0 457 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVB MOVBU
funcaux y2 y2 - - y3 y4 -
text 16 0 01047a923f000271e0079f9ac0035fd6 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0001ff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 040400 0
data y11 SRODATA 4 1 28000 94070400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.unicode/utf8.RuneStart$abstract" 0
sym y17 "" 0
sym y18 "go:info.uint8" 0
sym y19 "go:info.bool" 0
sym y20 "type:bool" 0
dwfn y13 y14 y15 y16 y17 "unicode/utf8.RuneStart" 1:457 1 0 1 24
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uint8" 0 0 1 p2:457:16:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "bool" 0 0 1 p2:457:24:0:0
var 0 0 "b" 5 1 0 0 0 8 y18 "unicode/utf8/utf8.go" 457 16 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "unicode/utf8/utf8.go" 457 24 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:28
data y13 SDWARFFCN 32 0 0 06000000000010019c2900000000000000002e7e72300001c903000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y16
reloc 14 4 R_DWARFSECREF 0 y14
reloc 26 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 8 0 0 010004000c015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 24 0 0 0009020000000000000000040203c303140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 37 0 1 05756e69636f64652f757466382e52756e6553746172740001c90301226200000000000000 1
reloc 32 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `RuneStart`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G42's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG42` gives (`b1`: `v6`, `v1`, `v4`, `v2`, `v11`, `v12`, then the return). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 8, 9, 9])]

/-- The class table `checkG42` gives. -/
def kt : KTab := (match checkG42 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG42`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v4`: `b = 0xc5` (`v6`) in `R0`, every other register `poison`, the
empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .int .w8 0xc5 else .poison,
    flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v4`: `X0` holds `0xc5` in its low byte and ones above it (only the low
byte of a byte argument's register is known), the activation's `g` and `FP`, the PC of `v4`, a
zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0xffffffffffffffc5 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The register holds the 32-bit `0xc0`. -/
def isC0 : Option Val → Bool
  | some (.int .w32 x) => x == 0xc0
  | _ => false

theorem isC0_spec {o : Option Val} (h : isC0 o = true) : o = some (.int .w32 0xc0) := by
  unfold isC0 at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `RuneStart`: it holds an arm64 op; `checkG42` accepts it
with `tab` and `kt` and `checkG41` does not; it accesses no frame variable and has no home slot;
`b1` holds `v4` (`ANDconst [192] v6`, of type `uint32`) at index 2, where `R0` has class 8 and
G35's table is empty; `stepLoc` runs `v4` from `s0` to `R1 = 0xc0`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG42 lc0 ps bs g).toOption == some (tab, kt) && (checkG41 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 4).isSome && blk.values[2]? == some 4 && (val 4).op == .ARM64ANDconst &&
    (kAt lc kt 1 blk 2).get 0 == some 8 && uL35 lc (uIn35 lc 1) blk 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) (fun s1 => isC0 s1.regs[1]?)

theorem g42_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG42 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG41 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 4 = some (val 4) ∧ blk.values[2]? = some 4 ∧
      (val 4).op = .ARM64ANDconst ∧
      (kAt lc kt 1 blk 2).get 0 = some 8 ∧ uL35 lc (uIn35 lc 1) blk 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 4)) (fun s1 => isC0 s1.regs[1]?) = true := by
  have hf := g42_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h41, hav, hsl, hm1, hbs, hvs, hi2, hop, hk0, hu2, hrun⟩ := hf
  refine ⟨hl, ?_, h41, hav, hsl, hm1, ?_, ?_, hi2, hop, hk0, hu2, hrun⟩
  · revert hres; cases checkG42 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g42Env (hc : checkG42 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              checkG42L_spec hl (checkG42_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG42L_spec hl (checkG42_spec hc).2
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

/-! ## `v4`: `AND $192, R0, R1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w8 0xc5) ∨ x = .poison := by
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
      show (m0.x 0).setWidth 8 = 0xc5
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g42Inv0 (h0 : (kAt lc kt 1 blk 2).get 0 = some 8) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of `v4`, `ANDconst`: none of G41's applies. -/
theorem pre4 (hop : (val 4).op = .ARM64ANDconst) : G41Pre lc s0 (val 4) := by
  have hne : ∀ o : Op, o ≠ .ARM64ANDconst → (val 4).op ≠ o := fun o h h' =>
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
  · intro h; rcases h with h | h | h <;> exact absurd h (hne _ (by decide))

/-- **G42 on `unicode/utf8.RuneStart`**: `b1` masks the byte `b` (`v6`, in `R0`) by `0xc0` at type
`uint32` (`v4`, `ANDconst [192]`, `AND $192, R0, R1`), which `checkG41` rejects (the result's
class 32 exceeds the argument's 8) and `checkG42` accepts. From `s0`, `b = 0xc5`, where the
machine's `X0` holds ones above the low byte, `stepLoc` runs `v4` to `R1 = 0xc0`, and `g42_value`
relates it to a machine state after `v4`'s code whose `X1` is `0xc0` in its low 32 bits, under an
activation extending `E` that is again a `G28Env`. -/
theorem genG42_witness :
    (checkG41 lc0 ps bs g).toOption = none ∧ m0.x 0 = 0xffffffffffffffc5 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 4) = .ok s1 ∧
        s1.regs[1]? = some (.int .w32 0xc0) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧ (m1.x 1).setWidth 32 = 0xc0 := by
  obtain ⟨hl, hc, h41, hav, hsl, hm1, hb, hv4, hi2, hop, hk0, hu2, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isC0_spec hr
  have hE := g42Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ANDconst → (val 4).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g42_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 4 = some (val 4) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv4
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g42_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g42Inv0 hk0)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 2); rw [hu2]; intro e he; cases he)
    (pre4 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h41, rfl, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', ?_⟩
  exact (hm1'.regs 1 _ hr1).1 1 (by simp [objX?])

end GoFV.Proof.Witness.GenG42
