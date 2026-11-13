import GoFV.Proof.Gen.G46
import GoFV.Proof.Witness.GenG45

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG46

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `examples/ifaces/main/sq.area,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "sq.area" 1 0 0
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
type t3 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t2 STRUCT 8 8 0 comparable,named "sq" "main.sq" 1
field 0 "s" t3 0 0
type t1 FUNC 8 8 8 hasptr,direct "method(sq) func() float64" "method(main.sq) func() float64" 1 0 1
field 0 "q" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "main.sq.area" "main.sq.area" 1 - 0 - - - - 0
posbase p2 "./main.go" 1 1 -1
aux a3 name "q" "q" PPARAM t2 0 1 used p2:14:7:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p2:14:20:0:0
aux a1 call "AuxCall{main.sq.area}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 16 0
abiparam out 0 t3 a4 16 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 INT64 8 8 0 comparable,named "int64" "int64"
type t9 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t10 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t11 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t12 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t13 INT 8 8 0 comparable,named "int" "int"
type t14 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t15 UINT 8 8 0 comparable,named "uint" "uint"
type t16 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t17 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t18 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t19 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t21 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t13
type t22 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t16
type t23 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t3
type t25 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t18
type t26 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t27 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t28 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t29 SSA ? ? ? - "mem" ""
type t30 SSA ? ? ? - "flags" ""
type t31 SSA ? ? ? - "void" ""
type t32 SSA 16 8 ? - "int128" ""
type t33 RESULTS ? ? ? - "mem" "" 1 t29
type t34 PTR 8 8 8 hasptr,direct,comparable "*sq" "*main.sq" t2
type t35 RESULTS ? ? ? - "float64,mem" "" 2 t3,t29
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t13,Float32=t14,Float64=t3,UInt=t15,Uintptr=t16,String=t17,BytePtr=t18,Int32Ptr=t19,UInt32Ptr=t20,IntPtr=t21,UintptrPtr=t22,Float32Ptr=t23,Float64Ptr=t24,BytePtrPtr=t25,Complex64=t26,Complex128=t27,UnsafePtr=t28,Mem=t29,Flags=t30,Void=t31,Int128=t32,ResultMem=t33
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t24 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v7 Const64F t3 0 - p0:0:0:0:0 0 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:0:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t24 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v7 Const64F t3 0 - p0:0:0:0:0 0 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 3 -
v v2 SP t16 0 - p0:0:0:0:0 2 -
v v3 SB t16 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t34 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t24 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v7 Const64F t3 0 - p0:0:0:0:0 0 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 5 "decompose user"
slot s2 a3 t3 0 - 0
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names s2
named s2 -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 1 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 1 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v9
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 2:14:14
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 0 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 2 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v9 StructSelect t3 0 - p2:14:47:0:0 0 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:14:6:2:0 1 -
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v9,v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 20 "expand calls"
aux a5 nameoff "q+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:14:47:2:0 1 v4
v v8 StructSelect t3 0 - p2:14:41:0:0 2 v6
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v8,v8
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v9 SB t16 0 - p0:0:0:0:0 0 -
v v7 SP t16 0 - p0:0:0:0:0 2 -
v v5 OffPtr t34 0 - p0:0:0:0:0 0 v7
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 1 -
v v3 LocalAddr t24 0 a4 p2:14:33:0:0 0 v7,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts 0=v5
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:14:47:2:0 0 v4
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v9 SB t16 0 - p0:0:0:0:0 0 -
v v7 SP t16 0 - p0:0:0:0:0 2 -
v v5 OffPtr t34 0 - p0:0:0:0:0 0 v7
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 3 -
v v3 LocalAddr t24 0 a4 p2:14:33:0:0 0 v7,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts 0=v5
freev v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:14:47:2:0 0 v4
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v9 SB t16 0 - p0:0:0:0:0 0 -
v v7 SP t16 0 - p0:0:0:0:0 2 -
v v5 OffPtr t34 0 - p0:0:0:0:0 0 v7
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 3 -
v v3 LocalAddr t24 0 a4 p2:14:33:0:0 0 v7,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts 0=v5
freev v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 2 -
v v6 StructMake t2 0 - p2:14:47:2:0 0 v4
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v9 SB t16 0 - p0:0:0:0:0 0 -
v v7 SP t16 0 - p0:0:0:0:0 2 -
v v5 OffPtr t34 0 - p0:0:0:0:0 0 v7
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 3 -
v v3 LocalAddr t24 0 a4 p2:14:33:0:0 0 v7,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts 0=v5
freev v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 Mul64F t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 2:14:14
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v3,v5,v7,v9,v6,v8,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.sq.area}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 16 0
abiparam out 0 t3 a4 16 -1
callreg 0:80000000 - 0 -
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v6,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
regalloc 12 v4:F0,v10:F0,v11:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v6,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
regalloc 12 v4:F0,v10:F0,v11:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p2:14:47:1:0 0 0 - v11 - -
v v4 ArgFloatReg t3 0 a5 p2:14:47:2:0 2 -
v v1 InitMem t29 0 - p0:0:0:0:0 1 -
v v10 ARM64FMULD t3 0 - p2:14:44:1:0 1 v4,v4
v v11 MakeResult t35 0 - p2:14:33:0:0 1 v10,v1
names -
namedx a3/t2/0/-/0 v6
splits s1/0/t3=s2
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v5,v6,v7,v8,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a5:3
cache linestarts 2:14:14
fstate scheduled,laidout
regalloc 12 v4:F0,v10:F0,v11:[]
dcllen 2
end
frontend
end
ptrcache t2,t3,t6,t7,t8,t9,t11,t13,t14,t16,t17,t18,t25
typelink t29=t33
typeorder t5,t9,t6,t10,t7,t11,t8,t12,t13,t15,t16,t26,t27,t14,t3,t4,t18,t19,t20,t21,t22,t23,t24,t25,t34,t1,t2,t17,t28,t29,t31,t30,t32,t33,t35
eof
"#

/-- `examples/ifaces/main/sq.area,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "sq.area" 1
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
type t1 8 8 0 0 - "sq"
name n1 "q" PPARAM t1 1 "main.q" 0 a3
type t2 8 8 0 0 - "float64"
name n2 "~r0" PPARAMOUT t2 1 "main.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./main.go" 1 1 -1 1 "./main.go" "./main.go" 1 1
sym y1 "main.sq.area" 1
curfn p2:14:6:0:0 0 0
regargs 8224:0:t2
text y1 0 0 0 0 14 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.sq.area.arginfo1" 0
sym y4 "main.sq.area.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:14:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:14:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:14:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:14:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:14:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:14:6:2:0
p 6 6 0 0 0 - FMULD 0 REG/8224/0/0/NONE/0/0/-/- 8224 - REG/8224/0/0/NONE/0/0/-/- 0 0 p2:14:44:1:0
p 7 7 0 0 0 - RET 0 _ 0 - _ 0 0 p2:14:47:2:0
p 8 8 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 14 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t2 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:10:9040
dbgregout n2
dbgpc 1:10:7
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p2:14:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:14:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:14:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:14:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:14:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:14:6:2:0
p 6 0 0 0 112 - FMULD 0 REG/8224/0/0/NONE/5/0/-/- 8224 - REG/8224/0/0/NONE/5/0/-/- 0 0 p2:14:44:1:0
p 7 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:14:47:2:0
fn y1 8 0 0 0 14 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
funcaux y2 y2 - - y3 y4 -
text 16 0 0008601ec0035fd60000000000000000 0
pcln y9 y10 y11 y12 y5,y6,y7,y8 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 5 1 8000 fe0008fdff 0
data y4 SDATA 2 1 8000 0000 0
data y5 SRODATA 0 1 28000 - 0
data y6 SRODATA 0 1 28000 - 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 3 1 28000 040400 0
data y9 SRODATA 3 1 28000 020400 0
data y10 SRODATA 3 1 28000 040400 0
data y11 SRODATA 3 1 28000 1e0400 0
data y12 SRODATA 3 1 28000 000400 0
end
dwarf
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "go:info.main.sq.area$abstract" 0
sym y17 "" 0
sym y18 "go:info.main.sq" 0
sym y19 "go:info.float64" 0
sym y20 "type:float64" 0
dwfn y13 y14 y15 y16 y17 "main.sq.area" 1:14 1 0 1 7
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y16 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "main.sq" 0 0 1 p2:14:7:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "float64" 0 0 1 p2:14:20:0:0
var 0 0 "q" 5 1 0 0 0 8 y18 "./main.go" 14 7 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y19 "./main.go" 14 20 0 1 0 0 -
scope 0 0 - 0,1
dieref y13 3 y16 0
dieoff y16 0:17
data y13 SDWARFFCN 31 0 0 06000000000010019c2900000000000000002e7e723000010e000000000000 6
reloc 0 0 R_USETYPE 0 y20
reloc 1 4 R_DWARFSECREF 0 y16
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 10 4 R_DWARFSECREF 0 y16
reloc 14 4 R_DWARFSECREF 0 y14
reloc 25 4 R_DWARFSECREF 0 y19
data y14 SDWARFLOC 9 0 0 010004000402904000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y15 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 23 0 0 000902000000000000000004020308140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y16 SDWARFABSFCN 26 0 1 056d61696e2e73712e6172656100010e01227100000000000000 1
reloc 21 4 R_DWARFSECREF 0 y18
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `sq.area`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G46's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG46` gives (`b1`: `v4`, `v1`, `v10`'s `FMULD F0, F0, F0` after the
`PCDATA` at 5, `v11`, then the `RET`). -/
def tab : PcTab := [(1, [5, 5, 5, 7, 7])]

/-- The class table `checkG46` gives. -/
def kt : KTab := (match checkG46 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG46`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The bits of `1.5`. -/
def side : BitVec 64 := 0x3ff8000000000000

/-- The bits of `1.5 · 1.5 = 2.25`. -/
def area : BitVec 64 := 0x4002000000000000

/-- The `runLoc` state before `v10`: the side `s.a = 1.5` (`v4`) in `F0` (Go register 31), every
other register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG37.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 31 then .int .w64 side else .poison,
    flags := .poison, slots := [], mem := .mem GenG37.mem0 }

/-- The machine before `v10`: `V0` holds `1.5`'s bits, the X registers the activation's `g` and
`FP`, the PC of `v10`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun k => if k = 0 then side.setWidth 128 else 0,
    nzcv := ⟨false, false, false, false⟩, pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- The value is the 64-bit `area`. -/
def isArea : Option Val → Bool
  | some (.int .w64 x) => x == area
  | _ => false

theorem isArea_spec {o : Option Val} (h : isArea o = true) : o = some (.int .w64 area) := by
  unfold isArea at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `sq.area`: it holds an arm64 op; `checkG46` accepts it with
`tab` and `kt` and `checkG45` does not; it accesses no frame variable and has no home slot; `b1`
holds `v10` (`FMULD v4 v4`, of type `float64`, in `F0`) at index 2, where `F0` has class 64 and
G35's table is empty; `stepLoc` runs `v10` from `s0` to `F0 = area`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG46 lc0 ps bs g).toOption == some (tab, kt) && (checkG45 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 10).isSome && blk.values[2]? == some 10 && (val 10).op == .ARM64FMULD &&
    (val 10).args[0]? == some 4 && (val 10).args[1]? == some 4 &&
    (kAt lc kt 1 blk 2).get 31 == some 64 && uL35 lc (uIn35 lc 1) blk 2 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) (fun s1 => isArea s1.regs[31]?)

theorem g46_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG46 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG45 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 10 = some (val 10) ∧ blk.values[2]? = some 10 ∧
      (val 10).op = .ARM64FMULD ∧ (val 10).args[0]? = some 4 ∧ (val 10).args[1]? = some 4 ∧
      (kAt lc kt 1 blk 2).get 31 = some 64 ∧ uL35 lc (uIn35 lc 1) blk 2 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) (fun s1 => isArea s1.regs[31]?) = true := by
  have hf := g46_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h45, hav, hsl, hm1, hbs, hvs, hi2, hop, ha0, ha1, hk31, hu2, hrun⟩ := hf
  refine ⟨hl, ?_, h45, hav, hsl, hm1, ?_, ?_, hi2, hop, ha0, ha1, hk31, hu2, hrun⟩
  · revert hres; cases checkG46 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g46Env (hc : checkG46 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              checkG46L_spec hl (checkG46_spec hc).2
            intro p hp
            exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
          addr := GenG12.addrAgree
          glob := fun _ _ _ _ => rfl
          syms := by
            obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
              checkG46L_spec hl (checkG46_spec hc).2
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

/-! ## `v10`: `FMULD F0, F0, F0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 31 ∧ x = .int .w64 side) ∨ x = .poison := by
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
    · refine ⟨fun k hk => by simp [objX?] at hk, fun k hk => ?_⟩
      simp only [objV?] at hk
      cases hk
      show (m0.v (BitVec.ofNat 5 (31 - 31))).setWidth 64 = side
      simp only [m0]
      decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG37.mem0, rfl, GenG37.memInj0 _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g46Inv0 (h31 : (kAt lc kt 1 blk 2).get 31 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 2) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG37.mem0, rfl, by simp [KeysNodup, GenG37.mem0],
      fun b al a h => by simp [GenG37.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h31] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- A value is no `FNaNSwap` pair with itself. -/
theorem fnanSwap_self (x : Val) : ¬ FNaNSwap x x := by
  intro h
  unfold FNaNSwap at h
  split at h
  all_goals first | exact (Nat.lt_irrefl _ h.1) | exact h

/-- The per-value premises of `v10`, `FMULD v4 v4`: G44's and G45's do not apply, and an operand
is no `FNaNSwap` pair with itself. -/
theorem pre10 (hop : (val 10).op = .ARM64FMULD) (ha0 : (val 10).args[0]? = some 4)
    (ha1 : (val 10).args[1]? = some 4) : G46Pre lc s0 (val 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMULD → (val 10).op ≠ o := fun o h h' =>
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
  · intro _ _ _ _ _ a0 a1 x y h0 h1 hx hy
    rw [ha0] at h0
    rw [ha1] at h1
    cases h0
    cases h1
    rw [hx] at hy
    cases hy
    exact fnanSwap_self x
  · intro _ _ _ _ hl; rw [hop] at hl; cases hl

/-- **G46 on `sq.area`** (`examples/ifaces`, `func (s sq) area() float64 { return s.a * s.a }`):
`b1` multiplies the side `s.a` (`v4`, in `F0`) by itself (`v10`, `FMULD v4 v4`, `FMULD F0, F0,
F0`), which `checkG45` rejects and `checkG46` accepts. From `s0`, with `s.a = 1.5`, `stepLoc` runs
`v10` to `F0 = 2.25` (`0x4002000000000000`), and `g46_value` relates it to a machine state after
`v10`'s code whose `V0` holds those bits in its low 64, under an activation extending `E` that is
again a `G28Env`. -/
theorem genG46_witness :
    (checkG45 lc0 ps bs g).toOption = none ∧ (m0.v 0).setWidth 64 = side ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 10) = .ok s1 ∧
        s1.regs[31]? = some (.int .w64 area) ∧
        E.Extends E1 ∧ G28Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 3 m1 ∧ (m1.v 0).setWidth 64 = area := by
  obtain ⟨hl, hc, h45, hav, hsl, hm1, hb, hv10, hi2, hop, ha0, ha1, hk31, hu2, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isArea_spec hr
  have hE := g46Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FMULD → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g46_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 10 = some (val 10) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv10
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g46_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi2 hv0 (by rw [hop]; rfl) locMatch0 (g46Inv0 hk31)
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 2); rw [hu2]; intro e he; cases he)
    (pre10 hop ha0 ha1)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  refine ⟨h45, by decide, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1', ?_⟩
  exact (hm1'.regs 31 _ hr1).2 0 (by simp [objV?])

end GoFV.Proof.Witness.GenG46
