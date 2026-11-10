import GoFV.Proof.Gen.G48
import GoFV.Proof.Witness.GenG49

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness of slice G48 (issue #553, `docs/plans/proofs3.md` §8 item 7)

`runtime.exit`'s ABI wrapper (quick-v10) passes `code` from `R0` to the `ABI0` `runtime.exit` on
the stack: `MOVW R0, 8(RSP)`, then `CALL runtime.exit(SB)`. `checkG57` rejects it, `checkG48`
accepts it, and `g48_value` relates the store (`genG48_witness`) and the call, under `CallOKStk`
for a callee that returns at once (`genG48_call_witness`), to the machine in an activation whose
`outargs` block sits at `SP`.
-/

namespace GoFV.Proof.Witness.GenG48

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/exit,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "exit" 1 1 0
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
type t2 INT32 4 4 0 comparable,named "int32" "int32"
type t1 FUNC 8 8 8 hasptr,direct "func(int32)" "func(int32)" 0 1 0
field 0 "code" t2 ? 0
aux a2 sym "runtime.exit" "runtime.exit" 1 - 0 - - - - 0
posbase p188 "runtime/stubs2.go" 1 1 -1
aux a3 name "code" "code" PPARAM t2 0 1 used p188:20:11:0:0
aux a1 call "AuxCall{runtime.exit}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
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
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t2
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
posbase p1 "<autogenerated>" 1 1 -1
aux a5 sym "runtime.exit" "runtime.exit" 0 - 0 - - - - 0
aux a4 call "AuxCall{runtime.exit}" a5 0 1 0 16 0 0 0
abiparam in 0 t2 - - 8
slot s1 a3 t2 0 - 0
f b1 t1 a1 8 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t2,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t18 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:0:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
dcllen 1
end
pass 1 "number lines"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t18 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t18 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 3 "early deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 4 "short circuit"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 5 "decompose user"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 7 "opt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 8 "zero arg cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 9 "opt deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 1
end
pass 10 "generic cse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 11 "phiopt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 12 "gcse deadcode"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 13 "nilcheckelim"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 14 "prove"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 15 "divisible"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 16 "divmod"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 17 "middle opt"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 18 "known bits"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 19 "early fuse"
f b1 t1 a1 8 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v6 StaticLECall t32 8 a4 p1:1:0:1:0 1 v5,v1
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 20 "expand calls"
aux a6 nameoff "code+0" a3 0
aux a7 type "int32" t2
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 2 -
v v2 OffPtr t18 0 - p0:0:0:0:0 0 v3
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2,8=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 21 "decompose builtin"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 2 -
v v2 OffPtr t18 0 - p0:0:0:0:0 0 v3
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2,8=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 22 "softfloat"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 2 -
v v2 OffPtr t18 0 - p0:0:0:0:0 0 v3
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2,8=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 23 "branchelim"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v4 SB t15 0 - p0:0:0:0:0 0 -
v v3 SP t15 0 - p0:0:0:0:0 2 -
v v2 OffPtr t18 0 - p0:0:0:0:0 0 v3
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v2,8=v9
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 24 "late opt"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 25 "dead auto elim"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 26 "sccp"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 27 "generic deadcode"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 28 "late fuse"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 29 "check bce"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 30 "dse"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 31 "memcombine"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 32 "writebarrier"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 StaticCall t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v9 OffPtr t18 8 - p0:0:0:0:0 1 v3
v v10 Store t28 0 a7 p1:1:0:1:0 1 v9,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 8=v9
freev v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 33 "lower"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 34 "addressing modes"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 35 "late lower"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 36 "pair"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1
cache linestarts 1:1:1
dcllen 1
end
pass 38 "lowered cse"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 39 "elim unread autos"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 41 "lowered deadcode"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 42 "checkLower"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 43 "loop invariant"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 45 "tighten"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 46 "late deadcode"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 47 "critical"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 48 "phi tighten"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 49 "likelyadjust"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
dcllen 1
end
pass 50 "layout"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate laidout
dcllen 1
end
pass 51 "schedule"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 52 "late nilcheck"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 53 "flagalloc"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v9,v2,v4
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 1
end
pass 54 "regalloc"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v3:SP,v5:R0
dcllen 1
end
pass 55 "loop rotate"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v3:SP,v5:R0
dcllen 1
end
pass 56 "trim"
f b1 t1 a1 10 1
b b1 Ret p1:1:0:0:0 0 0 - v8 - -
v v5 ArgIntReg t2 0 a6 p1:1:0:0:0 1 -
v v3 SP t15 0 - p0:0:0:0:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVWstore t28 8 - p1:1:0:1:0 1 v3,v5,v1
v v6 ARM64CALLstatic t32 8 a4 p1:1:0:1:0 1 v10
v v7 SelectN t28 0 - p1:1:0:0:0 1 v6
v v8 MakeResult t32 0 - p1:1:0:0:0 1 v7
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a6:2,-:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v3:SP,v5:R0
dcllen 1
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t7,t5,t8,t2,t9,t6,t10,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32
eof
"#

/-- `std/std/runtime/exit,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "exit" 1
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
type t1 4 4 0 0 - "int32"
name n1 "code" PPARAM t1 1 "runtime.code" 0 a3
in n1 0 used
out n1 0 used
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "runtime.exit" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 210085
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.exit.arginfo1" 0
sym y4 "runtime.exit.argliveinfo" 0
sym y5 "runtime.exit" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:1:0
p 7 7 0 0 0 - MOVW 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/NONE/0/8/-/- 0 0 p1:1:0:1:0
p 8 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 9 9 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:1:0
p 10 10 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:0:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 210085
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVW MOVW
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:-10000:1:6:50
dbgregout -
dbgpc 1:6:10
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p1:1:0:0:0
p 12 0 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p1:1:0:0:1
p 13 4 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 14 8 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 3 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 4 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 5 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:1:0
p 7 12 0 0 375 - MOVW 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p1:1:0:1:0
p 8 16 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p1:1:0:1:0
p 9 16 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p1:1:0:1:0
p 10 20 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 15 24 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 16 28 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:0:0
fn y1 8 24 23 0 1 210085
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVW MOVW
funcaux y2 y2 - - y3 y4 -
text 32 0 fe0f1ef8fd831ff8fd2300d1e00b00b900000094fd835ff8fe0742f8c0035fd6 1
reloc 16 4 R_CALLARM64 0 y5
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y2,_,_,_,y3,y4
usedfiles 0
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0004ff 0
data y4 SDATA 2 1 8000 0000 0
data y6 SRODATA 5 1 28000 0003010500 0
data y7 SRODATA 5 1 28000 0004020400 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 5 1 28000 0003040500 0
data y10 SRODATA 7 1 28000 020140063f0100 0
data y11 SRODATA 3 1 28000 020800 0
data y12 SRODATA 3 1 28000 040800 0
data y13 SRODATA 3 1 28000 000800 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
posbase p188 "runtime/stubs2.go" 1 1 -1 185 "runtime/stubs2.go" "runtime/stubs2.go" 1 1
sym y18 "go:info.int32" 0
dwfn y14 y15 y16 - y17 "runtime.exit" 0:1 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "int32" 0 0 1 p188:20:11:0:0
var 0 0 "code" 5 1 0 0 0 8 y18 "runtime/stubs2.go" 20 11 0 0 0 0 v0
scope 0 0 - 0
data y14 SDWARFFCN 42 0 0 0372756e74696d652e6578697400000020019c0100000001012d636f6465000014000000000000000000 3
reloc 14 2 R_DWTXTADDR_U2 0 y1
reloc 33 4 R_DWARFSECREF 0 y18
reloc 37 4 R_DWARFSECREF 0 y15
data y15 SDWARFLOC 9 0 0 010000040014015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y17 SDWARFLINES 18 0 0 00090200000000000000000a0f0220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.exit`'s ABI wrapper. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G48's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG48` gives (`b1`: the `PCDATA`s at 5 and 6, `v10`'s `MOVW R0, 8(RSP)` at
Prog 7, `v6`'s `CALL runtime.exit(SB)` at 9 after the `PCDATA` at 8, then the `RET` at 10). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 8, 10, 10, 10])]

/-- The class table `checkG48` gives. -/
def kt : KTab := (match checkG48 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- `SP`: the Phase 1 address of `outargs 0` (`Addrs.fixed`: `2^62`), where `ι` must put it
(`AddrAgree`). -/
def spO : BitVec 64 := 0x4000000000000000

/-- `ι`: the nil block, the globals at `symA`, the activation's `outargs` block at `SP`. -/
def ι48 : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .outargs 0 => some 0x4000000000000000
  | _ => none

/-- A framed activation (`SP = spO`, `g = 0x9000`, saved `LR` and `FP` 0) whose `outargs` block
sits at `SP` (`outSP`), with the PC table of `checkG48`. -/
def E : MatchEnv :=
  { lc, ι := ι48, sp := spO, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab, outSP := true }

/-- `SP`'s pointer: the start of the activation's `outargs` block. -/
def pO : Ptr := ⟨.outargs 0, 0⟩

/-- The Phase 1 memory before `v10`: the `outargs` block, 12 `poison` bytes (`outargsSize`: the
fixed frame word and `exit`'s `int32` argument). -/
def mem1 : Mem := { blocks := #[(.outargs 0, { data := Array.replicate 12 .poison })] }

/-- The `runLoc` state before `v10`: `code` (`v5`) = 7 in `R0`, `SP` (`v3`, `pO`) in the Go
register `SP`, every other register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .int .w32 7 else if i.val = 30 then .ptr pO else .poison,
    flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v10`: `X0 = 7`, the activation's `g` and `FP`, the PC of `v10`, the memory
0. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 7 else if k = 28 then 0x9000
      else if k = 29 then spO - 8 else 0,
    sp := spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 3, mem := fun _ => 0 }

/-- After the store: the memory holds `code`'s 4 bytes at `⟨outargs 0, 8⟩`, and its first block is
the `outargs` block, whose byte 8 is 7 and which holds no pointer word at offsets 0 to 8. -/
def dstIs (s : LocState) : Bool :=
  match s.mem with
  | .mem mm => mm.read ⟨.outargs 0, 8⟩ 4 == some #[.b 7, .b 0, .b 0, .b 0] &&
      match mm.blocks[0]? with
      | some (b, al) => b == .outargs 0 && al.data[8]? == some (.b 7) &&
          (List.range 9).all fun o => (ptrWordAt? al.data o).isNone
      | none => false
  | _ => false

/-- What compiled evaluation checks on `runtime.exit`'s ABI wrapper: it holds an arm64 op;
`checkG48` accepts it with `tab` and `kt` and `checkG57` does not (`v10: argument v3 in register
30`: the store's base is `SP`); it accesses no frame variable and has no home slot; its activation
is `0`; `b1` holds `v10` (`MOVWstore [8] v3 v5 v1`) at index 3, where `R0` has class 32, the Go
register `SP` class 64 and G35's table is empty; `stepLoc` runs `v10` from `s0` to a memory holding
`code`'s bytes at `⟨outargs 0, 8⟩`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG48 lc0 ps bs g).toOption == some (tab, kt) && (checkG57 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && lc.ctx.act == 0 &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 10).isSome && blk.values[3]? == some 10 &&
    (val 10).op == .ARM64MOVWstore &&
    (kAt lc kt 1 blk 3).get 0 == some 32 && (kAt lc kt 1 blk 3).get spReg == some 64 &&
    uL35 lc (uIn35 lc 1) blk 3 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) dstIs

theorem g48_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG48 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG57 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧ lc.ctx.act = 0 ∧
      1 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 1 = some blk ∧
      lc.ctx.f.value? 10 = some (val 10) ∧ blk.values[3]? = some 10 ∧
      (val 10).op = .ARM64MOVWstore ∧
      (kAt lc kt 1 blk 3).get 0 = some 32 ∧ (kAt lc kt 1 blk 3).get spReg = some 64 ∧
      uL35 lc (uIn35 lc 1) blk 3 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 10)) dstIs = true := by
  have hf := g48_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h57, hav, hsl, hact, hm1, hbs, hvs, hi3, hop, hk0, hk30, hu3, hrun⟩ := hf
  refine ⟨hl, ?_, h57, hav, hsl, hact, hm1, ?_, ?_, hi3, hop, hk0, hk30, hu3, hrun⟩
  · revert hres; cases checkG48 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

theorem dstIs_spec {s : LocState} (h : dstIs s = true) :
    ∃ mm al, s.mem = .mem mm ∧ mm.read ⟨.outargs 0, 8⟩ 4 = some #[.b 7, .b 0, .b 0, .b 0] ∧
      (Blk.outargs 0, al) ∈ mm.blocks ∧ al.data[8]? = some (.b 7) ∧
      ∀ o, o ≤ 8 → ptrWordAt? al.data o = none := by
  unfold dstIs at h
  split at h
  · rename_i mm hm
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    split at h2
    · rename_i b al hba
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Option.isNone_iff_eq_none] at h2
      obtain ⟨⟨rfl, h3⟩, h4⟩ := h2
      exact ⟨mm, al, hm, h1, Array.mem_of_getElem? hba, h3, fun o ho => h4 o (by omega)⟩
    · cases h2
  · cases h

/-! ## The activation -/

/-- `ι48` puts every block with a Phase 1 address (`nil`, `outargs 0`) at it. -/
theorem addrAgree48 : AddrAgree ι48 := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι48] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | outargs k =>
    cases k with
    | zero =>
      have h : (Blk.outargs 0).base? = some 0x4000000000000000 := by decide
      rw [h] at hb
      cases hb
      simp only [ι48, Option.some.injEq] at ha
      subst ha
      rfl
    | succ k => simp [ι48] at ha
  | _ => simp [ι48] at ha <;> simp [Blk.base?] at hb

theorem g48Env (hc : checkG48 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -⟩ :=
                checkG48L_spec hl (checkG48_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := addrAgree48
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -⟩ :=
                checkG48L_spec hl (checkG48_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by show 0 ≤ (8 : Int); decide
            frame := ⟨by show 4096 + 8 ≤ spO.toNat; decide,
              by show spO.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
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

theorem mem1_mem {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .outargs 0 ∧ al = { data := Array.replicate 12 .poison } := by
  simpa [mem1] using h

/-- `mem1` injected into the machine memory 0 by `ι48`: `outargs 0`'s `poison` bytes at `SP`. -/
theorem memInj1 : MemInj ι48 mem1 (fun _ => 0) := by
  refine ⟨rfl, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩
  · intro b al hb
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    exact ⟨spO, rfl, fun _ => by decide, by simp [spO]⟩
  · intro b al b' al' a a' hb hb' hne
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    obtain ⟨rfl, rfl⟩ := mem1_mem hb'
    exact absurd rfl hne
  · intro b al a hb _
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

/-- The separation of mode `outSP`: the `outargs` block's first word, below `writableFrom`, is
the saved `LR` word at `SP`, and `poison`. -/
theorem sepW1 : SepFromW ι48 (StkAt E) mem1 := by
  intro b al a hb ha y hy i hi he
  obtain ⟨rfl, rfl⟩ := mem1_mem hb
  obtain rfl : a = spO := (Option.some.inj ha).symm
  rcases hy with ⟨-, -, hlt⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x4000000000000000 := rfl
    have h4 : spO.toNat = 0x4000000000000000 := rfl
    exact ⟨by simp only [Blk.writableFrom]; omega, by simp⟩
  · cases hk

/-! ## `v10`: `MOVWstore [8] v3 v5 v1` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w32 7) ∨ (r = spReg ∧ x = .ptr pO) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 1 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x 0).setWidth 32 = 7
      decide
    · exact ⟨fun k hk => by simp [objX?, spReg] at hk, fun k hk => by simp [objV?, spReg] at hk⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g48Inv0 (h0 : (kAt lc kt 1 blk 3).get 0 = some 32)
    (h30 : (kAt lc kt 1 blk 3).get spReg = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 3) s0 E.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sepW1⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h30] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- `SPInv`: `outargs 0` at `SP`, the Go register `SP` holding `pO`, whose address `ι48` gives
as `SP`. -/
theorem spInv0 (hact : lc.ctx.act = 0) : SPInv E s0 := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show ι48 (.outargs lc.ctx.act) = some spO
    rw [hact]
    rfl
  · rcases s0_regs hx with ⟨h, -⟩ | ⟨-, rfl⟩ | rfl
    · simp [spReg] at h
    · exact ⟨spO, rfl, by simp [pO]; rfl⟩
    · trivial

/-- The per-value premises of G53 on `v10`, `MOVWstore`: none of them applies. -/
theorem pre53 (hop : (val 10).op = .ARM64MOVWstore) : G53Pre lc s0 (val 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVWstore → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩, ?_⟩
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

/-- The per-value premises of G54, which G57 takes, on `v10`: G53's (`pre53`); the loops'
(`Pre54a`, `Pre54b`) do not apply. -/
theorem pre54 (hop : (val 10).op = .ARM64MOVWstore) : G54Pre lc s0 (val 10) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOVWstore → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  exact ⟨pre53 hop, fun h => absurd h (hne _ (by decide)), fun h => absurd h (hne _ (by decide))⟩

/-- **G48 on `runtime.exit`'s ABI wrapper** (`ABIInternal` to `ABI0`: `code` arrives in `R0` and
leaves on the stack): `b1` stores `code` to the stack argument (`v10`, `MOVWstore [8] v3 v5 v1`,
`MOVW R0, 8(RSP)`) and calls the `ABI0` `runtime.exit` (`v6`, `CALLstatic`, whose ABI has one
stack input), which `checkG57` rejects (`v10: argument v3 in register 30`) and `checkG48` accepts.
In an activation whose `outargs` block (12 `poison` bytes) sits at `SP` (`outSP`, `SPInv`), from
`s0` with `code = 7` in `R0` and `SP`'s pointer in the Go register `SP`, `stepLoc` runs `v10` to a
memory holding `7` at `⟨outargs 0, 8⟩`, and `g48_value` relates it to a machine state after
`v10`'s `MOVW` whose memory holds `7` at `SP + 8`, under an activation extending `E` that is again
a `G49Env`, `SPInv` kept. -/
theorem genG48_witness :
    checkG48 lc0 ps bs g = .ok (tab, kt) ∧ (checkG57 lc0 ps bs g).toOption = none ∧
      ∃ s1 mm E1 m1, stepLoc GenG2.env lc s0 (val 10) = .ok s1 ∧ s1.mem = .mem mm ∧
        mm.read ⟨.outargs 0, 8⟩ 4 = some #[.b 7, .b 0, .b 0, .b 0] ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 1 4 m1 ∧ SPInv E1 s1 ∧ m1.mem (spO + 8) = 7 := by
  obtain ⟨hl, hc, h57, hav, hsl, hact, hm1, hb, hv10, hi3, hop, hk0, hk30, hu3, hrun⟩ := facts
  obtain ⟨s1, hs1, hd⟩ := GenG1.okThen_spec hrun
  obtain ⟨mm, al, hmm, hrd, hal, hal8, hpw⟩ := dstIs_spec hd
  have hE := g48Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOVWstore → (val 10).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g48_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 10 = some (val 10) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv10
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, hsp1, -⟩ := g48_value (H := GenG2.H0)
    (env := GenG2.env) hc hE hl0 hm0 hb0 hi3 hv0 (by rw [hop]; rfl) locMatch0 (g48Inv0 hk0 hk30)
    (spInv0 hact) rfl
    (by change UOKL m0 (uL35 lc (uIn35 lc 1) blk 3); rw [hu3]; intro e he; cases he)
    (pre54 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  -- Byte 8 of `outargs 0` after the store, read through `MemInj`: no pointer word covers it.
  have h8 : m1.mem (spO + 8) = 7 := by
    obtain ⟨mm1, hmm1, hinj⟩ := hm1'.mem
    rw [hmm] at hmm1
    cases hmm1
    obtain ⟨W, hW⟩ := hinj.bytes
    obtain ⟨hw, -, hby⟩ := hW _ _ _ hal (hx1.2 (.outargs 0) spO rfl)
    obtain ⟨h0, hd8⟩ := Array.getElem?_eq_some_iff.1 hal8
    have hr := hby 8 h0 (fun o ho ho' => by
      obtain ⟨p, hp, -⟩ := hw o ho
      rw [hpw o (by omega)] at hp
      cases hp)
    rw [hd8] at hr
    exact hr.symm
  exact ⟨hc, h57, s1, mm, E1, m1, hs1, hmm, hrd, hx1, hE1, hp1, hm1', hsp1, h8⟩

/-! ## `v6`: `CALLstatic {runtime.exit} v10`, the call with a stack argument -/

/-- Byte `i` of the `outargs` block after the store: `code = 7` at offset 8, else 0. -/
def byte2 (i : Nat) : BitVec 8 := if i = 8 then 7 else 0

/-- The `outargs` block after `v10`: the saved-`LR` word `poison`, then `code`'s 4 bytes. -/
def data2 : Array Byte :=
  Array.ofFn (n := 12) fun i => if i.val < 8 then .poison else .b (byte2 i.val)

/-- The Phase 1 memory before `v6`. -/
def mem2 : Mem := { blocks := #[(.outargs 0, { data := data2 })] }

/-- The machine memory before `v6`: the stack argument `7` at `SP + 8`, 0 elsewhere. -/
def M2 : Memory := fun y => if (y - spO).toNat < 12 then byte2 (y - spO).toNat else 0

/-- The `runLoc` state before `v6`: `SP`'s pointer in the Go register `SP`, every other register
`poison`, the memory `mem2`. -/
def sC : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 30 then .ptr pO else .poison,
    flags := .poison, slots := [], mem := .mem mem2 }

/-- The machine before `v6`: the activation's `g` and `FP`, the PC of `v6`, the memory `M2`. -/
def mC : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then spO - 8 else 0,
    sp := spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 4, mem := M2 }

/-- The memory is `mem1`: the `outargs` block all `poison` (Phase 1's call consumes the stack
arguments). -/
def memIs1 : Val → Bool
  | .mem mm => decide (mm = mem1)
  | _ => false

theorem memIs1_spec {x : Val} (h : memIs1 x = true) : x = .mem mem1 := by
  unfold memIs1 at h
  split at h
  · rw [of_decide_eq_true h]
  · cases h

/-- The call `v` has an ABI that `callRegs` and `callRegsZ` reject (a stack input) and whose
register arguments and results `callRegsS` gives as none. -/
def stkCall (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, cabi) =>
    (callRegs cabi).toOption.isNone && (callRegsZ lc.ctx.tabs cabi).toOption.isNone &&
      (callRegsS cabi).toOption == some ([], [])
  | none => false

theorem stkCall_spec {v : Value} (hf : stkCall v = true) {name : GoStr} {abi : Nat}
    {cabi : CallABI} (hc : callOf? lc.ctx.tabs v.aux = some (name, abi, cabi)) :
    (∀ {r}, callRegs cabi ≠ .ok r) ∧ (∀ {r}, callRegsZ lc.ctx.tabs cabi ≠ .ok r) ∧
      (∀ {ins outs}, callRegsS cabi = .ok (ins, outs) → ins = [] ∧ outs = []) := by
  unfold stkCall at hf
  rw [hc] at hf
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hf
  obtain ⟨⟨h1, h2⟩, h3⟩ := hf
  refine ⟨fun {r} h => ?_, fun {r} h => ?_, fun {ins outs} h => ?_⟩
  · rw [h] at h1; cases h1
  · rw [h] at h2; cases h2
  · rw [h] at h3
    simpa [Except.toOption] using h3

/-- What compiled evaluation checks on `v6`: `b1` holds it at index 4, a static call with a stack
input (`stkCall`), where the Go register `SP` has class 64 and G35's table is empty; `stepLoc`
runs it from `sC` to a state whose memory is `mem1` (the stack argument consumed). -/
def callFacts : Bool :=
  (lc.ctx.f.value? 6).isSome && blk.values[4]? == some 6 && (val 6).op == .ARM64CALLstatic &&
    stkCall (val 6) && (kAt lc kt 1 blk 4).get spReg == some 64 &&
    uL35 lc (uIn35 lc 1) blk 4 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc sC (val 6)) (fun s => memIs1 s.mem)

theorem g48_callFacts : callFacts = true := by
  native_decide

theorem cfacts :
    lc.ctx.f.value? 6 = some (val 6) ∧ blk.values[4]? = some 6 ∧
      (val 6).op = .ARM64CALLstatic ∧ stkCall (val 6) = true ∧
      (kAt lc kt 1 blk 4).get spReg = some 64 ∧ uL35 lc (uIn35 lc 1) blk 4 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc sC (val 6)) (fun s => memIs1 s.mem) = true := by
  have hf := g48_callFacts
  simp only [callFacts, Bool.and_eq_true, beq_iff_eq, and_assoc] at hf
  obtain ⟨hvs, hi4, hop, hst, hk30, hu4, hrun⟩ := hf
  refine ⟨?_, hi4, hop, hst, hk30, hu4, hrun⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
  simp [val, hv]

theorem mem2_mem {b : Blk} {al : Alloc} (h : (b, al) ∈ mem2.blocks) :
    b = .outargs 0 ∧ al = { data := data2 } := by
  simpa [mem2] using h

/-- `mem2` injected into `M2` by `ι48`: the stack argument's bytes at `SP + 8`. -/
theorem memInj2 : MemInj ι48 mem2 M2 := by
  refine ⟨rfl, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩
  · intro b al hb
    obtain ⟨rfl, rfl⟩ := mem2_mem hb
    exact ⟨spO, rfl, fun _ => by decide, by simp [spO, data2]⟩
  · intro b al b' al' a a' hb hb' hne
    obtain ⟨rfl, rfl⟩ := mem2_mem hb
    obtain ⟨rfl, rfl⟩ := mem2_mem hb'
    exact absurd rfl hne
  · intro b al a hb ha
    obtain ⟨rfl, rfl⟩ := mem2_mem hb
    have ha' : a = spO := (Option.some.inj ha).symm
    subst ha'
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp only [data2, Array.size_ofFn] at hi
    have hd : (spO + BitVec.ofNat 64 i - spO).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    by_cases h8 : i < 8
    · simp [ByteRel, data2, h8]
    · simp [ByteRel, M2, data2, hd, hi, h8]

theorem keys2 : KeysNodup mem2 := by simp [KeysNodup, mem2]

/-- The separation of mode `outSP`: the `outargs` block's saved-`LR` word is `poison`. -/
theorem sepW2 : SepFromW ι48 (StkAt E) mem2 := by
  intro b al a hb ha y hy i hi he
  obtain ⟨rfl, rfl⟩ := mem2_mem hb
  obtain rfl : a = spO := (Option.some.inj ha).symm
  rcases hy with ⟨-, -, hlt⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x4000000000000000 := rfl
    have h4 : spO.toNat = 0x4000000000000000 := rfl
    have hi8 : i < 8 := by omega
    exact ⟨by simp only [Blk.writableFrom]; omega, by simp [data2, hi8]⟩
  · cases hk

theorem sC_regs {r : Nat} {x : Val} (h : sC.regs[r]? = some x) :
    (r = spReg ∧ x = .ptr pO) ∨ x = .poison := by
  simp only [sC, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h30; exact Or.inl ⟨h30, h.symm⟩
    · exact Or.inr h.symm
  · cases h

theorem locMatchC : LocMatch E sC 1 4 mC where
  regs := by
    intro r v hv
    rcases sC_regs hv with ⟨rfl, rfl⟩ | rfl
    · exact ⟨fun k hk => by simp [objX?, spReg] at hk, fun k hk => by simp [objV?, spReg] at hk⟩
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [sC] at h
  mem := ⟨mem2, rfl, memInj2⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, mC, M2, E]; decide,
    by simp only [MState.word, readMem, mC, M2, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g48InvC (h30 : (kAt lc kt 1 blk 4).get spReg = some 64) :
    G3Inv E lc (kAt lc kt 1 blk 4) sC E.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem2, rfl, keys2, sepW2⟩
    rcases sC_regs hv with ⟨rfl, rfl⟩ | rfl
    · rw [h30] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [sC] at h

theorem spInvC (hact : lc.ctx.act = 0) : SPInv E sC := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show ι48 (.outargs lc.ctx.act) = some spO
    rw [hact]
    rfl
  · rcases sC_regs hx with ⟨-, rfl⟩ | rfl
    · exact ⟨spO, rfl, by simp [pO]; rfl⟩
    · trivial

/-- The per-value premises of G54 on `v6`, `CALLstatic`: none of them applies. -/
theorem pre54C (hop : (val 6).op = .ARM64CALLstatic) : G54Pre lc sC (val 6) := by
  have hne : ∀ o : Op, o ≠ .ARM64CALLstatic → (val 6).op ≠ o := fun o h h' =>
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

/-- `mem1` (all `poison`) injects into every machine memory. -/
theorem memInj1M (M : Memory) : MemInj ι48 mem1 M := by
  refine ⟨rfl, ?_, ?_, ⟨fun _ _ => False, ?_⟩⟩
  · intro b al hb
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    exact ⟨spO, rfl, fun _ => by decide, by simp [spO]⟩
  · intro b al b' al' a a' hb hb' hne
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    obtain ⟨rfl, rfl⟩ := mem1_mem hb'
    exact absurd rfl hne
  · intro b al a hb _
    obtain ⟨rfl, rfl⟩ := mem1_mem hb
    refine ⟨fun o ho => ho.elim, fun o _ ho => ho.elim, fun i hi _ => ?_⟩
    simp [ByteRel]

/-- `CallOKStk` for a callee that returns at once (`GenG2.H0`), at `v6` from `sC`: the call has no
register argument or result (`callRegsS` gives none), the machine keeps its memory (the stack
argument `7` at `SP + 8` included), and Phase 1's memory after the call, `mem1` (the stack
argument consumed, `GenG2.env`), is injected into it under `SepFromW`. -/
theorem callOKStkC {s2 : LocState} (hst : stkCall (val 6) = true) (hs2 : s2.mem = .mem mem1) :
    CallOKStk GenG2.H0 E g L lc sC s2 (val 6) mC := by
  intro _ name abi cabi ins outs hc hcr y args mm m₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨-, -, h3⟩ := stkCall_spec hst hc
  obtain ⟨rfl, rfl⟩ := h3 hcr
  exact ⟨E.ι, { m₁ with pc := m₁.x 30 }, mem1, rfl, fun _ _ h => h, addrAgree48, rfl, rfl, rfl,
    rfl, fun _ _ => rfl, hs2, memInj1M _, keys1, sepW1, fun r hr => by cases hr⟩

/-- **G48 on the stack-argument call of `runtime.exit`'s ABI wrapper**: `v6`, `CALLstatic
{runtime.exit} v10`, `CALL runtime.exit(SB)` of the `ABI0` `exit`, whose one input the ABI
assigns to the stack (`callRegs`, `callRegsZ` reject it; `callRegsS` gives no register). From
`sC`, after the store of `code = 7` at `⟨outargs 0, 8⟩` (the machine's `SP + 8` holds 7), in an
activation with `outargs 0` at `SP` (`outSP`, `SPInv`), with a callee that returns at once
(`GenG2.H0`; `CallOKStk` by `callOKStkC`), `stepLoc` runs the call (Phase 1 consumes the stack
argument: `outargs` is `poison` again) and `g48_value` relates it to a machine state after `v6`'s
`CALL` under an activation extending `E` that is again a `G49Env`, with `G3Inv` of the mode
`outSP` and `SPInv` kept. -/
theorem genG48_call_witness :
    mC.mem (spO + 8) = 7 ∧
      ∃ s2 E2 m2, stepLoc GenG2.env lc sC (val 6) = .ok s2 ∧ s2.mem = .mem mem1 ∧
        E.Extends E2 ∧ G49Env lc g L ps 0 tab E2 ∧ PStar GenG2.H0 L ps.toList 0 mC m2 ∧
        LocMatch E2 s2 1 5 m2 ∧ G3Inv E2 lc (kAt lc kt 1 blk 5) s2 E.outSP ∧
        SPInv E2 s2 := by
  obtain ⟨hl, hc, -, hav, hsl, hact, hm1, hb, -, -, -, -, -, -, -⟩ := facts
  obtain ⟨hv6, hi4, hop, hst, hk30, hu4, hrun⟩ := cfacts
  obtain ⟨s2, hs2, hmem⟩ := GenG1.okThen_spec hrun
  have hmem1 := memIs1_spec hmem
  have hE := g48Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64CALLstatic → (val 6).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 1 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 1 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 6 = some (val 6) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv6
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2, hinv2, hsp2, -⟩ := g48_value (H := GenG2.H0)
    (env := GenG2.env) hc hE hl0 hm0 hb0 hi4 hv0 (by rw [hop]; rfl) locMatchC (g48InvC hk30)
    (spInvC hact) rfl
    (by change UOKL mC (uL35 lc (uIn35 lc 1) blk 4); rw [hu4]; intro e he; cases he)
    (pre54C hop)
    (by
      intro _ _ _ _ _ _ _ _ _ _ hc' hcr
      exact absurd hcr (stkCall_spec hst hc').1)
    (by
      intro _ _ _ _ _ _ hc' hcr
      exact absurd hcr (stkCall_spec hst hc').2.1)
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (callOKStkC hst hmem1) hs2
  exact ⟨by decide, s2, E2, m2, hs2, hmem1, hx2, hE2, hp2, hm2, hinv2, hsp2⟩

end GoFV.Proof.Witness.GenG48
