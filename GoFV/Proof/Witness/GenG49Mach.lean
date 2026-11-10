import GoFV.Proof.Gen.G49Mach
import GoFV.Gen.Check57
import GoFV.Proof.Witness.GenG2

/-!
# Non-vacuity witness: `VarsAt49` at `Addrs.fixed` and at `Addrs.atSP` on `runtime.secret_getStack`'s ABI0 wrapper

`std/std/runtime/secret_getStack,0.ssa` and `std/std/runtime/secret_getStack,0.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the ABI0 wrapper
of `func secret_getStack() (uintptr, uintptr)`, which calls the ABIInternal function and stores
its results from `R0` and `R1` into its stack results `~r0` and `~r1` (aux 3 and 4) at their
`NAME_PARAM` operands 0 and 8. `checkG57` accepts it (as every slice from G49 does), and it is
end to end on quick-v10 (#668). Its two results are accessed `Blk.local` variables 8 bytes
apart: at `Addrs.fixed` no activation of it is a `G49Env` (`g49Env_fixed_apart`), at
`Addrs.atSP` the activation with the results at their operands is one (`g49Env_atSP`):
`genG49Mach_witness`.
-/

namespace GoFV.Proof.Witness.GenG49Mach

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/secret_getStack,0.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "secret_getStack" 0 1 0
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
config abiself 0
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
type t1 FUNC 8 8 8 hasptr,direct "func() (uintptr, uintptr)" "func() (uintptr, uintptr)" 0 0 2
field 0 "" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "runtime/secret.getStack" "runtime/secret.getStack" 0 - 0 - - - - 0
posbase p178 "runtime/secret.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p178:82:25:0:0
aux a4 name "~r1" "~r1" PPARAMOUT t2 8 1 - p178:82:34:0:0
aux a1 call "AuxCall{runtime/secret.getStack}" a2 0 0 2 24 0 0 0
abiparam out 0 t2 a3 - 8
abiparam out 1 t2 a4 - 16
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
posbase p1 "<autogenerated>" 1 1 -1
type t33 RESULTS ? ? ? - "uintptr,uintptr,mem" "" 3 t2,t2,t28
aux a6 sym "runtime/secret.getStack" "runtime/secret.getStack" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime/secret.getStack}" a6 1 0 2 8 0 0 2
abiparam out 0 t2 - 0 -1
abiparam out 1 t2 - 1 -1
f b1 t1 a1 12 1
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t14,UInt=t15,Uintptr=t2,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Const64 t2 0 - p0:0:0:0:0 0 -
v v7 StaticLECall t33 0 a5 p1:1:0:0:0 4 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v9 SelectN t2 0 - p1:1:0:0:0 0 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts 0=v6
freev -
freeb -
dcllen 6
end
pass 1 "number lines"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Const64 t2 0 - p0:0:0:0:0 0 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 4 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v9 SelectN t2 0 - p1:1:0:0:0 0 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts 0=v6
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t2 0 - p0:0:0:0:0 2 -
v v3 SB t2 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t21 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Const64 t2 0 - p0:0:0:0:0 0 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 4 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v9 SelectN t2 0 - p1:1:0:0:0 0 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts 0=v6
freev -
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 3 "early deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 4 "short circuit"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 5 "decompose user"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 7 "opt"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 8 "zero arg cse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 9 "opt deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 1:1:1
dcllen 6
end
pass 10 "generic cse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 11 "phiopt"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 12 "gcse deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 13 "nilcheckelim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 14 "prove"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 15 "divisible"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 16 "divmod"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 17 "middle opt"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 18 "known bits"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 19 "early fuse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticLECall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:0:0 1 v7
v v11 SelectN t2 1 - p1:1:0:0:0 1 v7
v v12 MakeResult t33 0 - p1:1:0:0:0 1 v10,v11,v8
names -
splits -
canon -
consts -
freev v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 20 "expand calls"
aux a7 type "uintptr" t2
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v9 SB t2 0 - p0:0:0:0:0 0 -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 21 "decompose builtin"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v9 SB t2 0 - p0:0:0:0:0 0 -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 22 "softfloat"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v9 SB t2 0 - p0:0:0:0:0 0 -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 23 "branchelim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v9 SB t2 0 - p0:0:0:0:0 0 -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev -
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 24 "late opt"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 25 "dead auto elim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 26 "sccp"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 27 "generic deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 28 "late fuse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 29 "check bce"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 30 "dse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 31 "memcombine"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 32 "writebarrier"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 StaticCall t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 2 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v5 LocalAddr t21 0 a3 p1:1:0:0:0 1 v6,v8
v v4 Store t28 0 a7 p1:1:0:0:0 2 v5,v10,v8
v v3 LocalAddr t21 0 a4 p1:1:0:0:0 1 v6,v4
v v2 Store t28 0 a7 p1:1:0:0:0 1 v3,v11,v4
names -
splits -
canon -
consts -
freev v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 33 "lower"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 34 "addressing modes"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 35 "late lower"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 36 "pair"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 38 "lowered cse"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 39 "elim unread autos"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 41 "lowered deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 42 "checkLower"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 43 "loop invariant"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 45 "tighten"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 46 "late deadcode"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 47 "critical"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 48 "phi tighten"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 49 "likelyadjust"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
dcllen 6
end
pass 50 "layout"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate laidout
dcllen 6
end
pass 51 "schedule"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 6
end
pass 52 "late nilcheck"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 6
end
pass 53 "flagalloc"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 6
end
pass 54 "regalloc"
aux a5 call "AuxCall{runtime/secret.getStack}" a6 1 0 2 8 0 0 2
abiparam out 0 t2 - 0 -1
abiparam out 1 t2 - 1 -1
callreg - 0:1,1:2 7fffffff97ffffff -
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:SP,v7:[R0;R1],v10:R0,v11:R1
dcllen 6
end
pass 55 "loop rotate"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:SP,v7:[R0;R1],v10:R0,v11:R1
dcllen 6
end
pass 56 "trim"
f b1 t1 a1 12 1
b b1 Ret p1:1:0:1:0 0 0 - v12 - -
v v6 SP t2 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v7 ARM64CALLstatic t33 0 a5 p1:1:0:1:0 3 v1
v v10 SelectN t2 0 - p1:1:0:1:0 1 v7
v v11 SelectN t2 1 - p1:1:0:1:0 1 v7
v v8 SelectN t28 2 - p1:1:0:0:0 1 v7
v v4 ARM64MOVDstore t28 0 a3 p1:1:0:0:0 1 v6,v10,v8
v v2 ARM64MOVDstore t28 0 a4 p1:1:0:0:0 1 v6,v11,v4
v v12 MakeResult t32 0 - p1:1:0:0:0 1 v2
names -
splits -
canon -
consts -
freev v3,v5,v9
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap -:1
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 12 v6:SP,v7:[R0;R1],v10:R0,v11:R1
dcllen 6
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t15,t2,t25,t26,t13,t14,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `std/std/runtime/secret_getStack,0.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "secret_getStack" 0
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
name n1 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a3
name n2 "~r1" PPARAMOUT t1 1 "runtime.~r1" 0 a4
name n3 ".autotmp_2" PAUTO t1 1 "runtime..autotmp_2" 0 -
name n4 ".autotmp_3" PAUTO t1 1 "runtime..autotmp_3" 0 -
name n5 ".autotmp_4" PAUTO t1 3 "runtime..autotmp_4" 0 -
name n6 ".autotmp_5" PAUTO t1 3 "runtime..autotmp_5" 0 -
in n1 0 -
in n2 8 -
in n3 0 used,autotmp
in n4 0 used,autotmp
in n5 0 used,autotmp
in n6 0 used,autotmp
out n1 0 used
out n2 8 used
opt n3 0 autotmp
opt n4 0 autotmp
opt n5 0 autotmp
opt n6 0 autotmp
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "runtime/secret.getStack" 0
curfn p1:1:0:0:0 0 0
regargs -
text y1 0 0 23 0 1 90085
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime/secret.getStack" 1
sym y4 "runtime.~r0" 0
sym y5 "runtime.~r1" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p1:1:0:1:0
p 4 4 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p1:1:0:1:0
p 5 5 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:1:0
p 6 6 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/0/y4/- 0 0 p1:1:0:2:0
p 7 7 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/PARAM/0/8/y5/- 0 0 p1:1:0:2:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 90085
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgregout -
dbgpc -
end
asm
sym y6 "" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i16 0 0 p1:1:0:0:0
p 10 0 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p1:1:0:0:1
p 11 4 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 12 8 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 12 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 3 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:1:0
p 4 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p1:1:0:1:0
p 5 12 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y3/- 0 0 p1:1:0:1:0
p 6 16 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/48/0/y4/- 0 0 p1:1:0:2:0
p 7 20 0 0 304 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/PARAM/47/8/y5/- 0 0 p1:1:0:2:0
p 8 24 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 13 28 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:2:0
p 14 32 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:2:0
fn y1 16 8 23 0 1 90085
funcaux y2 y2 - - - - -
text 48 0 fe0f1ff8fd831ff8fd2300d100000094e00f00f9e11300f9fd835ff8fe0741f8c0035fd6000000000000000000000000 1
reloc 12 4 R_CALLARM64 0 y3
pcln y8 y9 y10 y11 y6,y7 y2,y2
usedfiles 0
data y2 Sxxx 0 4 8000 0100000000000000 0
data y6 SRODATA 5 1 28000 0003010900 0
data y7 SRODATA 5 1 28000 0003020900 0
data y8 SRODATA 7 1 28000 020120071f0400 0
data y9 SRODATA 3 1 28000 020c00 0
data y10 SRODATA 3 1 28000 040c00 0
data y11 SRODATA 3 1 28000 000c00 0
end
dwarf
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
posbase p178 "runtime/secret.go" 1 1 -1 175 "runtime/secret.go" "runtime/secret.go" 1 1
sym y16 "go:info.uintptr" 0
dwfn y12 y13 y14 - y15 "runtime/secret.getStack" 0:1 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "uintptr" 0 0 1 p178:82:25:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "uintptr" 0 0 1 p178:82:34:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p1:1:0:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p1:1:0:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p1:1:0:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "uintptr" 0 0 1 p1:1:0:0:0
var 0 0 "~r0" 5 0 1 0 0 8 y16 "runtime/secret.go" 82 25 0 0 0 0 -
var 1 0 "~r1" 5 0 1 0 0 16 y16 "runtime/secret.go" 82 34 0 1 0 0 -
scope 0 0 - 0,1
data y12 SDWARFFCN 65 0 0 0372756e74696d652f7365637265742e676574537461636b00000030019c0100000001012e7e7230000152000000000291082e7e72310001520000000002911000 3
reloc 25 2 R_DWTXTADDR_U2 0 y1
reloc 43 4 R_DWARFSECREF 0 y16
reloc 57 4 R_DWARFSECREF 0 y16
data y13 SDWARFLOC 0 0 0 - 0
data y14 SDWARFRANGE 0 0 0 - 0
data y15 SDWARFLINES 20 0 0 00090200000000000000000a0f06af0220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded wrapper (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of the wrapper. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context the slices' checks run on (`liveCtx`). -/
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

/-- The PC table `checkG57` gives. -/
def tab : PcTab := (match checkG57 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation at `SP = 0x7fff0000` (`g = 0x9000`, saved `LR` and `FP` 0) with GenG2's
injection (`nil ↦ 0`, the globals at `symA`), no home slot, the PC table of `checkG57`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- What compiled evaluation checks on the wrapper: `checkG57` accepts it; the Prog IDs are below
`2^32`; the accessed frame variables are the results `~r1` (aux 4) and `~r0` (aux 3), both
`Blk.local` (`Tables.forgeable`), at `NAME_PARAM` 8 and 0, `SP + 32` and `SP + 24`; the activation
is 0; there is no home slot. -/
def gFacts : Bool :=
  (checkG57 lc0 ps bs g).toOption.isSome && ps.toList.all (fun p => decide (p.id < 2 ^ 32)) &&
    accessedVars lc == [4, 3] && varOp g 3 == some (.PARAM, 0) && varOp g 4 == some (.PARAM, 8) &&
    lc.ctx.tabs.forgeable 3 && lc.ctx.tabs.forgeable 4 && lc.ctx.act == 0 &&
    (homeSlots lc).isEmpty && decide (frameOff L .PARAM 0 = 24) && decide (frameOff L .PARAM 8 = 32)

theorem g49Mach_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    (checkG57 lc0 ps bs g).toOption.isSome = true ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      accessedVars lc = [4, 3] ∧ varOp g 3 = some (.PARAM, 0) ∧ varOp g 4 = some (.PARAM, 8) ∧
      lc.ctx.tabs.forgeable 3 = true ∧ lc.ctx.tabs.forgeable 4 = true ∧ lc.ctx.act = 0 ∧
      (homeSlots lc).isEmpty = true ∧ frameOff L .PARAM 0 = 24 ∧ frameOff L .PARAM 8 = 32 := by
  have hf := g49Mach_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    and_assoc] at hf
  exact hf

section Fixed

open scoped GoFV.SSA.Sem.Fixed

/-- `E` is an activation of the wrapper at `Addrs.fixed` without the variables' places
(`G28Env`): its `ι` gives no frame block an address. -/
theorem g28Env : G28Env lc g L ps 0 tab E := by
  obtain ⟨-, hlt, hav, -, -, hf3, hf4, -, hsl, -, -⟩ := facts
  exact
    { env :=
      { env :=
        { env :=
          { env :=
            { lcEq := rfl
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
              extra := by show 0 ≤ (8 : Int); decide
              frame := ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
                by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
            vars := by
              intro x hx o _ hf
              rw [hav] at hx
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
              rcases hx with rfl | rfl
              · rw [hf4] at hf; cases hf
              · rw [hf3] at hf; cases hf }
          wbs := fun h => by cases h }
        icalls := fun h => by cases h }
      memeqs := fun h => by cases h }

/-- At `Addrs.fixed`, no activation of the wrapper, under any layout, Prog list, return address
and PC table, is a `G49Env`: its results' `local` blocks would sit at `SP + frameOff` 8 bytes
apart, `Blk.fixedBase?` puts them `2^24` apart. -/
theorem fixed_none (L' : Link) (ps' : Array GoFV.Asm.Prog) (ret : BitVec 64) (tab' : PcTab)
    (E' : MatchEnv) : ¬ G49Env lc g L' ps' ret tab' E' := by
  obtain ⟨-, -, hav, h3, h4, hf3, hf4, -, -, -, -⟩ := facts
  intro hE
  refine g49Env_fixed_apart hE (x := 4) (y := 3) (by simp [hav]) (by simp [hav]) h4 h3
    (.inr rfl) (.inr rfl) hf4 hf3 ?_
  simp only [frameOff]
  omega

end Fixed

/-- A concrete instance of `addrAgree_fixed_apart`'s premises: at `Addrs.fixed`, the `local`
blocks 1 and 2 of activation 0 at their fixed bases, `2^62 + 2^24` and `2^62 + 2^25`, are at
`s + 0` and `s + 2^24` for `s = 2^62 + 2^24`. -/
theorem addrAgree_fixed_apart_witness :
    ∃ ι : Blk → Option (BitVec 64), @AddrAgree Addrs.fixed ι ∧
      ι (.local 0 1) = some (BitVec.ofNat 64 (2 ^ 62 + 2 ^ 24) + BitVec.ofInt 64 0) ∧
      ι (.local 0 2) = some (BitVec.ofNat 64 (2 ^ 62 + 2 ^ 24) + BitVec.ofInt 64 (2 ^ 24)) := by
  refine ⟨fun b => (Blk.fixedBase? b).map (BitVec.ofNat 64), ?_, by decide, by decide⟩
  intro b n a hb ha _
  have hb' : Blk.fixedBase? b = some n := hb
  dsimp only at ha
  rw [hb'] at ha
  injection ha with ha
  exact ha.symm

/-- The activation `E` with the results' `local` blocks at their frame operands. -/
def EM : MatchEnv := { E with ι := ιSP g L E.sp E.ι }

/-- The results' bases under `Addrs.atSP`: `SP + 24` and `SP + 32`. -/
theorem iotaM : EM.ι (.local 0 3) = some (EM.sp + BitVec.ofInt 64 24) ∧
    EM.ι (.local 0 4) = some (EM.sp + BitVec.ofInt 64 32) := by
  obtain ⟨-, -, -, h3, h4, -, -, -, -, ho0, ho8⟩ := facts
  have hι : EM.ι = ιSP g L E.sp E.ι := rfl
  have hsp : EM.sp = E.sp := rfl
  rw [hι, hsp, ιSP_local0 h3, ιSP_local0 h4, ho0, ho8]
  exact ⟨rfl, rfl⟩

/-- **`VarsAt49` at `Addrs.fixed` and at `Addrs.atSP` on `runtime.secret_getStack`'s ABI0
wrapper.** `checkG57` accepts the wrapper, whose accessed frame variables are its two stack
results `~r0` and `~r1` (aux 3 and 4, `Blk.local`, `NAME_PARAM` 0 and 8). At `Addrs.fixed` no
activation of it is a `G49Env` (`fixed_none`, by `g49Env_fixed_apart`): `g57_value` and the
other slice theorems hold of it only vacuously there. At `Addrs.atSP (baseSP g L E.sp)` the
activation `EM`, whose `ι` puts the two results at `SP + 24` and `SP + 32`, is a `G49Env`
(`g49Env_atSP` of G28's activation `g28Env`). -/
theorem genG49Mach_witness :
    (checkG57 lc0 ps bs g).toOption.isSome = true ∧ accessedVars lc = [4, 3] ∧
      lc.ctx.tabs.forgeable 3 = true ∧ lc.ctx.tabs.forgeable 4 = true ∧
      (∀ L' ps' ret tab' E', ¬ @G49Env Addrs.fixed lc g L' ps' ret tab' E') ∧
      @G49Env (Addrs.atSP (baseSP g L E.sp)) lc g L ps 0 tab EM ∧
      EM.ι (.local 0 3) = some (EM.sp + BitVec.ofInt 64 24) ∧
      EM.ι (.local 0 4) = some (EM.sp + BitVec.ofInt 64 32) := by
  obtain ⟨h57, -, hav, -, -, hf3, hf4, hact, -, -, -⟩ := facts
  exact ⟨h57, hav, hf3, hf4, fixed_none, g49Env_atSP g28Env hact, iotaM⟩

end GoFV.Proof.Witness.GenG49Mach
