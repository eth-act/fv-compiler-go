import GoFV.Proof.Gen.G9
import GoFV.Proof.Witness.GenG2

/-!
# Non-vacuity witness: slice G9 of the genssa validator on `runtime.fint64to32`

`std/runtime/fint64to32,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): the soft-float
conversion `func fint64to32(x int64) uint32 { return fintto32(x) }` (`runtime/softfloat64.go`).

`checkG8` rejects it: `R0` holds the 64-bit argument `v6` and the 32-bit result `v10` of the
static call `v8 = CALLstatic {runtime.fintto32} v6 v1` (G2's `resultReg`); `checkG9` accepts it
with the PC table `tab` and the class table `kt`. By compiled evaluation (`native_decide`, listed
in `scripts/axioms-allowlist.txt`; `g9_facts`), `stepLoc` runs the call `v8` (a callee contract
`env9` returning the 32-bit 7), its result `v10` and its memory `v9` from the state after the
entry values (`x` in `R0`). On a framed activation with `G8Env` (`SP = 0x7fff0000`, every symbol
at `2^40`, the Progs at `0x10000 + 4·ID`, `ret = 0`) and a callee hook `Hc` that returns to `X30`
with `X0 = 7` (which satisfies `CallOK`: `callOKc`), `g9_value` three times gives a machine run of
the Progs through the `CALL` to a state related before `v11` (`genG9_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG9

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/runtime/fint64to32,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "fint64to32" 1 0 0
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
type t2 INT64 8 8 0 comparable,named "int64" "int64"
type t3 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t1 FUNC 8 8 8 hasptr,direct "func(int64) uint32" "func(int64) uint32" 0 1 1
field 0 "x" t2 ? 0
field 1 "" t3 ? 0
aux a2 sym "runtime.fint64to32" "runtime.fint64to32" 1 - 0 - - - - 0
posbase p186 "runtime/softfloat64.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p186:562:17:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t3 0 1 - p186:562:26:0:0
aux a1 call "AuxCall{runtime.fint64to32}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
type t4 BOOL 1 1 0 comparable,named "bool" "bool"
type t5 INT8 1 1 0 comparable,named "int8" "int8"
type t6 INT16 2 2 0 comparable,named "int16" "int16"
type t7 INT32 4 4 0 comparable,named "int32" "int32"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t3
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
type t33 PTR 8 8 8 hasptr,direct,comparable "*int64" "*int64" t2
type t34 RESULTS ? ? ? - "uint32,mem" "" 2 t3,t28
aux a6 sym "runtime.fintto32" "runtime.fintto32" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.fintto32}" a6 1 1 1 8 8 1 1
abiparam in 0 t2 - 0 0
abiparam out 0 t3 - 0 -1
slot s1 a3 t2 0 - 0
f b1 t1 a1 11 1
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t2,UInt8=t8,UInt16=t9,UInt32=t3,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v7 Const32 t3 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t34 8 a5 p186:563:17:0:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v7 Const32 t3 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t19 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v7 Const32 t3 0 - p0:0:0:0:0 0 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7
freev -
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 186:563:563
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p186:562:6:2:0 1 -
v v8 StaticLECall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 20 "expand calls"
aux a7 nameoff "x+0" a3 0
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 2 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p186:563:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 2 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p186:563:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 2 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p186:563:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 2 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
v v7 SB t15 0 - p0:0:0:0:0 0 -
v v5 SP t15 0 - p0:0:0:0:0 2 -
v v4 OffPtr t33 0 - p0:0:0:0:0 0 v5
v v3 LocalAddr t19 0 a4 p186:563:2:0:0 0 v5,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v4
freev v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 StaticCall t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2
cache linestarts 186:563:563
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v3,v4,v5,v7,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.fint64to32}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t3 a4 0 -1
callreg 0:1 - 0 -
aux a5 call "AuxCall{runtime.fintto32}" a6 1 1 1 8 8 1 1
abiparam in 0 t2 - 0 0
abiparam out 0 t3 - 0 -1
callreg 0:1 0:1 7fffffff97ffffff -
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
regalloc 12 v6:R0,v8:[R0],v10:R0,v11:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
regalloc 12 v6:R0,v8:[R0],v10:R0,v11:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 11 1
b b1 Ret p186:563:2:1:0 0 0 - v11 - -
v v6 ArgIntReg t2 0 a7 p186:563:2:1:0 1 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v8 ARM64CALLstatic t34 8 a5 p186:563:17:1:0 2 v6,v1
v v10 SelectN t3 0 - p186:563:17:1:0 1 v8
v v9 SelectN t28 1 - p186:563:17:0:0 1 v8
v v11 MakeResult t34 0 - p186:563:2:0:0 1 v10,v9
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v5,v7
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,-:2,a7:3
cache linestarts 186:563:563
fstate scheduled,laidout
regalloc 12 v6:R0,v8:[R0],v10:R0,v11:[]
dcllen 3
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27
typelink t28=t32
typeorder t5,t8,t6,t9,t7,t3,t2,t10,t11,t14,t15,t25,t26,t12,t13,t4,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/runtime/fint64to32,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "fint64to32" 1
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
type t1 8 8 0 0 - "int64"
name n1 "x" PPARAM t1 1 "runtime.x" 0 a3
type t2 4 4 0 0 - "uint32"
name n2 "~r0" PPARAMOUT t2 1 "runtime.~r0" 0 a4
name n3 ".autotmp_2" PAUTO t2 3 "runtime..autotmp_2" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used,autotmp
out n1 0 used
opt n3 0 autotmp
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p186 "runtime/softfloat64.go" 1 1 -1 183 "runtime/softfloat64.go" "runtime/softfloat64.go" 1 1
sym y1 "runtime.fint64to32" 1
curfn p186:562:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 562 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.fint64to32.arginfo1" 0
sym y4 "runtime.fint64to32.argliveinfo" 0
sym y5 "runtime.fintto32" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p186:562:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p186:562:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p186:562:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p186:562:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p186:562:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p186:562:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p186:563:17:1:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p186:563:17:1:0
p 8 8 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p186:563:17:1:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p186:563:2:2:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 562 201080
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
dbgloc 0 1:-10000:1:8:50
dbgregout n2
dbgpc 1:8:9
end
asm
sym y6 "runtime.morestack_noctxt" 0
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i8 0 0 p186:562:6:0:0
p 11 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p186:562:6:0:0
p 12 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p186:562:6:0:0
p 13 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p186:562:6:0:0
p 14 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@23 0 0 p186:562:6:0:0
p 15 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p186:562:6:0:0
p 16 12 32 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-32/-/- 0 0 p186:562:6:0:1
p 17 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p186:562:6:0:0
p 18 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p186:562:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p186:562:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p186:562:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p186:562:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p186:562:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p186:562:6:2:0
p 6 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p186:563:17:1:0
p 7 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p186:563:17:1:0
p 8 24 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p186:563:17:1:0
p 9 28 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p186:563:2:2:0
p 19 32 -32 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/32/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p186:563:2:2:0
p 20 36 32 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p186:563:2:2:0
p 21 40 -32 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p186:563:2:2:0
p 22 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p186:562:6:0:0
p 23 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p186:562:6:0:0
p 24 40 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p186:562:6:0:0
p 25 44 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p186:562:6:0:0
p 26 48 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y6/- 0 0 p186:562:6:0:0
p 27 52 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p186:562:6:0:0
p 28 52 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p186:562:6:0:0
p 29 56 32 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@11 0 0 p186:562:6:0:0
fn y1 8 24 0 0 562 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 64 0 900b40f9ff6330eb09010054fe0f1ef8fd831ff8fd2300d100000094fd835ff8fe0742f8c0035fd6e00700f9e3031eaa00000094e00740f9f2ffff1700000000 2
reloc 24 4 R_CALLARM64 0 y5
reloc 48 4 R_CALLARM64 0 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y2,_,_,_,y3,y4
usedfiles 183
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y7 SRODATA 11 1 28000 0001010202030107020300 0
data y8 SRODATA 7 1 28000 00060204010600 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 5 1 28000 0006040a00 0
data y11 SRODATA 7 1 28000 020440053f0700 0
data y12 SRODATA 4 1 28000 f0021000 0
data y13 SRODATA 8 1 28000 e608060204010600 0
data y14 SRODATA 3 1 28000 001000 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.runtime.fint64to32$abstract" 0
sym y19 "" 0
sym y20 "go:info.int64" 0
sym y21 "go:info.uint32" 0
sym y22 "type:uint32" 0
dwfn y15 y16 y17 y18 y19 "runtime.fint64to32" 183:562 1 0 1 4262
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y18 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "int64" 0 0 1 p186:562:17:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "uint32" 0 0 1 p186:563:17:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "uint32" 0 0 1 p186:562:26:0:0
var 0 0 "x" 5 1 0 0 0 8 y20 "runtime/softfloat64.go" 562 17 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y21 "runtime/softfloat64.go" 562 26 0 1 0 0 -
scope 0 0 - 0,1
dieref y15 3 y18 0
dieoff y18 0:24
data y15 SDWARFFCN 33 0 0 0600000000000040019c2900000000000000002e7e72300001b204000000000000 6
reloc 0 0 R_USETYPE 0 y22
reloc 1 4 R_DWARFSECREF 0 y18
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y18
reloc 15 4 R_DWARFSECREF 0 y16
reloc 27 4 R_DWARFSECREF 0 y21
data y16 SDWARFLOC 9 0 0 01000004001c015000 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y19 SDWARFLINES 30 0 0 000902000000000000000004b80103ac04140a8788063706860218000101 1
reloc 3 8 R_ADDR 0 y1
data y18 SDWARFABSFCN 33 0 1 0572756e74696d652e66696e743634746f33320001b20401227800000000000000 1
reloc 28 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded `fint64to32` (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

def lc : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

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

/-- The PC table `checkG9` gives (block `b1`: the call `v8`'s `CALL` at 8). -/
def tab : PcTab := [(1, [5, 5, 5, 9, 9, 9, 9])]

/-- The class table `checkG9` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot)]

/-- Block `b1`: `v6 = ArgIntReg` (`R0`), `v1 = InitMem`, `v8 = CALLstatic v6 v1`,
`v10 = SelectN [0] v8` (`R0`), `v9 = SelectN [1] v8`, `v11 = MakeResult v10 v9`; `Ret`. -/
def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at their symbols and the PC table of `checkG9`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The callee `runtime.fintto32` returns the 32-bit 7 and the memory unchanged. -/
def env9 : Env := { extern := fun _ => some fun _ _ m => .returned [.int .w32 7] m }

/-- The `runLoc` state after the entry values: `x` in `R0`, every other register `poison`, the
empty memory. -/
def s0 (x : BitVec 64) : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .i64 x else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v8`: `X0 = x`, the activation's `g` and `FP`, the PC of `v8`, the memory
0. -/
def m0 (x : BitVec 64) : MState :=
  { x := fun k => if k = 0 then x else if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8
      else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 2, mem := fun _ => 0 }

/-- A callee that returns to `X30` with `X0 = 7`. -/
def Hc : Hooks :=
  ⟨fun m => some (.ret { m with x := fun k => if k = 0 then 7 else m.x k, pc := m.x 30 })⟩

/-- The static call `v` has the one result register `R0`. -/
def outs0 (lc : LocCtx) (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, cabi) =>
    match callRegs cabi with
    | .ok (_, outs) => decide (outs = [0])
    | .error _ => false
  | none => false

/-- `R0` holds the 32-bit 7. -/
def r0is7 (s : LocState) : Bool :=
  match s.regs[0]? with
  | some (Val.int Width.w32 x) => decide (x = 7)
  | _ => false

/-- What compiled evaluation checks on `fint64to32`: `checkG9` accepts it with `tab` and `kt` and
`checkG8` does not; it accesses no frame variable and has no home slot; `b1` holds `v8`, `v10`,
`v9` at 2, 3, 4; their ops; `v8`'s result register is `R0`; `R0` holds a 64-bit value before `v8`;
and `stepLoc` runs `v8` (to `R0 = 7` and the memory `mem0`), `v10`, `v9` from `s0 5`. -/
def gFacts : Bool :=
  (checkG9 lc ps bs g).toOption == some (tab, kt) && (checkG8 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 8).isSome && (lc.ctx.f.value? 10).isSome && (lc.ctx.f.value? 9).isSome &&
    blk1.values[2]? == some 8 && blk1.values[3]? == some 10 && blk1.values[4]? == some 9 &&
    (val 8).op == .ARM64CALLstatic && (val 10).op == .SelectN && (val 9).op == .SelectN &&
    outs0 lc (val 8) && (kAt lc kt 1 blk1 2).get 0 == some 64 &&
    GenG1.okThen (stepLoc env9 lc (s0 5) (val 8)) fun s1 =>
      r0is7 s1 && GenG2.memIs0 s1.mem &&
      GenG1.okThen (stepLoc env9 lc s1 (val 10)) fun s2 =>
        GenG1.okThen (stepLoc env9 lc s2 (val 9)) fun _ => true

theorem g9_facts : gFacts = true := by
  native_decide

/-- The facts of `g9_facts` as hypotheses. -/
theorem facts :
    checkG9 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 8 = some (val 8) ∧
      lc.ctx.f.value? 10 = some (val 10) ∧ lc.ctx.f.value? 9 = some (val 9) ∧
      blk1.values[2]? = some 8 ∧ blk1.values[3]? = some 10 ∧ blk1.values[4]? = some 9 ∧
      (val 8).op = .ARM64CALLstatic ∧ (val 10).op = .SelectN ∧ (val 9).op = .SelectN ∧
      outs0 lc (val 8) = true ∧ (kAt lc kt 1 blk1 2).get 0 = some 64 ∧
      (GenG1.okThen (stepLoc env9 lc (s0 5) (val 8)) fun s1 =>
        r0is7 s1 && GenG2.memIs0 s1.mem &&
        GenG1.okThen (stepLoc env9 lc s1 (val 10)) fun s2 =>
          GenG1.okThen (stepLoc env9 lc s2 (val 9)) fun _ => true) = true := by
  have hf := g9_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv8⟩, hv10⟩, hv9⟩, hi2⟩, hi3⟩,
    hi4⟩, hop8⟩, hop10⟩, hop9⟩, hout⟩, hk0⟩, hrun⟩ := hf
  have hval : ∀ n, (lc.ctx.f.value? n).isSome = true → lc.ctx.f.value? n = some (val n) := by
    intro n h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
    simp [val, hv]
  refine ⟨?_, hav, hsl, hm1, ?_, hval _ hv8, hval _ hv10, hval _ hv9, hi2, hi3, hi4, hop8, hop10,
    hop9, hout, hk0, hrun⟩
  · revert hres; cases checkG9 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]

theorem g9Env (hc : checkG9 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G8Env lc g L ps 0 tab E where
  env := {
    env := {
      lcEq := rfl
      link := rfl
      pcOf := rfl
      retOut := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG9_spec hc
        intro p hp
        exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
      addr := GenG2.addrAgree
      glob := fun _ _ _ _ => rfl
      syms := by
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG9_spec hc
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
  wbs := fun h => by cases h

theorem locMatch0 (x : BitVec 64) : LocMatch E (s0 x) 1 2 (m0 x) where
  regs := by
    intro r v hv
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · split at hv
        · subst hv
          rename_i h0
          subst h0
          simp only [objX?] at hk
          cases hk
          exact Or.inl rfl
        · subst hv; trivial
      · split at hv
        · rename_i h0; subst h0; simp [objV?] at hk
        · subst hv; trivial
    · cases hv
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g9Inv0 (x : BitVec 64) {K : KMap} (h0 : K.get 0 = some 64) : G3Inv E lc K (s0 x) where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    simp only [s0, Array.getElem?_ofFn] at hv
    split at hv
    · simp only [Option.some.injEq] at hv
      split at hv
      · rename_i h0'
        subst hv; subst h0'
        rw [h0] at hc; cases hc; rfl
      · subst hv; trivial
    · cases hv
  slots := by intro k v h; simp [s0] at h

/-- The callee contract of `Hc` at a static call whose one result register is `R0`: it returns to
`X30` with the memory `mem0` and the result 7 in `R0`, as `runLoc`'s state after the call has
(stated for any context, so that the kernel never evaluates the parsed function). -/
theorem callOKc {lc' : LocCtx} {g' : G2In} {L' : Link} {v : Value} {E' : MatchEnv}
    (hA : AddrAgree E'.ι) (hnil : E'.ι .nil = some 0)
    {s s' : LocState} {m : MState} (hmem : GenG2.memIs0 s'.mem = true) (h7 : r0is7 s' = true)
    (hno : outs0 lc' v = true) : CallOK Hc E' g' L' lc' s s' v m := by
  intro _ name abi cabi ins outs y args mm m₁ hc hcr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hout : outs = [0] := by
    unfold outs0 at hno
    rw [hc] at hno
    dsimp only at hno
    rw [hcr] at hno
    exact of_decide_eq_true hno
  have hm' : s'.mem = .mem GenG2.mem0 := by
    unfold GenG2.memIs0 at hmem
    split at hmem
    · rename_i mm' he
      rw [he, of_decide_eq_true hmem]
    · cases hmem
  have h0 : s'.regs[0]? = some (.int .w32 7) := by
    unfold r0is7 at h7
    split at h7
    · rename_i x hx
      rw [hx, of_decide_eq_true h7]
    · cases h7
  subst hout
  have h28 : (if (28 : Reg) = 0 then (7 : BitVec 64) else m₁.x 28) = m₁.x 28 :=
    ite_eq_right_iff.2 fun h => absurd h (by decide)
  have h29 : (if (29 : Reg) = 0 then (7 : BitVec 64) else m₁.x 29) = m₁.x 29 :=
    ite_eq_right_iff.2 fun h => absurd h (by decide)
  refine ⟨E'.ι, { m₁ with x := fun k => if k = 0 then 7 else m₁.x k, pc := m₁.x 30 },
    GenG2.mem0, rfl, fun _ _ h => h, hA, rfl, rfl, h28, h29, fun _ _ => rfl, hm',
    GenG2.memInj0 hnil _, GenG2.keys0, GenG2.sep0, fun r hr x hx => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  rw [h0] at hx
  cases hx
  refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
  simp only [objX?] at hk
  cases hk
  simp (config := { decide := true }) [ValRel]

theorem callOKc_ne {E' : MatchEnv} {s s' : LocState} {v : Value} {m : MState}
    (h : v.op ≠ .ARM64CALLstatic) : CallOK Hc E' g L lc s s' v m :=
  fun hop => absurd hop h

theorem wbOKc_ne {E' : MatchEnv} {s : LocState} {v : Value} {m : MState}
    (h : v.op ≠ .ARM64LoweredWB) : WbOK Hc E' g L lc s v m :=
  fun hop => absurd hop h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G9 on `fint64to32`**: from the state after the entry values (`x = 5` in `R0`), the static
call `v8` (whose result register `R0` held the 64-bit argument), its 32-bit result `v10` and its
memory `v9` are matched by a machine run of the Progs through the `CALL` and the callee `Hc` to a
state related before `v11`, with the registers at their classes, under an activation that extends
`E` and is a `G8Env`. -/
theorem genG9_value_witness :
    ∃ s1 s2 s3 E' m3, stepLoc env9 lc (s0 5) (val 8) = .ok s1 ∧
      stepLoc env9 lc s1 (val 10) = .ok s2 ∧ stepLoc env9 lc s2 (val 9) = .ok s3 ∧
      E.Extends E' ∧ G8Env lc g L ps 0 tab E' ∧ PStar Hc L ps.toList 0 (m0 5) m3 ∧
      LocMatch E' s3 1 5 m3 ∧ G3Inv E' lc (kAt lc kt 1 blk1 5) s3 := by
  obtain ⟨hc, hav, hsl, hm1, hb, hv8, hv10, hv9, hi2, hi3, hi4, hop8, hop10, hop9, hout, hk0,
    hrun⟩ := facts
  obtain ⟨s1, hs1, hrun⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hrun
  obtain ⟨⟨h7, hmem⟩, hrun⟩ := hrun
  obtain ⟨s2, hs2, hrun⟩ := GenG1.okThen_spec hrun
  obtain ⟨s3, hs3, -⟩ := GenG1.okThen_spec hrun
  have hE := g9Env hc hav hsl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g9_value (H := Hc) (env := env9) hc hE hm1
    hb hi2 hv8 (by rw [hop8]; rfl) (locMatch0 5) (g9Inv0 5 hk0)
    (g7Pre_of (by rw [hop8]; decide) (by rw [hop8]; decide)
      (by rw [hop8]; simp [loadOp?, narrowLoad?]) (by rw [hop8]; decide) (by rw [hop8]; decide)
      (by rw [hop8]; decide) _)
    (callOKc GenG2.addrAgree rfl hmem h7 hout) (wbOKc_ne (by rw [hop8]; decide)) hs1
  obtain ⟨E2, m2, hx2, hE2, hp2, hm2, hinv2⟩ := g9_value (H := Hc) (env := env9) hc hE1 hm1
    hb hi3 hv10 (by rw [hop10]; rfl) hm1' hinv1
    (g7Pre_of (by rw [hop10]; decide) (by rw [hop10]; decide)
      (by rw [hop10]; simp [loadOp?, narrowLoad?]) (by rw [hop10]; decide) (by rw [hop10]; decide)
      (by rw [hop10]; decide) _)
    (callOKc_ne (by rw [hop10]; decide)) (wbOKc_ne (by rw [hop10]; decide)) hs2
  obtain ⟨E3, m3, hx3, hE3, hp3, hm3, hinv3⟩ := g9_value (H := Hc) (env := env9) hc hE2 hm1
    hb hi4 hv9 (by rw [hop9]; rfl) hm2 hinv2
    (g7Pre_of (by rw [hop9]; decide) (by rw [hop9]; decide)
      (by rw [hop9]; simp [loadOp?, narrowLoad?]) (by rw [hop9]; decide) (by rw [hop9]; decide)
      (by rw [hop9]; decide) _)
    (callOKc_ne (by rw [hop9]; decide)) (wbOKc_ne (by rw [hop9]; decide)) hs3
  exact ⟨s1, s2, s3, E3, m3, hs1, hs2, hs3,
    MatchEnv.Extends.trans (MatchEnv.Extends.trans hx1 hx2) hx3, hE3,
    (hp1.trans hp2).trans hp3, hm3, hinv3⟩

end GoFV.Proof.Witness.GenG9
