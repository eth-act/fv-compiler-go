import GoFV.Proof.Gen.G12
import GoFV.Proof.Witness.GenG11

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G12 of the genssa validator on `runtime.subtractb`

`std/std/runtime/subtractb,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): `subtractb`
(`runtime/stubs.go`), `return (*byte)(unsafe.Pointer(uintptr(unsafe.Pointer(p)) - x))`.

`checkG11` rejects it (`v11 = Convert`); `checkG12` accepts it with the PC table `tab` and the
class table `kt`. Block `b1`: `v7 = ArgIntReg` (`p`, `R0`), `v8 = ArgIntReg` (`x`, `R1`),
`v1 = InitMem`, `v11 = Convert v7 v1` (`R0`), `v12 = SUB v11 v8` (`R0`), `v13 = Convert v12 v1`
(`R0`), `v15 = MakeResult v13 v1`; `Ret`. Its Progs: `SUB R1, R0, R0`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g12_facts`),
`stepLoc` runs `v11` from the state after the entry values with `p` a pointer 16 bytes into the
heap object `heap 1` (`pP`), and `R0` then holds its Phase 1 address `2^41 + 16`. On a framed
activation with `G10Env` (as `GenG11`'s) that injects `heap 1` at its Phase 1 address `2^41`
(`ι`), `g12_value` gives the state before `v12` with `R0` related to `X0` at its class: the
conversion emits no code and the integer is the machine word (`genG12_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG12

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/subtractb,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "subtractb" 1 1 0
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
type t3 UINT8 1 1 0 comparable,named "byte" "uint8"
type t2 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t3
type t4 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t1 FUNC 8 8 8 hasptr,direct "func(*byte, uintptr) *byte" "func(*uint8, uintptr) *uint8" 0 2 1
field 0 "p" t2 ? 0
field 1 "n" t4 ? 0
field 2 "" t2 ? 0
aux a2 sym "runtime.subtractb" "runtime.subtractb" 1 - 0 - - - - 0
posbase p49 "runtime/mbitmap.go" 1 1 -1
aux a3 name "p" "p" PPARAM t2 0 1 used p49:1041:16:0:0
aux a4 name "n" "n" PPARAM t4 8 1 used p49:1041:25:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t2 0 1 - p49:1041:36:0:0
aux a1 call "AuxCall{runtime.subtractb}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t4 a4 1 8
abiparam out 0 t2 a5 0 -1
type t5 BOOL 1 1 0 comparable,named "bool" "bool"
type t6 INT8 1 1 0 comparable,named "int8" "int8"
type t7 INT16 2 2 0 comparable,named "int16" "int16"
type t8 INT32 4 4 0 comparable,named "int32" "int32"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t8
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t4
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t19
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
type t35 PTR 8 8 8 hasptr,direct,comparable "**byte" "**uint8" t2
type t36 RESULTS ? ? ? - "*byte,mem" "" 2 t2,t30
slot s1 a3 t2 0 - 0
slot s2 a4 t4 0 - 0
f b1 t1 a1 15 1
typs Bool=t5,Int8=t6,Int16=t7,Int32=t8,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t4,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t35 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v9 ConstNil t2 0 - p0:0:0:0:0 0 -
v v10 Copy t29 0 - p49:1045:55:2:0 1 v7
v v11 Convert t4 0 - p49:1045:54:0:0 1 v10,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v14 Copy t2 0 - p49:1045:31:2:0 1 v13
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 3344556677=v9
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t35 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v9 ConstNil t2 0 - p0:0:0:0:0 0 -
v v10 Copy t29 0 - p49:1045:55:2:0 1 v7
v v11 Convert t4 0 - p49:1045:54:1:0 1 v10,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v14 Copy t2 0 - p49:1045:31:2:0 1 v13
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v14,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 3344556677=v9
freev -
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t35 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p49:1041:6:2:0 2 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v9 ConstNil t2 0 - p0:0:0:0:0 0 -
v v10 Copy t29 0 - p49:1045:55:2:0 0 v7
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 2 v12,v1
v v14 Copy t2 0 - p49:1045:31:2:0 0 v13
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 3344556677=v9
freev -
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache linestarts 49:1045:1045
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p49:1041:6:2:0 1 -
v v8 Arg t4 0 a4 p49:1041:6:2:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v14,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 20 "expand calls"
aux a6 nameoff "p+0" a3 0
aux a7 nameoff "n+0" a4 0
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
v v14 SB t4 0 - p0:0:0:0:0 0 -
v v10 SP t4 0 - p0:0:0:0:0 3 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v6 OffPtr t23 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t35 0 a5 p49:1045:2:0:0 0 v10,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 0=v9,v6
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
v v14 SB t4 0 - p0:0:0:0:0 0 -
v v10 SP t4 0 - p0:0:0:0:0 3 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v6 OffPtr t23 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t35 0 a5 p49:1045:2:0:0 0 v10,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 0=v9,v6
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
v v14 SB t4 0 - p0:0:0:0:0 0 -
v v10 SP t4 0 - p0:0:0:0:0 3 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v6 OffPtr t23 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t35 0 a5 p49:1045:2:0:0 0 v10,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 0=v9,v6
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
v v14 SB t4 0 - p0:0:0:0:0 0 -
v v10 SP t4 0 - p0:0:0:0:0 3 -
v v9 OffPtr t35 0 - p0:0:0:0:0 0 v10
v v6 OffPtr t23 0 - p0:0:0:0:0 0 v10
v v5 LocalAddr t35 0 a5 p49:1045:2:0:0 0 v10,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts 0=v9,v6
freev v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 Sub64 t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 49:1045:1045
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v5,v6,v9,v10,v14,v4,v3,v2
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.subtractb}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t4 a4 1 8
abiparam out 0 t2 a5 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v10,v14
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
regalloc 16 v7:R0,v8:R1,v11:R0,v12:R0,v13:R0,v15:[]
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v10,v14
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
regalloc 16 v7:R0,v8:R1,v11:R0,v12:R0,v13:R0,v15:[]
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 15 1
b b1 Ret p49:1045:55:1:0 0 0 - v15 - -
v v7 ArgIntReg t2 0 a6 p49:1045:55:1:0 1 -
v v8 ArgIntReg t4 1 a7 p49:1045:55:1:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v11 Convert t4 0 - p49:1045:54:1:0 1 v7,v1
v v12 ARM64SUB t4 0 - p49:1045:59:0:0 1 v11,v8
v v13 Convert t29 0 - p49:1045:59:0:0 1 v12,v1
v v15 MakeResult t36 0 - p49:1045:2:0:0 1 v13,v1
names s1,s2
named s1 v7
named s2 v8
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2
consts -
freev v2,v3,v4,v5,v6,v9,v10,v14
freeb -
cache postorder b1
cache idom b1:-
cache sdom b1:-:-:-:2:5
cache loopnest 2 0 - -
cache auxmap a3:1,a4:2,-:3,a6:4,a7:5
cache linestarts 49:1045:1045
fstate scheduled,laidout
regalloc 16 v7:R0,v8:R1,v11:R0,v12:R0,v13:R0,v15:[]
dcllen 3
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t23,t26,t27,t28,t29
typelink t2=t19,t3=t10,t26=t35,t30=t34
typeorder t6,t3=t10,t7,t11,t8,t12,t9,t13,t14,t17,t4,t27,t28,t15,t16,t5,t2=t19,t20,t21,t22,t23,t24,t25,t26=t35,t1,t18,t29,t30,t32,t31,t33,t34,t36
eof
"#

/-- `std/std/runtime/subtractb,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "subtractb" 1
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
type t1 8 8 8 1 01 "*byte"
name n1 "p" PPARAM t1 1 "runtime.p" 0 a3
type t2 8 8 0 0 - "uintptr"
name n2 "n" PPARAM t2 1 "runtime.n" 0 a4
name n3 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a5
in n1 0 used
in n2 8 used
in n3 0 outregs
out n1 0 used
out n2 8 used
opt n3 0 outregs
stack 0 0 8
end
genin
posbase p49 "runtime/mbitmap.go" 1 1 -1 48 "runtime/mbitmap.go" "runtime/mbitmap.go" 1 1
sym y1 "runtime.subtractb" 1
curfn p49:1041:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 1041 201084
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.subtractb.arginfo1" 0
sym y5 "runtime.subtractb.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p49:1041:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p49:1041:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p49:1041:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p49:1041:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p49:1041:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p49:1041:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p49:1045:54:1:0
p 7 7 0 0 0 - SUB 0 REG/8193/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p49:1045:54:1:0
p 8 8 0 0 0 - RET 0 _ 0 - _ 0 0 p49:1045:55:2:0
p 9 9 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 1041 201084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgloc 0 1:-10000:1:12:50
dbgloc 1 1:-10000:-1:-30000:51
dbgregout n3
dbgpc 1:12:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p49:1041:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p49:1041:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p49:1041:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p49:1041:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p49:1041:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p49:1041:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p49:1045:54:1:0
p 7 0 0 0 23 - SUB 0 REG/8193/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p49:1045:54:1:0
p 8 4 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p49:1045:55:2:0
fn y1 16 0 0 0 1041 2010cc
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
funcaux y2 y3 - - y4 y5 -
text 16 0 000001cbc0035fd60000000000000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 48
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080808ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010400 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040400 0
data y10 SRODATA 3 1 28000 020400 0
data y11 SRODATA 3 1 28000 620400 0
data y12 SRODATA 4 1 28000 ac100400 0
data y13 SRODATA 3 1 28000 000400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.runtime.subtractb$abstract" 0
sym y18 "" 0
sym y19 "go:info.*uint8" 0
sym y20 "go:info.uintptr" 0
sym y21 "type:*uint8" 0
dwfn y14 y15 y16 y17 y18 "runtime.subtractb" 48:1041 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y17 n1,n2,n3
dwname n1 1 1 0 0 0 0 0 0 - - "*uint8" 0 0 1 p49:1041:16:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "uintptr" 0 0 1 p49:1041:25:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "*uint8" 0 0 1 p49:1041:36:0:0
var 0 0 "p" 5 1 0 0 0 8 y19 "runtime/mbitmap.go" 1041 16 0 0 1 0 v0
var 1 0 "n" 5 1 0 0 0 16 y20 "runtime/mbitmap.go" 1041 25 0 1 1 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y19 "runtime/mbitmap.go" 1041 36 0 2 0 0 -
scope 0 0 - 0,1,2
dieref y14 3 y17 0
dieref y14 5 y17 1
dieoff y17 0:23,1:31
data y14 SDWARFFCN 42 0 0 0600000000000010019c2900000000000000002900000000000000002e7e723000019108000000000000 8
reloc 0 0 R_USETYPE 0 y21
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
reloc 20 4 R_DWARFSECREF 0 y17
reloc 24 4 R_DWARFSECREF 9 y15
reloc 36 4 R_DWARFSECREF 0 y19
data y15 SDWARFLOC 18 0 0 010000040004015000010000040010015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 24 0 0 00090200000000000000000431038f08140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 40 0 1 0572756e74696d652e73756274726163746200019108012270000000000000226e00000000000000 2
reloc 27 4 R_DWARFSECREF 0 y19
reloc 35 4 R_DWARFSECREF 0 y20
end
eof
"#

/-- The loaded `subtractb` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG12` gives (block `b1`: `v12`'s `SUB` after the no-op Progs from 5). -/
def tab : PcTab := [(1, [5, 5, 5, 5, 5, 8, 8, 8])]

/-- The class table `checkG12` gives: nothing known at the entry `b1`. -/
def kt : KTab := [(1, KMap.bot)]

def blk1 : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- `ι`: the nil block, the globals at their symbols, and the heap object `heap 1` at its Phase 1
address `2^41`. -/
def ι : Blk → Option (BitVec 64)
  | .nil => some 0
  | .global _ => some GenG2.symA
  | .heap 1 => some 0x20000000000
  | _ => none

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` and the PC table of `checkG12`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `p`: 16 bytes into the heap object `heap 1`. -/
def pP : Ptr := ⟨.heap 1, 16⟩

/-- The `runLoc` state after the entry values: `p` in `R0`, every other register `poison`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pP else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v11`: `X0` the address of `p` under `ι`, the activation's `g` and `FP`,
the PC of `v11`, the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x20000000010 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 3, mem := fun _ => 0 }

/-- `R0` holds the integer `2^41 + 16`. -/
def r0Is (s : LocState) : Bool :=
  match (s.regs[0]? : Option Val) with
  | some (Val.int Width.w64 x) => x == 0x20000000010
  | _ => false

theorem r0Is_spec {s : LocState} (h : r0Is s = true) : s.regs[0]? = some (.i64 0x20000000010) := by
  unfold r0Is at h
  split at h
  · rename_i x hx
    simp only [beq_iff_eq] at h
    rw [hx, h]
  · cases h

/-- What compiled evaluation checks on `subtractb`: `checkG12` accepts it with `tab` and `kt` and
`checkG11` does not; it accesses no frame variable and has no home slot; `b1` holds `v11` at
index 3, a `Convert`, and `R0` has class 64 before it; `stepLoc` runs `v11` from `s0` and `R0`
then holds the integer `2^41 + 16`. -/
def gFacts : Bool :=
  (checkG12 lc ps bs g).toOption == some (tab, kt) && (checkG11 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 1 && (lc.ctx.f.block? 1).isSome &&
    (lc.ctx.f.value? 11).isSome && blk1.values[3]? == some 11 && (val 11).op == .Convert &&
    (kAt lc kt 1 blk1 3).get 0 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) r0Is

theorem g12_facts : gFacts = true := by
  native_decide

/-- The facts of `g12_facts` as hypotheses. -/
theorem facts :
    checkG12 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 1 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 1 = some blk1 ∧ lc.ctx.f.value? 11 = some (val 11) ∧
      blk1.values[3]? = some 11 ∧ (val 11).op = .Convert ∧ (kAt lc kt 1 blk1 3).get 0 = some 64 ∧
      (GenG1.okThen (stepLoc GenG2.env lc s0 (val 11)) r0Is) = true := by
  have hf := g12_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm1⟩, hb1s⟩, hv11⟩, hi3⟩, hop⟩, hk0⟩, hrun⟩ := hf
  refine ⟨?_, hav, hsl, hm1, ?_, ?_, hi3, hop, hk0, hrun⟩
  · revert hres; cases checkG12 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb1s
    simp [blk1, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv11
    simp [val, hv]

theorem addrAgree : AddrAgree ι := by
  intro b n a hb ha _
  cases b with
  | nil => simp [ι] at ha; simp [Blk.base?] at hb; subst hb; subst ha; rfl
  | heap k =>
    simp only [Blk.base?, Option.some.injEq] at hb
    subst hb
    unfold ι at ha
    split at ha <;> first | cases ha | skip
    all_goals simp_all
  | _ => simp [ι] at ha <;> simp [Blk.base?] at hb

theorem g12Env (hc : checkG12 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG12_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG12_spec hc
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
  icalls := fun h => by cases h

theorem locMatch0 : LocMatch E s0 1 3 m0 where
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
          exact ⟨0x20000000000, rfl, by decide⟩
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

theorem g12Inv0 (h0 : (kAt lc kt 1 blk1 3).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 1 blk1 3) s0 where
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

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G12 on `subtractb`**: from the state after the entry values with `p` (`pP`) in `R0`,
`g12_value` runs the conversion `v11` with no code and gives the state before `v12`, `R0` holding
the integer `2^41 + 16` related to `X0`, under an activation that extends `E` and is a
`G10Env`. -/
theorem genG12_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 11) = .ok s1 ∧
      s1.regs[0]? = some (.i64 0x20000000010) ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 1 4 m1 ∧ G3Inv E' lc (kAt lc kt 1 blk1 4) s1 := by
  obtain ⟨hc, hav, hsl, hm1, hb, hv11, hi3, hop, hk0, hrun⟩ := facts
  obtain ⟨s1, hs1, hr0⟩ := GenG1.okThen_spec hrun
  have hE := g12Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .Convert → (val 11).op ≠ o := fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g12_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm1 hb hi3 hv11 (by rw [hop]; rfl) locMatch0 (g12Inv0 hk0)
    (g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; simp [loadOp?, narrowLoad?])
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _)
    (fun h => absurd h (hne _ (by decide))) (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  exact ⟨s1, E1, m1, hs1, r0Is_spec hr0, hx1, hE1, hp1, hm1', hinv1⟩

end GoFV.Proof.Witness.GenG12
