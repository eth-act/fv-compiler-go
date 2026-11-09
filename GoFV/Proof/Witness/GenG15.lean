import GoFV.Proof.Gen.G15
import GoFV.Proof.Witness.GenG14

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G15 of the genssa validator on `(*T3).M` of `test/recover`

`test/recover/main/(*T3).M,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain` (file names `%28%2AT3%29.M,1.*`), embedded verbatim
(`fSsa`, `fProg`): the pointer-receiver wrapper of `func (T3) M()`, `T3` an empty struct, which
calls `main.T3.M` with its zero-sized receiver, which Go's ABI assigns to the stack (at offset 8,
no byte), and panics through `runtime.panicwrap` on a nil receiver.

`checkG14` rejects it (`stack argument`); `checkG15` accepts it with the PC table `tab` and the
class table `kt`. Block `b2`: `v15 = CALLstatic {main.T3.M} v1`, `v16 = SelectN [0] v15`,
`v17 = MakeResult v16`; `Ret`. Its Progs: `CALL main.T3.M(SB)`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g15_facts`),
`callRegs` rejects the call's ABI and `callRegsZ` gives no register argument and no result, and
`stepLoc` runs `v15` (every callee returning at once, `GenG2.env`) from the state before it with
the receiver in `R0` and the memory `GenG2.mem0`. On a framed activation with `G10Env` (as
`GenG14`'s) and a hook that returns at once (`GenG2.H0`, which satisfies `CallOKZ`: `callOKZ0`),
`g15_value` runs `CALL main.T3.M(SB)` and the hook, and gives the state before `v16`
(`genG15_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG15

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/recover/main/(*T3).M,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "(*T3).M" 1 0 0
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
type t3 STRUCT 0 1 0 comparable,named "T3" "main.T3" 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*T3" "*main.T3" t3
type t1 FUNC 8 8 8 hasptr,direct "method(*T3) func()" "method(*main.T3) func()" 1 0 0
field 0 "" t2 ? 0
aux a2 sym "main.(*T3).M" "main.(*T3).M" 1 - 0 - - - - 0
posbase p2 "./recover.go" 1 1 -1
aux a3 name "~p0" "~p0" PPARAM t2 0 1 used p2:402:7:0:0
aux a1 call "AuxCall{main.(*T3).M}" a2 1 1 0 8 8 1 0
abiparam in 0 t2 a3 0 0
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
type t15 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t16 UINT 8 8 0 comparable,named "uint" "uint"
type t17 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t18 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t9
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t7
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t11
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t17
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t14
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t19
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
posbase p1 "<autogenerated>" 1 1 -1
type t35 PTR 8 8 8 hasptr,direct,comparable "**T3" "**main.T3" t2
aux a5 sym "main.T3.M" "main.T3.M" 1 - 0 - - - - 0
aux a4 call "AuxCall{main.T3.M}" a5 1 1 0 8 0 0 0
abiparam in 0 t3 - - 8
aux a7 sym "runtime.panicwrap" "runtime.panicwrap" 1 - 0 - - - - 0
aux a6 call "AuxCall{runtime.panicwrap}" a7 1 0 0 8 0 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 17 3
typs Bool=t4,Int8=t5,Int16=t6,Int32=t7,Int64=t8,UInt8=t9,UInt16=t10,UInt32=t11,UInt64=t12,Int=t13,Float32=t14,Float64=t15,UInt=t16,Uintptr=t17,String=t18,BytePtr=t19,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:0:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v11 Copy t2 0 - p1:1:0:2:0 1 v5
v v12 Copy t30 0 - p1:1:0:2:0 3 v1
v v13 NilCheck t2 0 - p1:1:0:0:0 1 v11,v12
v v14 Load t3 0 - p1:1:0:0:0 1 v13,v12
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v12
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v8 Copy t30 0 - p1:1:0:2:0 1 v1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v8
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5,v11
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v11 Copy t2 0 - p1:1:0:2:0 1 v5
v v12 Copy t30 0 - p1:1:0:2:0 3 v1
v v13 NilCheck t2 0 - p1:1:0:0:0 1 v11,v12
v v14 Load t3 0 - p1:1:0:0:0 1 v13,v12
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v12
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v8 Copy t30 0 - p1:1:0:2:0 1 v1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v8
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5,v11
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t17 0 - p0:0:0:0:0 1 -
v v3 SB t17 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Arg t2 0 a3 p1:1:0:2:0 3 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v11 Copy t2 0 - p1:1:0:2:0 0 v5
v v12 Copy t30 0 - p1:1:0:2:0 0 v1
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v8 Copy t30 0 - p1:1:0:2:0 0 v1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5,v5
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev -
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev v8,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev v8,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev v8,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v7 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v6 ConstNil t2 0 - p0:0:0:0:0 1 -
v v7 EqPtr t4 0 - p1:1:0:1:0 1 v5,v6
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:1
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:0
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 3344556677=v6
freev v8,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache linestarts 1:1:1
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 3 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 NilCheck t2 0 - p1:1:0:0:0 0 v5,v1
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v14 Empty t3 0 - p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 Copy t2 0 - p1:1:0:0:0 0 v5
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 2 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v13 Copy t2 0 - p1:1:0:0:0 0 v5
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 Arg t2 0 a3 p1:1:0:2:0 1 -
v v14 Empty t3 0 - p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticLECall t34 0 a4 p1:1:0:0:0 1 v14,v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticLECall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v13,v7,v6,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 20 "expand calls"
aux a8 nameoff "~p0+0" a3 0
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v14 OpInvalid t3 0 - p1:1:0:0:0 0 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v13 SB t17 0 - p0:0:0:0:0 0 -
v v7 SP t17 0 - p0:0:0:0:0 1 -
v v6 OffPtr t35 0 - p0:0:0:0:0 0 v7
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v6
freev v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v13 SB t17 0 - p0:0:0:0:0 0 -
v v7 SP t17 0 - p0:0:0:0:0 1 -
v v6 OffPtr t35 0 - p0:0:0:0:0 0 v7
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v6
freev v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v13 SB t17 0 - p0:0:0:0:0 0 -
v v7 SP t17 0 - p0:0:0:0:0 1 -
v v6 OffPtr t35 0 - p0:0:0:0:0 0 v7
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v6
freev v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
v v13 SB t17 0 - p0:0:0:0:0 0 -
v v7 SP t17 0 - p0:0:0:0:0 1 -
v v6 OffPtr t35 0 - p0:0:0:0:0 0 v7
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts 0=v6
freev v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 17 3
b b1 If p1:1:0:0:0 0 0 - v8 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v8 IsNonNil t4 0 - p1:1:0:1:0 1 v5
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 StaticCall t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 StaticCall t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2
cache linestarts 1:1:1
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 0 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v6,v8,v7,v13,v14,v12,v11,v4,v3,v2
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v11,v12,v13,v14
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v11,v12,v13,v14
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 17 3
b b1 ARM64NZ p1:1:0:1:0 1 0 - v5 b2:0,b3:0 -
v v5 ArgIntReg t2 0 a8 p1:1:0:0:0 1 -
v v1 InitMem t30 0 - p0:0:0:0:0 2 -
b b2 Ret p1:1:0:0:0 0 0 - v17 - b1:0
v v15 ARM64CALLstatic t34 0 a4 p1:1:0:0:0 1 v1
v v16 SelectN t30 0 - p1:1:0:0:0 1 v15
v v17 MakeResult t34 0 - p1:1:0:0:0 1 v16
b b3 Exit p1:1:0:0:0 0 0 - v10 - b1:1
v v9 ARM64CALLstatic t34 0 a6 p1:1:0:0:0 1 v1
v v10 SelectN t30 0 - p1:1:0:0:0 1 v9
names s1
named s1 v5
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v3,v4,v6,v7,v8,v11,v12,v13,v14
freeb -
cache postorder b3,b2,b1
cache idom b1:-,b2:b1,b3:b1
cache sdom b1:-:b2:-:2:17,b2:b1:-:b3:5:8,b3:b1:-:-:11:14
cache loopnest 4 0 - -
cache auxmap a3:1,-:2,a8:3
cache linestarts 1:1:1
fstate scheduled,laidout
regalloc 6 v5:R0
dcllen 2
end
frontend
end
ptrcache t3,t6,t7,t8,t9,t11,t13,t14,t15,t17,t18,t19,t26,t29
typelink t30=t34
typeorder t5,t9,t6,t10,t7,t11,t8,t12,t13,t16,t17,t27,t28,t14,t15,t4,t19,t20,t21,t22,t23,t24,t25,t26,t35,t2,t1,t3,t18,t29,t30,t32,t31,t33,t34
eof
"#

/-- `test/recover/main/(*T3).M,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "(*T3).M" 1
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
type t1 8 8 8 1 01 "*T3"
name n1 "~p0" PPARAM t1 1 "main.~p0" 0 a3
type t2 0 1 0 0 - "T3"
name n2 ".autotmp_1" PAUTO t2 3 "main..autotmp_1" 0 -
in n1 0 used
in n2 0 used,autotmp
out n1 0 used
opt n2 0 autotmp
stack 0 0 8
end
genin
posbase p1 "<autogenerated>" 1 1 -1 0 "<autogenerated>" "<autogenerated>" 1 1
sym y1 "main.(*T3).M" 1
curfn p1:1:0:0:0 0 0
regargs 8192:0:t1
text y1 0 0 23 0 1 200091
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "main.(*T3).M.arginfo1" 0
sym y5 "main.(*T3).M.argliveinfo" 0
sym y6 "main.T3.M" 1
sym y7 "runtime.panicwrap" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p1:1:0:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p1:1:0:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p1:1:0:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p1:1:0:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p1:1:0:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 6 6 0 0 0 - CBZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@10 0 0 p1:1:0:1:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p1:1:0:2:0
p 8 8 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p1:1:0:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p1:1:0:0:0
p 10 10 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p1:1:0:2:0
p 11 11 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p1:1:0:0:0
p 12 12 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgregout -
dbgpc -
end
asm
sym y8 "runtime.morestack_noctxt" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p1:1:0:0:0
p 13 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 14 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 15 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 16 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@25 0 0 p1:1:0:0:0
p 17 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 18 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p1:1:0:0:1
p 19 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p1:1:0:0:0
p 20 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p1:1:0:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p1:1:0:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p1:1:0:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p1:1:0:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 6 24 0 0 85 - CBZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/10/-/@10 0 0 p1:1:0:1:0
p 7 28 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p1:1:0:2:0
p 8 28 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p1:1:0:2:0
p 9 32 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 21 36 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 22 40 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p1:1:0:0:0
p 10 44 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p1:1:0:2:0
p 11 48 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 23 52 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p1:1:0:0:0
p 24 52 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 25 52 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p1:1:0:0:0
p 26 52 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p1:1:0:0:0
p 27 56 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 28 60 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y8/- 0 0 p1:1:0:0:0
p 29 64 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p1:1:0:0:0
p 30 64 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p1:1:0:0:0
p 31 68 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@13 0 0 p1:1:0:0:0
fn y1 8 8 23 0 1 200091
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y3 - - y4 y5 -
text 80 0 900b40f9ff6330eb69010054fe0f1ff8fd831ff8fd2300d1a00000b400000094fd835ff8fe0741f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9efffff170000000000000000 3
reloc 28 4 R_CALLARM64 0 y6
reloc 44 4 R_CALLARM64 0 y7
reloc 60 4 R_CALLARM64 0 y8
pcln y13 y14 y15 y16 y9,y10,y11,y12 y2,y3,_,_,_,y4,y5
usedfiles 0
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 3 1 8000 0008ff 0
data y5 SDATA 2 1 8000 0000 0
data y9 SRODATA 11 1 28000 00010102020a0103020400 0
data y10 SRODATA 7 1 28000 00070406030700 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 5 1 28000 0006040e00 0
data y13 SRODATA 11 1 28000 020420061f0120021f0700 0
data y14 SRODATA 3 1 28000 021400 0
data y15 SRODATA 3 1 28000 041400 0
data y16 SRODATA 3 1 28000 001400 0
end
dwarf
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
posbase p2 "./recover.go" 1 1 -1 1 "./recover.go" "./recover.go" 1 1
sym y21 "go:info.*main.T3" 0
sym y22 "go:info.main.T3" 0
sym y23 "type:main.T3" 0
dwfn y17 y18 y19 - y20 "main.(*T3).M" 0:1 1 1 1 165
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1
dwname n1 1 1 0 0 0 0 0 0 - - "*main.T3" 0 0 1 p2:402:7:0:0
dwname n2 1 0 1 0 0 0 0 0 - - "main.T3" 0 0 1 p1:1:0:0:0
var 0 0 "~p0" 5 0 0 0 0 8 y21 "./recover.go" 402 7 0 0 0 0 -
var 1 0 ".autotmp_1" 52 0 0 0 0 0 y22 "<autogenerated>" 1 0 0 1 0 0 -
scope 0 0 - 0,1
data y17 SDWARFFCN 55 0 0 046d61696e2e282a5433292e4d00000050019c012e7e70300000920300000000029108282e6175746f746d705f31000100000000019c00 4
reloc 0 0 R_USETYPE 0 y23
reloc 14 2 R_DWTXTADDR_U2 0 y1
reloc 28 4 R_DWARFSECREF 0 y21
reloc 48 4 R_DWARFSECREF 0 y22
data y18 SDWARFLOC 0 0 0 - 0
data y19 SDWARFRANGE 0 0 0 - 0
data y20 SDWARFLINES 26 0 0 00090200000000000000000a8706af0637068706370220000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded `(*T3).M` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG15` gives (`b1`: `CBZ`; `b2`: `v15`'s `CALL` after the `PCDATA` at 7,
then `RET`; `b3`: `v9`'s `CALL`, then `HINT`). -/
def tab : PcTab := [(1, [5, 5, 5]), (2, [7, 9, 9, 9]), (3, [10, 11, 11])]

/-- The class table `checkG15` gives: `R0` of class 64 in `b2` and `b3`. -/
def kt : KTab := (match checkG15 lc ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- `ι`: as `GenG12.ι`, the heap object `heap 1` at `2^41`. -/
def ι : Blk → Option (BitVec 64) := GenG12.ι

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` and the PC table of `checkG15`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The receiver: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The `runLoc` state before `v15`: the receiver in `R0`, every other register `poison`, the
memory `GenG2.mem0`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 0 then .ptr pB else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v15`: `X0` the receiver's address `2^41`, the activation's `g` and `FP`,
the PC of `v15`, the memory 0. -/
def m0 : MState :=
  { x := fun k => if k = 0 then 0x20000000000 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 0, mem := fun _ => 0 }

/-- The call `v` has an ABI that `callRegs` rejects and on which `callRegsZ` gives no result. -/
def zeroCall (v : Value) : Bool :=
  match callOf? lc.ctx.tabs v.aux with
  | some (_, _, cabi) =>
    (callRegs cabi).toOption.isNone &&
      match callRegsZ lc.ctx.tabs cabi with
      | .ok (_, outs) => outs.isEmpty
      | .error _ => false
  | none => false

/-- What compiled evaluation checks on `(*T3).M`: `checkG15` accepts it with `tab` and `kt` and
`checkG14` does not; it accesses no frame variable and has no home slot; `b2` holds `v15` at
index 0, a static call that `callRegs` rejects and `callRegsZ` accepts with no result, `R0` has
class 64 before it; `stepLoc` runs it from `s0` to the memory `GenG2.mem0`. -/
def gFacts : Bool :=
  (checkG15 lc ps bs g).toOption == some (tab, kt) && (checkG14 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 15).isSome && blk2.values[0]? == some 15 &&
    (val 15).op == .ARM64CALLstatic && zeroCall (val 15) &&
    (kAt lc kt 2 blk2 0).get 0 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 15)) fun s => GenG2.memIs0 s.mem

theorem g15_facts : gFacts = true := by
  native_decide

/-- The facts of `g15_facts` as hypotheses. -/
theorem facts :
    checkG15 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 2 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 2 = some blk2 ∧ lc.ctx.f.value? 15 = some (val 15) ∧
      blk2.values[0]? = some 15 ∧ (val 15).op = .ARM64CALLstatic ∧ zeroCall (val 15) = true ∧
      (kAt lc kt 2 blk2 0).get 0 = some 64 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 15)) (fun s => GenG2.memIs0 s.mem) = true := by
  have hf := g15_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv15⟩, hi0⟩, hop⟩, hz⟩, hk0⟩, hrun⟩ := hf
  refine ⟨?_, hav, hsl, hm2, ?_, ?_, hi0, hop, hz, hk0, hrun⟩
  · revert hres; cases checkG15 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv15
    simp [val, hv]

theorem g15Env (hc : checkG15 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG15_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG15_spec hc
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

theorem locMatch0 : LocMatch E s0 2 0 m0 where
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

theorem g15Inv0 (h0 : (kAt lc kt 2 blk2 0).get 0 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk2 0) s0 where
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

/-- The callee contract `CallOKZ` of a callee that returns at once with the memory `mem0` and no
results, at a call `zeroCall` accepts. -/
theorem callOKZ0 {E' : MatchEnv} (hA : AddrAgree E'.ι) (hnil : E'.ι .nil = some 0)
    {s s' : LocState} {v : Value} {m : MState} (hmem : GenG2.memIs0 s'.mem = true)
    (hz : zeroCall v = true) : CallOKZ GenG2.H0 E' g L lc s s' v m := by
  intro _ name abi cabi ins outs hc hcr y args mm m₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hout : outs = [] := by
    simp only [zeroCall, hc, hcr, Bool.and_eq_true, List.isEmpty_iff] at hz
    exact hz.2
  have hm' : s'.mem = .mem GenG2.mem0 := by
    unfold GenG2.memIs0 at hmem
    split at hmem
    · rename_i mm' he
      rw [he, of_decide_eq_true hmem]
    · cases hmem
  subst hout
  exact ⟨E'.ι, { m₁ with pc := m₁.x 30 }, GenG2.mem0, rfl, fun _ _ h => h, hA, rfl, rfl, rfl, rfl,
    fun _ _ => rfl, hm', GenG2.memInj0 hnil _, GenG2.keys0, GenG2.sep0, fun r hr => by cases hr⟩

/-- `callRegs` rejects the ABI of a call `zeroCall` accepts: `CallOK` holds vacuously. -/
theorem callOK15 {E' : MatchEnv} {s s' : LocState} {v : Value} {m : MState}
    (hz : zeroCall v = true) : CallOK GenG2.H0 E' g L lc s s' v m := by
  intro _ name abi cabi ins outs y args mm m₁ hc hcr
  unfold zeroCall at hz
  rw [hc] at hz
  dsimp only at hz
  rw [hcr] at hz
  simp [Except.toOption] at hz

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G15 on `(*T3).M`**: from the state before `v15` with the receiver in `R0`, `g15_value` runs
the static call `v15` of `main.T3.M`, whose zero-sized receiver Go's ABI passes on the stack,
`CALL main.T3.M(SB)` and a callee that returns at once, and gives the state before `v16` with the
memory `GenG2.mem0`, under an activation that extends `E` and is a `G10Env`. -/
theorem genG15_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 15) = .ok s1 ∧ s1.mem = .mem GenG2.mem0 ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 2 1 m1 ∧ G3Inv E' lc (kAt lc kt 2 blk2 1) s1 := by
  obtain ⟨hc, hav, hsl, hm2, hb, hv15, hi0, hop, hz, hk0, hrun⟩ := facts
  obtain ⟨s1, hs1, hmem⟩ := GenG1.okThen_spec hrun
  have hE := g15Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64CALLstatic → (val 15).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g15_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm2 hb hi0 hv15 (by rw [hop]; rfl) locMatch0 (g15Inv0 hk0)
    ⟨⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; simp [loadOp?, narrowLoad?])
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _,
      fun h => absurd h (hne _ (by decide))⟩,
      fun _ _ _ _ h => by rw [hop] at h; cases h⟩
    (callOK15 hz) (callOKZ0 GenG12.addrAgree rfl hmem hz) (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hm' : s1.mem = .mem GenG2.mem0 := by
    unfold GenG2.memIs0 at hmem
    split at hmem
    · rename_i mm' he
      rw [he, of_decide_eq_true hmem]
    · cases hmem
  exact ⟨s1, E1, m1, hs1, hm', hx1, hE1, hp1, hm1', hinv1⟩

end GoFV.Proof.Witness.GenG15
