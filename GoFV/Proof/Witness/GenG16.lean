import GoFV.Proof.Gen.G16
import GoFV.Proof.Witness.GenG15

/-!
# Non-vacuity witness: slice G16 of the genssa validator on `spanSetSpinePointer.lookup`

`std/std/runtime/spanSetSpinePointer.lookup,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`):
`spanSetSpinePointer.lookup` (`runtime/mspanset.go`),
`return (*atomic.Pointer[spanSetBlock])(add(s.p, goarch.PtrSize*idx))`.

`checkG15` rejects it (`v16 = ADDshiftLL`); `checkG16` accepts it with the PC table `tab` and
the class table `kt`. Block `b2`: `v8 = ArgIntReg` (`idx`, `R1`), `v18 = ArgIntReg` (`s.p`,
`R0`), `v1 = InitMem`, `v16 = ADDshiftLL [3] v18 v8` (`R0`), `v13 = InlMark`,
`v20 = MakeResult v16 v1`; `Ret`. Its Progs: `ADD R1<<3, R0, R0`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g16_facts`),
`stepLoc` runs `v16` from a state with `s.p` the start of the heap object `heap 1` in `R0` and
the index 2 in `R1`, and `R0` then holds the integer `2^41 + 16`, the address of offset 16 of
`heap 1`. On a framed activation with `G10Env` (as `GenG12`'s, `heap 1` injected at `2^41`),
`g16_value` runs `ADD R1<<3, R0, R0` and gives the state before `v13`, `R0` related to `X0`, which
then holds `2^41 + 16` (`genG16_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG16

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/spanSetSpinePointer.lookup,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "spanSetSpinePointer.lookup" 1 0 0
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
type t3 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t2 STRUCT 8 8 8 hasptr,direct,comparable,named "spanSetSpinePointer" "runtime.spanSetSpinePointer" 1
field 0 "p" t3 0 0
type t4 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t8 STRUCT 0 1 0 comparable,named "atomic.noCopy" "internal/runtime/atomic.noCopy" 0
type t7 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.UnsafePointer" "internal/runtime/atomic.UnsafePointer" 2
field 0 "noCopy" t8 0 0
field 1 "value" t3 0 0
type t6 STRUCT 8 8 8 hasptr,direct,comparable,named "atomic.Pointer[runtime.spanSetBlock]" "internal/runtime/atomic.Pointer[runtime.spanSetBlock]" 1
field 0 "u" t7 0 0
type t5 PTR 8 8 8 hasptr,direct,comparable "*atomic.Pointer[runtime.spanSetBlock]" "*internal/runtime/atomic.Pointer[runtime.spanSetBlock]" t6
type t1 FUNC 8 8 8 hasptr,direct "method(spanSetSpinePointer) func(uintptr) *atomic.Pointer[runtime.spanSetBlock]" "method(runtime.spanSetSpinePointer) func(uintptr) *internal/runtime/atomic.Pointer[runtime.spanSetBlock]" 1 1 1
field 0 "s" t2 ? 0
field 1 "idx" t4 ? 0
field 2 "" t5 ? 0
aux a2 sym "runtime.spanSetSpinePointer.lookup" "runtime.spanSetSpinePointer.lookup" 1 - 0 - - - - 0
posbase p99 "runtime/mspanset.go" 1 1 -1
aux a3 name "s" "s" PPARAM t2 0 1 used p99:320:7:0:0
aux a4 name "idx" "idx" PPARAM t4 8 1 used p99:320:37:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t5 0 1 - p99:320:50:0:0
aux a1 call "AuxCall{runtime.spanSetSpinePointer.lookup}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t4 a4 1 8
abiparam out 0 t5 a5 0 -1
type t9 BOOL 1 1 0 comparable,named "bool" "bool"
type t10 INT8 1 1 0 comparable,named "int8" "int8"
type t11 INT16 2 2 0 comparable,named "int16" "int16"
type t12 INT32 4 4 0 comparable,named "int32" "int32"
type t13 INT64 8 8 0 comparable,named "int64" "int64"
type t14 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t15 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t16 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t17 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t18 INT 8 8 0 comparable,named "int" "int"
type t19 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t20 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t21 UINT 8 8 0 comparable,named "uint" "uint"
type t22 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t23 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t12
type t25 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t18
type t27 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t4
type t28 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t19
type t29 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t20
type t30 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t23
type t31 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t32 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t33 SSA ? ? ? - "mem" ""
type t34 SSA ? ? ? - "flags" ""
type t35 SSA ? ? ? - "void" ""
type t36 SSA 16 8 ? - "int128" ""
type t37 RESULTS ? ? ? - "mem" "" 1 t33
type t38 PTR 8 8 8 hasptr,direct,comparable "*spanSetSpinePointer" "*runtime.spanSetSpinePointer" t2
type t39 PTR 8 8 8 hasptr,direct,comparable "**atomic.Pointer[runtime.spanSetBlock]" "**internal/runtime/atomic.Pointer[runtime.spanSetBlock]" t5
posbase p574 "runtime/stubs.go" 1 1 301
type t40 RESULTS ? ? ? - "*atomic.Pointer[runtime.spanSetBlock],mem" "" 2 t5,t33
slot s1 a3 t2 0 - 0
slot s2 a4 t4 0 - 0
aux a6 name "p" "p" PAUTO t3 0 1 used p574:24:10:0:0
slot s3 a6 t3 0 - 0
aux a7 name "x" "x" PAUTO t4 0 1 used p574:24:28:0:0
slot s4 a7 t4 0 - 0
aux a8 name "~r0" "~r0" PAUTO t3 0 1 - p574:24:39:0:0
slot s5 a8 t3 0 - 0
f b1 t1 a1 20 2
typs Bool=t9,Int8=t10,Int16=t11,Int32=t12,Int64=t13,UInt8=t14,UInt16=t15,UInt32=t16,UInt64=t17,Int=t18,Float32=t19,Float64=t20,UInt=t21,Uintptr=t4,String=t22,BytePtr=t23,Int32Ptr=t24,UInt32Ptr=t25,IntPtr=t26,UintptrPtr=t27,Float32Ptr=t28,Float64Ptr=t29,BytePtrPtr=t30,Complex64=t31,Complex128=t32,UnsafePtr=t3,Mem=t33,Flags=t34,Void=t35,Int128=t36,ResultMem=t37
b b1 Plain p99:321:44:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 7 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t27 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t39 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v9 ConstNil t5 0 - p0:0:0:0:0 0 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:0:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v14 Convert t4 0 - p574:25:32:0:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
b b2 Ret p99:321:44:1:0 0 0 - v20 - b1:0
v v17 Copy t3 0 - p99:321:44:2:0 1 v16
v v18 Copy t5 0 - p99:321:44:2:0 1 v17
v v19 Copy t33 0 - p99:321:2:2:0 1 v1
v v20 MakeResult t40 0 - p99:321:2:0:0 1 v18,v19
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v12
named s5 v16,v17
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11,3344556677=v9
freev -
freeb -
dcllen 6
end
pass 1 "number lines"
f b1 t1 a1 20 2
b b1 Plain p99:321:44:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 7 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t27 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t39 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v9 ConstNil t5 0 - p0:0:0:0:0 0 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
b b2 Ret p99:321:44:1:0 0 0 - v20 - b1:0
v v17 Copy t3 0 - p99:321:44:2:0 1 v16
v v18 Copy t5 0 - p99:321:44:2:0 1 v17
v v19 Copy t33 0 - p99:321:2:2:0 1 v1
v v20 MakeResult t40 0 - p99:321:2:0:0 1 v18,v19
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v12
named s5 v16,v17
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11,3344556677=v9
freev -
freeb -
cache postorder b2,b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 20 2
b b1 Plain p99:321:44:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 8 -
v v2 SP t4 0 - p0:0:0:0:0 3 -
v v3 SB t4 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t38 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t27 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t39 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v9 ConstNil t5 0 - p0:0:0:0:0 0 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 3 v15,v1
b b2 Ret p99:321:44:1:0 0 0 - v20 - b1:0
v v17 Copy t3 0 - p99:321:44:2:0 0 v16
v v18 Copy t5 0 - p99:321:44:2:0 0 v16
v v19 Copy t33 0 - p99:321:2:2:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:0:0 1 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v12
named s5 v16,v16
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11,3344556677=v9
freev -
freeb -
cache postorder b2,b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 3 "early deadcode"
f b1 t1 a1 20 2
b b1 Plain p99:321:44:1:0 0 0 - - b2:0 -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
b b2 Ret p99:321:44:1:0 0 0 - v20 - b1:0
v v20 MakeResult t40 0 - p99:321:2:0:0 1 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v12
named s5 v16
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b2,b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 4 "short circuit"
f b2 t1 a1 20 2
b b1 BlockInvalid p99:321:44:1:0 0 0 - - - -
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v12
named s5 v16
splits -
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 5 "decompose user"
slot s6 a3 t3 0 - 0
f b2 t1 a1 20 2
b b1 BlockInvalid p99:321:44:1:0 0 0 - - - -
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5,s6
named s2 v8
named s3 v10
named s4 v12
named s5 v16
named s6 -
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v14 Convert t4 0 - p574:25:32:1:0 1 v10,v1
v v15 Add64 t4 0 - p574:25:35:0:0 1 v14,v12
v v16 Convert t3 0 - p574:25:35:0:0 1 v15,v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 7 "opt"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 8 "zero arg cse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 9 "opt deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 10 "generic cse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 11 "phiopt"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 12 "gcse deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 13 "nilcheckelim"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 14 "prove"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 15 "divisible"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 16 "divmod"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v11 Const64 t4 8 - p0:0:0:0:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Mul64 t4 0 - p99:321:64:1:0 1 v11,v8
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 8=v11
freev v15,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 17 "middle opt"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v11,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 18 "known bits"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v11,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 19 "early fuse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p99:320:6:2:0 1 -
v v8 Arg t4 0 a4 p99:320:6:2:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v11,v14,v19,v18,v17,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 20 "expand calls"
aux a9 nameoff "idx+0" a4 0
aux a10 nameoff "s+0" a3 0
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v7 StructMake t2 0 - p99:321:44:2:0 1 v18
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v10 StructSelect t3 0 - p99:321:46:0:0 1 v7
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v10,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v11 SB t4 0 - p0:0:0:0:0 0 -
v v14 SP t4 0 - p0:0:0:0:0 3 -
v v19 OffPtr t38 0 - p0:0:0:0:0 0 v14
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v17 OffPtr t27 0 - p0:0:0:0:0 0 v14
v v9 LocalAddr t39 0 a5 p99:321:2:1:0 0 v14,v1
names s2,s3,s4,s5
named s2 v8
named s3 v10
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v19,v17
freev v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 21 "decompose builtin"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v11 SB t4 0 - p0:0:0:0:0 0 -
v v14 SP t4 0 - p0:0:0:0:0 3 -
v v19 OffPtr t38 0 - p0:0:0:0:0 0 v14
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v17 OffPtr t27 0 - p0:0:0:0:0 0 v14
v v9 LocalAddr t39 0 a5 p99:321:2:1:0 0 v14,v1
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v19,v17
freev v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 22 "softfloat"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v11 SB t4 0 - p0:0:0:0:0 0 -
v v14 SP t4 0 - p0:0:0:0:0 3 -
v v19 OffPtr t38 0 - p0:0:0:0:0 0 v14
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v17 OffPtr t27 0 - p0:0:0:0:0 0 v14
v v9 LocalAddr t39 0 a5 p99:321:2:1:0 0 v14,v1
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v19,v17
freev v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 23 "branchelim"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 3 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v11 SB t4 0 - p0:0:0:0:0 0 -
v v14 SP t4 0 - p0:0:0:0:0 3 -
v v19 OffPtr t38 0 - p0:0:0:0:0 0 v14
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v17 OffPtr t27 0 - p0:0:0:0:0 0 v14
v v9 LocalAddr t39 0 a5 p99:321:2:1:0 0 v14,v1
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts 0=v19,v17
freev v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 24 "late opt"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 25 "dead auto elim"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 26 "sccp"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s3,s4,s5
named s2 v8
named s3 -
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 27 "generic deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 28 "late fuse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 29 "check bce"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 30 "dse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 31 "memcombine"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 32 "writebarrier"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v12 Lsh64x64 t4 1 - p99:321:64:1:0 1 v8,v15
v v13 InlMark t35 301 - p99:321:44:0:0 0 v1
v v16 AddPtr t3 0 - p574:25:35:1:0 1 v18,v12
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v15 Const64 t17 3 - p99:321:64:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 33 "lower"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 34 "addressing modes"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 35 "late lower"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 36 "pair"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s4,s5
named s2 v8
named s4 v12
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 38 "lowered cse"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 39 "elim unread autos"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 41 "lowered deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 42 "checkLower"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 43 "loop invariant"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 45 "tighten"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 46 "late deadcode"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 47 "critical"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 48 "phi tighten"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 49 "likelyadjust"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
dcllen 6
end
pass 50 "layout"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate laidout
dcllen 6
end
pass 51 "schedule"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
dcllen 6
end
pass 52 "late nilcheck"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
dcllen 6
end
pass 53 "flagalloc"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v15,v12,v9,v17,v19,v14,v11,v10,v7,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
dcllen 6
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.spanSetSpinePointer.lookup}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t4 a4 1 8
abiparam out 0 t5 a5 0 -1
callreg 0:1 - 0 -
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12,v14,v15,v17,v19
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
regalloc 21 v8:R1,v16:R0,v18:R0,v20:[]
dcllen 6
end
pass 55 "loop rotate"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12,v14,v15,v17,v19
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
regalloc 21 v8:R1,v16:R0,v18:R0,v20:[]
dcllen 6
end
pass 56 "trim"
f b2 t1 a1 20 2
b b2 Ret p99:321:44:1:0 0 0 - v20 - -
v v8 ArgIntReg t4 1 a9 p99:321:44:1:0 1 -
v v18 ArgIntReg t3 0 a10 p99:321:44:2:0 1 -
v v1 InitMem t33 0 - p0:0:0:0:0 2 -
v v16 ARM64ADDshiftLL t3 3 - p574:25:35:1:0 1 v18,v8
v v13 InlMark t35 301 - p99:321:44:1:0 0 v1
v v20 MakeResult t40 0 - p99:321:2:1:0 1 v16,v1
names s2,s5
named s2 v8
named s5 v16
namedx a3/t2/0/-/0 v7
splits s1/0/t3=s6
canon a3/t2/0/-/0=s1,a4/t4/0/-/0=s2,a6/t3/0/-/0=s3,a7/t4/0/-/0=s4,a8/t3/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v7,v9,v10,v11,v12,v14,v15,v17,v19
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 99:321:321,574:25:25
fstate scheduled,laidout
regalloc 21 v8:R1,v16:R0,v18:R0,v20:[]
dcllen 6
end
frontend
end
ptrcache t3,t4,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t27,t30,t31,t32
typelink t33=t37
typeorder t10,t14,t11,t15,t12,t16,t13,t17,t18,t21,t4,t31,t32,t19,t20,t9,t23,t24,t25,t26,t27,t28,t29,t30,t39,t38,t5,t1,t8,t7,t2,t6,t22,t3,t33,t35,t34,t36,t37,t40
eof
"#

/-- `std/std/runtime/spanSetSpinePointer.lookup,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "spanSetSpinePointer.lookup" 1
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
type t1 8 8 8 1 01 "spanSetSpinePointer"
name n1 "s" PPARAM t1 1 "runtime.s" 0 a3
type t2 8 8 0 0 - "uintptr"
name n2 "idx" PPARAM t2 1 "runtime.idx" 0 a4
type t3 8 8 8 1 01 "*atomic.Pointer[runtime.spanSetBlock]"
name n3 "~r0" PPARAMOUT t3 1 "runtime.~r0" 0 a5
type t4 8 8 8 1 01 "unsafe.Pointer"
name n4 "p" PAUTO t4 1 "runtime.p" 0 a6
name n5 "x" PAUTO t2 1 "runtime.x" 0 a7
name n6 "~r0" PAUTO t4 1 "runtime.~r0" 0 a8
in n1 0 used
in n2 8 used
in n3 0 outregs
in n4 0 used
in n5 0 used
in n6 0 -
out n1 0 used
out n2 8 used
opt n4 0 -
opt n3 0 outregs
opt n6 0 -
opt n5 0 -
stack 0 0 8
end
genin
posbase p99 "runtime/mspanset.go" 1 1 -1 96 "runtime/mspanset.go" "runtime/mspanset.go" 1 1
sym y1 "runtime.spanSetSpinePointer.lookup" 1
curfn p99:320:6:0:0 0 0
regargs 8192:0:t4,8193:8:t2
text y1 0 0 0 0 320 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.spanSetSpinePointer.lookup.arginfo1" 0
sym y5 "runtime.spanSetSpinePointer.lookup.argliveinfo" 0
sym y6 "runtime.add" 1
inl i301 - p99:321:44:0:0 y6 "add"
posbase p574 "runtime/stubs.go" 1 1 301 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p99:320:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p99:320:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p99:320:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p99:320:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p99:320:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p99:320:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p574:25:35:1:0
p 10 10 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p99:320:6:1:0
p 7 7 0 0 0 - ADD 0 SHIFT/0/0/0/NONE/0/68608/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p574:25:35:1:0
p 8 8 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p99:321:44:1:0
p 11 11 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 320 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @9 301
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n2 t2 0
dbgslot 1 n6 t4 0
dbgslot 2 n1 t4 0
dbgvar 0 n2 0
dbgvar 1 n1 2
dbgloc 0 2:-10000:-1:-30000:51
dbgloc 1 2:-10000:2:16:50
dbgregout n3
dbgpc 2:16:8
end
asm
sym y7 "" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p99:320:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p99:320:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p99:320:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p99:320:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p99:320:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p99:320:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p574:25:35:1:0
p 10 0 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p99:320:6:1:0
p 7 4 0 0 27 - ADD 0 SHIFT/0/0/0/NONE/8/68608/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p574:25:35:1:0
p 8 8 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 9 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p99:321:44:1:0
fn y1 16 0 0 0 320 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 8193 STP LDP
inlmark @9 301
funcaux y2 y3 - - y4 y5 -
text 16 0 1f2003d5000c018bc0035fd600000000 0
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y3,_,_,_,y4,y5
usedfiles 84,96
inltree 0 -1 p99:321:44:0:0 y6 "add" 8
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 7 1 8000 fe0008fd0808ff 0
data y5 SDATA 2 1 8000 0000 0
data y7 SRODATA 3 1 28000 010400 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 3 1 28000 040400 0
data y11 SRODATA 3 1 28000 020400 0
data y12 SRODATA 8 1 28000 c201011701180200 0
data y13 SRODATA 10 1 28000 820501cd0401d0040200 0
data y14 SRODATA 7 1 28000 00010201010200 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.runtime.spanSetSpinePointer.lookup$abstract" 0
sym y19 "" 0
posbase p86 "runtime/stubs.go" 1 1 -1 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
sym y20 "go:info.runtime.add$abstract" 0
sym y21 "go:info.runtime.spanSetSpinePointer" 0
sym y22 "go:info.uintptr" 0
sym y23 "go:info.*internal/runtime/atomic.Pointer[runtime.spanSetBlock]" 0
sym y24 "type:*internal/runtime/atomic.Pointer[runtime.spanSetBlock]" 0
dwfn y15 y16 y17 y18 y19 "runtime.spanSetSpinePointer.lookup" 96:320 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y18 n1,n2,n3
dwinlfn y6 y20
dwinldcl y6 "p" 0 p86:24:10:0:0
dwinldcl y6 "x" 0 p86:24:28:0:0
dwinldcl y6 "~r0" 0 p86:24:39:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "runtime.spanSetSpinePointer" 0 0 1 p99:320:7:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "uintptr" 0 0 1 p99:320:37:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p574:24:10:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "*internal/runtime/atomic.Pointer[runtime.spanSetBlock]" 0 0 1 p99:320:50:0:0
dwname n6 1 0 0 1 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p574:24:39:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p574:24:28:0:0
var 0 0 "s" 5 1 0 0 0 8 y21 "runtime/mspanset.go" 320 7 0 0 1 0 v1
var 1 0 "idx" 5 1 0 0 0 16 y22 "runtime/mspanset.go" 320 37 0 1 1 0 v0
var 2 0 "~r0" 5 1 1 0 0 0 y23 "runtime/mspanset.go" 320 50 0 2 0 0 -
scope 0 0 - 0,1,2
inlcall 0 301 96:321 y20 - 1 4:8 -
dieref y15 3 y18 0
dieref y15 5 y18 1
dieoff y18 0:40,1:48
data y15 SDWARFFCN 58 0 0 0600000000000010019c2900000000000000002900000000000000002e7e72300001c002000000000009000000000000000061000000c1020000 10
reloc 0 0 R_USETYPE 0 y24
reloc 1 4 R_DWARFSECREF 0 y18
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y18
reloc 15 4 R_DWARFSECREF 0 y16
reloc 20 4 R_DWARFSECREF 0 y18
reloc 24 4 R_DWARFSECREF 9 y16
reloc 36 4 R_DWARFSECREF 0 y23
reloc 42 4 R_DWARFSECREF 0 y20
reloc 46 4 R_DWARFSECREF 0 y17
data y16 SDWARFLOC 18 0 0 010000040008015000010000040010015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 7 0 0 01000004040800 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y19 SDWARFLINES 34 0 0 0009020000000000000000046103ba0214045503dd7d33046103a3023c0208000101 1
reloc 3 8 R_ADDR 0 y1
data y18 SDWARFABSFCN 59 0 1 0572756e74696d652e7370616e5365745370696e65506f696e7465722e6c6f6f6b75700001c0020122730000000000002269647800000000000000 2
reloc 44 4 R_DWARFSECREF 0 y21
reloc 54 4 R_DWARFSECREF 0 y22
end
eof
"#

/-- The loaded `spanSetSpinePointer.lookup` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG16` gives (block `b2`: the no-op Progs from 5, `v16`'s `ADD`, then
`RET`). -/
def tab : PcTab := [(2, [5, 5, 5, 5, 9, 9, 9])]

/-- The class table `checkG16` gives: nothing known at the entry `b2`. -/
def kt : KTab := [(2, KMap.bot)]

def blk2 : Block := (lc.ctx.f.block? 2).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- `ι`: as `GenG12.ι`, the heap object `heap 1` at `2^41`. -/
def ι : Blk → Option (BitVec 64) := GenG12.ι

/-- The machine address of `heap 1`. -/
def A : BitVec 64 := 0x20000000000

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, `heap 1` at `2^41` and the PC table of `checkG16`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `s.p`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The `runLoc` state before `v16`: `s.p` (`pB`) in `R0`, the index 2 in `R1`, every other
register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pB else if i.val = 1 then .i64 2 else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v16`: `X0` the address `A` of `s.p`, `X1` 2, the activation's `g` and
`FP`, the PC of `v16`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 1 then 2 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 3, mem := fun _ => 0 }

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

/-- What compiled evaluation checks on `spanSetSpinePointer.lookup`: `checkG16` accepts it with
`tab` and `kt` and `checkG15` does not; it accesses no frame variable and has no home slot; `b2`
holds `v16` at index 3, an `ADDshiftLL`, and `R0` and `R1` have class 64 before it; `stepLoc` runs
`v16` from `s0` and `R0` then holds the integer `2^41 + 16`, which `Ptr.ofAddr` reads as offset 16
of `heap 1`. -/
def gFacts : Bool :=
  (checkG16 lc ps bs g).toOption == some (tab, kt) && (checkG15 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 16).isSome && blk2.values[3]? == some 16 &&
    (val 16).op == .ARM64ADDshiftLL &&
    (kAt lc kt 2 blk2 3).get 0 == some 64 && (kAt lc kt 2 blk2 3).get 1 == some 64 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 16)) r0Is &&
    (Ptr.ofAddr 0x20000000010).blk == .heap 1 && (Ptr.ofAddr 0x20000000010).off == 16

theorem g16_facts : gFacts = true := by
  native_decide

/-- The facts of `g16_facts` as hypotheses. -/
theorem facts :
    checkG16 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 2 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 2 = some blk2 ∧ lc.ctx.f.value? 16 = some (val 16) ∧
      blk2.values[3]? = some 16 ∧ (val 16).op = .ARM64ADDshiftLL ∧
      (kAt lc kt 2 blk2 3).get 0 = some 64 ∧ (kAt lc kt 2 blk2 3).get 1 = some 64 ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 16)) r0Is = true ∧
      (Ptr.ofAddr 0x20000000010).blk = .heap 1 ∧ (Ptr.ofAddr 0x20000000010).off = 16 := by
  have hf := g16_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv16⟩, hi3⟩, hop⟩, hk0⟩, hk1⟩, hrun⟩,
    hob⟩, hoo⟩ := hf
  refine ⟨?_, hav, hsl, hm2, ?_, ?_, hi3, hop, hk0, hk1, hrun, hob, hoo⟩
  · revert hres; cases checkG16 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv16
    simp [val, hv]

theorem g16Env (hc : checkG16 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG16_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG16_spec hc
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

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .ptr pB) ∨ (r = 1 ∧ x = .i64 2) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 2 3 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact ⟨A, rfl, by decide⟩
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl rfl
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g16Inv0 (h0 : (kAt lc kt 2 blk2 3).get 0 = some 64)
    (h1 : (kAt lc kt 2 blk2 3).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk2 3) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

theorem g7Pre_of {v : Value} (h1 : v.op ≠ .ARM64CMP) (h2 : v.op ≠ .ARM64CMPconst)
    (h3 : loadOp? v.op = none) (h4 : v.op ≠ .ARM64LDP) (h5 : v.op ≠ .ARM64SUB)
    (h6 : v.op ≠ .ARM64LoweredNilCheck) (s : LocState) : G7Pre lc s v :=
  ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **G16 on `spanSetSpinePointer.lookup`**: from the state before `v16` with `s.p` (`pB`, the
start of `heap 1`) in `R0` and the index 2 in `R1`, `g16_value` runs the shifted add `v16`
(`ADD R1<<3, R0, R0`) and gives the state before `v13`, with `R0` holding the integer `2^41 + 16`
related to `X0` under an activation that extends `E` and is a `G10Env`: `X0` is then
`2^41 + 16`. -/
theorem genG16_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 16) = .ok s1 ∧
      s1.regs[0]? = some (.i64 0x20000000010) ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 2 4 m1 ∧ G3Inv E' lc (kAt lc kt 2 blk2 4) s1 ∧ m1.x 0 = 0x20000000010 := by
  obtain ⟨hc, hav, hsl, hm2, hb, hv16, hi3, hop, hk0, hk1, hrun, hob, hoo⟩ := facts
  obtain ⟨s1, hs1, hr0⟩ := GenG1.okThen_spec hrun
  have hE := g16Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64ADDshiftLL → (val 16).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g16_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm2 hb hi3 hv16 (by rw [hop]; rfl) locMatch0 (g16Inv0 hk0 hk1)
    ⟨⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; rfl)
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _,
      fun h => absurd h (hne _ (by decide))⟩,
      fun _ _ _ _ hl => by rw [hop] at hl; simp [loadIdxOp?] at hl⟩
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hr0' := r0Is_spec hr0
  refine ⟨s1, E1, m1, hs1, hr0', hx1, hE1, hp1, hm1', hinv1, ?_⟩
  have hrel := (hm1'.regs 0 _ hr0').1 0 (by simp [objX?])
  rcases hrel with h | ⟨-, a, ha, h⟩
  · exact h
  · have h1 : E1.ι (.heap 1) = some A := hx1.2 _ _ rfl
    rw [hob, h1] at ha
    cases ha
    rw [h, hoo]
    decide

end GoFV.Proof.Witness.GenG16
