import GoFV.Proof.Gen.G14
import GoFV.Proof.Witness.GenG13

/-!
# Non-vacuity witness: slice G14 of the genssa validator on `runtime.argv_index`

`std/std/runtime/argv_index,1.ssa` and `…,1.prog` of the corpus
`gofv-corpus/2aae1000ea1d/quick-v10/plain`, embedded verbatim (`fSsa`, `fProg`): `argv_index`
(`runtime/runtime1.go`), `return *(**byte)(add(unsafe.Pointer(argv), uintptr(i)*goarch.PtrSize))`.

`checkG13` rejects it (`v22 = MOVDloadidx8`); `checkG14` accepts it with the PC table `tab` and
the class table `kt`. Block `b1`: `v7 = ArgIntReg` (`argv`, `R0`), `v8 = ArgIntReg` (`i`, `R1`),
`v1 = InitMem`, `v11 = MOVWreg v8` (`R1`), `v22 = MOVDloadidx8 v7 v11 v1` (`R0`),
`v23 = MakeResult v22 v1`; `Ret`. Its Progs: `MOVW R1, R1`, `MOVD (R0)(R1<<3), R0`, `RET`.

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`; `g14_facts`),
`stepLoc` runs `v22` from a state with `argv` the start of the heap object `heap 1` of 32 bytes
(`mem7`: the word at offset 16 is 7, every other byte 0) in `R0` and the index `2` in `R1`, and
`R0` then holds the word 7 loaded from offset 16. On a framed activation with `G10Env` (as
`GenG13`'s, `heap 1` injected at `2^41`) and the machine memory holding the object's bytes there
(`M7`), `g14_value` runs `MOVD (R0)(R1<<3), R0` and gives the state before `v23`, `R0` related to
`X0`, which then holds 7 (`genG14_value_witness`).
-/

namespace GoFV.Proof.Witness.GenG14

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/argv_index,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "argv_index" 1 1 0
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
type t4 UINT8 1 1 0 comparable,named "byte" "uint8"
type t3 PTR 8 8 8 hasptr,direct,comparable "*byte" "*uint8" t4
type t2 PTR 8 8 8 hasptr,direct,comparable "**byte" "**uint8" t3
type t5 INT32 4 4 0 comparable,named "int32" "int32"
type t1 FUNC 8 8 8 hasptr,direct "func(**byte, int32) *byte" "func(**uint8, int32) *uint8" 0 2 1
field 0 "argv" t2 ? 0
field 1 "i" t5 ? 0
field 2 "" t3 ? 0
aux a2 sym "runtime.argv_index" "runtime.argv_index" 1 - 0 - - - - 0
posbase p84 "runtime/runtime1.go" 1 1 -1
aux a3 name "argv" "argv" PPARAM t2 0 1 used p84:65:17:0:0
aux a4 name "i" "i" PPARAM t5 8 1 used p84:65:30:0:0
aux a5 name "~r0" "~r0" PPARAMOUT t3 0 1 - p84:65:39:0:0
aux a1 call "AuxCall{runtime.argv_index}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t5 a4 1 8
abiparam out 0 t3 a5 0 -1
type t6 BOOL 1 1 0 comparable,named "bool" "bool"
type t7 INT8 1 1 0 comparable,named "int8" "int8"
type t8 INT16 2 2 0 comparable,named "int16" "int16"
type t9 INT64 8 8 0 comparable,named "int64" "int64"
type t10 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t10
type t21 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t5
type t22 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t23 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t24 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t18
type t25 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t26 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t27 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t20
type t28 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t29 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t30 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t31 SSA ? ? ? - "mem" ""
type t32 SSA ? ? ? - "flags" ""
type t33 SSA ? ? ? - "void" ""
type t34 SSA 16 8 ? - "int128" ""
type t35 RESULTS ? ? ? - "mem" "" 1 t31
type t36 PTR 8 8 8 hasptr,direct,comparable "***byte" "***uint8" t2
posbase p8594 "runtime/stubs.go" 1 1 8316
type t37 RESULTS ? ? ? - "*byte,mem" "" 2 t3,t31
slot s1 a3 t2 0 - 0
slot s2 a4 t5 0 - 0
aux a6 name "p" "p" PAUTO t30 0 1 used p8594:24:10:0:0
slot s3 a6 t30 0 - 0
aux a7 name "x" "x" PAUTO t18 0 1 used p8594:24:28:0:0
slot s4 a7 t18 0 - 0
aux a8 name "~r0" "~r0" PAUTO t30 0 1 - p8594:24:39:0:0
slot s5 a8 t30 0 - 0
f b1 t1 a1 23 2
typs Bool=t6,Int8=t7,Int16=t8,Int32=t5,Int64=t9,UInt8=t10,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t20,Int32Ptr=t21,UInt32Ptr=t22,IntPtr=t23,UintptrPtr=t24,Float32Ptr=t25,Float64Ptr=t26,BytePtrPtr=t27,Complex64=t28,Complex128=t29,UnsafePtr=t30,Mem=t31,Flags=t32,Void=t33,Int128=t34,ResultMem=t35
b b1 Plain p84:66:22:1:0 0 0 - - b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v9 ConstNil t3 0 - p0:0:0:0:0 0 -
v v10 Copy t30 0 - p84:66:38:2:0 1 v7
v v11 SignExt32to64 t18 0 - p84:66:53:0:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v15 Convert t18 0 - p8594:25:32:0:0 1 v10,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
b b2 Ret p84:66:22:1:0 0 0 - v23 - b1:0
v v18 Copy t30 0 - p84:66:22:2:0 1 v17
v v19 Copy t2 0 - p84:66:22:2:0 1 v18
v v20 Copy t31 0 - p84:66:9:2:0 3 v1
v v21 NilCheck t2 0 - p84:66:9:0:0 1 v19,v20
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v20
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v20
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v13
named s5 v17,v18
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12,3344556677=v9
freev -
freeb -
dcllen 6
end
pass 1 "number lines"
f b1 t1 a1 23 2
b b1 Plain p84:66:22:1:0 0 0 - - b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 7 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v9 ConstNil t3 0 - p0:0:0:0:0 0 -
v v10 Copy t30 0 - p84:66:38:2:0 1 v7
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v10,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
b b2 Ret p84:66:22:1:0 0 0 - v23 - b1:0
v v18 Copy t30 0 - p84:66:22:2:0 1 v17
v v19 Copy t2 0 - p84:66:22:2:0 1 v18
v v20 Copy t31 0 - p84:66:9:2:0 3 v1
v v21 NilCheck t2 0 - p84:66:9:0:0 1 v19,v20
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v20
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v20
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v10
named s4 v13
named s5 v17,v18
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12,3344556677=v9
freev -
freeb -
cache postorder b2,b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 23 2
b b1 Plain p84:66:22:1:0 0 0 - - b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 10 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t36 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t21 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t2 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p84:65:6:2:0 2 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v9 ConstNil t3 0 - p0:0:0:0:0 0 -
v v10 Copy t30 0 - p84:66:38:2:0 0 v7
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v7,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 3 v16,v1
b b2 Ret p84:66:22:1:0 0 0 - v23 - b1:0
v v18 Copy t30 0 - p84:66:22:2:0 0 v17
v v19 Copy t2 0 - p84:66:22:2:0 0 v17
v v20 Copy t31 0 - p84:66:9:2:0 0 v1
v v21 NilCheck t2 0 - p84:66:9:0:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17,v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12,3344556677=v9
freev -
freeb -
cache postorder b2,b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 3 "early deadcode"
f b1 t1 a1 23 2
b b1 Plain p84:66:22:1:0 0 0 - - b2:0 -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v7,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
b b2 Ret p84:66:22:1:0 0 0 - v23 - b1:0
v v21 NilCheck t2 0 - p84:66:9:0:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb -
cache postorder b2,b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 4 "short circuit"
f b2 t1 a1 23 2
b b1 BlockInvalid p84:66:22:1:0 0 0 - - - -
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v7,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 5 "decompose user"
f b2 t1 a1 23 2
b b1 BlockInvalid p84:66:22:1:0 0 0 - - - -
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v7,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb -
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 6 "pre-opt deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 6 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v15 Convert t18 0 - p8594:25:32:1:0 1 v7,v1
v v16 Add64 t18 0 - p8594:25:35:0:0 1 v15,v13
v v17 Convert t30 0 - p8594:25:35:0:0 1 v16,v1
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 7 "opt"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 8 "zero arg cse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 9 "opt deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 10 "generic cse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 11 "phiopt"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 12 "gcse deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v14 InlMark t33 8316 - p84:66:22:0:0 0 v1
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 NilCheck t2 0 - p84:66:9:1:0 1 v17,v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 13 "nilcheckelim"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v21 Copy t2 0 - p84:66:9:1:0 1 v17
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 14 "prove"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v21 Copy t2 0 - p84:66:9:1:0 1 v17
v v22 Load t3 0 - p84:66:9:0:0 1 v21,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 15 "divisible"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v21,v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 16 "divmod"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v12 Const64 t18 8 - p0:0:0:0:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Mul64 t18 0 - p84:66:55:0:0 1 v11,v12
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 8=v12
freev v21,v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 17 "middle opt"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v12,v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 18 "known bits"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v12,v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 19 "early fuse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 Arg t2 0 a3 p84:65:6:2:0 1 -
v v8 Arg t5 0 a4 p84:65:6:2:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v12,v16,v15,v20,v19,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 20 "expand calls"
aux a9 nameoff "argv+0" a3 0
aux a10 nameoff "i+0" a4 0
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
v v12 SB t18 0 - p0:0:0:0:0 0 -
v v16 SP t18 0 - p0:0:0:0:0 3 -
v v15 OffPtr t36 0 - p0:0:0:0:0 0 v16
v v20 OffPtr t21 0 - p0:0:0:0:0 0 v16
v v19 LocalAddr t2 0 a5 p84:66:2:0:0 0 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 0=v15,v20
freev v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 21 "decompose builtin"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
v v12 SB t18 0 - p0:0:0:0:0 0 -
v v16 SP t18 0 - p0:0:0:0:0 3 -
v v15 OffPtr t36 0 - p0:0:0:0:0 0 v16
v v20 OffPtr t21 0 - p0:0:0:0:0 0 v16
v v19 LocalAddr t2 0 a5 p84:66:2:0:0 0 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 0=v15,v20
freev v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 22 "softfloat"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
v v12 SB t18 0 - p0:0:0:0:0 0 -
v v16 SP t18 0 - p0:0:0:0:0 3 -
v v15 OffPtr t36 0 - p0:0:0:0:0 0 v16
v v20 OffPtr t21 0 - p0:0:0:0:0 0 v16
v v19 LocalAddr t2 0 a5 p84:66:2:0:0 0 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 0=v15,v20
freev v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 23 "branchelim"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 4 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
v v12 SB t18 0 - p0:0:0:0:0 0 -
v v16 SP t18 0 - p0:0:0:0:0 3 -
v v15 OffPtr t36 0 - p0:0:0:0:0 0 v16
v v20 OffPtr t21 0 - p0:0:0:0:0 0 v16
v v19 LocalAddr t2 0 a5 p84:66:2:0:0 0 v16,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts 0=v15,v20
freev v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 24 "late opt"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 25 "dead auto elim"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 26 "sccp"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 27 "generic deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 28 "late fuse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 29 "check bce"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 30 "dse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 31 "memcombine"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 32 "writebarrier"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 SignExt32to64 t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v13 Lsh64x64 t18 1 - p84:66:55:0:0 1 v11,v21
v v17 AddPtr t30 0 - p8594:25:35:1:0 1 v7,v13
v v22 Load t3 0 - p84:66:9:1:0 1 v17,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
v v21 Const64 t13 3 - p84:66:55:0:0 1 -
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 33 "lower"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25:25=2
dcllen 6
end
pass 34 "addressing modes"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25:25=2
dcllen 6
end
pass 35 "late lower"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 36 "pair"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 3 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v14 InlMark t33 8316 - p84:66:22:1:0 0 v1
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3,s4,s5
named s1 v7
named s2 v8
named s3 v7
named s4 v13
named s5 v17
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 37 "lowered deadcode for cse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 38 "lowered cse"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 39 "elim unread autos"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 40 "tighten tuple selectors"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 41 "lowered deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 42 "checkLower"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 43 "loop invariant"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 44 "late phielim and copyelim"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 45 "tighten"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 46 "late deadcode"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 47 "critical"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 48 "phi tighten"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 49 "likelyadjust"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
dcllen 6
end
pass 50 "layout"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate laidout
dcllen 6
end
pass 51 "schedule"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
dcllen 6
end
pass 52 "late nilcheck"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
dcllen 6
end
pass 53 "flagalloc"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v14,v21,v17,v13,v19,v20,v15,v16,v12,v18,v10,v9,v6,v5,v4,v3,v2
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
dcllen 6
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.argv_index}" a2 1 2 1 8 16 2 1
abiparam in 0 t2 a3 0 0
abiparam in 1 t5 a4 1 8
abiparam out 0 t3 a5 0 -1
callreg 0:1 - 0 -
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v9,v10,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
regalloc 24 v7:R0,v8:R1,v11:R1,v22:R0,v23:[]
dcllen 6
end
pass 55 "loop rotate"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v9,v10,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
regalloc 24 v7:R0,v8:R1,v11:R1,v22:R0,v23:[]
dcllen 6
end
pass 56 "trim"
f b2 t1 a1 23 2
b b2 Ret p84:66:22:1:0 0 0 - v23 - -
v v7 ArgIntReg t2 0 a9 p84:66:22:1:0 1 -
v v8 ArgIntReg t5 1 a10 p84:66:22:1:0 1 -
v v1 InitMem t31 0 - p0:0:0:0:0 2 -
v v11 ARM64MOVWreg t18 0 - p84:66:53:1:0 1 v8
v v22 ARM64MOVDloadidx8 t3 0 - p84:66:9:1:0 1 v7,v11,v1
v v23 MakeResult t37 0 - p84:66:2:0:0 1 v22,v1
names s1,s2,s3
named s1 v7
named s2 v8
named s3 v7
splits -
canon a3/t2/0/-/0=s1,a4/t5/0/-/0=s2,a6/t30/0/-/0=s3,a7/t18/0/-/0=s4,a8/t30/0/-/0=s5
consts -
freev v2,v3,v4,v5,v6,v9,v10,v12,v13,v14,v15,v16,v17,v18,v19,v20,v21
freeb b1
cache postorder b2
cache idom b2:-
cache sdom b2:-:-:-:2:5
cache loopnest 3 0 - -
cache auxmap a3:1,a4:2,-:3,a9:4,a10:5
cache linestarts 84:66:66,8594:25:25
fstate scheduled,laidout
regalloc 24 v7:R0,v8:R1,v11:R1,v22:R0,v23:[]
dcllen 6
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t24,t27,t28,t29,t30
typelink t2=t27,t3=t20,t4=t10,t31=t35
typeorder t7,t4=t10,t8,t11,t5,t12,t9,t13,t14,t17,t18,t28,t29,t15,t16,t6,t3=t20,t21,t22,t23,t24,t25,t26,t2=t27,t36,t1,t19,t30,t31,t33,t32,t34,t35,t37
eof
"#

/-- `std/std/runtime/argv_index,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "argv_index" 1
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
type t1 8 8 8 1 01 "**byte"
name n1 "argv" PPARAM t1 1 "runtime.argv" 0 a3
type t2 4 4 0 0 - "int32"
name n2 "i" PPARAM t2 1 "runtime.i" 0 a4
type t3 8 8 8 1 01 "*byte"
name n3 "~r0" PPARAMOUT t3 1 "runtime.~r0" 0 a5
type t4 8 8 8 1 01 "unsafe.Pointer"
name n4 "p" PAUTO t4 1 "runtime.p" 0 a6
type t5 8 8 0 0 - "uintptr"
name n5 "x" PAUTO t5 1 "runtime.x" 0 a7
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
posbase p84 "runtime/runtime1.go" 1 1 -1 82 "runtime/runtime1.go" "runtime/runtime1.go" 1 1
sym y1 "runtime.argv_index" 1
curfn p84:65:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2
text y1 0 0 0 0 65 201084
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.argv_index.arginfo1" 0
sym y5 "runtime.argv_index.argliveinfo" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p84:65:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p84:65:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p84:65:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p84:65:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p84:65:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p84:65:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p84:66:53:1:0
p 7 7 0 0 0 - MOVW 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p84:66:53:1:0
p 8 8 0 0 0 - MOVD 0 MEM/8192/8801/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p84:66:9:2:0
p 9 9 0 0 0 - RET 0 _ 0 - _ 0 0 p84:66:22:2:0
p 10 10 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 65 201084
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVW MOVW
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 2
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgslot 2 n4 t4 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgvar 2 n4 2
dbgloc 0 2:-10000:2:22:50
dbgloc 1 2:-10000:2:11:51
dbgloc 2 2:-10000:2:22:50
dbgregout n3
dbgpc 2:22:9,2:11:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p84:65:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p84:65:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p84:65:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p84:65:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p84:65:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p84:65:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p84:66:53:1:0
p 7 0 0 0 369 - MOVW 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p84:66:53:1:0
p 8 4 0 0 342 - MOVD 0 MEM/8192/8801/0/NONE/114/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p84:66:9:2:0
p 9 8 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p84:66:22:2:0
fn y1 16 0 0 0 65 2010cc
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVW MOVW
funcaux y2 y3 - - y4 y5 -
text 16 0 217c4093007861f8c0035fd600000000 0
pcln y10 y11 y12 y13 y6,y7,y8,y9 y2,y3,_,_,_,y4,y5
usedfiles 82
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 5 1 8000 00080804ff 0
data y5 SDATA 2 1 8000 0000 0
data y6 SRODATA 3 1 28000 010400 0
data y7 SRODATA 0 1 28000 - 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 3 1 28000 040400 0
data y10 SRODATA 3 1 28000 020400 0
data y11 SRODATA 4 1 28000 a6010400 0
data y12 SRODATA 4 1 28000 86010400 0
data y13 SRODATA 3 1 28000 000400 0
end
dwarf
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "go:info.runtime.argv_index$abstract" 0
sym y18 "" 0
sym y19 "runtime.add" 1
inl i8316 - p84:66:22:0:0 y19 "add"
posbase p8594 "runtime/stubs.go" 1 1 8316 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
posbase p86 "runtime/stubs.go" 1 1 -1 84 "runtime/stubs.go" "runtime/stubs.go" 1 1
sym y20 "go:info.runtime.add$abstract" 0
sym y21 "go:info.**uint8" 0
sym y22 "go:info.int32" 0
sym y23 "go:info.*uint8" 0
sym y24 "go:info.unsafe.Pointer" 0
sym y25 "type:*uint8" 0
dwfn y14 y15 y16 y17 y18 "runtime.argv_index" 82:65 1 0 1 4262
dwdcl n1,n2
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y17 n1,n2,n3
dwinlfn y19 y20
dwinldcl y19 "p" 0 p86:24:10:0:0
dwinldcl y19 "x" 0 p86:24:28:0:0
dwinldcl y19 "~r0" 0 p86:24:39:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "**uint8" 0 0 1 p84:65:17:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "int32" 0 0 1 p84:65:30:0:0
dwname n4 1 0 0 1 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p8594:24:10:0:0
dwname n3 1 0 0 0 0 0 0 1 - - "*uint8" 0 0 1 p84:65:39:0:0
dwname n6 1 0 0 1 0 0 0 0 - - "unsafe.Pointer" 0 0 1 p8594:24:39:0:0
dwname n5 1 0 0 1 0 0 0 0 - - "uintptr" 0 0 1 p8594:24:28:0:0
var 0 0 "argv" 5 1 0 0 0 8 y21 "runtime/runtime1.go" 65 17 0 0 1 0 v0
var 1 0 "i" 5 1 0 0 0 16 y22 "runtime/runtime1.go" 65 30 0 1 1 0 v1
var 2 0 "~r0" 5 1 1 0 0 0 y23 "runtime/runtime1.go" 65 39 0 2 0 0 -
var 3 0 "p" 5 1 0 1 0 -8 y24 "runtime/stubs.go" 24 10 8317 0 1 0 v2
scope 0 0 - 0,1,2,3
inlcall 0 8316 82:66 y20 - 1 - 3
dieref y14 3 y17 0
dieref y14 5 y17 1
dieoff y17 0:23,1:34
data y14 SDWARFFCN 41 0 0 0600000000000010019c2900000000000000002900000000000000002e7e7230000141000000000000 8
reloc 0 0 R_USETYPE 0 y25
reloc 1 4 R_DWARFSECREF 0 y17
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y17
reloc 15 4 R_DWARFSECREF 0 y15
reloc 20 4 R_DWARFSECREF 0 y17
reloc 24 4 R_DWARFSECREF 9 y15
reloc 35 4 R_DWARFSECREF 0 y23
data y15 SDWARFLOC 18 0 0 010000040008015000010000040004015100 2
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
data y16 SDWARFRANGE 0 0 0 - 0
data y18 SDWARFLINES 23 0 0 00090200000000000000000453033c140637020c000101 1
reloc 3 8 R_ADDR 0 y1
data y17 SDWARFABSFCN 43 0 1 0572756e74696d652e617267765f696e646578000141012261726776000000000000226900000000000000 2
reloc 30 4 R_DWARFSECREF 0 y21
reloc 38 4 R_DWARFSECREF 0 y22
end
eof
"#

/-- The loaded `argv_index` (`GenG2.load`, as `gen-check`). -/
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

/-- The PC table `checkG14` gives (block `b2`: `v11`'s `MOVW` after the no-op Progs from 5,
`v22`'s `MOVD`, then `RET`). -/
def tab : PcTab := [(2, [5, 5, 5, 5, 8, 9, 9])]

/-- The class table `checkG14` gives: nothing known at the entry `b2`. -/
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
at `symA`, `heap 1` at `2^41` and the PC table of `checkG14`. -/
def E : MatchEnv :=
  { lc, ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The argument `argv`: the start of the heap object `heap 1`. -/
def pB : Ptr := ⟨.heap 1, 0⟩

/-- The address `v22` loads from: `argv + 2 · 8`. -/
def pQ : Ptr := ⟨.heap 1, 16⟩

/-- The bytes of `heap 1`: the little-endian word 7 at offset 16, 0 elsewhere. -/
def byte7 (i : Nat) : BitVec 8 := if i = 16 then 7 else 0

/-- The Phase 1 memory before `v22`: `heap 1` a block of 32 bytes `byte7`. -/
def mem7 : Mem :=
  { blocks := #[(.heap 1, { data := Array.ofFn (n := 32) fun i => .b (byte7 i.val) })],
    nextHeap := 2 }

/-- The machine memory before `v22`: the bytes of `heap 1` at `A`, 0 elsewhere. -/
def M7 : Memory := fun y => if (y - A).toNat < 32 then byte7 (y - A).toNat else 0

/-- The `runLoc` state before `v22`: `argv` (`pB`) in `R0`, the index 2 in `R1`, every other
register `poison`, the memory `mem7`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem7 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .ptr pB else if i.val = 1 then .i64 2 else .poison,
    flags := .poison, slots := [], mem := .mem mem7 }

/-- The machine before `v22`: `X0` the address `A` of `argv`, `X1` 2, the activation's `g` and
`FP`, the PC of `v22`, the memory `M7`. -/
def m0 : MState :=
  { x := fun k => if k = 0 then A else if k = 1 then 2 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 2 4, mem := M7 }

/-- `R0` holds the integer 7. -/
def r0Is7 (s : LocState) : Bool :=
  match (s.regs[0]? : Option Val) with
  | some (Val.int Width.w64 x) => x == 7
  | _ => false

theorem r0Is7_spec {s : LocState} (h : r0Is7 s = true) : s.regs[0]? = some (.i64 7) := by
  unfold r0Is7 at h
  split at h
  · rename_i x hx
    simp only [beq_iff_eq] at h
    rw [hx, h]
  · cases h

/-- `v22`'s address in `s0`: the arguments read as words whose `idxSum` at scale 8 addresses
`pQ`. -/
def addrIsQ (s : LocState) : Bool :=
  GenG1.okThen (s.read lc 7) fun x => GenG1.okThen (s.read lc 11) fun y =>
    Arm64.addr (idxSum (2 ^ 3) x y) 0 == some pQ

theorem addrIsQ_spec {s : LocState} (h : addrIsQ s = true) :
    ∃ x y, s.read lc 7 = .ok x ∧ s.read lc 11 = .ok y ∧
      Arm64.addr (idxSum (2 ^ 3) x y) 0 = some pQ := by
  obtain ⟨x, hx, h1⟩ := GenG1.okThen_spec h
  obtain ⟨y, hy, h2⟩ := GenG1.okThen_spec h1
  exact ⟨x, y, hx, hy, by simpa using h2⟩

/-- A shape other than `bool`. -/
def notBool : Ty → Bool
  | .bool => false
  | _ => true

/-- What compiled evaluation checks on `argv_index`: `checkG14` accepts it with `tab` and `kt`
and `checkG13` does not; it accesses no frame variable and has no home slot; `b2` holds `v22` at
index 4, a `MOVDloadidx8` of `v7` and `v11`, not a boolean, and `R0` and `R1` have class 64
before it; in `s0` its address is `pQ`, where `mem7` has 8 readable bytes; `stepLoc` runs `v22`
from `s0` and `R0` then holds 7, which `Ptr.ofAddr` reads as no block's address. -/
def gFacts : Bool :=
  (checkG14 lc ps bs g).toOption == some (tab, kt) && (checkG13 lc ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 2 && (lc.ctx.f.block? 2).isSome &&
    (lc.ctx.f.value? 22).isSome && blk2.values[4]? == some 22 &&
    (val 22).op == .ARM64MOVDloadidx8 && (val 22).args[0]? == some 7 &&
    (val 22).args[1]? == some 11 && notBool (lc.ty (val 22).id) &&
    (kAt lc kt 2 blk2 4).get 0 == some 64 && (kAt lc kt 2 blk2 4).get 1 == some 64 &&
    addrIsQ s0 && (mem7.read pQ 8).isSome &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 22)) r0Is7 && (Ptr.ofAddr 7).blk == .nil

theorem g14_facts : gFacts = true := by
  native_decide

/-- The facts of `g14_facts` as hypotheses. -/
theorem facts :
    checkG14 lc ps bs g = .ok (tab, kt) ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧ 2 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 2 = some blk2 ∧ lc.ctx.f.value? 22 = some (val 22) ∧
      blk2.values[4]? = some 22 ∧ (val 22).op = .ARM64MOVDloadidx8 ∧
      (val 22).args[0]? = some 7 ∧ (val 22).args[1]? = some 11 ∧
      notBool (lc.ty (val 22).id) = true ∧
      (kAt lc kt 2 blk2 4).get 0 = some 64 ∧ (kAt lc kt 2 blk2 4).get 1 = some 64 ∧
      addrIsQ s0 = true ∧ (mem7.read pQ 8).isSome = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 22)) r0Is7 = true ∧
      (Ptr.ofAddr 7).blk = .nil := by
  have hf := g14_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hres, -⟩, hav⟩, hsl⟩, hm2⟩, hb2s⟩, hv22⟩, hi4⟩, hop⟩, ha0⟩, ha1⟩,
    hnb⟩, hk0⟩, hk1⟩, hq⟩, hrd⟩, hrun⟩, h7⟩ := hf
  refine ⟨?_, hav, hsl, hm2, ?_, ?_, hi4, hop, ha0, ha1, hnb, hk0, hk1, hq, hrd, hrun, h7⟩
  · revert hres; cases checkG14 lc ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hb2s
    simp [blk2, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hv22
    simp [val, hv]

theorem g14Env (hc : checkG14 lc ps bs g = .ok (tab, kt)) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G10Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        lcEq := rfl
        link := rfl
        pcOf := rfl
        retOut := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG14_spec hc
          intro p hp
          exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
        addr := GenG12.addrAgree
        glob := fun _ _ _ _ => rfl
        syms := by
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -⟩ := checkG14_spec hc
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

theorem mem7_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem7.blocks) :
    b = .heap 1 ∧ al = { data := Array.ofFn (n := 32) fun i => .b (byte7 i.val) } := by
  simpa [mem7] using h

/-- `mem7` injected into `M7` by `ι`: `heap 1`'s bytes at `A`. -/
theorem memInj7 : MemInj ι mem7 M7 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem7_blocks h
    exact ⟨A, rfl, fun _ => by decide, by simp [A]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := mem7_blocks h
    obtain ⟨rfl, -⟩ := mem7_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem7_blocks h
    have ha' : a = A := by simp [ι, GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    simp only [Array.size_ofFn] at hi
    have hd : (A + BitVec.ofNat 64 i - A).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, M7, hd, hi]

theorem keys7 : KeysNodup mem7 := by simp [KeysNodup, mem7]

theorem sep7 : SepFrom ι (StkAt E) mem7 := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := mem7_blocks h
  have ha' : a = A := by simp [ι, GenG12.ι] at ha; exact ha.symm
  subst ha'
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x7fff0000 := rfl
    have hA : A.toNat = 0x20000000000 := rfl
    rw [hsp] at h2
    simp only [hA, Array.size_ofFn]
    omega
  · cases hk

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

theorem locMatch0 : LocMatch E s0 2 4 m0 where
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
  mem := ⟨mem7, rfl, memInj7⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M7, E, A]; decide,
    by simp only [MState.word, readMem, m0, M7, E, A]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g14Inv0 (h0 : (kAt lc kt 2 blk2 4).get 0 = some 64)
    (h1 : (kAt lc kt 2 blk2 4).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 2 blk2 4) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem7, rfl, keys7, sep7⟩
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

/-- `v22` reads 8 valid bytes of `heap 1` at `pQ`, not as a boolean. -/
theorem idxPre0 (hop : (val 22).op = .ARM64MOVDloadidx8) (ha0 : (val 22).args[0]? = some 7)
    (ha1 : (val 22).args[1]? = some 11) (hnb : notBool (lc.ty (val 22).id) = true)
    (hq : addrIsQ s0 = true) (hrd : (mem7.read pQ 8).isSome = true) : IdxPre lc s0 (val 22) := by
  intro as n sh sg hl a0 a1 x y h0 h1 hx hy
  rw [hop] at hl
  simp only [loadIdxOp?, Option.some.injEq, Prod.mk.injEq] at hl
  obtain ⟨-, rfl, rfl, -⟩ := hl
  rw [ha0] at h0
  cases h0
  rw [ha1] at h1
  cases h1
  obtain ⟨x', y', hx', hy', hp⟩ := addrIsQ_spec hq
  rw [hx] at hx'
  cases hx'
  rw [hy] at hy'
  cases hy'
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hrd
  refine ⟨pQ, mem7, bs, hp, rfl, hbs, fun hb => ?_⟩
  rw [hb] at hnb
  cases hnb

/-- **G14 on `argv_index`**: from the state before `v22` with `argv` (`pB`) in `R0`, the index 2
in `R1` and `heap 1` holding the word 7 at offset 16 (`mem7`, at `A` in `M7`), `g14_value` runs
the register-index load `v22` (`MOVD (R0)(R1<<3), R0`) and gives the state before `v23`, with `R0`
holding 7 related to `X0` under an activation that extends `E` and is a `G10Env`: `X0` is then
7. -/
theorem genG14_value_witness :
    ∃ s1 E' m1, stepLoc GenG2.env lc s0 (val 22) = .ok s1 ∧ s1.regs[0]? = some (.i64 7) ∧
      E.Extends E' ∧ G10Env lc g L ps 0 tab E' ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
      LocMatch E' s1 2 5 m1 ∧ G3Inv E' lc (kAt lc kt 2 blk2 5) s1 ∧ m1.x 0 = 7 := by
  obtain ⟨hc, hav, hsl, hm2, hb, hv22, hi4, hop, ha0, ha1, hnb, hk0, hk1, hq, hrd, hrun, h7⟩ := facts
  obtain ⟨s1, hs1, hr0⟩ := GenG1.okThen_spec hrun
  have hE := g14Env hc hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOVDloadidx8 → (val 22).op ≠ o :=
    fun o h h' => h (h'.symm.trans hop)
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', hinv1⟩ := g14_value (H := GenG2.H0) (env := GenG2.env) hc
    hE hm2 hb hi4 hv22 (by rw [hop]; rfl) locMatch0 (g14Inv0 hk0 hk1)
    ⟨⟨g7Pre_of (hne _ (by decide)) (hne _ (by decide)) (by rw [hop]; simp [loadOp?, narrowLoad?])
      (hne _ (by decide)) (hne _ (by decide)) (hne _ (by decide)) _,
      fun h => absurd h (hne _ (by decide))⟩, idxPre0 hop ha0 ha1 hnb hq hrd⟩
    (fun h => absurd h (hne _ (by decide))) (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hr0' := r0Is7_spec hr0
  refine ⟨s1, E1, m1, hs1, hr0', hx1, hE1, hp1, hm1', hinv1, ?_⟩
  have hrel := (hm1'.regs 0 _ hr0').1 0 (by simp [objX?])
  rcases hrel with h | ⟨hn, -⟩
  · exact h
  · exact absurd h7 hn

end GoFV.Proof.Witness.GenG14
