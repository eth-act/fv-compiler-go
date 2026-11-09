import GoFV.Proof.Gen.G52
import GoFV.Proof.Witness.GenG49

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: slice G52 of the genssa validator on `main.nrand` (`test/ken_chan`)

`test/ken_chan/main/nrand,1.ssa` and `.prog` of quick-v10, embedded verbatim: `genG52_witness`
runs its remainder `v32` (`MOD`, `REM R0, R1, R0`) through `g52_value`.
-/

namespace GoFV.Proof.Witness.GenG52

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/ken_chan/main/nrand,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "nrand" 1 0 0
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
type t2 INT 8 8 0 comparable,named "int" "int"
type t1 FUNC 8 8 8 hasptr,direct "func(int) int" "func(int) int" 0 1 1
field 0 "n" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "main.nrand" "main.nrand" 1 - 0 - - - - 0
posbase p2 "./chan.go" 1 1 -1
aux a3 name "n" "n" PPARAM t2 0 1 used p2:17:12:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p2:17:19:0:0
aux a1 call "AuxCall{main.nrand}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t2
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
aux a5 sym "main.randx" "main.randx" 0 - 0 - - - - 0
aux a6 type "int" t2
type t33 RESULTS ? ? ? - "int,mem" "" 2 t2,t28
aux a8 sym "runtime.panicdivide" "runtime.panicdivide" 1 - 0 - - - - 0
aux a7 call "AuxCall{runtime.panicdivide}" a8 1 0 0 8 0 0 0
slot s1 a3 t2 0 - 0
f b1 t1 a1 34 5
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t2,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:17:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:0:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 3 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:0:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:0:0 1 v24,v25
v v27 Copy t2 0 - p2:22:15:2:0 2 v6
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v27,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v19 Copy t28 0 - p2:20:9:2:0 2 v13
v v20 Load t2 0 - p2:20:9:0:0 1 v18,v19
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v19
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v27
v v33 Copy t28 0 - p2:22:2:2:0 1 v25
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v33
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v29 Copy t28 0 - p2:22:15:2:0 1 v25
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 2 v29
v v31 SelectN t28 0 - p2:22:15:0:0 0 v30
names s1
named s1 v6,v27
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev -
freeb -
dcllen 2
end
pass 1 "number lines"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:17:6:2:0 1 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 3 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v27 Copy t2 0 - p2:22:15:2:0 2 v6
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v27,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v19 Copy t28 0 - p2:20:9:2:0 2 v13
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v19
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v19
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v27
v v33 Copy t28 0 - p2:22:2:2:0 1 v25
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v33
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v29 Copy t28 0 - p2:22:15:2:0 1 v25
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 2 v29
v v31 SelectN t28 0 - p2:22:15:0:0 0 v30
names s1
named s1 v6,v27
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev -
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v4 LocalAddr t20 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t20 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p2:17:6:2:0 3 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 5 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 5 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v27 Copy t2 0 - p2:22:15:2:0 0 v6
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v19 Copy t28 0 - p2:20:9:2:0 0 v13
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v13
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v33 Copy t28 0 - p2:22:2:2:0 0 v25
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v29 Copy t28 0 - p2:22:15:2:0 0 v25
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 2 v25
v v31 SelectN t28 0 - p2:22:15:0:0 0 v30
names s1
named s1 v6,v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev -
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 3 "early deadcode"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 4 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v13
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v29,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 4 "short circuit"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 4 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v13
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v29,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 5 "decompose user"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 4 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v13
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v29,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 1 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 1 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 4 v12,v11,v1
v v14 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v15 Load t2 0 - p2:19:11:1:0 1 v14,v13
v v16 Const64 t2 1000000 - p0:0:0:0:0 2 -
v v17 Leq64 t3 0 - p2:19:11:0:0 1 v16,v15
v v18 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v20 Load t2 0 - p2:20:9:1:0 1 v18,v13
v v21 Sub64 t2 0 - p2:20:9:0:0 1 v20,v16
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v29,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 7 "opt"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 2 v12,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 8 "zero arg cse"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 2 v12,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 9 "opt deadcode"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v9,v10
v v12 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v13 Store t28 0 a6 p2:18:8:0:0 2 v12,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v22 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 1 v3
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v24,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v22,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache linestarts 2:18:22
dcllen 2
end
pass 10 "generic cse"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v12 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v22 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 11 "phiopt"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v12 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v22 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v24 Addr t20 0 a5 p0:0:0:0:0 0 v3
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 12 "gcse deadcode"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 13 "nilcheckelim"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 14 "prove"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 15 "divisible"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 16 "divmod"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 17 "middle opt"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 18 "known bits"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 19 "early fuse"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 Arg t2 0 a3 p2:17:6:2:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticLECall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v24,v22,v12,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 20 "expand calls"
aux a9 nameoff "n+0" a3 0
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v24 SP t15 0 - p0:0:0:0:0 2 -
v v22 OffPtr t20 0 - p0:0:0:0:0 0 v24
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 4 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v12 LocalAddr t20 0 a4 p2:22:2:0:0 0 v24,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,v22,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 21 "decompose builtin"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v24 SP t15 0 - p0:0:0:0:0 2 -
v v22 OffPtr t20 0 - p0:0:0:0:0 0 v24
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 4 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v12 LocalAddr t20 0 a4 p2:22:2:0:0 0 v24,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,v22,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 22 "softfloat"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v24 SP t15 0 - p0:0:0:0:0 2 -
v v22 OffPtr t20 0 - p0:0:0:0:0 0 v24
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 4 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v12 LocalAddr t20 0 a4 p2:22:2:0:0 0 v24,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,v22,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 23 "branchelim"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
v v24 SP t15 0 - p0:0:0:0:0 2 -
v v22 OffPtr t20 0 - p0:0:0:0:0 0 v24
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 4 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v12 LocalAddr t20 0 a4 p2:22:2:0:0 0 v24,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,v22,10007=v10,1000000=v16
freev v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 24 "late opt"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 25 "dead auto elim"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 26 "sccp"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 27 "generic deadcode"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 28 "late fuse"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 29 "check bce"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 30 "dse"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 31 "memcombine"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 32 "writebarrier"
f b1 t1 a1 34 5
b b1 If p2:19:14:0:0 0 0 - v17 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 1 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v7 Const64 t2 0 - p0:0:0:0:0 1 -
v v10 Const64 t2 10007 - p0:0:0:0:0 1 -
v v16 Const64 t2 1000000 - p0:0:0:0:0 1 -
v v29 Const64 t2 -989993 - p2:20:9:1:0 1 -
v v8 Addr t20 0 a5 p0:0:0:0:0 4 v3
v v9 Load t2 0 - p2:18:8:1:0 2 v8,v1
v v11 Add64 t2 0 - p2:18:8:0:0 2 v10,v9
v v13 Store t28 0 a6 p2:18:8:0:0 2 v8,v11,v1
v v17 Leq64 t3 0 - p2:19:11:1:0 1 v16,v11
b b2 If p2:22:15:0:0 1 0 - v28 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 Load t2 0 - p2:22:15:1:0 1 v8,v25
v v28 Neq64 t3 0 - p2:22:15:0:0 1 v6,v7
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 Add64 t2 0 - p2:20:9:1:0 1 v29,v9
v v23 Store t28 0 a6 p2:20:9:0:0 1 v8,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 Mod64 t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 StaticCall t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts 0=v7,10007=v10,1000000=v16
freev v12,v22,v24,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 33 "lower"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADDconst t2 10007 - p2:18:8:0:0 2 v9
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMPconst t29 1000000 - p2:19:11:1:0 1 v11
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUBconst t2 989993 - p2:20:9:1:0 1 v9
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v22,v28,v12,v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22:20=1
dcllen 2
end
pass 34 "addressing modes"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADDconst t2 10007 - p2:18:8:0:0 2 v9
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMPconst t29 1000000 - p2:19:11:1:0 1 v11
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUBconst t2 989993 - p2:20:9:1:0 1 v9
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v22,v28,v12,v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22:20=1
dcllen 2
end
pass 35 "late lower"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 36 "pair"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3
cache linestarts 2:18:22
dcllen 2
end
pass 38 "lowered cse"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 39 "elim unread autos"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 41 "lowered deadcode"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 42 "checkLower"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 43 "loop invariant"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 45 "tighten"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 46 "late deadcode"
f b1 t1 a1 34 5
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2
cache sdom b1:-:b3:-:2:29,b2:b1:b5:-:11:26,b3:b1:-:b2:5:8,b4:b2:-:-:20:23,b5:b2:-:b4:14:17
cache loopnest 6 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 47 "critical"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 48 "phi tighten"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 49 "likelyadjust"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b1
cache sdom b1:-:b6:-:2:35,b2:b1:b5:-:17:32,b3:b1:-:b2:11:14,b4:b2:-:-:26:29,b5:b2:-:b4:20:23,b6:b1:-:b3:5:8
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
dcllen 2
end
pass 50 "layout"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate laidout
dcllen 2
end
pass 51 "schedule"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
dcllen 2
end
pass 52 "late nilcheck"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
dcllen 2
end
pass 53 "flagalloc"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v22 ARM64MOVDconst t11 10007 - p2:18:8:0:0 1 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v22
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v28 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v28
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v12 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v12
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v17,v8,v29,v16,v10,v7,v31,v20,v18,v15,v14,v33,v19,v27,v5,v4,v2
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
dcllen 2
end
pass 54 "regalloc"
aux a1 call "AuxCall{main.nrand}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 0 0
abiparam out 0 t2 a4 0 -1
callreg 0:1 - 0 -
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v17 ARM64MOVDconst t11 10007 - p2:18:8:2:0 1 -
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v17
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v8 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v8
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v29 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v29
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v10,v14,v15,v16,v18,v19,v20,v27,v31,v33
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
regalloc 35 v3:SB,v6:R0,v8:R3,v9:R1,v11:R2,v17:R2,v21:R1,v26:R1,v29:R2,v32:R0,v34:[]
dcllen 2
end
pass 55 "loop rotate"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b6:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v17 ARM64MOVDconst t11 10007 - p2:18:8:2:0 1 -
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v17
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v8 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v8
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v29 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v29
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b6 Plain p2:19:14:0:0 0 0 - - b2:0 b1:1
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b6:0,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v10,v14,v15,v16,v18,v19,v20,v27,v31,v33
freeb -
cache postorder b4,b5,b2,b3,b6,b1
cache idom b1:-,b3:b1,b6:b1,b2:b1,b4:b2,b5:b2
cache sdom b1:-:b6:-:2:35,b3:b1:-:b2:11:14,b6:b1:-:b3:5:8,b2:b1:b5:-:17:32,b4:b2:-:-:26:29,b5:b2:-:b4:20:23
cache loopnest 7 0 - -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
regalloc 35 v3:SB,v6:R0,v8:R3,v9:R1,v11:R2,v17:R2,v21:R1,v26:R1,v29:R2,v32:R0,v34:[]
dcllen 2
end
pass 56 "trim"
f b1 t1 a1 34 6
b b1 ARM64GE p2:19:14:0:0 0 0 - v24 b3:0,b2:0 -
v v6 ArgIntReg t2 0 a9 p2:19:14:0:0 2 -
v v3 SB t15 0 - p0:0:0:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 2 -
v v9 ARM64MOVDload t2 0 a5 p2:18:8:1:0 2 v3,v1
v v17 ARM64MOVDconst t11 10007 - p2:18:8:2:0 1 -
v v11 ARM64ADD t2 0 - p2:18:8:0:0 2 v9,v17
v v13 ARM64MOVDstore t28 0 a5 p2:18:8:0:0 2 v3,v11,v1
v v8 ARM64MOVDconst t11 1000000 - p2:19:11:1:0 1 -
v v24 ARM64CMP t29 0 - p2:19:11:1:0 1 v11,v8
b b3 Plain p2:20:12:0:0 0 0 - - b2:1 b1:0
v v29 ARM64MOVDconst t11 989993 - p2:20:9:1:0 1 -
v v21 ARM64SUB t2 0 - p2:20:9:1:0 1 v9,v29
v v23 ARM64MOVDstore t28 0 a5 p2:20:9:0:0 1 v3,v21,v13
b b2 ARM64NZ p2:22:15:0:0 1 0 - v6 b4:0,b5:0 b1:1,b3:0
v v25 Phi t28 0 - p2:22:2:0:0 3 v13,v23
b b4 Ret p2:22:15:1:0 0 0 - v34 - b2:0
v v26 ARM64MOVDload t2 0 a5 p2:22:15:1:0 1 v3,v25
v v32 ARM64MOD t2 0 - p2:22:15:0:0 1 v26,v6
v v34 MakeResult t33 0 - p2:22:2:0:0 1 v32,v25
b b5 Exit p2:22:15:0:0 0 0 - v30 - b2:1
v v30 ARM64CALLstatic t32 0 a7 p2:22:15:0:0 1 v25
names s1
named s1 v6
splits -
canon a3/t2/0/-/0=s1
consts -
freev v2,v4,v5,v7,v10,v14,v15,v16,v18,v19,v20,v27,v31,v33
freeb -
cache auxmap -:1,a3:2,a5:3,a9:4
cache linestarts 2:18:22
fstate scheduled,laidout
regalloc 35 v3:SB,v6:R0,v8:R3,v9:R1,v11:R2,v17:R2,v21:R1,v26:R1,v29:R2,v32:R0,v34:[]
dcllen 2
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t2,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t33
eof
"#

/-- `test/ken_chan/main/nrand,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "nrand" 1
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
type t1 8 8 0 0 - "int"
name n1 "n" PPARAM t1 1 "main.n" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "main.~r0" 0 a4
in n1 0 used
in n2 0 outregs
out n1 0 used
opt n2 0 outregs
stack 0 0 8
end
genin
posbase p2 "./chan.go" 1 1 -1 1 "./chan.go" "./chan.go" 1 1
sym y1 "main.nrand" 1
curfn p2:17:6:0:0 0 0
regargs 8192:0:t1
text y1 0 0 0 0 17 201080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.nrand.arginfo1" 0
sym y4 "main.nrand.argliveinfo" 0
sym y5 "main.randx" 0
sym y6 "runtime.panicdivide" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p2:17:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:17:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:17:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p2:17:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p2:17:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p2:17:6:2:0
p 6 6 0 0 0 - MOVD 0 MEM/0/0/0/EXTERN/0/0/y5/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:18:8:1:0
p 7 7 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/10007/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:18:8:2:0
p 8 8 0 0 0 - ADD 0 REG/8194/0/0/NONE/0/0/-/- 8193 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:18:8:2:0
p 9 9 0 0 0 - MOVD 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:18:8:2:0
p 10 10 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/1000000/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p2:19:11:1:0
p 11 11 0 0 0 - CMP 0 REG/8195/0/0/NONE/0/0/-/- 8194 - _ 0 0 p2:19:11:2:0
p 12 12 0 0 0 - BLT 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@16 0 0 p2:19:14:2:0
p 13 13 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/989993/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:20:9:1:0
p 14 14 0 0 0 - SUB 0 REG/8194/0/0/NONE/0/0/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:20:9:2:0
p 15 15 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:20:9:2:0
p 16 16 0 0 0 - CBZ 0 REG/8192/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@20 0 0 p2:22:15:2:0
p 17 17 0 0 0 - MOVD 0 MEM/0/0/0/EXTERN/0/0/y5/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:22:15:1:0
p 18 18 0 0 0 - REM 0 REG/8192/0/0/NONE/0/0/-/- 8193 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:22:15:2:0
p 19 19 0 0 0 - RET 0 _ 0 - _ 0 0 p2:22:15:2:0
p 20 20 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:22:15:2:0
p 21 21 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2:22:15:2:0
p 22 22 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2:22:15:0:0
p 23 23 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 17 201080
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
dbgloc 0 1:-10000:4:32:50
dbgregout n2
dbgpc 4:32:19
end
asm
sym y7 "runtime.morestack_noctxt" 0
sym y8 "" 0
sym y9 "" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/16/-/i8 0 0 p2:17:6:0:0
p 24 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 25 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:17:6:0:0
p 26 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:17:6:0:0
p 27 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@45 0 0 p2:17:6:0:0
p 28 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 29 12 16 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-16/-/- 0 0 p2:17:6:0:1
p 30 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:17:6:0:0
p 31 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:17:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:17:6:0:0
p 3 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p2:17:6:0:0
p 4 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p2:17:6:0:0
p 5 24 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p2:17:6:2:0
p 32 24 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:17:6:2:0
p 6 24 0 0 338 - MOVD 0 MEM/0/0/0/EXTERN/110/0/y5/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:18:8:1:0
p 33 32 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:18:8:1:0
p 7 32 0 0 318 - MOVD 0 CONST/0/0/0/NONE/23/10007/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:18:8:2:0
p 8 36 0 0 23 - ADD 0 REG/8194/0/0/NONE/2/0/-/- 8193 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:18:8:2:0
p 34 40 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:18:8:2:0
p 9 40 0 0 313 - MOVD 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:18:8:2:0
p 35 48 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:18:8:2:0
p 10 48 0 0 320 - MOVD 0 CONST/0/0/0/NONE/25/1000000/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:19:11:1:0
p 11 56 0 0 92 - CMP 0 REG/8195/0/0/NONE/2/0/-/- 8194 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:19:11:2:0
p 12 60 0 0 80 - BLT 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/16/-/@16 0 0 p2:19:14:2:0
p 13 64 0 0 320 - MOVD 0 CONST/0/0/0/NONE/25/989993/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:20:9:1:0
p 14 72 0 0 23 - SUB 0 REG/8194/0/0/NONE/2/0/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:20:9:2:0
p 36 76 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:20:9:2:0
p 15 76 0 0 313 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p2:20:9:2:0
p 37 84 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:20:9:2:0
p 16 84 0 0 85 - CBZ 0 REG/8192/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/20/-/@20 0 0 p2:22:15:2:0
p 38 88 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-4/-/- 0 0 p2:22:15:2:0
p 17 88 0 0 338 - MOVD 0 MEM/0/0/0/EXTERN/110/0/y5/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:22:15:1:0
p 39 96 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p2:22:15:1:0
p 18 96 0 0 414 - REM 0 REG/8192/0/0/NONE/2/0/-/- 8193 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:22:15:2:0
p 40 104 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p2:22:15:2:0
p 19 104 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:22:15:2:0
p 41 108 -16 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/16/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:22:15:2:0
p 42 112 16 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:22:15:2:0
p 20 116 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:22:15:2:0
p 21 116 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p2:22:15:2:0
p 22 120 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:22:15:0:0
p 43 124 -16 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:22:15:0:0
p 44 124 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 45 124 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:17:6:0:0
p 46 124 0 0 308 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/87/8/-/- 0 0 p2:17:6:0:0
p 47 128 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 48 132 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y7/- 0 0 p2:17:6:0:0
p 49 136 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 50 136 0 0 333 - MOVD 0 MEM/8383/0/0/NONE/87/8/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 51 140 16 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@24 0 0 p2:17:6:0:0
fn y1 8 8 0 0 17 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
funcaux y2 y2 - - y3 y4 -
text 144 0 900b40f9ff6330eba9030054fe0f1ff8fd831ff8fd2300d11b000090610340f9e2e284d22200028b1b000090620300f9034888d2e301a0f25f0003ebcb000054226583d2e201a0f2210002cb1b000090610300f9000100b41b000090610340f93b0cc09a6087009bfd835ff8fe0741f8c0035fd6000000941f2003d5e00700f9e3031eaa00000094e00740f9ddffff17 6
reloc 24 8 R_ARM64_PCREL_LDST64 0 y5
reloc 40 8 R_ARM64_PCREL_LDST64 0 y5
reloc 76 8 R_ARM64_PCREL_LDST64 0 y5
reloc 88 8 R_ARM64_PCREL_LDST64 0 y5
reloc 116 4 R_CALLARM64 0 y6
reloc 132 4 R_CALLARM64 0 y7
pcln y12 y13 y14 y15 y8,y9,y10,y11 y2,y2,_,_,_,y3,y4
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y8 SRODATA 29 1 28000 0001010202030302040205020607030204010502020204050103020200 0
data y9 SRODATA 7 1 28000 001d0202010500 0
data y10 SRODATA 0 1 28000 - 0
data y11 SRODATA 5 1 28000 0006041e00 0
data y12 SRODATA 11 1 28000 020420181f0120021f0500 0
data y13 SRODATA 3 1 28000 042400 0
data y14 SRODATA 13 1 28000 2406020602040205040a090500 0
data y15 SRODATA 3 1 28000 002400 0
end
dwarf
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "go:info.main.nrand$abstract" 0
sym y20 "" 0
sym y21 "go:info.int" 0
sym y22 "type:int" 0
dwfn y16 y17 y18 y19 y20 "main.nrand" 1:17 1 0 1 46
dwdcl n1
dwclosure 0 -
dwparents -
dwparams n1,n2
dwprecursor y1 y19 n1,n2
dwname n1 1 1 0 0 0 0 0 0 - - "int" 0 0 1 p2:17:12:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "int" 0 0 1 p2:17:19:0:0
var 0 0 "n" 5 1 0 0 0 8 y21 "./chan.go" 17 12 0 0 1 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y21 "./chan.go" 17 19 0 1 0 0 -
scope 0 0 - 0,1
dieref y16 3 y19 0
dieoff y19 0:15
data y16 SDWARFFCN 32 0 0 0600000000009001019c2900000000000000002e7e7230000111000000000000 6
reloc 0 0 R_USETYPE 0 y22
reloc 1 4 R_DWARFSECREF 0 y19
reloc 5 1 R_DWTXTADDR_U1 0 y1
reloc 11 4 R_DWARFSECREF 0 y19
reloc 15 4 R_DWARFSECREF 0 y17
reloc 26 4 R_DWARFSECREF 0 y21
data y17 SDWARFLOC 8 0 0 0100040068015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y18 SDWARFRANGE 0 0 0 - 0
data y20 SDWARFLINES 44 0 0 00090200000000000000000402030b140a8788065f06b0065f0660065f890637065f06ff037f330214000101 1
reloc 3 8 R_ADDR 0 y1
data y19 SDWARFABSFCN 24 0 1 056d61696e2e6e72616e6400011101226e00000000000000 1
reloc 19 4 R_DWARFSECREF 0 y21
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.nrand`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G52's check runs on (`liveCtx`). -/
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

/-- The PC table `checkG52` gives. -/
def tab : PcTab := (match checkG52 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG52` gives. -/
def kt : KTab := (match checkG52 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

def blk : Block := (lc.ctx.f.block? 4).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA` and the PC table of `checkG52`. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The dividend `randx = -17`. -/
def xw : BitVec 64 := 0xffffffffffffffef

/-- The divisor `n = 5`. -/
def nw : BitVec 64 := 5

/-- `-17 % 5 = -2` (Go's remainder has the dividend's sign). -/
def remW : BitVec 64 := 0xfffffffffffffffe

/-- The `runLoc` state before `v32`: `n` (`v6`) in `R0`, `randx` (`v26`) in `R1`, every other
register `poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i =>
      if i.val = 0 then .int .w64 nw else if i.val = 1 then .int .w64 xw else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v32`: `X0 = n`, `X1 = randx`, the activation's `g` and `FP`, the PC of
`v32`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 0 then nw else if k = 1 then xw else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 4 1, mem := fun _ => 0 }

/-- The register holds the 64-bit `remW`. -/
def isR : Option Val → Bool
  | some (.int .w64 x) => x == remW
  | _ => false

theorem isR_spec {o : Option Val} (h : isR o = true) : o = some (.int .w64 remW) := by
  unfold isR at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `main.nrand`: it holds an arm64 op; `checkG52` accepts it
with `tab` and `kt` and `checkG49` does not; it accesses no frame variable and has no home slot;
`b4` holds `v32` (`MOD v26 v6`) at index 1, where `R0` and `R1` have class 64 and G35's table is
empty; `stepLoc` runs `v32` from `s0` to `R0 = remW`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG52 lc0 ps bs g).toOption == some (tab, kt) && (checkG49 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    lc.ctx.f.blocks.toList.contains 4 && (lc.ctx.f.block? 4).isSome &&
    (lc.ctx.f.value? 32).isSome && blk.values[1]? == some 32 &&
    (val 32).op == .ARM64MOD &&
    (kAt lc kt 4 blk 1).get 0 == some 64 && (kAt lc kt 4 blk 1).get 1 == some 64 &&
    uL35 lc (uIn35 lc 4) blk 1 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 32)) (fun s1 => isR s1.regs[0]?)

theorem g52_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG52 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG49 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧
      4 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 4 = some blk ∧
      lc.ctx.f.value? 32 = some (val 32) ∧ blk.values[1]? = some 32 ∧
      (val 32).op = .ARM64MOD ∧
      (kAt lc kt 4 blk 1).get 0 = some 64 ∧ (kAt lc kt 4 blk 1).get 1 = some 64 ∧
      uL35 lc (uIn35 lc 4) blk 1 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 32)) (fun s1 => isR s1.regs[0]?) = true := by
  have hf := g52_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h49, hav, hsl, hm1, hbs, hvs, hi1, hop, hk0, hk1, hu1, hrun⟩ := hf
  refine ⟨hl, ?_, h49, hav, hsl, hm1, ?_, ?_, hi1, hop, hk0, hk1, hu1, hrun⟩
  · revert hres; cases checkG52 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g52Env (hc : checkG52 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
                checkG52L_spec hl (checkG52_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG12.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -⟩ :=
                checkG52L_spec hl (checkG52_spec hc).2
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
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## `v32`: `REM R0, R1, R0` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 0 ∧ x = .int .w64 nw) ∨ (r = 1 ∧ x = .int .w64 xw) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    split at h
    · rename_i h0; exact Or.inl ⟨h0, h.symm⟩
    · split at h
      · rename_i _ h1; exact Or.inr (Or.inl ⟨h1, h.symm⟩)
      · exact Or.inr (Or.inr h.symm)
  · cases h

theorem locMatch0 : LocMatch E s0 4 1 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 0 = nw by decide)
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      exact Or.inl (show m0.x 1 = xw by decide)
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g52Inv0 (h0 : (kAt lc kt 4 blk 1).get 0 = some 64)
    (h1 : (kAt lc kt 4 blk 1).get 1 = some 64) :
    G3Inv E lc (kAt lc kt 4 blk 1) s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, GenG2.keys0, GenG2.sep0⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [h0] at hc; cases hc; rfl
    · rw [h1] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- The per-value premises of G51 on `v32`, `MOD`: none of them applies. -/
theorem pre32 (hop : (val 32).op = .ARM64MOD) : G51Pre lc s0 (val 32) := by
  have hne : ∀ o : Op, o ≠ .ARM64MOD → (val 32).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩,
    ?_, ?_⟩
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

/-- **G52 on `main.nrand`** (`test/ken_chan`: `func nrand(n int) int`, which ends in
`return randx % n`; on arm64 `REM R0, R1, R0`): `b4` takes the remainder (`v32`, `MOD v26 v6`),
which `checkG49` rejects and `checkG52` accepts. From `s0`, with `n = 5` in `R0` and
`randx = -17` in `R1`, `stepLoc` runs `v32` to `R0 = -2`, and `g52_value` relates it to a machine
state after `v32`'s code with `X0 = -2`, under an activation extending `E` that is again a
`G49Env`. -/
theorem genG52_witness :
    (checkG49 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 32) = .ok s1 ∧
        s1.regs[0]? = some (.int .w64 remW) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 4 2 m1 ∧ m1.x 0 = remW := by
  obtain ⟨hl, hc, h49, hav, hsl, hm1, hb, hv32, hi1, hop, hk0, hk1, hu1, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr0 := isR_spec hr
  have hE := g52Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64MOD → (val 32).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g52_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hm0 : 4 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 4 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 32 = some (val 32) := by rw [← liveCtx_ctx (lc := lc0)]; exact hv32
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := g52_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hm0 hb0 hi1 hv0 (by rw [hop]; rfl) locMatch0 (g52Inv0 hk0 hk1)
    (by change UOKL m0 (uL35 lc (uIn35 lc 4) blk 1); rw [hu1]; intro e he; cases he)
    (pre32 hop)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (GenG10.icallOK_ne (by rw [hop]; rfl))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide))) hs1
  have hA : AddrAgree E1.ι := by
    obtain ⟨⟨⟨⟨⟨⟨-, -, -, -, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE1
    exact hA
  have hx0 : m1.x 0 = remW := valRel_i64 hA ((hm1'.regs 0 _ hr0).1 0 rfl)
  exact ⟨h49, s1, E1, m1, hs1, hr0, hx1, hE1, hp1, hm1', hx0⟩

end GoFV.Proof.Witness.GenG52
