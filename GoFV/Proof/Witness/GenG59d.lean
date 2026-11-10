import GoFV.Proof.Gen.G58
import GoFV.Proof.Witness.GenG2

/-!
# Witness: a `Defer` block's terminator (`Cx.term`'s `Defer` arm, `term_core`, `g58_term`)

`test/defer/main.test1helper` (quick-v10), its `.ssa`/`.prog` embedded verbatim below. Block `b3`
is a `Defer` block (`v24 = CALLstatic {runtime.deferproc}`, successors `b4`, `b7`); `ssaGenBlock`
emits a `JMP` to `b4` (Prog 19), as for a `Plain` block. `checkG58` accepts the function with the
PC table `tab` (before the `Defer` arm of `Cx.term`, every slice rejected it at `b3: block kind
Defer`), and `g58_term` relates `stepTermLoc`'s step of `b3` to the machine's `JMP` to `b4`'s start.
-/

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG59d

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `test/defer/main/test1helper,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "main"
func "test1helper" 1 0 0
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
type t1 FUNC 8 8 8 hasptr,direct "func()" "func()" 0 0 0
aux a2 sym "main.test1helper" "main.test1helper" 1 - 0 - - - - 0
aux a1 call "AuxCall{main.test1helper}" a2 1 0 0 8 0 0 0
type t2 BOOL 1 1 0 comparable,named "bool" "bool"
type t3 INT8 1 1 0 comparable,named "int8" "int8"
type t4 INT16 2 2 0 comparable,named "int16" "int16"
type t5 INT32 4 4 0 comparable,named "int32" "int32"
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
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t5
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
posbase p2 "./defer.go" 1 1 -1
type t33 STRUCT 16 8 0 noalg "struct { F uintptr; X0 int }" "noalg.struct { F uintptr; X0 int }" 2
field 0 "F" t15 0 0
field 1 "X0" t11 8 0
aux a3 sym "type:noalg.struct { F uintptr; X0 int }" "type:noalg.struct { F uintptr; X0 int }" 0 - 0 - t33 - - 0
rtype 16 0 1151813130 25 "runtime.gcbits." ""
aux a4 sym "main.test1helper.deferwrap1" "main.test1helper.deferwrap1" 1 - 0 - - - - 0
type t34 PTR 8 8 8 hasptr,noalg,direct "*struct { F uintptr; X0 int }" "noalg.*struct { F uintptr; X0 int }" t33
type t35 RESULTS ? ? ? - "*struct { F uintptr; X0 int },mem" "" 2 t34,t28
aux a6 sym "runtime.mallocgcSmallNoScanSC2" "runtime.mallocgcSmallNoScanSC2" 1 - 0 - - - - 0
aux a5 call "AuxCall{runtime.mallocgcSmallNoScanSC2}" a6 1 3 1 8 24 3 1
abiparam in 0 t15 - 0 0
abiparam in 1 t17 - 1 8
abiparam in 2 t2 - 2 16
abiparam out 0 t34 - 0 -1
aux a7 type "uintptr" t15
aux a8 type "int" t11
aux a10 sym "runtime.deferproc" "runtime.deferproc" 1 - 0 - - - - 0
aux a9 call "AuxCall{runtime.deferproc}" a10 1 1 0 8 8 1 0
abiparam in 0 t15 - 0 0
aux a12 sym "runtime.deferreturn" "runtime.deferreturn" 1 - 0 - - - - 0
aux a11 call "AuxCall{runtime.deferreturn}" a12 1 0 0 8 0 0 0
aux a13 call "AuxCall{runtime.deferreturn}" a12 1 0 0 8 0 0 0
aux a14 name "i" "i" PAUTO t11 0 1 used p2:18:6:0:0
slot s1 a14 t11 0 - 0
f b1 t1 a1 37 7
typs Bool=t2,Int8=t3,Int16=t4,Int32=t5,Int64=t6,UInt8=t7,UInt16=t8,UInt32=t9,UInt64=t10,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Plain p2:18:2:0:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 2 v4,v32
v v7 Less64 t2 0 - p2:18:16:0:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b6:0,b7:0 b2:0
v v8 Copy t11 0 - p2:19:3:2:0 2 v5
v v12 Copy t28 0 - p2:19:3:2:0 1 v37
v v13 StaticLECall t35 40 a5 p2:19:3:0:0 2 v10,v9,v11,v12
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v8,v19
v v23 Copy t1 0 - p2:19:3:2:0 1 v15
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v23,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b6:0
v v30 Copy t11 0 - p2:18:23:2:0 1 v8
v v32 Add64 t11 0 - p2:18:23:0:0 1 v30,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v33 Copy t28 0 - p2:21:1:2:0 1 v37
v v34 StaticLECall t32 8 a11 p2:21:1:0:0 1 v33
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 Plain p2:18:23:2:0 0 0 - - b4:0 b3:0
b b7 Ret p2:21:1:0:0 0 0 - v29 - b3:1
v v26 Copy t28 0 - p2:21:1:2:0 1 v25
v v27 StaticLECall t32 8 a13 p2:21:1:0:0 1 v26
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:0:0 1 v28
names s1
named s1 v4,v5,v8,v30,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev -
freeb -
dcllen 3
end
pass 1 "number lines"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 2 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b6:0,b7:0 b2:0
v v8 Copy t11 0 - p2:19:3:2:0 2 v5
v v12 Copy t28 0 - p2:19:3:2:0 1 v37
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v12
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v8,v19
v v23 Copy t1 0 - p2:19:3:2:0 1 v15
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v23,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b6:0
v v30 Copy t11 0 - p2:18:23:2:0 1 v8
v v32 Add64 t11 0 - p2:18:23:1:0 1 v30,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v33 Copy t28 0 - p2:21:1:2:0 1 v37
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v33
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 Plain p2:19:3:0:0 0 0 - - b4:0 b3:0
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v26 Copy t28 0 - p2:21:1:2:0 1 v25
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v26
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v8,v30,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:18:21
dcllen 3
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 5 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 4 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b6:0,b7:0 b2:0
v v8 Copy t11 0 - p2:19:3:2:0 0 v5
v v12 Copy t28 0 - p2:19:3:2:0 0 v37
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 4 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v23 Copy t1 0 - p2:19:3:2:0 0 v15
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 3 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b6:0
v v30 Copy t11 0 - p2:18:23:2:0 0 v5
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v33 Copy t28 0 - p2:21:1:2:0 0 v37
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 Plain p2:19:3:0:0 0 0 - - b4:0 b3:0
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v26 Copy t28 0 - p2:21:1:2:0 0 v25
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v5,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev -
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:18:21
dcllen 3
end
pass 3 "early deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b6:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b6:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 Plain p2:19:3:0:0 0 0 - - b4:0 b3:0
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v26,v33,v30,v23,v12,v8,v2
freeb -
cache postorder b4,b6,b7,b3,b5,b2,b1
cache linestarts 2:18:21
dcllen 3
end
pass 4 "short circuit"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 BlockInvalid p2:19:3:0:0 0 0 - - - -
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v26,v33,v30,v23,v12,v8,v2
freeb -
cache linestarts 2:18:21
dcllen 3
end
pass 5 "decompose user"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b6 BlockInvalid p2:19:3:0:0 0 0 - - - -
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v26,v33,v30,v23,v12,v8,v2
freeb -
cache linestarts 2:18:21
dcllen 3
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 2 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v17 NilCheck t34 0 - p2:19:3:0:0 1 v15,v14
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v17
v v19 Store t28 0 a7 p2:19:3:0:0 2 v18,v16,v14
v v20 NilCheck t34 0 - p2:19:3:0:0 1 v15,v19
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v20
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v26,v33,v30,v23,v12,v8,v2
freeb b6
cache linestarts 2:18:21
dcllen 3
end
pass 7 "opt"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache linestarts 2:18:21
dcllen 3
end
pass 8 "zero arg cse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache linestarts 2:18:21
dcllen 3
end
pass 9 "opt deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache linestarts 2:18:21
dcllen 3
end
pass 10 "generic cse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 11 "phiopt"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 12 "gcse deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 13 "nilcheckelim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 14 "prove"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 15 "divisible"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 16 "divmod"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 17 "middle opt"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 18 "known bits"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 19 "early fuse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticLECall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:0:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticLECall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticLECall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticLECall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 20 "expand calls"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v20 SP t15 0 - p0:0:0:0:0 0 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 21 "decompose builtin"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v20 SP t15 0 - p0:0:0:0:0 0 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 22 "softfloat"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v20 SP t15 0 - p0:0:0:0:0 0 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 23 "branchelim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v20 SP t15 0 - p0:0:0:0:0 0 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 24 "late opt"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 25 "dead auto elim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v20,v17,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 26 "sccp"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
v v20 ConstBool t2 1 - p2:18:16:1:0 0 -
v v17 Const64 t11 1 - p2:18:23:1:0 0 -
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 27 "generic deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 28 "late fuse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 29 "check bce"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 30 "dse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 31 "memcombine"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 32 "writebarrier"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 Const64 t11 0 - p0:0:0:0:0 1 -
v v6 Const64 t11 10 - p0:0:0:0:0 1 -
v v10 Const64 t15 16 - p0:0:0:0:0 1 -
v v11 ConstBool t2 1 - p0:0:0:0:0 1 -
v v31 Const64 t11 1 - p0:0:0:0:0 1 -
v v9 Addr t17 0 a3 p0:0:0:0:0 1 v3
v v16 Addr t15 0 a4 p0:0:0:0:0 1 v3
b b2 If p2:18:18:0:0 1 0 - v7 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v7 Less64 t2 0 - p2:18:16:1:0 1 v5,v6
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 StaticCall t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v18 OffPtr t21 0 - p2:19:3:0:0 1 v15
v v21 OffPtr t20 8 - p2:19:3:0:0 1 v15
v v19 Store t28 0 a7 p2:19:3:0:0 1 v18,v16,v14
v v22 Store t28 0 a8 p2:19:3:0:0 1 v21,v5,v19
v v24 StaticCall t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 Add64 t11 0 - p2:18:23:1:0 1 v5,v31
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 StaticCall t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 StaticCall t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts 0=v4,1=v11,v31,10=v6,16=v10
freev v17,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21:18=0
dcllen 3
end
pass 33 "lower"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDconst t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v19 ARM64MOVDstore t28 0 - p2:19:3:0:0 1 v15,v16,v14
v v22 ARM64MOVDstore t28 8 - p2:19:3:0:0 1 v15,v5,v19
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 34 "addressing modes"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64MOVDconst t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v19 ARM64MOVDstore t28 0 - p2:19:3:0:0 1 v15,v16,v14
v v22 ARM64MOVDstore t28 8 - p2:19:3:0:0 1 v15,v5,v19
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 35 "late lower"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 3 v13
v v19 ARM64MOVDstore t28 0 - p2:19:3:0:0 1 v15,v16,v14
v v22 ARM64MOVDstore t28 8 - p2:19:3:0:0 1 v15,v5,v19
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 36 "pair"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v22 Copy t28 0 - p2:19:3:0:0 1 v19
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v22
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 38 "lowered cse"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 39 "elim unread autos"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 41 "lowered deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 42 "checkLower"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 43 "loop invariant"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 45 "tighten"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 46 "late deadcode"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 47 "critical"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 48 "phi tighten"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 49 "likelyadjust"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b5:b2,b7:b3
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b5:b2:-:b3:8:11,b7:b3:-:b4:17:20
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
dcllen 3
end
pass 50 "layout"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
fstate laidout
dcllen 3
end
pass 51 "schedule"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
fstate scheduled,laidout
dcllen 3
end
pass 52 "late nilcheck"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
fstate scheduled,laidout
dcllen 3
end
pass 53 "flagalloc"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v16 ARM64MOVDaddr t15 0 a4 p0:0:0:0:0 1 v3
v v9 ARM64MOVDaddr t17 0 a3 p0:0:0:0:0 1 v3
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v11 ARM64MOVDconst t2 1 - p0:0:0:0:0 1 -
v v10 ARM64MOVDconst t15 16 - p0:0:0:0:0 1 -
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 3 v4,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v10,v9,v11,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v16,v5,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v5
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v22,v21,v18,v7,v31,v6,v20,v26,v33,v30,v23,v12,v8,v2
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:0 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
fstate scheduled,laidout
dcllen 3
end
pass 54 "regalloc"
aux a5 call "AuxCall{runtime.mallocgcSmallNoScanSC2}" a6 1 3 1 8 24 3 1
abiparam in 0 t15 - 0 0
abiparam in 1 t17 - 1 8
abiparam in 2 t2 - 2 16
abiparam out 0 t34 - 0 -1
callreg 0:1,1:2,2:4 0:1 7fffffff97ffffff -
aux a9 call "AuxCall{runtime.deferproc}" a10 1 1 0 8 8 1 0
abiparam in 0 t15 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v26 Copy t11 0 - p2:18:16:2:0 1 v4
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 2 v26,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v31 StoreReg t11 0 - p2:18:16:0:0 2 v5
v v22 ARM64MOVDconst t15 16 - p2:19:3:2:0 1 -
v v21 ARM64MOVDaddr t17 0 a3 p2:19:3:2:0 1 v3
v v18 ARM64MOVDconst t2 1 - p2:19:3:2:0 1 -
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v22,v21,v18,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v7 ARM64MOVDaddr t15 0 a4 p2:19:3:2:0 1 v3
v v6 LoadReg t11 0 - p2:19:3:2:0 1 v31
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v7,v6,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v20 LoadReg t11 0 - p2:18:23:2:0 1 v31
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v20
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v2,v8,v12,v23,v30,v33
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b2:b1,b3:b2,b4:b3,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b4:b3:-:-:23:26,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:1 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
fstate scheduled,laidout
regalloc 33 v3:SB,v4:ZERO,v5:R0,v6:R4,v7:R3,v13:[R0],v15:R0,v18:R2,v20:R3,v21:R1,v22:R0,v24:[],v26:R0,v31:@a14/t11/0/-/0,v32:R0
dcllen 3
end
pass 55 "loop rotate"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v26 Copy t11 0 - p2:18:16:2:0 1 v4
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v20 LoadReg t11 0 - p2:18:23:2:0 1 v31
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v20
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 2 v26,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v31 StoreReg t11 0 - p2:18:16:0:0 2 v5
v v22 ARM64MOVDconst t15 16 - p2:19:3:2:0 1 -
v v21 ARM64MOVDaddr t17 0 a3 p2:19:3:2:0 1 v3
v v18 ARM64MOVDconst t2 1 - p2:19:3:2:0 1 -
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v22,v21,v18,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v7 ARM64MOVDaddr t15 0 a4 p2:19:3:2:0 1 v3
v v6 LoadReg t11 0 - p2:19:3:2:0 1 v31
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v7,v6,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v2,v8,v12,v23,v30,v33
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b4:b3,b2:b1,b3:b2,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b4:b3:-:-:23:26,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:1 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
hotness b4:3
fstate scheduled,laidout
regalloc 33 v3:SB,v4:ZERO,v5:R0,v6:R4,v7:R3,v13:[R0],v15:R0,v18:R2,v20:R3,v21:R1,v22:R0,v24:[],v26:R0,v31:@a14/t11/0/-/0,v32:R0
dcllen 3
end
pass 56 "trim"
f b1 t1 a1 37 7
b b1 Plain p2:18:2:1:0 0 0 - - b2:0 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v1 InitMem t28 0 - p0:0:0:0:0 1 -
v v4 ARM64ZERO t11 0 - p0:0:0:0:0 1 -
v v26 Copy t11 0 - p2:18:16:2:0 1 v4
b b4 Plain p2:18:23:0:0 0 0 - - b2:1 b3:0
v v20 LoadReg t11 0 - p2:18:23:2:0 1 v31
v v32 ARM64ADDconst t11 1 - p2:18:23:1:0 1 v20
b b2 ARM64LT p2:18:18:0:0 1 0 - v17 b3:0,b5:0 b1:0,b4:0
v v5 Phi t11 0 - p2:18:16:0:0 2 v26,v32
v v37 Phi t28 0 - p2:18:16:0:0 2 v1,v25
v v17 ARM64CMPconst t29 10 - p2:18:16:1:0 1 v5
b b3 Defer p2:19:3:0:0 1 0 - v24 b4:0,b7:0 b2:0
v v31 StoreReg t11 0 - p2:18:16:0:0 2 v5
v v22 ARM64MOVDconst t15 16 - p2:19:3:2:0 1 -
v v21 ARM64MOVDaddr t17 0 a3 p2:19:3:2:0 1 v3
v v18 ARM64MOVDconst t2 1 - p2:19:3:2:0 1 -
v v13 ARM64CALLstatic t35 40 a5 p2:19:3:1:0 2 v22,v21,v18,v37
v v15 SelectN t34 0 - p2:19:3:1:0 2 v13
v v14 SelectN t28 1 - p2:19:3:0:0 1 v13
v v7 ARM64MOVDaddr t15 0 a4 p2:19:3:2:0 1 v3
v v6 LoadReg t11 0 - p2:19:3:2:0 1 v31
v v19 ARM64STP t28 0 - p2:19:3:0:0 1 v15,v7,v6,v14
v v24 ARM64CALLstatic t32 8 a9 p2:19:3:0:0 2 v15,v19
v v25 SelectN t28 0 - p2:19:3:0:0 2 v24
b b7 Ret p2:21:1:1:0 0 0 - v29 - b3:1
v v27 ARM64CALLstatic t32 8 a13 p2:21:1:1:0 1 v25
v v28 SelectN t28 0 - p2:21:1:0:0 1 v27
v v29 MakeResult t32 0 - p2:19:3:1:0 1 v28
b b5 Ret p2:21:1:0:0 0 0 - v36 - b2:1
v v34 ARM64CALLstatic t32 8 a11 p2:21:1:1:0 1 v37
v v35 SelectN t28 0 - p2:21:1:0:0 1 v34
v v36 MakeResult t32 0 - p2:21:1:0:0 1 v35
names s1
named s1 v4,v5,v32
splits -
canon a14/t11/0/-/0=s1
consts -
freev v2,v8,v12,v23,v30,v33
freeb b6
cache postorder b4,b7,b3,b5,b2,b1
cache idom b1:-,b4:b3,b2:b1,b3:b2,b7:b3,b5:b2
cache sdom b1:-:b2:-:2:35,b4:b3:-:-:23:26,b2:b1:b5:-:5:32,b3:b2:b7:-:14:29,b7:b3:-:b4:17:20,b5:b2:-:b3:8:11
cache loopnest 8 0 b2:-:3:1:1:1 b2:0,b3:0,b4:0
cache auxmap -:1,a3:2,a4:3
cache linestarts 2:18:21
hotness b4:3
fstate scheduled,laidout
regalloc 33 v3:SB,v4:ZERO,v5:R0,v6:R4,v7:R3,v13:[R0],v15:R0,v18:R2,v20:R3,v21:R1,v22:R0,v24:[],v26:R0,v31:@a14/t11/0/-/0,v32:R0
dcllen 3
end
frontend
end
ptrcache t4,t5,t6,t7,t9,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t3,t7,t4,t8,t5,t9,t6,t10,t11,t14,t15,t25,t26,t12,t13,t2,t17,t18,t19,t20,t21,t22,t23,t24,t34,t1,t33,t16,t27,t28,t30,t29,t31,t32,t35
eof
"#

/-- `test/defer/main/test1helper,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "main"
func "test1helper" 1
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
name n1 "i" PAUTO t1 1 "main.i" 0 a14
name n2 ".autotmp_1" PAUTO t1 1 "main..autotmp_1" 0 -
type t2 8 8 8 1 01 "*struct { F uintptr; X0 int }"
name n3 ".autotmp_2" PAUTO t2 3 "main..autotmp_2" 0 -
in n1 0 used
in n2 0 used,autotmp
in n3 0 used,autotmp
out n1 -8 used
opt n3 0 autotmp
opt n2 0 autotmp
stack 8 0 8
end
genin
posbase p2 "./defer.go" 1 1 -1 1 "./defer.go" "./defer.go" 1 1
sym y1 "main.test1helper" 1
curfn p2:17:6:0:0 1 1
regargs -
text y1 0 0 0 0 17 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "main.i" 0
sym y4 "type:noalg.struct { F uintptr; X0 int }" 0
sym y5 "runtime.mallocgcSmallNoScanSC2" 1
sym y6 "main.test1helper.deferwrap1" 1
sym y7 "runtime.deferproc" 1
sym y8 "runtime.deferreturn" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i0 0 0 p2:17:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:17:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p2:17:6:0:0
p 3 3 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:18:16:1:0
p 4 4 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@7 0 0 p2:18:2:2:0
p 5 5 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y3/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p2:18:23:1:0
p 6 6 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8195 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:18:23:2:0
p 7 7 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/10/-/- 8192 - _ 0 0 p2:18:16:1:0
p 8 8 0 0 0 - BGE 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@22 0 0 p2:18:18:2:0
p 9 9 0 0 0 - MOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y3/- 0 0 p2:18:16:2:0
p 10 10 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/16/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2:19:3:1:0
p 11 11 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y4/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2:19:3:2:0
p 12 12 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/1/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2:19:3:2:0
p 13 13 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2:19:3:1:0
p 14 14 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p2:19:3:1:0
p 15 15 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y6/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p2:19:3:2:0
p 16 16 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y3/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p2:19:3:2:0
p 17 17 0 0 0 - STP 0 REGREG/8195/0/0/NONE/0/8196/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 0 0 p2:19:3:2:0
p 18 18 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y7/- 0 0 p2:19:3:2:0
p 19 19 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@5 0 0 p2:19:3:2:0
p 20 20 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p2:21:1:1:0
p 21 21 0 0 0 - RET 0 _ 0 - _ 0 0 p2:21:1:2:0
p 22 22 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p2:21:1:1:0
p 23 23 0 0 0 - RET 0 _ 0 - _ 0 0 p2:21:1:0:0
p 24 24 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 17 200080
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgvar 0 n1 0
dbgloc 0 1:26:-1:-30000:50
dbgregout -
dbgpc 1:26:4
end
asm
sym y9 "runtime.morestack_noctxt" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/64/-/i0 0 0 p2:17:6:0:0
p 25 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 26 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:17:6:0:0
p 27 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:17:6:0:0
p 28 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@39 0 0 p2:17:6:0:0
p 29 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 30 12 64 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-64/-/- 0 0 p2:17:6:0:1
p 31 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p2:17:6:0:0
p 32 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:17:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p2:17:6:0:0
p 3 24 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:18:16:1:0
p 4 28 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/7/-/@7 0 0 p2:18:2:2:0
p 5 32 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y3/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:18:23:1:0
p 6 36 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8195 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:18:23:2:0
p 7 40 0 0 96 - CMP 0 CONST/0/0/0/NONE/18/10/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:18:16:1:0
p 8 44 0 0 80 - BGE 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/22/-/@22 0 0 p2:18:18:2:0
p 9 48 0 0 304 - MOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y3/- 0 0 p2:18:16:2:0
p 10 52 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/16/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2:19:3:1:0
p 11 56 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y4/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2:19:3:2:0
p 12 64 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/1/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2:19:3:2:0
p 13 68 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2:19:3:1:0
p 14 68 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y5/- 0 0 p2:19:3:1:0
p 15 72 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y6/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:19:3:2:0
p 16 80 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y3/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p2:19:3:2:0
p 17 84 0 0 436 - STP 0 REGREG/8195/0/0/NONE/7/8196/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 0 0 p2:19:3:2:0
p 18 88 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y7/- 0 0 p2:19:3:2:0
p 19 92 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/5/-/@5 0 0 p2:19:3:2:0
p 20 96 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p2:21:1:1:0
p 21 100 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:21:1:2:0
p 33 104 -64 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/64/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:21:1:2:0
p 34 108 64 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:21:1:2:0
p 22 112 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p2:21:1:1:0
p 23 116 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p2:21:1:0:0
p 35 120 -64 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/64/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p2:21:1:0:0
p 36 124 64 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p2:21:1:0:0
p 37 128 -64 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2:21:1:0:0
p 38 128 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 39 128 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2:17:6:0:0
p 40 128 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p2:17:6:0:0
p 41 132 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y9/- 0 0 p2:17:6:0:0
p 42 136 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p2:17:6:0:0
p 43 136 64 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@25 0 0 p2:17:6:0:0
fn y1 0 56 0 0 17 200080
funcaux y2 y2 - - - - -
text 144 0 900b40f9ff6330ebc9030054fe0f1cf8fd831ff8fd2300d1e0031faa03000014e31b40f9600400911f2800f12a020054e01b00f9e0037cb20100009021000091e20340b2000000940300009063000091e41b40f9031000a900000094f1ffff1700000094fd835ff8fe0744f8c0035fd600000094fd835ff8fe0744f8c0035fd6e3031eaa00000094deffff1700000000 7
reloc 56 8 R_ADDRARM64 0 y4
reloc 68 4 R_CALLARM64 0 y5
reloc 72 8 R_ADDRARM64 0 y6
reloc 88 4 R_CALLARM64 0 y7
reloc 96 4 R_CALLARM64 0 y8
reloc 112 4 R_CALLARM64 0 y8
reloc 132 4 R_CALLARM64 0 y9
pcln y12 y13 y14 y15 y10,y11 y2,y2
usedfiles 1
data y2 Sxxx 0 4 8000 0100000000000000 0
data y10 SRODATA 11 1 28000 00010102021d0102020200 0
data y11 SRODATA 7 1 28000 0011020f010400 0
data y12 SRODATA 13 1 28000 02048001177f018001037f0500 0
data y13 SRODATA 3 1 28000 042400 0
data y14 SRODATA 11 1 28000 24060207020b0408070400 0
data y15 SRODATA 3 1 28000 002400 0
end
dwarf
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "go:info.int" 0
dwfn y16 y17 y18 - y19 "main.test1helper" 1:17 1 0 1 9
dwdcl n1
dwclosure 0 -
dwmark p2:18:2:0:0 1
dwmark p2:20:2:0:0 0
dwparents 0
dwparams -
dwname n1 1 1 0 0 0 0 -8 0 - - "int" 0 0 1 p2:18:6:0:0
dwname n3 1 0 1 0 0 0 0 0 - - "noalg.*struct { F uintptr; X0 int }" 0 0 1 p2:19:3:0:0
dwname n2 1 0 1 0 0 0 0 0 - - "int" 0 0 1 p2:19:3:0:0
var 0 0 "i" 52 1 0 0 0 -16 y20 "./defer.go" 18 6 0 0 0 0 v0
scope 0 0 0:144 -
scope 1 0 24:96 0
data y16 SDWARFFCN 48 0 0 036d61696e2e746573743168656c70657200009001019c0200000011010c000000002769001200000000000000000000 4
reloc 18 1 R_DWTXTADDR_U1 0 y1
reloc 30 4 R_DWARFSECREF 0 y18
reloc 38 4 R_DWARFSECREF 0 y20
reloc 42 4 R_DWARFSECREF 0 y17
data y17 SDWARFLOC 9 0 0 0100041c9001015000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y18 SDWARFRANGE 6 0 0 010004186000 1
reloc 1 1 R_DWTXTADDR_U1 0 y1
data y19 SDWARFLINES 50 0 0 00090200000000000000000402030b140a878806370637063706370637066006370687063706081106370687ab0210000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `main.test1helper`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context the checks run on (`liveCtx`). -/
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

/-- The PC table `checkG58` computes: `b3`'s twelve values from Prog 9, its terminator (the `JMP`
to `b4`) at Prog 19; `b4` starts at Prog 5. -/
def tab : PcTab := [(1, [3, 3, 3, 3, 4]), (4, [5, 6, 7]), (2, [7, 7, 7, 8]),
  (3, [9, 10, 11, 12, 13, 15, 15, 15, 16, 17, 18, 19, 19]), (7, [20, 21, 21, 21]),
  (5, [22, 23, 23, 23])]

/-- The class table `checkG58` computes. -/
def kt : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- Block `b3`: `…`, `v24 = CALLstatic v15 v19`, `v25 = SelectN [0] v24`; `Defer v24`, successors
`b4`, `b7`. -/
def blk : Block := (lc.ctx.f.block? 3).getD default

/-- P0's layout: GenG2's, a 32-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- A `runLoc` state at `b3`'s terminator: every register `poison`, no live slot, the empty
memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 64 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine at `b3`'s terminator: the activation's `g` and `FP`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 3 blk.values.size, mem := fun _ => 0 }

/-- The home slots lie above the saved `LR` and below `2^64`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) &&
        decide (GenG2.sp0.toNat + (frameOff L nc off).toNat + 8 ≤ 2 ^ 64)
    | none => true

/-- What compiled evaluation checks on `main.test1helper`: `checkG58` accepts it with `tab` and
`kt`; `b3` is a `Defer` block of it; the Progs' IDs are below `2^32`; the home slots fit; no frame
variable is accessed; G35's table at `b3`'s end is empty; and `stepTermLoc` takes `b3` to `b4`. -/
def gFacts : Bool :=
  (checkG58 lc0 ps bs g).toOption == some (tab, kt) && lc.ctx.f.blocks.toList.contains 3 &&
    (lc.ctx.f.block? 3).isSome && blk.kind == .Defer && ps.toList.all (·.id < 2 ^ 32) &&
    slotsFit && (accessedVars lc).isEmpty && uL35 lc (uIn35 lc 3) blk blk.values.size == [] &&
    GenG1.okThen (stepTermLoc lc s0 blk) (fun r => GenG1.gotoIs r.1 4)

theorem g59d_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    checkG58 lc0 ps bs g = .ok (tab, kt) ∧ 3 ∈ lc.ctx.f.blocks.toList ∧
      lc.ctx.f.block? 3 = some blk ∧ blk.kind = .Defer ∧ (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧
      slotsFit = true ∧ (accessedVars lc).isEmpty = true ∧
      uL35 lc (uIn35 lc 3) blk blk.values.size = [] ∧
      GenG1.okThen (stepTermLoc lc s0 blk) (fun r => GenG1.gotoIs r.1 4) = true := by
  have hf := g59d_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    decide_eq_true_eq, List.all_eq_true] at hf
  obtain ⟨hres, hm3, hbs, hk, hlt, hfit, hav, hu, hrun⟩ := hf
  refine ⟨?_, hm3, ?_, hk, hlt, hfit, hav, hu, hrun⟩
  · revert hres; cases checkG58 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]

/-! ## The activation -/

theorem env59d (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hfit : slotsFit = true) : G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
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
            slot := fun k hk nc off hs => by simp [E, hk, hs]
            extra := by decide
            frame := by
              refine ⟨by decide, by decide, fun k off hk => ?_⟩
              simp only [E] at hk
              split at hk
              · rename_i hmem
                obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
                have := List.all_eq_true.1 hfit k hmem
                simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
                exact this
              · cases hk }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem locMatch0 : LocMatch E s0 3 blk.values.size m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem inv0 (K : KMap) : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c _ hv _ => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- **A `Defer` block under G58, on `test/defer/main.test1helper`** (`Cx.term`'s `Defer` arm,
`TermOK.defer`, `term_core`'s `Defer` case, through `g58_term`): `checkG58` accepts the function,
whose block `b3` is a `Defer` block; from `s0`, `stepTermLoc` goes to `b4` (successor 0: the
deferred call's registration returned), and `g58_term` relates it to a machine run of `b3`'s
`JMP` (Prog 19) to a state at `b4`'s start, matching the state after the step. -/
theorem genG59d_witness :
    checkG58 lc0 ps bs g = .ok (tab, kt) ∧ blk.kind = .Defer ∧
      ∃ e s1 m1, stepTermLoc lc s0 blk = .ok (.goto e, s1) ∧ e.b = 4 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E s1 4 0 m1 ∧ m1.pc = E.pcOf 4 0 := by
  obtain ⟨hc, hm3, hb, hk, hlt, hfit, hav, hu, hrun⟩ := facts
  obtain ⟨⟨n, s1⟩, hs1, hn⟩ := GenG1.okThen_spec hrun
  obtain ⟨e, rfl, he⟩ := GenG1.gotoIs_spec hn
  have hE := env59d hlt hav hfit
  -- `g58_term` reads the blocks of `lc0`: rewrite rather than unfold (the kernel would evaluate
  -- `lc0`).
  have hm0 : 3 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm3
  have hb0 : lc0.ctx.f.block? 3 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  obtain ⟨m1, hp1, hm1, -, -, -, -⟩ := g58_term (H := GenG2.H0) hc hE hm0 hb0 locMatch0 (inv0 _)
    (fun h => Bool.false_ne_true h)
    (fun h => by rcases h with h | h <;> rw [hk] at h <;> cases h)
    (by
      change UOKL m0 (uL35 lc (uIn35 lc 3) blk blk.values.size)
      rw [hu]
      intro x hx
      cases hx)
    hs1
  rw [he] at hm1
  exact ⟨hc, hk, e, s1, m1, hs1, he, hp1, hm1, hm1.pc⟩

end GoFV.Proof.Witness.GenG59d
