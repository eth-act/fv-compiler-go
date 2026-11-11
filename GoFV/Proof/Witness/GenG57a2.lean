import GoFV.Proof.Witness.GenG57a
import GoFV.Proof.Witness.GenG12

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG57a2

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/bootstrapRand,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "bootstrapRand" 1 0 0
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
type t2 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t1 FUNC 8 8 8 hasptr,direct "func() uint64" "func() uint64" 0 0 1
field 0 "" t2 ? 0
aux a2 sym "runtime.bootstrapRand" "runtime.bootstrapRand" 1 - 0 - - - - 0
posbase p173 "runtime/rand.go" 1 1 -1
aux a3 name "~r0" "~r0" PPARAMOUT t2 0 1 - p173:124:22:0:0
aux a1 call "AuxCall{runtime.bootstrapRand}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
type t3 BOOL 1 1 0 comparable,named "bool" "bool"
type t4 INT8 1 1 0 comparable,named "int8" "int8"
type t5 INT16 2 2 0 comparable,named "int16" "int16"
type t6 INT32 4 4 0 comparable,named "int32" "int32"
type t7 INT64 8 8 0 comparable,named "int64" "int64"
type t8 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t9 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t10 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t11 INT 8 8 0 comparable,named "int" "int"
type t12 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t13 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
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
posbase p2522 "runtime/lock_spinbit.go" 1 1 2249
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t2
type t37 STRUCT 0 1 0 comparable,named "lockRankStruct" "runtime.lockRankStruct" 0
type t36 STRUCT 8 8 0 comparable,named "mutex" "runtime.mutex" 2
field 0 "lockRankStruct" t37 0 1
field 1 "key" t15 0 0
type t39 UINT8 1 1 0 comparable,named "byte" "uint8"
type t38 ARRAY 32 1 0 comparable "[32]byte" "[32]uint8" t39 32
type t41 ARRAY 256 8 0 comparable "[32]uint64" "[32]uint64" t2 32
type t42 ARRAY 32 8 0 comparable "[4]uint64" "[4]uint64" t2 4
type t40 STRUCT 304 8 0 comparable,named "chacha8rand.State" "internal/chacha8rand.State" 5
field 0 "buf" t41 0 0
field 1 "seed" t42 256 0
field 2 "i" t10 288 0
field 3 "n" t10 292 0
field 4 "c" t10 296 0
type t35 STRUCT 352 8 0 comparable "struct { lock mutex; seed [32]byte; state chacha8rand.State; init bool }" "struct { runtime.lock runtime.mutex; runtime.seed [32]uint8; runtime.state internal/chacha8rand.State; runtime.init bool }" 4
field 0 "lock" t36 0 0
field 1 "seed" t38 8 0
field 2 "state" t40 40 0
field 3 "init" t3 344 0
type t34 PTR 8 8 8 hasptr,direct,comparable "*struct { lock mutex; seed [32]byte; state chacha8rand.State; init bool }" "*struct { runtime.lock runtime.mutex; runtime.seed [32]uint8; runtime.state internal/chacha8rand.State; runtime.init bool }" t35
aux a4 sym "runtime.globalRand" "runtime.globalRand" 0 - 0 - - - - 0
type t43 PTR 8 8 8 hasptr,direct,comparable "*mutex" "*runtime.mutex" t36
type t44 INT64 8 8 0 comparable,named "lockRank" "runtime.lockRank"
aux a5 str "randinit missed" "randinit missed" "go:string.\"randinit missed\""
aux a7 sym "runtime.lock2" "runtime.lock2" 1 - 0 - - - - 0
aux a6 call "AuxCall{runtime.lock2}" a7 1 1 0 8 8 1 0
abiparam in 0 t43 - 0 0
posbase p2526 "runtime/lockrank_off.go" 1 1 2253
type t45 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t3
aux a9 sym "runtime.fatal" "runtime.fatal" 1 - 0 - - - - 0
aux a8 call "AuxCall{runtime.fatal}" a9 1 1 0 8 16 2 0
abiparam in 0 t16 - 0,1 0
posbase p2523 "internal/chacha8rand/chacha8.go" 1 1 2250
type t46 PTR 8 8 8 hasptr,direct,comparable "*chacha8rand.State" "*internal/chacha8rand.State" t40
type t47 RESULTS ? ? ? - "uint64,mem" "" 2 t2,t28
aux a10 type "uint32" t10
type t48 PTR 8 8 8 hasptr,direct,comparable "*[32]uint64" "*[32]uint64" t41
aux a12 sym "internal/chacha8rand.(*State).Refill" "internal/chacha8rand.(*State).Refill" 1 - 0 - - - - 0
aux a11 call "AuxCall{internal/chacha8rand.(*State).Refill}" a12 1 1 0 8 8 1 0
abiparam in 0 t46 - 0 0
posbase p2524 "runtime/lock_spinbit.go" 1 1 2251
aux a14 sym "runtime.unlock2" "runtime.unlock2" 1 - 0 - - - - 0
aux a13 call "AuxCall{runtime.unlock2}" a14 1 1 0 8 8 1 0
abiparam in 0 t43 - 0 0
posbase p2527 "runtime/lockrank_off.go" 1 1 2254
aux a15 name "l" "l" PAUTO t43 0 1 used p2522:160:11:0:0
slot s1 a15 t43 0 - 0
posbase p2525 "runtime/lockrank_off.go" 1 1 2252
aux a16 name "~r0" "~r0" PAUTO t44 0 1 - p2525:19:28:0:0
slot s2 a16 t44 0 - 0
aux a17 name "l" "l" PAUTO t43 0 1 used p2526:23:19:0:0
slot s3 a17 t43 0 - 0
aux a18 name "rank" "rank" PAUTO t44 0 1 - p2526:23:29:0:0
slot s4 a18 t44 0 - 0
aux a19 name "chacha8rand.s" "s" PAUTO t46 0 1 used p2523:54:7:0:0
slot s5 a19 t46 0 - 0
aux a20 name "~r0" "~r0" PAUTO t2 0 1 - p2523:54:25:0:0
slot s6 a20 t2 0 - 0
aux a21 name "~r1" "~r1" PAUTO t3 0 1 - p2523:54:33:0:0
slot s7 a21 t3 0 - 0
aux a22 name "chacha8rand.i" "i" PAUTO t10 0 1 used p2523:55:2:0:0
slot s8 a22 t10 0 - 0
aux a23 name "x" "x" PAUTO t2 0 1 used p173:130:6:0:0
slot s9 a23 t2 0 - 0
aux a24 name "ok" "ok" PAUTO t3 0 1 used p173:130:9:0:0
slot s10 a24 t3 0 - 0
aux a25 name "l" "l" PAUTO t43 0 1 used p2524:269:13:0:0
slot s11 a25 t43 0 - 0
aux a26 name "l" "l" PAUTO t43 0 1 used p2527:35:21:0:0
slot s12 a26 t43 0 - 0
f b1 t1 a1 77 17
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t2,Int=t11,Float32=t12,Float64=t13,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 Plain p2522:161:29:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v9 Const64 t11 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 2252 - p2522:161:29:1:0 0 v1
v v11 Const64 t44 0 - p0:0:0:0:0 1 -
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v50 Const64 t11 32 - p0:0:0:0:0 0 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
b b2 Plain p2522:161:14:0:0 0 0 - - b3:0 b1:0
v v12 Copy t43 0 - p2522:161:14:2:0 1 v7
v v13 Copy t44 0 - p2522:161:14:2:0 0 v11
v v14 Copy t28 0 - p2522:161:14:2:0 2 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v14
v v16 StaticLECall t32 8 a6 p2526:24:7:0:0 1 v12,v14
v v17 SelectN t28 0 - p2526:24:7:0:0 1 v16
b b3 Plain p173:126:16:0:0 0 0 - - b4:0 b2:0
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 b3:0
v v19 OffPtr t45 344 - p173:126:16:0:0 1 v18
v v20 Copy t28 0 - p173:126:16:2:0 3 v17
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v20
b b5 Plain p173:130:25:0:0 0 0 - - b7:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:0:0 1 v20,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v23 Copy t28 0 - p173:127:8:2:0 1 v20
v v24 StaticLECall t32 16 a8 p173:127:8:0:0 1 v22,v23
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 Plain p173:130:25:0:0 0 0 - - b8:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 1 v77,v71
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b11:0 b7:0
v v27 OffPtr t46 40 - p173:130:25:0:0 3 v26
v v29 Copy t28 0 - p173:130:36:2:0 7 v76
v v30 InlMark t30 2250 - p173:130:36:1:0 0 v29
v v31 NilCheck t46 0 - p2523:55:8:0:0 1 v27,v29
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 2 v32,v29
v v34 NilCheck t46 0 - p2523:56:11:0:0 1 v27,v29
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v29
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:0:0 0 0 - - b7:1 b14:0
b b10 Ret p173:136:1:0:0 0 0 - v74 - -
v v72 Unknown t2 0 - p173:136:1:2:0 1 -
v v73 Unknown t28 0 - p173:136:1:2:0 1 -
v v74 MakeResult t47 0 - p173:136:1:0:0 1 v72,v73
b b11 Plain p173:130:36:1:0 0 0 - - b13:1 b8:1
v v38 Copy t10 0 - p2523:59:10:2:0 2 v33
v v40 Add32 t10 0 - p2523:59:10:0:0 1 v38,v39
v v41 Copy t46 0 - p2523:59:3:2:0 2 v27
v v42 Copy t28 0 - p2523:59:3:2:0 2 v29
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v41,v42
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 3 v44,v40,v42
v v46 NilCheck t46 0 - p2523:60:10:0:0 1 v41,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v38,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
b b12 Plain p173:130:36:1:0 0 0 - - b13:0 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b15:0,b14:0 b12:0,b11:0
v v55 Phi t2 0 - p173:130:12:0:0 1 v5,v53
v v56 Phi t3 0 - p173:130:12:0:0 1 v28,v54
v v75 Phi t28 0 - p173:130:12:0:0 2 v29,v45
b b14 Plain p173:134:13:0:0 0 0 - - b9:0 b13:1
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v69 Copy t28 0 - p173:134:26:2:0 1 v75
v v70 StaticLECall t32 8 a11 p173:134:26:0:0 1 v68,v69
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b15 Plain p2524:270:16:0:0 0 0 - - b16:0 b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v59 Copy t28 0 - p173:131:10:2:0 3 v75
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v59
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v59
v v62 StaticLECall t32 8 a13 p2527:36:9:0:0 1 v58,v59
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
b b16 Plain p173:132:4:2:0 0 0 - - b17:0 b15:0
b b17 Ret p173:132:4:1:0 0 0 - v66 - b16:0
v v64 Copy t2 0 - p173:132:4:2:0 1 v55
v v65 Copy t28 0 - p173:132:4:2:0 1 v63
v v66 MakeResult t47 0 - p173:132:4:0:0 1 v64,v65
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7,v12
named s2 v11,v13
named s3 v12
named s4 v13
named s5 v27,v41
named s6 v5,v5,v53,v55
named s7 v28,v28,v54,v56
named s8 v33,v38
named s9 v55,v64
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v9,v11,v28,1=v39,v54,31=v48,32=v50
freev -
freeb -
dcllen 16
end
pass 1 "number lines"
f b1 t1 a1 77 17
b b1 Plain p2522:161:29:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v9 Const64 t11 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 2252 - p2522:161:29:1:0 0 v1
v v11 Const64 t44 0 - p0:0:0:0:0 1 -
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v50 Const64 t11 32 - p0:0:0:0:0 0 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
b b2 Plain p2522:161:14:1:0 0 0 - - b3:0 b1:0
v v12 Copy t43 0 - p2522:161:14:2:0 1 v7
v v13 Copy t44 0 - p2522:161:14:2:0 0 v11
v v14 Copy t28 0 - p2522:161:14:2:0 2 v1
v v15 InlMark t30 2253 - p2522:161:14:0:0 0 v14
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v12,v14
v v17 SelectN t28 0 - p2526:24:7:0:0 1 v16
b b3 Plain p173:126:16:1:0 0 0 - - b4:0 b2:0
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 b3:0
v v19 OffPtr t45 344 - p173:126:16:0:0 1 v18
v v20 Copy t28 0 - p173:126:16:2:0 3 v17
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v20
b b5 Plain p173:130:25:1:0 0 0 - - b7:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v20,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v23 Copy t28 0 - p173:127:8:2:0 1 v20
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v23
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 Plain p173:130:25:1:0 0 0 - - b8:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 1 v77,v71
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b11:0 b7:0
v v27 OffPtr t46 40 - p173:130:25:0:0 3 v26
v v29 Copy t28 0 - p173:130:36:2:0 7 v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v29
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v29
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 2 v32,v29
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v29
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v29
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b7:1 b14:0
b b10 Ret p173:136:1:0:0 0 0 - v74 - -
v v72 Unknown t2 0 - p173:136:1:2:0 1 -
v v73 Unknown t28 0 - p173:136:1:2:0 1 -
v v74 MakeResult t47 0 - p173:136:1:0:0 1 v72,v73
b b11 Plain p173:130:36:1:0 0 0 - - b13:1 b8:1
v v38 Copy t10 0 - p2523:59:10:2:0 2 v33
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v38,v39
v v41 Copy t46 0 - p2523:59:3:2:0 2 v27
v v42 Copy t28 0 - p2523:59:3:2:0 2 v29
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v41,v42
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 3 v44,v40,v42
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v41,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v38,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
b b12 Plain p173:130:36:1:0 0 0 - - b13:0 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b15:0,b14:0 b12:0,b11:0
v v55 Phi t2 0 - p173:130:12:0:0 1 v5,v53
v v56 Phi t3 0 - p173:130:12:0:0 1 v28,v54
v v75 Phi t28 0 - p173:130:12:0:0 2 v29,v45
b b14 Plain p173:134:13:0:0 0 0 - - b9:0 b13:1
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v69 Copy t28 0 - p173:134:26:2:0 1 v75
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v69
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b15 Plain p2524:270:16:1:0 0 0 - - b16:0 b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v59 Copy t28 0 - p173:131:10:2:0 3 v75
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v59
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v59
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v59
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
b b16 Plain p2524:270:16:1:0 0 0 - - b17:0 b15:0
b b17 Ret p173:132:4:1:0 0 0 - v66 - b16:0
v v64 Copy t2 0 - p173:132:4:2:0 1 v55
v v65 Copy t28 0 - p173:132:4:2:0 1 v63
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v64,v65
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7,v12
named s2 v11,v13
named s3 v12
named s4 v13
named s5 v27,v41
named s6 v5,v5,v53,v55
named s7 v28,v28,v54,v56
named s8 v33,v38
named s9 v55,v64
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v9,v11,v28,1=v39,v54,31=v48,32=v50
freev -
freeb -
cache postorder b17,b16,b15,b9,b14,b13,b12,b11,b8,b7,b5,b6,b4,b3,b2,b1
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 77 17
b b1 Plain p2522:161:29:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 6 -
v v2 SP t15 0 - p0:0:0:0:0 1 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v4 LocalAddr t33 0 a3 p0:0:0:0:0 0 v2,v1
v v5 Const64 t2 0 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v9 Const64 t11 0 - p0:0:0:0:0 0 -
v v10 InlMark t30 2252 - p2522:161:29:1:0 0 v1
v v11 Const64 t44 0 - p0:0:0:0:0 1 -
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v50 Const64 t11 32 - p0:0:0:0:0 0 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
b b2 Plain p2522:161:14:1:0 0 0 - - b3:0 b1:0
v v12 Copy t43 0 - p2522:161:14:2:0 0 v7
v v13 Copy t44 0 - p2522:161:14:2:0 0 v11
v v14 Copy t28 0 - p2522:161:14:2:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:0:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 5 v16
b b3 Plain p173:126:16:1:0 0 0 - - b4:0 b2:0
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 b3:0
v v19 OffPtr t45 344 - p173:126:16:0:0 1 v18
v v20 Copy t28 0 - p173:126:16:2:0 0 v17
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b7:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v23 Copy t28 0 - p173:127:8:2:0 0 v17
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 Plain p173:130:25:1:0 0 0 - - b8:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 10 v77,v71
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b11:0 b7:0
v v27 OffPtr t46 40 - p173:130:25:0:0 5 v26
v v29 Copy t28 0 - p173:130:36:2:0 0 v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 4 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b7:1 b14:0
b b10 Ret p173:136:1:0:0 0 0 - v74 - -
v v72 Unknown t2 0 - p173:136:1:2:0 1 -
v v73 Unknown t28 0 - p173:136:1:2:0 1 -
v v74 MakeResult t47 0 - p173:136:1:0:0 1 v72,v73
b b11 Plain p173:130:36:1:0 0 0 - - b13:1 b8:1
v v38 Copy t10 0 - p2523:59:10:2:0 0 v33
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v41 Copy t46 0 - p2523:59:3:2:0 0 v27
v v42 Copy t28 0 - p2523:59:3:2:0 0 v76
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 3 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
b b12 Plain p173:130:36:1:0 0 0 - - b13:0 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b15:0,b14:0 b12:0,b11:0
v v55 Phi t2 0 - p173:130:12:0:0 2 v5,v53
v v56 Phi t3 0 - p173:130:12:0:0 1 v28,v54
v v75 Phi t28 0 - p173:130:12:0:0 6 v76,v45
b b14 Plain p173:134:13:0:0 0 0 - - b9:0 b13:1
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v69 Copy t28 0 - p173:134:26:2:0 0 v75
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b15 Plain p2524:270:16:1:0 0 0 - - b16:0 b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v59 Copy t28 0 - p173:131:10:2:0 0 v75
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v75
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v75
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v75
v v63 SelectN t28 0 - p2527:36:9:0:0 2 v62
b b16 Plain p2524:270:16:1:0 0 0 - - b17:0 b15:0
b b17 Ret p173:132:4:1:0 0 0 - v66 - b16:0
v v64 Copy t2 0 - p173:132:4:2:0 0 v55
v v65 Copy t28 0 - p173:132:4:2:0 0 v63
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v55,v63
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7,v7
named s2 v11,v11
named s3 v7
named s4 v11
named s5 v27,v27
named s6 v5,v5,v53,v55
named s7 v28,v28,v54,v56
named s8 v33,v33
named s9 v55,v55
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v9,v11,v28,1=v39,v54,31=v48,32=v50
freev -
freeb -
cache postorder b17,b16,b15,b9,b14,b13,b12,b11,b8,b7,b5,b6,b4,b3,b2,b1
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 3 "early deadcode"
f b1 t1 a1 77 17
b b1 Plain p2522:161:29:1:0 0 0 - - b2:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v5 Const64 t2 0 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
b b2 Plain p2522:161:14:1:0 0 0 - - b3:0 b1:0
v v15 InlMark t30 2253 - p2522:161:14:0:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
b b3 Plain p173:126:16:1:0 0 0 - - b4:0 b2:0
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 b3:0
v v19 OffPtr t45 344 - p173:126:16:0:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b7:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 Plain p173:130:25:1:0 0 0 - - b8:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b11:0 b7:0
v v27 OffPtr t46 40 - p173:130:25:0:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b7:1 b14:0
b b11 Plain p173:130:36:1:0 0 0 - - b13:1 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 3 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
b b12 Plain p173:130:36:1:0 0 0 - - b13:0 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b15:0,b14:0 b12:0,b11:0
v v55 Phi t2 0 - p173:130:12:0:0 1 v5,v53
v v56 Phi t3 0 - p173:130:12:0:0 1 v28,v54
v v75 Phi t28 0 - p173:130:12:0:0 4 v76,v45
b b14 Plain p173:134:13:0:0 0 0 - - b9:0 b13:1
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b15 Plain p2524:270:16:1:0 0 0 - - b16:0 b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v75
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v75
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v75
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
b b16 Plain p2524:270:16:1:0 0 0 - - b17:0 b15:0
b b17 Ret p173:132:4:1:0 0 0 - v66 - b16:0
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v55,v63
names s1,s3,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v5,v53,v55
named s7 v28,v54,v56
named s8 v33
named s9 v55
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v28,1=v39,v54,31=v48
freev v65,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b10
cache postorder b17,b16,b15,b9,b14,b13,b12,b11,b8,b7,b5,b6,b4,b3,b2,b1
cache linestarts 173:125:134,2522:161:161:161=0,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 4 "short circuit"
f b4 t1 a1 77 17
b b1 BlockInvalid p2522:161:29:1:0 0 0 - - - -
b b2 BlockInvalid p2522:161:14:1:0 0 0 - - - -
b b3 BlockInvalid p173:126:16:1:0 0 0 - - - -
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 0 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 BlockInvalid p173:130:25:1:0 0 0 - - - -
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b13:1,b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v55 OpInvalid t2 0 - p173:130:12:0:0 0 -
v v75 Phi t28 0 - p173:130:12:0:0 1 v45,v76
b b11 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b12 Plain p173:130:36:1:0 0 0 - - b9:1 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b17:0,b9:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 6 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v56 Copy t3 0 - p173:130:12:1:0 1 v54
b b14 BlockInvalid p173:134:13:0:0 0 0 - - - -
b b15 BlockInvalid p2524:270:16:1:0 0 0 - - - -
b b16 BlockInvalid p2524:270:16:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v5,v53,v55
named s7 v28,v54,v56
named s8 v33
named s9 v55
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v28,1=v39,v54,31=v48
freev v65,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b10
cache linestarts 173:125:134,2522:161:161:161=0,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 5 "decompose user"
f b4 t1 a1 77 17
b b1 BlockInvalid p2522:161:29:1:0 0 0 - - - -
b b2 BlockInvalid p2522:161:14:1:0 0 0 - - - -
b b3 BlockInvalid p173:126:16:1:0 0 0 - - - -
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v5 Const64 t2 0 - p0:0:0:0:0 0 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v28 ConstBool t3 0 - p0:0:0:0:0 0 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b7 BlockInvalid p173:130:25:1:0 0 0 - - - -
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b13:1,b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v55 OpInvalid t2 0 - p173:130:12:0:0 0 -
v v75 Phi t28 0 - p173:130:12:0:0 1 v45,v76
b b11 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b12 Plain p173:130:36:1:0 0 0 - - b9:1 b8:0
b b13 If p173:130:3:0:0 0 0 - v56 b17:0,b9:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 6 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v56 Copy t3 0 - p173:130:12:1:0 1 v54
b b14 BlockInvalid p173:134:13:0:0 0 0 - - - -
b b15 BlockInvalid p2524:270:16:1:0 0 0 - - - -
b b16 BlockInvalid p2524:270:16:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s7,s8,s9,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v5,v53,v55
named s7 v28,v54,v56
named s8 v33
named s9 v55
named s10 v56
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 0=v5,v28,1=v39,v54,31=v48
freev v65,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b10
cache linestarts 173:125:134,2522:161:161:161=0,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 6 "pre-opt deadcode"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 ConstString t16 0 a5 p0:0:0:0:0 1 -
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v54 ConstBool t3 1 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b13:1,b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v75 Phi t28 0 - p173:130:12:0:0 1 v45,v76
b b12 Plain p173:130:36:1:0 0 0 - - b9:1 b8:0
b b13 If p173:130:3:1:0 0 0 - v54 b17:0,b9:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 6 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 PtrIndex t33 0 - p2523:60:14:0:0 1 v47,v51
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s7,s8,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s7 v54
named s8 v33
named s10 v54
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,v54,31=v48
freev v56,v55,v28,v5,v65,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache linestarts 173:125:134:130=11,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 7 "opt"
aux a27 sym "go:string.\"randinit missed\"" "go:string.\"randinit missed\"" 0 SRODATA 15 dupok,local,contentaddressable - - 72616e64696e6974206d6973736564 0
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 5 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v55
v v55 SB t15 0 - p0:0:0:0:0 1 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b13:1,b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v75 Phi t28 0 - p173:130:12:0:0 1 v45,v76
b b12 Plain p173:130:36:1:0 0 0 - - b9:1 b8:0
b b13 First p173:130:3:1:0 0 0 - - b17:0,b9:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 6 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s7,s8,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s7 v54
named s8 v33
named s10 v54
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 8 "zero arg cse"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v55 SB t15 0 - p0:0:0:0:0 0 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b13:1,b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v75
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v75 Phi t28 0 - p173:130:12:0:0 1 v45,v76
b b12 Plain p173:130:36:1:0 0 0 - - b9:1 b8:0
b b13 First p173:130:3:1:0 0 0 - - b17:0,b9:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 6 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s7,s8,s10,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s7 v54
named s8 v33
named s10 v54
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 9 "opt deadcode"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 1 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v26 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 1 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v18
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v26
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 1 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 1 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v34
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 1 v67
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v68,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 1 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 1 v43
v v45 Store t28 0 a10 p2523:59:6:0:0 5 v44,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 1 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v46
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 1 v57
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v58,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 10 "generic cse"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Addr t34 0 a4 p0:0:0:0:0 5 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v26 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 5 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 4 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 2 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 0 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v31
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 0 v6
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 0 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 0 v31
v v45 Store t28 0 a10 p2523:59:6:0:0 5 v32,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 0 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v31
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 0 v6
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 11 "phiopt"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 6 -
v v6 Addr t34 0 a4 p0:0:0:0:0 5 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v18 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v26 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v57 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v67 Addr t34 0 a4 p0:0:0:0:0 0 v3
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 5 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 4 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 2 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 0 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v31
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v68 OffPtr t46 40 - p173:134:13:0:0 0 v6
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 0 v27,v76
v v44 OffPtr t19 288 - p2523:59:3:0:0 0 v31
v v45 Store t28 0 a10 p2523:59:6:0:0 5 v32,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 0 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v31
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v58 OffPtr t43 0 - p173:131:22:0:0 0 v6
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8,s11,s12
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
named s11 v58
named s12 v58
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 12 "gcse deadcode"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v6 Addr t34 0 a4 p0:0:0:0:0 3 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 8 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 5 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 NilCheck t46 0 - p2523:55:8:1:0 3 v27,v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 2 v31
v v33 Load t10 0 - p2523:55:8:0:0 3 v32,v76
v v34 NilCheck t46 0 - p2523:56:11:1:0 0 v27,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v31
v v36 Load t10 0 - p2523:56:11:0:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 NilCheck t46 0 - p2523:59:3:0:0 0 v27,v76
v v45 Store t28 0 a10 p2523:59:6:0:0 5 v32,v40,v76
v v46 NilCheck t46 0 - p2523:60:10:1:0 0 v27,v45
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v31
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:0:0 1 v52,v45
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 13 "nilcheckelim"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v6 Addr t34 0 a4 p0:0:0:0:0 3 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v27 OffPtr t46 40 - p173:130:25:1:0 5 v6
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v31 Copy t46 0 - p2523:55:8:1:0 3 v27
v v34 Copy t46 0 - p2523:56:11:1:0 0 v27
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 288 - p2523:55:8:0:0 2 v31
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v31
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v43 Copy t46 0 - p2523:59:3:0:0 0 v27
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v31
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v46 Copy t46 0 - p2523:60:10:1:0 0 v27
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 14 "prove"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 3 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 5 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 Copy t46 0 - p2523:55:8:1:0 3 v27
v v34 Copy t46 0 - p2523:56:11:1:0 0 v27
v v32 OffPtr t19 288 - p2523:55:8:0:0 2 v31
v v35 OffPtr t19 292 - p2523:56:11:0:0 1 v31
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v43 Copy t46 0 - p2523:59:3:0:0 0 v27
v v46 Copy t46 0 - p2523:60:10:1:0 0 v27
v v47 OffPtr t48 0 - p2523:60:10:0:0 1 v31
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 15 "divisible"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 3 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 288 - p2523:55:8:1:0 2 v27
v v35 OffPtr t19 292 - p2523:56:11:1:0 1 v27
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 0 - p2523:60:10:1:0 1 v27
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v46,v43,v34,v31,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 16 "divmod"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v65 Const64 t11 8 - p2523:60:14:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 3 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 4 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 288 - p2523:55:8:1:0 2 v27
v v35 OffPtr t19 292 - p2523:56:11:1:0 1 v27
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 0 - p2523:60:10:1:0 1 v27
v v49 And32 t10 0 - p2523:60:16:0:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Mul64 t11 0 - p2523:60:14:0:0 1 v51,v65
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v46,v43,v34,v31,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 17 "middle opt"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v65,v43,v34,v31,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 18 "known bits"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b12:0,b13:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b12:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 Plain p173:130:36:1:0 0 0 - - b9:0 b8:0
b b13 Plain p173:130:3:1:0 0 0 - - b17:0 b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b13:0
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v65,v43,v34,v31,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b12,b17,b13,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b12,b12:b8,b13:b8,b17:b13
cache sdom b4:-:b6:-:2:47,b5:b4:b8:-:11:44,b6:b4:-:b5:5:8,b8:b5:b13:-:14:41,b9:b12:-:-:32:35,b12:b8:b9:-:29:38,b13:b8:b17:b12:17:26,b17:b13:-:-:20:23
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 19 "early fuse"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 1 v56,v28
v v16 StaticLECall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticLECall t32 16 a8 p173:127:8:1:0 1 v22,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticLECall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticLECall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v65,v43,v34,v31,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 20 "expand calls"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 2 v56,v28
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v65 SP t15 0 - p0:0:0:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v43,v34,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v43 StringPtr t17 0 - p173:127:8:1:0 1 v22
v v34 StringLen t11 0 - p173:127:8:2:0 1 v22
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 2 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
v v31 LocalAddr t33 0 a3 p173:132:4:1:0 0 v65,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 21 "decompose builtin"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 2 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 2 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 0 v56,v28
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v65 SP t15 0 - p0:0:0:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 2 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
v v31 LocalAddr t33 0 a3 p173:132:4:1:0 0 v65,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 22 "softfloat"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 2 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 2 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 0 v56,v28
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v65 SP t15 0 - p0:0:0:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 2 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
v v31 LocalAddr t33 0 a3 p173:132:4:1:0 0 v65,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 23 "branchelim"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 2 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 2 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v22 StringMake t16 0 - p0:0:0:0:0 0 v56,v28
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
v v65 SP t15 0 - p0:0:0:0:0 1 -
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 2 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
v v31 LocalAddr t33 0 a3 p173:132:4:1:0 0 v65,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 24 "late opt"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 25 "dead auto elim"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 26 "sccp"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b12 BlockInvalid p173:130:36:1:0 0 0 - - - -
b b13 BlockInvalid p173:130:3:1:0 0 0 - - - -
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 27 "generic deadcode"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 28 "late fuse"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 29 "check bce"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 30 "dse"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 31 "memcombine"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 32 "writebarrier"
f b4 t1 a1 77 17
b b4 If p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 2 -
v v28 Const64 t11 15 - p0:0:0:0:0 1 -
v v39 Const32 t10 1 - p0:0:0:0:0 1 -
v v48 Const32 t10 31 - p0:0:0:0:0 1 -
v v6 Addr t34 0 a4 p0:0:0:0:0 6 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 Addr t17 0 a27 p0:0:0:0:0 1 v3
v v7 OffPtr t43 0 - p173:125:18:0:0 2 v6
v v19 OffPtr t45 344 - p173:126:16:1:0 1 v6
v v16 StaticCall t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 Load t3 0 - p173:126:16:0:0 1 v19,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 StaticCall t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 If p2523:56:11:0:0 0 0 - v37 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 OffPtr t46 40 - p173:130:25:1:0 1 v6
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v32 OffPtr t19 328 - p2523:55:8:1:0 2 v6
v v35 OffPtr t19 332 - p2523:56:11:1:0 1 v6
v v33 Load t10 0 - p2523:55:8:1:0 3 v32,v76
v v36 Load t10 0 - p2523:56:11:1:0 1 v35,v76
v v37 Leq32U t3 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 StaticCall t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 Add32 t10 0 - p2523:59:10:1:0 1 v33,v39
v v47 OffPtr t48 40 - p2523:60:10:2:0 1 v6
v v49 And32 t10 0 - p2523:60:16:1:0 1 v33,v48
v v45 Store t28 0 a10 p2523:59:6:0:0 4 v32,v40,v76
v v51 ZeroExt32to64 t11 0 - p2523:60:14:0:0 1 v49
v v5 Lsh64x64 t11 1 - p2523:60:14:0:0 1 v51,v46
v v52 AddPtr t33 0 - p2523:60:14:0:0 1 v47,v5
v v53 Load t2 0 - p2523:60:14:1:0 1 v52,v45
v v46 Const64 t2 3 - p2523:60:14:0:0 1 -
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 StaticCall t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts 1=v39,31=v48
freev v31,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 33 "lower"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 ARM64MOVWUload t10 328 a4 p2523:55:8:1:0 3 v3,v76
v v36 ARM64MOVWUload t10 332 a4 p2523:56:11:1:0 1 v3,v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v46,v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 34 "addressing modes"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 ARM64MOVWUload t10 328 a4 p2523:55:8:1:0 3 v3,v76
v v36 ARM64MOVWUload t10 332 a4 p2523:56:11:1:0 1 v3,v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v46,v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 35 "late lower"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 5 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 ARM64MOVWUload t10 328 a4 p2523:55:8:1:0 3 v3,v76
v v36 ARM64MOVWUload t10 332 a4 p2523:56:11:1:0 1 v3,v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v46,v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 36 "pair"
type t49 TUPLE ? ? ? - "uint32,uint32" "" t10 t10
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 37 "lowered deadcode for cse"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 38 "lowered cse"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 39 "elim unread autos"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 40 "tighten tuple selectors"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 41 "lowered deadcode"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 42 "checkLower"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 43 "loop invariant"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 44 "late phielim and copyelim"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 45 "tighten"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 46 "late deadcode"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b5:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b4:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b13,b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:35,b5:b4:b8:-:11:32,b6:b4:-:b5:5:8,b8:b5:b17:-:14:29,b9:b8:-:-:23:26,b17:b8:-:b9:17:20
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 47 "critical"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b13:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 48 "phi tighten"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 0 0 - v21 b13:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b8 ARM64ULE p2523:56:11:0:0 0 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 49 "likelyadjust"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b5:b4,b6:b4,b8:b5,b9:b8,b17:b8,b13:b4
cache sdom b4:-:b6:-:2:41,b5:b4:b8:-:17:38,b6:b4:-:b13:5:8,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26,b13:b4:-:b5:11:14
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
dcllen 16
end
pass 50 "layout"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
fstate laidout
dcllen 16
end
pass 51 "schedule"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
fstate scheduled,laidout
dcllen 16
end
pass 52 "late nilcheck"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
fstate scheduled,laidout
dcllen 16
end
pass 53 "flagalloc"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 7 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v7 ARM64MOVDaddr t43 0 a4 p173:125:18:0:0 2 v3
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v7,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v56 ARM64MOVDaddr t17 0 a27 p0:0:0:0:0 1 v3
v v28 ARM64MOVDconst t11 15 - p0:0:0:0:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v56,v28,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v27 ARM64MOVDaddr t46 40 a4 p173:130:25:1:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v27,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v47 ARM64MOVDaddr t48 40 a4 p2523:60:10:2:0 1 v3
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v47,v51,v45
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v7,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v53,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v52,v5,v49,v37,v35,v32,v19,v6,v48,v39,v65,v22,v34,v43,v58,v44,v68,v67,v57,v26,v18,v75,v55,v54,v64,v59,v69,v42,v41,v38,v74,v73,v72,v29,v23,v20,v14,v13,v12,v50,v11,v10,v9,v4,v2
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:0 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
fstate scheduled,laidout
dcllen 16
end
pass 54 "regalloc"
aux a1 call "AuxCall{runtime.bootstrapRand}" a2 1 0 1 8 0 0 1
abiparam out 0 t2 a3 0 -1
callreg 0:1 - 0 -
aux a6 call "AuxCall{runtime.lock2}" a7 1 1 0 8 8 1 0
abiparam in 0 t43 - 0 0
callreg 0:1 - 7fffffff97ffffff -
aux a8 call "AuxCall{runtime.fatal}" a9 1 1 0 8 16 2 0
abiparam in 0 t16 - 0,1 0
callreg 0:1,1:2 - 7fffffff97ffffff -
aux a11 call "AuxCall{internal/chacha8rand.(*State).Refill}" a12 1 1 0 8 8 1 0
abiparam in 0 t46 - 0 0
callreg 0:1 - 7fffffff97ffffff -
aux a13 call "AuxCall{runtime.unlock2}" a14 1 1 0 8 8 1 0
abiparam in 0 t43 - 0 0
callreg 0:1 - 7fffffff97ffffff -
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v52 ARM64MOVDaddr t43 0 a4 p2526:24:7:2:0 1 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v52,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v5 ARM64MOVDaddr t17 0 a27 p173:127:8:2:0 1 v3
v v49 ARM64MOVDconst t11 15 - p173:127:8:2:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v5,v49,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v37 ARM64MOVDaddr t46 40 a4 p173:134:26:2:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v37,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v35 ARM64MOVDaddr t48 40 a4 p2523:60:14:2:0 1 v3
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v35,v51,v45
v v19 StoreReg t2 0 - p2523:60:14:1:0 1 v53
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v32 ARM64MOVDaddr t43 0 a4 p2527:36:9:2:0 1 v3
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v32,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v6 LoadReg t2 0 - p173:132:4:2:0 1 v19
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v6,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v2,v4,v9,v10,v11,v12,v13,v14,v18,v20,v22,v23,v26,v29,v34,v38,v39,v41,v42,v43,v44,v48,v50,v54,v55,v57,v58,v59,v64,v65,v67,v68,v69,v72,v73,v74,v75
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b8:b5,b9:b8,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b8:b5:b17:-:20:35,b9:b8:-:-:29:32,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:1 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
fstate scheduled,laidout
regalloc 71 v3:SB,v5:R0,v6:R0,v16:[],v19:@a20/t2/0/-/0,v21:R1,v24:[],v32:R0,v33:R1,v35:R2,v36:R2,v37:R0,v40:R2,v46:(R1;R2),v49:R1,v51:R1,v52:R0,v53:R1,v62:[],v66:[],v70:[]
dcllen 16
end
pass 55 "loop rotate"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b13:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v52 ARM64MOVDaddr t43 0 a4 p2526:24:7:2:0 1 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v52,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b13 Plain p173:126:16:0:0 0 0 - - b5:0 b4:0
b b6 Plain p173:127:9:0:0 0 0 - - b5:1 b4:1
v v5 ARM64MOVDaddr t17 0 a27 p173:127:8:2:0 1 v3
v v49 ARM64MOVDconst t11 15 - p173:127:8:2:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v5,v49,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b5 Plain p173:130:25:1:0 0 0 - - b8:0 b13:0,b6:0
v v77 Phi t28 0 - p173:129:2:1:0 1 v17,v25
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v37 ARM64MOVDaddr t46 40 a4 p173:134:26:2:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v37,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b5:0,b9:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v77,v71
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v35 ARM64MOVDaddr t48 40 a4 p2523:60:14:2:0 1 v3
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v35,v51,v45
v v19 StoreReg t2 0 - p2523:60:14:1:0 1 v53
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v32 ARM64MOVDaddr t43 0 a4 p2527:36:9:2:0 1 v3
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v32,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v6 LoadReg t2 0 - p173:132:4:2:0 1 v19
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v6,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v2,v4,v9,v10,v11,v12,v13,v14,v18,v20,v22,v23,v26,v29,v34,v38,v39,v41,v42,v43,v44,v48,v50,v54,v55,v57,v58,v59,v64,v65,v67,v68,v69,v72,v73,v74,v75
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache postorder b9,b17,b8,b5,b13,b6,b4
cache idom b4:-,b13:b4,b6:b4,b5:b4,b9:b8,b8:b5,b17:b8
cache sdom b4:-:b6:-:2:41,b13:b4:-:b5:11:14,b6:b4:-:b13:5:8,b5:b4:b8:-:17:38,b9:b8:-:-:29:32,b8:b5:b17:-:20:35,b17:b8:-:b9:23:26
cache loopnest 18 0 b8:-:2:1:1:1 b8:0,b9:0
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
hotness b9:3
fstate scheduled,laidout
regalloc 71 v3:SB,v5:R0,v6:R0,v16:[],v19:@a20/t2/0/-/0,v21:R1,v24:[],v32:R0,v33:R1,v35:R2,v36:R2,v37:R0,v40:R2,v46:(R1;R2),v49:R1,v51:R1,v52:R0,v53:R1,v62:[],v66:[],v70:[]
dcllen 16
end
pass 56 "trim"
f b4 t1 a1 77 17
b b4 ARM64TBNZ p173:126:16:0:0 1 0 - v21 b8:0,b6:0 -
v v3 SB t15 0 - p0:0:0:0:0 8 -
v v1 InitMem t28 0 - p0:0:0:0:0 3 -
v v8 InlMark t30 2249 - p173:125:6:1:0 0 v1
v v15 InlMark t30 2253 - p2522:161:14:1:0 0 v1
v v52 ARM64MOVDaddr t43 0 a4 p2526:24:7:2:0 1 v3
v v16 ARM64CALLstatic t32 8 a6 p2526:24:7:1:0 1 v52,v1
v v17 SelectN t28 0 - p2526:24:7:0:0 3 v16
v v21 ARM64MOVBUload t3 344 a4 p173:126:16:1:0 1 v3,v17
b b6 Plain p173:127:9:0:0 0 0 - - b8:2 b4:1
v v5 ARM64MOVDaddr t17 0 a27 p173:127:8:2:0 1 v3
v v49 ARM64MOVDconst t11 15 - p173:127:8:2:0 1 -
v v24 ARM64CALLstatic t32 16 a8 p173:127:8:1:0 1 v5,v49,v17
v v25 SelectN t28 0 - p173:127:8:0:0 1 v24
b b9 Plain p173:130:25:1:0 0 0 - - b8:1 b8:0
v v37 ARM64MOVDaddr t46 40 a4 p173:134:26:2:0 1 v3
v v70 ARM64CALLstatic t32 8 a11 p173:134:26:1:0 1 v37,v76
v v71 SelectN t28 0 - p173:134:26:0:0 1 v70
b b8 ARM64ULE p2523:56:11:0:0 1 0 - v31 b9:0,b17:0 b4:0,b9:0,b6:0
v v76 Phi t28 0 - p0:0:0:0:0 4 v17,v71,v25
v v46 ARM64LDPW t49 328 a4 p2523:55:8:1:0 2 v3,v76
v v33 Select0 t10 0 - p2523:55:8:1:0 3 v46
v v36 Select1 t10 0 - p2523:56:11:1:0 1 v46
v v30 InlMark t30 2250 - p173:130:36:0:0 0 v76
v v31 ARM64CMPW t29 0 - p2523:56:7:0:0 1 v36,v33
b b17 Ret p173:132:4:1:0 0 0 - v66 - b8:1
v v40 ARM64ADDconst t10 1 - p2523:59:10:1:0 1 v33
v v45 ARM64MOVWstore t28 328 a4 p2523:59:6:0:0 4 v3,v40,v76
v v51 ARM64ANDconst t11 31 - p2523:60:14:1:0 1 v33
v v35 ARM64MOVDaddr t48 40 a4 p2523:60:14:2:0 1 v3
v v53 ARM64MOVDloadidx8 t2 0 - p2523:60:14:1:0 1 v35,v51,v45
v v19 StoreReg t2 0 - p2523:60:14:1:0 1 v53
v v60 InlMark t30 2251 - p173:131:10:1:0 0 v45
v v61 InlMark t30 2254 - p2524:270:16:1:0 0 v45
v v32 ARM64MOVDaddr t43 0 a4 p2527:36:9:2:0 1 v3
v v62 ARM64CALLstatic t32 8 a13 p2527:36:9:1:0 1 v32,v45
v v63 SelectN t28 0 - p2527:36:9:0:0 1 v62
v v6 LoadReg t2 0 - p173:132:4:2:0 1 v19
v v66 MakeResult t47 0 - p173:132:4:1:0 1 v6,v63
names s1,s3,s5,s6,s8
named s1 v7
named s3 v7
named s5 v27
named s6 v53
named s8 v33
splits -
canon a15/t43/0/-/0=s1,a16/t44/0/-/0=s2,a17/t43/0/-/0=s3,a18/t44/0/-/0=s4,a19/t46/0/-/0=s5,a20/t2/0/-/0=s6,a21/t3/0/-/0=s7,a22/t10/0/-/0=s8,a23/t2/0/-/0=s9,a24/t3/0/-/0=s10,a25/t43/0/-/0=s11,a26/t43/0/-/0=s12
consts -
freev v2,v4,v9,v10,v11,v12,v13,v14,v18,v20,v22,v23,v26,v29,v34,v38,v39,v41,v42,v43,v44,v48,v50,v54,v55,v57,v58,v59,v64,v65,v67,v68,v69,v72,v73,v74,v75
freeb b12,b16,b15,b14,b11,b7,b3,b2,b1,b10
cache auxmap -:1,a4:2,a27:3
cache linestarts 173:125:134,2522:161:161,2523:55:60,2524:270:270,2526:24:24,2527:36:36
hotness b9:3
fstate scheduled,laidout
regalloc 71 v3:SB,v5:R0,v6:R0,v16:[],v19:@a20/t2/0/-/0,v21:R1,v24:[],v32:R0,v33:R1,v35:R2,v36:R2,v37:R0,v40:R2,v46:(R1;R2),v49:R1,v51:R1,v52:R0,v53:R1,v62:[],v66:[],v70:[]
dcllen 16
end
frontend
end
ptrcache t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t21,t24,t25,t26,t27,t36,t38,t39,t40
typelink t8=t39,t28=t32
typeorder t4,t8=t39,t5,t9,t6,t10,t7,t44,t2,t11,t14,t15,t25,t26,t12,t13,t3,t17,t18,t19,t33,t20,t21,t22,t23,t45,t24,t48,t34,t43,t46,t1,t42,t38,t41,t35,t36,t40,t37,t16,t27,t28,t30,t29,t31,t49,t32,t47
eof
"#

/-- `std/std/runtime/bootstrapRand,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "bootstrapRand" 1
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
type t1 8 8 0 0 - "uint64"
name n1 "~r0" PPARAMOUT t1 1 "runtime.~r0" 0 a3
name n2 "x" PAUTO t1 1 "runtime.x" 0 a23
type t2 1 1 0 0 - "bool"
name n3 "ok" PAUTO t2 1 "runtime.ok" 0 a24
name n4 ".autotmp_3" PAUTO t1 1 "runtime..autotmp_3" 0 -
name n5 ".autotmp_4" PAUTO t2 1 "runtime..autotmp_4" 0 -
type t3 8 8 8 1 01 "*mutex"
name n6 "l" PAUTO t3 1 "runtime.l" 0 a15
type t4 8 8 8 1 01 "*chacha8rand.State"
name n7 "s" PAUTO t4 1 "internal/chacha8rand.s" 0 a19
name n8 "~r0" PAUTO t1 1 "runtime.~r0" 0 a20
name n9 "~r1" PAUTO t2 1 "runtime.~r1" 0 a21
type t5 4 4 0 0 - "uint32"
name n10 "i" PAUTO t5 1 "internal/chacha8rand.i" 0 a22
name n11 "l" PAUTO t3 1 "runtime.l" 0 a25
name n12 "l" PAUTO t3 1 "runtime.l" 0 -
type t6 8 8 0 0 - "lockRank"
name n13 "~r0" PAUTO t6 1 "runtime.~r0" 0 a16
name n14 "l" PAUTO t3 1 "runtime.l" 0 a17
name n15 "rank" PAUTO t6 1 "runtime.rank" 0 a18
name n16 "l" PAUTO t3 1 "runtime.l" 0 a26
in n1 0 outregs
in n2 0 used
in n3 0 used
in n4 0 used,autotmp
in n5 0 used,autotmp
in n6 0 used
in n7 0 used
in n8 0 -
in n9 0 -
in n10 0 used
in n11 0 used
in n12 0 -
in n13 0 -
in n14 0 used
in n15 0 -
in n16 0 used
out n8 -8 used
opt n6 0 -
opt n11 0 -
opt n12 0 -
opt n14 0 -
opt n16 0 -
opt n7 0 -
opt n4 0 autotmp
opt n15 0 -
opt n2 0 -
opt n1 0 outregs
opt n13 0 -
opt n10 0 -
opt n5 0 autotmp
opt n3 0 -
opt n9 0 -
stack 8 0 8
end
genin
posbase p173 "runtime/rand.go" 1 1 -1 170 "runtime/rand.go" "runtime/rand.go" 1 1
sym y1 "runtime.bootstrapRand" 1
curfn p173:124:6:0:0 0 0
regargs -
text y1 0 0 0 0 124 300080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "runtime.lock" 1
inl i2249 - p173:125:6:0:0 y3 "lock"
posbase p2522 "runtime/lock_spinbit.go" 1 1 2249 71 "runtime/lock_spinbit.go" "runtime/lock_spinbit.go" 1 1
sym y4 "runtime.lockWithRank" 1
inl i2253 i2249 p2522:161:14:0:0 y4 "lockWithRank"
posbase p2526 "runtime/lockrank_off.go" 1 1 2253 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
sym y5 "runtime.globalRand" 0
sym y6 "runtime.lock2" 1
sym y7 "go:string.\"randinit missed\"" 0
sym y8 "runtime.fatal" 1
sym y9 "internal/chacha8rand.(*State).Refill" 1
sym y10 "internal/chacha8rand.(*State).Next" 1
inl i2250 - p173:130:36:0:0 y10 "(*State).Next"
posbase p2523 "internal/chacha8rand/chacha8.go" 1 1 2250 77 "internal/chacha8rand/chacha8.go" "internal/chacha8rand/chacha8.go" 1 1
sym y11 "runtime.~r0" 0
sym y12 "runtime.unlock" 1
inl i2251 - p173:131:10:0:0 y12 "unlock"
posbase p2524 "runtime/lock_spinbit.go" 1 1 2251 71 "runtime/lock_spinbit.go" "runtime/lock_spinbit.go" 1 1
sym y13 "runtime.unlockWithRank" 1
inl i2254 i2251 p2524:270:16:0:0 y13 "unlockWithRank"
posbase p2527 "runtime/lockrank_off.go" 1 1 2254 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
sym y14 "runtime.unlock2" 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/32/-/i0 0 0 p173:124:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p173:124:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p173:124:6:0:0
p 3 3 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p173:125:6:2:0
p 4 4 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2522:161:14:1:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p2526:24:7:2:0
p 6 6 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2526:24:7:1:0
p 7 7 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - CONST/0/0/0/NONE/0/0/-/- 0 0 p2526:24:7:1:0
p 8 8 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y6/- 0 0 p2526:24:7:1:0
p 9 9 0 0 0 - MOVBU 0 MEM/0/0/0/EXTERN/0/344/y5/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p173:126:16:1:0
p 10 10 0 0 0 - TBNZ 0 CONST/0/0/0/NONE/0/0/-/- 8193 - BRANCH/0/0/0/NONE/0/0/-/@17 0 0 p173:126:16:2:0
p 11 11 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y7/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p173:127:8:1:0
p 12 12 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/15/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p173:127:8:2:0
p 13 13 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y8/- 0 0 p173:127:8:1:0
p 14 14 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@17 0 0 p173:127:9:2:0
p 15 15 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/40/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p173:134:26:1:0
p 16 16 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y9/- 0 0 p173:134:26:1:0
p 17 17 0 0 0 - LDPW 0 MEM/0/0/0/EXTERN/0/328/y5/- 0 - REGREG/8193/0/0/NONE/0/8194/-/- 0 0 p2523:55:8:1:0
p 18 18 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p173:130:36:2:0
p 19 19 0 0 0 - CMPW 0 REG/8193/0/0/NONE/0/0/-/- 8194 - _ 0 0 p2523:56:7:2:0
p 20 20 0 0 0 - BLS 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@15 0 0 p2523:56:11:2:0
p 21 21 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2523:59:10:1:0
p 22 22 0 0 0 - MOVW 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/328/y5/- 0 0 p2523:59:6:2:0
p 23 23 0 0 0 - AND 0 CONST/0/0/0/NONE/0/31/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2523:60:14:1:0
p 24 24 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/40/y5/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p2523:60:14:2:0
p 25 25 0 0 0 - MOVD 0 MEM/8194/8801/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p2523:60:14:2:0
p 26 26 0 0 0 - MOVD 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8383/0/0/AUTO/0/-8/y11/- 0 0 p2523:60:14:2:0
p 27 27 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p173:131:10:1:0
p 28 28 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p2524:270:16:1:0
p 29 29 0 0 0 - MOVD 0 ADDR/0/0/0/EXTERN/0/0/y5/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p2527:36:9:1:0
p 30 30 0 0 0 - CALL 0 _ 0 - MEM/0/0/0/EXTERN/0/0/y14/- 0 0 p2527:36:9:1:0
p 31 31 0 0 0 - MOVD 0 MEM/8383/0/0/AUTO/0/-8/y11/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p173:132:4:1:0
p 32 32 0 0 0 - RET 0 _ 0 - _ 0 0 p173:132:4:2:0
p 33 33 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 124 300080
inlmark @3 2249
inlmark @4 2253
inlmark @18 2250
inlmark @27 2251
inlmark @28 2254
funcaux y2 y2 - - - - -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y7:1
autot -
dbgentry 4
dbgslot 0 n6 t3 0
dbgslot 1 n14 t3 0
dbgslot 2 n7 t4 0
dbgslot 3 n8 t1 0
dbgslot 4 n10 t5 0
dbgvar 0 n6 0
dbgvar 1 n14 1
dbgvar 2 n7 2
dbgvar 3 n10 4
dbgloc 3 8:30:17:51:51
dbgregout n1
dbgpc 8:30:19,17:51:24
end
asm
sym y15 "runtime.morestack_noctxt" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/48/-/i0 0 0 p173:124:6:0:0
p 34 0 0 0 333 - MOVD 0 MEM/8220/0/0/NONE/86/16/-/- 0 - REG/8208/0/0/NONE/2/0/-/- 0 0 p173:124:6:0:0
p 35 4 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p173:124:6:0:0
p 36 4 0 0 93 - CMP 0 REG/8208/0/0/NONE/2/0/-/- 8383 - NONE/0/0/0/NONE/1/0/-/- 0 0 p173:124:6:0:0
p 37 8 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@46 0 0 p173:124:6:0:0
p 38 12 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p173:124:6:0:0
p 39 12 48 0 312 - MOVD 64 REG/8222/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/78/-48/-/- 0 0 p173:124:6:0:1
p 40 16 0 0 307 - MOVD 0 REG/8221/0/0/NONE/2/0/-/- 0 - MEM/8383/0/0/NONE/79/-8/-/- 0 0 p173:124:6:0:0
p 41 20 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/8/-/- 8383 - REG/8221/0/0/NONE/2/0/-/- 0 0 p173:124:6:0:0
p 1 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p173:124:6:0:0
p 2 24 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p173:124:6:0:0
p 3 24 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p173:125:6:2:0
p 4 28 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2522:161:14:1:0
p 5 32 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p2526:24:7:2:0
p 6 32 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2526:24:7:1:0
p 7 40 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/16/0/-/- 0 0 p2526:24:7:1:0
p 8 40 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y6/- 0 0 p2526:24:7:1:0
p 9 44 0 0 299 - MOVBU 0 MEM/0/0/0/EXTERN/110/344/y5/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p173:126:16:1:0
p 10 52 0 0 470 - TBNZ 0 CONST/0/0/0/NONE/16/0/-/- 8193 - BRANCH/0/0/0/NONE/36/17/-/@17 0 0 p173:126:16:2:0
p 11 56 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y7/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p173:127:8:1:0
p 12 64 0 0 317 - MOVD 0 CONST/0/0/0/NONE/17/15/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p173:127:8:2:0
p 13 68 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y8/- 0 0 p173:127:8:1:0
p 14 72 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/17/-/@17 0 0 p173:127:9:2:0
p 15 76 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/40/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p173:134:26:1:0
p 16 84 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y9/- 0 0 p173:134:26:1:0
p 17 88 0 0 268 - LDPW 0 MEM/0/0/0/EXTERN/110/328/y5/- 0 - REGREG/8193/0/0/NONE/7/8194/-/- 0 0 p2523:55:8:1:0
p 18 100 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p173:130:36:2:0
p 19 104 0 0 92 - CMPW 0 REG/8193/0/0/NONE/2/0/-/- 8194 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2523:56:7:2:0
p 20 108 0 0 80 - BLS 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/15/-/@15 0 0 p2523:56:11:2:0
p 21 112 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2523:59:10:1:0
p 22 116 0 0 380 - MOVW 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/EXTERN/110/328/y5/- 0 0 p2523:59:6:2:0
p 23 124 0 0 53 - AND 0 CONST/0/0/0/NONE/17/31/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2523:60:14:1:0
p 24 128 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/40/y5/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p2523:60:14:2:0
p 25 136 0 0 342 - MOVD 0 MEM/8194/8801/0/NONE/114/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p2523:60:14:2:0
p 26 140 0 0 304 - MOVD 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/0/0/0/AUTO/47/-8/y11/- 0 0 p2523:60:14:2:0
p 27 144 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p173:131:10:1:0
p 28 148 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p2524:270:16:1:0
p 29 152 0 0 324 - MOVD 0 ADDR/0/0/0/EXTERN/31/0/y5/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p2527:36:9:1:0
p 30 160 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/EXTERN/36/0/y14/- 0 0 p2527:36:9:1:0
p 31 164 0 0 329 - MOVD 0 MEM/0/0/0/AUTO/47/-8/y11/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p173:132:4:1:0
p 32 168 0 0 332 - MOVD 0 MEM/8383/0/0/NONE/79/-8/-/- 0 - REG/8221/0/0/NONE/2/0/-/- 0 0 p173:132:4:2:0
p 42 172 -48 0 336 - MOVD 32 MEM/8383/0/0/NONE/86/48/-/- 0 - REG/8222/0/0/NONE/2/0/-/- 0 0 p173:132:4:2:0
p 43 176 48 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p173:132:4:2:0
p 44 180 -48 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p173:132:4:2:0
p 45 180 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p173:124:6:0:0
p 46 180 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p173:124:6:0:0
p 47 180 0 0 301 - MOVD 0 REG/8222/0/0/NONE/2/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p173:124:6:0:0
p 48 184 0 0 2 - CALL 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/y15/- 0 0 p173:124:6:0:0
p 49 188 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/23/-1/-/- 0 0 p173:124:6:0:0
p 50 188 48 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/0/-/@34 0 0 p173:124:6:0:0
fn y1 0 40 0 0 124 300080
inlmark @3 2249
inlmark @4 2253
inlmark @18 2250
inlmark @27 2251
inlmark @28 2254
funcaux y2 y2 - - - - -
text 192 0 900b40f9ff6330eb69050054fe0f1df8fd831ff8fd2300d11f2003d51f2003d50000009000000091000000941b00009061034039210100370000009000000091e10f40b200000094040000140000009000000091000000941b0000907b030091610b40291f2003d55f00016b09ffff54220400911b000090620300b9211040920200009042000091417861f8e11300f91f2003d51f2003d5000000900000009100000094e01340f9fd835ff8fe0743f8c0035fd6e3031eaa00000094d1ffff17 13
reloc 32 8 R_ADDRARM64 0 y5
reloc 40 4 R_CALLARM64 0 y6
reloc 44 8 R_ARM64_PCREL_LDST8 344 y5
reloc 56 8 R_ADDRARM64 0 y7
reloc 68 4 R_CALLARM64 0 y8
reloc 76 8 R_ADDRARM64 40 y5
reloc 84 4 R_CALLARM64 0 y9
reloc 88 8 R_ADDRARM64 328 y5
reloc 116 8 R_ARM64_PCREL_LDST32 328 y5
reloc 128 8 R_ADDRARM64 40 y5
reloc 152 8 R_ADDRARM64 0 y5
reloc 160 4 R_CALLARM64 0 y14
reloc 184 4 R_CALLARM64 0 y15
pcln y18 y19 y20 y21 y16,y17 y2,y2
usedfiles 35,71,77,170
inltree 0 -1 p173:125:6:0:0 y3 "lock" 24
inltree 1 0 p2522:161:14:0:0 y4 "lockWithRank" 28
inltree 2 -1 p173:130:36:0:0 y10 "(*State).Next" 100
inltree 3 -1 p173:131:10:0:0 y12 "unlock" 144
inltree 4 3 p2524:270:16:0:0 y13 "unlockWithRank" 148
data y2 Sxxx 0 4 8000 0100000000000000 0
data y16 SRODATA 11 1 28000 0001010202050127020100 0
data y17 SRODATA 7 1 28000 000a0223010300 0
data y18 SRODATA 7 1 28000 020460285f0400 0
data y19 SRODATA 32 1 28000 d60207c5010147038e020bb90103ba0101b9010aba0101c5010147038e020700 0
data y20 SRODATA 45 1 28000 fa010602014801910203cc010302050e039d0103960101930102060302058e0101960201d30303c001040f0300 0
data y21 SRODATA 23 1 28000 000702010203030b06030501060a050108010203090700 0
end
dwarf
sym y22 "" 0
sym y23 "" 0
sym y24 "" 0
sym y25 "" 0
sym y26 "runtime.getLockRank" 1
inl i2252 i2249 p2522:161:29:0:0 y26 "getLockRank"
posbase p2525 "runtime/lockrank_off.go" 1 1 2252 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
posbase p72 "runtime/lock_spinbit.go" 1 1 -1 71 "runtime/lock_spinbit.go" "runtime/lock_spinbit.go" 1 1
posbase p78 "internal/chacha8rand/chacha8.go" 1 1 -1 77 "internal/chacha8rand/chacha8.go" "internal/chacha8rand/chacha8.go" 1 1
posbase p36 "runtime/lockrank_off.go" 1 1 -1 35 "runtime/lockrank_off.go" "runtime/lockrank_off.go" 1 1
sym y27 "go:info.runtime.lock$abstract" 0
sym y28 "go:info.internal/chacha8rand.(*State).Next$abstract" 0
sym y29 "go:info.runtime.unlock$abstract" 0
sym y30 "go:info.runtime.getLockRank$abstract" 0
sym y31 "go:info.runtime.lockWithRank$abstract" 0
sym y32 "go:info.runtime.unlockWithRank$abstract" 0
sym y33 "go:info.uint64" 0
sym y34 "go:info.*runtime.mutex" 0
sym y35 "go:info.*internal/chacha8rand.State" 0
sym y36 "go:info.uint32" 0
sym y37 "type:uint64" 0
dwfn y22 y23 y24 - y25 "runtime.bootstrapRand" 170:124 1 0 1 4262
dwdcl n8
dwclosure 0 -
dwmark p173:129:2:0:0 1
dwmark p173:129:6:0:0 2
dwmark p173:130:3:0:0 3
dwmark p173:133:3:0:0 2
dwmark p173:135:2:0:0 0
dwparents 0,1,2
dwparams n1
dwinlfn y3 y27
dwinlfn y10 y28
dwinlfn y12 y29
dwinlfn y26 y30
dwinlfn y4 y31
dwinlfn y13 y32
dwinldcl y3 "l" 0 p72:160:11:0:0
dwinldcl y10 "s" 0 p78:54:7:0:0
dwinldcl y10 "~r0" 0 p78:54:25:0:0
dwinldcl y10 "~r1" 0 p78:54:33:0:0
dwinldcl y10 "i" 0 p78:55:2:0:0
dwinldcl y12 "l" 0 p72:269:13:0:0
dwinldcl y26 "l" 0 p36:19:18:0:0
dwinldcl y26 "~r0" 0 p36:19:28:0:0
dwinldcl y4 "l" 0 p36:23:19:0:0
dwinldcl y4 "rank" 0 p36:23:29:0:0
dwinldcl y13 "l" 0 p36:35:21:0:0
dwname n8 1 1 0 1 0 0 -8 0 - - "uint64" 0 0 1 p2523:54:25:0:0
dwname n6 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p2522:160:11:0:0
dwname n11 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p2524:269:13:0:0
dwname n12 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p2525:19:18:0:0
dwname n14 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p2526:23:19:0:0
dwname n16 1 0 0 1 0 0 0 0 - - "*runtime.mutex" 0 0 1 p2527:35:21:0:0
dwname n7 1 0 0 1 0 0 0 0 - - "*internal/chacha8rand.State" 0 0 1 p2523:54:7:0:0
dwname n4 1 0 1 0 0 0 0 0 - - "uint64" 0 0 1 p173:130:12:0:0
dwname n15 1 0 0 1 0 0 0 0 - - "runtime.lockRank" 0 0 1 p2526:23:29:0:0
dwname n2 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p173:130:6:0:0
dwname n1 1 0 0 0 0 0 0 1 - - "uint64" 0 0 1 p173:124:22:0:0
dwname n13 1 0 0 1 0 0 0 0 - - "runtime.lockRank" 0 0 1 p2525:19:28:0:0
dwname n10 1 0 0 0 1 0 0 0 - - "uint32" 0 0 1 p2523:55:2:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p173:130:12:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "bool" 0 0 1 p173:130:9:0:0
dwname n9 1 0 0 1 0 0 0 0 - - "bool" 0 0 1 p2523:54:33:0:0
var 0 0 "~r0" 5 1 1 0 0 0 y33 "runtime/rand.go" 124 22 0 0 0 0 -
var 1 0 "~r0" 5 0 0 1 0 -16 y33 "internal/chacha8rand/chacha8.go" 54 25 2251 1 0 0 -
var 2 0 "l" 5 1 0 1 0 -8 y34 "runtime/lock_spinbit.go" 160 11 2250 0 1 0 -
var 3 0 "l" 5 1 0 1 0 -8 y34 "runtime/lockrank_off.go" 23 19 2254 0 1 0 -
var 4 0 "s" 5 1 0 1 0 -8 y35 "internal/chacha8rand/chacha8.go" 54 7 2251 0 1 0 -
var 5 0 "i" 52 1 0 0 0 -8 y36 "internal/chacha8rand/chacha8.go" 55 2 2251 3 1 0 v3
scope 0 0 0:192 0,1,2,3,4,5
scope 1 0 76:88,100:104,144:148,164:180 -
scope 2 1 76:88,100:104,144:148,164:180 -
scope 3 2 100:104,144:148,164:180 -
inlcall 0 2249 170:125 y27 1 1 28:44 2
inlcall 1 2253 71:161 y31 - 0 32:44 3
inlcall 2 2250 170:130 y28 - 1 88:100,104:144 1,4,5
inlcall 3 2251 170:131 y29 4 1 148:164 -
inlcall 4 2254 71:270 y32 - 0 152:164 -
dieref y22 5 y27 0
dieref y22 8 y31 0
dieref y22 11 y28 0
dieref y22 12 y28 3
data y22 SDWARFFCN 154 0 0 0372756e74696d652e626f6f74737472617052616e64000000c001019cab0000007c012e7e723000017c0000000000090000000000000000ab0000007d2a000000000009000000000000000048000000a1012a00000000000000090000000000000000ab00000082012a000000000023000000000000000000090000000000000000ab0000008301090000000000000000480000008e02000000 18
reloc 0 0 R_USETYPE 0 y37
reloc 23 2 R_DWTXTADDR_U2 0 y1
reloc 42 4 R_DWARFSECREF 0 y33
reloc 48 4 R_DWARFSECREF 0 y27
reloc 52 4 R_DWARFSECREF 0 y24
reloc 62 4 R_DWARFSECREF 0 y27
reloc 68 4 R_DWARFSECREF 0 y31
reloc 72 4 R_DWARFSECREF 7 y24
reloc 83 4 R_DWARFSECREF 0 y31
reloc 91 4 R_DWARFSECREF 0 y28
reloc 95 4 R_DWARFSECREF 14 y24
reloc 106 4 R_DWARFSECREF 0 y28
reloc 112 4 R_DWARFSECREF 0 y28
reloc 116 4 R_DWARFSECREF 0 y23
reloc 122 4 R_DWARFSECREF 0 y29
reloc 126 4 R_DWARFSECREF 25 y24
reloc 137 4 R_DWARFSECREF 0 y32
reloc 141 4 R_DWARFSECREF 34 y24
data y23 SDWARFLOC 10 0 0 01000004688001015100 1
reloc 1 2 R_DWTXTADDR_U2 0 y1
data y24 SDWARFRANGE 43 0 0 010000041c2c0001000004202c000100000458640468900100010000049401a40100010000049801a40100 5
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 8 2 R_DWTXTADDR_U2 0 y1
reloc 15 2 R_DWTXTADDR_U2 0 y1
reloc 26 2 R_DWTXTADDR_U2 0 y1
reloc 35 2 R_DWTXTADDR_U2 0 y1
data y25 SDWARFLINES 121 0 0 000902000000000000000004ab0103f600140a870688044806031f3c042403fb7e3304ab0103e1008c065f0638065f063706370603023c044e03b57f8304ab010603c6008c044e03ba7f33066206370660063704ab010603c200b404480386013c0424039a7e3304ab0103db008c063706037c83020c000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.bootstrapRand`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G55's check runs on (`liveCtx`). -/
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

def blk : Block := (lc.ctx.f.block? 8).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- G55's value check with G57's group A tried when it rejects a value (as slice G57 composes
them). -/
def vkW (v : Value) : Except String VKind2 :=
  match vkind55 lc g v with
  | .ok kd => .ok kd
  | .error e =>
    match vkind57a lc g v with
    | some r => r
    | none => .error e

/-- The block walk of G55's check (`checkG55L`) with `vkW`. -/
def c2 : Cx2 :=
  let idx := (ps.toList.zipIdx).foldl (fun m (p, i) => m.insert p.id i) {}
  let cx : Cx := { lc, ps, idx, bstart := bs }
  { cx, g, vk := vkW, tm := cx.termG3 }

/-- The PC table of the block walk (`b8`: `v46`'s `LDPW` at Prog 17). -/
def tab : PcTab :=
  match c2.blocks lc.ctx.f.blocks.toList with
  | .ok t => t
  | .error _ => []

/-- The class table of G55's check (`kFlow`). -/
def kt : KTab :=
  let kin := kFlow lc (65 * lc.ctx.f.blocks.size + 2)
  lc.ctx.f.blocks.toList.map fun b => (b, (kin[b]?).getD KMap.bot)

/-- The class map before `v46` (index 1 of `b8`). -/
def K : KMap := kAt lc kt 8 blk 1

/-- P0's layout: the Prog with ID `n` at `0x10000 + 4n`, a 32-byte frame (the home slot, at
operand offset `-8`, then lies 16 bytes above `SP`), every symbol at `symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, the home slots at their frame operands and the PC table of the block walk. -/
def E : MatchEnv :=
  { lc, ι := GenG12.ι, sp := GenG2.sp0,
    slot := fun k => if k ∈ homeSlots lc then (g.slotOp k).map (fun p => frameOff L p.1 p.2) else none,
    g := 0x9000, lr := 0, fp := 0, framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- `runtime.globalRand` at offset 328 (`globalRand.state`'s first words). -/
def pG : Ptr := ⟨.global "runtime.globalRand", 328⟩

/-- 4 bytes above. -/
def pG4 : Ptr := ⟨.global "runtime.globalRand", 332⟩

/-- Byte `i` of `runtime.globalRand`: `i - 327` from offset 328 on, 0 below. -/
def byteG (i : Nat) : BitVec 8 := if 328 ≤ i then BitVec.ofNat 8 (i - 327) else 0

/-- The first 336 bytes of `runtime.globalRand`. -/
def bytesG : Array Byte := Array.ofFn (n := 336) fun i => .b (byteG i.val)

/-- The Phase 1 memory: the global `runtime.globalRand`. -/
def memG : Mem := { blocks := #[(.global "runtime.globalRand", { data := bytesG })] }

/-- The machine memory: the bytes of `runtime.globalRand` at `symA`, 0 elsewhere. -/
def MG : Memory := fun y =>
  if (y - GenG2.symA).toNat < 336 then byteG (y - GenG2.symA).toNat else 0

/-- The `runLoc` state before `v46`: every register `poison`, the memory `memG`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := memG },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem memG }

/-- The machine before `v46`: the activation's `g` and `FP`, the PC of `v46`, the memory `MG`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 8 1, mem := MG }

/-- The home slots have at most 8 bytes and lie above the saved `LR` and below 4096 bytes above
`SP`. -/
def slotsFit : Bool :=
  (homeSlots lc).all fun k =>
    decide ((E.lc.slotTy k).size ≤ 8) &&
    match g.slotOp k with
    | some (nc, off) => decide (8 ≤ frameOff L nc off) && decide (frameOff L nc off < 4096)
    | none => true

/-- The register holds the 32-bit `w`. -/
def isW32 (w : BitVec 32) : Option Val → Bool
  | some (.int .w32 x) => x == w
  | _ => false

theorem isW32_spec {w : BitVec 32} {o : Option Val} (h : isW32 w o = true) :
    o = some (.int .w32 w) := by
  unfold isW32 at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `runtime.bootstrapRand`: G55's check rejects it (`v46: pair
load shape`); the block walk with `vkind57a` (`vkW`) succeeds with `tab`, where `v46` (index 1 of
`b8`) starts at Prog 17 and the next value at Prog 18; the frame check passes, the function
accesses no frame variable, its home slots fit, its Prog IDs are distinct and below `2^32` and
every register home has a width class; `v46` is `LDPW {runtime.globalRand} [328] v3 v76`, which
`vkind57a` accepts with a pattern Prog 17 matches; the class map before it holds its reads; its
aux is the global `runtime.globalRand`, where `memG` reads 4 bytes at 328 and at 332; `stepLoc`
runs `v46` from `s0` to `R1 = 0x04030201`, `R2 = 0x08070605`. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (checkG55 lc0 ps bs g).toOption.isNone &&
    (c2.blocks lc.ctx.f.blocks.toList).toOption.isSome &&
    ((tab.lookup 8).getD []).getD 1 0 == 17 && ((tab.lookup 8).getD []).getD 2 0 == 18 &&
    (match checkFrame lc g with | .ok _ => true | .error _ => false) &&
    (accessedVars lc).isEmpty && slotsFit &&
    ps.toList.all (·.id < 2 ^ 32) && decide ((ps.toList.map (·.id)).Nodup) &&
    GenG57a.homesOK lc &&
    (lc.ctx.f.value? 46).isSome && blk.values[1]? == some 46 && (val 46).op == .ARM64LDPW &&
    GenG57a.vkOK (vkind57a lc g (val 46)) ps 17 &&
    (kReads lc (val 46)).all (fun rc => K.get rc.1 == some rc.2) &&
    ((val 46).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) == some "runtime.globalRand" &&
    (val 46).auxInt.toInt == 328 &&
    (memG.read pG 4).isSome && (memG.read pG4 4).isSome &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 46))
      (fun s1 => isW32 0x04030201 s1.regs[1]? && isW32 0x08070605 s1.regs[2]?)

theorem g57a2_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (checkG55 lc0 ps bs g).toOption = none ∧
      ((tab.lookup 8).getD []).getD 1 0 = 17 ∧ ((tab.lookup 8).getD []).getD 2 0 = 18 ∧
      checkFrame lc g = .ok () ∧ (accessedVars lc).isEmpty = true ∧ slotsFit = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      GenG57a.homesOK lc = true ∧
      lc.ctx.f.value? 46 = some (val 46) ∧ blk.values[1]? = some 46 ∧
      (val 46).op = .ARM64LDPW ∧ GenG57a.vkOK (vkind57a lc g (val 46)) ps 17 = true ∧
      (∀ rc ∈ kReads lc (val 46), K.get rc.1 = some rc.2) ∧
      ((val 46).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) =
        some "runtime.globalRand" ∧ (val 46).auxInt.toInt = 328 ∧
      (memG.read pG 4).isSome = true ∧ (memG.read pG4 4).isSome = true ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 46))
        (fun s1 => isW32 0x04030201 s1.regs[1]? && isW32 0x08070605 s1.regs[2]?) = true := by
  have hf := g57a2_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    Option.isNone_iff_eq_none, and_assoc] at hf
  obtain ⟨hl, h55, -, h1, h2, hcf, hav, hfit, hlt, hnd, hho, hv, hi, hop, hvk, hrd, hsy, hoff,
    hr0, hr1, hrun⟩ := hf
  refine ⟨hl, h55, h1, h2, ?_, hav, hfit, ?_, hnd, hho, ?_, hi, hop, hvk, ?_, hsy, hoff, hr0, hr1,
    hrun⟩
  · revert hcf; cases checkFrame lc g <;> simp
  · exact fun p hp => by simpa using List.all_eq_true.1 hlt p hp
  · obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.1 hv
    simp [val, hv']
  · exact fun rc hrc => by simpa using List.all_eq_true.1 hrd rc hrc

/-! ## The activation -/

theorem g57a2Env (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hfit : slotsFit = true) :
    G49Env lc g L ps 0 tab E where
  env := {
    env := {
      env := {
        env := {
          env := {
            lcEq := rfl
            link := rfl
            pcOf := rfl
            retOut := fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG12.addrAgree
            glob := fun _ _ _ _ => rfl
            syms := by
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk nc off hs => by simp [E, hk, hs]
            extra := by show 0 ≤ (8 : Int); decide
            frame := by
              refine ⟨by show 4096 + 8 ≤ GenG2.sp0.toNat; decide,
                by show GenG2.sp0.toNat + 8 ≤ 2 ^ 64; decide, fun k off hk => ?_⟩
              simp only [E] at hk
              split at hk
              · rename_i hmem
                obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
                have := List.all_eq_true.1 hfit k hmem
                simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
                refine ⟨this.2.1, ?_⟩
                have hsp : GenG2.sp0.toNat = 0x7fff0000 := rfl
                show GenG2.sp0.toNat + _ + 8 ≤ 2 ^ 64
                rw [hsp]
                dsimp only at this ⊢
                omega
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

/-! ## The memory -/

theorem memG_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ memG.blocks) :
    b = .global "runtime.globalRand" ∧ al = { data := bytesG } := by
  simpa [memG] using h

/-- `memG` injected into `MG` by `ι`: `runtime.globalRand`'s bytes at `symA`. -/
theorem memInjG : MemInj GenG12.ι memG MG where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := memG_blocks h
    exact ⟨GenG2.symA, rfl, fun _ => by decide, by simp [bytesG, GenG2.symA]⟩
  inj := by
    intro b al b' al' a a' h h' hne
    obtain ⟨rfl, -⟩ := memG_blocks h
    obtain ⟨rfl, -⟩ := memG_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    obtain ⟨rfl, rfl⟩ := memG_blocks h
    have ha' : a = GenG2.symA := by simp [GenG12.ι] at ha; exact ha.symm
    subst ha'
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    have hi' : i < 336 := by simpa [bytesG] using hi
    have hd : (GenG2.symA + BitVec.ofNat 64 i - GenG2.symA).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]
      omega
    simp [ByteRel, MG, hd, hi', bytesG]

theorem keysG : KeysNodup memG := by simp [KeysNodup, memG]

theorem sepG (hfit : slotsFit = true) : SepFrom GenG12.ι (StkAt E) memG := by
  intro b al a h ha y hy
  obtain ⟨rfl, rfl⟩ := memG_blocks h
  have ha' : a = GenG2.symA := by simp [GenG12.ι] at ha; exact ha.symm
  subst ha'
  have hsp : E.sp.toNat = 0x7fff0000 := rfl
  have hA : GenG2.symA.toNat = 0x10000000000 := rfl
  simp only [hA, bytesG, Array.size_ofFn]
  rcases hy with ⟨-, -, h2⟩ | ⟨k, off, hk, -, h2⟩
  · rw [hsp] at h2
    omega
  · simp only [E] at hk
    split at hk
    · rename_i hmem
      obtain ⟨⟨nc, o⟩, hso, rfl⟩ := Option.map_eq_some_iff.1 hk
      have := List.all_eq_true.1 hfit k hmem
      simp only [hso, Bool.and_eq_true, decide_eq_true_eq] at this
      rw [hsp] at h2
      dsimp only at this h2
      omega
    · cases hk

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 8 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨memG, rfl, memInjG⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, MG, E]; decide,
    by simp only [MState.word, readMem, m0, MG, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g57a2Inv0 (hfit : slotsFit = true) : G3Inv E lc K s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, memG, rfl, keysG, sepG hfit⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-! ## `v46`: `LDPW runtime.globalRand+328(SB), (R1, R2)` -/

/-- `PairPre50` on `v46`: it reads 4 valid bytes of `runtime.globalRand` at 328 and at 332. -/
theorem pre46 (hop : (val 46).op = .ARM64LDPW)
    (hsy : ((val 46).aux.bind (symOf? lc.ctx.tabs ·)).map (·.1.toStringLossy) =
      some "runtime.globalRand") (hoff : (val 46).auxInt.toInt = 328)
    (hr0 : (memG.read pG 4).isSome = true) (hr1 : (memG.read pG4 4).isSome = true) :
    PairPre50 lc s0 (val 46) := by
  intro as n sg fp hpo a x _ _
  rw [hop] at hpo
  simp only [pairOp50, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hpo
  obtain ⟨-, rfl, -, rfl⟩ := hpo
  obtain ⟨y, hy, hsy'⟩ := Option.map_eq_some_iff.1 hsy
  obtain ⟨x', hx', hs'⟩ := Option.bind_eq_some_iff.1 hy
  obtain ⟨name, abi⟩ := y
  simp only at hsy'
  have hpq := pairAddr_globN (a := x) (n := 4) hx' hs'
  rw [hsy', hoff] at hpq
  have hp : (⟨.global "runtime.globalRand", BitVec.ofInt 64 (328 : Int)⟩ : Ptr) = pG := by
    simp only [pG]; decide
  have hq : (⟨.global "runtime.globalRand", BitVec.ofInt 64 (328 : Int) + BitVec.ofNat 64 4⟩ :
      Ptr) = pG4 := by
    simp only [pG4]; decide
  rw [hp, hq] at hpq
  obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hr0
  obtain ⟨bs', hbs'⟩ := Option.isSome_iff_exists.1 hr1
  exact ⟨pG, pG4, memG, bs, bs', hpq, rfl, hbs, hbs', fun h => by cases h⟩

/-- **G57, group A, on `runtime.bootstrapRand`** (`globalRand.state` read as a pair of
`uint32`s: `LDPW runtime.globalRand+328(SB), (R1, R2)`): `b8`'s `v46` (`LDPW
{runtime.globalRand} [328] v3 v76`, a pair load of a global, with an aux), which `checkG55`
rejects (`v46: pair load shape`) and `vkind57a` accepts. From `s0`, with `runtime.globalRand`'s
bytes 328 to 335 `1, …, 8`, `stepLoc` runs `v46` to `R1 = 0x04030201`, `R2 = 0x08070605`, and
`vk57a_step` relates it to a machine state after Prog 17 whose `X1` holds `0x04030201` in its low
word, under an activation (with the function's home slot at its frame operand) extending `E` that
is again a `G49Env`. -/
theorem genG57a2_witness :
    (checkG55 lc0 ps bs g).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 46) = .ok s1 ∧
        s1.regs[1]? = some (.int .w32 0x04030201) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 8 2 m1 ∧ (m1.x 1).setWidth 32 = 0x04030201 := by
  obtain ⟨hl, h55, h1, h2, hcf, hav, hfit, hlt, hnd, hho, hv, hi, hop, hvk, hrd, hsy, hoff, hr0,
    hr1, hrun⟩ := facts
  obtain ⟨pt, hvk, hk17, hok⟩ := GenG57a.vkOK_spec hvk
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  simp only [Bool.and_eq_true] at hr
  have hr1' := isW32_spec hr.1
  have hE := g57a2Env hlt hav hfit
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 32 8 ps.toList 0 E :=
    ⟨hl, fun i r hh hr => .inl (GenG57a.clsReg0 hho i r hh hr), hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), GenG12.addrAgree⟩
  obtain ⟨htemp, hVK⟩ := vkind57a_spec hvk
  have hvs : VStep2 ps (.prog pt) 17 18 :=
    ⟨17, Nat.le_refl _, rfl, hk17, hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have hj : E.pcOf 8 1 = pcAt GenG2.text ps.toList 17 := by
    show pcOfTab GenG2.text ps.toList tab 8 1 = _
    unfold pcOfTab; rw [h1]
  have hj' : E.pcOf 8 (1 + 1) = pcAt GenG2.text ps.toList 18 := by
    show pcOfTab GenG2.text ps.toList tab 8 2 = _
    unfold pcOfTab; rw [h2]
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -⟩ := vk57a_step (H := GenG2.H0) (env := GenG2.env)
    (L := []) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0 (g57a2Inv0 hfit)
    (fun _ h => by cases h) (pre46 hop hsy hoff hr0 hr1) hs1
  exact ⟨h55, s1, E1, m1, hs1, hr1', hx1, hE1, hp1, hm1',
    (hm1'.regs 1 _ hr1').1 1 (by simp [objX?])⟩

end GoFV.Proof.Witness.GenG57a2
