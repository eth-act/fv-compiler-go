import GoFV.Proof.Gen.G60
import GoFV.Proof.Witness.GenG54
import GoFV.Proof.Witness.GenG48
import GoFV.Asm.ConstLoad

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG60

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/math/sqrt,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "math"
func "sqrt" 1 0 0
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
config localpkg "math"
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
type t2 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t1 FUNC 8 8 8 hasptr,direct "func(float64) float64" "func(float64) float64" 0 1 1
field 0 "x" t2 ? 0
field 1 "" t2 ? 0
aux a2 sym "math.sqrt" "math.sqrt" 1 - 0 - - - - 0
posbase p51 "math/sqrt.go" 1 1 -1
aux a3 name "x" "x" PPARAM t2 0 1 used p51:100:11:0:0
aux a4 name "~r0" "~r0" PPARAMOUT t2 0 1 - p51:100:22:0:0
aux a1 call "AuxCall{math.sqrt}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 16 0
abiparam out 0 t2 a4 16 -1
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
type t14 UINT 8 8 0 comparable,named "uint" "uint"
type t15 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t16 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t17 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t8
type t18 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t6
type t19 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t10
type t20 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t12
type t21 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t15
type t22 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t13
type t23 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t2
type t24 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t17
type t25 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t26 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t27 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t28 SSA ? ? ? - "mem" ""
type t29 SSA ? ? ? - "flags" ""
type t30 SSA ? ? ? - "void" ""
type t31 SSA 16 8 ? - "int128" ""
type t32 RESULTS ? ? ? - "mem" "" 1 t28
posbase p75 "math/unsafe.go" 1 1 19
aux a5 name "f" "f" PAUTO t2 0 1 addrtaken,used p75:35:18:0:0
aux a6 type "float64" t2
type t33 PTR 8 8 8 hasptr,direct,comparable "*uint64" "*uint64" t11
posbase p72 "math/bits.go" 1 1 16
posbase p73 "math/bits.go" 1 1 17
type t34 RESULTS ? ? ? - "float64,mem" "" 2 t2,t28
posbase p74 "math/bits.go" 1 1 18
posbase p77 "math/unsafe.go" 1 1 21
aux a7 name "b" "b" PAUTO t11 0 1 addrtaken,used p77:41:22:0:0
aux a8 type "uint64" t11
posbase p76 "math/unsafe.go" 1 1 20
aux a9 name "b" "b" PAUTO t11 0 1 addrtaken,used p76:41:22:0:0
slot s1 a3 t2 0 - 0
aux a10 name "f" "f" PAUTO t2 0 1 used p72:34:12:0:0
slot s2 a10 t2 0 - 0
aux a11 name "is" "is" PAUTO t3 0 1 used p72:34:24:0:0
slot s3 a11 t3 0 - 0
aux a12 name "f" "f" PAUTO t2 0 1 used p73:46:12:0:0
slot s4 a12 t2 0 - 0
aux a13 name "sign" "sign" PAUTO t12 0 1 used p73:46:23:0:0
slot s5 a13 t12 0 - 0
aux a14 name "~r0" "~r0" PAUTO t3 0 1 used p73:46:33:0:0
slot s6 a14 t3 0 - 0
aux a15 name "~r0" "~r0" PAUTO t2 0 1 - p77:41:32:0:0
slot s7 a15 t2 0 - 0
aux a16 name "~r0" "~r0" PAUTO t2 0 1 - p74:31:12:0:0
slot s8 a16 t2 0 - 0
aux a17 name "~r0" "~r0" PAUTO t11 0 1 - p75:35:29:0:0
slot s9 a17 t11 0 - 0
aux a18 name "ix" "ix" PAUTO t11 0 1 used p51:108:2:0:0
slot s10 a18 t11 0 - 0
aux a19 name "exp" "exp" PAUTO t12 0 1 used p51:110:2:0:0
slot s11 a19 t12 0 - 0
aux a20 name "q" "q" PAUTO t11 0 1 used p51:127:6:0:0
slot s12 a20 t11 0 - 0
aux a21 name "s" "s" PAUTO t11 0 1 used p51:127:9:0:0
slot s13 a21 t11 0 - 0
aux a22 name "r" "r" PAUTO t11 0 1 used p51:128:2:0:0
slot s14 a22 t11 0 - 0
aux a23 name "t" "t" PAUTO t11 0 1 used p51:130:3:0:0
slot s15 a23 t11 0 - 0
aux a24 name "~r0" "~r0" PAUTO t2 0 1 - p76:41:32:0:0
slot s16 a24 t2 0 - 0
f b1 t1 a1 164 39
typs Bool=t3,Int8=t4,Int16=t5,Int32=t6,Int64=t7,UInt8=t8,UInt16=t9,UInt32=t10,UInt64=t11,Int=t12,Float32=t13,Float64=t2,UInt=t14,Uintptr=t15,String=t16,BytePtr=t17,Int32Ptr=t18,UInt32Ptr=t19,IntPtr=t20,UintptrPtr=t21,Float32Ptr=t22,Float64Ptr=t23,BytePtrPtr=t24,Complex64=t25,Complex128=t26,UnsafePtr=t27,Mem=t28,Flags=t29,Void=t30,Int128=t31,ResultMem=t32
b b1 If p51:103:14:0:0 0 0 - v8 b3:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 8 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p51:100:6:2:0 3 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:0:0 2 v6,v7
v v10 ConstBool t3 0 - p0:0:0:0:0 0 -
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p51:108:19:1:0 0 0 - - b22:0 b17:0
v v53 Copy t2 0 - p51:108:19:2:0 1 v33
v v54 Copy t28 0 - p51:108:19:2:0 2 v156
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v54
v v56 Store t28 0 a6 p51:108:19:0:0 6 v55,v53,v54
v v57 InlMark t30 19 - p51:108:19:1:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v59 Copy t27 0 - p75:35:71:2:0 1 v58
v v60 Copy t33 0 - p75:35:70:2:0 1 v59
v v61 NilCheck t33 0 - p75:35:45:0:0 1 v60,v56
v v62 Load t11 0 - p75:35:45:0:0 1 v61,v56
b b3 If p51:103:26:0:0 0 0 - v15 b6:0,b7:0 b1:0,b5:0
v v15 Phi t3 0 - p51:103:26:0:0 2 v8,v14
v v157 Phi t28 0 - p51:103:26:0:0 2 v1,v11
v v161 Phi t2 0 - p51:103:26:0:0 2 v6,v9
b b4 Plain p51:103:22:1:0 0 0 - - b5:0 b1:1
v v9 Copy t2 0 - p51:103:22:2:0 3 v6
v v11 Copy t28 0 - p51:103:22:2:0 2 v1
v v12 InlMark t30 16 - p51:103:22:1:0 0 v11
v v13 Neq64F t3 0 - p72:39:11:0:0 1 v9,v9
b b5 Plain p51:103:14:0:0 0 0 - - b3:1 b4:0
v v14 Copy t3 0 - p51:103:14:2:0 1 v13
b b6 If p51:103:26:0:0 0 0 - v32 b15:0,b14:0 b3:0,b13:0
v v32 Phi t3 0 - p51:103:26:0:0 1 v15,v31
v v156 Phi t28 0 - p51:103:26:0:0 3 v157,v158
v v160 Phi t2 0 - p51:103:26:0:0 2 v161,v162
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v16 Copy t2 0 - p51:103:34:2:0 5 v161
v v18 Copy t28 0 - p51:103:34:2:0 3 v157
v v19 InlMark t30 17 - p51:103:34:1:0 0 v18
v v21 Eq64 t3 0 - p73:51:10:0:0 1 v17,v20
b b8 Plain p51:103:34:1:0 0 0 - - b13:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:0:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:0:0 1 v29,v28
v v158 Phi t28 0 - p51:103:34:0:0 1 v18,v159
v v162 Phi t2 0 - p51:103:34:0:0 1 v16,v163
b b9 Plain p73:52:10:0:0 0 0 - - b8:0 b7:0
v v22 Copy t2 0 - p73:52:10:2:0 1 v16
v v23 Abs t2 0 - p73:52:10:0:0 1 v22
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v24 Copy t12 0 - p73:53:17:2:0 1 v17
v v25 Less64 t3 0 - p73:53:17:0:0 1 v24,v20
b b11 Plain p73:56:11:2:0 0 0 - - b8:1 b10:1,b12:0
v v159 Copy t28 0 - p51:106:13:2:0 1 v18
v v163 Copy t2 0 - p51:104:3:2:0 1 v16
v v164 Phi t2 0 - p0:0:0:0:0 1 v16,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v26 Copy t2 0 - p73:54:7:2:0 1 v16
v v27 Neg64F t2 0 - p73:54:7:0:0 1 v26
b b13 Plain p51:103:26:0:0 0 0 - - b6:1 b8:0
v v31 Copy t3 0 - p51:103:26:2:0 1 v30
b b14 If p51:105:11:0:0 0 0 - v34 b18:0,b17:0 b6:1
v v33 Copy t2 0 - p51:105:9:2:0 2 v160
v v34 Less64F t3 0 - p51:105:9:0:0 1 v33,v7
b b15 Plain p51:103:2:1:0 0 0 - - b16:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b15:0
v v35 Copy t2 0 - p51:104:3:2:0 1 v160
v v36 Copy t28 0 - p51:104:3:2:0 1 v156
v v37 MakeResult t34 0 - p51:104:3:0:0 1 v35,v36
b b17 Plain p51:102:2:1:0 0 0 - - b2:0 b14:1
b b18 Plain p51:105:2:1:0 0 0 - - b19:0 b14:0
b b19 Plain p74:31:44:1:0 0 0 - - b20:0 b18:0
v v38 Copy t28 0 - p51:106:13:2:0 3 v156
v v39 InlMark t30 18 - p51:106:13:1:0 0 v38
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v38
v v42 Store t28 0 a8 p74:31:44:0:0 5 v41,v40,v38
v v43 InlMark t30 21 - p74:31:44:1:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v45 Copy t27 0 - p77:41:76:2:0 1 v44
v v46 Copy t23 0 - p77:41:75:2:0 1 v45
v v47 NilCheck t23 0 - p77:41:49:0:0 1 v46,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
b b20 Plain p51:106:13:1:0 0 0 - - b21:0 b19:0
v v49 Copy t2 0 - p51:106:13:2:0 1 v48
b b21 Ret p51:106:3:1:0 0 0 - v52 - b20:0
v v50 Copy t2 0 - p51:106:3:2:0 1 v49
v v51 Copy t28 0 - p51:106:3:2:0 1 v42
v v52 MakeResult t34 0 - p51:106:3:0:0 1 v50,v51
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b2:0
v v63 Copy t11 0 - p51:108:5:2:0 3 v62
v v65 Rsh64Ux64 t11 0 - p51:110:17:0:0 1 v63,v64
v v67 And64 t11 0 - p51:110:27:0:0 1 v65,v66
v v68 Copy t12 0 - p51:110:27:2:0 3 v67
v v69 Eq64 t3 0 - p51:111:9:0:0 1 v68,v20
b b23 If p51:121:14:0:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v68,v81
v v84 Sub64 t12 0 - p51:118:6:0:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:0:0 1 v63,v70
v v87 Com64 t11 0 - p51:119:5:0:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:0:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:0:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
v v148 Phi t28 0 - p51:118:6:0:0 1 v56,v149
b b24 Plain p51:112:9:2:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b26:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v63,v77
v v72 And64 t11 0 - p51:112:9:0:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v149 Copy t28 0 - p51:144:24:2:0 1 v56
v v155 Phi t12 0 - p51:112:21:0:0 2 v68,v79
b b26 Plain p51:114:7:0:0 0 0 - - b27:0 b25:0
v v75 Copy t11 0 - p51:113:7:2:0 1 v70
v v77 Lsh64x64 t11 0 - p51:113:7:0:0 1 v75,v76
v v78 Copy t12 0 - p51:114:7:2:0 1 v155
v v79 Sub64 t12 0 - p51:114:7:0:0 1 v78,v17
b b27 Plain p51:112:24:0:0 0 0 - - b25:1 b26:0
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v80 Copy t12 0 - p51:116:6:2:0 1 v155
v v81 Add64 t12 0 - p51:116:6:0:0 1 v80,v17
b b29 Plain p51:129:2:0:0 0 0 - - b31:0 b23:1,b30:0
v v94 Copy t12 0 - p51:124:6:2:0 1 v84
v v95 Rsh64x64 t12 0 - p51:124:6:0:0 1 v94,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:0:0 1 v96,v76
v v146 Copy t28 0 - p51:144:24:2:0 1 v148
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v92 Copy t11 0 - p51:122:6:2:0 1 v89
v v93 Lsh64x64 t11 0 - p51:122:6:0:0 1 v92,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 2 v98,v116
v v100 Neq64 t3 0 - p51:129:8:0:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 4 v73,v144
v v145 Phi t28 0 - p51:129:8:0:0 2 v146,v147
v v150 Phi t12 0 - p51:129:8:0:0 2 v95,v151
v v152 Phi t11 0 - p51:129:8:0:0 2 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 1 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b35:0 b31:0
v v101 Copy t11 0 - p51:130:10:2:0 2 v153
v v102 Copy t11 0 - p51:130:10:2:0 3 v99
v v103 Add64 t11 0 - p51:130:10:0:0 2 v101,v102
v v104 Copy t11 0 - p51:131:8:2:0 3 v152
v v105 Leq64U t3 0 - p51:131:8:0:0 1 v103,v104
b b33 Plain p51:129:11:0:0 0 0 - - b31:1 b35:0
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b37:0 b31:1
v v117 Copy t11 0 - p51:140:8:2:0 1 v152
v v118 Neq64 t3 0 - p51:140:8:0:0 1 v117,v73
b b35 Plain p51:137:9:0:0 0 0 - - b33:0 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v104,v110
v v114 Lsh64x64 t11 0 - p51:136:6:0:0 1 v113,v76
v v115 Phi t11 0 - p51:136:6:0:0 1 v102,v107
v v116 Rsh64Ux64 t11 0 - p51:137:5:0:0 1 v115,v76
v v144 Phi t11 0 - p51:136:6:0:0 1 v143,v112
v v147 Copy t28 0 - p51:144:24:2:0 1 v145
v v151 Copy t12 0 - p51:143:24:2:0 1 v150
v v154 Phi t11 0 - p51:136:6:0:0 1 v101,v108
b b36 Plain p51:134:6:0:0 0 0 - - b35:1 b32:0
v v106 Copy t11 0 - p51:132:10:2:0 2 v103
v v107 Copy t11 0 - p51:132:10:2:0 3 v102
v v108 Add64 t11 0 - p51:132:10:0:0 1 v106,v107
v v109 Copy t11 0 - p51:133:7:2:0 1 v104
v v110 Sub64 t11 0 - p51:133:7:0:0 1 v109,v106
v v111 Copy t11 0 - p51:134:6:2:0 1 v143
v v112 Add64 t11 0 - p51:134:6:0:0 1 v111,v107
b b37 Plain p51:144:24:1:0 0 0 - - b39:0 b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:0:0 1 v123,v76
v v125 Copy t12 0 - p51:143:24:2:0 1 v150
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v125,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v128 Copy t11 0 - p51:143:26:2:0 1 v127
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v128,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v131 Copy t28 0 - p51:144:24:2:0 2 v145
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v131
v v133 Store t28 0 a8 p51:144:24:0:0 5 v132,v130,v131
v v134 InlMark t30 20 - p51:144:24:1:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v136 Copy t27 0 - p76:41:76:2:0 1 v135
v v137 Copy t23 0 - p76:41:75:2:0 1 v136
v v138 NilCheck t23 0 - p76:41:49:0:0 1 v137,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
b b38 Plain p51:141:12:0:0 0 0 - - b37:1 b34:0
v v119 Copy t11 0 - p51:141:5:2:0 2 v143
v v121 And64 t11 0 - p51:141:10:0:0 1 v119,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v119,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b37:0
v v140 Copy t2 0 - p51:144:2:2:0 1 v139
v v141 Copy t28 0 - p51:144:2:2:0 1 v133
v v142 MakeResult t34 0 - p51:144:2:0:0 1 v140,v141
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6,v9,v16,v33,v35,v53,v160,v161,v162,v163
named s2 v9
named s3 v10,v13,v14
named s4 v16,v22,v23,v26,v27,v28,v164
named s5 v17,v24
named s6 v30,v31
named s7 v48,v49
named s8 v49,v50
named s9 v62,v63
named s10 v63,v70,v75,v77,v85,v88,v89,v92,v93,v96,v97,v104,v109,v110,v113,v114,v117,v130,v152
named s11 v68,v78,v79,v80,v81,v82,v84,v94,v95,v125,v150,v151,v155
named s12 v73,v111,v112,v119,v122,v123,v143,v144
named s13 v73,v101,v108,v153,v154
named s14 v98,v99,v102,v107,v115,v116
named s15 v103,v106
named s16 v139,v140
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v10,v20,v73,1=v17,v76,v120,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev -
freeb -
dcllen 22
end
pass 1 "number lines"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b3:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 4 -
v v2 SP t15 0 - p0:0:0:0:0 8 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p51:100:6:2:0 3 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 2 v6,v7
v v10 ConstBool t3 0 - p0:0:0:0:0 0 -
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p51:108:19:1:0 0 0 - - b22:0 b17:0
v v53 Copy t2 0 - p51:108:19:2:0 1 v33
v v54 Copy t28 0 - p51:108:19:2:0 2 v156
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v54
v v56 Store t28 0 a6 p51:108:19:1:0 6 v55,v53,v54
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v59 Copy t27 0 - p75:35:71:2:0 1 v58
v v60 Copy t33 0 - p75:35:70:2:0 1 v59
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v60,v56
v v62 Load t11 0 - p75:35:45:0:0 1 v61,v56
b b3 If p51:103:26:0:0 0 0 - v15 b6:0,b7:0 b1:0,b5:0
v v15 Phi t3 0 - p51:103:26:0:0 2 v8,v14
v v157 Phi t28 0 - p51:103:26:0:0 2 v1,v11
v v161 Phi t2 0 - p51:103:26:0:0 2 v6,v9
b b4 Plain p51:103:22:1:0 0 0 - - b5:0 b1:1
v v9 Copy t2 0 - p51:103:22:2:0 3 v6
v v11 Copy t28 0 - p51:103:22:2:0 2 v1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v11
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v9,v9
b b5 Plain p51:103:14:0:0 0 0 - - b3:1 b4:0
v v14 Copy t3 0 - p51:103:14:2:0 1 v13
b b6 If p51:103:26:0:0 0 0 - v32 b15:0,b14:0 b3:0,b13:0
v v32 Phi t3 0 - p51:103:26:0:0 1 v15,v31
v v156 Phi t28 0 - p51:103:26:0:0 3 v157,v158
v v160 Phi t2 0 - p51:103:26:0:0 2 v161,v162
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v16 Copy t2 0 - p51:103:34:2:0 5 v161
v v18 Copy t28 0 - p51:103:34:2:0 3 v157
v v19 InlMark t30 17 - p51:103:34:0:0 0 v18
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b8 Plain p51:103:34:1:0 0 0 - - b13:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
v v158 Phi t28 0 - p51:103:34:1:0 1 v18,v159
v v162 Phi t2 0 - p51:103:34:0:0 1 v16,v163
b b9 Plain p73:52:10:0:0 0 0 - - b8:0 b7:0
v v22 Copy t2 0 - p73:52:10:2:0 1 v16
v v23 Abs t2 0 - p73:52:10:1:0 1 v22
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v24 Copy t12 0 - p73:53:17:2:0 1 v17
v v25 Less64 t3 0 - p73:53:17:1:0 1 v24,v20
b b11 Plain p0:0:0:0:0 0 0 - - b8:1 b10:1,b12:0
v v159 Copy t28 0 - p51:106:13:2:0 1 v18
v v163 Copy t2 0 - p51:104:3:2:0 1 v16
v v164 Phi t2 0 - p0:0:0:0:0 1 v16,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v26 Copy t2 0 - p73:54:7:2:0 1 v16
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v26
b b13 Plain p51:103:26:0:0 0 0 - - b6:1 b8:0
v v31 Copy t3 0 - p51:103:26:2:0 1 v30
b b14 If p51:105:11:0:0 0 0 - v34 b18:0,b17:0 b6:1
v v33 Copy t2 0 - p51:105:9:2:0 2 v160
v v34 Less64F t3 0 - p51:105:9:1:0 1 v33,v7
b b15 Plain p51:103:2:1:0 0 0 - - b16:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b15:0
v v35 Copy t2 0 - p51:104:3:2:0 1 v160
v v36 Copy t28 0 - p51:104:3:2:0 1 v156
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v35,v36
b b17 Plain p51:102:2:1:0 0 0 - - b2:0 b14:1
b b18 Plain p51:105:2:1:0 0 0 - - b19:0 b14:0
b b19 Plain p74:31:44:1:0 0 0 - - b20:0 b18:0
v v38 Copy t28 0 - p51:106:13:2:0 3 v156
v v39 InlMark t30 18 - p51:106:13:1:0 0 v38
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v38
v v42 Store t28 0 a8 p74:31:44:1:0 5 v41,v40,v38
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v45 Copy t27 0 - p77:41:76:2:0 1 v44
v v46 Copy t23 0 - p77:41:75:2:0 1 v45
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v46,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
b b20 Plain p51:106:13:1:0 0 0 - - b21:0 b19:0
v v49 Copy t2 0 - p51:106:13:2:0 1 v48
b b21 Ret p51:106:3:1:0 0 0 - v52 - b20:0
v v50 Copy t2 0 - p51:106:3:2:0 1 v49
v v51 Copy t28 0 - p51:106:3:2:0 1 v42
v v52 MakeResult t34 0 - p51:106:3:0:0 1 v50,v51
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b2:0
v v63 Copy t11 0 - p51:108:5:2:0 3 v62
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v63,v64
v v67 And64 t11 0 - p51:110:27:0:0 1 v65,v66
v v68 Copy t12 0 - p51:110:27:2:0 3 v67
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v68,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v68,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:0:0 1 v63,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
v v148 Phi t28 0 - p51:118:6:1:0 1 v56,v149
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b26:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v63,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v149 Copy t28 0 - p51:144:24:2:0 1 v56
v v155 Phi t12 0 - p51:112:21:0:0 2 v68,v79
b b26 Plain p51:114:7:0:0 0 0 - - b27:0 b25:0
v v75 Copy t11 0 - p51:113:7:2:0 1 v70
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v75,v76
v v78 Copy t12 0 - p51:114:7:2:0 1 v155
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v78,v17
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b26:0
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v80 Copy t12 0 - p51:116:6:2:0 1 v155
v v81 Add64 t12 0 - p51:116:6:1:0 1 v80,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v94 Copy t12 0 - p51:124:6:2:0 1 v84
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 1 v94,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
v v146 Copy t28 0 - p51:144:24:2:0 1 v148
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v92 Copy t11 0 - p51:122:6:2:0 1 v89
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v92,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 2 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 4 v73,v144
v v145 Phi t28 0 - p51:129:8:0:0 2 v146,v147
v v150 Phi t12 0 - p51:129:8:0:0 2 v95,v151
v v152 Phi t11 0 - p51:129:8:0:0 2 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 1 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b35:0 b31:0
v v101 Copy t11 0 - p51:130:10:2:0 2 v153
v v102 Copy t11 0 - p51:130:10:2:0 3 v99
v v103 Add64 t11 0 - p51:130:10:1:0 2 v101,v102
v v104 Copy t11 0 - p51:131:8:2:0 3 v152
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v104
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b35:0
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b37:0 b31:1
v v117 Copy t11 0 - p51:140:8:2:0 1 v152
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v117,v73
b b35 Plain p51:137:9:1:0 0 0 - - b33:0 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v104,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v115 Phi t11 0 - p51:136:6:0:0 1 v102,v107
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v115,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v147 Copy t28 0 - p51:144:24:2:0 1 v145
v v151 Copy t12 0 - p51:143:24:2:0 1 v150
v v154 Phi t11 0 - p51:136:6:0:0 1 v101,v108
b b36 Plain p51:134:6:0:0 0 0 - - b35:1 b32:0
v v106 Copy t11 0 - p51:132:10:2:0 2 v103
v v107 Copy t11 0 - p51:132:10:2:0 3 v102
v v108 Add64 t11 0 - p51:132:10:1:0 1 v106,v107
v v109 Copy t11 0 - p51:133:7:2:0 1 v104
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v109,v106
v v111 Copy t11 0 - p51:134:6:2:0 1 v143
v v112 Add64 t11 0 - p51:134:6:1:0 1 v111,v107
b b37 Plain p51:144:24:1:0 0 0 - - b39:0 b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v125 Copy t12 0 - p51:143:24:2:0 1 v150
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v125,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v128 Copy t11 0 - p51:143:26:2:0 1 v127
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v128,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v131 Copy t28 0 - p51:144:24:2:0 2 v145
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v131
v v133 Store t28 0 a8 p51:144:24:1:0 5 v132,v130,v131
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v136 Copy t27 0 - p76:41:76:2:0 1 v135
v v137 Copy t23 0 - p76:41:75:2:0 1 v136
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v137,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
b b38 Plain p51:141:12:0:0 0 0 - - b37:1 b34:0
v v119 Copy t11 0 - p51:141:5:2:0 2 v143
v v121 And64 t11 0 - p51:141:10:1:0 1 v119,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v119,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b37:0
v v140 Copy t2 0 - p51:144:2:2:0 1 v139
v v141 Copy t28 0 - p51:144:2:2:0 1 v133
v v142 MakeResult t34 0 - p51:144:2:0:0 1 v140,v141
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6,v9,v16,v33,v35,v53,v160,v161,v162,v163
named s2 v9
named s3 v10,v13,v14
named s4 v16,v22,v23,v26,v27,v28,v164
named s5 v17,v24
named s6 v30,v31
named s7 v48,v49
named s8 v49,v50
named s9 v62,v63
named s10 v63,v70,v75,v77,v85,v88,v89,v92,v93,v96,v97,v104,v109,v110,v113,v114,v117,v130,v152
named s11 v68,v78,v79,v80,v81,v82,v84,v94,v95,v125,v150,v151,v155
named s12 v73,v111,v112,v119,v122,v123,v143,v144
named s13 v73,v101,v108,v153,v154
named s14 v98,v99,v102,v107,v115,v116
named s15 v103,v106
named s16 v139,v140
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v10,v20,v73,1=v17,v76,v120,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev -
freeb -
cache postorder b16,b15,b21,b20,b19,b18,b27,b26,b33,b35,b36,b32,b39,b37,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b2,b17,b14,b6,b13,b8,b9,b11,b12,b10,b7,b3,b5,b4,b1
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b3:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 19 -
v v2 SP t15 0 - p0:0:0:0:0 8 -
v v3 SB t15 0 - p0:0:0:0:0 0 -
v v4 LocalAddr t23 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t23 0 a4 p0:0:0:0:0 0 v2,v1
v v6 Arg t2 0 a3 p51:100:6:2:0 20 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 2 v6,v7
v v10 ConstBool t3 0 - p0:0:0:0:0 0 -
v v17 Const64 t12 1 - p0:0:0:0:0 8 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p51:108:19:1:0 0 0 - - b22:0 b17:0
v v53 Copy t2 0 - p51:108:19:2:0 0 v6
v v54 Copy t28 0 - p51:108:19:2:0 0 v1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 12 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 3 v2,v56
v v59 Copy t27 0 - p75:35:71:2:0 0 v58
v v60 Copy t33 0 - p75:35:70:2:0 0 v58
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v58,v56
v v62 Load t11 0 - p75:35:45:0:0 4 v61,v56
b b3 If p51:103:26:0:0 0 0 - v15 b6:0,b7:0 b1:0,b5:0
v v15 Phi t3 0 - p51:103:26:0:0 2 v8,v13
v v157 Copy t28 0 - p51:103:26:0:0 0 v1
v v161 Copy t2 0 - p51:103:26:0:0 0 v6
b b4 Plain p51:103:22:1:0 0 0 - - b5:0 b1:1
v v9 Copy t2 0 - p51:103:22:2:0 0 v6
v v11 Copy t28 0 - p51:103:22:2:0 0 v1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 2 v6,v6
b b5 Plain p51:103:14:0:0 0 0 - - b3:1 b4:0
v v14 Copy t3 0 - p51:103:14:2:0 0 v13
b b6 If p51:103:26:0:0 0 0 - v32 b15:0,b14:0 b3:0,b13:0
v v32 Phi t3 0 - p51:103:26:0:0 1 v15,v30
v v156 Copy t28 0 - p51:103:26:0:0 0 v1
v v160 Copy t2 0 - p51:103:26:0:0 0 v6
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v16 Copy t2 0 - p51:103:34:2:0 0 v6
v v18 Copy t28 0 - p51:103:34:2:0 0 v1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b8 Plain p51:103:34:1:0 0 0 - - b13:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 2 v29,v28
v v158 Copy t28 0 - p51:103:34:1:0 0 v1
v v162 Copy t2 0 - p51:103:34:0:0 0 v6
b b9 Plain p73:52:10:0:0 0 0 - - b8:0 b7:0
v v22 Copy t2 0 - p73:52:10:2:0 0 v6
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v24 Copy t12 0 - p73:53:17:2:0 0 v17
v v25 Less64 t3 0 - p73:53:17:1:0 1 v17,v20
b b11 Plain p0:0:0:0:0 0 0 - - b8:1 b10:1,b12:0
v v159 Copy t28 0 - p51:106:13:2:0 0 v1
v v163 Copy t2 0 - p51:104:3:2:0 0 v6
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v26 Copy t2 0 - p73:54:7:2:0 0 v6
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b13 Plain p51:103:26:0:0 0 0 - - b6:1 b8:0
v v31 Copy t3 0 - p51:103:26:2:0 0 v30
b b14 If p51:105:11:0:0 0 0 - v34 b18:0,b17:0 b6:1
v v33 Copy t2 0 - p51:105:9:2:0 0 v6
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b15 Plain p51:103:2:1:0 0 0 - - b16:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b15:0
v v35 Copy t2 0 - p51:104:3:2:0 0 v6
v v36 Copy t28 0 - p51:104:3:2:0 0 v1
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b17 Plain p51:102:2:1:0 0 0 - - b2:0 b14:1
b b18 Plain p51:105:2:1:0 0 0 - - b19:0 b14:0
b b19 Plain p74:31:44:1:0 0 0 - - b20:0 b18:0
v v38 Copy t28 0 - p51:106:13:2:0 0 v1
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 6 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 3 v2,v42
v v45 Copy t27 0 - p77:41:76:2:0 0 v44
v v46 Copy t23 0 - p77:41:75:2:0 0 v44
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v44,v42
v v48 Load t2 0 - p77:41:49:0:0 3 v47,v42
b b20 Plain p51:106:13:1:0 0 0 - - b21:0 b19:0
v v49 Copy t2 0 - p51:106:13:2:0 0 v48
b b21 Ret p51:106:3:1:0 0 0 - v52 - b20:0
v v50 Copy t2 0 - p51:106:3:2:0 0 v48
v v51 Copy t28 0 - p51:106:3:2:0 0 v42
v v52 MakeResult t34 0 - p51:106:3:0:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b2:0
v v63 Copy t11 0 - p51:108:5:2:0 0 v62
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 4 v65,v66
v v68 Copy t12 0 - p51:110:27:2:0 0 v67
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 3 v82,v83
v v85 Phi t11 0 - p51:118:6:0:0 1 v62,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 3 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
v v148 Copy t28 0 - p51:118:6:1:0 0 v56
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b26:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v149 Copy t28 0 - p51:144:24:2:0 0 v56
v v155 Phi t12 0 - p51:112:21:0:0 4 v67,v79
b b26 Plain p51:114:7:0:0 0 0 - - b27:0 b25:0
v v75 Copy t11 0 - p51:113:7:2:0 0 v70
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v70,v76
v v78 Copy t12 0 - p51:114:7:2:0 0 v155
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v155,v17
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b26:0
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v80 Copy t12 0 - p51:116:6:2:0 0 v155
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v94 Copy t12 0 - p51:124:6:2:0 0 v84
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 4 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
v v146 Copy t28 0 - p51:144:24:2:0 0 v56
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v92 Copy t11 0 - p51:122:6:2:0 0 v89
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 8 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 7 v73,v144
v v145 Copy t28 0 - p51:129:8:0:0 0 v56
v v150 Copy t12 0 - p51:129:8:0:0 0 v95
v v152 Phi t11 0 - p51:129:8:0:0 7 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 3 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b35:0 b31:0
v v101 Copy t11 0 - p51:130:10:2:0 0 v153
v v102 Copy t11 0 - p51:130:10:2:0 0 v99
v v103 Add64 t11 0 - p51:130:10:1:0 4 v153,v99
v v104 Copy t11 0 - p51:131:8:2:0 0 v152
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b35:0
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b37:0 b31:1
v v117 Copy t11 0 - p51:140:8:2:0 0 v152
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b35 Plain p51:137:9:1:0 0 0 - - b33:0 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v115 Copy t11 0 - p51:136:6:0:0 0 v99
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v147 Copy t28 0 - p51:144:24:2:0 0 v56
v v151 Copy t12 0 - p51:143:24:2:0 0 v95
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b36 Plain p51:134:6:0:0 0 0 - - b35:1 b32:0
v v106 Copy t11 0 - p51:132:10:2:0 0 v103
v v107 Copy t11 0 - p51:132:10:2:0 0 v99
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v109 Copy t11 0 - p51:133:7:2:0 0 v152
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v111 Copy t11 0 - p51:134:6:2:0 0 v143
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b37 Plain p51:144:24:1:0 0 0 - - b39:0 b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v125 Copy t12 0 - p51:143:24:2:0 0 v95
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v95,v17
v v127 Add64 t12 0 - p51:143:26:0:0 2 v126,v83
v v128 Copy t11 0 - p51:143:26:2:0 0 v127
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v131 Copy t28 0 - p51:144:24:2:0 0 v56
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 6 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 3 v2,v133
v v136 Copy t27 0 - p76:41:76:2:0 0 v135
v v137 Copy t23 0 - p76:41:75:2:0 0 v135
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v135,v133
v v139 Load t2 0 - p76:41:49:0:0 2 v138,v133
b b38 Plain p51:141:12:0:0 0 0 - - b37:1 b34:0
v v119 Copy t11 0 - p51:141:5:2:0 0 v143
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b37:0
v v140 Copy t2 0 - p51:144:2:2:0 0 v139
v v141 Copy t28 0 - p51:144:2:2:0 0 v133
v v142 MakeResult t34 0 - p51:144:2:0:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6,v6,v6,v6,v6,v6,v6,v6,v6,v6
named s2 v6
named s3 v10,v13,v13
named s4 v6,v6,v23,v6,v27,v28,v164
named s5 v17,v17
named s6 v30,v30
named s7 v48,v48
named s8 v48,v48
named s9 v62,v62
named s10 v62,v70,v70,v77,v85,v88,v89,v89,v93,v96,v97,v152,v152,v110,v113,v114,v152,v130,v152
named s11 v67,v155,v79,v155,v81,v82,v84,v84,v95,v95,v95,v95,v155
named s12 v73,v143,v112,v143,v122,v123,v143,v144
named s13 v73,v153,v108,v153,v154
named s14 v98,v99,v99,v99,v99,v116
named s15 v103,v103
named s16 v139,v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v10,v20,v73,1=v17,v76,v120,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev -
freeb -
cache postorder b16,b15,b21,b20,b19,b18,b27,b26,b33,b35,b36,b32,b39,b37,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b2,b17,b14,b6,b13,b8,b9,b11,b12,b10,b7,b3,b5,b4,b1
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 3 "early deadcode"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b3:0,b4:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 2 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b2 Plain p51:108:19:1:0 0 0 - - b22:0 b17:0
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 6 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v58,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v61,v56
b b3 If p51:103:26:0:0 0 0 - v15 b6:0,b7:0 b1:0,b5:0
v v15 Phi t3 0 - p51:103:26:0:0 2 v8,v13
b b4 Plain p51:103:22:1:0 0 0 - - b5:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b5 Plain p51:103:14:0:0 0 0 - - b3:1 b4:0
b b6 If p51:103:26:0:0 0 0 - v32 b15:0,b14:0 b3:0,b13:0
v v32 Phi t3 0 - p51:103:26:0:0 1 v15,v30
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b8 Plain p51:103:34:1:0 0 0 - - b13:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
b b9 Plain p73:52:10:0:0 0 0 - - b8:0 b7:0
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v25 Less64 t3 0 - p73:53:17:1:0 1 v17,v20
b b11 Plain p0:0:0:0:0 0 0 - - b8:1 b10:1,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b13 Plain p51:103:26:0:0 0 0 - - b6:1 b8:0
b b14 If p51:105:11:0:0 0 0 - v34 b18:0,b17:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b15 Plain p51:103:2:1:0 0 0 - - b16:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b15:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b17 Plain p51:102:2:1:0 0 0 - - b2:0 b14:1
b b18 Plain p51:105:2:1:0 0 0 - - b19:0 b14:0
b b19 Plain p74:31:44:1:0 0 0 - - b20:0 b18:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 5 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v44,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
b b20 Plain p51:106:13:1:0 0 0 - - b21:0 b19:0
b b21 Ret p51:106:3:1:0 0 0 - v52 - b20:0
v v52 MakeResult t34 0 - p51:106:3:0:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b2:0
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b26:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b26 Plain p51:114:7:0:0 0 0 - - b27:0 b25:0
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v70,v76
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v155,v17
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b26:0
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b35:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b35:0
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b37:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b35 Plain p51:137:9:1:0 0 0 - - b33:0 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b36 Plain p51:134:6:0:0 0 0 - - b35:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b37 Plain p51:144:24:1:0 0 0 - - b39:0 b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v95,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 5 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v135,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
b b38 Plain p51:141:12:0:0 0 0 - - b37:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b37:0
v v142 MakeResult t34 0 - p51:144:2:0:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev v141,v140,v119,v137,v136,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb -
cache postorder b16,b15,b21,b20,b19,b18,b27,b26,b33,b35,b36,b32,b39,b37,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b2,b17,b14,b6,b13,b8,b9,b11,b12,b10,b7,b3,b5,b4,b1
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 4 "short circuit"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v141 ConstBool t3 1 - p0:0:0:0:0 0 -
b b2 BlockInvalid p51:108:19:1:0 0 0 - - - -
b b3 If p51:103:26:0:0 0 0 - v15 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v15 Copy t3 0 - p51:103:26:1:0 1 v13
b b4 BlockInvalid p51:103:22:1:0 0 0 - - - -
b b5 BlockInvalid p51:103:22:1:0 0 0 - - - -
b b6 If p51:103:26:0:0 0 0 - v32 b16:0,b14:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
v v32 Copy t3 0 - p51:103:26:1:0 1 v30
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b8 BlockInvalid p51:103:34:1:0 0 0 - - - -
b b9 Plain p73:52:10:0:0 0 0 - - b6:0 b7:0
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v25 Less64 t3 0 - p73:53:17:1:0 1 v17,v20
b b11 Plain p0:0:0:0:0 0 0 - - b6:1 b10:1,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b13 BlockInvalid p51:103:34:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b15 BlockInvalid p51:103:2:1:0 0 0 - - - -
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b17 BlockInvalid p51:102:2:1:0 0 0 - - - -
b b18 BlockInvalid p51:105:2:1:0 0 0 - - - -
b b19 BlockInvalid p74:31:44:1:0 0 0 - - - -
b b20 BlockInvalid p51:106:13:1:0 0 0 - - - -
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 5 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v44,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 6 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v58,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v61,v56
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b26 BlockInvalid p51:114:7:0:0 0 0 - - - -
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v70,v76
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v155,v17
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b35 BlockInvalid p51:137:9:1:0 0 0 - - - -
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b37 BlockInvalid p51:144:24:1:0 0 0 - - - -
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v95,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 5 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v135,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,v141,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev v140,v119,v137,v136,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb -
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 5 "decompose user"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v141 ConstBool t3 1 - p0:0:0:0:0 0 -
b b2 BlockInvalid p51:108:19:1:0 0 0 - - - -
b b3 If p51:103:26:0:0 0 0 - v15 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v15 Copy t3 0 - p51:103:26:1:0 1 v13
b b4 BlockInvalid p51:103:22:1:0 0 0 - - - -
b b5 BlockInvalid p51:103:22:1:0 0 0 - - - -
b b6 If p51:103:26:0:0 0 0 - v32 b16:0,b14:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
v v32 Copy t3 0 - p51:103:26:1:0 1 v30
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b8 BlockInvalid p51:103:34:1:0 0 0 - - - -
b b9 Plain p73:52:10:0:0 0 0 - - b6:0 b7:0
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v25 Less64 t3 0 - p73:53:17:1:0 1 v17,v20
b b11 Plain p0:0:0:0:0 0 0 - - b6:1 b10:1,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b13 BlockInvalid p51:103:34:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b15 BlockInvalid p51:103:2:1:0 0 0 - - - -
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b17 BlockInvalid p51:102:2:1:0 0 0 - - - -
b b18 BlockInvalid p51:105:2:1:0 0 0 - - - -
b b19 BlockInvalid p74:31:44:1:0 0 0 - - - -
b b20 BlockInvalid p51:106:13:1:0 0 0 - - - -
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 5 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v44,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 6 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v58,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v61,v56
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b26 BlockInvalid p51:114:7:0:0 0 0 - - - -
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v70,v76
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v155,v17
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b35 BlockInvalid p51:137:9:1:0 0 0 - - - -
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b37 BlockInvalid p51:144:24:1:0 0 0 - - - -
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v95,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 5 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v135,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,v141,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev v140,v119,v137,v136,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb -
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 7 -
v v20 Const64 t12 0 - p0:0:0:0:0 3 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v83 Const64 t12 1023 - p0:0:0:0:0 2 -
v v86 Const64 t11 9218868437227405312 - p0:0:0:0:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:0:0 0 0 - v30 b16:0,b14:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
b b7 If p73:51:13:0:0 0 0 - v21 b9:0,b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v21 Eq64 t3 0 - p73:51:10:1:0 1 v17,v20
b b9 Plain p73:52:10:0:0 0 0 - - b6:0 b7:0
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 If p73:53:19:0:0 0 0 - v25 b12:0,b11:0 b7:1
v v25 Less64 t3 0 - p73:53:17:1:0 1 v17,v20
b b11 Plain p0:0:0:0:0 0 0 - - b6:1 b10:1,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:0
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 5 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:0:0 1 v2,v42
v v47 NilCheck t23 0 - p77:41:49:1:0 1 v44,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v47,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 6 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:0:0 1 v2,v56
v v61 NilCheck t33 0 - p75:35:45:1:0 1 v58,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v61,v56
v v65 Rsh64Ux64 t11 0 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Sub64 t12 0 - p51:118:6:1:0 2 v82,v83
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v87 Com64 t11 0 - p51:119:5:1:0 1 v86
v v88 And64 t11 0 - p51:119:5:0:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v90 And64 t12 0 - p51:121:8:1:0 1 v84,v17
v v91 Eq64 t3 0 - p51:121:11:0:0 1 v90,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 0 - p51:113:7:1:0 1 v70,v76
v v79 Sub64 t12 0 - p51:114:7:1:0 1 v155,v17
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 0 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 0 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 0 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 0 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 0 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 0 - p51:143:8:1:0 1 v123,v76
v v126 Sub64 t12 0 - p51:143:24:0:0 1 v95,v17
v v127 Add64 t12 0 - p51:143:26:0:0 1 v126,v83
v v129 Lsh64x64 t11 0 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 5 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:0:0 1 v2,v133
v v138 NilCheck t23 0 - p76:41:49:1:0 1 v135,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v138,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,1023=v83,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9218868437227405312=v86,9221120237041090561=v40
freev v32,v15,v141,v140,v119,v137,v136,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 7 "opt"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 1 -
v v20 Const64 t12 0 - p0:0:0:0:0 1 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:0:0 0 0 - v30 b16:0,b14:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
b b7 First p73:51:13:1:0 0 0 - - b10:0,b9:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b9 Plain p73:52:10:0:0 0 0 - - b6:0 b7:1
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 First p73:53:19:1:0 0 0 - - b11:0,b12:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:1 b10:0,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:1
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:1:0 1 v2,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v44,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 5 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:1:0 1 v2,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v58,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v32,v82
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v88 And64 t11 0 - p51:119:5:1:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v15,v140
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v141
v v141 Const64 t12 1 - p51:121:11:0:0 1 -
v v140 Const64 t12 0 - p51:121:11:0:0 1 -
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v119,v155
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:1:0 1 v2,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v135,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 8 "zero arg cse"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 9 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:0:0 0 0 - v30 b16:0,b14:0 b9:0,b11:0
v v28 Phi t2 0 - p51:103:34:1:0 1 v23,v164
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v28
b b7 First p73:51:13:1:0 0 0 - - b10:0,b9:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b9 Plain p73:52:10:0:0 0 0 - - b6:0 b7:1
v v23 Abs t2 0 - p73:52:10:1:0 1 v6
b b10 First p73:53:19:1:0 0 0 - - b11:0,b12:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:1 b10:0,b12:0
v v164 Phi t2 0 - p0:0:0:0:0 1 v6,v27
b b12 Plain p73:54:7:0:0 0 0 - - b11:1 b10:1
v v27 Neg64F t2 0 - p73:54:7:1:0 1 v6
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:1:0 1 v2,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v44,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 5 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:1:0 1 v2,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v58,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v32,v82
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v140 Const64 t12 0 - p51:121:11:0:0 0 -
v v88 And64 t11 0 - p51:119:5:1:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v15,v20
v v141 Const64 t12 1 - p51:121:11:0:0 0 -
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v119,v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:1:0 1 v2,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v135,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6,v23,v27,v28,v164
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 9 "opt deadcode"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 1 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:1:0 1 v2,v42
v v48 Load t2 0 - p77:41:49:0:0 1 v44,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 1 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 5 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:1:0 1 v2,v56
v v62 Load t11 0 - p75:35:45:0:0 3 v58,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v65,v66
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v32,v82
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v88 And64 t11 0 - p51:119:5:1:0 1 v85,v87
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v15,v20
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v70,v71
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v72,v73
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v119,v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v143,v120
v v122 Add64 t11 0 - p51:141:5:0:0 1 v143,v121
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v124,v129
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 1 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:1:0 1 v2,v133
v v139 Load t2 0 - p76:41:49:0:0 1 v135,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache linestarts 51:102:144:103=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 10 "generic cse"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:2:0 0 v2,v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 5 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:2:0 0 v2,v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:2:0 0 v2,v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:103=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 11 "phiopt"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 6 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v44 LocalAddr t33 0 a7 p77:41:76:2:0 0 v2,v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 5 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v58 LocalAddr t23 0 a5 p75:35:71:2:0 0 v2,v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v135 LocalAddr t33 0 a9 p76:41:76:2:0 0 v2,v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:103=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 12 "gcse deadcode"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 13 "nilcheckelim"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 5 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 3 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
v v155 Phi t12 0 - p51:112:21:0:0 2 v67,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 14 "prove"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 15 "divisible"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 16 "divmod"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 17 "middle opt"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 18 "known bits"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:2,b3:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 If p51:103:26:0:0 0 0 - v13 b16:1,b7:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
b b6 If p51:103:26:1:0 0 0 - v30 b16:0,b14:0 b11:0
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
b b7 Plain p73:51:13:1:0 0 0 - - b10:0 b3:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
b b10 Plain p73:53:19:1:0 0 0 - - b11:0 b7:0
b b11 Plain p0:0:0:0:0 0 0 - - b6:0 b10:0
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b3:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v135,v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b39,b38,b34,b31,b29,b30,b23,b28,b25,b24,b22,b14,b6,b11,b10,b7,b3,b1
cache idom b1:-,b3:b1,b6:b11,b7:b3,b10:b7,b11:b10,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b29:b23,b30:b23,b31:b29,b32:b31,b33:b32,b34:b31,b36:b32,b38:b34,b39:b34
cache sdom b1:-:b3:-:2:143,b3:b1:b7:b16:5:134,b6:b11:b14:-:17:122,b7:b3:b10:-:8:131,b10:b7:b11:-:11:128,b11:b10:b6:-:14:125,b14:b6:b22:-:20:119,b16:b1:-:-:137:140,b21:b14:-:-:113:116,b22:b14:b24:b21:23:110,b23:b22:b30:-:50:107,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b29:b23:b31:-:59:104,b30:b23:-:b29:53:56,b31:b29:b34:-:62:101,b32:b31:b36:-:83:98,b33:b32:-:-:92:95,b34:b31:b38:b32:65:80,b36:b32:-:b33:86:89,b38:b34:-:b39:68:71,b39:b34:-:-:74:77
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 19 "early fuse"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 Arg t2 0 a3 p51:100:6:2:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v135 b16:0,b14:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
v v135 OrB t3 0 - p73:56:11:1:0 1 v13,v30
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v58,v44,v141,v140,v27,v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 20 "expand calls"
aux a25 nameoff "x+0" a3 0
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 9 -
v v2 SP t15 0 - p0:0:0:0:0 7 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v58 SB t15 0 - p0:0:0:0:0 0 -
v v44 OffPtr t23 0 - p0:0:0:0:0 0 v2
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v135 b16:0,b14:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
v v135 OrB t3 0 - p73:56:11:1:0 1 v13,v30
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
v v141 LocalAddr t23 0 a4 p51:104:3:1:0 0 v2,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
v v140 LocalAddr t23 0 a4 p51:106:3:1:0 0 v2,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 LocalAddr t23 0 a4 p51:144:2:1:0 0 v2,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,v44,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 21 "decompose builtin"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 9 -
v v2 SP t15 0 - p0:0:0:0:0 7 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v58 SB t15 0 - p0:0:0:0:0 0 -
v v44 OffPtr t23 0 - p0:0:0:0:0 0 v2
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v135 b16:0,b14:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
v v135 OrB t3 0 - p73:56:11:1:0 1 v13,v30
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
v v141 LocalAddr t23 0 a4 p51:104:3:1:0 0 v2,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
v v140 LocalAddr t23 0 a4 p51:106:3:1:0 0 v2,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 LocalAddr t23 0 a4 p51:144:2:1:0 0 v2,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,v44,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 22 "softfloat"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 9 -
v v2 SP t15 0 - p0:0:0:0:0 7 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v58 SB t15 0 - p0:0:0:0:0 0 -
v v44 OffPtr t23 0 - p0:0:0:0:0 0 v2
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v135 b16:0,b14:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
v v135 OrB t3 0 - p73:56:11:1:0 1 v13,v30
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
v v141 LocalAddr t23 0 a4 p51:104:3:1:0 0 v2,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
v v140 LocalAddr t23 0 a4 p51:106:3:1:0 0 v2,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 If p51:121:14:1:0 0 0 - v91 b30:0,b29:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 Plain p51:129:2:1:0 0 0 - - b31:0 b23:1,b30:0
v v96 Phi t11 0 - p51:124:6:0:0 1 v89,v93
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b30 Plain p51:122:10:0:0 0 0 - - b29:1 b23:0
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b29:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 If p51:140:11:0:0 0 0 - v118 b38:0,b39:0 b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 Plain p51:141:12:0:0 0 0 - - b39:1 b34:0
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
b b39 Ret p51:144:2:1:0 0 0 - v142 - b34:1,b38:0
v v123 Phi t11 0 - p51:143:5:0:0 1 v143,v122
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 LocalAddr t23 0 a4 p51:144:2:1:0 0 v2,v133
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,v44,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 23 "branchelim"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 9 -
v v2 SP t15 0 - p0:0:0:0:0 7 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 7 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 7 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v58 SB t15 0 - p0:0:0:0:0 0 -
v v44 OffPtr t23 0 - p0:0:0:0:0 0 v2
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v135 b16:0,b14:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v13 Neq64F t3 0 - p72:39:11:1:0 1 v6,v6
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v30 Less64F t3 0 - p73:56:11:1:0 1 v29,v6
v v135 OrB t3 0 - p73:56:11:1:0 1 v13,v30
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:1
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:0,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
v v141 LocalAddr t23 0 a4 p51:104:3:1:0 0 v2,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 4 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
v v140 LocalAddr t23 0 a4 p51:106:3:1:0 0 v2,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 2 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v93 Lsh64x64 t11 1 - p51:122:6:1:0 1 v89,v76
v v96 CondSelect t11 0 - p51:124:6:0:0 1 v93,v89,v91
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 BlockInvalid p51:129:2:1:0 0 0 - - - -
b b30 BlockInvalid p51:122:10:0:0 0 0 - - - -
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 4 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 LocalAddr t23 0 a4 p51:144:2:1:0 0 v2,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 BlockInvalid p51:141:12:0:0 0 0 - - - -
b b39 BlockInvalid p51:144:2:1:0 0 0 - - - -
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,v44,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v164,v23,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 24 "late opt"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 BlockInvalid p51:129:2:1:0 0 0 - - - -
b b30 BlockInvalid p51:122:10:0:0 0 0 - - - -
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 BlockInvalid p51:141:12:0:0 0 0 - - - -
b b39 BlockInvalid p51:144:2:1:0 0 0 - - - -
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v27,v93,v140,v141,v135,v30,v13,v44,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:122=23:144=34,72:39:39:39=6,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 25 "dead auto elim"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 BlockInvalid p51:129:2:1:0 0 0 - - - -
b b30 BlockInvalid p51:122:10:0:0 0 0 - - - -
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 BlockInvalid p51:141:12:0:0 0 0 - - - -
b b39 BlockInvalid p51:144:2:1:0 0 0 - - - -
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v27,v93,v140,v141,v135,v30,v13,v44,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:122=23:144=34,72:39:39:39=6,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 26 "sccp"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
v v27 Const64 t12 -1 - p51:114:7:1:0 0 -
v v93 Const64 t12 1 - p51:116:6:1:0 0 -
v v140 Const64 t11 9007199254740992 - p51:130:10:1:0 0 -
v v141 Const64 t11 0 - p51:141:10:1:0 0 -
v v135 Const64 t11 0 - p51:141:5:0:0 0 -
v v30 Const64 t11 18014398509481984 - p51:132:10:1:0 0 -
v v13 Const64 t11 9007199254740992 - p51:134:6:1:0 0 -
v v44 Const64 t11 4503599627370496 - p51:137:5:1:0 0 -
b b3 BlockInvalid p51:103:26:0:0 0 0 - - - -
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v12 InlMark t30 16 - p51:103:22:0:0 0 v1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b7 BlockInvalid p73:51:13:1:0 0 0 - - - -
b b10 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b11 BlockInvalid p73:53:19:1:0 0 0 - - - -
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b29 BlockInvalid p51:129:2:1:0 0 0 - - - -
b b30 BlockInvalid p51:122:10:0:0 0 0 - - - -
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
b b38 BlockInvalid p51:141:12:0:0 0 0 - - - -
b b39 BlockInvalid p51:144:2:1:0 0 0 - - - -
names s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s3 v13
named s4 v6
named s5 v17
named s6 v30
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v93,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:122=23:144=34,72:39:39:39=6,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 27 "generic deadcode"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 28 "late fuse"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 29 "check bce"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 30 "dse"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 31 "memcombine"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 32 "writebarrier"
f b1 t1 a1 164 39
b b1 If p51:103:14:0:0 0 0 - v8 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 7 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v7 Const64F t2 0 - p0:0:0:0:0 2 -
v v17 Const64 t12 1 - p0:0:0:0:0 2 -
v v20 Const64 t12 0 - p0:0:0:0:0 2 -
v v29 Const64F t2 9218868437227405311 - p0:0:0:0:0 1 -
v v32 Const64 t12 -1023 - p51:118:6:1:0 1 -
v v40 Const64 t11 9221120237041090561 - p0:0:0:0:0 1 -
v v64 Const64 t14 52 - p0:0:0:0:0 2 -
v v66 Const64 t11 2047 - p0:0:0:0:0 1 -
v v71 Const64 t11 4503599627370496 - p0:0:0:0:0 2 -
v v73 Const64 t11 0 - p0:0:0:0:0 6 -
v v76 Const64 t14 1 - p0:0:0:0:0 6 -
v v87 Const64 t11 -9218868437227405313 - p51:119:5:2:0 1 -
v v98 Const64 t11 9007199254740992 - p0:0:0:0:0 1 -
v v119 Const64 t12 -1 - p51:114:7:1:0 1 -
v v120 Const64 t11 1 - p0:0:0:0:0 1 -
v v136 Const64 t12 1022 - p51:143:26:0:0 1 -
v v8 Eq64F t3 0 - p51:103:9:1:0 1 v6,v7
b b6 If p51:103:26:1:0 0 0 - v164 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v164 Leq64F t3 0 - p73:56:11:1:0 1 v6,v29
b b14 If p51:105:11:0:0 0 0 - v34 b21:0,b22:0 b6:0
v v34 Less64F t3 0 - p51:105:9:1:0 1 v6,v7
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v41 LocalAddr t33 0 a7 p74:31:44:0:0 2 v2,v1
v v42 Store t28 0 a8 p74:31:44:1:0 3 v41,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 Load t2 0 - p77:41:49:1:0 1 v41,v42
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 If p51:111:12:0:0 0 0 - v69 b24:0,b23:0 b14:1
v v55 LocalAddr t23 0 a5 p51:108:19:0:0 2 v2,v1
v v56 Store t28 0 a6 p51:108:19:1:0 4 v55,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 Load t11 0 - p75:35:45:1:0 3 v55,v56
v v65 Rsh64Ux64 t11 1 - p51:110:17:1:0 1 v62,v64
v v67 And64 t11 0 - p51:110:27:0:0 2 v66,v65
v v69 Eq64 t3 0 - p51:111:9:1:0 1 v67,v20
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 Add64 t12 0 - p51:118:6:1:0 2 v82,v32
v v88 And64 t11 0 - p51:119:5:1:0 1 v87,v85
v v15 And64 t12 0 - p51:121:11:0:0 1 v84,v17
v v89 Or64 t11 0 - p51:120:5:1:0 1 v88,v71
v v91 Neq64 t3 0 - p51:121:11:1:0 1 v20,v15
v v96 Lsh64x8 t11 1 - p51:124:6:0:0 1 v89,v23
v v95 Rsh64x64 t12 1 - p51:124:6:1:0 1 v84,v76
v v97 Lsh64x64 t11 1 - p51:126:5:1:0 1 v96,v76
v v23 CvtBoolToUint8 t8 0 - p51:124:6:0:0 1 v91
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 If p51:112:24:0:0 1 0 - v74 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
v v72 And64 t11 0 - p51:112:9:1:0 1 v71,v70
v v74 Eq64 t3 0 - p51:112:21:0:0 1 v73,v72
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 Lsh64x64 t11 1 - p51:113:7:1:0 1 v70,v76
v v79 Add64 t12 0 - p51:114:7:1:0 1 v155,v119
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 Add64 t12 0 - p51:116:6:1:0 1 v155,v17
b b31 If p51:129:11:0:0 1 0 - v100 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
v v100 Neq64 t3 0 - p51:129:8:1:0 1 v99,v73
b b32 If p51:131:8:0:0 0 0 - v105 b36:0,b33:0 b31:0
v v103 Add64 t11 0 - p51:130:10:1:0 3 v153,v99
v v105 Leq64U t3 0 - p51:131:8:1:0 1 v103,v152
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 Lsh64x64 t11 1 - p51:136:6:1:0 1 v113,v76
v v116 Rsh64Ux64 t11 1 - p51:137:5:1:0 1 v99,v76
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v118 Neq64 t3 0 - p51:140:8:1:0 1 v152,v73
v v121 And64 t11 0 - p51:141:10:1:0 1 v120,v143
v v122 Add64 t11 0 - p51:141:5:0:0 1 v121,v143
v v123 CondSelect t11 0 - p51:143:5:0:0 1 v122,v143,v118
v v124 Rsh64Ux64 t11 1 - p51:143:8:1:0 1 v123,v76
v v127 Add64 t12 0 - p51:143:26:0:0 1 v136,v95
v v132 LocalAddr t33 0 a9 p51:144:24:0:0 2 v2,v56
v v129 Lsh64x64 t11 1 - p51:143:32:0:0 1 v127,v64
v v130 Add64 t11 0 - p51:143:12:0:0 1 v129,v124
v v133 Store t28 0 a8 p51:144:24:1:0 3 v132,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 Load t2 0 - p76:41:49:1:0 1 v132,v133
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 Add64 t11 0 - p51:132:10:1:0 1 v103,v99
v v110 Sub64 t11 0 - p51:133:7:1:0 1 v152,v103
v v112 Add64 t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts 0=v7,v73,v20,1=v17,v76,v120,52=v64,2047=v66,4503599627370496=v71,9007199254740992=v98,9218868437227405311=v29,9221120237041090561=v40
freev v12,v44,v13,v30,v135,v141,v140,v93,v27,v58,v28,v137,v138,v126,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:137=0:116=0:130=0:141=0:132=0:134=0,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 33 "lower"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64MOVDconst t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v13 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 1 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 1 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64SLLconst t11 1 - p51:126:5:1:0 1 v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64SLLconst t11 1 - p51:113:7:1:0 1 v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64SLLconst t11 1 - p51:136:6:1:0 1 v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:118=1:114=1,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 34 "addressing modes"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64MOVDconst t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v13 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 1 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 1 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64SLLconst t11 1 - p51:126:5:1:0 1 v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 3 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64SLLconst t11 1 - p51:113:7:1:0 1 v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 1 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64SLLconst t11 1 - p51:136:6:1:0 1 v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144:118=1:114=1,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 35 "late lower"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v13 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 1 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 36 "pair"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v13 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 1 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s5,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s5 v17
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v13 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 1 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 38 "lowered cse"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 3 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 6 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 2 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v12 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 0 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 ARM64MOVDstore t28 0 a7 p74:31:44:1:0 2 v2,v40,v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 ARM64FMOVDstore t28 0 a5 p51:108:19:1:0 2 v2,v6,v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 2 v124,v127
v v133 ARM64MOVDstore t28 0 a9 p51:144:24:1:0 2 v2,v130,v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 39 "elim unread autos"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v12 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 0 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 Copy t28 0 - p74:31:44:1:0 2 v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 Copy t28 0 - p51:108:19:1:0 2 v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v133 Copy t28 0 - p51:144:24:1:0 2 v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 5 -
v v2 SP t15 0 - p0:0:0:0:0 0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:0:0 0 0 - v12 b21:0,b22:0 b6:0
v v13 ARM64FCMPD0 t29 0 - p51:105:9:1:0 0 v6
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v42 Copy t28 0 - p74:31:44:1:0 2 v1
v v43 InlMark t30 21 - p74:31:44:0:0 0 v42
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v42
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v56 Copy t28 0 - p51:108:19:1:0 2 v1
v v57 InlMark t30 19 - p51:108:19:0:0 0 v56
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v133 Copy t28 0 - p51:144:24:1:0 2 v56
v v134 InlMark t30 20 - p51:144:24:0:0 0 v133
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v133
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 41 "lowered deadcode"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144:105=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 42 "checkLower"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144:105=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 43 "loop invariant"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144:105=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144:105=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 45 "tighten"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:4:1:1:0 b25:0,b27:0,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144:105=2,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 46 "late deadcode"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b16:1,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b39,b38,b30,b29,b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b21,b27,b33,b36,b32,b34,b31,b23,b28,b25,b24,b22,b14,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32
cache sdom b1:-:b6:-:2:95,b6:b1:b14:b16:5:86,b14:b6:b22:-:8:83,b16:b1:-:-:89:92,b21:b14:-:-:77:80,b22:b14:b24:b21:11:74,b23:b22:b31:-:38:71,b24:b22:b25:b23:14:35,b25:b24:b28:-:17:32,b27:b25:-:-:26:29,b28:b25:-:b27:20:23,b31:b23:b34:-:41:68,b32:b31:b36:-:50:65,b33:b32:-:-:59:62,b34:b31:-:b32:44:47,b36:b32:-:b33:53:56
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:4:1:1:0 b25:0,b27:0,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 47 "critical"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b38:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 48 "phi tighten"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 0 0 - v12 b38:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 0 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 0 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 49 "likelyadjust"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v12 b21:0,b22:0 b6:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b16:b1,b21:b14,b22:b14,b23:b22,b24:b22,b25:b24,b27:b25,b28:b25,b31:b23,b32:b31,b33:b32,b34:b31,b36:b32,b39:b6,b38:b1,b30:b22,b29:b32
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b16:b1:-:-:113:116,b21:b14:-:-:95:98,b22:b14:b30:b21:17:92,b23:b22:b31:-:50:89,b24:b22:b25:b23:26:47,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b36:b32:-:b33:71:74,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b30:b22:-:b24:20:23,b29:b32:-:b36:65:68
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
dcllen 22
end
pass 50 "layout"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v12 b21:0,b22:0 b6:0
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b31:b23,b32:b31,b36:b32,b29:b32,b33:b32,b34:b31,b25:b24,b27:b25,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
fstate laidout
dcllen 22
end
pass 51 "schedule"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v12 b21:0,b22:0 b6:0
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b31:b23,b32:b31,b36:b32,b29:b32,b33:b32,b34:b31,b25:b24,b27:b25,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
fstate scheduled,laidout
dcllen 22
end
pass 52 "late nilcheck"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 4 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 2 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v12 b21:0,b22:0 b6:0
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v133,v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b31:b23,b32:b31,b36:b32,b29:b32,b33:b32,b34:b31,b25:b24,b27:b25,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
fstate scheduled,laidout
dcllen 22
end
pass 53 "flagalloc"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v29 ARM64FMOVDconst t2 9218868437227405311 - p0:0:0:0:0 1 -
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v29
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v133 b21:0,b22:0 b6:0
v v133 ARM64FCMPD0 t29 0 - p51:103:9:2:0 1 v6
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v40 ARM64MOVDconst t11 9221120237041090561 - p0:0:0:0:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v40
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v98 ARM64MOVDconst t11 9007199254740992 - p0:0:0:0:0 1 -
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v98,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v73,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v73,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v73,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v56,v42,v13,v2,v129,v132,v118,v93,v105,v140,v100,v126,v28,v141,v74,v72,v58,v135,v23,v15,v30,v69,v65,v55,v41,v34,v164,v8,v136,v120,v119,v87,v76,v71,v66,v64,v32,v20,v17,v7,v90,v61,v47,v25,v21,v86,v83,v131,v128,v125,v111,v109,v107,v106,v151,v147,v115,v117,v104,v102,v101,v150,v145,v92,v146,v94,v80,v78,v75,v149,v148,v68,v63,v51,v50,v49,v46,v45,v38,v36,v35,v33,v31,v26,v163,v159,v24,v22,v162,v158,v18,v16,v160,v156,v14,v11,v9,v161,v157,v60,v59,v54,v53,v10,v5,v4,v3
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b31:b23,b32:b31,b36:b32,b29:b32,b33:b32,b34:b31,b25:b24,b27:b25,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
fstate scheduled,laidout
dcllen 22
end
pass 54 "regalloc"
aux a1 call "AuxCall{math.sqrt}" a2 1 1 1 8 8 1 1
abiparam in 0 t2 a3 16 0
abiparam out 0 t2 a4 16 -1
callreg 0:80000000 - 0 -
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v56 ARM64FMOVDconst t2 9218868437227405311 - p73:56:11:2:0 1 -
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v56
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v133 b21:0,b22:0 b6:0
v v133 ARM64FCMPD0 t29 0 - p51:103:9:2:0 1 v6
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
v v42 Copy t11 0 - p51:111:9:2:0 1 v73
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v13 ARM64MOVDconst t11 9221120237041090561 - p77:41:49:2:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v13
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v2 Copy t11 0 - p51:121:14:2:0 1 v73
v v129 ARM64MOVDconst t11 9007199254740992 - p51:121:14:2:0 1 -
v v132 Copy t11 0 - p51:129:8:2:0 1 v73
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v129,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v2,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v132,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v42,v79
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v3,v4,v5,v7,v8,v9,v10,v11,v14,v15,v16,v17,v18,v20,v21,v22,v23,v24,v25,v26,v28,v30,v31,v32,v33,v34,v35,v36,v38,v41,v45,v46,v47,v49,v50,v51,v53,v54,v55,v58,v59,v60,v61,v63,v64,v65,v66,v68,v69,v71,v72,v74,v75,v76,v78,v80,v83,v86,v87,v90,v92,v93,v94,v100,v101,v102,v104,v105,v106,v107,v109,v111,v115,v117,v118,v119,v120,v125,v126,v128,v131,v135,v136,v140,v141,v145,v146,v147,v148,v149,v150,v151,v156,v157,v158,v159,v160,v161,v162,v163,v164
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b31:b23,b32:b31,b36:b32,b29:b32,b33:b32,b34:b31,b25:b24,b27:b25,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b33:b32:-:-:77:80,b34:b31:-:b32:56:59,b25:b24:b28:-:29:44,b27:b25:-:-:38:41,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
fstate scheduled,laidout
regalloc 156 v2:R2,v6:F0,v13:R0,v37:[],v42:R1,v48:F0,v52:[],v56:F1,v62:R0,v67:R1,v70:R0,v73:ZERO,v77:R0,v79:R1,v81:R1,v82:R1,v84:R1,v85:R0,v88:R0,v89:R0,v91:R2,v95:R1,v96:R0,v97:R0,v99:R3,v103:R5,v108:R4,v110:R0,v112:R2,v113:R0,v114:R0,v116:R3,v121:R3,v122:R3,v123:R0,v124:R0,v127:R1,v129:R3,v130:R0,v132:R4,v139:F0,v142:[],v143:R2,v144:R2,v152:R0,v153:R4,v154:R4,v155:R1
dcllen 22
end
pass 55 "loop rotate"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b38:0,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b39:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v56 ARM64FMOVDconst t2 9218868437227405311 - p73:56:11:2:0 1 -
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v56
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v133 b21:0,b22:0 b6:0
v v133 ARM64FCMPD0 t29 0 - p51:103:9:2:0 1 v6
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b30:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
v v42 Copy t11 0 - p51:111:9:2:0 1 v73
b b30 Plain p51:111:12:1:0 0 0 - - b23:0 b22:1
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v13 ARM64MOVDconst t11 9221120237041090561 - p77:41:49:2:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v13
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b39 Plain p51:103:26:1:0 0 0 - - b16:0 b6:1
b b38 Plain p51:103:14:0:0 0 0 - - b16:1 b1:0
b b16 Ret p51:104:3:1:0 0 0 - v37 - b39:0,b38:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b30:0,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v2 Copy t11 0 - p51:121:14:2:0 1 v73
v v129 ARM64MOVDconst t11 9007199254740992 - p51:121:14:2:0 1 -
v v132 Copy t11 0 - p51:129:8:2:0 1 v73
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b29:0,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v129,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v2,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v132,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b29:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b29 Plain p51:131:8:0:0 0 0 - - b33:0 b32:1
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v42,v79
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v3,v4,v5,v7,v8,v9,v10,v11,v14,v15,v16,v17,v18,v20,v21,v22,v23,v24,v25,v26,v28,v30,v31,v32,v33,v34,v35,v36,v38,v41,v45,v46,v47,v49,v50,v51,v53,v54,v55,v58,v59,v60,v61,v63,v64,v65,v66,v68,v69,v71,v72,v74,v75,v76,v78,v80,v83,v86,v87,v90,v92,v93,v94,v100,v101,v102,v104,v105,v106,v107,v109,v111,v115,v117,v118,v119,v120,v125,v126,v128,v131,v135,v136,v140,v141,v145,v146,v147,v148,v149,v150,v151,v156,v157,v158,v159,v160,v161,v162,v163,v164
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache postorder b16,b38,b21,b27,b33,b36,b29,b32,b34,b31,b23,b28,b25,b24,b30,b22,b14,b39,b6,b1
cache idom b1:-,b6:b1,b14:b6,b22:b14,b24:b22,b30:b22,b21:b14,b39:b6,b38:b1,b16:b1,b23:b22,b33:b32,b31:b23,b32:b31,b36:b32,b29:b32,b34:b31,b27:b25,b25:b24,b28:b25
cache sdom b1:-:b6:-:2:119,b6:b1:b39:b38:5:104,b14:b6:b22:-:14:101,b22:b14:b30:b21:17:92,b24:b22:b25:b23:26:47,b30:b22:-:b24:20:23,b21:b14:-:-:95:98,b39:b6:-:b14:8:11,b38:b1:-:b16:107:110,b16:b1:-:-:113:116,b23:b22:b31:-:50:89,b33:b32:-:-:77:80,b31:b23:b34:-:53:86,b32:b31:b29:-:62:83,b36:b32:-:b33:71:74,b29:b32:-:b36:65:68,b34:b31:-:b32:56:59,b27:b25:-:-:38:41,b25:b24:b28:-:29:44,b28:b25:-:b27:32:35
cache loopnest 40 0 b25:-:2:1:1:0,b31:-:5:1:1:0 b25:0,b27:0,b29:1,b31:1,b32:1,b33:1,b36:1
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
hotness b27:3,b33:3
fstate scheduled,laidout
regalloc 156 v2:R2,v6:F0,v13:R0,v37:[],v42:R1,v48:F0,v52:[],v56:F1,v62:R0,v67:R1,v70:R0,v73:ZERO,v77:R0,v79:R1,v81:R1,v82:R1,v84:R1,v85:R0,v88:R0,v89:R0,v91:R2,v95:R1,v96:R0,v97:R0,v99:R3,v103:R5,v108:R4,v110:R0,v112:R2,v113:R0,v114:R0,v116:R3,v121:R3,v122:R3,v123:R0,v124:R0,v127:R1,v129:R3,v130:R0,v132:R4,v139:F0,v142:[],v143:R2,v144:R2,v152:R0,v153:R4,v154:R4,v155:R1
dcllen 22
end
pass 56 "trim"
f b1 t1 a1 164 39
b b1 ARM64EQ p51:103:14:0:0 -1 0 - v12 b16:1,b6:0 -
v v6 ArgFloatReg t2 0 a25 p51:103:14:0:0 5 -
v v1 InitMem t28 0 - p0:0:0:0:0 8 -
v v12 ARM64FCMPD0 t29 0 - p51:103:9:1:0 1 v6
b b6 ARM64FLE p51:103:26:1:0 1 0 - v44 b14:0,b16:0 b1:1
v v19 InlMark t30 17 - p51:103:34:0:0 0 v1
v v56 ARM64FMOVDconst t2 9218868437227405311 - p73:56:11:2:0 1 -
v v44 ARM64FCMPD t29 0 - p73:56:11:1:0 1 v6,v56
b b14 ARM64FLT p51:105:11:1:0 -1 0 - v133 b21:0,b22:0 b6:0
v v133 ARM64FCMPD0 t29 0 - p51:103:9:2:0 1 v6
b b22 ARM64Z p51:111:12:1:0 0 0 - v67 b24:0,b23:0 b14:1
v v62 ARM64FMOVDfpgp t11 0 - p75:35:45:1:0 3 v6
v v73 ARM64ZERO t11 0 - p0:0:0:0:0 3 -
v v57 InlMark t30 19 - p51:108:19:1:0 0 v1
v v67 ARM64UBFX t11 13323 - p51:110:27:1:0 2 v62
b b24 Plain p51:111:9:0:0 0 0 - - b25:0 b22:0
v v42 Copy t11 0 - p51:111:9:2:0 1 v73
b b21 Ret p51:106:3:1:0 0 0 - v52 - b14:0
v v13 ARM64MOVDconst t11 9221120237041090561 - p77:41:49:2:0 1 -
v v48 ARM64FMOVDgpfp t2 0 - p77:41:49:1:0 1 v13
v v39 InlMark t30 18 - p51:106:13:1:0 0 v1
v v43 InlMark t30 21 - p74:31:44:1:0 0 v1
v v52 MakeResult t34 0 - p51:106:3:1:0 1 v48,v1
b b16 Ret p51:104:3:1:0 0 0 - v37 - b6:1,b1:0
v v37 MakeResult t34 0 - p51:104:3:1:0 1 v6,v1
b b23 Plain p51:121:14:1:0 0 0 - - b31:0 b22:1,b28:0
v v82 Phi t12 0 - p51:118:6:0:0 1 v67,v81
v v85 Phi t11 0 - p51:118:6:1:0 1 v62,v70
v v84 ARM64SUBconst t12 1023 - p51:118:6:1:0 2 v82
v v88 ARM64ANDconst t11 -9218868437227405313 - p51:119:5:1:0 1 v85
v v89 ARM64ORconst t11 4503599627370496 - p51:120:5:1:0 1 v88
v v138 ARM64TSTconst t29 1 - p51:121:11:1:0 1 v84
v v91 ARM64NotEqual t3 0 - p51:121:11:1:0 1 v138
v v96 ARM64SLL t11 0 - p51:124:6:0:0 2 v89,v91
v v97 ARM64ADD t11 0 - p51:126:5:1:0 1 v96,v96
v v2 Copy t11 0 - p51:121:14:2:0 1 v73
v v129 ARM64MOVDconst t11 9007199254740992 - p51:121:14:2:0 1 -
v v132 Copy t11 0 - p51:129:8:2:0 1 v73
b b33 Plain p51:129:11:1:0 0 0 - - b31:1 b32:1,b36:0
v v113 Phi t11 0 - p51:136:6:0:0 2 v152,v110
v v154 Phi t11 0 - p51:136:6:0:0 1 v153,v108
v v144 Phi t11 0 - p51:136:6:1:0 1 v143,v112
v v114 ARM64ADD t11 0 - p51:136:6:1:0 1 v113,v113
v v116 ARM64SRLconst t11 1 - p51:137:5:1:0 1 v99
b b31 ARM64NZ p51:129:11:1:0 1 0 - v99 b32:0,b34:0 b23:0,b33:0
v v99 Phi t11 0 - p51:129:8:0:0 5 v129,v116
v v143 Phi t11 0 - p51:129:8:0:0 5 v2,v144
v v152 Phi t11 0 - p51:129:8:0:0 4 v97,v114
v v153 Phi t11 0 - p51:129:8:0:0 2 v132,v154
b b32 ARM64UGE p51:131:8:0:0 0 0 - v137 b36:0,b33:0 b31:0
v v103 ARM64ADD t11 0 - p51:130:10:1:0 3 v153,v99
v v137 ARM64CMP t29 0 - p51:131:8:1:0 1 v152,v103
b b36 Plain p51:134:6:0:0 0 0 - - b33:1 b32:0
v v108 ARM64ADD t11 0 - p51:132:10:1:0 1 v103,v99
v v110 ARM64SUB t11 0 - p51:133:7:1:0 1 v152,v103
v v112 ARM64ADD t11 0 - p51:134:6:1:0 1 v143,v99
b b34 Ret p51:140:11:0:0 0 0 - v142 - b31:1
v v95 ARM64SRAconst t12 1 - p51:124:6:1:0 1 v84
v v121 ARM64ANDconst t11 1 - p51:141:10:1:0 1 v143
v v122 ARM64ADD t11 0 - p51:141:5:0:0 1 v121,v143
v v127 ARM64ADDconst t12 1022 - p51:143:26:0:0 1 v95
v v134 InlMark t30 20 - p51:144:24:1:0 0 v1
v v27 ARM64CMPconst t29 0 - p51:140:8:1:0 1 v152
v v123 ARM64CSEL t11 4577 - p51:143:5:0:0 1 v122,v143,v27
v v124 ARM64SRLconst t11 1 - p51:143:8:1:0 1 v123
v v130 ARM64ADDshiftLL t11 52 - p51:143:12:0:0 1 v124,v127
v v139 ARM64FMOVDgpfp t2 0 - p76:41:49:1:0 1 v130
v v142 MakeResult t34 0 - p51:144:2:1:0 1 v139,v1
b b27 Plain p51:112:24:1:0 0 0 - - b25:1 b25:0
v v77 ARM64ADD t11 0 - p51:113:7:1:0 1 v70,v70
v v79 ARM64SUBconst t12 1 - p51:114:7:1:0 1 v155
b b25 ARM64TBZ p51:112:24:1:0 1 52 - v70 b27:0,b28:0 b24:0,b27:0
v v70 Phi t11 0 - p51:112:21:0:0 4 v62,v77
v v155 Phi t12 0 - p51:112:21:0:0 2 v42,v79
b b28 Plain p51:116:6:0:0 0 0 - - b23:1 b25:1
v v81 ARM64ADDconst t12 1 - p51:116:6:1:0 1 v155
names s1,s2,s4,s7,s8,s9,s10,s11,s12,s13,s14,s15,s16
named s1 v6
named s2 v6
named s4 v6
named s7 v48
named s8 v48
named s9 v62
named s10 v62,v70,v77,v85,v88,v89,v96,v97,v152,v110,v113,v114,v130
named s11 v67,v155,v79,v81,v82,v84,v95
named s12 v73,v143,v112,v122,v123,v144
named s13 v73,v153,v108,v154
named s14 v98,v99,v116
named s15 v103
named s16 v139
splits -
canon a3/t2/0/-/0=s1,a10/t2/0/-/0=s2,a11/t3/0/-/0=s3,a12/t2/0/-/0=s4,a13/t12/0/-/0=s5,a14/t3/0/-/0=s6,a15/t2/0/-/0=s7,a16/t2/0/-/0=s8,a17/t11/0/-/0=s9,a18/t11/0/-/0=s10,a19/t12/0/-/0=s11,a20/t11/0/-/0=s12,a21/t11/0/-/0=s13,a22/t11/0/-/0=s14,a23/t11/0/-/0=s15,a24/t2/0/-/0=s16
consts -
freev v3,v4,v5,v7,v8,v9,v10,v11,v14,v15,v16,v17,v18,v20,v21,v22,v23,v24,v25,v26,v28,v30,v31,v32,v33,v34,v35,v36,v38,v41,v45,v46,v47,v49,v50,v51,v53,v54,v55,v58,v59,v60,v61,v63,v64,v65,v66,v68,v69,v71,v72,v74,v75,v76,v78,v80,v83,v86,v87,v90,v92,v93,v94,v100,v101,v102,v104,v105,v106,v107,v109,v111,v115,v117,v118,v119,v120,v125,v126,v128,v131,v135,v136,v140,v141,v145,v146,v147,v148,v149,v150,v151,v156,v157,v158,v159,v160,v161,v162,v163,v164
freeb b11,b10,b7,b3,b12,b9,b37,b35,b26,b20,b19,b18,b17,b15,b13,b8,b5,b4,b2
cache auxmap -:1,a3:2,a7:3,a5:4,a9:5,a25:6
cache linestarts 51:102:144,72:39:39,73:51:56,74:31:31,75:35:35,76:41:41,77:41:41
hotness b27:3,b33:3
fstate scheduled,laidout
regalloc 156 v2:R2,v6:F0,v13:R0,v37:[],v42:R1,v48:F0,v52:[],v56:F1,v62:R0,v67:R1,v70:R0,v73:ZERO,v77:R0,v79:R1,v81:R1,v82:R1,v84:R1,v85:R0,v88:R0,v89:R0,v91:R2,v95:R1,v96:R0,v97:R0,v99:R3,v103:R5,v108:R4,v110:R0,v112:R2,v113:R0,v114:R0,v116:R3,v121:R3,v122:R3,v123:R0,v124:R0,v127:R1,v129:R3,v130:R0,v132:R4,v139:F0,v142:[],v143:R2,v144:R2,v152:R0,v153:R4,v154:R4,v155:R1
dcllen 22
end
frontend
end
ptrcache t2,t5,t6,t7,t8,t10,t11,t12,t13,t15,t16,t17,t24
typelink t28=t32
typeorder t4,t8,t5,t9,t6,t10,t7,t11,t12,t14,t15,t25,t26,t13,t2,t3,t17,t18,t19,t33,t20,t21,t22,t23,t24,t1,t16,t27,t28,t30,t29,t31,t32,t34
eof
"#

/-- `std/std/math/sqrt,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "math"
func "sqrt" 1
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
type t1 8 8 0 0 - "float64"
name n1 "x" PPARAM t1 1 "math.x" 0 a3
name n2 "~r0" PPARAMOUT t1 1 "math.~r0" 0 a4
type t2 8 8 0 0 - "uint64"
name n3 "ix" PAUTO t2 1 "math.ix" 0 a18
type t3 8 8 0 0 - "int"
name n4 "exp" PAUTO t3 1 "math.exp" 1 a19
name n5 "q" PAUTO t2 1 "math.q" 0 a20
name n6 "s" PAUTO t2 1 "math.s" 0 a21
name n7 "r" PAUTO t2 1 "math.r" 0 a22
name n8 "t" PAUTO t2 1 "math.t" 0 a23
name n9 "f" PAUTO t1 1 "math.f" 0 a10
type t4 1 1 0 0 - "bool"
name n10 "is" PAUTO t4 1 "math.is" 0 a11
name n11 "f" PAUTO t1 1 "math.f" 0 a12
name n12 "sign" PAUTO t3 1 "math.sign" 0 a13
name n13 "~r0" PAUTO t4 1 "math.~r0" 0 a14
name n14 "~r0" PAUTO t1 1 "math.~r0" 0 a16
name n15 "f" PAUTO t1 1 "math.f" 0 a5
name n16 "~r0" PAUTO t2 1 "math.~r0" 0 a17
name n17 "b" PAUTO t2 1 "math.b" 0 a9
name n18 "~r0" PAUTO t1 1 "math.~r0" 0 a24
name n19 "b" PAUTO t2 1 "math.b" 0 a7
name n20 "~r0" PAUTO t1 1 "math.~r0" 0 a15
name n21 ".autotmp_20" PAUTO t4 3 "math..autotmp_20" 0 -
name n22 ".autotmp_21" PAUTO t4 3 "math..autotmp_21" 0 -
in n1 0 used
in n2 0 outregs
in n3 0 used
in n4 0 used
in n5 0 used
in n6 0 used
in n7 0 used
in n8 0 used
in n9 0 used
in n10 0 used
in n11 0 used
in n12 0 used
in n13 0 used
in n14 0 -
in n15 0 used,addrtaken
in n16 0 -
in n17 0 used,addrtaken
in n18 0 -
in n19 0 used,addrtaken
in n20 0 -
in n21 0 used,autotmp
in n22 0 used,autotmp
out n1 0 used
opt n17 0 addrtaken
opt n19 0 addrtaken
opt n4 0 -
opt n9 0 -
opt n11 0 -
opt n15 0 addrtaken
opt n3 0 -
opt n5 0 -
opt n7 0 -
opt n6 0 -
opt n12 0 -
opt n8 0 -
opt n2 0 outregs
opt n14 0 -
opt n16 0 -
opt n18 0 -
opt n20 0 -
opt n21 0 autotmp
opt n22 0 autotmp
opt n10 0 -
opt n13 0 -
stack 0 0 8
end
genin
posbase p51 "math/sqrt.go" 1 1 -1 50 "math/sqrt.go" "math/sqrt.go" 1 1
sym y1 "math.sqrt" 1
curfn p51:100:6:0:0 0 0
regargs 8224:0:t1
text y1 0 0 0 0 100 200080
end
prog0
sym y2 "gclocals\xc2\xb7g5+hNtRBP6YXNjfog7aZjQ==" 0
sym y3 "math.sqrt.arginfo1" 0
sym y4 "math.sqrt.argliveinfo" 0
sym y5 "math.IsInf" 1
inl i17 - p51:103:34:0:0 y5 "IsInf"
posbase p73 "math/bits.go" 1 1 17 17 "math/bits.go" "math/bits.go" 1 1
sym y6 "math.Float64bits" 1
inl i19 - p51:108:19:0:0 y6 "Float64bits"
posbase p75 "math/unsafe.go" 1 1 19 52 "math/unsafe.go" "math/unsafe.go" 1 1
sym y7 "math.NaN" 1
inl i18 - p51:106:13:0:0 y7 "NaN"
posbase p74 "math/bits.go" 1 1 18 17 "math/bits.go" "math/bits.go" 1 1
sym y8 "math.Float64frombits" 1
inl i21 i18 p74:31:44:0:0 y8 "Float64frombits"
posbase p77 "math/unsafe.go" 1 1 21 52 "math/unsafe.go" "math/unsafe.go" 1 1
inl i20 - p51:144:24:0:0 y8 "Float64frombits"
posbase p76 "math/unsafe.go" 1 1 20 52 "math/unsafe.go" "math/unsafe.go" 1 1
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 0 p51:100:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p51:100:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p51:100:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p51:100:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p51:100:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p51:100:6:2:0
p 6 6 0 0 0 - FCMPD 0 FCONST/0/0/0/NONE/0/0/-/f0 8224 - _ 0 0 p51:103:9:1:0
p 7 7 0 0 0 - BEQ 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@25 0 0 p51:103:14:2:0
p 8 8 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 9 9 0 0 0 - FMOVD 0 FCONST/0/0/0/NONE/0/0/-/f7fefffffffffffff 0 - REG/8225/0/0/NONE/0/0/-/- 0 0 p73:56:11:1:0
p 10 10 0 0 0 - FCMPD 0 REG/8225/0/0/NONE/0/0/-/- 8224 - _ 0 0 p73:56:11:2:0
p 11 11 0 0 0 - BHI 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@25 0 0 p51:103:26:1:0
p 12 12 0 0 0 - FCMPD 0 FCONST/0/0/0/NONE/0/0/-/f0 8224 - _ 0 0 p51:103:9:2:0
p 13 13 0 0 0 - BMI 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@20 0 0 p51:105:11:1:0
p 14 14 0 0 0 - FMOVD 0 REG/8224/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p75:35:45:1:0
p 15 15 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p51:108:19:1:0
p 16 16 0 0 0 - UBFX 0 CONST/0/0/0/NONE/0/52/-/- 8192 0:CONST/0/0/0/NONE/0/11/-/- REG/8193/0/0/NONE/0/0/-/- 0 0 p51:110:27:1:0
p 17 17 0 0 0 - CBNZ 0 REG/8193/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@26 0 0 p51:111:12:1:0
p 18 18 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:111:9:2:0
p 19 19 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@60 0 0 p51:111:9:2:0
p 20 20 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/9221120237041090561/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p77:41:49:1:0
p 21 21 0 0 0 - FMOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p77:41:49:2:0
p 22 22 0 0 0 - NOP 0 _ 0 - _ 0 0 p0:0:0:0:0
p 23 23 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p74:31:44:1:0
p 24 24 0 0 0 - RET 0 _ 0 - _ 0 0 p51:106:3:1:0
p 25 25 0 0 0 - RET 0 _ 0 - _ 0 0 p51:104:3:1:0
p 26 26 0 0 0 - SUB 0 CONST/0/0/0/NONE/0/1023/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:118:6:1:0
p 27 27 0 0 0 - AND 0 CONST/0/0/0/NONE/0/-9218868437227405313/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:119:5:1:0
p 28 28 0 0 0 - ORR 0 CONST/0/0/0/NONE/0/4503599627370496/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:120:5:1:0
p 29 29 0 0 0 - TST 0 CONST/0/0/0/NONE/0/1/-/- 8193 - _ 0 0 p51:121:11:1:0
p 30 30 0 0 0 - CSET 0 SPECIAL/0/0/0/NONE/0/129/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p51:121:11:2:0
p 31 31 0 0 0 - LSL 0 REG/8194/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:124:6:2:0
p 32 32 0 0 0 - ADD 0 REG/8192/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:126:5:1:0
p 33 33 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p51:121:14:2:0
p 34 34 0 0 0 - MOVD 0 CONST/0/0/0/NONE/0/9007199254740992/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p51:121:14:2:0
p 35 35 0 0 0 - MOVD 0 REG/8223/0/0/NONE/0/0/-/- 0 - REG/8196/0/0/NONE/0/0/-/- 0 0 p51:129:8:2:0
p 36 36 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@39 0 0 p51:121:14:1:0
p 37 37 0 0 0 - ADD 0 REG/8192/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:136:6:1:0
p 38 38 0 0 0 - LSR 0 CONST/0/0/0/NONE/0/1/-/- 8195 - REG/8195/0/0/NONE/0/0/-/- 0 0 p51:137:5:1:0
p 39 39 0 0 0 - CBZ 0 REG/8195/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@47 0 0 p51:129:11:1:0
p 40 40 0 0 0 - ADD 0 REG/8195/0/0/NONE/0/0/-/- 8196 - REG/8197/0/0/NONE/0/0/-/- 0 0 p51:130:10:1:0
p 41 41 0 0 0 - CMP 0 REG/8197/0/0/NONE/0/0/-/- 8192 - _ 0 0 p51:131:8:1:0
p 42 42 0 0 0 - BLO 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@37 0 0 p51:131:8:2:0
p 43 43 0 0 0 - ADD 0 REG/8195/0/0/NONE/0/0/-/- 8197 - REG/8196/0/0/NONE/0/0/-/- 0 0 p51:132:10:1:0
p 44 44 0 0 0 - SUB 0 REG/8197/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:133:7:1:0
p 45 45 0 0 0 - ADD 0 REG/8195/0/0/NONE/0/0/-/- 8194 - REG/8194/0/0/NONE/0/0/-/- 0 0 p51:134:6:1:0
p 46 46 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@37 0 0 p51:134:6:2:0
p 47 47 0 0 0 - ASR 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:124:6:1:0
p 48 48 0 0 0 - AND 0 CONST/0/0/0/NONE/0/1/-/- 8194 - REG/8195/0/0/NONE/0/0/-/- 0 0 p51:141:10:1:0
p 49 49 0 0 0 - ADD 0 REG/8194/0/0/NONE/0/0/-/- 8195 - REG/8195/0/0/NONE/0/0/-/- 0 0 p51:141:5:2:0
p 50 50 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1022/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:143:26:2:0
p 51 51 0 0 0 - HINT 0 CONST/0/0/0/NONE/0/0/-/- 0 - _ 0 0 p51:144:24:1:0
p 52 52 0 0 0 - CMP 0 CONST/0/0/0/NONE/0/0/-/- 8192 - _ 0 0 p51:140:8:1:0
p 53 53 0 0 0 - CSEL 0 SPECIAL/0/0/0/NONE/0/129/-/- 8195 0:REG/8194/0/0/NONE/0/0/-/- REG/8192/0/0/NONE/0/0/-/- 0 0 p51:143:5:1:0
p 54 54 0 0 0 - LSR 0 CONST/0/0/0/NONE/0/1/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:143:8:2:0
p 55 55 0 0 0 - ADD 0 SHIFT/0/0/0/NONE/0/118784/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:143:12:2:0
p 56 56 0 0 0 - FMOVD 0 REG/8192/0/0/NONE/0/0/-/- 0 - REG/8224/0/0/NONE/0/0/-/- 0 0 p76:41:49:1:0
p 57 57 0 0 0 - RET 0 _ 0 - _ 0 0 p51:140:11:0:0
p 58 58 0 0 0 - ADD 0 REG/8192/0/0/NONE/0/0/-/- 8192 - REG/8192/0/0/NONE/0/0/-/- 0 0 p51:113:7:1:0
p 59 59 0 0 0 - SUB 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:114:7:1:0
p 60 60 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/52/-/- 8192 - BRANCH/0/0/0/NONE/0/0/-/@58 0 0 p51:112:24:1:0
p 61 61 0 0 0 - ADD 0 CONST/0/0/0/NONE/0/1/-/- 8193 - REG/8193/0/0/NONE/0/0/-/- 0 0 p51:116:6:1:0
p 62 62 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@26 0 0 p51:116:6:2:0
p 63 63 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 100 200080
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
inlmark @6 17
inlmark @24 18
inlmark @15 19
inlmark @23 21
inlmark @51 20
funcaux y2 y2 - - y3 y4 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:1,y4:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n9 t1 0
dbgslot 2 n11 t1 0
dbgslot 3 n20 t1 0
dbgslot 4 n14 t1 0
dbgslot 5 n16 t2 0
dbgslot 6 n3 t2 0
dbgslot 7 n4 t3 0
dbgslot 8 n5 t2 0
dbgslot 9 n6 t2 0
dbgslot 10 n7 t2 0
dbgslot 11 n8 t2 0
dbgslot 12 n18 t1 0
dbgvar 0 n1 0
dbgvar 1 n9 1
dbgvar 2 n11 2
dbgvar 3 n3 6
dbgvar 4 n4 7
dbgvar 5 n5 8
dbgvar 6 n6 9
dbgvar 7 n7 10
dbgvar 8 n8 11
dbgloc 0 1:-10000:21:48:9040
dbgloc 1 1:-10000:21:48:9040
dbgloc 2 1:-10000:21:48:9040
dbgloc 3 22:62:21:-10000:50,23:-10000:34:123:50,34:130:-1:-30000:50
dbgloc 4 22:67:24:42:51,23:-10000:34:127:51,27:79:25:-10000:51,25:-10000:-1:-30000:51
dbgloc 5 22:57:21:-10000:50,33:-10000:31:-10000:52,31:-10000:-1:-30000:50
dbgloc 6 22:57:21:-10000:50,33:-10000:31:-10000:54,31:-10000:-1:-30000:50
dbgloc 7 33:116:31:-10000:53,31:-10000:34:121:53
dbgloc 8 32:103:34:-10000:55
dbgregout n2
dbgpc 21:48:22,22:62:15,21:-10000:20,23:-10000:26,34:123:54,34:130:56,22:67:17,24:42:19,34:127:51,27:79:60,25:-10000:60,22:57:16,33:-10000:37,31:-10000:39,33:116:39,34:121:49,32:103:41,34:-10000:47
end
asm
sym y9 "$f64.7fefffffffffffff" 0
sym y10 "" 0
sym y11 "" 0
sym y12 "" 0
sym y13 "" 0
sym y14 "" 0
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i8 0 2 p51:100:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p51:100:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p51:100:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p51:100:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p51:100:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p51:100:6:2:0
p 6 0 0 0 115 - FCMPD 0 FCONST/0/0/0/NONE/30/0/-/f0 8224 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:103:9:1:0
p 7 4 0 0 80 - BEQ 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/25/-/@25 0 0 p51:103:14:2:0
p 8 8 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 64 8 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-3/-/- 0 0 p0:0:0:0:0
p 9 8 0 0 162 - FMOVD 0 MEM/0/0/0/EXTERN/110/0/y9/f7fefffffffffffff 0 - REG/8225/0/0/NONE/5/0/-/- 0 0 p73:56:11:1:0
p 65 16 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-1/-/- 0 0 p73:56:11:1:0
p 10 16 0 0 114 - FCMPD 0 REG/8225/0/0/NONE/5/0/-/- 8224 - NONE/0/0/0/NONE/1/0/-/- 0 0 p73:56:11:2:0
p 11 20 0 0 80 - BHI 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/25/-/@25 0 0 p51:103:26:1:0
p 12 24 0 0 115 - FCMPD 0 FCONST/0/0/0/NONE/30/0/-/f0 8224 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:103:9:2:0
p 13 28 0 0 80 - BMI 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/20/-/@20 0 0 p51:105:11:1:0
p 14 32 0 0 137 - FMOVD 0 REG/8224/0/0/NONE/5/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p75:35:45:1:0
p 15 36 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:108:19:1:0
p 16 40 0 0 81 - UBFX 0 CONST/0/0/0/NONE/18/52/-/- 8192 0:CONST/0/0/0/NONE/18/11/-/- REG/8193/0/0/NONE/2/0/-/- 0 0 p51:110:27:1:0
p 17 44 0 0 85 - CBNZ 0 REG/8193/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/26/-/@26 0 0 p51:111:12:1:0
p 18 48 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:111:9:2:0
p 19 52 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/60/-/@60 0 0 p51:111:9:2:0
p 20 56 0 0 320 - MOVD 0 CONST/0/0/0/NONE/27/9221120237041090561/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p77:41:49:1:0
p 21 64 0 0 136 - FMOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p77:41:49:2:0
p 22 68 0 0 7 - NOP 0 NONE/0/0/0/NONE/1/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p0:0:0:0:0
p 23 68 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p74:31:44:1:0
p 24 72 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p51:106:3:1:0
p 25 76 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p51:104:3:1:0
p 26 80 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/1023/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:118:6:1:0
p 27 84 0 0 53 - AND 0 CONST/0/0/0/NONE/22/-9218868437227405313/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:119:5:1:0
p 28 88 0 0 53 - ORR 0 CONST/0/0/0/NONE/22/4503599627370496/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:120:5:1:0
p 29 92 0 0 475 - TST 0 CONST/0/0/0/NONE/17/1/-/- 8193 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:121:11:1:0
p 30 96 0 0 103 - CSET 0 SPECIAL/0/0/0/NONE/11/129/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p51:121:11:2:0
p 31 100 0 0 272 - LSL 0 REG/8194/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:124:6:2:0
p 32 104 0 0 23 - ADD 0 REG/8192/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:126:5:1:0
p 33 108 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p51:121:14:2:0
p 34 112 0 0 317 - MOVD 0 CONST/0/0/0/NONE/22/9007199254740992/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p51:121:14:2:0
p 35 116 0 0 301 - MOVD 0 REG/8223/0/0/NONE/3/0/-/- 0 - REG/8196/0/0/NONE/2/0/-/- 0 0 p51:129:8:2:0
p 36 120 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/39/-/@39 0 0 p51:121:14:1:0
p 37 124 0 0 23 - ADD 0 REG/8192/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:136:6:1:0
p 38 128 0 0 274 - LSR 0 CONST/0/0/0/NONE/17/1/-/- 8195 - REG/8195/0/0/NONE/2/0/-/- 0 0 p51:137:5:1:0
p 39 132 0 0 85 - CBZ 0 REG/8195/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/47/-/@47 0 0 p51:129:11:1:0
p 40 136 0 0 23 - ADD 0 REG/8195/0/0/NONE/2/0/-/- 8196 - REG/8197/0/0/NONE/2/0/-/- 0 0 p51:130:10:1:0
p 41 140 0 0 92 - CMP 0 REG/8197/0/0/NONE/2/0/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:131:8:1:0
p 42 144 0 0 80 - BLO 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/37/-/@37 0 0 p51:131:8:2:0
p 43 148 0 0 23 - ADD 0 REG/8195/0/0/NONE/2/0/-/- 8197 - REG/8196/0/0/NONE/2/0/-/- 0 0 p51:132:10:1:0
p 44 152 0 0 23 - SUB 0 REG/8197/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:133:7:1:0
p 45 156 0 0 23 - ADD 0 REG/8195/0/0/NONE/2/0/-/- 8194 - REG/8194/0/0/NONE/2/0/-/- 0 0 p51:134:6:1:0
p 46 160 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/37/-/@37 0 0 p51:134:6:2:0
p 47 164 0 0 274 - ASR 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:124:6:1:0
p 48 168 0 0 53 - AND 0 CONST/0/0/0/NONE/17/1/-/- 8194 - REG/8195/0/0/NONE/2/0/-/- 0 0 p51:141:10:1:0
p 49 172 0 0 23 - ADD 0 REG/8194/0/0/NONE/2/0/-/- 8195 - REG/8195/0/0/NONE/2/0/-/- 0 0 p51:141:5:2:0
p 50 176 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1022/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:143:26:2:0
p 51 180 0 0 232 - HINT 0 CONST/0/0/0/NONE/16/0/-/- 0 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:144:24:1:0
p 52 184 0 0 96 - CMP 0 CONST/0/0/0/NONE/16/0/-/- 8192 - NONE/0/0/0/NONE/1/0/-/- 0 0 p51:140:8:1:0
p 53 188 0 0 102 - CSEL 0 SPECIAL/0/0/0/NONE/11/129/-/- 8195 0:REG/8194/0/0/NONE/2/0/-/- REG/8192/0/0/NONE/2/0/-/- 0 0 p51:143:5:1:0
p 54 192 0 0 274 - LSR 0 CONST/0/0/0/NONE/17/1/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:143:8:2:0
p 55 196 0 0 27 - ADD 0 SHIFT/0/0/0/NONE/8/118784/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:143:12:2:0
p 56 200 0 0 136 - FMOVD 0 REG/8192/0/0/NONE/2/0/-/- 0 - REG/8224/0/0/NONE/5/0/-/- 0 0 p76:41:49:1:0
p 57 204 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p51:140:11:0:0
p 58 208 0 0 23 - ADD 0 REG/8192/0/0/NONE/2/0/-/- 8192 - REG/8192/0/0/NONE/2/0/-/- 0 0 p51:113:7:1:0
p 59 212 0 0 31 - SUB 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:114:7:1:0
p 60 216 0 0 470 - TBZ 0 CONST/0/0/0/NONE/18/52/-/- 8192 - BRANCH/0/0/0/NONE/36/58/-/@58 0 0 p51:112:24:1:0
p 61 220 0 0 31 - ADD 0 CONST/0/0/0/NONE/17/1/-/- 8193 - REG/8193/0/0/NONE/2/0/-/- 0 0 p51:116:6:1:0
p 62 224 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/26/-/@26 0 0 p51:116:6:2:0
fn y1 8 0 0 0 100 2000c8
spill MEM/8383/0/0/NONE/0/8/-/- 8224 0 FMOVD FMOVD
inlmark @6 17
inlmark @24 18
inlmark @15 19
inlmark @23 21
inlmark @51 20
funcaux y2 y2 - - y3 y4 -
text 240 0 0820601e400200541b000090610340fd0020611ec80100540820601ee40000540000669e1f2003d501f874d3210100b5e1031faa29000014200080d200ffeff20000679e1f2003d5c0035fd6c0035fd621fc0fd100d0419200004cb23f0040f2e2079f9a0020c29a0000008be2031faa0304e0d2e4031faa030000140000008b63fc41d3030100b48500038b1f0005eb63ffff54a400038b000005cb4200038bf7ffff1721fc4193430040926300028b21f80f911f2003d51f0000f16010829a00fc41d300d0018b0000679ec0035fd60000008b210400d1c0ffa7b621040091dcffff17000000000000000000000000 1
reloc 8 8 R_ARM64_PCREL_LDST64 0 y9
pcln y14 y15 y16 y17 y10,y11,y12,y13 y2,y2,_,_,_,y3,y4
usedfiles 17,50,52
inltree 0 -1 p51:103:34:0:0 y5 "IsInf" 0
inltree 1 -1 p51:108:19:0:0 y6 "Float64bits" 36
inltree 2 -1 p51:106:13:0:0 y7 "NaN" 72
inltree 3 2 p74:31:44:0:0 y8 "Float64frombits" 68
inltree 4 -1 p51:144:24:0:0 y8 "Float64frombits" 180
data y2 Sxxx 0 4 8000 0100000000000000 0
data y3 SDATA 3 1 8000 0008ff 0
data y4 SDATA 2 1 8000 0000 0
data y9 SRODATA 8 8 8800 ffffffffffffef7f 0
data y10 SRODATA 7 1 28000 00020302043800 0
data y11 SRODATA 0 1 28000 - 0
data y12 SRODATA 0 1 28000 - 0
data y13 SRODATA 3 1 28000 043c00 0
data y14 SRODATA 3 1 28000 023c00 0
data y15 SRODATA 21 1 28000 660241034203040103050403450142200401030900 0
data y16 SRODATA 90 1 28000 d001025d035e0204018b0101920101040102038b0103130196010103011c0102010201020206010401090210010f011e0102010f0102010202020102010202130122020401020107010603cb0101c60101350102010301080500 0
data y17 SRODATA 21 1 28000 000202030103040103050803010105200a01090900 0
end
dwarf
sym y18 "" 0
sym y19 "" 0
sym y20 "" 0
sym y21 "" 0
sym y22 "math.IsNaN" 1
inl i16 - p51:103:22:0:0 y22 "IsNaN"
posbase p72 "math/bits.go" 1 1 16 17 "math/bits.go" "math/bits.go" 1 1
posbase p18 "math/bits.go" 1 1 -1 17 "math/bits.go" "math/bits.go" 1 1
posbase p53 "math/unsafe.go" 1 1 -1 52 "math/unsafe.go" "math/unsafe.go" 1 1
sym y23 "go:info.math.IsNaN$abstract" 0
sym y24 "go:info.math.IsInf$abstract" 0
sym y25 "go:info.math.NaN$abstract" 0
sym y26 "go:info.math.Float64bits$abstract" 0
sym y27 "go:info.math.Float64frombits$abstract" 0
sym y28 "go:info.float64" 0
sym y29 "go:info.uint64" 0
sym y30 "go:info.int" 0
sym y31 "type:float64" 0
dwfn y18 y19 y20 - y21 "math.sqrt" 50:100 1 0 1 177
dwdcl n1
dwclosure 0 -
dwmark p51:129:2:0:0 1
dwmark p51:129:13:0:0 2
dwmark p51:138:2:0:0 0
dwparents 0,1
dwparams n1,n2
dwinlfn y22 y23
dwinlfn y5 y24
dwinlfn y7 y25
dwinlfn y6 y26
dwinlfn y8 y27
dwinldcl y22 "f" 0 p18:34:12:0:0
dwinldcl y22 "is" 0 p18:34:24:0:0
dwinldcl y5 "f" 0 p18:46:12:0:0
dwinldcl y5 "sign" 0 p18:46:23:0:0
dwinldcl y5 "~r0" 0 p18:46:33:0:0
dwinldcl y7 "~r0" 0 p18:31:12:0:0
dwinldcl y6 "f" 0 p53:35:18:0:0
dwinldcl y6 "~r0" 0 p53:35:29:0:0
dwinldcl y8 "b" 0 p53:41:22:0:0
dwinldcl y8 "~r0" 0 p53:41:32:0:0
dwname n1 1 1 0 0 0 0 0 0 - - "float64" 0 0 1 p51:100:11:0:0
dwname n17 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p76:41:22:0:0
dwname n19 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p77:41:22:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "int" 0 0 1 p51:110:2:0:0
dwname n9 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p72:34:12:0:0
dwname n11 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p73:46:12:0:0
dwname n15 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p75:35:18:0:0
dwname n3 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p51:108:2:0:0
dwname n5 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p51:127:6:0:0
dwname n7 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p51:128:2:0:0
dwname n6 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p51:127:9:0:0
dwname n12 1 0 0 1 0 0 0 0 - - "int" 0 0 1 p73:46:23:0:0
dwname n8 1 0 0 0 0 0 0 0 - - "uint64" 0 0 1 p51:130:3:0:0
dwname n2 1 0 0 0 0 0 0 1 - - "float64" 0 0 1 p51:100:22:0:0
dwname n14 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p74:31:12:0:0
dwname n16 1 0 0 1 0 0 0 0 - - "uint64" 0 0 1 p75:35:29:0:0
dwname n18 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p76:41:32:0:0
dwname n20 1 0 0 1 0 0 0 0 - - "float64" 0 0 1 p77:41:32:0:0
dwname n21 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p51:103:26:0:0
dwname n22 1 0 1 0 0 0 0 0 - - "bool" 0 0 1 p51:103:14:0:0
dwname n10 1 0 0 1 0 0 0 0 - - "bool" 0 0 1 p72:34:24:0:0
dwname n13 1 0 0 1 0 0 0 0 - - "bool" 0 0 1 p73:46:33:0:0
var 0 0 "x" 5 1 0 0 0 8 y28 "math/sqrt.go" 100 11 0 0 0 0 v0
var 1 0 "~r0" 5 1 1 0 0 0 y28 "math/sqrt.go" 100 22 0 1 0 0 -
var 2 0 "f" 5 1 0 1 0 -8 y28 "math/bits.go" 34 12 17 0 1 0 v1
var 3 0 "f" 5 1 0 1 0 -8 y28 "math/bits.go" 46 12 18 0 1 0 v2
var 4 0 "ix" 52 1 0 0 0 -8 y29 "math/sqrt.go" 108 2 0 2 0 0 v3
var 5 0 "exp" 52 1 0 0 0 -8 y30 "math/sqrt.go" 110 2 0 3 0 0 v4
var 6 0 "q" 52 1 0 0 0 -8 y29 "math/sqrt.go" 127 6 0 4 0 0 v5
var 7 0 "s" 52 1 0 0 0 -8 y29 "math/sqrt.go" 127 9 0 5 0 0 v6
var 8 0 "r" 52 1 0 0 0 -8 y29 "math/sqrt.go" 128 2 0 6 0 0 v7
var 9 0 "t" 52 1 0 0 0 -8 y29 "math/sqrt.go" 130 3 0 7 0 0 v8
scope 0 0 0:240 0,1,2,3,4,5,6,7,8
scope 1 0 116:120,124:164 -
scope 2 1 124:132,136:164 9
inlcall 0 17 50:103 y24 - 1 8:20 3
inlcall 1 19 50:108 y26 - 1 32:36 -
inlcall 2 18 50:106 y25 3 1 56:72 -
inlcall 3 21 17:31 y27 - 0 56:68 -
inlcall 4 20 50:144 y27 - 1 200:204 -
inlcall 5 16 50:103 y23 - 1 - 2
dieref y18 20 y24 0
data y18 SDWARFFCN 217 0 0 036d6174682e73717274000000f001019c3300000064012d7800006400000000000000002e7e72300001640000000000276978006c000000000000000027657870006e00000000000000002771007f00000000000000002773007f0000000000000000277200800100000000000000000c000000002774008201000000000000000000090000000000000000330000006729000000000000000000090000000000000000330000006c00090000000000000000330000006a090000000000000000120000001f00000900000000000000003300000090010000 30
reloc 0 0 R_USETYPE 0 y31
reloc 11 2 R_DWTXTADDR_U2 0 y1
reloc 28 4 R_DWARFSECREF 0 y28
reloc 32 4 R_DWARFSECREF 0 y19
reloc 43 4 R_DWARFSECREF 0 y28
reloc 53 4 R_DWARFSECREF 0 y29
reloc 57 4 R_DWARFSECREF 10 y19
reloc 67 4 R_DWARFSECREF 0 y30
reloc 71 4 R_DWARFSECREF 32 y19
reloc 79 4 R_DWARFSECREF 0 y29
reloc 83 4 R_DWARFSECREF 61 y19
reloc 91 4 R_DWARFSECREF 0 y29
reloc 95 4 R_DWARFSECREF 83 y19
reloc 104 4 R_DWARFSECREF 0 y29
reloc 108 4 R_DWARFSECREF 105 y19
reloc 113 4 R_DWARFSECREF 0 y20
reloc 122 4 R_DWARFSECREF 0 y29
reloc 126 4 R_DWARFSECREF 123 y19
reloc 132 4 R_DWARFSECREF 0 y24
reloc 136 4 R_DWARFSECREF 13 y20
reloc 146 4 R_DWARFSECREF 0 y24
reloc 150 4 R_DWARFSECREF 134 y19
reloc 156 4 R_DWARFSECREF 0 y26
reloc 160 4 R_DWARFSECREF 20 y20
reloc 171 4 R_DWARFSECREF 0 y25
reloc 175 4 R_DWARFSECREF 27 y20
reloc 185 4 R_DWARFSECREF 0 y27
reloc 189 4 R_DWARFSECREF 34 y20
reloc 201 4 R_DWARFSECREF 0 y27
reloc 205 4 R_DWARFSECREF 41 y20
data y19 SDWARFLOC 144 0 0 0100000400440290400001000004243801500450c001015004c801f001015000010000042c3401510450b401015104d801d801015104d801f0010151000100000428380150047c84010152048401f0010150000100000428380150047c84010154048401f00101500001000004840184010153048401ac01015300010000048c01a40101550001000004004402904000 8
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 11 2 R_DWTXTADDR_U2 0 y1
reloc 33 2 R_DWTXTADDR_U2 0 y1
reloc 62 2 R_DWTXTADDR_U2 0 y1
reloc 84 2 R_DWTXTADDR_U2 0 y1
reloc 106 2 R_DWTXTADDR_U2 0 y1
reloc 124 2 R_DWTXTADDR_U2 0 y1
reloc 135 2 R_DWTXTADDR_U2 0 y1
data y20 SDWARFRANGE 50 0 0 010000047c8401048801a401000100000408140001000004202400010000043848000100000438440001000004c801cc0100 6
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 14 2 R_DWTXTADDR_U2 0 y1
reloc 21 2 R_DWTXTADDR_U2 0 y1
reloc 28 2 R_DWTXTADDR_U2 0 y1
reloc 35 2 R_DWTXTADDR_U2 0 y1
reloc 42 2 R_DWTXTADDR_U2 0 y1
data y21 SDWARFLINES 156 0 0 0009020000000000000000043303e100140637041206035533065f043306032a3c06370639043503be7f33043303c4003c3938063704350603be7f5b065f041206037a33043303c6003c3503093c38383806373a063906037f3303036406037c33030a3c38037c333838063706383838063706037a33030c3c0637390638333a0637043506039e7f5b043303de003c03693338353b06370210000101 1
reloc 3 8 R_ADDR 0 y1
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`) with P0' (`p0PrimeSyms`, as `gen-check`
runs G56 and G60): genssa's `FMOVD $(MaxFloat64), F1` becomes the load
`FMOVD $f64.7fefffffffffffff(SB), F1` (`math.MaxFloat64` is no `FMOV` immediate), the symbol added
to G2's symbols. -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) := do
  let (lc, ps, bs, g) ← GenG2.load fSsa fProg
  let (syms', ps') ← GoFV.Asm.p0PrimeSyms g.syms ps
  return (lc, ps', bs, { g with syms := syms' })

/-- `runLoc`'s context of `math.sqrt`. -/
def lc0 : LocCtx :=
  match stIn with
  | .ok x => x.1
  | .error _ => { ctx := default, homes := #[], temps := #[] }

/-- The context G60's check runs on (`liveCtx`). -/
def lc : LocCtx := liveCtx lc0

/-- P0'. -/
def ps : Array GoFV.Asm.Prog :=
  match stIn with
  | .ok x => x.2.1
  | .error _ => #[]

def bs : ID → Option Nat :=
  match stIn with
  | .ok x => x.2.2.1
  | .error _ => fun _ => none

/-- G2's inputs with the constant symbol. -/
def g : G2In :=
  match stIn with
  | .ok x => x.2.2.2
  | .error _ => { syms := #[], slotOp := fun _ => none, stksize := 0 }

/-- The PC table `checkG60` gives. -/
def tab : PcTab := (match checkG60 lc0 ps bs g with
  | .ok (t, _) => t
  | .error _ => [])

/-- The class table `checkG60` gives. -/
def kt : KTab := (match checkG60 lc0 ps bs g with
  | .ok (_, k) => k
  | .error _ => [])

/-- `b6`, the block of `v56`. -/
def blk : Block := (lc.ctx.f.block? 6).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0''s layout: the Prog with ID `n` at `0x10000 + 4n`, a 16-byte frame, every symbol at
`symA`. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- The float constant symbol of `math.MaxFloat64`. -/
def cName : String := "$f64.7fefffffffffffff"

/-- Its allocation: the eight little-endian bytes of `math.MaxFloat64`'s bits, read-only. -/
def cAl : Alloc := roAlloc (leBytesU8 0x7fefffffffffffff 8)

/-- A framed activation whose `outargs` block sits at `SP` (`SP = GenG48.spO`, `g = 0x9000`, saved
`LR` and `FP` 0; `GenG48.ι48`: the globals at `symA`, `outargs 0` at `SP`), with the PC table of
`checkG60`. -/
def E : MatchEnv :=
  { lc, ι := GenG48.ι48, sp := GenG48.spO, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab, outSP := true }

/-- The Phase 1 memory before `v56`: the constant symbol, read-only. -/
def mem1 : Mem := { blocks := #[(.global cName, cAl)] }

/-- The machine memory before `v56`: `math.MaxFloat64`'s bits, little-endian, at `symA`, 0
elsewhere. -/
def M1 : Memory := fun y =>
  if y = GenG2.symA + 7 then 0x7f else if y = GenG2.symA + 6 then 0xef
  else if y = GenG2.symA + 5 then 0xff else if y = GenG2.symA + 4 then 0xff
  else if y = GenG2.symA + 3 then 0xff else if y = GenG2.symA + 2 then 0xff
  else if y = GenG2.symA + 1 then 0xff else if y = GenG2.symA then 0xff else 0

/-- The `runLoc` state before `v56`: every register `poison`, the memory `mem1`. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := mem1 },
    regs := Array.replicate 64 .poison, flags := .poison, slots := [], mem := .mem mem1 }

/-- The machine before `v56`: the activation's `g` and `FP`, every V register 0, the PC of
`v56`, the memory `M1`. -/
def m0 : MState :=
  { x := fun k => if k = 28 then 0x9000 else if k = 29 then GenG48.spO - 8 else 0,
    sp := GenG48.spO, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 6 1, mem := M1 }

/-- `F1` (Go register 32) holds `math.MaxFloat64`'s bits. -/
def f1Is (s : LocState) : Bool :=
  match (s.regs[32]? : Option Val) with
  | some (Val.int .w64 x) => x == 0x7fefffffffffffff
  | _ => false

theorem f1Is_spec {s : LocState} (h : f1Is s = true) :
    s.regs[32]? = some (.int .w64 0x7fefffffffffffff) := by
  unfold f1Is at h
  split at h
  · rename_i x hx
    simp only [beq_iff_eq] at h
    subst h
    exact hx
  · cases h

/-- What compiled evaluation checks on `math.sqrt`: it holds an arm64 op; on P0', `checkG60`
accepts it with `tab` and `kt`, and neither `checkG56` (first at `v96`'s `SLL` of a narrow
argument, G58's group A) nor `checkG59` (its constant is a load) does; it accesses no frame
variable and has no home slot; it is of activation 0; `b6` holds `v56` (`FMOVDconst [MaxFloat64]`) at index 1, where G35's
table is empty; the float constant symbols among G2's symbols are `$f64.7fef…` alone, with `cAl`;
`stepLoc` runs `v56` from `s0` to a state with `math.MaxFloat64`'s bits in `F1` (Go register
32). -/
def gFacts : Bool :=
  lc.ctx.f.lowered &&
    (checkG60 lc0 ps bs g).toOption == some (tab, kt) && (checkG56 lc0 ps bs g).toOption.isNone &&
    (checkG59 lc0 ps bs g).toOption.isNone &&
    (accessedVars lc).isEmpty && (homeSlots lc).isEmpty && lc.ctx.act == 0 &&
    lc.ctx.f.blocks.toList.contains 6 && (lc.ctx.f.block? 6).isSome &&
    (lc.ctx.f.value? 56).isSome && blk.values[1]? == some 56 &&
    (val 56).op == .ARM64FMOVDconst &&
    constRo (symNames g) == [(cName, cAl)] &&
    uL35 lc (uIn35 lc 6) blk 1 == [] &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 56)) f1Is

theorem g60_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ checkG60 lc0 ps bs g = .ok (tab, kt) ∧
      (checkG56 lc0 ps bs g).toOption = none ∧ (checkG59 lc0 ps bs g).toOption = none ∧
      (accessedVars lc).isEmpty = true ∧ (homeSlots lc).isEmpty = true ∧ lc.ctx.act = 0 ∧
      6 ∈ lc.ctx.f.blocks.toList ∧ lc.ctx.f.block? 6 = some blk ∧
      lc.ctx.f.value? 56 = some (val 56) ∧ blk.values[1]? = some 56 ∧
      (val 56).op = .ARM64FMOVDconst ∧
      constRo (symNames g) = [(cName, cAl)] ∧
      uL35 lc (uIn35 lc 6) blk 1 = [] ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 56)) f1Is = true := by
  have hf := g60_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, and_assoc,
    Option.isNone_iff_eq_none] at hf
  obtain ⟨hl, hres, h56, h59, hav, hsl, hact, hm1, hbs, hvs, hi1, hop, hro, hu1, hrun⟩ := hf
  refine ⟨hl, ?_, h56, h59, hav, hsl, hact, hm1, ?_, ?_, hi1, hop, hro, hu1, hrun⟩
  · revert hres; cases checkG60 lc0 ps bs g <;> simp [Except.toOption]
  · obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hbs
    simp [blk, hb]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]

/-! ## The activation -/

theorem g60Env (hc : checkG60 lc0 ps bs g = .ok (tab, kt)) (hl : lc.ctx.f.lowered = true)
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
                checkG60L_spec hl (checkG60_spec hc).2
              intro p hp
              exact GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp)
            addr := GenG48.addrAgree48
            glob := fun _ _ _ _ => rfl
            syms := by
              obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlt, -, -, -, -, -, -, -⟩ :=
                checkG60L_spec hl (checkG60_spec hc).2
              intro y
              have hs : L.sym y = GenG2.symA := rfl
              rw [hs]
              refine ⟨by decide, fun p hp => ?_⟩
              exact GenG2.prog_addr_ne (hlt p hp) hp (Or.inr (by decide)) (by decide)
            calls := fun h => by cases h
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by show 0 ≤ (8 : Int); decide
            frame := ⟨by show 4096 + 8 ≤ GenG48.spO.toNat; decide,
              by show GenG48.spO.toNat + 8 ≤ 2 ^ 64; decide, fun k off h => by cases h⟩ }
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

theorem cAl_size : cAl.data.size = 8 := by
  simp [cAl, roAlloc, leBytesU8]

/-- `M1` holds `math.MaxFloat64`'s bits little-endian at `symA`. -/
theorem m1_bytes : ∀ i, i < 8 →
    M1 (GenG2.symA + BitVec.ofNat 64 i) = BitVec.ofNat 8 (0x7fefffffffffffff / 256 ^ i) := by
  decide

theorem mem1_blocks {b : Blk} {al : Alloc} (h : (b, al) ∈ mem1.blocks) :
    b = .global cName ∧ al = cAl := by
  simpa [mem1] using h

/-- `mem1` injected into `M1` by `GenG48.ι48`: the constant's bytes at `symA`. -/
theorem memInj1 : MemInj GenG48.ι48 mem1 M1 where
  nil := rfl
  mapped := by
    intro b al h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    refine ⟨GenG2.symA, rfl, fun _ => by decide, ?_⟩
    rw [cAl_size]
    decide
  inj := by
    intro b al b' al' a a' h h' hne ha ha'
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    obtain ⟨rfl, rfl⟩ := mem1_blocks h'
    exact absurd rfl hne
  bytes := by
    refine ⟨fun _ _ => False, fun b al a h ha => ?_⟩
    refine ⟨fun o h => h.elim, fun o _ h => h.elim, fun i hi _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = GenG2.symA := by simp [GenG48.ι48] at ha; exact ha.symm
    subst ha'
    have hi8 : i < 8 := cAl_size ▸ hi
    have hb : cAl.data[i]? = some (.b (BitVec.ofNat 8 (0x7fefffffffffffff / 256 ^ i))) :=
      roAlloc_byte hi8
    rw [Array.getElem?_eq_getElem hi, Option.some.injEq] at hb
    change ByteRel GenG48.ι48 cAl.data[i] _
    rw [hb]
    exact (m1_bytes i hi8).symm

theorem keys1 : KeysNodup mem1 := by simp [KeysNodup, mem1]

theorem sep1 : SepFrom GenG48.ι48 (StkAt E) mem1 := by
  intro b al a h ha y hy
  rcases hy with ⟨-, h1, -⟩ | ⟨k, off, hk, -⟩
  · have hsp : E.sp.toNat = 0x4000000000000000 := rfl
    rw [hsp] at h1
    obtain ⟨rfl, rfl⟩ := mem1_blocks h
    have ha' : a = GenG2.symA := by simp [GenG48.ι48] at ha; exact ha.symm
    subst ha'
    have hA : GenG2.symA.toNat = 0x10000000000 := rfl
    simp only [hA, cAl_size]
    omega
  · cases hk

/-- The constant symbol is in `mem1`, read-only: `RoPre56` at `s0`. -/
theorem ro0 (hro : constRo (symNames g) = [(cName, cAl)]) : RoPre56 g s0 := by
  intro mm hmm
  change Val.mem mem1 = Val.mem mm at hmm
  cases hmm
  rw [hro]
  intro n a h
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨rfl, by simp [mem1, Mem.find?]⟩

/-! ## `v56`: `FMOVDconst [MaxFloat64]` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) : x = .poison := by
  simp only [s0, Array.getElem?_replicate] at h
  split at h
  · simp only [Option.some.injEq] at h; exact h.symm
  · cases h

theorem locMatch0 : LocMatch E s0 6 1 m0 where
  regs := by
    intro r v hv
    rw [s0_regs hv]
    exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨mem1, rfl, memInj1⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, M1, E]; decide,
    by simp only [MState.word, readMem, m0, M1, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem g60Inv0 : G3Inv E lc (kAt lc kt 6 blk 1) s0 E.outSP where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, mem1, rfl, keys1, sep1.w⟩
    rw [s0_regs hv]
    trivial
  slots := by intro k v h; simp [s0] at h

/-- `SPInv`: `outargs 0` at `SP`; the Go register `SP` holds `poison`. -/
theorem spInv0 (hact : lc.ctx.act = 0) : SPInv E s0 := by
  refine fun _ => ⟨?_, fun x hx => ?_⟩
  · show GenG48.ι48 (.outargs lc.ctx.act) = some GenG48.spO
    rw [hact]
    rfl
  · rw [s0_regs hx]
    trivial

/-- The per-value premises of G54 on `v56`, `FMOVDconst`: none of them applies. -/
theorem pre54 (hop : (val 56).op = .ARM64FMOVDconst) : G54Pre lc s0 (val 56) := by
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDconst → (val 56).op ≠ o := fun o h h' =>
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

/-- **G60 on `math.sqrt`** (`v56: FMOVDconst [MaxFloat64]` in `F1`, the bound of `sqrt`'s
`x > MaxFloat64` test): `math.MaxFloat64` is no `FMOV` immediate, so on P0' its Prog is the load
`FMOVD $f64.7fefffffffffffff(SB), F1`. `checkG59` rejects the function (G59 has no constant load)
and `checkG56` rejects it (its `SLL` of a narrow argument is G58's), and `checkG60` accepts it. From
`s0`, whose memory has the constant symbol (`RoPre56`, as `lreach_roMem` gives), with every V
register 0 in `m0` and the constant's bytes at the symbol's linked address, `stepLoc` runs `v56`
and `g60_value` relates it to a machine state after the load with `math.MaxFloat64`'s bits in
`V1`'s low word, under an activation extending `E` (whose `outargs` block sits at `SP`, G48's mode) that is again a
`G49Env`. -/
theorem genG60_witness :
    (checkG56 lc0 ps bs g).toOption = none ∧ (checkG59 lc0 ps bs g).toOption = none ∧
      (m0.v 1).setWidth 64 = 0 ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 56) = .ok s1 ∧
        s1.regs[32]? = some (.int .w64 0x7fefffffffffffff) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧ PStar GenG2.H0 L ps.toList 0 m0 m1 ∧
        LocMatch E1 s1 6 2 m1 ∧ (m1.v 1).setWidth 64 = 0x7fefffffffffffff := by
  obtain ⟨hl, hc, h56, h59, hav, hsl, hact, hm1, hb, hv56, hi1, hop, hro, hu1, hrun⟩ := facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr32 := f1Is_spec hr
  have hE := g60Env hc hl hav hsl
  have hne : ∀ o : Op, o ≠ .ARM64FMOVDconst → (val 56).op ≠ o := fun o h h' =>
    h (h'.symm.trans hop)
  -- `g60_value` reads the blocks and values of `lc0`: rewrite rather than unfold (the kernel
  -- would evaluate `lc0`).
  have hl0 : lc0.ctx.f.lowered = true := by rw [← liveCtx_ctx (lc := lc0)]; exact hl
  have hm0 : 6 ∈ lc0.ctx.f.blocks.toList := by rw [← liveCtx_ctx (lc := lc0)]; exact hm1
  have hb0 : lc0.ctx.f.block? 6 = some blk := by rw [← liveCtx_ctx (lc := lc0)]; exact hb
  have hv0 : lc0.ctx.f.value? 56 = some (val 56) := by
    rw [← liveCtx_ctx (lc := lc0)]; exact hv56
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1', -, -, -⟩ := g60_value (H := GenG2.H0) (env := GenG2.env)
    hc hE hl0 hm0 hb0 hi1 hv0 (by rw [hop]; rfl) locMatch0 g60Inv0 (spInv0 hact) rfl
    (by change UOKL m0 (uL35 lc (uIn35 lc 6) blk 1); rw [hu1]; intro e he; cases he)
    (pre54 hop) (ro0 hro)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun _ _ _ _ _ _ _ _ _ _ hn => by rw [hop] at hn; cases hn)
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) (fun h => absurd h (hne _ (by decide)))
    (fun h => absurd h (hne _ (by decide))) hs1
  have hV : (m1.v 1).setWidth 64 = 0x7fefffffffffffff :=
    (hm1'.regs 32 _ hr32).2 1 rfl
  exact ⟨h56, h59, rfl, s1, E1, m1, hs1, hr32, hx1, hE1, hp1, hm1', hV⟩

end GoFV.Proof.Witness.GenG60
