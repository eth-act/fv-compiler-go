import GoFV.Gen.Check57
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Witness.GenG2

open scoped GoFV.SSA.Sem.Fixed

namespace GoFV.Proof.Witness.GenG58a3

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Proof.Gen

/-- `std/std/runtime/%28%2ApinState%29.set,1.ssa` (quick-v10). -/
def fSsa : String := r#"gofv-ssa 5.1
pkg "runtime"
func "(*pinState).set" 1 0 0
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
type t5 UINT8 1 1 0 comparable,named "uint8" "uint8"
type t4 PTR 8 8 8 hasptr,direct,comparable "*uint8" "*uint8" t5
type t3 STRUCT 16 8 8 hasptr,comparable,named "pinState" "runtime.pinState" 3
field 0 "bytep" t4 0 0
field 1 "byteVal" t5 8 0
field 2 "mask" t5 9 0
type t2 PTR 8 8 8 hasptr,direct,comparable "*pinState" "*runtime.pinState" t3
type t6 BOOL 1 1 0 comparable,named "bool" "bool"
type t1 FUNC 8 8 8 hasptr,direct "method(*pinState) func(bool, bool)" "method(*runtime.pinState) func(bool, bool)" 1 2 0
field 0 "v" t2 ? 0
field 1 "val" t6 ? 0
field 2 "multipin" t6 ? 0
aux a2 sym "runtime.(*pinState).set" "runtime.(*pinState).set" 1 - 0 - - - - 0
posbase p52 "runtime/pinner.go" 1 1 -1
aux a3 name "v" "v" PPARAM t2 0 1 used p52:265:7:0:0
aux a4 name "val" "val" PPARAM t6 8 1 used p52:265:24:0:0
aux a5 name "multipin" "multipin" PPARAM t6 9 1 used p52:265:34:0:0
aux a1 call "AuxCall{runtime.(*pinState).set}" a2 1 3 0 8 16 3 0
abiparam in 0 t2 a3 0 0
abiparam in 1 t6 a4 1 8
abiparam in 2 t6 a5 2 9
type t7 INT8 1 1 0 comparable,named "int8" "int8"
type t8 INT16 2 2 0 comparable,named "int16" "int16"
type t9 INT32 4 4 0 comparable,named "int32" "int32"
type t10 INT64 8 8 0 comparable,named "int64" "int64"
type t11 UINT16 2 2 0 comparable,named "uint16" "uint16"
type t12 UINT32 4 4 0 comparable,named "uint32" "uint32"
type t13 UINT64 8 8 0 comparable,named "uint64" "uint64"
type t14 INT 8 8 0 comparable,named "int" "int"
type t15 FLOAT32 4 4 0 comparable,named "float32" "float32"
type t16 FLOAT64 8 8 0 comparable,named "float64" "float64"
type t17 UINT 8 8 0 comparable,named "uint" "uint"
type t18 UINTPTR 8 8 0 comparable,named "uintptr" "uintptr"
type t19 STRING 16 8 8 hasptr,comparable,named "string" "string"
type t20 PTR 8 8 8 hasptr,direct,comparable "*int32" "*int32" t9
type t21 PTR 8 8 8 hasptr,direct,comparable "*uint32" "*uint32" t12
type t22 PTR 8 8 8 hasptr,direct,comparable "*int" "*int" t14
type t23 PTR 8 8 8 hasptr,direct,comparable "*uintptr" "*uintptr" t18
type t24 PTR 8 8 8 hasptr,direct,comparable "*float32" "*float32" t15
type t25 PTR 8 8 8 hasptr,direct,comparable "*float64" "*float64" t16
type t26 PTR 8 8 8 hasptr,direct,comparable "**uint8" "**uint8" t4
type t27 COMPLEX64 8 4 0 comparable,named "complex64" "complex64"
type t28 COMPLEX128 16 8 0 comparable,named "complex128" "complex128"
type t29 UNSAFEPTR 8 8 8 hasptr,direct,comparable,named "unsafe.Pointer" "unsafe.Pointer"
type t30 SSA ? ? ? - "mem" ""
type t31 SSA ? ? ? - "flags" ""
type t32 SSA ? ? ? - "void" ""
type t33 SSA 16 8 ? - "int128" ""
type t34 RESULTS ? ? ? - "mem" "" 1 t30
type t35 PTR 8 8 8 hasptr,direct,comparable "**pinState" "**runtime.pinState" t2
type t36 PTR 8 8 8 hasptr,direct,comparable "*bool" "*bool" t6
aux a6 sym "runtime.arm64HasATOMICS" "runtime.arm64HasATOMICS" 0 - 0 - - - - 0
type t37 TUPLE ? ? ? - "uint8,mem" "" t5 t30
slot s1 a3 t2 0 - 0
slot s2 a4 t6 0 - 0
slot s3 a5 t6 0 - 0
aux a7 name "mask" "mask" PAUTO t5 0 1 used p52:266:2:0:0
slot s4 a7 t5 0 - 0
f b1 t1 a1 52 12
typs Bool=t6,Int8=t7,Int16=t8,Int32=t9,Int64=t10,UInt8=t5,UInt16=t11,UInt32=t12,UInt64=t13,Int=t14,Float32=t15,Float64=t16,UInt=t17,Uintptr=t18,String=t19,BytePtr=t4,Int32Ptr=t20,UInt32Ptr=t21,IntPtr=t22,UintptrPtr=t23,Float32Ptr=t24,Float64Ptr=t25,BytePtrPtr=t26,Complex64=t27,Complex128=t28,UnsafePtr=t29,Mem=t30,Flags=t31,Void=t32,Int128=t33,ResultMem=t34
b b1 If p52:267:2:0:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p52:265:6:2:0 2 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:0:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v16 b5:0,b6:0 b1:1,b3:0
v v16 Copy t6 0 - p52:270:2:2:0 1 v8
v v48 Phi t5 0 - p52:270:2:0:0 2 v12,v15
v v49 Copy t30 0 - p52:273:16:2:0 2 v1
v v50 Copy t2 0 - p52:273:16:2:0 2 v7
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v13 Copy t5 0 - p52:268:8:2:0 1 v12
v v15 Lsh8x64 t5 0 - p52:268:8:0:0 1 v13,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v17 Copy t2 0 - p52:271:15:2:0 1 v50
v v18 Copy t30 0 - p52:271:15:2:0 5 v49
v v19 NilCheck t2 0 - p52:271:15:0:0 1 v17,v18
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v18
v v22 Copy t5 0 - p52:271:13:2:0 2 v48
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v18
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v31 Copy t2 0 - p52:273:16:2:0 1 v50
v v32 Copy t30 0 - p52:273:16:2:0 5 v49
v v33 NilCheck t2 0 - p52:273:16:0:0 1 v31,v32
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v32
v v36 Copy t5 0 - p52:273:24:2:0 1 v48
v v37 Com8 t5 0 - p52:273:24:0:0 2 v36
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v32
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v25 Copy t30 0 - p52:271:13:2:0 1 v18
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v22,v25
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v28 Copy t30 0 - p52:271:13:2:0 1 v18
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v22,v28
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:0:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v40 Copy t30 0 - p52:273:14:2:0 1 v32
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v40
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v43 Copy t30 0 - p52:273:14:2:0 1 v32
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v43
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:0:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7,v17,v31,v50
named s2 v8,v16
named s3 v9
named s4 v12,v13,v15,v22,v36,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev -
freeb -
dcllen 6
end
pass 1 "number lines"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 6 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p52:265:6:2:0 2 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v16 b5:0,b6:0 b1:1,b3:0
v v16 Copy t6 0 - p52:270:2:2:0 1 v8
v v48 Phi t5 0 - p52:270:2:1:0 2 v12,v15
v v49 Copy t30 0 - p52:273:16:2:0 2 v1
v v50 Copy t2 0 - p52:273:16:2:0 2 v7
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v13 Copy t5 0 - p52:268:8:2:0 1 v12
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v13,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v17 Copy t2 0 - p52:271:15:2:0 1 v50
v v18 Copy t30 0 - p52:271:15:2:0 5 v49
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v17,v18
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v18
v v22 Copy t5 0 - p52:271:13:2:0 2 v48
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v18
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v31 Copy t2 0 - p52:273:16:2:0 1 v50
v v32 Copy t30 0 - p52:273:16:2:0 5 v49
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v31,v32
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v32
v v36 Copy t5 0 - p52:273:24:2:0 1 v48
v v37 Com8 t5 0 - p52:273:24:0:0 2 v36
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v32
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v25 Copy t30 0 - p52:271:13:2:0 1 v18
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v22,v25
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v28 Copy t30 0 - p52:271:13:2:0 1 v18
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v22,v28
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v40 Copy t30 0 - p52:273:14:2:0 1 v32
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v40
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v43 Copy t30 0 - p52:273:14:2:0 1 v32
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v43
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7,v17,v31,v50
named s2 v8,v16
named s3 v9
named s4 v12,v13,v15,v22,v36,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev -
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 2 "early phielim and copyelim"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 22 -
v v2 SP t18 0 - p0:0:0:0:0 3 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v4 LocalAddr t35 0 a3 p0:0:0:0:0 0 v2,v1
v v5 LocalAddr t36 0 a4 p0:0:0:0:0 0 v2,v1
v v6 LocalAddr t36 0 a5 p0:0:0:0:0 0 v2,v1
v v7 Arg t2 0 a3 p52:265:6:2:0 6 -
v v8 Arg t6 0 a4 p52:265:6:2:0 2 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 3 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v16 Copy t6 0 - p52:270:2:2:0 0 v8
v v48 Phi t5 0 - p52:270:2:1:0 5 v12,v15
v v49 Copy t30 0 - p52:273:16:2:0 0 v1
v v50 Copy t2 0 - p52:273:16:2:0 0 v7
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v13 Copy t5 0 - p52:268:8:2:0 0 v12
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v17 Copy t2 0 - p52:271:15:2:0 0 v7
v v18 Copy t30 0 - p52:271:15:2:0 0 v1
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v22 Copy t5 0 - p52:271:13:2:0 0 v48
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v31 Copy t2 0 - p52:273:16:2:0 0 v7
v v32 Copy t30 0 - p52:273:16:2:0 0 v1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v36 Copy t5 0 - p52:273:24:2:0 0 v48
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v25 Copy t30 0 - p52:271:13:2:0 0 v1
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v28 Copy t30 0 - p52:271:13:2:0 0 v1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v40 Copy t30 0 - p52:273:14:2:0 0 v1
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v43 Copy t30 0 - p52:273:14:2:0 0 v1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7,v7,v7,v7
named s2 v8,v8
named s3 v9
named s4 v12,v12,v15,v48,v48,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev -
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 3 "early deadcode"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 4 "short circuit"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 5 "decompose user"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 6 "pre-opt deadcode"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 0 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 7 "opt"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 8 "zero arg cse"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 9 "opt deadcode"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 1 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 1 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 1 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 1 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v19
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 1 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v33
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v38,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache linestarts 52:266:275
dcllen 6
end
pass 10 "generic cse"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 0 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 0 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v10
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 0 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v10
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 11 "phiopt"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v38 Addr t36 0 a6 p0:0:0:0:0 0 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 0 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v10
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 0 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v10
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 12 "gcse deadcode"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 12 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 3 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 NilCheck t2 0 - p52:271:15:1:0 0 v7,v1
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v10
v v21 Load t4 0 - p52:271:15:0:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 NilCheck t2 0 - p52:273:16:1:0 0 v7,v1
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v10
v v35 Load t4 0 - p52:273:16:0:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 13 "nilcheckelim"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v10 NilCheck t2 0 - p52:266:11:1:0 5 v7,v1
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 Copy t2 0 - p52:271:15:1:0 0 v10
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v10
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 Copy t2 0 - p52:273:16:1:0 0 v10
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v10
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 14 "prove"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 5 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v19 Copy t2 0 - p52:271:15:1:0 0 v10
v v20 OffPtr t26 0 - p52:271:15:0:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v33 Copy t2 0 - p52:273:16:1:0 0 v10
v v34 OffPtr t26 0 - p52:273:16:0:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 15 "divisible"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v33,v19,v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 16 "divmod"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v33,v19,v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 17 "middle opt"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v33,v19,v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 18 "known bits"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v33,v19,v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 19 "early fuse"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 Arg t2 0 a3 p52:265:6:2:0 1 -
v v8 Arg t6 0 a4 p52:265:6:2:0 1 -
v v9 Arg t6 0 a5 p52:265:6:2:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 1=v14
freev v33,v19,v38,v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 20 "expand calls"
aux a8 nameoff "v+0" a3 0
aux a9 nameoff "val+0" a4 0
aux a10 nameoff "multipin+0" a5 0
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v33 SP t18 0 - p0:0:0:0:0 2 -
v v19 OffPtr t35 0 - p0:0:0:0:0 0 v33
v v38 OffPtr t36 0 - p0:0:0:0:0 0 v33
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 0=v19,v38,1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 21 "decompose builtin"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v33 SP t18 0 - p0:0:0:0:0 2 -
v v19 OffPtr t35 0 - p0:0:0:0:0 0 v33
v v38 OffPtr t36 0 - p0:0:0:0:0 0 v33
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 0=v19,v38,1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 22 "softfloat"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v9 b3:0,b2:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v33 SP t18 0 - p0:0:0:0:0 2 -
v v19 OffPtr t35 0 - p0:0:0:0:0 0 v33
v v38 OffPtr t36 0 - p0:0:0:0:0 0 v33
b b2 If p52:270:2:0:0 0 0 - v8 b5:0,b6:0 b1:1,b3:0
v v48 Phi t5 0 - p52:270:2:1:0 3 v12,v15
b b3 Plain p52:268:12:0:0 0 0 - - b2:1 b1:0
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b2:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b2:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 0=v19,v38,1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b2,b3,b1
cache idom b1:-,b2:b1,b3:b1,b4:b2,b5:b2,b6:b2,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b3:-:2:71,b2:b1:b6:-:11:68,b3:b1:-:b2:5:8,b4:b2:-:-:62:65,b5:b2:b8:b4:38:59,b6:b2:b11:b5:14:35,b7:b5:-:b9:47:50,b8:b5:-:b7:41:44,b9:b5:-:-:53:56,b10:b6:-:b12:23:26,b11:b6:-:b10:17:20,b12:b6:-:-:29:32
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 23 "branchelim"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v14 Const64 t17 1 - p0:0:0:0:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 2 v11,v1
v v33 SP t18 0 - p0:0:0:0:0 2 -
v v19 OffPtr t35 0 - p0:0:0:0:0 0 v33
v v38 OffPtr t36 0 - p0:0:0:0:0 0 v33
v v15 Lsh8x64 t5 1 - p52:268:8:1:0 1 v12,v14
v v48 CondSelect t5 0 - p52:270:2:1:0 3 v15,v12,v9
b b2 BlockInvalid p52:270:2:0:0 0 0 - - - -
b b3 BlockInvalid p52:268:12:0:0 0 0 - - - -
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts 0=v19,v38,1=v14
freev v43,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 24 "late opt"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b2 BlockInvalid p52:270:2:0:0 0 0 - - - -
b b3 BlockInvalid p52:268:12:0:0 0 0 - - - -
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275:268=1
dcllen 6
end
pass 25 "dead auto elim"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b2 BlockInvalid p52:270:2:0:0 0 0 - - - -
b b3 BlockInvalid p52:268:12:0:0 0 0 - - - -
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275:268=1
dcllen 6
end
pass 26 "sccp"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b2 BlockInvalid p52:270:2:0:0 0 0 - - - -
b b3 BlockInvalid p52:268:12:0:0 0 0 - - - -
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v15,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275:268=1
dcllen 6
end
pass 27 "generic deadcode"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 28 "late fuse"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 29 "check bce"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 30 "dse"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 31 "memcombine"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 32 "writebarrier"
f b1 t1 a1 52 12
b b1 If p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 1 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 NilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v23 Addr t36 0 a6 p0:0:0:0:0 2 v3
v v11 OffPtr t4 9 - p52:266:11:0:0 1 v10
v v12 Load t5 0 - p52:266:11:0:0 1 v11,v1
v v48 Lsh8x8 t5 1 - p52:270:2:1:0 3 v12,v43
v v43 CvtBoolToUint8 t5 0 - p52:270:2:1:0 1 v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 If p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v20 OffPtr t26 0 - p52:271:15:1:0 1 v10
v v24 Load t6 0 - p52:271:13:0:0 1 v23,v1
v v21 Load t4 0 - p52:271:15:1:0 2 v20,v1
b b6 If p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v34 OffPtr t26 0 - p52:273:16:1:0 1 v10
v v37 Com8 t5 0 - p52:273:24:0:0 2 v48
v v39 Load t6 0 - p52:273:14:0:0 1 v23,v1
v v35 Load t4 0 - p52:273:16:1:0 2 v34,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 AtomicOr8valueVariant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 AtomicOr8value t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 AtomicAnd8valueVariant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 AtomicAnd8value t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 33 "lower"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 34 "addressing modes"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 35 "late lower"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 36 "pair"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 37 "lowered deadcode for cse"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5
cache linestarts 52:266:275
dcllen 6
end
pass 38 "lowered cse"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 39 "elim unread autos"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 40 "tighten tuple selectors"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 41 "lowered deadcode"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 42 "checkLower"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 43 "loop invariant"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 44 "late phielim and copyelim"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 45 "tighten"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 46 "late deadcode"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 47 "critical"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 48 "phi tighten"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 49 "likelyadjust"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b4:b1,b5:b1,b6:b1,b7:b5,b8:b5,b9:b5,b10:b6,b11:b6,b12:b6
cache sdom b1:-:b6:-:2:59,b4:b1:-:-:53:56,b5:b1:b8:b4:29:50,b6:b1:b11:b5:5:26,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
dcllen 6
end
pass 50 "layout"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v10 ARM64LoweredNilCheck t2 0 - p52:266:11:1:0 3 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v10,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v10,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v10,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate laidout
dcllen 6
end
pass 51 "schedule"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 4 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 10 -
v v10 ARM64LoweredNilCheck t32 0 - p52:266:11:1:0 0 v7,v1
v v12 ARM64MOVBUload t5 9 - p52:266:11:0:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
dcllen 6
end
pass 52 "late nilcheck"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 3 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v12 ARM64MOVBUload t5 9 - p52:266:11:1:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
dcllen 6
end
pass 53 "flagalloc"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 3 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v12 ARM64MOVBUload t5 9 - p52:266:11:1:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v34,v20,v43,v11,v23,v15,v38,v19,v33,v14,v40,v28,v25,v36,v32,v31,v22,v18,v17,v13,v50,v49,v16,v6,v5,v4,v2
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
dcllen 6
end
pass 54 "regalloc"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 3 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v12 ARM64MOVBUload t5 9 - p52:266:11:1:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v2,v4,v5,v6,v11,v13,v14,v15,v16,v17,v18,v19,v20,v22,v23,v25,v28,v31,v32,v33,v34,v36,v38,v40,v43,v49,v50
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
regalloc 49 v3:SB,v7:R0,v8:R1,v9:R2,v12:R3,v21:R0,v24:R1,v26:(R1;-),v29:(R3;-),v35:R0,v37:R1,v39:R2,v41:(R2;-),v44:(R3;-),v48:R2
tempregs v29:R1,v44:R2
dcllen 6
end
pass 55 "loop rotate"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 3 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v12 ARM64MOVBUload t5 9 - p52:266:11:1:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b9:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b9:1 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b9 Plain p52:275:1:1:0 0 0 - - b4:0 b7:0,b8:0
v v51 Phi t30 0 - p0:0:0:0:0 1 v27,v30
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b12:0 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b12:1 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b12 Plain p52:275:1:1:0 0 0 - - b4:1 b10:0,b11:0
v v52 Phi t30 0 - p0:0:0:0:0 1 v42,v45
b b4 Ret p52:275:1:0:0 0 0 - v47 - b9:0,b12:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v51,v52
v v47 MakeResult t34 0 - p52:275:1:0:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v2,v4,v5,v6,v11,v13,v14,v15,v16,v17,v18,v19,v20,v22,v23,v25,v28,v31,v32,v33,v34,v36,v38,v40,v43,v49,v50
freeb b3,b2
cache postorder b4,b9,b7,b8,b5,b12,b10,b11,b6,b1
cache idom b1:-,b5:b1,b7:b5,b8:b5,b9:b5,b6:b1,b10:b6,b11:b6,b12:b6,b4:b1
cache sdom b1:-:b6:-:2:59,b5:b1:b8:b4:29:50,b7:b5:-:b9:38:41,b8:b5:-:b7:32:35,b9:b5:-:-:44:47,b6:b1:b11:b5:5:26,b10:b6:-:b12:14:17,b11:b6:-:b10:8:11,b12:b6:-:-:20:23,b4:b1:-:-:53:56
cache loopnest 13 0 - -
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
regalloc 49 v3:SB,v7:R0,v8:R1,v9:R2,v12:R3,v21:R0,v24:R1,v26:(R1;-),v29:(R3;-),v35:R0,v37:R1,v39:R2,v41:(R2;-),v44:(R3;-),v48:R2
tempregs v29:R1,v44:R2
dcllen 6
end
pass 56 "trim"
f b1 t1 a1 52 12
b b1 ARM64TBNZ p52:267:2:1:0 0 0 - v8 b5:0,b6:0 -
v v7 ArgIntReg t2 0 a8 p52:267:2:1:0 3 -
v v9 ArgIntReg t6 2 a10 p52:267:2:1:0 1 -
v v8 ArgIntReg t6 1 a9 p52:267:2:1:0 1 -
v v3 SB t18 0 - p0:0:0:0:0 2 -
v v1 InitMem t30 0 - p0:0:0:0:0 9 -
v v12 ARM64MOVBUload t5 9 - p52:266:11:1:0 1 v7,v1
v v48 ARM64SLL t5 0 - p52:270:2:1:0 3 v12,v9
b b5 ARM64TBNZ p52:271:13:0:0 1 0 - v24 b7:0,b8:0 b1:0
v v21 ARM64MOVDload t4 0 - p52:271:15:1:0 2 v7,v1
v v24 ARM64MOVBUload t6 0 a6 p52:271:13:0:0 1 v3,v1
b b7 Plain p52:271:13:0:0 0 0 - - b4:0 b5:0
v v26 ARM64LoweredAtomicOr8Variant t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v27 Select1 t30 0 - p52:271:13:0:0 1 v26
b b8 Plain p52:271:13:0:0 0 0 - - b4:2 b5:1
v v29 ARM64LoweredAtomicOr8 t37 0 - p52:271:13:0:0 1 v21,v48,v1
v v30 Select1 t30 0 - p52:271:13:0:0 1 v29
b b6 ARM64TBNZ p52:273:24:0:0 1 0 - v39 b10:0,b11:0 b1:1
v v35 ARM64MOVDload t4 0 - p52:273:16:1:0 2 v7,v1
v v37 ARM64MVN t5 0 - p52:273:24:0:0 2 v48
v v39 ARM64MOVBUload t6 0 a6 p52:273:14:0:0 1 v3,v1
b b10 Plain p52:273:24:0:0 0 0 - - b4:1 b6:0
v v41 ARM64LoweredAtomicAnd8Variant t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v42 Select1 t30 0 - p52:273:14:0:0 1 v41
b b11 Plain p52:273:24:0:0 0 0 - - b4:3 b6:1
v v44 ARM64LoweredAtomicAnd8 t37 0 - p52:273:14:0:0 1 v35,v37,v1
v v45 Select1 t30 0 - p52:273:14:0:0 1 v44
b b4 Ret p52:275:1:0:0 0 0 - v47 - b7:0,b10:0,b8:0,b11:0
v v46 Phi t30 0 - p52:275:1:0:0 1 v27,v42,v30,v45
v v47 MakeResult t34 0 - p52:275:1:1:0 1 v46
names s1,s2,s3,s4
named s1 v7
named s2 v8
named s3 v9
named s4 v12,v48
splits -
canon a3/t2/0/-/0=s1,a4/t6/0/-/0=s2,a5/t6/0/-/0=s3,a7/t5/0/-/0=s4
consts -
freev v2,v4,v5,v6,v11,v13,v14,v15,v16,v17,v18,v19,v20,v22,v23,v25,v28,v31,v32,v33,v34,v36,v38,v40,v43,v49,v50
freeb b3,b2
cache auxmap -:1,a3:2,a4:3,a5:4,a6:5,a8:6,a9:7,a10:8
cache linestarts 52:266:275
fstate scheduled,laidout
regalloc 49 v3:SB,v7:R0,v8:R1,v9:R2,v12:R3,v21:R0,v24:R1,v26:(R1;-),v29:(R3;-),v35:R0,v37:R1,v39:R2,v41:(R2;-),v44:(R3;-),v48:R2
tempregs v29:R1,v44:R2
dcllen 6
end
frontend
end
ptrcache t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t23,t26,t27,t28,t29
typelink t30=t34
typeorder t7,t5,t8,t11,t9,t12,t10,t13,t14,t17,t18,t27,t28,t15,t16,t6,t4,t20,t21,t22,t23,t24,t25,t36,t26,t35,t2,t1,t3,t19,t29,t30,t32,t31,t33,t37,t34
eof
"#

/-- `std/std/runtime/%28%2ApinState%29.set,1.prog` (quick-v10). -/
def fProg : String := r#"gofv-prog 3
pkg "runtime"
func "(*pinState).set" 1
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
type t1 8 8 8 1 01 "*pinState"
name n1 "v" PPARAM t1 1 "runtime.v" 0 a3
type t2 1 1 0 0 - "bool"
name n2 "val" PPARAM t2 1 "runtime.val" 0 a4
name n3 "multipin" PPARAM t2 1 "runtime.multipin" 0 a5
type t3 1 1 0 0 - "uint8"
name n4 "mask" PAUTO t3 1 "runtime.mask" 0 a7
type t4 8 8 8 1 01 "*uint8"
name n5 ".autotmp_4" PAUTO t4 3 "runtime..autotmp_4" 0 -
name n6 ".autotmp_5" PAUTO t4 3 "runtime..autotmp_5" 0 -
in n1 0 used
in n2 8 used
in n3 9 used
in n4 0 used
in n5 0 used,autotmp
in n6 0 used,autotmp
out n1 0 used
out n2 8 used
out n3 9 used
opt n5 0 autotmp
opt n6 0 autotmp
opt n4 0 -
stack 0 0 8
end
genin
posbase p52 "runtime/pinner.go" 1 1 -1 51 "runtime/pinner.go" "runtime/pinner.go" 1 1
sym y1 "runtime.(*pinState).set" 1
curfn p52:265:6:0:0 0 0
regargs 8192:0:t1,8193:8:t2,8194:9:t2
text y1 0 0 0 0 265 201080
end
prog0
sym y2 "gclocals\xc2\xb7wvjpxkknJ4nY1JtrArJJaw==" 0
sym y3 "gclocals\xc2\xb7J26BEvPExEQhJvjp9E8Whg==" 0
sym y4 "runtime.(*pinState).set.arginfo1" 0
sym y5 "runtime.(*pinState).set.argliveinfo" 0
sym y6 "runtime.arm64HasATOMICS" 0
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 0 p52:265:6:0:0
p 1 1 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - MEM/0/0/0/EXTERN/0/0/y2/- 0 0 p52:265:6:0:0
p 2 2 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/1/-/- 0 - MEM/0/0/0/EXTERN/0/0/y3/- 0 0 p52:265:6:0:0
p 3 3 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/5/-/- 0 - MEM/0/0/0/EXTERN/0/0/y4/- 0 0 p52:265:6:0:0
p 4 4 0 0 0 - FUNCDATA 0 CONST/0/0/0/NONE/0/6/-/- 0 - MEM/0/0/0/EXTERN/0/0/y5/- 0 0 p52:265:6:0:0
p 5 5 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/3/-/- 0 - CONST/0/0/0/NONE/0/1/-/- 0 0 p52:265:6:2:0
p 6 6 0 0 0 - PCDATA 0 CONST/0/0/0/NONE/0/0/-/- 0 - CONST/0/0/0/NONE/0/-2/-/- 0 0 p52:266:11:1:0
p 7 7 0 0 0 - MOVBU 0 MEM/8192/0/0/NONE/0/9/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p52:266:11:1:0
p 8 8 0 0 0 - LSL 0 REG/8194/0/0/NONE/0/0/-/- 8195 - REG/8194/0/0/NONE/0/0/-/- 0 0 p52:270:2:1:0
p 9 9 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8193 - BRANCH/0/0/0/NONE/0/0/-/@20 0 0 p52:267:2:1:0
p 10 10 0 0 0 - MOVD 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p52:271:15:1:0
p 11 11 0 0 0 - MOVBU 0 MEM/0/0/0/EXTERN/0/0/y6/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p52:271:13:2:0
p 12 12 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8193 - BRANCH/0/0/0/NONE/0/0/-/@15 0 0 p52:271:13:2:0
p 13 13 0 0 0 - LDORALB 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8193 0 p52:271:13:2:0
p 14 14 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@31 0 0 p52:271:13:2:0
p 15 15 0 0 0 - LDAXRB 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p52:271:13:2:0
p 16 16 0 0 0 - ORR 0 REG/8194/0/0/NONE/0/0/-/- 8195 - REG/8193/0/0/NONE/0/0/-/- 0 0 p52:271:13:2:0
p 17 17 0 0 0 - STLXRB 0 REG/8193/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8219 0 p52:271:13:2:0
p 18 18 0 0 0 - CBNZ 0 REG/8219/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@15 0 0 p52:271:13:2:0
p 19 19 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@31 0 0 p52:271:13:2:0
p 20 20 0 0 0 - MOVD 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8192/0/0/NONE/0/0/-/- 0 0 p52:273:16:1:0
p 21 21 0 0 0 - MVN 0 REG/8194/0/0/NONE/0/0/-/- 0 - REG/8193/0/0/NONE/0/0/-/- 0 0 p52:273:24:2:0
p 22 22 0 0 0 - MOVBU 0 MEM/0/0/0/EXTERN/0/0/y6/- 0 - REG/8194/0/0/NONE/0/0/-/- 0 0 p52:273:14:2:0
p 23 23 0 0 0 - TBZ 0 CONST/0/0/0/NONE/0/0/-/- 8194 - BRANCH/0/0/0/NONE/0/0/-/@27 0 0 p52:273:24:2:0
p 24 24 0 0 0 - MVN 0 REG/8193/0/0/NONE/0/0/-/- 0 - REG/8219/0/0/NONE/0/0/-/- 0 0 p52:273:14:2:0
p 25 25 0 0 0 - LDCLRALB 0 REG/8219/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8194 0 p52:273:14:2:0
p 26 26 0 0 0 - JMP 0 _ 0 - BRANCH/0/0/0/NONE/0/0/-/@31 0 0 p52:273:24:2:0
p 27 27 0 0 0 - LDAXRB 0 MEM/8192/0/0/NONE/0/0/-/- 0 - REG/8195/0/0/NONE/0/0/-/- 0 0 p52:273:14:2:0
p 28 28 0 0 0 - AND 0 REG/8193/0/0/NONE/0/0/-/- 8195 - REG/8194/0/0/NONE/0/0/-/- 0 0 p52:273:14:2:0
p 29 29 0 0 0 - STLXRB 0 REG/8194/0/0/NONE/0/0/-/- 0 - MEM/8192/0/0/NONE/0/0/-/- 8219 0 p52:273:14:2:0
p 30 30 0 0 0 - CBNZ 0 REG/8219/0/0/NONE/0/0/-/- 0 - BRANCH/0/0/0/NONE/0/0/-/@27 0 0 p52:273:14:2:0
p 31 31 0 0 0 - RET 0 _ 0 - _ 0 0 p52:275:1:0:0
p 32 32 0 0 0 - END 0 _ 0 - _ 0 0 p0:0:0:0:0
fn y1 0 0 0 0 265 201080
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVB MOVBU
spill MEM/8383/0/0/NONE/0/17/-/- 8194 0 MOVB MOVBU
funcaux y2 y3 - - y4 y5 -
needzero -
regargs -
text 0 0 - 0
symalign y2:4,y3:4,y4:1,y5:1
autot -
dbgentry 1
dbgslot 0 n1 t1 0
dbgslot 1 n2 t2 0
dbgslot 2 n3 t2 0
dbgslot 3 n4 t3 0
dbgvar 0 n1 0
dbgvar 1 n2 1
dbgvar 2 n3 2
dbgvar 3 n4 3
dbgloc 0 1:-10000:5:21:50
dbgloc 1 1:-10000:5:24:51
dbgloc 2 1:-10000:1:48:52
dbgloc 3 1:12:-1:-30000:53
dbgregout -
dbgpc 5:21:11,5:24:12,1:48:9,1:12:8
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
p 0 0 0 0 0 - TEXT 0 MEM/0/0/0/EXTERN/0/0/y1/- 0 - TEXTSIZE/0/0/0/NONE/0/0/-/i16 0 2 p52:265:6:0:0
p 1 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - MEM/0/0/0/EXTERN/110/0/y2/- 0 0 p52:265:6:0:0
p 2 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/1/-/- 0 - MEM/0/0/0/EXTERN/110/0/y3/- 0 0 p52:265:6:0:0
p 3 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/18/5/-/- 0 - MEM/0/0/0/EXTERN/110/0/y4/- 0 0 p52:265:6:0:0
p 4 0 0 0 4 - FUNCDATA 0 CONST/0/0/0/NONE/17/6/-/- 0 - MEM/0/0/0/EXTERN/110/0/y5/- 0 0 p52:265:6:0:0
p 5 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/17/3/-/- 0 - CONST/0/0/0/NONE/17/1/-/- 0 0 p52:265:6:2:0
p 6 0 0 0 13 - PCDATA 0 CONST/0/0/0/NONE/16/0/-/- 0 - CONST/0/0/0/NONE/22/-2/-/- 0 0 p52:266:11:1:0
p 7 0 0 0 294 - MOVBU 0 MEM/8192/0/0/NONE/89/9/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p52:266:11:1:0
p 8 4 0 0 272 - LSL 0 REG/8194/0/0/NONE/2/0/-/- 8195 - REG/8194/0/0/NONE/2/0/-/- 0 0 p52:270:2:1:0
p 9 8 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8193 - BRANCH/0/0/0/NONE/36/20/-/@20 0 0 p52:267:2:1:0
p 10 12 0 0 333 - MOVD 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p52:271:15:1:0
p 11 16 0 0 299 - MOVBU 0 MEM/0/0/0/EXTERN/110/0/y6/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p52:271:13:2:0
p 12 24 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8193 - BRANCH/0/0/0/NONE/36/15/-/@15 0 0 p52:271:13:2:0
p 13 28 0 0 465 - LDORALB 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8193 0 p52:271:13:2:0
p 14 32 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/31/-/@31 0 0 p52:271:13:2:0
p 15 36 0 0 234 - LDAXRB 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p52:271:13:2:0
p 16 40 0 0 49 - ORR 0 REG/8194/0/0/NONE/2/0/-/- 8195 - REG/8193/0/0/NONE/2/0/-/- 0 0 p52:271:13:2:0
p 17 44 0 0 425 - STLXRB 0 REG/8193/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8219 0 p52:271:13:2:0
p 18 48 0 0 85 - CBNZ 0 REG/8219/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/15/-/@15 0 0 p52:271:13:2:0
p 19 52 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/31/-/@31 0 0 p52:271:13:2:0
p 20 56 0 0 333 - MOVD 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8192/0/0/NONE/2/0/-/- 0 0 p52:273:16:1:0
p 21 60 0 0 405 - MVN 0 REG/8194/0/0/NONE/2/0/-/- 0 - REG/8193/0/0/NONE/2/0/-/- 0 0 p52:273:24:2:0
p 22 64 0 0 299 - MOVBU 0 MEM/0/0/0/EXTERN/110/0/y6/- 0 - REG/8194/0/0/NONE/2/0/-/- 0 0 p52:273:14:2:0
p 23 72 0 0 470 - TBZ 0 CONST/0/0/0/NONE/16/0/-/- 8194 - BRANCH/0/0/0/NONE/36/27/-/@27 0 0 p52:273:24:2:0
p 24 76 0 0 405 - MVN 0 REG/8193/0/0/NONE/2/0/-/- 0 - REG/8219/0/0/NONE/2/0/-/- 0 0 p52:273:14:2:0
p 25 80 0 0 465 - LDCLRALB 0 REG/8219/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8194 0 p52:273:14:2:0
p 26 84 0 0 5 - JMP 0 NONE/0/0/0/NONE/1/0/-/- 0 - BRANCH/0/0/0/NONE/36/31/-/@31 0 0 p52:273:24:2:0
p 27 88 0 0 234 - LDAXRB 0 MEM/8192/0/0/NONE/77/0/-/- 0 - REG/8195/0/0/NONE/2/0/-/- 0 0 p52:273:14:2:0
p 28 92 0 0 49 - AND 0 REG/8193/0/0/NONE/2/0/-/- 8195 - REG/8194/0/0/NONE/2/0/-/- 0 0 p52:273:14:2:0
p 29 96 0 0 425 - STLXRB 0 REG/8194/0/0/NONE/2/0/-/- 0 - MEM/8192/0/0/NONE/77/0/-/- 8219 0 p52:273:14:2:0
p 30 100 0 0 85 - CBNZ 0 REG/8219/0/0/NONE/2/0/-/- 0 - BRANCH/0/0/0/NONE/36/27/-/@27 0 0 p52:273:14:2:0
p 31 104 0 0 15 - RET 0 NONE/0/0/0/NONE/1/0/-/- 0 - MEM/8222/0/0/NONE/77/0/-/- 0 0 p52:275:1:0:0
fn y1 16 0 0 0 265 2010c8
spill MEM/8383/0/0/NONE/0/8/-/- 8192 0 MOVD MOVD
spill MEM/8383/0/0/NONE/0/16/-/- 8193 0 MOVB MOVBU
spill MEM/8383/0/0/NONE/0/17/-/- 8194 0 MOVB MOVBU
funcaux y2 y3 - - y4 y5 -
text 112 0 032440396220c29a81010036000040f91b00009061034039610000360130e2381200001403fc5f08610002aa01fc1b08bbffffb50d000014000040f9e10322aa1b0000906203403982000036fb0321aa0210fb380500001403fc5f086200018a02fc1b08bbffffb5c0035fd600000000 2
reloc 16 8 R_ARM64_PCREL_LDST8 0 y6
reloc 64 8 R_ARM64_PCREL_LDST8 0 y6
pcln y11 y12 y13 y14 y7,y8,y9,y10 y2,y3,_,_,_,y4,y5
usedfiles 51
data y2 Sxxx 0 4 8000 02000000010000000100 0
data y3 Sxxx 0 4 8000 0200000000000000 0
data y4 SDATA 7 1 8000 000808010901ff 0
data y5 SDATA 2 1 8000 0000 0
data y7 SRODATA 3 1 28000 011c00 0
data y8 SRODATA 0 1 28000 - 0
data y9 SRODATA 0 1 28000 - 0
data y10 SRODATA 3 1 28000 041c00 0
data y11 SRODATA 3 1 28000 021c00 0
data y12 SRODATA 3 1 28000 681c00 0
data y13 SRODATA 14 1 28000 96040108010501080b040c040200 0
data y14 SRODATA 3 1 28000 001c00 0
end
dwarf
sym y15 "" 0
sym y16 "" 0
sym y17 "" 0
sym y18 "go:info.runtime.(*pinState).set$abstract" 0
sym y19 "" 0
sym y20 "go:info.*runtime.pinState" 0
sym y21 "go:info.bool" 0
sym y22 "go:info.uint8" 0
dwfn y15 y16 y17 y18 y19 "runtime.(*pinState).set" 51:265 1 0 1 4262
dwdcl n1,n2,n3
dwclosure 0 -
dwparents -
dwparams n1,n2,n3
dwprecursor y1 y18 n1,n2,n3,n4
dwname n1 1 1 0 0 0 0 0 0 - - "*runtime.pinState" 0 0 1 p52:265:7:0:0
dwname n2 1 1 0 0 0 0 8 0 - - "bool" 0 0 1 p52:265:24:0:0
dwname n3 1 1 0 0 0 0 9 0 - - "bool" 0 0 1 p52:265:34:0:0
dwname n5 1 0 1 0 0 0 0 0 - - "*uint8" 0 0 1 p52:271:13:0:0
dwname n6 1 0 1 0 0 0 0 0 - - "*uint8" 0 0 1 p52:273:14:0:0
dwname n4 1 0 0 0 0 0 0 0 - - "uint8" 0 0 1 p52:266:2:0:0
var 0 0 "v" 5 1 0 0 0 8 y20 "runtime/pinner.go" 265 7 0 0 1 0 v0
var 1 0 "val" 5 1 0 0 0 16 y21 "runtime/pinner.go" 265 24 0 1 1 0 v1
var 2 0 "multipin" 5 1 0 0 0 17 y21 "runtime/pinner.go" 265 34 0 2 1 0 v2
var 3 0 "mask" 52 1 0 0 0 -8 y22 "runtime/pinner.go" 266 2 0 3 1 0 v3
scope 0 0 - 0,1,2,3
dieref y15 2 y18 0
dieref y15 4 y18 1
dieref y15 6 y18 2
dieref y15 8 y18 3
dieoff y18 0:29,1:37,2:47,3:62
data y15 SDWARFFCN 47 0 0 0600000000000070019c29000000000000000029000000000000000029000000000000000023000000000000000000 10
reloc 1 4 R_DWARFSECREF 0 y18
reloc 5 2 R_DWTXTADDR_U2 0 y1
reloc 11 4 R_DWARFSECREF 0 y18
reloc 15 4 R_DWARFSECREF 0 y16
reloc 20 4 R_DWARFSECREF 0 y18
reloc 24 4 R_DWARFSECREF 9 y16
reloc 29 4 R_DWARFSECREF 0 y18
reloc 33 4 R_DWARFSECREF 18 y16
reloc 38 4 R_DWARFSECREF 0 y18
reloc 42 4 R_DWARFSECREF 27 y16
data y16 SDWARFLOC 36 0 0 010000040010015000010000040018015100010000040008015200010000040470015300 4
reloc 1 2 R_DWTXTADDR_U2 0 y1
reloc 10 2 R_DWTXTADDR_U2 0 y1
reloc 19 2 R_DWTXTADDR_U2 0 y1
reloc 28 2 R_DWTXTADDR_U2 0 y1
data y17 SDWARFRANGE 0 0 0 - 0
data y19 SDWARFLINES 35 0 0 00090200000000000000000434038402143b343b06370608b106370608d90208000101 1
reloc 3 8 R_ADDR 0 y1
data y18 SDWARFABSFCN 75 0 1 0572756e74696d652e282a70696e5374617465292e736574000189020122760000000000002276616c000000000000226d756c746970696e000000000000216d61736b008a020000000000 4
reloc 33 4 R_DWARFSECREF 0 y20
reloc 43 4 R_DWARFSECREF 0 y21
reloc 58 4 R_DWARFSECREF 0 y21
reloc 70 4 R_DWARFSECREF 0 y22
end
eof
"#

/-- The loaded function (`GenG2.load`, as `gen-check`). -/
def stIn : Except String (LocCtx × Array GoFV.Asm.Prog × (ID → Option Nat) × G2In) :=
  GenG2.load fSsa fProg

/-- `runLoc`'s context of `runtime.(*pinState).set`. -/
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

/-- The index of `v48`'s `LSL R2, R3, R2` among the Progs (`kdOK` checks it). -/
def jF : Nat := 8

/-- A PC table for `b1` with `v48` (index 6) at its Prog and the value after it at the next. -/
def tab : PcTab := [(1, List.replicate 7 8 ++ [9])]

/-- Every home past `lc.homes` is none, which `homeOK10` accepts. -/
theorem homeOK10_all {lc : LocCtx} (h : ∀ i, i < lc.homes.size → homeOK10 lc i = true) (i : Nat) :
    homeOK10 lc i = true := by
  by_cases hi : i < lc.homes.size
  · exact h i hi
  · have hh : lc.home i = none := by
      simp only [LocCtx.home]
      rw [getElem?_neg lc.homes i hi]
      rfl
    unfold homeOK10 homeOK4 homeOK3 homeOK2 homeOK
    rw [hh]
    rfl

/-- The class map before `v48`: the classes of its arguments' registers. -/
def K0 : KMap := ((KMap.bot.set! 3 (some 8)).set! 2 (some 1))

def blk : Block := (lc.ctx.f.block? 1).getD default

def val (n : ID) : Value := (lc.ctx.f.value? n).getD default

/-- P0's layout: GenG2's, a 16-byte frame with 8 bytes of extra space. -/
def L : Link := Link.byId (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList

/-- A framed activation (`SP = 0x7fff0000`, `g = 0x9000`, saved `LR` and `FP` 0) with the globals
at `symA`, no home slot, the PC table `tab`. -/
def E : MatchEnv :=
  { lc, ι := GenG2.ι, sp := GenG2.sp0, slot := fun _ => none, g := 0x9000, lr := 0, fp := 0,
    framed := true, pcOf := pcOfTab GenG2.text ps.toList tab }

/-- The `runLoc` state before `v48`: its arguments in their registers, every other register
`poison`, the empty memory. -/
def s0 : LocState :=
  { fr := { regs := Array.replicate 32 none, args := [], mem0 := GenG2.mem0 },
    regs := Array.ofFn (n := 64) fun i => if i.val = 3 then .int .w8 5 else if i.val = 2 then .bool true else .poison,
    flags := .poison, slots := [], mem := .mem GenG2.mem0 }

/-- The machine before `v48`: the arguments' words, the activation's `g` and `FP`, the PC of
`v48`, a zero memory. -/
def m0 : MState :=
  { x := fun k => if k = 3 then 5 else if k = 2 then 1 else if k = 28 then 0x9000
      else if k = 29 then GenG2.sp0 - 8 else 0,
    sp := GenG2.sp0, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := E.pcOf 1 6, mem := fun _ => 0 }

/-- The pattern of an accepted single-Prog value. -/
def patOf : Option (Except String VKind2) → Option Pat
  | some (.ok (.prog pat)) => some pat
  | _ => none

theorem patOf_some {o : Option (Except String VKind2)} {pat : Pat} (h : patOf o = some pat) :
    o = some (.ok (.prog pat)) := by
  unfold patOf at h
  split at h
  · cases h; rfl
  · cases h

/-- `vkind58a` accepts `v48` with a pattern the Prog at `jF` matches. -/
def kdOK : Bool := (patOf (vkind58a lc g (val 48))).any fun pat => (ps[jF]?).any pat.ok

/-- The register value `.int .w8 10`. -/
def isRes : Option Val → Bool
  | some (.int .w8 x) => x == 10
  | _ => false

theorem isRes_spec {o : Option Val} (h : isRes o = true) : o = some (.int .w8 10) := by
  unfold isRes at h
  split at h
  · rename_i x; rw [beq_iff_eq.1 h]
  · cases h

/-- What compiled evaluation checks on `runtime.(*pinState).set`: it holds an arm64 op; G57's value check
`vkind57` rejects `v48` (SLL by a boolean), which `vkind58a` accepts with the Prog at `jF`; the Progs
have distinct IDs below `2^32`; every home is one G10 handles; `checkFrame` passes; `b1` holds
`v48` at index 6; no frame variable is accessed and there is no home slot; `v48` reads its
registers at the classes of `K0`; and `stepLoc` runs `v48` to `.int .w8 10` in its register. -/
def gFacts : Bool :=
  lc.ctx.f.lowered && (vkind57 lc g (val 48)).toOption.isNone && kdOK &&
    ps.toList.all (·.id < 2 ^ 32) && decide (ps.toList.map (·.id)).Nodup &&
    (List.range lc.homes.size).all (homeOK10 lc) && (checkFrame lc g).toOption == some () &&
    (lc.ctx.f.block? 1).isSome && (lc.ctx.f.value? 48).isSome && blk.values[6]? == some 48 &&
    (val 48).op == .ARM64SLL && (accessedVars lc).isEmpty && (homeSlots lc).isEmpty &&
    (kReads lc (val 48)).all (fun rc => K0.get rc.1 == some rc.2) && K0.get 3 == some 8 && K0.get 2 == some 1 &&
    GenG1.okThen (stepLoc GenG2.env lc s0 (val 48)) (fun s1 => isRes s1.regs[2]?)

theorem g58a3_facts : gFacts = true := by
  native_decide

/-- The facts of `gFacts` as hypotheses. -/
theorem facts :
    lc.ctx.f.lowered = true ∧ (vkind57 lc g (val 48)).toOption = none ∧ kdOK = true ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      (∀ i, homeOK10 lc i = true) ∧ checkFrame lc g = .ok () ∧
      lc.ctx.f.value? 48 = some (val 48) ∧ blk.values[6]? = some 48 ∧
      (val 48).op = .ARM64SLL ∧ (accessedVars lc).isEmpty = true ∧
      (homeSlots lc).isEmpty = true ∧
      (∀ rc ∈ kReads lc (val 48), K0.get rc.1 = some rc.2) ∧ (K0.get 3 = some 8 ∧ K0.get 2 = some 1) ∧
      GenG1.okThen (stepLoc GenG2.env lc s0 (val 48)) (fun s1 => isRes s1.regs[2]?) = true := by
  have hf := g58a3_facts
  simp only [gFacts, Bool.and_eq_true, beq_iff_eq, and_assoc, Option.isNone_iff_eq_none,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at hf
  obtain ⟨hl, h57, hkd, hlt, hnd, hhome, hcf, -, hvs, hi, hop, hav, hsl, hrd, hrest⟩ := hf
  refine ⟨hl, h57, hkd, hlt, hnd, homeOK10_all hhome, ?_, ?_, hi, hop, hav, hsl, hrd, ?_⟩
  · revert hcf; cases checkFrame lc g <;> simp [Except.toOption]
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hvs
    simp [val, hv]
  · simpa only [and_assoc] using hrest

/-- `vkind58a`'s pattern for `v48` and the Prog at `jF` it matches. -/
theorem kd_spec (h : kdOK = true) :
    ∃ pat, vkind58a lc g (val 48) = some (.ok (.prog pat)) ∧ (ps[jF]?).any pat.ok = true := by
  obtain ⟨pat, hp, h⟩ := (Option.any_eq_true _ _).1 h
  exact ⟨pat, patOf_some hp, h⟩

/-! ## The activation -/

theorem env58 (hlt : ∀ p ∈ ps.toList, p.id < 2 ^ 32) (hav : (accessedVars lc).isEmpty = true)
    (hsl : (homeSlots lc).isEmpty = true) : G49Env lc g L ps 0 tab E where
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
            slot := fun k hk => by simp [List.isEmpty_iff.1 hsl] at hk
            extra := by decide
            frame := ⟨by decide, by decide, fun k off h => by cases h⟩ }
          vars := by
            intro x hx
            simp [List.isEmpty_iff.1 hav] at hx }
        wbs := fun h => by cases h }
      icalls := fun h => by cases h }
    memeqs := fun h => by cases h }
  vars := by
    intro x hx
    simp [List.isEmpty_iff.1 hav] at hx

/-! ## `v48`: `LSL R2, R3, R2` -/

theorem s0_regs {r : Nat} {x : Val} (h : s0.regs[r]? = some x) :
    (r = 3 ∧ x = .int .w8 5) ∨ (r = 2 ∧ x = .bool true) ∨ x = .poison := by
  simp only [s0, Array.getElem?_ofFn] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    by_cases h0 : r = 3
    · subst h0; simp
    ·
      by_cases h1 : r = 2
      · subst h1; simp
      · simp [h0, h1]
  · cases h

theorem locMatch0 : LocMatch E s0 1 6 m0 where
  regs := by
    intro r v hv
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show (m0.x _).setWidth _ = _; simp only [m0]; decide
    · refine ⟨fun k hk => ?_, fun k hk => by simp [objV?] at hk⟩
      simp only [objX?] at hk
      cases hk
      show m0.x _ = _; simp only [m0]; decide
    · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  flags := trivial
  slots := by intro k v h; simp [s0] at h
  mem := ⟨GenG2.mem0, rfl, GenG2.memInj0 rfl _⟩
  frame := ⟨rfl, rfl, fun _ => ⟨rfl, by simp only [MState.word, readMem, m0, E]; decide,
    by simp only [MState.word, readMem, m0, E]; decide⟩,
    fun h => by cases h⟩
  pc := rfl

theorem inv0 (hk3 : K0.get 3 = some 8) (hk2 : K0.get 2 = some 1) :
    G3Inv E lc K0 s0 where
  core := by
    refine ⟨fun r v c hr hv hc => ?_, GenG2.mem0, rfl, by simp [KeysNodup, GenG2.mem0],
      fun b al a h => by simp [GenG2.mem0] at h⟩
    rcases s0_regs hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl
    · rw [hk3] at hc; cases hc; rfl
    · rw [hk2] at hc; cases hc; rfl
    · trivial
  slots := by intro k v h; simp [s0] at h

/-- **G58, group A, on `runtime.(*pinState).set`** (whose `if multipin { mask <<= 1 }` lowers to
`SLL v12 v9`, the `uint8` mask shifted by the boolean `multipin` (`v9`, in `R2`): `checkG57` asks
the shift amount at least 8 bits (`v48: SLL widths`) and `vkind58a` accepts it (a boolean's register
is 0 or 1 on all 64 bits). From `s0`, with the mask 5 in `R3` and `true` in `R2`, `stepLoc` runs
`v48` to 10, and `vk58a_step` relates it to a machine run of its Prog to a state with `X2`'s low
byte 10, under an activation extending `E` that is again a `G49Env`.) -/
theorem genG58a3_witness :
    (vkind57 lc g (val 48)).toOption = none ∧
      ∃ s1 E1 m1, stepLoc GenG2.env lc s0 (val 48) = .ok s1 ∧ s1.regs[2]? = some (.int .w8 10) ∧
        E.Extends E1 ∧ G49Env lc g L ps 0 tab E1 ∧
        PStar GenG2.H0 L ps.toList 0 m0 m1 ∧ LocMatch E1 s1 1 7 m1 ∧
        (m1.x 2).setWidth 8 = 10 := by
  obtain ⟨hl, h57, hkd, hlt, hnd, hhome, hcf, hv, -, -, hav, hsl, hrd, ⟨hk3, hk2⟩, hrun⟩ :=
    facts
  obtain ⟨s1, hs1, hr⟩ := GenG1.okThen_spec hrun
  have hr1 := isRes_spec hr
  have hE := env58 hlt hav hsl
  obtain ⟨pat, hvk, hpat⟩ := kd_spec hkd
  obtain ⟨htemp, hVK⟩ := vkind58a_spec hvk
  obtain ⟨p, hp, hok⟩ := (Option.any_eq_true _ _).1 hpat
  obtain ⟨hk, hpk⟩ := Array.getElem?_eq_some_iff.1 hp
  have hvs : VStep2 ps (.prog pat) jF (jF + 1) :=
    ⟨jF, Nat.le_refl _, rfl, hk, by rw [hpk]; exact hok, fun l _ h1 h2 => absurd h2 (by omega)⟩
  have F : Facts lc (fun _ => GenG2.symA) GenG2.text 16 8 ps.toList 0 E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt,
      fun p hp => GenG2.prog_addr_ne (hlt p hp) hp (by simp) (by simp), GenG2.addrAgree⟩
  have hj : E.pcOf 1 6 = pcAt GenG2.text ps.toList jF := rfl
  have hj' : E.pcOf 1 (6 + 1) = pcAt GenG2.text ps.toList (jF + 1) := rfl
  obtain ⟨E1, m1, hx1, hE1, hp1, hm1, -, -⟩ := vk58a_step (H := GenG2.H0) (L := []) (bid := 1)
    (i := 6) (j := jF) (j' := jF + 1) hE F hcf hv hVK hvs htemp hj hj' hrd locMatch0
    (inv0 hk3 hk2) (fun e he => by cases he) hs1
  refine ⟨h57, s1, E1, m1, hs1, hr1, hx1, hE1, hp1, hm1, ?_⟩
  exact (hm1.regs 2 _ hr1).1 _ (by simp [objX?])

end GoFV.Proof.Witness.GenG58a3
